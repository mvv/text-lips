{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}

-- | Monadic parsing combinator library with attention to locations.
module Text.Lips
  ( ParsedLines(..)
  , Parser
  , ParserResult(..)
  , ParserStep(..)
  , startParser
  , startParserAtLine
  , starveParser
  , parseText
  , LocParsing(..)
  , ResetLineParsing(..)
  ) where

import Data.Typeable (Typeable)
import Data.Monoid (Monoid(..))
import Data.Word (Word)
import Data.String (IsString(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Unsafe as T
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Text.Loc
import Text.Parser.Combinators (Parsing(..))
import Text.Parser.Char (CharParsing(..))
import Control.Applicative
import Control.Monad (MonadPlus(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict

data SavedInput = SavedInput { siSave ∷ Text → SavedInput
                             , siLoad ∷ [Text] → [Text]
                             , siPop  ∷ SavedInput }

doNotSave ∷ SavedInput
doNotSave = SavedInput { siSave = const doNotSave
                       , siLoad = id
                       , siPop  = doNotSave }

save ∷ SavedInput → SavedInput
save = go []
  where go is p = SavedInput { siSave = \i → go (i : is) (siSave p i)
                             , siLoad = (++ reverse is)
                             , siPop  = p }

data Error = Error { errLoc ∷ LineCol
                   , errCtx ∷ [String]
                   , errMsg ∷ String }

data LastLine = LastLine Text {-# UNPACK #-} !Int
              | NoLastLine

data AccLines = AccLines { lsLines   ∷ Seq Text
                         , lsLastPre ∷ Text
                         , lsLast    ∷ LastLine }

updateLines ∷ Text → Char → Bool → LineCol → AccLines
            → (LineCol → AccLines → α) → α
updateLines _ '\n' _ l ls cont = cont l' ls'
  where
    !l'  = nextLine l
    !ls' = case lsLast ls of
             LastLine txt len →
               AccLines { lsLines   = lsLines ls |>
                                        (lsLastPre ls `mappend`
                                           T.take len txt)
                        , lsLastPre = T.empty
                        , lsLast    = NoLastLine }
             NoLastLine →
               ls { lsLines   = lsLines ls |> lsLastPre ls
                  , lsLastPre = T.empty }
updateLines i _ itIsNull l ls cont = cont l' ls'
  where
    !l'  = nextCol l
    !ls' = case lsLast ls of
             LastLine txt len →
               ls { lsLast    = LastLine txt (len + 1) }
             NoLastLine | itIsNull →
               ls { lsLastPre = lsLastPre ls `mappend` i }
             NoLastLine →
               ls { lsLast    = LastLine i 1 }

forceUpdateLines ∷ Text → Char → Bool → LineCol → AccLines
                 → (LineCol → AccLines → α) → α
forceUpdateLines _ '\n' _ l ls cont = cont l' ls'
  where !l'  = nextLine l
        !ls' = AccLines { lsLines   = lsLines ls |> lsLastPre ls
                        , lsLastPre = T.empty
                        , lsLast    = NoLastLine }
forceUpdateLines i _ itIsNull l ls cont = cont l' ls'
  where !l'  = nextCol l
        !ls' | itIsNull  = ls { lsLastPre = lsLastPre ls `mappend` i }
             | otherwise = ls { lsLast    = LastLine i 1 }

-- | Lines of text consumed by a parser (fully or partially).
data ParsedLines = ParsedLines { plFull    ∷ Seq Text -- ^ Fully consumed lines
                               , plPartial ∷ Maybe Text
                                 -- ^ Partially consumed line
                               }
                   deriving (Typeable, Show)

type WithSt r = [String] → LineCol → LineCol → AccLines
              → [Text] → SavedInput → ParserStep r

-- | Opaque parser type.
newtype Parser α =
  Parser { runParser ∷ ∀ r . (α → WithSt r)
                           → (α → WithSt r)
                           → (Error → WithSt r)
                           → (Error → WithSt r)
                           → WithSt r }

-- | Parser result.
data ParserResult α = ParserSuccess { prLeftovers ∷ [Text] -- ^ Unparsed input
                                    , prLines     ∷ ParsedLines -- ^ Parsed input
                                    , prLoc       ∷ LineCol -- ^ Last location
                                    , prResult    ∷ α -- ^ Parsed value
                                    }
                    | ParserFailure { prLeftovers ∷ [Text]
                                    , prLines     ∷ ParsedLines
                                    , prLoc       ∷ LineCol
                                    , prErrCtx    ∷ [String] -- ^ Error context
                                    , prErrMsg    ∷ String -- ^ Error message
                                    }
                    deriving (Typeable, Show)

-- | Parser continuation.
data ParserStep α = ParserCont (Text → ParserStep α) (ParserResult α)
                  | ParserDone (ParserResult α)

-- | Start a parser.
startParser ∷ Parser α → ParserStep α
startParser = startParserAtLine 1 T.empty

-- | Start a parser on a specific line number and provide it with a first
--   chunk of the input.
startParserAtLine ∷ Word → Text → Parser α → ParserStep α
startParserAtLine ln₀ pre₀ (Parser p) =
   p fc fc fh fh [] (LineCol ln₀ col₀) (LineCol ln₀ (col₀ + 1))
     lines₀ [] doNotSave
  where fc a _ _ nl ls is si =
            ParserDone (ParserSuccess { prLeftovers = lo
                                      , prLines     = ls'
                                      , prLoc       = nl
                                      , prResult    = a })
          where lo  = siLoad si is
                ls' = calcLines lo ls
        fh e _ _ _ ls is si =
            ParserDone (ParserFailure { prLeftovers = lo
                                      , prLines     = ls'
                                      , prLoc       = errLoc e
                                      , prErrCtx    = reverse (errCtx e)
                                      , prErrMsg    = errMsg e })
          where lo  = siLoad si is
                ls' = calcLines lo ls
        col₀   = fromIntegral (T.length pre₀)
        lines₀ = AccLines { lsLines   = Seq.empty
                          , lsLastPre = pre₀
                          , lsLast    = NoLastLine }
        calcLines lo (AccLines {..}) = go [] lo
          where lastLine       = case lsLast of
                                   LastLine txt len → lsLastPre `mappend`
                                                        T.take len txt
                                   NoLastLine       → lsLastPre
                go acc []      = ParsedLines lsLines
                               $ Just
                               $ mconcat
                               $ reverse (lastLine : acc)
                go acc (h : t) | (h₁, h₂) ← T.break (== '\n') h
                               , not (T.null h₂)
                               , line ← mconcat
                                      $ reverse
                                      $ h₁ : lastLine : acc
                               = ParsedLines (lsLines |> line) Nothing
                               | otherwise
                               = go (h : acc) t

-- | Feed a parser continuation with empty input.
starveParser ∷ ParserStep α → ParserResult α
starveParser (ParserCont _ r) = r
starveParser (ParserDone r)   = r

-- | Run a parser on a text.
parseText ∷ Text → Parser α → ParserResult α
parseText t p = case startParser p of
                  ParserCont c _ → starveParser (c t)
                  ParserDone r   → r

instance Functor Parser where
  fmap f (Parser p) = Parser $ \c cc → p (c . f) (cc . f)

instance Applicative Parser where
  pure a = Parser $ \c _ _ _ → c a
  {-# INLINE pure #-}
  Parser p₁ <*> Parser p₂ = Parser $ \c cc h ch →
    p₁ (\f → p₂ (c . f) (cc . f) h ch) (\f → p₂ (cc . f) (cc . f) ch ch) h ch
  {-# INLINE (<*>) #-}

instance Alternative Parser where
  empty = Parser $ \_ _ h _ ctx pl nl →
            h (Error nl ctx "Empty alternative") ctx pl nl
  {-# INLINE empty #-}
  Parser p₁ <|> Parser p₂ =
    Parser $ \c cc h ch ctx pl nl ls →
      p₁ c cc (\_ _ _ _ _ → p₂ c cc h ch ctx pl nl ls) ch ctx pl nl ls

instance Monad Parser where
  return = pure
  {-# INLINE return #-}
  Parser p >>= f = Parser $ \c cc h ch →
    p (\a → runParser (f a) c cc h ch) (\a → runParser (f a) cc cc ch ch) h ch
  {-# INLINE (>>=) #-}
  fail msg = Parser $ \_ _ h _ ctx pl nl →
               h (Error nl ctx msg) ctx pl nl
  {-# INLINE fail #-}

instance MonadPlus Parser where
  mzero = empty
  {-# INLINE mzero #-}
  mplus = (<|>)
  {-# INLINE mplus #-}

instance Parsing Parser where
  try (Parser p) =
    Parser $ \c cc h _ ctx pl nl ls is si →
      p (\a ctx' pl' nl' ls' is' si' → c  a ctx' pl' nl' ls' is' (siPop si'))
        (\a ctx' pl' nl' ls' is' si' → cc a ctx' pl' nl' ls' is' (siPop si'))
        (\e _    _   _   _   _   si' → h  e ctx  pl  nl  ls
                                          (siLoad si' is) (siPop si'))
        (\e _    _   _   _   _   si' → h  e ctx  pl  nl  ls
                                          (siLoad si' is) (siPop si'))
        ctx pl nl ls is (save si)
  Parser p <?> label = Parser $ \c cc h ch ctx →
                         p (\a _ → c a ctx) (\a _ → cc a ctx)
                           (\e _ → h e ctx) (\e _ → ch e ctx)
                           (label : ctx)
  {-# INLINE (<?>) #-}
  skipMany p = Parser $ \c cc h ch ctx pl nl ls →
                 runParser p (\_ → runParser (skipMany p) c  cc h  ch)
                             (\_ → runParser (skipMany p) cc cc ch ch)
                             (\_ _ _ _ _ → c () ctx pl nl ls)
                             ch ctx pl nl ls
  skipSome p = Parser $ \c cc h ch →
                 runParser p (\_ → runParser (skipMany p) c  cc h  ch)
                             (\_ → runParser (skipMany p) cc cc ch ch)
                             h ch
  {-# INLINE skipSome #-}
  unexpected = fail . ("Unexpected " ++)
  {-# INLINE unexpected #-}
  notFollowedBy (Parser p) = Parser $ \c _ h _ ctx pl nl ls is si →
    p (\a _ _ _ _ _ si' → h (Error nl ctx ("Unexpected " ++ show a))
                            ctx pl nl ls (siLoad si' is) (siPop si'))
      (\a _ _ _ _ _ si' → h (Error nl ctx ("Unexpected " ++ show a))
                            ctx pl nl ls (siLoad si' is) (siPop si'))
      (\_ _ _ _ _ _ si' → c () ctx pl nl ls (siLoad si' is) (siPop si'))
      (\_ _ _ _ _ _ si' → c () ctx pl nl ls (siLoad si' is) (siPop si'))
      ctx pl nl ls is (save si)
  eof = Parser $ \c _ h _ ctx pl nl ls is si →
          let go = ParserCont
                     (\i → if T.null i
                           then go
                           else h (Error nl ctx "End of input expected")
                                  ctx pl nl ls [i] (siSave si i))
                     (starveParser $ c () ctx pl nl ls is si) in
            if null is
            then go
            else h (Error nl ctx "End of input expected")
                   ctx pl nl ls is si

instance CharParsing Parser where
  satisfy p = Parser $ \_ cc h _ ctx pl nl ls is si →
    case is of
      i : tl | !ih ← T.unsafeHead i, p ih
             , !it ← T.unsafeTail i, !itIsNull ← T.null it
             → updateLines i ih itIsNull nl ls $ \nl' ls' →
                 cc ih ctx nl nl' ls'
                    (if itIsNull then tl else it : tl) si
      _ : _ → h (Error nl ctx "Unexpected input") ctx pl nl ls is si
      [] → go
        where
          go = ParserCont
                 (\i → case T.uncons i of
                         Just (!ih, it) | p ih, !itIsNull ← T.null it →
                           forceUpdateLines i ih itIsNull nl ls $ \nl' ls' →
                             cc ih ctx nl nl' ls'
                                (if itIsNull then [] else [it])
                                (siSave si i)
                         Just _ → h (Error nl ctx "Unexpected input")
                                    ctx pl nl ls [i] (siSave si i)
                         Nothing → go)
                 (starveParser $ h (Error nl ctx "Unexpected end of input")
                                   ctx pl nl ls [] si)
  char c = satisfy (== c) <?> ("A " ++ show c)
  notChar c = satisfy (/= c) <?> ("Not a " ++ show c)
  anyChar = Parser $ \_ cc h _ ctx pl nl ls is si →
    let ctx' = "Any character" : ctx in
      case is of
        i : tl | !ih ← T.unsafeHead i
               , !it ← T.unsafeTail i , !itIsNull ← T.null it
               → updateLines i ih itIsNull nl ls $ \nl' ls' →
                   cc ih ctx' nl nl' ls'
                      (if itIsNull then tl else it : tl) si
        [] → go
          where
            go = ParserCont
                   (\i → case T.uncons i of
                           Just (!ih, it) | !itIsNull ← T.null it →
                             forceUpdateLines i ih itIsNull nl ls $ \nl' ls' →
                               cc ih ctx' nl nl' ls'
                                  (if itIsNull then [] else [it])
                                  (siSave si i)
                           Nothing → go)
                   (starveParser $ h (Error nl ctx' "Unexpected end of input")
                                     ctx' pl nl ls [] si)

instance α ~ String ⇒ IsString (Parser α) where
  fromString = string
  {-# INLINE fromString #-}

-- | Parsers that provide location information.
class CharParsing p ⇒ LocParsing p where
  -- | Parser location type.
  type ParserLoc p
  -- | The current location.
  location ∷ p (ParserLoc p)
  default location ∷ (MonadTrans t, Monad m, LocParsing m, p ~ t m, ParserLoc p ~ ParserLoc m) ⇒ p (ParserLoc p)
  location = lift location
  -- | Attach the starting location to the parsed value.
  located  ∷ p α → p (Located (ParserLoc p) α)
  -- | Attach the spanned location to the parsed value.
  spanned  ∷ p α → p (Located (Span (ParserLoc p)) α)

-- | Parsers with resettable line numbers.
class LocParsing p ⇒ ResetLineParsing p where
  -- | Reset the current line number and return the text lines fully consumed
  --   by the parser so far.
  resetLineNr ∷ Word → p (Seq Text)
  default resetLineNr ∷ (MonadTrans t, Monad m, ResetLineParsing m, p ~ t m) ⇒ Word → p (Seq Text)
  resetLineNr = lift . resetLineNr

instance LocParsing Parser where
  type ParserLoc Parser = LineCol
  location = Parser $ \c _ _ _ ctx pl nl → c nl ctx pl nl
  {-# INLINE location #-}
  located (Parser p) = Parser $ \c cc h ch ctx pl nl →
                         p (c . Located nl) (cc . Located nl) h ch ctx pl nl
  {-# INLINE located #-}
  spanned (Parser p) = Parser $ \c cc h ch ctx pl nl →
    p (\a ctx' pl' → c (Located (Span nl (max nl pl')) a) ctx' pl')
      (\a ctx' pl' → cc (Located (Span nl (max nl pl')) a) ctx' pl')
      h ch ctx pl nl
  {-# INLINABLE spanned #-}

instance ResetLineParsing Parser where
  resetLineNr ln =
    Parser $ \c _ _ _ ctx _ nl ls@(AccLines {..}) →
      let col = locCol nl in
        c lsLines ctx (LineCol ln (col - 1)) (LineCol ln col)
          (ls { lsLines = Seq.empty })

instance (MonadPlus p, LocParsing p) ⇒ LocParsing (IdentityT p) where
  type ParserLoc (IdentityT p) = ParserLoc p
  located (IdentityT p) = IdentityT $ located p
  spanned (IdentityT p) = IdentityT $ spanned p

instance (MonadPlus p, ResetLineParsing p) ⇒ ResetLineParsing (IdentityT p) where

instance (MonadPlus p, LocParsing p) ⇒ LocParsing (ReaderT r p) where
  type ParserLoc (ReaderT r p) = ParserLoc p
  located (ReaderT p) = ReaderT $ located . p
  spanned (ReaderT p) = ReaderT $ spanned . p

instance (MonadPlus p, ResetLineParsing p) ⇒ ResetLineParsing (ReaderT r p) where

instance (Monoid w, MonadPlus p, LocParsing p)
         ⇒ LocParsing (Lazy.WriterT w p) where
  type ParserLoc (Lazy.WriterT w p) = ParserLoc p
  located (Lazy.WriterT p) = Lazy.WriterT $ do
                               Located l (a, w) ← located p
                               return (Located l a, w)
  spanned (Lazy.WriterT p) = Lazy.WriterT $ do
                               Located l (a, w) ← spanned p
                               return (Located l a, w)

instance (Monoid w, MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Lazy.WriterT w p) where

instance (Monoid w, MonadPlus p, LocParsing p)
         ⇒ LocParsing (Strict.WriterT w p) where
  type ParserLoc (Strict.WriterT w p) = ParserLoc p
  located (Strict.WriterT p) = Strict.WriterT $ do
                                 Located l (a, w) ← located p
                                 return (Located l a, w)
  spanned (Strict.WriterT p) = Strict.WriterT $ do
                                 Located l (a, w) ← spanned p
                                 return (Located l a, w)

instance (Monoid w, MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Strict.WriterT w p) where

instance (MonadPlus p, LocParsing p) ⇒ LocParsing (Lazy.StateT s p) where
  type ParserLoc (Lazy.StateT s p) = ParserLoc p
  located (Lazy.StateT p) = Lazy.StateT $ \s → do
                              Located l (a, s') ← located (p s)
                              return (Located l a, s')
  spanned (Lazy.StateT p) = Lazy.StateT $ \s → do
                              Located l (a, s') ← spanned (p s)
                              return (Located l a, s')

instance (MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Lazy.StateT s p) where

instance (MonadPlus p, LocParsing p) ⇒ LocParsing (Strict.StateT s p) where
  type ParserLoc (Strict.StateT s p) = ParserLoc p
  located (Strict.StateT p) = Strict.StateT $ \s → do
                                Located l (a, s') ← located (p s)
                                return (Located l a, s')
  spanned (Strict.StateT p) = Strict.StateT $ \s → do
                                Located l (a, s') ← spanned (p s)
                                return (Located l a, s')

instance (MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Strict.StateT s p) where

instance (Monoid w, MonadPlus p, LocParsing p)
         ⇒ LocParsing (Lazy.RWST r w s p) where
  type ParserLoc (Lazy.RWST r w s p) = ParserLoc p
  located (Lazy.RWST p) = Lazy.RWST $ \r s → do
                            Located l (a, w, s') ← located (p r s)
                            return (Located l a, w, s')
  spanned (Lazy.RWST p) = Lazy.RWST $ \r s → do
                            Located l (a, w, s') ← spanned (p r s)
                            return (Located l a, w, s')

instance (Monoid w, MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Lazy.RWST r w s p) where

instance (Monoid w, MonadPlus p, LocParsing p)
         ⇒ LocParsing (Strict.RWST r w s p) where
  type ParserLoc (Strict.RWST r w s p) = ParserLoc p
  located (Strict.RWST p) = Strict.RWST $ \r s → do
                              Located l (a, w, s') ← located (p r s)
                              return (Located l a, w, s')
  spanned (Strict.RWST p) = Strict.RWST $ \r s → do
                              Located l (a, w, s') ← spanned (p r s)
                              return (Located l a, w, s')

instance (Monoid w, MonadPlus p, ResetLineParsing p)
         ⇒ ResetLineParsing (Strict.RWST r w s p) where
