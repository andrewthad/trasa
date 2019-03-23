{-# LANGUAGE LambdaCase #-}
module Trasa.TH.Parse where

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import Data.Bifunctor (first)
import Language.Haskell.TH (Name,mkName)
import Control.Applicative ((<|>))
import Control.Monad (void)
import Data.Void (Void)
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char.Lexer as L

import Trasa.TH.Types
import Trasa.TH.Lexer

import Debug.Trace

type Parser = MP.Parsec (MP.ErrorFancy Void) Stream

wrongToken :: a -> S.Set (MP.ErrorItem a)
wrongToken t = S.singleton (MP.Tokens (t NE.:| []))

space :: Parser ()
space = flip MP.token (wrongToken $ LexemeSpace 0) $ \case
  LexemeSpace _ -> Just ()
  other -> Nothing

optionalSpace :: Parser ()
optionalSpace = void (MP.optional space)

string :: Parser String
string = flip MP.token (wrongToken (LexemeString 0 "")) $ \case
  LexemeString _ str -> Just str
  other -> Nothing

name :: Parser Name
name = fmap mkName string

match :: Lexeme -> Parser ()
match lexeme = flip MP.token (wrongToken lexeme) $ \other -> 
  if lexeme == other
  then Just ()
  else Nothing

matchChar :: ReservedChar -> Parser ()
matchChar = match . LexemeChar

newline :: Parser ()
newline = matchChar ReservedCharNewline

colon :: Parser ()
colon = matchChar ReservedCharColon

slash :: Parser ()
slash = matchChar ReservedCharSlash

questionMark :: Parser ()
questionMark = matchChar ReservedCharQuestionMark

ampersand :: Parser ()
ampersand = matchChar ReservedCharAmpersand

equal :: Parser ()
equal = matchChar ReservedCharEqual

bracket :: Parser a -> Parser a
bracket = MP.between (matchChar ReservedCharOpenBracket) (matchChar ReservedCharCloseBracket)

comma :: Parser ()
comma = matchChar ReservedCharComma

capture :: Parser (CaptureRep Name)
capture =
  fmap MatchRep string <|>
  fmap CaptureRep (colon *> name)

query :: Parser [QueryRep Name]
query = MP.sepBy (QueryRep <$> string <*> paramRep) ampersand
  where
    paramRep = MP.choice [ fmap OptionalRep optional, fmap ListRep list, pure FlagRep ]
    optional = MP.try (equal *> name)
    list = equal *> bracket name

list :: Parser a -> Parser [a]
list val = bracket (MP.sepBy val (optionalSpace *> comma <* optionalSpace))

response :: Parser (NE.NonEmpty Name)
response = list name >>= \case
  [] -> fail "Response requires at least one response type in the list"
  (n : ns) -> pure (n NE.:| ns)

routeRep :: Parser (RouteRep Name)
routeRep = do
  optionalSpace
  routeId <- string
  space
  method <- string
  space
  slash
  caps <- MP.sepBy capture slash
  qrys <- questionMark *> query <|> return []
  space
  req  <- list name
  space
  res  <- response
  optionalSpace
  newline
  return (RouteRep routeId method caps qrys req res)

routesRep :: Parser (RoutesRep Name)
routesRep = do
  optionalSpace
  void (MP.optional newline)
  optionalSpace
  match (LexemeSymbol ReservedSymbolDataType)
  colon
  optionalSpace
  dataType <- string
  newline
  routes <- MP.many routeRep
  return (RoutesRep dataType routes)

parseRoutesRep :: String -> Either String (RoutesRep Name)
parseRoutesRep str = do
  tokens <- first MP.errorBundlePretty (MP.parse stream "" str)
  first MP.errorBundlePretty (MP.parse routesRep "" (traceShowId tokens))
