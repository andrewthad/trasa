{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Trasa.Core
  (
  -- * Types
    Bodiedness(..)
  , Content(..)
  , Payload(..)
  , Router
  -- ** Existential
  , Prepared(..)
  , PreparedUrl(..)
  , Concealed(..)
  , Constructed(..)
  , conceal
  , concealedToPrepared
  , mapConstructed
  -- * Request Types
  -- ** Method
  , Method
  , encodeMethod
  , decodeMethod
  -- ** Queries
  , QueryString(..)
  , encodeQuery
  , decodeQuery
  -- ** Url
  , Url(..)
  , encodeUrl
  , decodeUrl
  , encodeUrlPieces
  -- ** Errors
  , TrasaErr(..)
  , status
  -- * Using Routes
  , prepareWith
  , prepareUrlWith
  , linkWith
  , linkUrlWith
  , dispatchWith
  , parseWith
  , payloadWith
  , requestWith
  , routerWith
  -- * Defining Routes
  -- ** Path
  , Path(..)
  , match
  , capture
  , end
  , (./)
  , mapPath
  , appendPath
  -- ** Query
  , Param(..)
  , Query(..)
  , Parameter(..)
  , Rec(..)
  , demoteParameter
  , flag
  , required
  , optional
  , list
  , qend
  , (.&)
  , mapQuery
  -- ** Request Body
  , RequestBody(..)
  , body
  , bodyless
  , encodeRequestBody
  , decodeRequestBody
  , mapRequestBody
  -- ** Response Body
  , ResponseBody(..)
  , resp
  , encodeResponseBody
  , decodeResponseBody
  , mapResponseBody
  -- ** Many
  , Many(..)
  , one
  , mapMany
  -- ** Meta
  , Meta(..)
  , MetaBuilder
  , metaBuilderToMetaCodec
  , MetaCodec
  , MetaClient
  , metaCodecToMetaClient
  , MetaServer
  , metaCodecToMetaServer
  , mapMetaPath
  , mapMetaQuery
  , mapMetaRequestBody
  , mapMetaResponseBody
  , mapMeta
  -- * Codecs
  , CaptureEncoding(..)
  , HasCaptureEncoding(..)
  , CaptureDecoding(..)
  , HasCaptureDecoding(..)
  , CaptureCodec(..)
  , HasCaptureCodec(..)
  , BodyEncoding(..)
  , HasBodyEncoding(..)
  , BodyDecoding(..)
  , HasBodyDecoding(..)
  , BodyCodec(..)
  , HasBodyCodec(..)
    -- ** Converting Codecs
  , captureCodecToCaptureEncoding
  , captureCodecToCaptureDecoding
  , bodyCodecToBodyEncoding
  , bodyCodecToBodyDecoding
  -- ** Type Class based Codecs
  , showReadCaptureCodec
  , showReadBodyCodec
  -- * Argument Currying
  , ParamBase
  , Arguments
  , UrlPieces
  , handler
  -- * Helpers
  , prettyRouter
  , generateAllRoutes
  ) where

import Control.Applicative (liftA2)
import Control.Monad (unless)
import Data.Bifunctor (first,bimap)
import Data.Foldable (toList)
import Data.Functor.Identity (Identity(..))
import Data.HashMap.Strict (HashMap)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (mapMaybe,listToMaybe,isJust,fromMaybe)
import Language.Haskell.TH.Syntax (Name,Q,Dec,TyVarBndr(..))
import Topaz.Types (Rec(..), type (++))
import qualified Data.ByteString.Lazy as LBS
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Semigroup as SG
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Language.Haskell.TH.Datatype as THD
import qualified Language.Haskell.TH.Syntax as TH
import qualified Network.HTTP.Media.Accept as N
import qualified Network.HTTP.Media.MediaType as N
import qualified Network.HTTP.Types.Status as N
import qualified Topaz.Rec as Topaz

import Trasa.Method
import Trasa.Url
import Trasa.Error
import Trasa.Codec

-- $setup
-- >>> :set -XTypeInType

newtype Many f a = Many { getMany :: NonEmpty (f a) }
  deriving (Functor)

instance Applicative f => Applicative (Many f) where
  pure = Many . pure . pure
  Many mf <*> Many mx = Many $ liftA2 (<*>) mf mx

one :: f a -> Many f a
one = Many . pure

mapMany :: (forall x. f x -> g x) -> Many f a -> Many g a
mapMany eta (Many m) = Many (fmap eta m)

-- | the type of the HTTP message body (json, text, etc) <https://en.wikipedia.org/wiki/HTTP_message_body>
data Bodiedness = forall a. Body a | Bodyless

data RequestBody :: (Type -> Type) -> Bodiedness -> Type where
  RequestBodyPresent :: !(f a) -> RequestBody f ('Body a)
  RequestBodyAbsent :: RequestBody f 'Bodyless

body :: rqf req -> RequestBody rqf ('Body req)
body = RequestBodyPresent

bodyless :: RequestBody rqf 'Bodyless
bodyless = RequestBodyAbsent

mapRequestBody :: (forall x. rqf x -> rqf' x) -> RequestBody rqf request -> RequestBody rqf' request
mapRequestBody _ RequestBodyAbsent = RequestBodyAbsent
mapRequestBody f (RequestBodyPresent reqBod) = RequestBodyPresent (f reqBod)

newtype ResponseBody rpf response = ResponseBody { getResponseBody :: rpf response }

resp :: rpf resp -> ResponseBody rpf resp
resp = ResponseBody

mapResponseBody :: (forall x. rpf x -> rpf' x) -> ResponseBody rpf request -> ResponseBody rpf' request
mapResponseBody f (ResponseBody resBod) = ResponseBody (f resBod)

data Path :: (Type -> Type) -> [Type] -> Type where
  PathNil :: Path cap '[]
  PathConsCapture :: !(cap a) -> !(Path cap as) -> Path cap (a ': as)
  PathConsMatch :: !T.Text -> !(Path cap as) -> Path cap as

-- | flipped ($), useful for constructing routes. e.g.
-- >  match "add" ./ capture int ./ capture int ./ end
infixr 7 ./
(./) :: (a -> b) -> a -> b
(./) f a = f a

match :: T.Text -> Path cpf caps -> Path cpf caps
match = PathConsMatch

capture :: cpf cap -> Path cpf caps -> Path cpf (cap ': caps)
capture = PathConsCapture

end :: Path cpf '[]
end = PathNil

mapPath :: (forall x. cf x -> cf' x) -> Path cf ps -> Path cf' ps
mapPath _ PathNil = PathNil
mapPath f (PathConsMatch s pnext) = PathConsMatch s (mapPath f pnext)
mapPath f (PathConsCapture c pnext) = PathConsCapture (f c) (mapPath f pnext)

appendPath :: Path f as -> Path f bs -> Path f (as ++ bs)
appendPath PathNil bs = bs
appendPath (PathConsMatch a as) bs = PathConsMatch a (appendPath as bs)
appendPath (PathConsCapture cas as) bs = PathConsCapture cas (appendPath as bs)

data Param
  = Flag
  | forall a. Required a
  | forall a. Optional a
  | forall a. List a

data Parameter :: Param -> Type where
  ParameterFlag :: !Bool -> Parameter 'Flag
  ParameterRequired :: !a -> Parameter ('Required a)
  ParameterOptional :: !(Maybe a) -> Parameter ('Optional a)
  ParameterList :: ![a] -> Parameter ('List a)

data Query :: (Type -> Type) -> Param -> Type where
  QueryFlag :: !T.Text -> Query cap 'Flag
  QueryRequired :: !T.Text -> !(cap a) -> Query cap ('Required a)
  QueryOptional :: !T.Text -> !(cap a) -> Query cap ('Optional a)
  QueryList :: !T.Text -> !(cap a) -> Query cap ('List a)

flag :: T.Text -> Query cpf 'Flag
flag = QueryFlag

required :: T.Text -> cpf query -> Query cpf ('Required query)
required = QueryRequired

optional :: T.Text -> cpf query -> Query cpf ('Optional query)
optional = QueryOptional

list :: T.Text -> cpf query -> Query cpf ('List query)
list = QueryList

qend :: Rec (Query qpf) '[]
qend = RecNil

infixr 7 .&

(.&) :: Query qpf q -> Rec (Query qpf) qs -> Rec (Query qpf) (q ': qs)
(.&) = RecCons

mapQuery :: (forall x. f x -> g x) -> Rec (Query f) qs -> Rec (Query g) qs
mapQuery eta = Topaz.map $ \case
  QueryFlag key -> QueryFlag key
  QueryRequired key query -> QueryRequired key (eta query)
  QueryOptional key query -> QueryOptional key (eta query)
  QueryList key query -> QueryList key (eta query)

data Meta capCodec qryCodec reqCodec respCodec caps qrys req resp = Meta
  { metaPath :: !(Path capCodec caps)
  , metaQuery :: !(Rec (Query qryCodec) qrys)
  , metaRequestBody :: !(RequestBody reqCodec req)
  , metaResponseBody :: !(ResponseBody respCodec resp)
  , metaMethod :: !Method
  }

mapMetaPath
  :: (forall x. cf x -> cg x)
  -> Meta cf qryCodec reqCodec respCodec caps qrys req resp
  -> Meta cg qryCodec reqCodec respCodec caps qrys req resp
mapMetaPath eta m = m { metaPath = mapPath eta (metaPath m) }

mapMetaQuery
  :: (forall x. qf x -> qg x)
  -> Meta capCodec qf reqCodec respCodec caps qrys req resp
  -> Meta capCodec qg reqCodec respCodec caps qrys req resp
mapMetaQuery eta m = m { metaQuery = mapQuery eta (metaQuery m) }

mapMetaRequestBody
  :: (forall x. rf x -> rg x)
  -> Meta capCodec qryCodec rf respCodec caps qrys req resp
  -> Meta capCodec qryCodec rg respCodec caps qrys req resp
mapMetaRequestBody eta m = m { metaRequestBody = mapRequestBody eta (metaRequestBody m) }

mapMetaResponseBody
  :: (forall x. rf x -> rg x)
  -> Meta capCodec qryCodec reqCodec rf caps qrys req resp
  -> Meta capCodec qryCodec reqCodec rg caps qrys req resp
mapMetaResponseBody eta m = m { metaResponseBody = mapResponseBody eta (metaResponseBody m)}

mapMeta
  :: (forall x. capCodec1 x -> capCodec2 x)
  -> (forall x. qryCodec1 x -> qryCodec2 x)
  -> (forall x. reqCodec1 x -> reqCodec2 x)
  -> (forall x. respCodec1 x -> respCodec2 x)
  -> Meta capCodec1 qryCodec1 reqCodec1 respCodec1 caps qrys req resp
  -> Meta capCodec2 qryCodec2 reqCodec2 respCodec2 caps qrys req resp
mapMeta mapCaps mapQrys mapReq mapResp (Meta caps qrys req res method) = Meta
  (mapPath mapCaps caps)
  (mapQuery mapQrys qrys)
  (mapRequestBody mapReq req)
  (mapResponseBody mapResp res)
  method

type MetaBuilder = Meta CaptureCodec CaptureCodec BodyCodec BodyCodec

-- | This function is a more general way to transform 'MetaBuilder' into 'MetaCodec'.
--
--   It wraps the req and resp codecs in Many.
metaBuilderToMetaCodec
  :: Meta capCodec qryCodec reqCodec respCodec caps qrys req resp
  -> Meta capCodec qryCodec (Many reqCodec) (Many respCodec) caps qrys req resp
metaBuilderToMetaCodec (Meta path query reqBody respBody method) = Meta
  path
  query
  (mapRequestBody one reqBody)
  (mapResponseBody one respBody)
  method

type MetaCodec = Meta CaptureCodec CaptureCodec (Many BodyCodec) (Many BodyCodec)

type MetaClient = Meta CaptureEncoding CaptureEncoding (Many BodyEncoding) (Many BodyDecoding)

metaCodecToMetaClient :: MetaCodec caps qrys req resp -> MetaClient caps qrys req resp
metaCodecToMetaClient = mapMeta captureEncoding captureEncoding (mapMany bodyEncoding) (mapMany bodyDecoding)

type MetaServer = Meta CaptureDecoding CaptureDecoding (Many BodyDecoding) (Many BodyEncoding)

metaCodecToMetaServer :: MetaCodec caps qrys req resp -> MetaServer caps qrys req resp
metaCodecToMetaServer = mapMeta captureDecoding captureDecoding (mapMany bodyDecoding) (mapMany bodyEncoding)

-- | Generate a @Url@ for use in hyperlinks.
linkWith
  :: forall route response reqCodec respCodec
  .  (forall caps qrys req resp. route caps qrys req resp -> Meta CaptureEncoding CaptureEncoding reqCodec respCodec caps qrys req resp)
  -> Prepared route response
  -- ^ The route to encode
  -> Url
linkWith toMeta (Prepared route captures querys _) =
  encodeUrlPieces (metaPath m) (metaQuery m) captures querys
  where m = toMeta route

linkUrlWith
  :: forall route reqCodec respCodec
  .  (forall caps qrys req resp. route caps qrys req resp -> Meta CaptureEncoding CaptureEncoding reqCodec respCodec caps qrys req resp)
  -> PreparedUrl route
  -- ^ The route to encode
  -> Url
linkUrlWith toMeta (PreparedUrl route captures querys) =
  encodeUrlPieces (metaPath m) (metaQuery m) captures querys
  where m = toMeta route

data Payload = Payload
  { payloadUrl :: !Url
  , payloadContent :: !(Maybe Content)
  , payloadAccepts :: !(NonEmpty N.MediaType)
  }

-- | Only useful for library authors
payloadWith
  :: forall route response
  .  (forall caps qrys req resp. route caps qrys req resp -> MetaClient caps qrys req resp)
  -> Prepared route response
  -- ^ The route to be payload encoded
  -> Payload
payloadWith toMeta p@(Prepared route _ _ reqBody) =
  Payload url content accepts
  where
    url = linkWith toMeta p
    m = toMeta route
    content = encodeRequestBody (metaRequestBody m) reqBody
    ResponseBody (Many decodings) = metaResponseBody m
    accepts = bodyDecodingNames =<< decodings

-- Only useful to implement packages like 'trasa-client'
requestWith
  :: Functor m
  => (forall caps qrys req resp. route caps qrys req resp -> MetaClient caps qrys req resp)
  -> (Method -> Url -> Maybe Content -> NonEmpty N.MediaType -> m (Either TrasaErr Content))
  -- ^ method, url, content, accepts -> response
  -> Prepared route response
  -> m (Either TrasaErr response)
requestWith toMeta run (Prepared route captures querys reqBody) =
  let m = toMeta route
      method = metaMethod m
      url = encodeUrlPieces (metaPath m) (metaQuery m) captures querys
      content = encodeRequestBody (metaRequestBody m) reqBody
      respBodyDecs@(ResponseBody (Many decodings)) = metaResponseBody m
      accepts = bodyDecodingNames =<< decodings
   in fmap (\c -> c >>= decodeResponseBody respBodyDecs) (run method url content accepts)

encodeRequestBody :: RequestBody (Many BodyEncoding) request -> RequestBody Identity request -> Maybe Content
encodeRequestBody RequestBodyAbsent RequestBodyAbsent = Nothing
encodeRequestBody (RequestBodyPresent (Many encodings)) (RequestBodyPresent (Identity rq)) =
  case NE.head encodings of
    BodyEncoding names encoding -> Just (Content (Just $NE.head names) (encoding rq))

decodeRequestBody
  :: RequestBody (Many BodyDecoding) req
  -> Maybe Content
  -> Either TrasaErr (RequestBody Identity req)
decodeRequestBody reqDec mcontent = case reqDec of
  RequestBodyPresent decs -> case mcontent of
    Nothing -> wrongBody
    Just (Content media bod) -> case media of
      Nothing -> let nel = getMany decs in go (toList nel) (NE.head $ bodyDecodingNames $ NE.head nel) bod
      Just m -> go (toList (getMany decs)) m bod
  RequestBodyAbsent -> case mcontent of
    Nothing -> Right RequestBodyAbsent
    Just (Content _ bod) -> if LBS.null bod
      then Right RequestBodyAbsent
      else wrongBody
  where
    wrongBody = Left (status N.status415)
    go :: [BodyDecoding a] -> N.MediaType -> LBS.ByteString -> Either TrasaErr (RequestBody Identity ('Body a))
    go [] _ _ = Left (status N.status415)
    go (BodyDecoding medias dec:decs) media bod = case any (flip mediaMatches media) medias of
      True -> bimap (TrasaErr N.status415 . LBS.fromStrict . T.encodeUtf8)
                    (RequestBodyPresent . Identity)
                    (dec bod)
      False -> go decs media bod

mediaMatches :: N.MediaType -> N.MediaType -> Bool
mediaMatches _ "*/*" = True
mediaMatches "*/*" _ = True
mediaMatches x y = N.matches x y

encodeResponseBody
  :: forall response
  .  [N.MediaType]
  -> ResponseBody (Many BodyEncoding) response
  -> response
  -> Either TrasaErr Content
encodeResponseBody medias (ResponseBody encs) res = go (toList (getMany encs))
  where
    go :: [BodyEncoding response] -> Either TrasaErr Content
    go [] = Left (status N.status406)
    go (BodyEncoding accepts e:es) = case acceptable (toList accepts) medias of
      Just typ -> Right (Content (Just typ) (e res))
      Nothing  -> go es
    acceptable :: [N.MediaType] -> [N.MediaType] -> Maybe N.MediaType
    acceptable [] _ = Nothing
    acceptable (a:as) ms = case any (N.matches a) ms of
      True  -> Just a
      False -> acceptable as ms

decodeResponseBody :: ResponseBody (Many BodyDecoding) response -> Content -> Either TrasaErr response
decodeResponseBody (ResponseBody (Many decodings)) (Content mname content) = go (toList decodings)
  where
    name = fromMaybe (NE.head $ bodyDecodingNames $ NE.head decodings) mname
    go :: [BodyDecoding response] -> Either TrasaErr response
    go [] = Left (status N.status415)
    go (BodyDecoding names dec:decs) = case any (N.matches name) names of
      True -> first (TrasaErr N.status400 . LBS.fromStrict . T.encodeUtf8) (dec content)
      False -> go decs

encodeUrlPieces
  :: Path CaptureEncoding captures
  -> Rec (Query CaptureEncoding) querys
  -> Rec Identity captures
  -> Rec Parameter querys
  -> Url
encodeUrlPieces pathEncoding queryEncoding path querys =
  Url (encodePath pathEncoding path) (QueryString (encodeQueries queryEncoding querys))
  where
    encodePath
      :: forall caps
      .  Path CaptureEncoding caps
      -> Rec Identity caps
      -> [T.Text]
    encodePath PathNil RecNil = []
    encodePath (PathConsMatch str ps) xs = str : encodePath ps xs
    encodePath (PathConsCapture (CaptureEncoding enc) ps) (Identity x `RecCons` xs) = enc x : encodePath ps xs
    encodeQueries
      :: forall qrys
      .  Rec (Query CaptureEncoding) qrys
      -> Rec Parameter qrys
      -> HM.HashMap T.Text QueryParam
    encodeQueries RecNil RecNil = HM.empty
    encodeQueries (QueryFlag key `RecCons` encs) (ParameterFlag on `RecCons` qs) =
      if on then HM.insert key QueryParamFlag rest else rest
      where rest = encodeQueries encs qs
    encodeQueries (QueryRequired key (CaptureEncoding enc) `RecCons` encs) (ParameterRequired val `RecCons` qs) =
      HM.insert key (QueryParamSingle (enc val)) rest
      where rest = encodeQueries encs qs
    encodeQueries (QueryOptional key (CaptureEncoding enc) `RecCons` encs) (ParameterOptional mval `RecCons` qs) =
      maybe rest (\val -> HM.insert key (QueryParamSingle (enc val)) rest) mval
      where rest = encodeQueries encs qs
    encodeQueries (QueryList key (CaptureEncoding enc) `RecCons` encs) (ParameterList vals `RecCons` qs) =
       HM.insert key (QueryParamList (fmap enc vals)) (encodeQueries encs qs)

-- | Only useful to implement packages like 'trasa-server'
dispatchWith
  :: forall route m
  .  Applicative m
  => (forall caps qrys req resp. route caps qrys req resp -> MetaServer caps qrys req resp)
  -> (forall caps qrys req resp. route caps qrys req resp -> Rec Identity caps -> Rec Parameter qrys -> RequestBody Identity req -> m resp)
  -> Router route -- ^ Router
  -> Method -- ^ Method
  -> [N.MediaType] -- ^ Accept headers
  -> Url -- ^ Everything after the authority
  -> Maybe Content -- ^ Content type and request body
  -> m (Either TrasaErr Content) -- ^ Encoded response
dispatchWith toMeta makeResponse madeRouter method accepts url mcontent =
  case parseWith toMeta madeRouter method url mcontent of
    Left err -> pure (Left err)
    Right (Concealed route path querys reqBody) ->
      encodeResponseBody accepts (metaResponseBody (toMeta route)) <$>
      makeResponse route path querys reqBody

-- | Build a router from all the possible routes, and methods to turn routes into needed metadata
routerWith
  :: forall route qryCodec reqCodec respCodec
  .  (forall caps qrys req resp. route caps qrys req resp -> Meta CaptureDecoding qryCodec reqCodec respCodec caps qrys req resp)
  -> [Constructed route]
  -> Router route
routerWith toMeta = Router . foldMap buildRouter
  where
    buildRouter :: Constructed route -> IxedRouter route 'Z
    buildRouter (Constructed route) = singletonIxedRouter route (metaMethod m) (metaPath m)
      where m = toMeta route


-- | Parses the path, the querystring, and the request body.
parseWith
  :: forall route capCodec respCodec
  .  (forall caps qrys req resp. route caps qrys req resp -> Meta capCodec CaptureDecoding (Many BodyDecoding) respCodec caps qrys req resp)
  -> Router route -- ^ Router
  -> Method -- ^ Request Method
  -> Url -- ^ Everything after the authority
  -> Maybe Content -- ^ Request content type and body
  -> Either TrasaErr (Concealed route)
parseWith toMeta madeRouter method (Url encodedPath encodedQuery) mcontent = do
  Pathed route captures <- parsePathWith madeRouter method encodedPath
  let m = toMeta route
  querys <- parseQueryWith (metaQuery m) encodedQuery
  reqBody <- decodeRequestBody (metaRequestBody m) mcontent
  pure (Concealed route captures querys reqBody)

-- | Parses only the path.
parsePathWith :: forall route.
     Router route
  -> Method -- ^ Method
  -> [T.Text] -- ^ Path Pieces
  -> Either TrasaErr (Pathed route)
parsePathWith (Router r0) method pieces0 = go VecNil pieces0 r0
  where
  go :: forall n.
        Vec n T.Text -- captures being accumulated
     -> [T.Text] -- remaining pieces
     -> IxedRouter route n -- router fragment
     -> Either TrasaErr (Pathed route)
  go captures ps (IxedRouter matches mcapture responders) = case ps of
    [] -> case HM.lookup (encodeMethod method) responders of
      Nothing -> Left (status N.status405)
      Just respondersAtMethod -> fromMaybe (Left (status N.status400)) . listToMaybe $
        ( mapMaybe
            (\(IxedResponder route capDecs) ->
                 fmap (\x -> (Right (Pathed route x))) (decodeCaptureVector capDecs captures)
            )
            respondersAtMethod
        )
    (p:psNext) ->
      let res1 = maybe [] (:[]) $ fmap (go captures psNext) (HM.lookup p matches)
          -- Since this uses snocVec to build up the captures,
          -- this algorithm's complexity includes a term that is
          -- O(n^2) in the number of captures. However, most routes
          -- that I deal with have one or two captures. Occassionally,
          -- I'll get one with four or five, but this happens
          -- so infrequently that I'm not concerned about this.
          res2 = maybe [] (:[]) $ fmap (go (snocVec p captures) psNext) mcapture
       in fromMaybe (Left (status N.status400)) . listToMaybe $ res1 ++ res2

parseQueryWith :: Rec (Query CaptureDecoding) querys -> QueryString -> Either TrasaErr (Rec Parameter querys)
parseQueryWith decoding (QueryString querys) = Topaz.traverse param decoding
  where
    param :: forall qry. Query CaptureDecoding qry -> Either TrasaErr (Parameter qry)
    param = \case
      QueryFlag key -> Right (ParameterFlag (HM.member key querys))
      QueryRequired key (CaptureDecoding dec) -> case HM.lookup key querys of
        Nothing -> Left (TrasaErr N.status400 "required query param is absent")
        Just query -> case query of
          QueryParamFlag -> Left (TrasaErr N.status400 "query flag given when key-value expected")
          QueryParamSingle txt -> case dec txt of
            Just dtxt -> Right (ParameterRequired dtxt)
            Nothing -> Left (TrasaErr N.status400 "failed to decode required query parameter")
          QueryParamList _ -> Left (TrasaErr N.status400 "query param list given when key-value expected")
      QueryOptional key (CaptureDecoding dec) -> case HM.lookup key querys of
        Nothing -> Right (ParameterOptional Nothing)
        Just query -> case query of
          QueryParamFlag -> Left (TrasaErr N.status400 "query flag given when key-value expected")
          QueryParamSingle txt -> Right (ParameterOptional (dec txt))
          QueryParamList _ -> Left (TrasaErr N.status400 "query param list given when key-value expected")
      QueryList key (CaptureDecoding dec) -> case HM.lookup key querys of
        Nothing -> Right (ParameterList [])
        Just query -> case query of
          QueryParamFlag -> Left (TrasaErr N.status400 "query flag given when list expected")
          QueryParamSingle txt -> Right (ParameterList (maybe [] (:[]) (dec txt)))
          QueryParamList txts -> Right (ParameterList (mapMaybe dec txts))

decodeCaptureVector ::
     IxedRec CaptureDecoding n xs
  -> Vec n T.Text
  -> Maybe (Rec Identity xs)
decodeCaptureVector IxedRecNil VecNil = Just RecNil
decodeCaptureVector (IxedRecCons (CaptureDecoding decode) rnext) (VecCons piece vnext) = do
  val <- decode piece
  vals <- decodeCaptureVector rnext vnext
  pure (Identity val `RecCons` vals)

type family ParamBase (param :: Param) :: Type where
  ParamBase 'Flag = Bool
  ParamBase ('Required a) = a
  ParamBase ('Optional a) = Maybe a
  ParamBase ('List a) = [a]

demoteParameter :: Parameter param -> ParamBase param
demoteParameter = \case
  ParameterFlag b -> b
  ParameterRequired v -> v
  ParameterOptional m -> m
  ParameterList l -> l

-- | A closed, total type family provided as a convenience to end users.
--   Other function is this library take advantage of 'Arguments' to allow
--   end users use normal function application. Without this, users would
--   need to write out 'Record' and 'RequestBody' values by hand, which
--   is tedious.
--
--   >>> :kind! Arguments '[Int,Bool] '[Flag,Optional Double,List Int] 'Bodyless Double
--   Arguments '[Int,Bool] '[Flag,Optional Double,List Int] 'Bodyless Double :: *
--   = Int -> Bool -> Bool -> Maybe Double -> [Int] -> Double
type family Arguments (pieces :: [Type]) (querys :: [Param]) (body :: Bodiedness) (result :: Type) :: Type where
  Arguments '[] '[] ('Body b) r = b -> r
  Arguments '[] '[] 'Bodyless r = r
  Arguments '[] (q ': qs) r b = ParamBase q -> Arguments '[] qs r b
  Arguments (c ': cs) qs b r = c -> Arguments cs qs b r

type family UrlPieces (pieces :: [Type]) (querys :: [Param]) (result :: Type) :: Type where
  UrlPieces '[] '[] r = r
  UrlPieces '[] (q ': qs) r = ParamBase q -> UrlPieces '[] qs r
  UrlPieces (c ': cs) qs r = c -> UrlPieces cs qs r

-- | Used my users to define a function called prepare, see tutorial
prepareWith
  :: (forall caps qrys req resp. route caps qrys req resp -> Meta capCodec qryCodec reqCodec respCodec caps qrys req resp)
  -> route captures query request response
  -- ^ The route to prepare
  -> Arguments captures query request (Prepared route response)
prepareWith toMeta route =
  prepareExplicit route (metaPath m) (metaQuery m) (metaRequestBody m)
  where m = toMeta route

prepareExplicit :: forall route captures queries request response rqf pf qf.
     route captures queries request response
  -> Path pf captures
  -> Rec (Query qf) queries
  -> RequestBody rqf request
  -> Arguments captures queries request (Prepared route response)
prepareExplicit route = go (Prepared route)
  where
  -- Adopted from: https://www.reddit.com/r/haskell/comments/67l9so/currying_a_typelevel_list/dgrghxz/
  go :: forall caps qrys z.
        (Rec Identity caps -> Rec Parameter qrys -> RequestBody Identity request -> z)
     -> Path pf caps
     -> Rec (Query qf) qrys
     -> RequestBody rqf request
     -> Arguments caps qrys request z
  go k PathNil RecNil RequestBodyAbsent =
    k RecNil RecNil RequestBodyAbsent
  go k PathNil RecNil (RequestBodyPresent _) =
    \reqBod -> k RecNil RecNil (RequestBodyPresent (Identity reqBod))
  go k PathNil (q `RecCons` qs) b =
    \qt -> go (\caps querys reqBody -> k caps (parameter q qt `RecCons` querys) reqBody) PathNil qs b
  go k (PathConsMatch _ pnext) qs b =
    go k pnext qs b
  go k (PathConsCapture _ pnext) qs b =
    \c -> go (\caps querys reqBod -> k (Identity c `RecCons` caps) querys reqBod) pnext qs b
  parameter :: forall param. Query qf param -> ParamBase param -> Parameter param
  parameter (QueryFlag _) b = ParameterFlag b
  parameter (QueryRequired _ _) v = ParameterRequired v
  parameter (QueryOptional _ _) m = ParameterOptional m
  parameter (QueryList _ _) l = ParameterList l

prepareUrlWith
  :: (forall caps qrys req resp. route caps qrys req resp -> Meta capCodec qryCodec reqCodec respCodec caps qrys req resp)
  -> route captures query request response
  -- ^ The route to prepare
  -> UrlPieces captures query (PreparedUrl route)
prepareUrlWith toMeta route =
  prepareUrlExplicit route (metaPath m) (metaQuery m)
  where m = toMeta route

prepareUrlExplicit :: forall route captures queries request response pf qf.
     route captures queries request response
  -> Path pf captures
  -> Rec (Query qf) queries
  -> UrlPieces captures queries (PreparedUrl route)
prepareUrlExplicit route = go (PreparedUrl route)
  where
  -- Adopted from: https://www.reddit.com/r/haskell/comments/67l9so/currying_a_typelevel_list/dgrghxz/
  go :: forall caps qrys z.
        (Rec Identity caps -> Rec Parameter qrys -> z)
     -> Path pf caps
     -> Rec (Query qf) qrys
     -> UrlPieces caps qrys z
  go k PathNil RecNil = k RecNil RecNil
  go k PathNil (q `RecCons` qs) =
    \qt -> go (\caps querys -> k caps (parameter q qt `RecCons` querys)) PathNil qs
  go k (PathConsMatch _ pnext) qs =
    go k pnext qs
  go k (PathConsCapture _ pnext) qs =
    \c -> go (\caps querys -> k (Identity c `RecCons` caps) querys) pnext qs
  parameter :: forall param. Query qf param -> ParamBase param -> Parameter param
  parameter (QueryFlag _) b = ParameterFlag b
  parameter (QueryRequired _ _) v = ParameterRequired v
  parameter (QueryOptional _ _) m = ParameterOptional m
  parameter (QueryList _ _) l = ParameterList l

-- | Uncurry the arguments type family
handler :: forall captures querys request x.
     Rec Identity captures
  -> Rec Parameter querys
  -> RequestBody Identity request
  -> Arguments captures querys request x
  -> x
handler = go
  where
  go :: forall caps qrys.
       Rec Identity caps
    -> Rec Parameter qrys
    -> RequestBody Identity request
    -> Arguments caps qrys request x
    -> x
  go RecNil RecNil RequestBodyAbsent f = f
  go RecNil RecNil (RequestBodyPresent (Identity b)) f = f b
  go RecNil (q `RecCons` qs) b f = go RecNil qs b (f (demoteParameter q))
  go (Identity c `RecCons` cs) qs b f = go cs qs b (f c)

-- | A route with all types hidden: the captures, the request body,
--   and the response body. This is needed so that users can
--   enumerate over all the routes.
data Constructed :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Type where
  Constructed :: !(route captures querys request response) -> Constructed route
-- I dont really like the name Constructed, but I don't want to call it
-- Some or Any since these get used a lot and a conflict would be likely.
-- Think, think, think.

mapConstructed ::
     (forall caps qrys req resp. sub caps qrys req resp -> route caps qrys req resp)
  -> Constructed sub
  -> Constructed route
mapConstructed f (Constructed sub) = Constructed (f sub)

data Pathed :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Type  where
  Pathed :: !(route captures querys request response) -> !(Rec Identity captures) -> Pathed route

-- | Includes the route, path, query parameters, and request body.
data Prepared :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Type -> Type where
  Prepared ::
       !(route captures querys request response)
    -> !(Rec Identity captures)
    -> !(Rec Parameter querys)
    -> !(RequestBody Identity request)
    -> Prepared route response

-- | Includes the route, path, query parameters
data PreparedUrl :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Type where
  PreparedUrl ::
       !(route captures querys request response)
    -> !(Rec Identity captures)
    -> !(Rec Parameter querys)
    -> PreparedUrl route

-- | Only needed to implement 'parseWith'. Most users do not need this.
--   If you need to create a route hierarchy to provide breadcrumbs,
--   then you will need this.
data Concealed :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Type where
  Concealed ::
       !(route captures querys request response)
    -> !(Rec Identity captures)
    -> !(Rec Parameter querys)
    -> !(RequestBody Identity request)
    -> Concealed route

-- | Conceal the response type.
conceal :: Prepared route response -> Concealed route
conceal (Prepared route caps querys req) = Concealed route caps querys req

concealedToPrepared
  :: forall route a
  .  Concealed route
  -> (forall resp. Prepared route resp -> a)
  -> a
concealedToPrepared (Concealed route caps qrys req) f = f (Prepared route caps qrys req)

-- | The HTTP content type and body.
data Content = Content
  { contentType :: !(Maybe N.MediaType)
  , contentData :: !LBS.ByteString
  } deriving (Show,Eq,Ord)

-- | Only promoted version used.
data Nat = S !Nat | Z

newtype Router route = Router (IxedRouter route 'Z)

data IxedRouter :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Nat -> Type where
  IxedRouter ::
       !(HashMap T.Text (IxedRouter route n))
    -> !(Maybe (IxedRouter route ('S n)))
    -> !(HashMap T.Text [IxedResponder route n]) -- Should be either zero or one, more than one means that there are trivially overlapped routes
    -> IxedRouter route n

-- | This monoid instance is provided so that we can
--   conveniently use foldMap elsewhere. We do not
--   provide a Monoid instance for Router like we do
--   for IxedRouter. End users only have one way to create
--   a router, and if they combine a Router with itself
--   using mappend, it would result in Router in which all
--   routes were overlapped.
instance Monoid (IxedRouter route n) where
  mempty = IxedRouter HM.empty Nothing HM.empty
  mappend = (SG.<>)

instance SG.Semigroup (IxedRouter route n) where
  (<>) = unionIxedRouter

data IxedResponder :: ([Type] -> [Param] -> Bodiedness -> Type -> Type) -> Nat -> Type where
  IxedResponder ::
       !(route captures query request response)
    -> !(IxedRec CaptureDecoding n captures)
    -> IxedResponder route n

data IxedRec :: (k -> Type) -> Nat -> [k] -> Type where
  IxedRecNil :: IxedRec f 'Z '[]
  IxedRecCons :: !(f r) -> !(IxedRec f n rs) -> IxedRec f ('S n) (r ': rs)

data Vec :: Nat -> Type -> Type where
  VecNil :: Vec 'Z a
  VecCons :: !a -> !(Vec n a) -> Vec ('S n) a

data IxedPath :: (Type -> Type) -> Nat -> [Type] -> Type where
  IxedPathNil :: IxedPath f 'Z '[]
  IxedPathCapture :: !(f a) -> !(IxedPath f n as) -> IxedPath f ('S n) (a ': as)
  IxedPathMatch :: !T.Text -> !(IxedPath f n a) -> IxedPath f n a

data LenPath :: Nat -> Type where
  LenPathNil :: LenPath 'Z
  LenPathCapture :: !(LenPath n) -> LenPath ('S n)
  LenPathMatch :: !T.Text -> !(LenPath n) -> LenPath n

-- Assumes length is in penultimate position.
data HideIx :: (Nat -> k -> Type) -> k -> Type where
  HideIx :: !(f n a) -> HideIx f a

-- toIxedRec :: Rec f xs -> HideIx (IxedRec f) xs
-- toIxedRec RecNil = HideIx IxedRecNil
-- toIxedRec (r `RecCons` rs) = case toIxedRec rs of
--   HideIx x -> HideIx (IxedRecCons r x)

snocVec :: a -> Vec n a -> Vec ('S n) a
snocVec a VecNil = VecCons a VecNil
snocVec a (VecCons b vnext) =
  VecCons b (snocVec a vnext)

pathToIxedPath :: Path f xs -> HideIx (IxedPath f) xs
pathToIxedPath PathNil = HideIx IxedPathNil
pathToIxedPath (PathConsCapture c pnext) =
  case pathToIxedPath pnext of
    HideIx ixed -> HideIx (IxedPathCapture c ixed)
pathToIxedPath (PathConsMatch s pnext) =
  case pathToIxedPath pnext of
    HideIx ixed -> HideIx (IxedPathMatch s ixed)

-- | Discards the static parts
ixedPathToIxedRec :: IxedPath f n xs -> IxedRec f n xs
ixedPathToIxedRec IxedPathNil = IxedRecNil
ixedPathToIxedRec (IxedPathCapture c pnext) =
  IxedRecCons c (ixedPathToIxedRec pnext)
ixedPathToIxedRec (IxedPathMatch _ pnext) =
  ixedPathToIxedRec pnext

ixedPathToLenPath :: IxedPath f n xs -> LenPath n
ixedPathToLenPath IxedPathNil = LenPathNil
ixedPathToLenPath (IxedPathCapture _ pnext) =
  LenPathCapture (ixedPathToLenPath pnext)
ixedPathToLenPath (IxedPathMatch s pnext) =
  LenPathMatch s (ixedPathToLenPath pnext)

snocLenPathMatch :: T.Text -> LenPath n -> LenPath n
snocLenPathMatch s x = case x of
  LenPathNil -> LenPathMatch s LenPathNil
  LenPathMatch t pnext -> LenPathMatch t (snocLenPathMatch s pnext)
  LenPathCapture pnext -> LenPathCapture (snocLenPathMatch s pnext)

snocLenPathCapture :: LenPath n -> LenPath ('S n)
snocLenPathCapture x = case x of
  LenPathNil -> LenPathCapture LenPathNil
  LenPathMatch t pnext -> LenPathMatch t (snocLenPathCapture pnext)
  LenPathCapture pnext -> LenPathCapture (snocLenPathCapture pnext)

reverseLenPathMatch :: LenPath n -> LenPath n
reverseLenPathMatch = go
  where
  go :: forall n. LenPath n -> LenPath n
  go LenPathNil = LenPathNil
  go (LenPathMatch s pnext) = snocLenPathMatch s (go pnext)
  go (LenPathCapture pnext) = snocLenPathCapture (go pnext)

singletonIxedRouter ::
  route captures querys request response -> Method -> Path CaptureDecoding captures -> IxedRouter route 'Z
singletonIxedRouter route method capDecs = case pathToIxedPath capDecs of
  HideIx ixedCapDecs ->
    let ixedCapDecsRec = ixedPathToIxedRec ixedCapDecs
        responder = IxedResponder route ixedCapDecsRec
        lenPath = reverseLenPathMatch (ixedPathToLenPath ixedCapDecs)
     in singletonIxedRouterHelper responder method lenPath

singletonIxedRouterHelper ::
  IxedResponder route n -> Method -> LenPath n -> IxedRouter route 'Z
singletonIxedRouterHelper responder method path =
  let r = IxedRouter HM.empty Nothing (HM.singleton (encodeMethod method) [responder])
   in singletonIxedRouterGo r path

singletonIxedRouterGo ::
  IxedRouter route n -> LenPath n -> IxedRouter route 'Z
singletonIxedRouterGo r lp = case lp of
  LenPathNil -> r
  LenPathCapture lpNext -> singletonIxedRouterGo (IxedRouter HM.empty (Just r) HM.empty) lpNext
  LenPathMatch s lpNext -> singletonIxedRouterGo (IxedRouter (HM.singleton s r) Nothing HM.empty) lpNext

unionIxedRouter :: IxedRouter route n -> IxedRouter route n -> IxedRouter route n
unionIxedRouter = go
  where
  go :: forall route n. IxedRouter route n -> IxedRouter route n -> IxedRouter route n
  go (IxedRouter matchesA captureA respsA) (IxedRouter matchesB captureB respsB) =
    IxedRouter
      (HM.unionWith go matchesA matchesB)
      (unionMaybeWith go captureA captureB)
      (HM.unionWith (++) respsA respsB)

unionMaybeWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
unionMaybeWith f x y = case x of
  Nothing -> y
  Just xval -> case y of
    Nothing -> x
    Just yval -> Just (f xval yval)

-- | Pretty prints a router, using indentation to show nesting
--   of routes under a common prefix. This also shows the request
--   methods that each route accepts. If there are any trivially
--   overlapped routes, the appends are asterisk to the method name
--   for which the routes are overlapped.
prettyRouter :: Router route -> String
prettyRouter (Router r) = L.unlines (prettyIxedRouter 0 (Nothing,r))

prettyIxedRouter ::
     Int -- ^ Indentation
  -> (Maybe String, IxedRouter route n)
  -> [String]
prettyIxedRouter indent (mnode,IxedRouter matches cap responders) =
  let spaces = L.replicate indent ' '
      nextIndent = if isJust mnode then indent + 2 else indent
      children1 = map (first (Just . ('/' : ) . T.unpack)) (HM.toList matches)
      children2 = maybe [] (\x -> [(Just "/:capture",x)]) cap
   in concat
        [ case mnode of
            Nothing -> if length responders > 0
              then ["/ " ++ showRespondersList responders]
              else []
            Just _ -> []
        , maybe [] (\x -> [x]) $ flip fmap mnode $ \node -> spaces
            ++ node
            ++ (if length responders > 0 then " " ++ showRespondersList responders else "")
        , prettyIxedRouter nextIndent =<< children1
        , prettyIxedRouter nextIndent =<< children2
        ]

showRespondersList :: HashMap T.Text [a] -> String
showRespondersList = id
  . (\x -> "[" ++ x ++ "]")
  . L.intercalate ","
  . map (\(method,xs) -> T.unpack method ++ (if L.length xs > 1 then "*" else ""))
  . HM.toList

-- | Given a route type @Route@, generate a function
--   that looks like
--
--   @
--   allRoutes :: ['Constructed' Route]
--   allRoutes = ...
--   @
--
--   Which could be useful e.g. with 'routerWith'.
--
--   This function makes two assumptions about your
--   route type:
--
--     1. It is kinded @['Type'] -> ['Param'] -> 'Bodiedness' -> 'Type' -> 'Type'@
--     2. Its value constructors have no arguments
--
--   Example:
--
--   @
--   data Route :: ['Type'] -> ['Param'] -> 'Bodiedness' -> 'Type' -> 'Type' where
--     HelloWorld   :: Route '[] '[] ''Bodyless' 'String'
--     GoodbyeWorld :: Route '[] '[] ''Bodyless' 'Data.Void.Void'
--   $(generateAllRoutes ''Route)
--   @
--
--   will generate:
--
--   @
--   allRoutes :: [Constructed Route]
--   allRoutes = [Constructed HelloWorld, Constructed GoodbyeWorld]
--   @
--
generateAllRoutes :: Name -> Q [Dec]
generateAllRoutes r = do
  d <- THD.reifyDatatype r
  hasConstructedKind (THD.datatypeVars d)
  noConstructorArgs (THD.datatypeCons d)
  let rhs = TH.ListE $ map
        (\c -> TH.AppE
          (TH.ConE 'Constructed)
          (TH.ConE (THD.constructorName c))
        )
        (THD.datatypeCons d)
  let name = TH.mkName "allRoutes"
  -- N.B: When we use mkName here instead of a tick,
  -- the generated code includes a ticked
  -- @'Constructed@ instead of just @Constructed@.
  -- Very strange, since I thought only 'PromotedT'
  -- was supposed to do that. Also, to allow for
  -- qualified imports we must fully qualify the name.
  let typ  = TH.AppT TH.ListT (TH.AppT (TH.ConT (TH.mkName "Trasa.Core.Constructed")) (TH.ConT (THD.datatypeName d)))
  let bod  = [TH.Clause [] (TH.NormalB rhs) []]
  pure [TH.SigD name typ, TH.FunD name bod]

-- Verify that the constructors all take no arguments.
noConstructorArgs :: [THD.ConstructorInfo] -> Q ()
noConstructorArgs = go
  where
    msg = "generateAllRoutes expects all"
      <> " constructors to have no arguments."

    go [] = pure ()
    go (c:cs) = case THD.constructorFields c of
      [] -> go cs
      _  -> fail msg

-- Confirm the correct kind for 'generateAllRoutes'. Verifies that
-- the type has kind
--
-- @['Type'] -> ['Param'] -> 'Bodiedness' -> 'Type' -> 'Type'@,
--
-- which is the kind that 'Constructed' needs.
hasConstructedKind :: [TyVarBndr] -> Q ()
hasConstructedKind = \case
  [captures, queries, bodiedness, response] -> do
    let correctKind = True
          && isListType captures
          && isListParam queries
          && isBodiedness bodiedness
          && isType response
    unless correctKind $ fail msg
  _ -> do
    fail msg
  where
    msg = "generateAllRoutes expects a type"
      ++ " with kind `[Type] -> [Param] -> Bodiedness"
      ++ " -> Type -> Type`."
    typeKind = TH.StarT
    paramKind = TH.ConT ''Param
    bodiednessKind = TH.ConT ''Bodiedness
    isListType = \case
      KindedTV _ (TH.AppT TH.ListT k) -> k == typeKind
      _ -> False
    isListParam = \case
      KindedTV _ (TH.AppT TH.ListT k) -> k == paramKind
      _ -> False
    isBodiedness = \case
      KindedTV _ k -> k == bodiednessKind
      _ -> False
    isType = \case
      PlainTV _ -> True
      KindedTV _ TH.StarT -> True
      _ -> False
