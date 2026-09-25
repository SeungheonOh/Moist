{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import Data.Aeson (FromJSON (parseJSON), eitherDecode, withObject, (.:))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Char (digitToInt, isHexDigit)
import Data.List (isPrefixOf)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Typeable (typeRep, typeRepTyCon, tyConPackage)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (ExBudget), ExRestrictingBudget (ExRestrictingBudget))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (ExCPU), ExMemory (ExMemory))
import PlutusCore.Evaluation.Machine.Exception (MachineError (OpenTermEvaluatedMachineError, PanicMachineError))
import PlutusCore.Flat (unflat)
import System.Exit (die)
import System.IO (hPutStrLn, stderr)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

data Request = Request String String String [String]

instance FromJSON Request where
  parseJSON = withObject "Request" $ \fields ->
    Request <$> fields .: "label" <*> fields .: "before" <*> fields .: "after" <*> fields .: "inputs"

type Term = UPLC.Term PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()

decodeHex :: String -> Either String BS.ByteString
decodeHex input
  | odd (length input) || not (all isHexDigit input) = Left "Invalid Flat hex"
  | otherwise = BS.pack <$> go input
  where
    go [] = Right []
    go (high : low : rest) = (fromIntegral (16 * digitToInt high + digitToInt low) :) <$> go rest
    go _ = Left "Invalid Flat hex length"

decode :: String -> IO Term
decode hex = do
  bytes <- either die pure (decodeHex hex)
  program <- either (die . show) (pure . UPLC.unUnrestrictedProgram) (unflat bytes)
  let UPLC.Program () version term = program
  unless (version == UPLC.Version 1 1 0) $ die "Expected UPLC 1.1.0"
  pure term

unit :: Term
unit = UPLC.Constant () (PLC.Some (PLC.ValueOf PLC.DefaultUniUnit ()))

observe :: Term -> Term -> Int -> Term
observe script argument context =
  let applied = UPLC.Apply () script argument
      consumed = case context of
        0 -> applied
        1 -> UPLC.Force () applied
        2 -> UPLC.Apply () applied (UPLC.Constant () (PLC.Some (PLC.ValueOf PLC.DefaultUniBool True)))
        _ -> UPLC.Case () applied (pure unit <> pure (UPLC.Error ()))
   in UPLC.Apply () (UPLC.LamAbs () (PLC.DeBruijn 0) unit) consumed

evaluate :: Term -> Either String (Bool, [Text])
evaluate term =
  let budget = ExBudget (ExCPU 10000000000) (ExMemory 10000000)
      Cek.CekReport result _ logs = Cek.runCekDeBruijn defaultCekParametersForTesting
        (Cek.restricting (ExRestrictingBudget budget)) Cek.logEmitter
        (UPLC.termMapNames UPLC.fakeNameDeBruijn term)
   in case Cek.cekResultToEither result of
        Right _ -> Right (True, logs)
        Left failure@(Cek.ErrorWithCause (Cek.OperationalError (Cek.CekOutOfExError _)) _) ->
          Left (show failure)
        Left failure@(Cek.ErrorWithCause (Cek.StructuralError OpenTermEvaluatedMachineError) _) ->
          Left (show failure)
        Left failure@(Cek.ErrorWithCause (Cek.StructuralError (PanicMachineError _)) _) ->
          Left (show failure)
        Left _ -> Right (False, logs)

checkRequest :: (Int, Int, Int, Int) -> Request -> IO (Int, Int, Int, Int)
checkRequest initial (Request label before after inputs) = do
  original <- decode before
  optimized <- decode after
  foldM (checkInput original optimized) initial (zip [0 :: Int ..] inputs)
  where
    checkInput original optimized counts (index, argument) = do
      value <- decode argument
      foldM (checkContext original optimized value index) counts [0 .. 3]
    checkContext original optimized value index (count, passed, failed, logChanges) context = do
      let location = label ++ "/input=" ++ show index ++ "/context=" ++ show context
      expected <- either (die . ((location ++ "/before inconclusive: ") ++)) pure
        (evaluate (observe original value context))
      actual <- either (die . ((location ++ "/after inconclusive: ") ++)) pure
        (evaluate (observe optimized value context))
      unless (fst actual == fst expected) $ die (location ++ ": acceptance mismatch: " ++ show (expected, actual))
      unless (snd actual == snd expected) $
        hPutStrLn stderr (location ++ ": evaluator logs changed: " ++ show (expected, actual))
      pure (count + 1, passed + fromEnum (fst expected), failed + fromEnum (not (fst expected)),
        logChanges + fromEnum (snd actual /= snd expected))

main :: IO ()
main = do
  let package = tyConPackage (typeRepTyCon (typeRep (Proxy :: Proxy PLC.DefaultFun)))
  unless ("plutus-core-1.65.0.0-" `isPrefixOf` package) $ die ("Expected plutus-core 1.65.0.0, linked " ++ package)
  requests <- LBS.lines <$> LBS.getContents
  unless (not (null requests)) $ die "No pass-audit requests"
  (count, passed, failed, logChanges) <- foldM (\counts line -> either die (checkRequest counts) (eitherDecode line)) (0, 0, 0, 0) requests
  unless (passed > 0 && failed > 0) $ die "Both accepting and rejecting cases are required"
  putStrLn $ "Verified " ++ show count ++ " reference comparisons: " ++ show passed
    ++ " successful and " ++ show failed ++ " failing; identical acceptance."
  putStrLn $ show logChanges ++ " comparisons have different evaluator logs (including builtin failure diagnostics)."
