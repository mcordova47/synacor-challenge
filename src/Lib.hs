module Lib
    ( executeProgram
    ) where

import Protolude

import Control.Monad.Trans.Writer (runWriterT)
import Control.Monad.Writer (MonadWriter(tell))
import qualified Data.ByteString.Lazy as BS
import Data.List.Split (chunksOf)
import qualified Data.Map as Map
import qualified Data.Text as Text

executeProgram :: IO ()
executeProgram = do
  program <- readChallenge
  -- putStrLn $ showText $ take 1288 program
  -- putStrLn $ showText $ length program
  -- execute program
  trace program
  where
    readChallenge =
      parseProgram <$> BS.readFile "/Users/marc.cordova/Documents/professional-development/synacore-challenge/challenge.bin"
    execute prog =
      execute' prog >>= \case
        (Left err, _) -> putStrLn err
        _ -> pure ()
    trace prog = do
      (res, trace') <- execute' prog
      case res of
        Left err -> putStrLn err
        _ -> pure ()
      putStrLn trace'
    execute' prog =
      runWriterT $ runExceptT $ evalStateT (executeSteps prog) memory
    memory = Memory
      { registers = Map.empty
      , stack = []
      }

data Memory = Memory
  { registers :: Map Register Int
  , stack :: [Int]
  }

executeSteps ::
  ( MonadIO m
  , MonadState Memory m
  , MonadWriter Text m
  , MonadError Text m
  )
  => [Step]
  -> m ()
executeSteps steps =
  executeSteps' stepsWithIndices
  where
    stepsWithIndices =
      zip [0..] steps
    executeSteps' = \case
      (n, op@(Operation Halt)) : _ -> do
        logStep n op
        putStrLn ("Halting execution" :: Text)
      (n, op@(Operation (Set reg expr))) : rest -> do
        logStep n op
        memory <- get
        let registers' = registers memory
        lit <- getLiteral expr
        put memory { registers = Map.insert reg lit registers' }
        executeSteps' rest
      (n, op@(Operation (Eq reg expr1 expr2))) : rest -> do
        logStep n op
        memory <- get
        let registers' = registers memory
        lit1 <- getLiteral expr1
        lit2 <- getLiteral expr2
        let value = if lit1 == lit2 then 1 else 0
        put memory { registers = Map.insert reg value registers' }
        executeSteps' rest
      (n, op@(Operation (Jmp to))) : rest -> do
        logStep n op
        to' <- getLiteral to
        jump to'
      (n, op@(Operation (Jt expr to))) : rest -> do
        logStep n op
        to' <- getLiteral to
        lit <- getLiteral expr
        if lit == 0 then
          executeSteps' rest
        else
          jump to'
      (n, op@(Operation (Jf expr to))) : rest -> do
        logStep n op
        to' <- getLiteral to
        lit <- getLiteral expr
        if lit == 0 then
          jump to'
        else
          executeSteps' rest
      (n, op@(Operation (Call to))) : rest -> do
        logStep n op
        push (n + 1)
        to' <- getLiteral to
        jump to'
      (line, op@(Operation (Out (Literal n)))) : rest -> do
        logStep line op
        putStr $ Text.singleton $ chr n
        executeSteps' rest
      (n, op@(Operation NoOp)) : rest -> do
        logStep n op
        executeSteps' rest
      (n, step) : _ -> do
        logStep n step
        putStrLn ("Not implemented: " <> show step :: Text)
      [] ->
        pure ()
    getLiteral = \case
      Literal lit ->
        pure lit
      Register reg -> do
        registers' <- registers <$> get
        case Map.lookup reg registers' of
          Just lit -> pure lit
          _ -> throwError $ "No value stored in register " <> show reg
      InvalidExpression expr ->
        throwError $ "Invalid expression: " <> show expr
    logStep line step =
      tell $ show line <> "\t" <> show step <> "\n"
    jump to =
      executeSteps' $ drop to stepsWithIndices
    push val = do
      memory <- get
      put memory { stack = val : stack memory }

data Step
  = Operation Operation
  | InvalidStep Int
  deriving Show

data Expression
  = Literal Int
  | Register Register
  | InvalidExpression Int
  deriving Show

data Register
  = RegisterZero
  | RegisterOne
  | RegisterTwo
  | RegisterThree
  | RegisterFour
  | RegisterFive
  | RegisterSix
  | RegisterSeven
  deriving (Show, Eq, Ord)

data Operation
  = Halt
  | Set Register Expression
  | Push Expression
  | Pop Register
  | Eq Register Expression Expression
  | Gt Register Expression Expression
  | Jmp Expression
  | Jt Expression Expression
  | Jf Expression Expression
  | Add Register Expression Expression
  | Mult Register Expression Expression
  | Mod Register Expression Expression
  | And Register Expression Expression
  | Or Register Expression Expression
  | Not Register Expression
  | Rmem Register Register
  | Wmem Register Expression
  | Call Expression
  | Ret
  | Out Expression
  | In Register
  | NoOp
  deriving Show

parseProgram :: BS.ByteString -> [Step]
parseProgram =
  parseSteps . concatMap fromLittleEndian . chunksOf 2 . BS.unpack
  where
    fromLittleEndian = \case
      [x, y] -> [fromIntegral y * 16^2 + fromIntegral x]
      _ -> []
    parseSteps = \case
      0 : rest ->
        Operation Halt : parseSteps rest
      1 : register : expr : rest | Register reg <- parseExpression register ->
        Operation (Set reg $ parseExpression expr) : parseSteps rest
      2 : expr : rest ->
        Operation (Push $ parseExpression expr) : parseSteps rest
      3 : register : rest | Register reg <- parseExpression register ->
        Operation (Pop reg) : parseSteps rest
      4 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Eq reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      5 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Gt reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      6 : to : rest ->
        Operation (Jmp $ parseExpression to) : parseSteps rest
      7 : expr : to : rest ->
        Operation (Jt (parseExpression expr) (parseExpression to)) : parseSteps rest
      8 : expr : to : rest ->
        Operation (Jf (parseExpression expr) (parseExpression to)) : parseSteps rest
      9 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Add reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      10 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Mult reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      11 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Mod reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      12 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (And reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      13 : register : expr1 : expr2 : rest | Register reg <- parseExpression register ->
        Operation (Or reg (parseExpression expr1) (parseExpression expr2)) : parseSteps rest
      14 : register : expr : rest | Register reg <- parseExpression register ->
        Operation (Not reg $ parseExpression expr) : parseSteps rest
      15 : register1 : register2 : rest | Register reg1 <- parseExpression register1, Register reg2 <- parseExpression register2 ->
        Operation (Rmem reg1 reg2) : parseSteps rest
      16 : register : expr : rest | Register reg <- parseExpression register ->
        Operation (Wmem reg $ parseExpression expr) : parseSteps rest
      17 : expr : rest ->
        Operation (Call $ parseExpression expr) : parseSteps rest
      18 : rest ->
        Operation Ret : parseSteps rest
      19 : expr : rest ->
        Operation (Out $ parseExpression expr) : parseSteps rest
      20 : register : rest | Register reg <- parseExpression register ->
        Operation (In reg) : parseSteps rest
      21 : rest ->
        Operation NoOp : parseSteps rest
      step : rest ->
        InvalidStep step : parseSteps rest
      [] ->
        []
    parseExpression = \case
      expr | expr < 32768 ->
        Literal expr
      32768 ->
        Register RegisterZero
      32769 ->
        Register RegisterOne
      32770 ->
        Register RegisterTwo
      32771 ->
        Register RegisterThree
      32772 ->
        Register RegisterFour
      32773 ->
        Register RegisterFive
      32774 ->
        Register RegisterSix
      32775 ->
        Register RegisterSeven
      expr ->
        InvalidExpression expr

showText :: Show a => a -> Text
showText =
  show
