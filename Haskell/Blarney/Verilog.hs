{-|
Module      : Blarney.Verilog
Description : Verilog generation
Copyright   : (c) Matthew Naylor, 2019
License     : MIT
Maintainer  : mattfn@gmail.com
Stability   : experimental

Convert Blarney functions to Verilog modules.
-}

module Blarney.Verilog
  ( writeVerilogModule  -- Generate Verilog module
  , writeVerilogTop     -- Generate Verilog top-level module
  ) where

-- Standard imports
import Prelude hiding ((<>))
import Data.List
import Numeric (showHex)
import System.IO
import Data.Maybe
import Data.Bits
import System.Process

-- Blarney imports
import Blarney.BV
import Blarney.Module
import Blarney.Interface
import Blarney.IfThenElse

-- Toplevel API
--------------------------------------------------------------------------------

-- | Convert given Blarney function to a Verilog module
writeVerilogModule :: Modular a
                   => a          -- ^ Blarney function
                   -> String     -- ^ Module name
                   -> String     -- ^ Output directory
                   -> IO ()
writeVerilogModule top mod dir =
    do system ("mkdir -p " ++ dir)
       nl <- netlist (makeModule top)
       writeVerilog fileName mod nl
  where
    fileName = dir ++ "/" ++ mod ++ ".v"

-- | Convert given Blarney function to a top-level Verilog module
writeVerilogTop :: Module ()  -- ^ Blarney module
                -> String     -- ^ Top-level module name
                -> String     -- ^ Output directory
                -> IO ()
writeVerilogTop top mod dir =
    do nl <- netlist top
       system ("mkdir -p " ++ dir)
       writeVerilog (dir ++ "/" ++ mod ++ ".v") mod nl
       writeFile (dir ++ "/" ++ mod ++ ".cpp") simCode
       writeFile (dir ++ "/" ++ mod ++ ".mk") makefileIncCode
       writeFile (dir ++ "/Makefile") makefileCode
  where
    fileName = dir ++ "/" ++ mod ++ ".v"

    simCode =
      unlines [
        "// Generated by Blarney"
      , "#include <verilated.h>"
      , "#include \"V" ++ mod ++ ".h\""
      , "V" ++ mod ++ " *top;"
      , "vluint64_t main_time = 0;"
      , "// Called by $time in Verilog"
      , "double sc_time_stamp () {"
      , "  return main_time;"
      , "}"
      , "int main(int argc, char** argv) {"
      , "  Verilated::commandArgs(argc, argv);"
      , "  top = new V" ++ mod ++ ";"
      , "  while (!Verilated::gotFinish()) {"
      , "    top->clock = 0; top->eval();"
      , "    top->clock = 1; top->eval();"
      , "    main_time++;"
      , "  }"
      , "  top->final(); delete top; return 0;"
      , "}"
      ]

    makefileIncCode =
      unlines [
        "all: " ++ mod
      , mod ++ ": *.v *.cpp"
      , "\tverilator -cc " ++ mod ++ ".v " ++ "-exe "
                           ++ mod ++ ".cpp " ++ "-o " ++ mod
                           ++ " -Wno-UNSIGNED"
                           ++ " -y $(BLARNEY_ROOT)/Verilog"
                           ++ " --x-assign unique"
                           ++ " --x-initial unique"
      , "\tmake -C obj_dir -j -f V" ++ mod ++ ".mk " ++ mod
      , "\tcp obj_dir/" ++ mod ++ " ."
      , "\trm -rf obj_dir"
      , ".PHONY: clean clean-" ++ mod
      , "clean: clean-" ++ mod
      , "clean-" ++ mod ++ ":"
      , "\trm -f " ++ mod
      ]

    makefileCode = "include *.mk"

writeVerilog :: String -> String -> [Net] -> IO ()
writeVerilog fileName modName netlist = do
  h <- openFile fileName WriteMode
  hPutStr h (showVerilogModule modName netlist $ "")
  hClose h

-- Internal helpers
--------------------------------------------------------------------------------

-- NetVerilog helper type
data NetVerilog = NetVerilog { decl :: Maybe ShowS -- declaration
                             , inst :: Maybe ShowS -- instanciation
                             , alws :: Maybe ShowS -- always block
                             , rsts :: Maybe ShowS -- reset logic
                             }
-- pretty helpers
--------------------------------------------------------------------------------
chr = showChar
str = showString
x <> y      = x . y
x <+> y     = x <> space <> y
x <^> y     = x <> chr '\n' <> y
sep         = foldr (\x y -> x <+> y) (str "")
--vsep        = foldr (\x y -> x <^> y) (str "")
brackets  s = chr '[' <> s <> chr ']'
parens    s = chr '(' <> s <> chr ')'
braces    s = chr '{' <> s <> chr '}'
dquotes   s = chr '"' <> s <> chr '"'
space       = chr ' '
spaces    n = str $ replicate n ' '
newline     = chr '\n'
dot         = chr '.'
comma       = chr ','
colon       = chr ':'
semi        = chr ';'
equals      = chr '='
argStyle n as =
  foldr (.) (str "") (intersperse (str ",\n") (map (\x -> spaces n <> x) as))

-- general helpers
--------------------------------------------------------------------------------
showIntLit :: Int -> Integer -> ShowS
showIntLit w v = shows w <> str "'h" <> showHex v
showDontCare :: Int -> ShowS
showDontCare w = shows w <> str "'b" <> str (replicate w 'x')
showExpr :: Expr -> ShowS
showExpr (ConstE w v) = showIntLit w v
showExpr (DontCareE w) = showDontCare w
showWire :: (InstId, Int, Name) -> ShowS
showWire (iId, nOut, Final nm) =    str nm
                                 <> chr '_' <> shows iId
                                 <> chr '_' <> shows nOut
showWire (iId, nOut, _) = error "Name must be Final"
showWireWidth :: Int -> (InstId, Int, Name) -> ShowS
showWireWidth width wId = brackets (shows (width-1) <> str ":0") <+> showWire wId
showNetInput :: NetInput -> ShowS
showNetInput (InputWire wId) = showWire wId
showNetInput (InputExpr expr) = showExpr expr
showVerilogModule :: String -> [Net] -> ShowS
showVerilogModule modName netlst =
     str "module" <+> str modName <+> chr '(' <^> showIOs <^> spaces 2 <> str ");"
  <^> spaces 2 <> showComment "Declarations"
  <^> spaces 2 <> showCommentLine
  <>  foldl (\x y -> x <^> spaces 2 <> y) (str "") (catMaybes $ map decl netVs)
  <^> spaces 2 <> showComment "Instances"
  <^> spaces 2 <> showCommentLine
  <>  foldl (\x y -> x <^> spaces 2 <> y) (str "") (catMaybes $ map inst netVs)
  <^> spaces 2 <> showComment "Always block"
  <^> spaces 2 <> showCommentLine
  <^> spaces 2 <> str "always" <+> chr '@' <> parens (str "posedge clock") <+> str "begin"
  <^> spaces 4 <> str "if (reset) begin"
  <> foldl (\x y -> x <^> spaces 6 <> y) (str "") (catMaybes $ map rsts netVs)
  <^> spaces 4 <> str "end else begin"
  <> foldl (\x y -> x <^> spaces 6 <> y) (str "") (catMaybes $ map alws netVs)
  <^> spaces 4 <> str "end"
  <^> spaces 2 <> str "end"
  <^> str "endmodule"
  where netVs = map genNetVerilog netlst
        netPrims = map netPrim netlst
        ins = [Input w s | (w, s) <- nub [(w, s) | Input w s <- netPrims]]
        outs = [Output w s | Output w s <- netPrims]
        showIOs = argStyle 2 $ str "input wire clock"
                             : str "input wire reset"
                             : map showIO (ins ++ outs)
        showIO (Input w s) = str "input wire" <+> brackets (shows (w-1) <> str ":0") <+> str s
        showIO (Output w s) = str "output wire" <+> brackets (shows (w-1) <> str ":0") <+> str s
        showIO _ = str ""
        showComment cmt = str "//" <+> str cmt
        --showCommentLine = remainCols (\r -> p "//" <> p (replicate (r-2) '/'))
        showCommentLine = str (replicate 78 '/')

-- declaration helpers
--------------------------------------------------------------------------------
declWire width wId = str "wire" <+> showWireWidth width wId <> semi
declWireInit width wId init =     str "wire" <+> showWireWidth width wId
                              <+> equals <+> showIntLit width init <> semi
declWireDontCare width wId  =     str "wire" <+> showWireWidth width wId
                              <+> equals <+> showDontCare width <> semi
declReg width reg = str "reg" <+> showWireWidth width reg <> semi
declRegInit width reg init =     str "reg" <+> showWireWidth width reg
                             <+> equals <+> showIntLit width init <> semi
declRAM initFile numPorts _ dw nId nName =
  foldl (<+>) (str "") $ map (\n -> declWire dw (nId, n, nName)) [0..numPorts-1]
declRegFile initFile aw dw id =
      str "reg" <+> brackets (shows (dw-1) <> str ":0")
  <+> str "rf" <> shows id <+> brackets (parens (str "2**" <> shows aw) <> str "-1" <> str ":0") <> semi
  <> showInit
  where showInit = case initFile of
          ""    ->     str ""
          fname ->     str "\ngenerate initial $readmemh" <> parens
                       (str fname <> comma <+> str "rf" <> shows id) <> semi
                   <+> str "endgenerate"

-- reset helpers
--------------------------------------------------------------------------------

resetRegister width reg init =
      showWire reg <+> str "<="
  <+> shows width <> str "'h" <> str (showHex init "") <> semi

-- instantiation helpers
--------------------------------------------------------------------------------
instPrefixOp op net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> str op <> parens (showNetInput (netInputs net !! 0)) <> semi
instInfixOp op net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> showNetInput (netInputs net !! 0)
  <+> str op <+> showNetInput (netInputs net !! 1) <> semi
instShift w op net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> a0 <+> str op <+> showNetInput (netInputs net !! 1) <> semi
  where a0 = if op == ">>>" then str "$signed" <> parens a0name
                            else a0name
        a0name = showNetInput (netInputs net !! 0)
instReplicate w net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> braces (shows w <> braces (showNetInput (netInputs net !! 0))) <> semi
instMux net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> showNetInput (netInputs net !! 0) <+> chr '?'
  <+> showNetInput (netInputs net !! 1) <+> colon
  <+> showNetInput (netInputs net !! 2) <> semi
instConcat net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> braces ( showNetInput (netInputs net !! 0) <> comma <+>
               showNetInput (netInputs net !! 1)) <> semi
instSelectBits net hi lo =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> sel (netInputs net !! 0) <> semi
  where sel (InputWire w) = showWire w <> brackets (shows hi <> colon <> shows lo)
        sel (InputExpr (ConstE _ v)) = showIntLit width ((v `shiftR` lo) .&. ((2^width)-1))
        sel (InputExpr (DontCareE _)) = showDontCare width
        width = hi+1-lo
instZeroExtend net wi wo =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> braces (braces (shows (wo-wi) <> braces (str "1'b0"))
  <>  comma <+> showNetInput (netInputs net !! 0)) <> semi
instSignExtend net wi wo =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> braces (braces (shows (wo-wi) <> braces (showNetInput (netInputs net !! 0)
  <>  brackets (shows (wi-1)))) <> comma
  <+> showNetInput (netInputs net !! 0)) <> semi
instCustom net name ins outs params clked =
      str name <> showParams <+> str name <> chr '_' <> shows nId
  <+> chr '(' <^> showArgs <^> spaces 2 <> str ");"
  where numParams = length params
        showParams = if numParams == 0 then space
                     else str "# (" <^> argStyle 4 allParams <^> spaces 2 <> str ")"
        allParams = [ dot <> str key <> parens (str val) | (key :-> val, i) <- zip params [1..] ]
        args = zip ins (netInputs net) ++ [ (o, InputWire (nId, n, netName net))
                                          | (o, n) <- zip (map fst outs) [0..] ]
        numArgs  = length args
        showArgs = argStyle 4 $ [ str ".clock(clock)" | clked ]
                             ++ [ str ".reset(reset)" | clked ]
                             ++ allArgs
        allArgs  = [ dot <> str name <> parens (showNetInput netInput)
                   | ((name, netInput), i) <- zip args [1..] ]
        nId = netInstId net
instTestPlusArgs wId s =
      str "assign" <+> showWire wId <+> equals
  <+> str "$test$plusargs" <> parens (dquotes $ str s) <+> str "== 0 ? 0 : 1;"
instOutput net s =
  str "assign" <+> str s <+> equals <+> showNetInput (netInputs net !! 0) <> semi
instInput net s =
  str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals <+> str s <> semi
instRAM net i aw dw =
      str "BlockRAM# (" <^> argStyle 6 ramParams
  <^> spaces 4 <> str ") ram" <> shows nId <+> chr '('
  <^> argStyle 6 ramArgs <^> spaces 4 <> str ");"
  where ramParams = [ str ".INIT_FILE"  <> parens (str (show $ fromMaybe "UNUSED" i))
                    , str ".ADDR_WIDTH" <> parens (shows aw)
                    , str ".DATA_WIDTH" <> parens (shows dw) ]
        ramArgs   = [ str ".CLK(clock)"
                    , str ".DI"   <> parens (showNetInput (netInputs net !! 1))
                    , str ".ADDR" <> parens (showNetInput (netInputs net !! 0))
                    , str ".WE"   <> parens (showNetInput (netInputs net !! 2))
                    , str ".DO"   <> parens (showWire (nId, 0, netName net)) ]
        nId = netInstId net
instTrueDualRAM net i aw dw =
      str "BlockRAMTrueDual# (" <^> (argStyle 6 ramParams)
  <^> spaces 4 <> str ") ram" <> shows nId <+> chr '('
  <^> argStyle 6 ramArgs <^> spaces 4 <> str ");"
  where ramParams = [ str ".INIT_FILE"  <> parens (str (show $ fromMaybe "UNUSED" i))
                    , str ".ADDR_WIDTH" <> parens (shows aw)
                    , str ".DATA_WIDTH" <> parens (shows dw) ]
        ramArgs   = [ str ".CLK(clock)"
                    , str ".DI_A"   <> parens (showNetInput (netInputs net !! 1))
                    , str ".ADDR_A" <> parens (showNetInput (netInputs net !! 0))
                    , str ".WE_A"   <> parens (showNetInput (netInputs net !! 2))
                    , str ".DO_A"   <> parens (showWire (nId, 0, netName net))
                    , str ".DI_B"   <> parens (showNetInput (netInputs net !! 4))
                    , str ".ADDR_B" <> parens (showNetInput (netInputs net !! 3))
                    , str ".WE_B"   <> parens (showNetInput (netInputs net !! 5))
                    , str ".DO_B"   <> parens (showWire (nId, 1, netName net)) ]
        nId = netInstId net
instRegFileRead id net =
      str "assign" <+> showWire (netInstId net, 0, netName net) <+> equals
  <+> str "rf" <> shows id <> brackets (showNetInput (netInputs net !! 0)) <> semi

-- always block helpers
--------------------------------------------------------------------------------
alwsRegister net = showWire (netInstId net, 0, netName net) <+> str "<="
               <+> showNetInput (netInputs net !! 0) <> semi
alwsRegisterEn net =
      str "if" <+> parens (showNetInput (netInputs net !! 0) <+> str "== 1")
  <+> showWire (netInstId net, 0, netName net) <+> str "<=" <+> showNetInput (netInputs net !! 1)
  <>  semi
alwsDisplay args net =
      str "if" <+> parens (showNetInput (netInputs net !! 0) <+> str "== 1")
  <+> str "$write ("
  <^> (argStyle 8 $ fmtArgs args (tail (netInputs net)))
  <^> spaces 6 <> str ");"
  where fmtArgs [] _ = []
        fmtArgs (DisplayArgString s : args) ins = shows s : (fmtArgs args ins)
        fmtArgs (DisplayArgBit w : args) (x:ins) = (showNetInput x) : (fmtArgs args ins)
alwsFinish net =
  str "if" <+> parens (showNetInput (netInputs net !! 0) <+> str "== 1")
           <+> str "$finish" <> semi
alwsRegFileWrite id net =
      str "if" <+> parens (showNetInput (netInputs net !! 0) <+> str "== 1")
  <+> str "rf" <> shows id <> brackets (showNetInput (netInputs net !! 1))
  <+> str "<=" <+> showNetInput (netInputs net !! 2) <> semi

-- generate NetVerilog
--------------------------------------------------------------------------------
genNetVerilog :: Net -> NetVerilog
genNetVerilog net = case netPrim net of
  Add w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "+" net }
  Sub w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "-" net }
  Mul w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "*" net }
  Div w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "/" net }
  Mod w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "%" net }
  Not w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instPrefixOp "~" net }
  And w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "&" net }
  Or w                    -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "|" net }
  Xor w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInfixOp "^" net }
  ShiftLeft w             -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instShift w "<<" net }
  ShiftRight w            -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instShift w ">>" net }
  ArithShiftRight w       -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instShift w ">>>" net }
  Equal w                 -> dfltNV { decl = Just $ declWire 1 wId
                                    , inst = Just $ instInfixOp "==" net }
  NotEqual w              -> dfltNV { decl = Just $ declWire 1 wId
                                    , inst = Just $ instInfixOp "!=" net }
  LessThan w              -> dfltNV { decl = Just $ declWire 1 wId
                                    , inst = Just $ instInfixOp "<" net }
  LessThanEq w            -> dfltNV { decl = Just $ declWire 1 wId
                                    , inst = Just $ instInfixOp "<=" net }
  Register i w            -> dfltNV { decl = Just $ declRegInit w wId i
                                    , alws = Just $ alwsRegister net
                                    , rsts = Just $ resetRegister w wId i }
  RegisterEn i w          -> dfltNV { decl = Just $ declRegInit w wId i
                                    , alws = Just $ alwsRegisterEn net
                                    , rsts = Just $ resetRegister w wId i }
  BRAM i aw dw            -> dfltNV { decl = Just $ declRAM i 1 aw dw nId nName
                                    , inst = Just $ instRAM net i aw dw }
  TrueDualBRAM i aw dw    -> dfltNV { decl = Just $ declRAM i 2 aw dw nId nName
                                    , inst = Just $ instTrueDualRAM net i aw dw }
  ReplicateBit w          -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instReplicate w net }
  ZeroExtend wi wo        -> dfltNV { decl = Just $ declWire wo wId
                                    , inst = Just $ instZeroExtend net wi wo }
  SignExtend wi wo        -> dfltNV { decl = Just $ declWire wo wId
                                    , inst = Just $ instSignExtend net wi wo }
  SelectBits w hi lo      -> dfltNV { decl = Just $ declWire (1+hi-lo) wId
                                    , inst = Just $ instSelectBits net hi lo }
  Concat aw bw            -> dfltNV { decl = Just $ declWire (aw+bw) wId
                                    , inst = Just $ instConcat net }
  Mux w                   -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instMux net }
  CountOnes w             -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instPrefixOp "$countones" net }
  Identity w              -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instPrefixOp "" net }
  Display args            -> dfltNV { alws = Just $ alwsDisplay args net }
  Finish                  -> dfltNV { alws = Just $ alwsFinish net }
  TestPlusArgs s          -> dfltNV { decl = Just $ declWire 1 wId
                                    , inst = Just $ instTestPlusArgs wId s }
  Input w s               -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instInput net s }
  Output w s              -> dfltNV { inst = Just $ instOutput net s }
  RegFileMake f aw dw vId -> dfltNV { decl = Just $ declRegFile f aw dw vId }
  RegFileRead w vId       -> dfltNV { decl = Just $ declWire w wId
                                    , inst = Just $ instRegFileRead vId net }
  RegFileWrite _ _ vId    -> dfltNV { alws = Just $ alwsRegFileWrite vId net }
  Custom p is os ps clked -> dfltNV { decl = Just $ sep [ declWire w (nId, n, nName)
                                                        | ((o, w), n) <- zip os [0..] ]
                                    , inst = Just $ instCustom net p is os ps clked }
  Const w i               -> dfltNV { decl = Just $ declWireInit w wId i }
  DontCare w              -> dfltNV { decl = Just $ declWireDontCare w wId }
  --_                       -> dfltNV
  where nId = netInstId net
        nName = netName net
        wId = (nId, 0, nName)
        dfltNV = NetVerilog { decl = Nothing
                            , inst = Nothing
                            , alws = Nothing
                            , rsts = Nothing }
