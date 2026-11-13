import RiscvZkvm.Interpreter.Run
import PureAbi

/-!
Run `build/pure.elf` in the riscv-zkvm proof model (`RiscvZkvm.Rv64.step`) on a
given bytecode, calldata and gas limit, and print the result the binary writes.

  lake exe run-pure build/pure.elf <code hex> <calldata hex> <gas> [fuel]
-/

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def parseHex (s : String) : List Nat :=
  let s : String := if s.startsWith "0x" then (s.drop 2).copy else s
  let rec go : List Char → List Nat
    | a :: b :: rest => (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def readByte (mem : Std.HashMap Word Word) (a : Nat) : Nat :=
  ((mem.getD (BitVec.ofNat 64 (a - a % 8)) 0).toNat >>> (8 * (a % 8))) % 256

def writeByte (mem : Std.HashMap Word Word) (a b : Nat) : Std.HashMap Word Word :=
  let k := BitVec.ofNat 64 (a - a % 8)
  let sh := 8 * (a % 8)
  let old := (mem.getD k 0).toNat
  mem.insert k (BitVec.ofNat 64 ((old &&& ((2 ^ 64 - 1) ^^^ (0xff <<< sh))) ||| (b <<< sh)))

def writeBytes (mem : Std.HashMap Word Word) (a : Nat) (bs : List Nat) : Std.HashMap Word Word :=
  (bs.zipIdx).foldl (fun m (b, i) => writeByte m (a + i) b) mem

def writeU64 (mem : Std.HashMap Word Word) (a v : Nat) : Std.HashMap Word Word :=
  mem.insert (BitVec.ofNat 64 a) (BitVec.ofNat 64 v)

def readU64 (mem : Std.HashMap Word Word) (a : Nat) : Nat :=
  (mem.getD (BitVec.ofNat 64 a) 0).toNat

def toHex (bs : List Nat) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bs.flatMap fun b => [d (b / 16), d (b % 16)])

partial def runTo (ret : Word) (fuel steps : Nat) (e : ExecState) : Nat × ExecState × Bool :=
  if e.pc == ret then (steps, e, true)
  else if steps ≥ fuel then (steps, e, false)
  else match e.stepExec with
    | some e' => runTo ret fuel (steps + 1) e'
    | none => (steps, e, false)

def main (args : List String) : IO UInt32 := do
  let [elf, codeHex, dataHex, gas] := args.take 4
    | IO.eprintln "usage: run-pure <elf> <code hex> <calldata hex> <gas> [fuel]"; return 2
  let fuel := (args[4]?.bind String.toNat?).getD 50000000
  let bytes ← IO.FS.readBinFile elf
  let img ← IO.ofExcept (parseElf64 bytes |>.mapError IO.userError)
  let l := load img
  let code := parseHex codeHex
  let data := parseHex dataHex
  let mut mem := l.state.mem
  mem := writeBytes mem PureAbi.codeAddr code
  mem := writeBytes mem PureAbi.calldataAddr data
  mem := writeU64 mem (PureAbi.inputAddr + 0) PureAbi.codeAddr
  mem := writeU64 mem (PureAbi.inputAddr + 8) code.length
  mem := writeU64 mem (PureAbi.inputAddr + 16) PureAbi.calldataAddr
  mem := writeU64 mem (PureAbi.inputAddr + 24) data.length
  mem := writeU64 mem (PureAbi.inputAddr + 32) gas.toNat!
  mem := writeU64 mem (PureAbi.inputAddr + 40) PureAbi.evmMemoryAddr
  mem := writeU64 mem (PureAbi.inputAddr + 48) PureAbi.evmMemoryCapacity
  mem := writeU64 mem (PureAbi.inputAddr + 56) PureAbi.evmStackAddr
  let regs := l.state.regs
    |>.set! 1 (BitVec.ofNat 64 PureAbi.returnAddr)
    |>.set! 2 (BitVec.ofNat 64 PureAbi.machineStackTop)
    |>.set! 10 (BitVec.ofNat 64 PureAbi.inputAddr)
    |>.set! 11 (BitVec.ofNat 64 PureAbi.outputAddr)
  let e0 : ExecState := { l.state with mem, regs }
  let (steps, e, ok) := runTo (BitVec.ofNat 64 PureAbi.returnAddr) fuel 0 e0
  if !ok then
    IO.println s!"STOPPED after {steps} steps at pc={e.pc.toHex}: {repr (classifyStop l e)}"
    return 1
  let status := readU64 e.mem PureAbi.outputAddr
  let gasLeft := readU64 e.mem (PureAbi.outputAddr + 8)
  let outPtr := readU64 e.mem (PureAbi.outputAddr + 16)
  let outLen := readU64 e.mem (PureAbi.outputAddr + 24)
  let out := (List.range outLen).map fun i => readByte e.mem (outPtr + i)
  let st := match status with | 0 => "success" | 1 => "revert" | _ => "failure"
  IO.println s!"status={st} gas_left={gasLeft} output=0x{toHex out} steps={steps}"
  return 0
