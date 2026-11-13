import RiscvZkvm.Rv64.Basic

/-!
The in-memory ABI of `monad_pure_execute` (see `cxx/pure_interp.cpp`) and the
fixed addresses the harness and the top-level theorem place its arguments at.
All addresses lie in the model's RAM window `[0xa0000000, 0xc0000000]`, above
the binary's 64 MiB heap.
-/

namespace PureAbi

/-- `monad_pure_input` (64 bytes). -/
def inputAddr : Nat := 0xa8000000
/-- `monad_pure_output` (32 bytes). -/
def outputAddr : Nat := 0xa8000100
/-- EVM operand stack: 1025 slots of 32 bytes. -/
def evmStackAddr : Nat := 0xa8001000
/-- Initial EVM memory buffer, zero-filled. -/
def evmMemoryAddr : Nat := 0xa8010000
def evmMemoryCapacity : Nat := 0x10000
/-- Contract bytecode. -/
def codeAddr : Nat := 0xa8100000
/-- Call data. -/
def calldataAddr : Nat := 0xa8200000
/-- Initial machine stack pointer (grows down). -/
def machineStackTop : Nat := 0xafff0000
/-- Return address handed to the entry point. Nothing is loaded there, so the
    run stops when the function returns. -/
def returnAddr : Nat := 0x90000000

end PureAbi
