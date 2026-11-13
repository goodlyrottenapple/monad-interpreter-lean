import PureInterp.Entry.Basic

/-!
# The bump allocator: `malloc`, `operator new`, `operator new[]`, `aligned_alloc`

`cxx/platform.cpp`: `aligned_alloc(al, n)` rounds the heap pointer `heap_next`
up to `al`, aborts if `n` bytes do not fit below `monad_pure_heap_end`,
advances `heap_next` past the block and returns it. `malloc` and the two
`operator new` bodies are `aligned_alloc(32, n)` inlined; the three are the
same 17 instructions up to pc-relative immediates (`alloc32Prog`).

The heap pointer cell `hcell ↦ₘ hn` is explicit: the result is
`p = (hn + 31) &&& ~31`, and the cell is left holding `n + p`.
Nothing is said here about the block's contents or validity; callers bring
ownership of the bytes they write.
-/

namespace PureInterp.Entry
open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-- The shape shared by `malloc` and both `operator new` bodies. -/
def alloc32Prog (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) : List Instr := [
  .BEQ .x10 .x0 0x0040#13,
  .AUIPC .x15 hi1, .LD .x15 .x15 lo1,
  .AUIPC .x14 hi2, .ADDI .x14 .x14 lo2,
  .ADDI .x15 .x15 0x01f#12, .ANDI .x15 .x15 0xfe0#12, .SUB .x14 .x14 .x15,
  .BGEU .x14 .x10 0x0010#13,
  .EBREAK, .EBREAK, .JAL .x0 0x1ffff8#21,
  .ADD .x10 .x10 .x15,
  .AUIPC .x14 hi3, .SD .x14 .x10 lo3, .ADDI .x10 .x15 0x000#12,
  .JALR .x0 .x1 0x000#12]

theorem alloc32Prog_length (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) : (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3).length = 17 := rfl

theorem f_malloc_eq : Image.f_malloc.prog =
    alloc32Prog 0x1fff7#20 0xc90#12 0x23ff7#20 0xca8#12 0x1fff7#20 0xc60#12 := rfl
theorem f_new_9f70_eq : Image.f_new_80009f70.prog =
    alloc32Prog 0x1fff7#20 0x9ec#12 0x23ff7#20 0xa04#12 0x1fff7#20 0x9bc#12 := rfl
theorem f_new_9fb4_eq : Image.f_new_80009fb4.prog =
    alloc32Prog 0x1fff7#20 0x9a8#12 0x23ff7#20 0x9c0#12 0x1fff7#20 0x978#12 := rfl

/-- pc-relative address formed by `auipc`/`addi` (or `auipc` + load/store offset). -/
abbrev pcrel (pc : Word) (hi : BitVec 20) (lo : BitVec 12) : Word :=
  pc + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64 + signExtend12 lo

theorem load_pcrel (hi : BitVec 20) (lo : BitVec 12) (base r15 hn : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [.AUIPC .x15 hi, .LD .x15 .x15 lo])
      ((.x15 ↦ᵣ r15) ** (pcrel base hi lo ↦ₘ hn))
      ((.x15 ↦ᵣ hn) ** (pcrel base hi lo ↦ₘ hn)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem alloc_round (hi : BitVec 20) (lo oA oM : BitVec 12) (base r14 hn : Word) :
    cpsTripleWithin 5 base (base + 20) (CodeReq.ofProg base [
      .AUIPC .x14 hi, .ADDI .x14 .x14 lo, .ADDI .x15 .x15 oA, .ANDI .x15 .x15 oM,
      .SUB .x14 .x14 .x15])
      ((.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ hn))
      ((.x14 ↦ᵣ (pcrel base hi lo - ((hn + signExtend12 oA) &&& signExtend12 oM))) **
       (.x15 ↦ᵣ ((hn + signExtend12 oA) &&& signExtend12 oM))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem alloc_bump (hi : BitVec 20) (lo oZ : BitVec 12) (base n p r14 hn : Word) :
    cpsTripleWithin 4 base (base + 16) (CodeReq.ofProg base [
      .ADD .x10 .x10 .x15, .AUIPC .x14 hi, .SD .x14 .x10 lo, .ADDI .x10 .x15 oZ])
      ((.x10 ↦ᵣ n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ p) ** (pcrel (base + 4) hi lo ↦ₘ hn))
      ((.x10 ↦ᵣ (p + signExtend12 oZ)) **
       (.x14 ↦ᵣ (base + (4 : Word) + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (.x15 ↦ᵣ p) ** (pcrel (base + 4) hi lo ↦ₘ (n + p))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The rounded-up heap pointer: `(hn + 31) &&& ~31`. -/
def round32 (hn : Word) : Word := (hn + signExtend12 0x01f#12) &&& signExtend12 0xfe0#12

/-- Allocation of `n ≠ 0` bytes that fit: returns `round32 hn` and stores
    `n + round32 hn` in the heap pointer cell. -/
theorem alloc32_spec (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) (base ra n r14 r15 hn hcell hend : Word)
    (h_hcell1 : pcrel (base + 4) hi1 lo1 = hcell)
    (h_hend : pcrel (base + 12) hi2 lo2 = hend)
    (h_hcell3 : pcrel (base + 48 + 4) hi3 lo3 = hcell)
    (hn0 : n ≠ 0)
    (hfit : ¬ BitVec.ult (hend - round32 hn) n) :
    cpsTripleWithin 14 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (hcell ↦ₘ hn))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (round32 hn + signExtend12 0x000#12)) **
       (.x14 ↦ᵣ (base + (48 : Word) + (4 : Word) + ((hi3.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (.x15 ↦ᵣ round32 hn) ** (hcell ↦ₘ (n + round32 hn))) := by
  have hbeq := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x10 .x0 0x0040#13 n 0 base)
    (fun hp hq => hn0 (pure_end2 hp hq))
  have h1 := load_pcrel hi1 lo1 (base + 4) r15 hn
  have h2 := alloc_round hi2 lo2 0x01f#12 0xfe0#12 (base + 12) r14 hn
  rw [h_hcell1] at h1
  rw [h_hend, show (hn + signExtend12 0x01f#12) &&& signExtend12 0xfe0#12 = round32 hn from rfl] at h2
  have hbgeu := cpsBranchWithin_takenStripPure2
    (bgeu_spec_gen_within .x14 .x10 0x0010#13 (hend - round32 hn) n (base + 32))
    (fun hp hq => hfit (pure_end2 hp hq))
  have e : base + 32 + signExtend13 0x0010#13 = base + 48 := by rv64_addr
  rw [e] at hbgeu
  have h3 := alloc_bump hi3 lo3 0x000#12 (base + 48) n (round32 hn) (hend - round32 hn) hn
  rw [h_hcell3] at h3
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 64)
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) 0 base (by rw [alloc32Prog_length]; decide) (by rw [alloc32Prog_length]; decide) (by simp))) hbeq
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 4) (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) _ 1 (by rfl) (by rfl) (by rw [alloc32Prog_length]; simp) (by rw [alloc32Prog_length]; decide)) h1
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 12) (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) _ 3 (by rfl) (by rfl) (by rw [alloc32Prog_length]; simp) (by rw [alloc32Prog_length]; decide)) h2
  have hbgeu := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) 8 (base + 32) (by rw [alloc32Prog_length]; decide) (by rw [alloc32Prog_length]; decide) (by rfl))) hbgeu
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 48) (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) _ 12 (by rfl) (by rfl) (by rw [alloc32Prog_length]; simp) (by rw [alloc32Prog_length]; decide)) h3
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) 16 (base + 64) (by rw [alloc32Prog_length]; decide) (by rw [alloc32Prog_length]; decide) (by rfl))) hj
  runBlock hbeq h1 h2 hbgeu h3 hj

/-- Allocation of zero bytes: returns null, heap untouched. -/
theorem alloc32_zero (hi1 : BitVec 20) (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12)
    (hi3 : BitVec 20) (lo3 : BitVec 12) (base ra n : Word) (hn0 : n = 0) :
    cpsTripleWithin 2 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n)) := by
  have hbeq := cpsBranchWithin_takenStripPure2
    (beq_spec_gen_within .x10 .x0 0x0040#13 n 0 base)
    (fun hp hq => (pure_end2 hp hq) hn0)
  have e : base + signExtend13 0x0040#13 = base + 64 := by
    rw [show signExtend13 0x0040#13 = (64 : Word) from by decide]
  rw [e] at hbeq
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 64)
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) 0 base (by rw [alloc32Prog_length]; decide) (by rw [alloc32Prog_length]; decide) (by simp))) hbeq
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base (alloc32Prog hi1 lo1 hi2 lo2 hi3 lo3) 16 (base + 64) (by rw [alloc32Prog_length]; decide) (by rw [alloc32Prog_length]; decide) (by rfl))) hj
  runBlock hbeq hj

/-- `malloc(n)`, `n ≠ 0` bytes that fit below the heap end. -/
theorem malloc_spec (base ra n r14 r15 hn hcell hend : Word)
    (h_hcell1 : pcrel (base + 4) 0x1fff7#20 0xc90#12 = hcell)
    (h_hend : pcrel (base + 12) 0x23ff7#20 0xca8#12 = hend)
    (h_hcell3 : pcrel (base + 48 + 4) 0x1fff7#20 0xc60#12 = hcell)
    (hn0 : n ≠ 0)
    (hfit : ¬ BitVec.ult (hend - round32 hn) n) :
    cpsTripleWithin 14 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_malloc.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (hcell ↦ₘ hn))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (round32 hn + signExtend12 0x000#12)) **
       (.x14 ↦ᵣ (base + (48 : Word) + (4 : Word) + (((0x1fff7#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (.x15 ↦ᵣ round32 hn) ** (hcell ↦ₘ (n + round32 hn))) := by
  rw [f_malloc_eq]
  exact alloc32_spec _ _ _ _ _ _ base ra n r14 r15 hn hcell hend h_hcell1 h_hend h_hcell3 hn0 hfit

/-- `malloc(n)` with `n = 0`: returns null. -/
theorem malloc_zero (base ra n : Word) (hn0 : n = 0) :
    cpsTripleWithin 2 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_malloc.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n)) := by
  rw [f_malloc_eq]
  exact alloc32_zero _ _ _ _ _ _ base ra n hn0

/-- `operator new(n)` (the copy at `0x80009f70`), `n ≠ 0` bytes that fit below the heap end. -/
theorem new_9f70_spec (base ra n r14 r15 hn hcell hend : Word)
    (h_hcell1 : pcrel (base + 4) 0x1fff7#20 0x9ec#12 = hcell)
    (h_hend : pcrel (base + 12) 0x23ff7#20 0xa04#12 = hend)
    (h_hcell3 : pcrel (base + 48 + 4) 0x1fff7#20 0x9bc#12 = hcell)
    (hn0 : n ≠ 0)
    (hfit : ¬ BitVec.ult (hend - round32 hn) n) :
    cpsTripleWithin 14 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_new_80009f70.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (hcell ↦ₘ hn))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (round32 hn + signExtend12 0x000#12)) **
       (.x14 ↦ᵣ (base + (48 : Word) + (4 : Word) + (((0x1fff7#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (.x15 ↦ᵣ round32 hn) ** (hcell ↦ₘ (n + round32 hn))) := by
  rw [f_new_9f70_eq]
  exact alloc32_spec _ _ _ _ _ _ base ra n r14 r15 hn hcell hend h_hcell1 h_hend h_hcell3 hn0 hfit

/-- `operator new(n)` (the copy at `0x80009f70`) with `n = 0`: returns null. -/
theorem new_9f70_zero (base ra n : Word) (hn0 : n = 0) :
    cpsTripleWithin 2 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_new_80009f70.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n)) := by
  rw [f_new_9f70_eq]
  exact alloc32_zero _ _ _ _ _ _ base ra n hn0

/-- `operator new[](n)` (the copy at `0x80009fb4`, called by `Intercode::pad`), `n ≠ 0` bytes that fit below the heap end. -/
theorem new_9fb4_spec (base ra n r14 r15 hn hcell hend : Word)
    (h_hcell1 : pcrel (base + 4) 0x1fff7#20 0x9a8#12 = hcell)
    (h_hend : pcrel (base + 12) 0x23ff7#20 0x9c0#12 = hend)
    (h_hcell3 : pcrel (base + 48 + 4) 0x1fff7#20 0x978#12 = hcell)
    (hn0 : n ≠ 0)
    (hfit : ¬ BitVec.ult (hend - round32 hn) n) :
    cpsTripleWithin 14 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_new_80009fb4.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) **
       (hcell ↦ₘ hn))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ (round32 hn + signExtend12 0x000#12)) **
       (.x14 ↦ᵣ (base + (48 : Word) + (4 : Word) + (((0x1fff7#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (.x15 ↦ᵣ round32 hn) ** (hcell ↦ₘ (n + round32 hn))) := by
  rw [f_new_9fb4_eq]
  exact alloc32_spec _ _ _ _ _ _ base ra n r14 r15 hn hcell hend h_hcell1 h_hend h_hcell3 hn0 hfit

/-- `operator new[](n)` (the copy at `0x80009fb4`, called by `Intercode::pad`) with `n = 0`: returns null. -/
theorem new_9fb4_zero (base ra n : Word) (hn0 : n = 0) :
    cpsTripleWithin 2 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_new_80009fb4.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ n)) := by
  rw [f_new_9fb4_eq]
  exact alloc32_zero _ _ _ _ _ _ base ra n hn0

/-! ## `aligned_alloc` -/

theorem aa_neg (base al r13 : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.SUB .x13 .x0 .x10])
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ al) ** (.x13 ↦ᵣ r13))
      ((.x0 ↦ᵣ 0) ** (.x10 ↦ᵣ al) ** (.x13 ↦ᵣ ((0 : Word) - al))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem aa_round (hi : BitVec 20) (lo oA : BitVec 12) (base al m r14 hn : Word) :
    cpsTripleWithin 6 base (base + 24) (CodeReq.ofProg base [
      .AUIPC .x14 hi, .ADDI .x14 .x14 lo, .ADDI .x15 .x15 oA, .ADD .x10 .x15 .x10,
      .AND .x10 .x10 .x13, .SUB .x14 .x14 .x10])
      ((.x10 ↦ᵣ al) ** (.x13 ↦ᵣ m) ** (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ hn))
      ((.x10 ↦ᵣ ((hn + signExtend12 oA + al) &&& m)) ** (.x13 ↦ᵣ m) **
       (.x14 ↦ᵣ (pcrel base hi lo - ((hn + signExtend12 oA + al) &&& m))) **
       (.x15 ↦ᵣ (hn + signExtend12 oA))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem aa_add (base n p : Word) :
    cpsTripleWithin 1 base (base + 4) (CodeReq.ofProg base [.ADD .x11 .x11 .x10])
      ((.x10 ↦ᵣ p) ** (.x11 ↦ᵣ n))
      ((.x10 ↦ᵣ p) ** (.x11 ↦ᵣ (n + p))) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

theorem aa_store (hi : BitVec 20) (lo : BitVec 12) (base v r15 hn : Word) :
    cpsTripleWithin 2 base (base + 8) (CodeReq.ofProg base [.AUIPC .x15 hi, .SD .x15 .x11 lo])
      ((.x11 ↦ᵣ v) ** (.x15 ↦ᵣ r15) ** (pcrel base hi lo ↦ₘ hn))
      ((.x11 ↦ᵣ v) ** (.x15 ↦ᵣ (base + ((hi.zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (pcrel base hi lo ↦ₘ v)) := by
  simp only [CodeReq.ofProg_cons, CodeReq.ofProg_nil]
  (runBlock)

/-- The heap pointer rounded up to `al` (a power of two): `(hn - 1 + al) &&& -al`. -/
def alignUp (al hn : Word) : Word := (hn + signExtend12 0xfff#12 + al) &&& ((0 : Word) - al)

/-- `aligned_alloc(al, n)`, `n ≠ 0` bytes that fit: returns `alignUp al hn`
    and stores `n + alignUp al hn` in the heap pointer cell. -/
theorem aligned_alloc_spec (base ra al n r13 r14 r15 hn hcell hend : Word)
    (h_hcell1 : pcrel (base + 4) 0x1fff7#20 0xce0#12 = hcell)
    (h_hend : pcrel (base + 16) 0x23ff7#20 0xcf4#12 = hend)
    (h_hcell3 : pcrel (base + 60) 0x1fff7#20 0xca8#12 = hcell)
    (hn0 : n ≠ 0)
    (hfit : ¬ BitVec.ult (hend - alignUp al hn) n) :
    cpsTripleWithin 16 base ((ra + signExtend12 0x000#12) &&& ~~~1)
      (CodeReq.ofProg base Image.f_aligned_alloc.prog)
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ al) ** (.x11 ↦ᵣ n) ** (.x13 ↦ᵣ r13) **
       (.x14 ↦ᵣ r14) ** (.x15 ↦ᵣ r15) ** (hcell ↦ₘ hn))
      ((.x0 ↦ᵣ 0) ** (.x1 ↦ᵣ ra) ** (.x10 ↦ᵣ alignUp al hn) ** (.x11 ↦ᵣ (n + alignUp al hn)) **
       (.x13 ↦ᵣ ((0 : Word) - al)) ** (.x14 ↦ᵣ (hend - alignUp al hn)) **
       (.x15 ↦ᵣ (base + (60 : Word) + (((0x1fff7#20 : BitVec 20).zeroExtend 32 : BitVec 32) <<< 12).signExtend 64)) **
       (hcell ↦ₘ (n + alignUp al hn))) := by
  have hbeq := cpsBranchWithin_ntakenStripPure2
    (beq_spec_gen_within .x11 .x0 0x0048#13 n 0 base)
    (fun hp hq => hn0 (pure_end2 hp hq))
  have h1 := load_pcrel 0x1fff7#20 0xce0#12 (base + 4) r15 hn
  have h2 := aa_neg (base + 12) al r13
  have h3 := aa_round 0x23ff7#20 0xcf4#12 0xfff#12 (base + 16) al ((0 : Word) - al) r14 hn
  rw [h_hcell1] at h1
  rw [h_hend, show (hn + signExtend12 0xfff#12 + al) &&& ((0 : Word) - al) = alignUp al hn from rfl] at h3
  have hbgeu := cpsBranchWithin_takenStripPure2
    (bgeu_spec_gen_within .x14 .x11 0x0010#13 (hend - alignUp al hn) n (base + 40))
    (fun hp hq => hfit (pure_end2 hp hq))
  have e : base + 40 + signExtend13 0x0010#13 = base + 56 := by rv64_addr
  rw [e] at hbgeu
  have h4 := aa_add (base + 56) n (alignUp al hn)
  have h5 := aa_store 0x1fff7#20 0xca8#12 (base + 60) (n + alignUp al hn) (hn + signExtend12 0xfff#12) hn
  rw [h_hcell3] at h5
  have hj := jalr_x0_spec_gen_within .x1 ra 0x000#12 (base + 68)
  have hbeq := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_aligned_alloc.prog 0 base (by decide) (by decide) (by simp))) hbeq
  have h1 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 4) Image.f_aligned_alloc.prog _ 1 (by rfl) (by decide) (by decide) (by decide)) h1
  have h2 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 12) Image.f_aligned_alloc.prog _ 3 (by rfl) (by decide) (by decide) (by decide)) h2
  have h3 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 16) Image.f_aligned_alloc.prog _ 4 (by rfl) (by decide) (by decide) (by decide)) h3
  have hbgeu := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_aligned_alloc.prog 10 (base + 40) (by decide) (by decide) (by rfl))) hbgeu
  have h4 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 56) Image.f_aligned_alloc.prog _ 14 (by rfl) (by decide) (by decide) (by decide)) h4
  have h5 := cpsTripleWithin_extend_code
    (CodeReq.ofProg_mono_sub base (base + 60) Image.f_aligned_alloc.prog _ 15 (by rfl) (by decide) (by decide) (by decide)) h5
  have hj := cpsTripleWithin_extend_code (CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base Image.f_aligned_alloc.prog 17 (base + 68) (by decide) (by decide) (by rfl))) hj
  runBlock hbeq h1 h2 h3 hbgeu h4 h5 hj

end PureInterp.Entry
