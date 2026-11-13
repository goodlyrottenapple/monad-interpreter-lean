import RiscvZkvm.Rv64.Logic.SepLogic
import RiscvZkvm.Rv64.Logic.ByteOps
import RiscvZkvm.Rv64.Execution
import PureInterp.Image.Index

/-!
# The linked image as one code requirement

`imageCode` is the code requirement of the whole text segment: all functions
of `Image.functions`, concatenated, loaded at `textBase`.

The functions are contiguous (checked once, by kernel evaluation, in
`functions_layout`), so every function's own `CodeReq.ofProg f.addr f.prog` is
included in `imageCode`. The per-function statements are generated into
`LinkIncluded.lean`; each is one application of `included_of_index` to a
`rfl` proof that the function is the `k`-th entry of `functions`.

`ImageLoaded s` says a machine state holds the image: the text segment in the
code map and the read-only data segment in memory.
-/

set_option maxRecDepth 100000

open RiscvZkvm.Rv64

namespace PureInterp.Image

/-! ## Generic facts about `CodeReq.ofProg` -/

/-- Every address of `ofProg base prog` is `base + 4 * k` for an index `k`. -/
theorem ofProg_some_index {base : Word} {prog : List Instr} {a : Word} {i : Instr}
    (h : CodeReq.ofProg base prog a = some i) :
    ∃ k, k < prog.length ∧ a = base + BitVec.ofNat 64 (4 * k) := by
  refine Classical.byContradiction fun hne => ?_
  have hnone := CodeReq.ofProg_none_range base prog (a := a) (fun k hk he => hne ⟨k, hk, he⟩)
  rw [hnone] at h
  cases h

/-- `ofProg` is exactly indexing, for a program that fits in the address space. -/
theorem ofProg_eq_some_iff {base : Word} {prog : List Instr} (hb : 4 * prog.length < 2 ^ 64)
    {a : Word} {i : Instr} :
    CodeReq.ofProg base prog a = some i ↔
      ∃ k, a = base + BitVec.ofNat 64 (4 * k) ∧ prog[k]? = some i := by
  constructor
  · intro h
    obtain ⟨k, hk, ha⟩ := ofProg_some_index h
    refine ⟨k, ha, ?_⟩
    have hl := CodeReq.ofProg_lookup base prog k hk hb
    rw [← ha, h] at hl
    rw [List.getElem?_eq_getElem hk]
    exact hl.symm
  · rintro ⟨k, ha, hk⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    rw [ha]
    exact CodeReq.ofProg_lookup base prog k hlt hb

/-! ## Contiguous layouts -/

/-- All instructions of a list of functions, in order. -/
def concat (fs : List (Word × List Instr)) : List Instr := fs.flatMap (·.2)

/-- `fs` is laid out without gaps from address `base` (a natural number). -/
def layout : Nat → List (Word × List Instr) → Bool
  | _, [] => true
  | base, f :: rest => f.1.toNat == base && layout (base + 4 * f.2.length) rest

/-- The end address of a layout starting at `base`. -/
def layoutEnd : Nat → List (Word × List Instr) → Nat
  | base, [] => base
  | base, f :: rest => layoutEnd (base + 4 * f.2.length) rest

theorem layoutEnd_eq (base : Nat) (fs : List (Word × List Instr)) :
    layoutEnd base fs = base + 4 * (concat fs).length := by
  induction fs generalizing base with
  | nil => simp [layoutEnd, concat]
  | cons f rest ih =>
    have h := ih (base + 4 * f.2.length)
    simp only [concat, List.flatMap_cons, List.length_append] at h ⊢
    simp only [layoutEnd]
    omega

/-- In a gap-free layout, the `k`-th function sits at `base + 4 * (number of
instructions before it)`, and the concatenation splits around it. -/
theorem layout_split {base : Word} {fs : List (Word × List Instr)}
    (hl : layout base.toNat fs = true) (hb : base.toNat + 4 * (concat fs).length < 2 ^ 64)
    {k : Nat} {a : Word} {p : List Instr} (hk : fs[k]? = some (a, p)) :
    ∃ pre post, concat fs = pre ++ p ++ post ∧ a = base + BitVec.ofNat 64 (4 * pre.length) := by
  induction fs generalizing base k with
  | nil => simp at hk
  | cons f rest ih =>
    simp only [layout, Bool.and_eq_true, beq_iff_eq] at hl
    obtain ⟨hf, hrest⟩ := hl
    have hcat : concat (f :: rest) = f.2 ++ concat rest := by simp [concat]
    rw [hcat, List.length_append] at hb
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨[], concat rest, by simp [hcat], ?_⟩
      apply BitVec.eq_of_toNat_eq
      simpa using hf
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have hbase : (base + BitVec.ofNat 64 (4 * f.2.length)).toNat = base.toNat + 4 * f.2.length := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      obtain ⟨pre, post, hc, ha⟩ := ih (base := base + BitVec.ofNat 64 (4 * f.2.length))
        (by rw [hbase]; exact hrest) (by rw [hbase]; omega) hk
      refine ⟨f.2 ++ pre, post, by simp [hcat, hc], ?_⟩
      rw [ha, List.length_append]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

/-- In a gap-free layout, each function's own code requirement is included in
the code requirement of the concatenation. -/
theorem included_of_layout {base : Word} {fs : List (Word × List Instr)}
    (hl : layout base.toNat fs = true) (hb : base.toNat + 4 * (concat fs).length < 2 ^ 64)
    {k : Nat} {a : Word} {p : List Instr} (hk : fs[k]? = some (a, p)) :
    ∀ x i, CodeReq.ofProg a p x = some i → CodeReq.ofProg base (concat fs) x = some i := by
  intro x i h
  obtain ⟨pre, post, hc, ha⟩ := layout_split hl hb hk
  have hlen : (concat fs).length = pre.length + p.length + post.length := by
    rw [hc]; simp [Nat.add_assoc]
  obtain ⟨j, hx, hj⟩ := (ofProg_eq_some_iff (by omega)).mp h
  refine (ofProg_eq_some_iff (by omega)).mpr ⟨pre.length + j, ?_, ?_⟩
  · rw [hx, ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · have hjlt : j < p.length := (List.getElem?_eq_some_iff.mp hj).1
    rw [hc, List.append_assoc, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, List.getElem?_append_left hjlt]
    exact hj

/-! ## The image -/

/-- All instructions of the text segment, in address order. -/
def imageProg : List Instr := concat functions

/-- The code requirement of the whole text segment. -/
def imageCode : CodeReq := CodeReq.ofProg textBase imageProg

/-- The functions are contiguous from `textBase`. -/
theorem functions_layout : layout textBase.toNat functions = true := by decide

/-- The text segment ends at `0x8000adb4`: 11,117 instructions. -/
theorem functions_layoutEnd : layoutEnd textBase.toNat functions = 0x8000adb4 := by decide

theorem imageProg_length : imageProg.length = 11117 := by
  have h := layoutEnd_eq textBase.toNat functions
  rw [functions_layoutEnd] at h
  have ht : textBase.toNat = 0x80000000 := by decide
  rw [ht] at h
  unfold imageProg
  omega

theorem imageProg_bound : textBase.toNat + 4 * (concat functions).length < 2 ^ 64 := by
  have h := imageProg_length
  have ht : textBase.toNat = 0x80000000 := by decide
  unfold imageProg at h
  rw [ht, h]
  decide

/-- The one lemma behind every generated `f_x.included`: the `k`-th function
of the image is included in `imageCode`. -/
theorem included_of_index {k : Nat} {a : Word} {p : List Instr}
    (hk : functions[k]? = some (a, p)) :
    ∀ x i, CodeReq.ofProg a p x = some i → imageCode x = some i :=
  included_of_layout functions_layout imageProg_bound hk

/-- `imageCode` is exactly indexing into `imageProg`. -/
theorem imageCode_eq_some_iff {a : Word} {i : Instr} :
    imageCode a = some i ↔
      ∃ k, a = textBase + BitVec.ofNat 64 (4 * k) ∧ imageProg[k]? = some i :=
  ofProg_eq_some_iff (by rw [imageProg_length]; decide)

/-! ## Loaded states -/

/-- The read-only data segment as doublewords: entry `d` is the little-endian
doubleword at `data0.addr + 8 * d`. -/
def dataWord (d : Nat) : Word := packBytes ((data0.bytes.drop (8 * d)).take 8)

/-- The machine state holds the image: the text segment is in the code map and
the data segment is in (doubleword-granular) memory at `data0.addr`. -/
structure ImageLoaded (s : MachineState) : Prop where
  code : ProgramAt s.code textBase imageProg
  data : ∀ d, 8 * d < data0.bytes.length →
    s.mem (data0.addr + BitVec.ofNat 64 (8 * d)) = dataWord d

theorem ImageLoaded.satisfied {s : MachineState} (h : ImageLoaded s) :
    imageCode.SatisfiedBy s := by
  intro a i hai
  obtain ⟨k, ha, hk⟩ := imageCode_eq_some_iff.mp hai
  have hlt : k < imageProg.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [ha, h.code k hlt]
  exact hk

/-- A function included in `imageCode` is in the code map of a loaded state. -/
theorem ImageLoaded.satisfied_of_included {s : MachineState} (h : ImageLoaded s)
    {cr : CodeReq} (hcr : ∀ a i, cr a = some i → imageCode a = some i) :
    cr.SatisfiedBy s :=
  fun a i hai => h.satisfied a i (hcr a i hai)

/-- A state whose code map is `loadProgram textBase imageProg` holds the text
segment. -/
theorem programAt_loadProgram :
    ProgramAt (loadProgram textBase imageProg) textBase imageProg :=
  loadProgram_programAt (by rw [imageProg_length]; decide)

end PureInterp.Image
