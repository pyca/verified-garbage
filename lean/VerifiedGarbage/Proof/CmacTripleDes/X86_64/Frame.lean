import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.CmacTripleDes.X86_64
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit`. -/
section

/-!
# The DES block's x86-64 code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.X86_64.leaf 64
materialize_value Impl.CmacTripleDes.X86_64.inputs
materialize_value Impl.CmacTripleDes.X86_64.sboxes
materialize_value Impl.CmacTripleDes.X86_64.output
materialize_value Impl.CmacTripleDes.X86_64.ipCode
materialize_value Impl.CmacTripleDes.X86_64.fpCode
materialize_code Impl.CmacTripleDes.X86_64.block

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Round`. -/
section

/-!
# A DES round on x86-64

The round's three parts are checked by evaluation (`Straight.check`): the
broadcast inputs (`inputs`) and the output (`output`), which only move,
mask and XOR bits, over the lane domain; the S-boxes (`sboxes`), which
combine words bitwise with constants that differ by position, over the row
domain (`Bitslice.rows`), on all 64 values of a box's input at once.
`round_ok` composes them: `R` and `L ⊕ f(R, K)`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86_64

/-- The round's memory: the broadcast inputs in slots 0–5 at `r15`, and the
round key at `r14`. -/
def rCfg : Cfg := { base := .r15, slots := 6, ext := .r14, exts := 1 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : VG.X86_64.State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r15) k) 64

/-- The round key's word. -/
abbrev keyW (s : VG.X86_64.State) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r14) 0) 64

/-! ## The inputs -/

/-- Bit `p` of slot `t`: in lane `p / 6`, below its fifth bit, bit `t` of
the box's input, `R`'s bit (atom `0 … 63`) XOR the key's (atom `64 …`). -/
def inG (t p : Nat) : List Nat :=
  if p < 48 ∧ p % 6 < 4 then [expSrc (6 * (p / 6) + t), 64 + 6 * (p / 6) + t] else []

def inPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 6).all fun t => e.slot t == some (outWord (VG.Proof.CmacTripleDes.X86_64.inG t))

theorem inputs_check :
    VG.X86_64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.X86_64.rCfg (linExt 1) inputs (linEnv [(.r13, 0)]) VG.Proof.CmacTripleDes.X86_64.inPost = true := by
  lit_decide

theorem inG_lt : ∀ t < 6, ∀ p < 64, ∀ a ∈ VG.Proof.CmacTripleDes.X86_64.inG t p, a < 2 ^ 7 := by lit_decide

/-- The registers the round keeps. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r10, .r11, .r14, .r15]

theorem inputs_kept :
    (.r12 :: .r13 :: VG.Proof.CmacTripleDes.X86_64.kept).all (fun r => inputs.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The inputs of `inputs`: `R` and the round key. -/
def inW (s : VG.X86_64.State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .r13 else VG.Proof.CmacTripleDes.X86_64.keyW s

theorem inputs_ok {s : VG.X86_64.State} (hok : Ok VG.Proof.CmacTripleDes.X86_64.rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 6, ∀ p < 64, (VG.Proof.CmacTripleDes.X86_64.slotW s' t).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86_64.inW s) (VG.Proof.CmacTripleDes.X86_64.inG t p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: VG.Proof.CmacTripleDes.X86_64.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.X86_64.inputs_check
  have hrel : Rel (LaneRel 7 (assign (VG.Proof.CmacTripleDes.X86_64.inW s) (2 ^ 7))) VG.Proof.CmacTripleDes.X86_64.rCfg (linExt 1) (linEnv [(.r13, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_⟩
    · simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel (VG.Proof.CmacTripleDes.X86_64.inW s) (i := 0) (by decide)
      · simp at h
    · simp only [VG.Proof.CmacTripleDes.X86_64.rCfg] at hj
      obtain rfl : j = 0 := by omega
      simp only [linExt, Option.some.injEq] at h; subst h
      exact inWord_rel (VG.Proof.CmacTripleDes.X86_64.inW s) (i := 1) (by decide)
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun t ht q hq => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost t (List.mem_range.mpr ht)
    simp only [beq_iff_eq] at h
    exact outWord_rel (VG.Proof.CmacTripleDes.X86_64.inG_lt t ht) (p.rel.slot t _ (by simp only [VG.Proof.CmacTripleDes.X86_64.rCfg]; omega) h) q hq
  · rw [List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.inputs_kept r hr]; decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 64).testBit t) 4096

def sbEnv : Env Nat := { reg := fun _ => none, slot := fun t => if t < 6 then some (VG.Proof.CmacTripleDes.X86_64.rowIn t) else none }

/-- At bit `6 (7 - i) + off i b`, output bit `b` of box `i`, on every row. -/
def sbPost (e : Env Nat) : Bool :=
  match e.reg .rax with
  | some F => (List.range 8).all fun i => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (64 * c + (6 * (7 - i) + off i b)) == (Proof.TripleDes.outputTable i b).testBit c
  | none => false

theorem sboxes_check : VG.X86_64.Straight.check (rows 64 6) VG.Proof.CmacTripleDes.X86_64.rCfg (fun _ => none) sboxes VG.Proof.CmacTripleDes.X86_64.sbEnv VG.Proof.CmacTripleDes.X86_64.sbPost = true := by
  lit_decide

theorem sboxes_kept :
    (.r12 :: .r13 :: VG.Proof.CmacTripleDes.X86_64.kept).all (fun r => sboxes.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The input of the box whose lane holds bit `p`, from bit `p` of the slots. -/
def boxIn (s : VG.X86_64.State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (VG.Proof.CmacTripleDes.X86_64.slotW s t).getLsbD p

theorem sboxes_ok {s : VG.X86_64.State} (hok : Ok VG.Proof.CmacTripleDes.X86_64.rCfg s) :
    ∃ s', runBlock isa sboxes s = some s' ∧
      (∀ i < 8, ∀ b < 4, (s'.gpr .rax).getLsbD (6 * (7 - i) + off i b) =
        (Spec.TripleDes.sBox i (VG.Proof.CmacTripleDes.X86_64.boxIn s (6 * (7 - i) + off i b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: VG.Proof.CmacTripleDes.X86_64.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.X86_64.sboxes_check
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .rax = some F ∧ ∀ i < 8, ∀ b < 4, ∀ c < 64,
      F.testBit (64 * c + (6 * (7 - i) + off i b)) = (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [VG.Proof.CmacTripleDes.X86_64.sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun i hi b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost i
        (List.mem_range.mpr hi)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  have key : ∀ p < 64, ∃ s', runBlock isa sboxes s = some s' ∧
      Post (RowRel p (VG.Proof.CmacTripleDes.X86_64.boxIn s p).toNat) VG.Proof.CmacTripleDes.X86_64.rCfg (fun _ => none) e' s s'
        (fun r => (sboxes.all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (VG.Proof.CmacTripleDes.X86_64.boxIn s p).isLt) hok
      ⟨fun r a h => by simp [VG.Proof.CmacTripleDes.X86_64.sbEnv] at h, fun t a ht h => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [VG.Proof.CmacTripleDes.X86_64.sbEnv] at h
    split at h
    · rename_i ht6
      cases h
      show (VG.Proof.CmacTripleDes.X86_64.rowIn t).testBit (64 * (VG.Proof.CmacTripleDes.X86_64.boxIn s p).toNat + p) = (VG.Proof.CmacTripleDes.X86_64.slotW s t).getLsbD p
      have hc := (VG.Proof.CmacTripleDes.X86_64.boxIn s p).isLt
      rw [VG.Proof.CmacTripleDes.X86_64.rowIn, testBit_tableOf, decide_eq_true (by omega : 64 * (boxIn s p).toNat + p < 4096),
        Bool.true_and, show (64 * (VG.Proof.CmacTripleDes.X86_64.boxIn s p).toNat + p) / 64 = (VG.Proof.CmacTripleDes.X86_64.boxIn s p).toNat by omega,
        BitVec.testBit_toNat, VG.Proof.CmacTripleDes.X86_64.boxIn, getLsbD_ofBits, decide_eq_true ht6, Bool.true_and]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun i hi b hb => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hp : 6 * (7 - i) + off i b < 64 := by revert i b; decide
    obtain ⟨s'', hs'', p₁⟩ := key _ hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg .rax F hF
    simp only [RowRel] at h
    rw [← h, hout i hi b hb _ (VG.Proof.CmacTripleDes.X86_64.boxIn s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.sboxes_kept r hr]; decide

/-! ## The output -/

/-- No memory. -/
def oCfg : Cfg := { base := .r15, slots := 0, ext := .r14, exts := 0 }

/-- `r12`: `R` (input word 2). -/
def oG12 (p : Nat) : List Nat := [128 + p]

/-- `r13`: bit `j` of `L` (input word 1) XOR, for `j < 32`, the S-boxes' bit
`pSrc j` (in `rax`, input word 0). -/
def oG13 (p : Nat) : List Nat := if p < 32 then [outPos (pSrc p), 64 + p] else [64 + p]

def oIns : List (Reg × Nat) := [(.rax, 0), (.r12, 1), (.r13, 2)]

theorem output_check :
    VG.X86_64.Straight.check (lanes 64 8) VG.Proof.CmacTripleDes.X86_64.oCfg (linExt 3) output (linEnv VG.Proof.CmacTripleDes.X86_64.oIns) (linPost 8 [(.r12, VG.Proof.CmacTripleDes.X86_64.oG12), (.r13, VG.Proof.CmacTripleDes.X86_64.oG13)]) = true := by
  lit_decide

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by
  lit_decide

/-- The inputs of `output`. -/
def oW (s : VG.X86_64.State) (i : Nat) : BitVec 64 :=
  if i = 0 then s.gpr .rax else if i = 1 then s.gpr .r12 else s.gpr .r13

theorem oCfg_ok (s : VG.X86_64.State) : Ok VG.Proof.CmacTripleDes.X86_64.oCfg s :=
  ⟨fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg]), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg]), by decide,
    fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg])⟩

theorem output_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa output s = some s' ∧
      (∀ p < 64, (s'.gpr .r12).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86_64.oW s) (VG.Proof.CmacTripleDes.X86_64.oG12 p)) ∧
      (∀ p < 64, (s'.gpr .r13).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86_64.oW s) (VG.Proof.CmacTripleDes.X86_64.oG13 p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86_64.kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.X86_64.output_check (VG.Proof.CmacTripleDes.X86_64.oCfg_ok s) (VG.Proof.CmacTripleDes.X86_64.oW s)
    (fun r i hri => by
      simp only [VG.Proof.CmacTripleDes.X86_64.oIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg]))
  refine ⟨s', hs', hout .r12 VG.Proof.CmacTripleDes.X86_64.oG12 (by simp), hout .r13 VG.Proof.CmacTripleDes.X86_64.oG13 (by simp), hrd, hwr,
    fun r hr => hoth r (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.output_kept r hr), ?_⟩
  funext a
  exact hfr a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, VG.Proof.CmacTripleDes.X86_64.oCfg, Region.Contains]

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : VG.X86_64.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : VG.X86_64.State}
    (h : ∀ t < 6, ∀ p < 64, (VG.Proof.CmacTripleDes.X86_64.slotW s₁ t).getLsbD p = xorBits (VG.Proof.CmacTripleDes.X86_64.inW s) (VG.Proof.CmacTripleDes.X86_64.inG t p))
    {i o : Nat} (hi : i < 8) (ho : o < 4) :
    VG.Proof.CmacTripleDes.X86_64.boxIn s₁ (6 * (7 - i) + o) = chunk ((s.gpr .r13).setWidth 32) ((VG.Proof.CmacTripleDes.X86_64.keyW s).setWidth 48) i := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hE := VG.Proof.CmacTripleDes.X86_64.expSrc_lt (6 * (7 - i) + t) (by omega)
  rw [VG.Proof.CmacTripleDes.X86_64.boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, h t ht _ (by omega),
    getLsbD_chunk _ _ hi ht, VG.Proof.CmacTripleDes.X86_64.inG, ite_eq_left (by omega), show (6 * (7 - i) + o) / 6 = 7 - i by omega]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86_64.inW, BitVec.getLsbD_setWidth,
    Nat.div_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega),
    Nat.mod_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega),
    show (64 + 6 * (7 - i) + t) / 64 = 1 by omega, show (64 + 6 * (7 - i) + t) % 64 = 6 * (7 - i) + t by omega,
    hE, show 6 * (7 - i) + t < 48 by omega, decide_true, Bool.true_and, ite_true]
  rfl

theorem off_lt : ∀ i < 8, ∀ b < 4, off i b < 4 := by decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on the low 32 bits of `r12` and
`r13`, with the round key the low 48 bits of `[r14]`. -/
theorem round_ok {s : VG.X86_64.State} (hok : Ok VG.Proof.CmacTripleDes.X86_64.rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      s'.gpr .r12 = s.gpr .r13 ∧
      (s'.gpr .r13).setWidth 32 = (s.gpr .r12).setWidth 32 ^^^
        Spec.TripleDes.roundFunction ((s.gpr .r13).setWidth 32) ((VG.Proof.CmacTripleDes.X86_64.keyW s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86_64.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s] s.mem s'.mem := by
  obtain ⟨s₁, h₁, hx, rd₁, wr₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.X86_64.inputs_ok hok
  have hok₁ : Ok VG.Proof.CmacTripleDes.X86_64.rCfg s₁ := hok.congr (k₁ .r15 (by simp [VG.Proof.CmacTripleDes.X86_64.kept])) (k₁ .r14 (by simp [VG.Proof.CmacTripleDes.X86_64.kept])) rd₁ wr₁
  obtain ⟨s₂, h₂, hy, rd₂, wr₂, k₂, f₂⟩ := VG.Proof.CmacTripleDes.X86_64.sboxes_ok hok₁
  obtain ⟨s₃, h₃, o12, o13, rd₃, wr₃, k₃, m₃⟩ := VG.Proof.CmacTripleDes.X86_64.output_ok s₂
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := (k₂ .r12 (by simp)).trans (k₁ .r12 (by simp))
  have r13₂ : s₂.gpr .r13 = s.gpr .r13 := (k₂ .r13 (by simp)).trans (k₁ .r13 (by simp))
  refine ⟨s₃, ?_, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    fun r hr => (k₃ r hr).trans ((k₂ r (by simp [hr])).trans (k₁ r (by simp [hr]))), ?_⟩
  · rw [round, VG.Proof.CmacTripleDes.X86_64.runBlock_append, VG.Proof.CmacTripleDes.X86_64.runBlock_append, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [o12 p hp, VG.Proof.CmacTripleDes.X86_64.oG12]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86_64.oW,
      show (128 + p) / 64 = 2 by omega, show (128 + p) % 64 = p by omega]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), r13₂]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := VG.Proof.CmacTripleDes.X86_64.pSrc_lt j hj
    have hi : 7 - pSrc j / 4 < 8 := by omega
    have hb : pSrc j % 4 < 4 := by omega
    have ho := VG.Proof.CmacTripleDes.X86_64.off_lt _ hi _ hb
    have hpos : outPos (pSrc j) = 6 * (7 - (7 - pSrc j / 4)) + off (7 - pSrc j / 4) (pSrc j % 4) := by
      rw [outPos, show 7 - (7 - pSrc j / 4) = pSrc j / 4 by omega]
    rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, o13 j (by omega), VG.Proof.CmacTripleDes.X86_64.oG13, ite_eq_left hj,
      BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and,
      getLsbD_roundFunction _ _ hj]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.X86_64.oW]
    rw [Nat.div_eq_of_lt (show outPos (pSrc j) < 64 by omega), Nat.mod_eq_of_lt (show outPos (pSrc j) < 64 by omega),
      show (64 + j) / 64 = 1 by omega, show (64 + j) % 64 = j by omega, ite_eq_left rfl, ite_eq_right (by decide),
      ite_eq_left rfl, r12₂, hpos, hy _ hi _ hb, VG.Proof.CmacTripleDes.X86_64.boxIn_eq hx hi ho, Bool.xor_comm]
  · have hr : slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s₁ = slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s := by
      simp only [slotRegion]; rw [show rCfg.base = .r15 from rfl, k₁ .r15 (by simp [VG.Proof.CmacTripleDes.X86_64.kept])]
    rw [hr] at f₂
    rw [m₃]; exact f₁.trans f₂

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Block`. -/
section

/-!
# TDEA on x86-64: the passes and the block

`block` encrypts the 64-bit block in `rax` with the key schedule at `r14`
(`block_ok`): `IP` into `r12` and `r13`, three passes of sixteen rounds
(`pass_ok`, the round keys `rbx` bytes apart, the halves exchanged after
each pass), and `IP⁻¹`. During the block, `r14` points to slot
`kpos p j` of the key schedule before round `j` of pass `p`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `r14` readable, and the slots
0–5 of the scratch buffer at `r15` writable, apart from it. -/
structure BlockPre (s : VG.X86_64.State) : Prop where
  sched : ∃ R ∈ s.rd ++ s.wr, R.base = s.gpr .r14 ∧ 384 ≤ R.len ∧ R.len < 2 ^ 64
  scr : ∃ R ∈ s.wr, R.base = s.gpr .r15 ∧ 48 ≤ R.len ∧ R.len < 2 ^ 64
  disj : Region.Disjoint ⟨s.gpr .r15, 48⟩ ⟨s.gpr .r14, 384⟩

/-- The slots of the broadcast inputs. -/
abbrev xR (s₀ : VG.X86_64.State) : Region := ⟨s₀.gpr .r15, 48⟩

/-- What the block keeps. -/
structure Same (s₀ s : VG.X86_64.State) : Prop where
  r15 : s.gpr .r15 = s₀.gpr .r15
  rbp : s.gpr .rbp = s₀.gpr .rbp
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.X86_64.xR s₀] s₀.mem s.mem

theorem Same.refl (s : VG.X86_64.State) : VG.Proof.CmacTripleDes.X86_64.Same s s := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : VG.X86_64.State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .r14)

theorem wordAddr_zero (a : Addr) : wordAddr a 0 = a := by simp [wordAddr]

theorem ok_at {s₀ s : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86_64.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : Ok VG.Proof.CmacTripleDes.X86_64.rCfg s := by
  obtain ⟨R, hR, hRb, hRl, hRw⟩ := hp.sched
  obtain ⟨X, hX, hXb, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, by decide, fun k hk' j hj => ?_⟩
  · rw [h.wr]
    exact ⟨X, hX, contains_word (off := 0) (by show s.gpr .r15 = _; rw [h.r15, ← hXb]; simp)
      (by simp only [VG.Proof.CmacTripleDes.X86_64.rCfg] at hk'; omega) hXl hXw⟩
  · simp only [VG.Proof.CmacTripleDes.X86_64.rCfg] at hk'
    obtain rfl : k = 0 := by omega
    rw [h.rd, h.wr]
    exact ⟨R, hR, contains_word (off := 8 * n) (by show s.gpr .r14 = _; rw [hk, hRb]) (by omega) hRl hRw⟩
  · simp only [VG.Proof.CmacTripleDes.X86_64.rCfg] at hk' hj
    obtain rfl : j = 0 := by omega
    rw [show rCfg.base = .r15 from rfl, show rCfg.ext = .r14 from rfl, h.r15, hk, VG.Proof.CmacTripleDes.X86_64.wordAddr_zero]
    exact hp.disj.sep (VG.X86_64.Straight.slot_contains _ hk' (by decide)) (Offset.contains_base _ (by omega) (by omega))

theorem key_at {s₀ s : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) (h : VG.Proof.CmacTripleDes.X86_64.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * n)) : VG.Proof.CmacTripleDes.X86_64.keyW s = (VG.Proof.CmacTripleDes.X86_64.sch s₀).getD n 0 := by
  rw [scheduleAt_getD _ _ hn, VG.Proof.CmacTripleDes.X86_64.keyW, VG.Proof.CmacTripleDes.X86_64.wordAddr_zero, hk]
  refine h.frame.readW (r := ⟨s₀.gpr .r14 + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.disj.sub_right (Offset.sub_base _ (by omega))).symm

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + s.gpr .rbx ∧ s'.gpr .r11 = s.gpr .r11 - 1 ∧
      s'.zf = some ((s.gpr .r11 - 1) == 0) ∧ (∀ r, r ≠ .r14 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, roundTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 64 := if p % 2 = 1 then BitVec.ofNat 64 (2 ^ 64 - 8) else BitVec.ofNat 64 8

theorem kpos_succ_addr (a : Addr) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p j) + VG.Proof.CmacTripleDes.X86_64.stride p = a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p (j + 1)) := by
  rw [BitVec.add_assoc, VG.Proof.CmacTripleDes.X86_64.stride, VG.Proof.CmacTripleDes.X86_64.kpos, VG.Proof.CmacTripleDes.X86_64.kpos]
  congr 1
  split
  · rename_i hodd
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : VG.X86_64.State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : VG.X86_64.State) : Prop where
  same : VG.Proof.CmacTripleDes.X86_64.Same s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p j)
  rbx : s.gpr .rbx = VG.Proof.CmacTripleDes.X86_64.stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (16 - j)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = VG.Proof.CmacTripleDes.rounds (passKeys (VG.Proof.CmacTripleDes.X86_64.sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : VG.Proof.CmacTripleDes.X86_64.kpos p j < 48 := by
  simp only [VG.Proof.CmacTripleDes.X86_64.kpos]; split <;> omega

theorem passKeys_at (s₀ : VG.X86_64.State) {p j : Nat} (hj : j < 16) :
    passKeys (VG.Proof.CmacTripleDes.X86_64.sch s₀) p j = ((VG.Proof.CmacTripleDes.X86_64.sch s₀).getD (VG.Proof.CmacTripleDes.X86_64.kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, VG.Proof.CmacTripleDes.X86_64.kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : VG.X86_64.State} (h : VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s fun s' =>
      s'.zf = some (decide (j + 1 = 16)) ∧ VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e12, e13, rd₁, wr₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.X86_64.round_ok (VG.Proof.CmacTripleDes.X86_64.ok_at hp h.same (VG.Proof.CmacTripleDes.X86_64.kpos_lt hp3 hj) h.r14)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t14, t11, tzf, tk, tm, trd, twr⟩ := VG.Proof.CmacTripleDes.X86_64.roundTail_ok s₁
  have kk : ∀ r ∈ VG.Proof.CmacTripleDes.X86_64.kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, kk .r11 (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.r11, VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega),
      VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r15 (by decide) (by decide), kk .r15 (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.same.r15]
  · rw [tk .rbp (by decide) (by decide), kk .rbp (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.same.rbp]
  · rw [tk .rsp (by decide) (by decide), kk .rsp (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.same.rsp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion VG.Proof.CmacTripleDes.X86_64.rCfg s = VG.Proof.CmacTripleDes.X86_64.xR s₀ := by
      simp only [slotRegion, VG.Proof.CmacTripleDes.X86_64.xR]; rw [show rCfg.base = .r15 from rfl, h.same.r15]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t14, kk .r14 (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), kk .rbx (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.r14, h.rbx, VG.Proof.CmacTripleDes.X86_64.kpos_succ_addr _ hp3 hj]
  · rw [tk .rbx (by decide) (by decide), kk .rbx (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.rbx]
  · rw [tk .r10 (by decide) (by decide), kk .r10 (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.r10]
  · rw [t11, kk .r11 (by simp [VG.Proof.CmacTripleDes.X86_64.kept]), h.r11, VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .r12 (by decide) (by decide), tk .r13 (by decide) (by decide), e12, e13,
      VG.Proof.CmacTripleDes.X86_64.key_at hp h.same (VG.Proof.CmacTripleDes.X86_64.kpos_lt hp3 hj) h.r14, VG.Proof.CmacTripleDes.X86_64.passKeys_at s₀ hj]

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : VG.X86_64.State} (h : VG.Proof.CmacTripleDes.X86_64.Same s₀ s) (h14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p 0))
    (hbx : s.gpr .rbx = VG.Proof.CmacTripleDes.X86_64.stride p) (h10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p))
    (hlr : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = lr) :
    WP isa pass s (VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩)
  have g : ∀ r, r ≠ .r11 → (s.setReg32 .r11 (16 : BitVec 32)).gpr r = s.gpr r := fun r hr => by
    simp [State.setReg32, gpr_setReg, hr]
  have h0 : VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr 0 (s.setReg32 .r11 (16 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide), h.r15], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp],
      h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h14], by rw [g _ (by decide), hbx],
      by rw [g _ (by decide), h10], by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide), g _ (by decide), hlr]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr 16)
    (fun (n : Nat) (t : VG.X86_64.State) => ∃ j, n = 16 - j ∧ j < 16 ∧ VG.Proof.CmacTripleDes.X86_64.PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, h0⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86_64.roundStep_ok hp hp3 hj ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 + (BitVec.ofNat 64 128 - s.gpr .rbx) ∧ s'.gpr .rbx = 0 - s.gpr .rbx ∧
      s'.gpr .r12 = s.gpr .r13 ∧ s'.gpr .r13 = s.gpr .r12 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some ((s.gpr .r10 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rax, .rbx, .r10, .r12, .r13, .r14] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, passTail, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, readSrc32, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      State.setReg32]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_setReg, zf_arithFlags]; simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : VG.X86_64.State) (x : BitVec 64) (p : Nat) (s : VG.X86_64.State) : Prop where
  same : VG.Proof.CmacTripleDes.X86_64.Same s₀ s
  r14 : s.gpr .r14 = s₀.gpr .r14 + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p 0)
  rbx : s.gpr .rbx = VG.Proof.CmacTripleDes.X86_64.stride p
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - p)
  halves : ((s.gpr .r12).setWidth 32, (s.gpr .r13).setWidth 32) = passes (VG.Proof.CmacTripleDes.X86_64.sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : Addr) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos p 16) + (BitVec.ofNat 64 128 - VG.Proof.CmacTripleDes.X86_64.stride p) =
      a + BitVec.ofNat 64 (8 * VG.Proof.CmacTripleDes.X86_64.kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - VG.Proof.CmacTripleDes.X86_64.stride p = VG.Proof.CmacTripleDes.X86_64.stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : VG.X86_64.State}
    (h : VG.Proof.CmacTripleDes.X86_64.OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' =>
      s'.zf = some (decide (p + 1 = 3)) ∧ VG.Proof.CmacTripleDes.X86_64.OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.pass_ok hp hp3 h.same h.r14 h.rbx h.r10 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t14, tbx, t12, t13, t10, tzf, tk, tm, trd, twr⟩ := VG.Proof.CmacTripleDes.X86_64.passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tzf, h₁.r10, VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega), VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r15 (by decide), h₁.same.r15]
  · rw [tk .rbp (by decide), h₁.same.rbp]
  · rw [tk .rsp (by decide), h₁.same.rsp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t14, h₁.r14, h₁.rbx, VG.Proof.CmacTripleDes.X86_64.kpos_tail_addr _ hp3]
  · rw [tbx, h₁.rbx, VG.Proof.CmacTripleDes.X86_64.stride_succ hp3]
  · rw [t10, h₁.r10, VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [t12, t13, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) {x : BitVec 64} {s : VG.X86_64.State} (h : VG.Proof.CmacTripleDes.X86_64.OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (VG.Proof.CmacTripleDes.X86_64.OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86_64.OInv s₀ x 3)
    (fun (n : Nat) (t : VG.X86_64.State) => ∃ p, n = 3 - p ∧ p < 3 ∧ VG.Proof.CmacTripleDes.X86_64.OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86_64.passBody_ok hp hp3 ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- `IP`'s high half into `r12`, its low half into `r13`, from `rax` (input word 0). -/
def ipG12 (t : Nat) : List Nat := if t < 32 then [ipSrc (32 + t)] else []
def ipG13 (t : Nat) : List Nat := if t < 32 then [ipSrc t] else []

theorem ip_check :
    VG.X86_64.Straight.check (lanes 64 6) VG.Proof.CmacTripleDes.X86_64.oCfg (linExt 1) ipCode (linEnv [(.rax, 0)])
      (linPost 6 [(.r12, VG.Proof.CmacTripleDes.X86_64.ipG12), (.r13, VG.Proof.CmacTripleDes.X86_64.ipG13)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `rax`, from `R` in `r12` (input word 0) and `L` in `r13` (input word 1). -/
def fpG (j : Nat) : List Nat := if 32 ≤ fpSrc j then [fpSrc j - 32] else [64 + fpSrc j]

theorem fp_check :
    VG.X86_64.Straight.check (lanes 64 7) VG.Proof.CmacTripleDes.X86_64.oCfg (linExt 2) fpCode (linEnv [(.r12, 0), (.r13, 1)]) (linPost 7 [(.rax, VG.Proof.CmacTripleDes.X86_64.fpG)]) = true := by
  lit_decide

def blockKept : List Reg := [.rbp, .rsp, .r14, .r15]

theorem ip_kept : blockKept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by lit_decide

theorem fp_kept : blockKept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

theorem frame_oCfg {s : VG.X86_64.State} {m m' : Mem} (h : Frame [slotRegion VG.Proof.CmacTripleDes.X86_64.oCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, VG.Proof.CmacTripleDes.X86_64.oCfg, Region.Contains]

theorem ip_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      ((s'.gpr .r12).setWidth 32, (s'.gpr .r13).setWidth 32) =
        split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86_64.blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.X86_64.ip_check (VG.Proof.CmacTripleDes.X86_64.oCfg_ok s) (fun _ => s.gpr .rax)
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.ip_kept r hr), VG.Proof.CmacTripleDes.X86_64.frame_oCfg hfr⟩
  have h12 := hout .r12 VG.Proof.CmacTripleDes.X86_64.ipG12 (by simp)
  have h13 := hout .r13 VG.Proof.CmacTripleDes.X86_64.ipG13 (by simp)
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · have hs := VG.Proof.CmacTripleDes.X86_64.ipSrc_lt (32 + t) (by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h12 t (by omega), VG.Proof.CmacTripleDes.X86_64.ipG12, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, BitVec.getLsbD_ushiftRight,
      Spec.TripleDes.permute, ← Spec.TripleDes.permute,
      getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl
  · have hs := VG.Proof.CmacTripleDes.X86_64.ipSrc_lt t (by omega)
    rw [BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and, h13 t (by omega), VG.Proof.CmacTripleDes.X86_64.ipG13, ite_eq_left ht,
      BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, Nat.mod_eq_of_lt hs]
    rfl

theorem fp_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.permute Spec.TripleDes.fp ((s.gpr .r12).setWidth 32 ++ (s.gpr .r13).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.CmacTripleDes.X86_64.blockKept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  let W : Nat → BitVec 64 := fun i => if i = 0 then s.gpr .r12 else s.gpr .r13
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.X86_64.fp_check (VG.Proof.CmacTripleDes.X86_64.oCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86_64.oCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, fun r hr => hoth r (List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.fp_kept r hr), VG.Proof.CmacTripleDes.X86_64.frame_oCfg hfr⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hs := VG.Proof.CmacTripleDes.X86_64.fpSrc_lt j hj
  rw [hout .rax VG.Proof.CmacTripleDes.X86_64.fpG (by simp) j hj, getLsbD_permute _ _ (by decide) hj, BitVec.getLsbD_append,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl, VG.Proof.CmacTripleDes.X86_64.fpG]
  by_cases h32 : 32 ≤ fpSrc j
  · rw [ite_eq_left h32, ite_eq_right (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      Nat.div_eq_of_lt (show fpSrc j - 32 < 64 by omega), Nat.mod_eq_of_lt (show fpSrc j - 32 < 64 by omega),
      BitVec.getLsbD_setWidth, show fpSrc j - 32 < 32 by omega, decide_true, Bool.true_and]
    rfl
  · rw [ite_eq_right h32, ite_eq_left (by omega)]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf,
      show (64 + fpSrc j) / 64 = 1 by omega, show (64 + fpSrc j) % 64 = fpSrc j by omega,
      BitVec.getLsbD_setWidth, show fpSrc j < 32 by omega, decide_true, Bool.true_and]
    rfl

theorem sub504_ok (s : VG.X86_64.State) :
    ∃ s', runBlock isa [.alu .sub .r14 (.imm 504)] s = some s' ∧
      s'.gpr .r14 = s.gpr .r14 - BitVec.ofNat 64 504 ∧ (∀ r, r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_self]; rfl
  · simp [gpr_setReg, hr]

/-- TDEA encryption of the block in `rax` (as a 64-bit integer) with the key
schedule at `r14`, into `rax`. -/
theorem block_ok {s₀ : VG.X86_64.State} (hp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₀) :
    WP isa VG.Impl.CmacTripleDes.X86_64.block s₀ fun s =>
      VG.Proof.CmacTripleDes.X86_64.Same s₀ s ∧ s.gpr .r14 = s₀.gpr .r14 ∧ s.gpr .rax = VG.Proof.CmacTripleDes.tdes (VG.Proof.CmacTripleDes.X86_64.sch s₀) (s₀.gpr .rax) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, k₁, m₁⟩ := VG.Proof.CmacTripleDes.X86_64.ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some]; rfl, ?_⟩⟩
  have g : ∀ r, r ≠ .r10 → r ≠ .rbx →
      ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)).gpr r = s₁.gpr r := fun r h1 h2 => by
    simp [State.setReg32, gpr_setReg, h1, h2]
  have hO : VG.Proof.CmacTripleDes.X86_64.OInv s₀ (s₀.gpr .rax) 0 ((s₁.setReg32 .r10 (3 : BitVec 32)).setReg32 .rbx (8 : BitVec 32)) :=
    ⟨⟨by rw [g _ (by decide) (by decide), k₁ _ (by decide)], by rw [g _ (by decide) (by decide), k₁ _ (by decide)],
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)], rd₁, wr₁,
      by show Frame [VG.Proof.CmacTripleDes.X86_64.xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), k₁ _ (by decide)]; simp [VG.Proof.CmacTripleDes.X86_64.kpos],
      by simp [State.setReg32, gpr_setReg, VG.Proof.CmacTripleDes.X86_64.stride],
      by simp [State.setReg32, gpr_setReg],
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  obtain ⟨s₄, h₄, r14₄, g4, m₄, rd₄, wr₄⟩ := VG.Proof.CmacTripleDes.X86_64.sub504_ok s₃
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, k₅, m₅⟩ := VG.Proof.CmacTripleDes.X86_64.fp_ok s₄
  refine WP.of_runBlock ⟨s₄, h₄, WP.of_runBlock ⟨s₅, h₅, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.r15]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rbp]
  · rw [k₅ _ (by decide), g4 _ (by decide), h₃.same.rsp]
  · rw [rd₅, rd₄, h₃.same.rd]
  · rw [wr₅, wr₄, h₃.same.wr]
  · rw [m₅, m₄]; exact h₃.same.frame
  · rw [k₅ _ (by decide), r14₄, h₃.r14, show 8 * VG.Proof.CmacTripleDes.X86_64.kpos 3 0 = 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, g4 _ (by decide), g4 _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit`. -/
section

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.X86_64.roundKeys

theorem Proof.CmacTripleDes.X86_64.roundKeys_eq :
    Impl.CmacTripleDes.X86_64.roundKeys = Impl.CmacTripleDes.X86_64.roundKeys.lit :=
  Impl.CmacTripleDes.X86_64.roundKeys.lit_eq

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit`. -/
section

/-! # TDEA-CMAC's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.X86_64.init
materialize_code Impl.CmacTripleDes.X86_64.update
materialize_code Impl.CmacTripleDes.X86_64.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract`. -/
section

/-!
# TDEA-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, which imply these (`Verified.lean`). The
functions call nothing and use no stack.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = rdi, key_len = rsi, out = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let out : Region := ⟨s.gpr .rdx, 400⟩
    let scr : Region := ⟨s.gpr .rcx, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint out ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 400 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) = k ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_update(schedule = rdi, state = rsi, data = rdx, n = rcx, scratch = r8)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 384⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86_64.ciphAt s.mem (s.gpr .rdi)) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rdx) 8 (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_finalize(key = rdi, state = rsi, last = rdx, last_len = rcx, scratch = r8)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 400⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let last : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 400 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 640 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat ≤ 8
  post s s' :=
    let ciph := VG.Proof.CmacTripleDes.X86_64.ciphAt s.mem (s.gpr .rdi)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (s.gpr .rdi + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .rcx).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.CT`. -/
section

/-!
# TDEA-CMAC on x86-64: constant time

The taint analysis (`Framework/X86_64/Taint.lean`) checks that only the
arguments, which are public, decide branches and addresses. `update` keeps the
data pointer and the blocks left in public slots of the scratch buffer, across
the blocks' stores of secrets at other offsets.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- `init`: the arguments are public; `rdx` and `rcx` point at the output and
the scratch buffer. -/
def τInit : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [400, 640],
    bases := [(.rdx, 0, 0), (.rcx, 1, 0)] }

/-- `update`: the arguments are public; `rsi` and `r8` point at the state and
the scratch buffer. -/
def τUpdate : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [8, 640],
    bases := [(.rsi, 0, 0), (.r8, 1, 0)] }

/-- `finalize`: the arguments are public; `rsi` and `r8` point at the state
and the scratch buffer. -/
def τFinalize : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [8, 640],
    bases := [(.rsi, 0, 0), (.r8, 1, 0)] }

theorem init_agree {s₁ s₂ : State} (h₁ : initX86_64.pre s₁) (h₂ : initX86_64.pre s₂)
    (hpub : initX86_64.pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.CmacTripleDes.X86_64.τInit s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, initX86_64.pre s → X86_64.Taint.Wf VG.Proof.CmacTripleDes.X86_64.τInit s := by
    intro s hs
    obtain ⟨-, hw, -, -, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.CmacTripleDes.X86_64.τInit], by simp [hw, d3], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.CmacTripleDes.X86_64.τInit, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [VG.Proof.CmacTripleDes.X86_64.τInit, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p3, p4]
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τInit] at h
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τInit] at h

theorem update_agree {s₁ s₂ : State} (h₁ : updateX86_64.pre s₁) (h₂ : updateX86_64.pre s₂)
    (hpub : updateX86_64.pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.CmacTripleDes.X86_64.τUpdate s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, updateX86_64.pre s → X86_64.Taint.Wf VG.Proof.CmacTripleDes.X86_64.τUpdate s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d5, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.CmacTripleDes.X86_64.τUpdate], by simp [hw, d5], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.CmacTripleDes.X86_64.τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [VG.Proof.CmacTripleDes.X86_64.τUpdate, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p2, p5]
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τUpdate] at h
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τUpdate] at h

theorem finalize_agree {s₁ s₂ : State} (h₁ : finalizeX86_64.pre s₁) (h₂ : finalizeX86_64.pre s₂)
    (hpub : finalizeX86_64.pub s₁ s₂) : X86_64.Taint.Agree VG.Proof.CmacTripleDes.X86_64.τFinalize s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, finalizeX86_64.pre s → X86_64.Taint.Wf VG.Proof.CmacTripleDes.X86_64.τFinalize s := by
    intro s hs
    obtain ⟨-, hw, -, -, -, -, d5, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.CmacTripleDes.X86_64.τFinalize], by simp [hw, d5], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.CmacTripleDes.X86_64.τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [VG.Proof.CmacTripleDes.X86_64.τFinalize, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p2, p5]
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τFinalize] at h
  · intro sl h; simp [VG.Proof.CmacTripleDes.X86_64.τFinalize] at h

theorem update_ct : ConstantTime isa updateX86_64.pre updateX86_64.pub Impl.CmacTripleDes.X86_64.update :=
  VG.Taint.constantTime (A := VG.X86_64.taint) VG.Proof.CmacTripleDes.X86_64.τUpdate (fun _ _ h₁ h₂ hp => VG.Proof.CmacTripleDes.X86_64.update_agree h₁ h₂ hp) (by taint_decide)

theorem init_ct : ConstantTime isa initX86_64.pre initX86_64.pub Impl.CmacTripleDes.X86_64.init :=
  VG.Taint.constantTime (A := VG.X86_64.taint) VG.Proof.CmacTripleDes.X86_64.τInit (fun _ _ h₁ h₂ hp => VG.Proof.CmacTripleDes.X86_64.init_agree h₁ h₂ hp) (by taint_decide)

theorem finalize_ct :
    ConstantTime isa finalizeX86_64.pre finalizeX86_64.pub Impl.CmacTripleDes.X86_64.finalize :=
  VG.Taint.constantTime (A := VG.X86_64.taint) VG.Proof.CmacTripleDes.X86_64.τFinalize (fun _ _ h₁ h₂ hp => VG.Proof.CmacTripleDes.X86_64.finalize_agree h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Save`. -/
section

/-!
# TDEA-CMAC on x86-64: saving and restoring the registers

Each function saves our caller's callee-saved registers to bytes `[48, 96)` of
the scratch buffer (`save`), and restores them from there, through `r15`
(`restore`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-- The memory after saving the registers to the scratch buffer at `S`. -/
abbrev savedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

theorem saved_bound : ∀ p ∈ saved, 48 ≤ p.2 ∧ p.2 + 8 ≤ 96 := by decide

theorem save_ok (s : State) (sc : Reg)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions s.wr (s.gpr sc + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save sc) s = some s' ∧ s'.gpr = s.gpr ∧ s'.mem = VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr sc) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, Spill.save_run sc saved s fun p hp => hw p.2 (VG.Proof.CmacTripleDes.X86_64.saved_bound p hp).1 (VG.Proof.CmacTripleDes.X86_64.saved_bound p hp).2, rfl, rfl,
    rfl, rfl⟩

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- The saved registers, read back. -/
theorem savedMem_read (s : State) (S : Addr) :
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 48) 64 = s.gpr .rbx ∧
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 56) 64 = s.gpr .rbp ∧
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 64) 64 = s.gpr .r12 ∧
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 72) 64 = s.gpr .r13 ∧
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 80) 64 = s.gpr .r14 ∧
    (VG.Proof.CmacTripleDes.X86_64.savedMem s S).readW (S + BitVec.ofNat 64 88) 64 = s.gpr .r15 :=
  have h := Spill.saveMem_saved s.mem S s.gpr saved (by decide)
  ⟨h (.rbx, 48) (by decide), h (.rbp, 56) (by decide), h (.r12, 64) (by decide), h (.r13, 72) (by decide),
    h (.r14, 80) (by decide), h (.r15, 88) (by decide)⟩

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 96) :
    (⟨b + BitVec.ofNat 64 48, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 48) + BitVec.ofNat 64 (d - 48) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) (S : Addr) : Frame [⟨S + BitVec.ofNat 64 48, 48⟩] s.mem (VG.Proof.CmacTripleDes.X86_64.savedMem s S) :=
  Spill.saveMem_frame _ _ _ _ fun p hp => VG.Proof.CmacTripleDes.X86_64.slot_contains _ (VG.Proof.CmacTripleDes.X86_64.saved_bound p hp).1 (VG.Proof.CmacTripleDes.X86_64.saved_bound p hp).2

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 88) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.map_some, hb,
      hr 48 (by decide) (by decide), hr 56 (by decide) (by decide), hr 64 (by decide) (by decide),
      hr 72 (by decide) (by decide), hr 80 (by decide) (by decide), hr 88 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, mem_setReg]

/-- The registers restored from slots that have not changed since they
were saved, the stack pointer kept: `gprPreserved`. -/
theorem restored {s₀ s s' : State} {S : Addr} (hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s.mem.readW (S + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64)
    (h : s'.gpr .rbx = s.mem.readW (S + BitVec.ofNat 64 48) 64 ∧
      s'.gpr .rbp = s.mem.readW (S + BitVec.ofNat 64 56) 64 ∧
      s'.gpr .r12 = s.mem.readW (S + BitVec.ofNat 64 64) 64 ∧
      s'.gpr .r13 = s.mem.readW (S + BitVec.ofNat 64 72) 64 ∧
      s'.gpr .r14 = s.mem.readW (S + BitVec.ofNat 64 80) 64 ∧
      s'.gpr .r15 = s.mem.readW (S + BitVec.ofNat 64 88) 64)
    (hsp : s'.gpr .rsp = s₀.gpr .rsp) : ∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r := by
  obtain ⟨a, b, c, d, e, f⟩ := VG.Proof.CmacTripleDes.X86_64.savedMem_read s₀ S
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha, hm 48 (by decide) (by decide), a]
  · rw [hb, hm 56 (by decide) (by decide), b]
  · exact hsp
  · rw [hc, hm 64 (by decide) (by decide), c]
  · rw [hd, hm 72 (by decide) (by decide), d]
  · rw [he, hm 80 (by decide) (by decide), e]
  · rw [hf, hm 88 (by decide) (by decide), f]

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update`. -/
section

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_update`

The invariant after `k` blocks (`LInv`): slot 12 points to the next block,
slot 13 holds the blocks left, only the state, the block's slots and slots
12–13 have changed since the registers were saved, and the state is the
chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

theorem bswap64_eq (x : BitVec 64) : bswap64 x = byteRev64 x := rfl

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .rdi
abbrev St : Addr := s₀.gpr .rsi
abbrev Dp : Addr := s₀.gpr .rdx
abbrev N : Nat := (s₀.gpr .rcx).toNat
abbrev S : Addr := s₀.gpr .r8

abbrev schR : Region := ⟨VG.Proof.CmacTripleDes.X86_64.W s₀, 384⟩
abbrev stR : Region := ⟨VG.Proof.CmacTripleDes.X86_64.St s₀, 8⟩
abbrev dataR : Region := ⟨VG.Proof.CmacTripleDes.X86_64.Dp s₀, 8 * VG.Proof.CmacTripleDes.X86_64.N s₀⟩
abbrev scrR : Region := ⟨VG.Proof.CmacTripleDes.X86_64.S s₀, 640⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacTripleDes.X86_64.ciphAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.W s₀)

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.Dp s₀) 8 (VG.Proof.CmacTripleDes.X86_64.N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region := [VG.Proof.CmacTripleDes.X86_64.stR s₀, ⟨VG.Proof.CmacTripleDes.X86_64.S s₀, 48⟩, ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.X86_64.schR s₀, VG.Proof.CmacTripleDes.X86_64.dataR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀]
  sch_st : (VG.Proof.CmacTripleDes.X86_64.schR s₀).Disjoint (VG.Proof.CmacTripleDes.X86_64.stR s₀)
  sch_scr : (VG.Proof.CmacTripleDes.X86_64.schR s₀).Disjoint (VG.Proof.CmacTripleDes.X86_64.scrR s₀)
  data_st : (VG.Proof.CmacTripleDes.X86_64.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.X86_64.stR s₀)
  data_scr : (VG.Proof.CmacTripleDes.X86_64.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.X86_64.scrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.X86_64.stR s₀).Disjoint (VG.Proof.CmacTripleDes.X86_64.scrR s₀)
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (VG.Proof.CmacTripleDes.X86_64.stR s₀)
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint (VG.Proof.CmacTripleDes.X86_64.scrR s₀)
  st_wrap : (VG.Proof.CmacTripleDes.X86_64.St s₀).toNat + 8 ≤ 2 ^ 64
  data_wrap : (VG.Proof.CmacTripleDes.X86_64.Dp s₀).toNat + 8 * VG.Proof.CmacTripleDes.X86_64.N s₀ ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacTripleDes.X86_64.S s₀).toNat + 640 ≤ 2 ^ 64

theorem UPre.of {s₀ : State} (h : updateX86_64.pre s₀) : VG.Proof.CmacTripleDes.X86_64.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = VG.Proof.CmacTripleDes.X86_64.W s₀
  r15 : s.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.S s₀
  rbp : s.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.St s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) 64 = VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k)
  left : s.mem.readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86_64.N s₀ - k)
  frame : Frame (VG.Proof.CmacTripleDes.X86_64.chg s₀) (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem (VG.Proof.CmacTripleDes.X86_64.St s₀) 8 =
    Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86_64.ciph s₀) (Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.St s₀) 8) ((VG.Proof.CmacTripleDes.X86_64.blks s₀).take k)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-! ## The blocks of straight-line code -/

theorem prologue_ok (s : State)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa updPre s = some s' ∧
      s'.gpr .r15 = s.gpr .r8 ∧ s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rcx == 0) ∧
      s'.mem = ((VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .r8)).writeW (s.gpr .r8 + BitVec.ofNat 64 96) (s.gpr .rdx)).writeW
        (s.gpr .r8 + BitVec.ofNat 64 104) (s.gpr .rcx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.save_ok s .r8 fun d h₁ h₂ => hw d h₁ (by omega)
  have hw' : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s₁.wr (s₁.gpr .r8 + BitVec.ofNat 64 d) 8 := by
    rw [g₁, wr₁]; exact hw
  refine ⟨_, by
    rw [updPre, VG.Proof.CmacTripleDes.X86_64.runBlock_append, h₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.store64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, execAlu, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg,
      hw' 96 (by decide) (by decide), hw' 104 (by decide) (by decide)]
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, and_self, gpr_setReg, gpr_arithFlags, zf_arithFlags,
    mem_arithFlags, rd_arithFlags, wr_arithFlags,
    BitVec.and_self, g₁, m₁, rd₁, wr₁]

theorem chainIn_ok (s : State) {P Q : Addr} (hp : s.gpr .rbp = P)
    (hq : s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 = Q)
    (r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa chainIn s = some s' ∧
      s'.gpr .rax = byteRev64 (s.mem.readW P 64 ^^^ s.mem.readW Q 64) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, chainIn, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      hp, hq, BitVec.add_zero, r96, rp, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, VG.Proof.CmacTripleDes.X86_64.bswap64_eq]
  · simp [gpr_setReg, h₁, h₂]

theorem chainOut_ok (s : State) {P : Addr} (hp : s.gpr .rbp = P)
    (wp : InRegions s.wr P 8) (w96 : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 96) 8)
    (w104 : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 104) 8)
    (sep96 : Mem.Sep (s.gpr .r15 + BitVec.ofNat 64 96) 8 P 8)
    (sep104 : Mem.Sep (s.gpr .r15 + BitVec.ofNat 64 104) 8 P 8) :
    ∃ s', runBlock isa chainOut s = some s' ∧
      s'.zf = some ((s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rax, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = (((s.mem.writeW P (byteRev64 (s.gpr .rax))).writeW (s.gpr .r15 + BitVec.ofNat 64 96)
        (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 + BitVec.ofNat 64 8)).writeW
        (s.gpr .r15 + BitVec.ofNat 64 104) (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 - 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8 := by
    obtain ⟨r, hr, hc⟩ := w96; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have r104 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 104) 8 := by
    obtain ⟨r, hr, hc⟩ := w104; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have h96 : (s.mem.writeW P (byteRev64 (s.gpr .rax))).readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 =
      s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 := Mem.readW_writeW_sep sep96 (by decide)
  have h104 : ((s.mem.writeW P (byteRev64 (s.gpr .rax))).writeW (s.gpr .r15 + BitVec.ofNat 64 96)
      (s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 96) 64 + BitVec.ofNat 64 8)).readW
        (s.gpr .r15 + BitVec.ofNat 64 104) 64 = s.mem.readW (s.gpr .r15 + BitVec.ofNat 64 104) 64 := by
    rw [VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_sep sep104 (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [chainOut, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, State.load64, State.store64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, ite_true, ite_false, hp, BitVec.add_zero, r96, r104, wp, w96, w104, h96, h104, VG.Proof.CmacTripleDes.X86_64.bswap64_eq,
      show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp []
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2]

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d, n⟩ (VG.Proof.CmacTripleDes.X86_64.scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86_64.N s₀) :
    Region.Sub ⟨VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k), 8⟩ (VG.Proof.CmacTripleDes.X86_64.dataR s₀) :=
  Offset.sub_base _ (by omega)

/-- Everything that changes, from the entry state on. -/
theorem UPre.big {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86_64.chg s₀) (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) m) :
    Frame [VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀] s₀.mem m :=
  ((VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacTripleDes.X86_64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩).trans
  (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.CmacTripleDes.X86_64.stR s₀, by simp, fun _ h => h⟩
    · exact ⟨VG.Proof.CmacTripleDes.X86_64.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.CmacTripleDes.X86_64.scrR s₀, by simp, UPre.scr_sub (by decide)⟩)

theorem UPre.sched {hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀} {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86_64.chg s₀) (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) m) :
    Spec.TripleDes.scheduleAt m (VG.Proof.CmacTripleDes.X86_64.W s₀) = Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.W s₀) :=
  VG.Proof.CmacTripleDes.X86_64.scheduleAt_frame (UPre.big hf) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr

theorem UPre.data {hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀} {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.X86_64.chg s₀) (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) m) {k : Nat}
    (hk : k < VG.Proof.CmacTripleDes.X86_64.N s₀) :
    Spec.Aes.bytesAt m (VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  bytesAt_frame (UPre.big hf) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.data_st.sub_left (UPre.data_sub hk)
    · exact hp.data_scr.sub_left (UPre.data_sub hk)) (by decide)

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀} {s : State} (h14 : s.gpr .r14 = VG.Proof.CmacTripleDes.X86_64.W s₀) (h15 : s.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : VG.Proof.CmacTripleDes.X86_64.BlockPre s where
  sched := ⟨VG.Proof.CmacTripleDes.X86_64.schR s₀, by rw [hrd, hp.rd]; simp, by rw [h14], Nat.le_refl _, by show 384 < 2 ^ 64; decide⟩
  scr := ⟨VG.Proof.CmacTripleDes.X86_64.scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
  disj := by
    rw [h14, h15]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem rbp_succ (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86_64.N s₀) :
    (VG.Proof.CmacTripleDes.X86_64.blks s₀).take (k + 1) =
      (VG.Proof.CmacTripleDes.X86_64.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86_64.N s₀) {s : State} (h : VG.Proof.CmacTripleDes.X86_64.LInv s₀ k s) :
    WP isa updBody s fun s' => VG.Proof.CmacTripleDes.X86_64.LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (VG.Proof.CmacTripleDes.X86_64.N s₀ - (k + 1) = 0)) := by
  have hN : VG.Proof.CmacTripleDes.X86_64.N s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hsw := hp.scr_wrap
  have hdw := hp.data_wrap
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacTripleDes.X86_64.schR s₀, VG.Proof.CmacTripleDes.X86_64.dataR s₀, VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have r96 : InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 96) 8 := by
    rw [rdwr, h.r15]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  obtain ⟨s₁, h₁, ax₁, k₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.chainIn_ok s (P := VG.Proof.CmacTripleDes.X86_64.St s₀)
    (Q := VG.Proof.CmacTripleDes.X86_64.Dp s₀ + BitVec.ofNat 64 (8 * k)) h.rbp (by rw [h.r15, h.dp]) r96
    (by rw [rdwr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [rdwr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  refine WP.seq (WP.of_runBlock ⟨s₁, h₁, ?_⟩)
  have r14₁ : s₁.gpr .r14 = VG.Proof.CmacTripleDes.X86_64.W s₀ := by rw [k₁ _ (by decide) (by decide), h.r14]
  have r15₁ : s₁.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.S s₀ := by rw [k₁ _ (by decide) (by decide), h.r15]
  have bp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₁ := UPre.block (hp := hp) r14₁ r15₁ (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.block_ok bp) fun s₂ ⟨same₂, r14₂, ax₂⟩ => ?_)
  have xR₁ : VG.Proof.CmacTripleDes.X86_64.xR s₁ = ⟨VG.Proof.CmacTripleDes.X86_64.S s₀, 48⟩ := by rw [VG.Proof.CmacTripleDes.X86_64.xR, r15₁]
  have f₂ : Frame [⟨VG.Proof.CmacTripleDes.X86_64.S s₀, 48⟩] s.mem s₂.mem := by rw [← m₁, ← xR₁]; exact same₂.frame
  have r15₂ : s₂.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.S s₀ := by rw [same₂.r15, r15₁]
  have slot₂ : ∀ d, 48 ≤ d → d + 8 ≤ 640 →
      s₂.mem.readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => f₂.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₂ : s₂.rd ++ s₂.wr = [VG.Proof.CmacTripleDes.X86_64.schR s₀, VG.Proof.CmacTripleDes.X86_64.dataR s₀, VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀] := by
    rw [same₂.rd, same₂.wr, rd₁, wr₁, rdwr]
  have wr₂ : s₂.wr = [VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  have sep : Mem.Sep (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104) 8 (VG.Proof.CmacTripleDes.X86_64.St s₀) 8 :=
    (hp.st_scr.symm.sub_left (UPre.scr_sub (d := 104) (n := 8) (by decide))).sep (Region.contains_self _ _)
      (Region.contains_self _ _)
  have sep96 : Mem.Sep (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) 8 (VG.Proof.CmacTripleDes.X86_64.St s₀) 8 :=
    (hp.st_scr.symm.sub_left (UPre.scr_sub (d := 96) (n := 8) (by decide))).sep (Region.contains_self _ _)
      (Region.contains_self _ _)
  have rbp₂ : s₂.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.St s₀ := by rw [same₂.rbp, k₁ _ (by decide) (by decide), h.rbp]
  obtain ⟨s₃, h₃, zf₃, k₃, m₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.X86_64.chainOut_ok s₂ (P := VG.Proof.CmacTripleDes.X86_64.St s₀) rbp₂
    (by rw [wr₂]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.stR s₀) (by simp) (Region.contains_self _ _))
    (by rw [wr₂, r15₂]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (by rw [wr₂, r15₂]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    (by rw [r15₂]; exact sep96) (by rw [r15₂]; exact sep)
  rw [r15₂] at m₃ zf₃
  rw [slot₂ 96 (by decide) (by decide), slot₂ 104 (by decide) (by decide), h.dp, h.left] at m₃
  rw [slot₂ 104 (by decide) (by decide), h.left] at zf₃
  have dec : BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86_64.N s₀ - k) - 1 = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86_64.N s₀ - (k + 1)) :=
    VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega)
  rw [dec] at m₃ zf₃
  -- The state's new value.
  have big : Frame [VG.Proof.CmacTripleDes.X86_64.stR s₀, VG.Proof.CmacTripleDes.X86_64.scrR s₀] s₀.mem s.mem := UPre.big h.frame
  have hS : VG.Proof.CmacTripleDes.X86_64.sch s₁ = Spec.TripleDes.scheduleAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.W s₀) := by
    rw [VG.Proof.CmacTripleDes.X86_64.sch, r14₁, m₁]; exact UPre.sched (hp := hp) h.frame
  have hD := UPre.data (hp := hp) h.frame hk
  refine WP.of_runBlock ⟨s₃, h₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k₃ _ (by decide), r14₂, r14₁]
  · rw [k₃ _ (by decide), r15₂]
  · rw [k₃ _ (by decide), rbp₂]
  · rw [k₃ _ (by decide), same₂.rsp, k₁ _ (by decide) (by decide), h.rsp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · rw [m₃, VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, VG.Proof.CmacTripleDes.X86_64.rbp_succ]
  · rw [m₃, Mem.readW_writeW_self64]
  · have c96 : (⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (64 / 8) := by
      have := Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    have c104 : (⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104) (64 / 8) := by
      rw [show VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104 = VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₃]
    exact (((h.frame.trans (f₂.mono fun r hr => by simp at hr; simp [hr])).writeW (r := VG.Proof.CmacTripleDes.X86_64.stR s₀) (by simp) _
      (by simpa using Region.contains_self (VG.Proof.CmacTripleDes.X86_64.St s₀) 8)).writeW (r := ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩)
        (by simp) _ c96).writeW (r := ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩) (by simp) _ c104
  · have c96 : (⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (64 / 8) := by
      have := Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    have c104 : (⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104) (64 / 8) := by
      rw [show VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104 = VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
    rw [m₃, bytesAt_frame (rs := [⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩])
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _ c104)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (d := 96) (n := 16) (by decide))) (by decide),
      ← le8_readW, Mem.readW_writeW_self64, ax₂, ax₁, ← tdesWith_le8, hS, le8_xor, le8_readW, le8_readW,
      h.state, hD, VG.Proof.CmacTripleDes.X86_64.take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [zf₃, VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero (by omega)]

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.X86_64.N s₀) {s : State}
    (h : VG.Proof.CmacTripleDes.X86_64.LInv s₀ k s) : WP isa (.loop updBody .ne) s (VG.Proof.CmacTripleDes.X86_64.LInv s₀ (VG.Proof.CmacTripleDes.X86_64.N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86_64.LInv s₀ (VG.Proof.CmacTripleDes.X86_64.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacTripleDes.X86_64.N s₀ - j ∧ j < VG.Proof.CmacTripleDes.X86_64.N s₀ ∧ VG.Proof.CmacTripleDes.X86_64.LInv s₀ j t) ?_ (VG.Proof.CmacTripleDes.X86_64.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86_64.body_ok hp hk h) fun s' ⟨h', zf'⟩ => ?_
  by_cases hz : VG.Proof.CmacTripleDes.X86_64.N s₀ - (k + 1) = 0
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [show VG.Proof.CmacTripleDes.X86_64.N s₀ = k + 1 by omega]
  · right
    refine ⟨by simp [X86_64.eval, zf', hz], VG.Proof.CmacTripleDes.X86_64.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem rcx_ofNat (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86_64.N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [VG.Proof.CmacTripleDes.X86_64.N]

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) :
    WP isa (.block updPre) s₀ fun s₁ => VG.Proof.CmacTripleDes.X86_64.LInv s₀ 0 s₁ ∧ s₁.zf = some (decide (VG.Proof.CmacTripleDes.X86_64.N s₀ = 0)) := by
  have hN : VG.Proof.CmacTripleDes.X86_64.N s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hsw := hp.scr_wrap
  obtain ⟨s₁, run₁, r15₁, r14₁, rbp₁, rsp₁, zf₁, mem₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacTripleDes.X86_64.prologue_ok s₀ fun d _ h₂ => by
      rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  have f96 : Frame [⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) s₁.mem := by
    have c0 : (⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) 8 := by
      have := Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      simpa using this
    rw [mem₁]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ ?_
    rw [show VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 104 = VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 96) (d := 8) (n := 8) (k := 16) (by decide) (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ⟨r14₁, r15₁, rbp₁, rsp₁, rd₁, wr₁, ?_, ?_,
    f96.mono fun r hr => by simp at hr; simp [hr], ?_⟩, ?_⟩
  · rw [mem₁, VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]; simp
  · rw [mem₁, Mem.readW_writeW_self64, VG.Proof.CmacTripleDes.X86_64.rcx_ofNat]; rfl
  · rw [bytesAt_frame (f96 : Frame _ (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) s₁.mem) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))) (by decide),
      bytesAt_frame (VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (UPre.scr_sub (by decide))) (by decide)]
    rfl
  · rw [zf₁, VG.Proof.CmacTripleDes.X86_64.rcx_ofNat, VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero hN]

theorem mid_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) {s₁ : State} (h : VG.Proof.CmacTripleDes.X86_64.LInv s₀ 0 s₁)
    (hz : s₁.zf = some (decide (VG.Proof.CmacTripleDes.X86_64.N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop updBody .ne)) s₁ (VG.Proof.CmacTripleDes.X86_64.LInv s₀ (VG.Proof.CmacTripleDes.X86_64.N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (VG.Proof.CmacTripleDes.X86_64.N s₀ = 0)) := hz
  by_cases hn : VG.Proof.CmacTripleDes.X86_64.N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacTripleDes.X86_64.loop_ok hp (by omega) h

theorem slot_read {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) {m : Mem}
    (hf : Frame (VG.Proof.CmacTripleDes.X86_64.chg s₀) (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)) m) (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 96) :
    m.readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.S s₀)).readW (VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d) 64 := by
  have hsw := hp.scr_wrap
  refine hf.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.S s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.st_scr.sub_right (UPre.scr_sub (by omega))).symm
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.UPre s₀) {s₂ : State} (h₂ : VG.Proof.CmacTripleDes.X86_64.LInv s₀ (VG.Proof.CmacTripleDes.X86_64.N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hsw := hp.scr_wrap
  have rdwr : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr]
  obtain ⟨s₃, run₃, b, c, d, e, f, g, rsp₃, mem₃⟩ := VG.Proof.CmacTripleDes.X86_64.restore_ok s₂ h₂.r15 fun d _ h₂' => by
    rw [rdwr, hp.rd, hp.wr]
    exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := VG.Proof.CmacTripleDes.X86_64.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₃, run₃, ⟨VG.Proof.CmacTripleDes.X86_64.restored (VG.Proof.CmacTripleDes.X86_64.slot_read hp h₂.frame) ⟨b, c, d, e, f, g⟩
    (by rw [rsp₃, h₂.rsp]), ?_⟩, ?_⟩
  · rw [mem₃]
    refine (UPre.big h₂.frame).readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_scr
  · show Spec.Aes.bytesAt s₃.mem (VG.Proof.CmacTripleDes.X86_64.St s₀) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.X86_64.ciph s₀) _ (VG.Proof.CmacTripleDes.X86_64.blks s₀)
    rw [mem₃, h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateX86_64.pre s₀) :
    WP isa update s₀ fun s' => gprPreserved s₀ s' ∧ updateX86_64.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.mid_wp hp h₁ z₁) fun _ h₂ => VG.Proof.CmacTripleDes.X86_64.epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Finalize`. -/
section

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in `rax`, as a
little-endian word: `Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a
byte at a time onto the zeroed slot 12, `0x80` after it, XORed with `K2`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them) and the scratch buffer `S`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L : Nat) : Prop where
  rdi : s₀.gpr .rdi = W
  rsi : s₀.gpr .rsi = St
  rdx : s₀.gpr .rdx = P
  rcx : (s₀.gpr .rcx).toNat = L
  r8 : s₀.gpr .r8 = S
  rd : s₀.rd = [⟨W, 400⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 8⟩, ⟨S, 640⟩]
  key_st : (⟨W, 400⟩ : Region).Disjoint ⟨St, 8⟩
  key_scr : (⟨W, 400⟩ : Region).Disjoint ⟨S, 640⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 640⟩
  st_scr : (⟨St, 8⟩ : Region).Disjoint ⟨S, 640⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 8⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 640⟩
  key_wrap : W.toNat + 400 ≤ 2 ^ 64
  st_wrap : St.toNat + 8 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 640 ≤ 2 ^ 64
  len : L ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeX86_64.pre s₀) :
    VG.Proof.CmacTripleDes.X86_64.FPre s₀ (s₀.gpr .rdi) (s₀.gpr .rsi) (s₀.gpr .rdx) (s₀.gpr .r8) (s₀.gpr .rcx).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- Slot 12, where a partial last block is formed. -/
abbrev slot12 (S : Addr) : Region := ⟨S + BitVec.ofNat 64 96, 8⟩

/-- What the branch on the length leaves: `Mₙ` in `rax`. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  r14 : s.gpr .r14 = W
  r15 : s.gpr .r15 = S
  rbp : s.gpr .rbp = St
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.X86_64.slot12 S] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S) s.mem
  blk : le8 (s.gpr .rax) = VG.Proof.CmacTripleDes.X86_64.mn s₀.mem W P L

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.X86_64.FPre s₀ W St P S L)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨S, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨W, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

end

theorem FPre.scrD {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem xor_comm (x y : List Byte) : Spec.Cmac.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-! ## Copying the last bytes -/

/-- The copy loop's body. -/
abbrev copyBody : List Instr :=
  [.movzx8 .rax lastByte, .store8 padByte .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hd : s.gpr .rdx = P)
    (h15 : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (hc : s.gpr .rcx = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa VG.Proof.CmacTripleDes.X86_64.copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .rdx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hd, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .r15 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (96 : Int) = C + BitVec.ofNat 64 i := by
    rw [hi, BitVec.mul_one, ← h15, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, VG.Proof.CmacTripleDes.X86_64.copyBody, lastByte, padByte, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
      ea₁, ea₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, hc]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Aes.bytesAt m p (i + 1) = Spec.Aes.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Aes.bytesAt, List.range_succ]

open VG.WriteBytes in
theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL₀ : 0 < L) (hL : L < 8) (hd : s.gpr .rdx = P)
    (h15 : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hc : s.gpr .rcx = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (.imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (0 : BitVec 32)) :=
    ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block VG.Proof.CmacTripleDes.X86_64.copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, r10₁, by simp [Spec.Aes.bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  have td : t.gpr .rdx = P := by rw [g _ (by decide) (by decide), hd]
  have t15 : t.gpr .r15 + BitVec.ofNat 64 96 = C := by rw [g _ (by decide) (by decide), h15]
  have tc : t.gpr .rcx = BitVec.ofNat 64 L := by rw [g _ (by decide) (by decide), hc]
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := VG.Proof.CmacTripleDes.X86_64.copyStep_ok t td t15 r10 tc
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, VG.Proof.CmacTripleDes.X86_64.bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i))
      (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', VG.Proof.CmacTripleDes.X86_64.succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    refine ⟨by simp [X86_64.eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [X86_64.eval, hz, he], L - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', VG.Proof.CmacTripleDes.X86_64.succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## The straight-line pieces -/

theorem pre1_ok (s : State) (hw : ∀ d, 48 ≤ d → d + 8 ≤ 96 → InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) 8)
    {L : Nat} (hc : s.gpr .rcx = BitVec.ofNat 64 L) (hL : L ≤ 8) :
    ∃ s', runBlock isa (save .r8 ++ ([.mov .r15 (.reg .r8), .mov .r14 (.reg .rdi), .mov .rbp (.reg .rsi),
        .alu .cmp .rcx (.imm 8)] : List Instr)) s = some s' ∧
      s'.gpr .r15 = s.gpr .r8 ∧ s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧
      (∀ r, r ∉ [Reg.r14, .r15, .rbp] → s'.gpr r = s.gpr r) ∧ s'.zf = some (decide (L = 8)) ∧
      s'.mem = VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .r8) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.save_ok s .r8 hw
  refine ⟨_, by
    rw [VG.Proof.CmacTripleDes.X86_64.runBlock_append, h₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, g₁]
  · simp [gpr_setReg, g₁]
  · simp [gpr_setReg, g₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, g₁, hr.1, hr.2.1, hr.2.2]
  · rw [zf_arithFlags]
    simp only [gpr_setReg, reduceCtorEq, ite_false, g₁]
    rw [hc, show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  · simp [mem_setReg, mem_arithFlags, m₁, g₁]
  · simp [rd_setReg, rd_arithFlags, rd₁]
  · simp [wr_setReg, wr_arithFlags, wr₁]

/-- Two words XORed from `[pb + pd]` and `[qb + qd]` into `rax`. -/
theorem xor1_ok (s : State) (pb qb : Reg) (pd qd : Nat) {P Q : Addr}
    (hp : s.gpr pb + BitVec.ofNat 64 pd = P) (hq : s.gpr qb + BitVec.ofNat 64 qd = Q) (hq' : qb ≠ .rax)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rq : InRegions (s.rd ++ s.wr) Q 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ pb pd)), .alu .xor .rax (.mem (at_ qb qd))] s = some s' ∧
      s'.gpr .rax = s.mem.readW P 64 ^^^ s.mem.readW Q 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, hq', hp, hq, rp, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]

theorem zero_ok (s : State) {C : Addr} {L : Nat} (hc : s.gpr .r15 + BitVec.ofNat 64 96 = C)
    (hL : s.gpr .rcx = BitVec.ofNat 64 L) (hL' : L < 2 ^ 64) (wc : InRegions s.wr C 8) :
    ∃ s', runBlock isa zero s = some s' ∧ s'.zf = some (decide (L = 0)) ∧
      s'.mem = s.mem.writeW C (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, zero, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.store64, State.ea, State.setReg32, VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hc, wc]
    rfl, ?_⟩
  refine ⟨?_, rfl, ?_, rfl, rfl⟩
  · rw [zf_arithFlags]
    simp only [hL, BitVec.and_self]
    rw [VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero hL']
  · intro r hr; simp [gpr_setReg, hr]

theorem pad_ok (s : State) {C K : Addr} {L : Nat}
    (hc : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 (96 : Int) = C + BitVec.ofNat 64 L)
    (hc' : s.gpr .r15 + BitVec.ofNat 64 96 = C) (hk : s.gpr .rdi + BitVec.ofNat 64 392 = K)
    (wc : InRegions s.wr (C + BitVec.ofNat 64 L) 1) (rc : InRegions (s.rd ++ s.wr) C 8)
    (rk : InRegions (s.rd ++ s.wr) K 8) :
    ∃ s', runBlock isa padK2 s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte) ∧
      s'.gpr .rax = (s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte)).readW C 64 ^^^
        (s.mem.writeW (C + BitVec.ofNat 64 L) (0x80 : Byte)).readW K 64 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [padK2, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, readSrc32, execAlu, State.load64, State.store8, State.ea, State.setReg32, VG.Proof.CmacTripleDes.X86_64.offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      hc, hc', hk, wc, rc, rk]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags]; rfl
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.FinalizeCorrect`. -/
section

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_finalize` is correct

After the branch on the length, `rax` holds `Mₙ` (`BPost`); the function XORs
in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the
state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- What the first block leaves. -/
structure P1 (s₀ : State) (W St P S : Addr) (s : State) : Prop where
  r15 : s.gpr .r15 = S
  r14 : s.gpr .r14 = W
  rbp : s.gpr .rbp = St
  rdi : s.gpr .rdi = W
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.X86_64.FPre s₀ W St P S L)
include hp

theorem FPre.save_frame : ∀ r ∈ [(⟨S + BitVec.ofNat 64 48, 48⟩ : Region)], (⟨P, L⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hp.last_scr.sub_right (FPre.scrD (by decide))

theorem FPre.keyD {d n : Nat} (h : d + n ≤ 400) {r : Region} (hr : Region.Sub r ⟨S, 640⟩) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right hr

theorem full_wp (hL : L = 8) {s : State} (h : VG.Proof.CmacTripleDes.X86_64.P1 s₀ W St P S s) :
    WP isa (.block full) s (VG.Proof.CmacTripleDes.X86_64.BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  obtain ⟨s', run, ax, g, m, rd, wr⟩ := VG.Proof.CmacTripleDes.X86_64.xor1_ok s .rdx .rdi 0 384 (P := P) (Q := W + BitVec.ofNat 64 384)
    (by rw [h.rdx]; simp) (by rw [h.rdi]) (by decide)
    (by rw [h.rd, h.wr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [h.rd, h.wr]; exact hp.inKey (d := 384) (n := 8) (by decide))
  refine WP.of_runBlock ⟨s', run, by rw [g _ (by decide), h.r14], by rw [g _ (by decide), h.r15],
    by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [m, h.mem]; exact Frame.refl _ _, ?_⟩
  have fs := VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ S
  rw [ax, h.mem, le8_xor, le8_readW, le8_readW,
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.last_scr.sub_right (FPre.scrD (by decide))) (by decide),
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.keyD (d := 384) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
  simp only [VG.Proof.CmacTripleDes.X86_64.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact VG.Proof.CmacTripleDes.X86_64.xor_comm _ _

open VG.WriteBytes in
theorem partial_wp (hL : L < 8) {s : State} (h : VG.Proof.CmacTripleDes.X86_64.P1 s₀ W St P S s) :
    WP isa partialBlock s (VG.Proof.CmacTripleDes.X86_64.BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hcx : s.gpr .rcx = BitVec.ofNat 64 L := by
    rw [h.rcx, ← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 96 = C := ⟨_, rfl⟩
  have hc : s.gpr .r15 + BitVec.ofNat 64 96 = C := by rw [h.r15, hC]
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  have sl : VG.Proof.CmacTripleDes.X86_64.slot12 S = ⟨C, 8⟩ := by rw [← hC]
  -- Zero the slot.
  obtain ⟨s₁, run₁, zf₁, mem₁, g₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.zero_ok s hc hcx (by omega)
    (by rw [h.wr, ← hC]; exact hp.inScr (d := 96) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  let m₁ := (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S).writeW C (BitVec.setWidth 64 (0 : BitVec 32))
  have zf : s₁.mem = m₁ := by rw [mem₁, h.mem]
  have fz : Frame [⟨C, 8⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S) m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have lastS : Spec.Aes.bytesAt (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S) P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame (VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ S) (hp.save_frame) (by omega)
  have lastZ : Spec.Aes.bytesAt m₁ P L = Spec.Aes.bytesAt s₀.mem P L := by
    rw [bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega),
      lastS]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s₂.gpr r = s.gpr r) ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r h₁ _ => g₁ r h₁,
        by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacTripleDes.X86_64.copy_ok s₁ (by omega) hL (by rw [g₁ _ (by decide), h.rdx])
        (by rw [g₁ _ (by decide)]; exact hc) (by rw [g₁ _ (by decide)]; exact hcx)
        (fun i hi => by rw [rd₁, wr₁, h.rd, h.wr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, h.wr, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + i) (n := 1) (by omega)) dPC) ?_
      rintro s₂ ⟨m₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁ r h₁], by rw [rd₂, rd₁, h.rd],
        by rw [wr₂, wr₁, h.wr]⟩
  · obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
    have r15₂ : s₂.gpr .r15 = S := by rw [g₂ _ (by decide) (by decide), h.r15]
    have rcx₂ : s₂.gpr .rcx = BitVec.ofNat 64 L := by rw [g₂ _ (by decide) (by decide), hcx]
    have rdi₂ : s₂.gpr .rdi = W := by rw [g₂ _ (by decide) (by decide), h.rdi]
    obtain ⟨s₃, run₃, m₃, ax₃, g₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.X86_64.pad_ok s₂ (C := C) (K := W + BitVec.ofNat 64 392) (L := L)
      (by rw [r15₂, rcx₂, BitVec.mul_one, show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, ← hC,
        BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L), ← BitVec.add_assoc])
      (by rw [r15₂, hC]) (by rw [rdi₂])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + L) (n := 1) (by omega))
      (by rw [rd₂, wr₂, ← hC]; exact VG.Proof.CmacTripleDes.X86_64.wr_in (hp.inScr (d := 96) (n := 8) (by decide)))
      (by rw [rd₂, wr₂]; exact hp.inKey (d := 392) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) : s₃.gpr r = s.gpr r := by rw [g₃ r h₁, g₂ r h₁ h₂]
    have hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have fB : Frame [⟨C, 8⟩] m₁ (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 8) (by omega) (by decide))
    have fW : Frame [⟨C, 8⟩] (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have f₃ : Frame [⟨C, 8⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S) s₃.mem := (fz.trans fB).trans fW
    have kD : (⟨W + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint ⟨C, 8⟩ := by
      rw [← hC]; exact hp.keyD (by decide) (FPre.scrD (by decide))
    have k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 392) 8 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 := by
      rw [bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
        bytesAt_frame (VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ S) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.keyD (d := 392) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
    have pad : Spec.Aes.bytesAt s₃.mem C 8 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (8 - L - 1) := by
      have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
        rw [← le8_readW, Mem.readW_writeW_self64]; decide
      have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) hz
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide), h.r14], by rw [gg _ (by decide) (by decide), h.r15],
      by rw [gg _ (by decide) (by decide), h.rbp], by rw [gg _ (by decide) (by decide), h.rsp],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [sl]; exact f₃, ?_⟩
    rw [ax₃, ← m₃, le8_xor, le8_readW, le8_readW, pad, k2]
    simp only [VG.Proof.CmacTripleDes.X86_64.mn, Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega, ite_false]
    exact VG.Proof.CmacTripleDes.X86_64.xor_comm _ _

end

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L : Nat} (hp : VG.Proof.CmacTripleDes.X86_64.FPre s₀ W St P S L) :
    WP isa finPre s₀ (VG.Proof.CmacTripleDes.X86_64.BPost s₀ W St P S L) := by
  have hcx : s₀.gpr .rcx = BitVec.ofNat 64 L := by rw [← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, r15₁, r14₁, rbp₁, g₁, zf₁, m₁, rd₁, wr₁⟩ :=
    VG.Proof.CmacTripleDes.X86_64.pre1_ok s₀ (fun d _ h => by rw [hp.r8]; exact hp.inScr (by omega)) hcx hp.len
  have h1 : VG.Proof.CmacTripleDes.X86_64.P1 s₀ W St P S s₁ := ⟨by rw [r15₁, hp.r8], by rw [r14₁, hp.rdi], by rw [rbp₁, hp.rsi],
    by rw [g₁ _ (by decide), hp.rdi], by rw [g₁ _ (by decide), hp.rdx], g₁ _ (by decide),
    g₁ _ (by decide), by rw [m₁, hp.r8], rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL : L = 8
  · exact WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun _ => VG.Proof.CmacTripleDes.X86_64.full_wp hp hL h1) (fun h => by cases h)
  · exact WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacTripleDes.X86_64.partial_wp hp (by have := hp.len; omega) h1)

theorem xorSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (r : InRegions (s.rd ++ s.wr) St 8) :
    ∃ s', runBlock isa [.alu .xor .rax (.mem (at_ .rbp 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = byteRev64 (s.gpr .rax ^^^ s.mem.readW St 64) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.bind_some, hb, BitVec.add_zero, r,
      ]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, VG.Proof.CmacTripleDes.X86_64.bswap64_eq]
  · simp [gpr_setReg, hr]

theorem storeSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (w : InRegions s.wr St 8) :
    ∃ s', runBlock isa [.bswap .rax, .store (at_ .rbp 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW St (byteRev64 (s.gpr .rax)) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      State.store64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat, gpr_setReg, rd_setReg, wr_setReg, hb,
      BitVec.add_zero, w]
    rfl, ?_⟩
  refine ⟨by simp [mem_setReg, VG.Proof.CmacTripleDes.X86_64.bswap64_eq], fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem finalize_wp {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ finalizeX86_64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rsi = St at hp
  generalize hP : s₀.gpr .rdx = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .rcx).toNat = L at hp
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have tw := hp.st_wrap
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, ax₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.CmacTripleDes.X86_64.xorSt_ok s₁ h₁.rbp
    (by rw [rdwr₁]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have bp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₂ :=
    { sched := ⟨⟨W, 400⟩, by rw [rd₂, h₁.rd, hp.rd]; simp, by rw [g₂ _ (by decide), h₁.r14],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨S, 640⟩, by rw [wr₂, h₁.wr, hp.wr]; simp, by rw [g₂ _ (by decide), h₁.r15],
        by show 48 ≤ 640; decide, by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [g₂ _ (by decide), g₂ _ (by decide), h₁.r14, h₁.r15]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right
          (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.block_ok bp) fun s₃ ⟨same₃, r14₃, ax₃⟩ => ?_)
  rw [WP.block_append_iff]
  have rbp₃ : s₃.gpr .rbp = St := by rw [same₃.rbp, g₂ _ (by decide), h₁.rbp]
  have r15₃ : s₃.gpr .r15 = S := by rw [same₃.r15, g₂ _ (by decide), h₁.r15]
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := VG.Proof.CmacTripleDes.X86_64.storeSt_ok s₃ rbp₃
    (by rw [same₃.wr, wr₂, h₁.wr, hp.wr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  have rdwr₄ : s₄.rd ++ s₄.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 640⟩] := by
    rw [rd₄, wr₄, same₃.rd, same₃.wr, rd₂, wr₂, rdwr₁]
  obtain ⟨s₅, run₅, b, c, d, e, f, g, rsp₅, m₅⟩ := VG.Proof.CmacTripleDes.X86_64.restore_ok s₄ (by rw [g₄ _ (by decide), r15₃]) fun d _ h₂' => by
    rw [rdwr₄]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨S, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  -- Memory.
  have xR₂ : VG.Proof.CmacTripleDes.X86_64.xR s₂ = ⟨S, 48⟩ := by rw [VG.Proof.CmacTripleDes.X86_64.xR, g₂ _ (by decide), h₁.r15]
  have f₃ : Frame [⟨S, 48⟩] s₁.mem s₃.mem := by rw [← m₂, ← xR₂]; exact same₃.frame
  have f₄ : Frame [⟨St, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fAll : Frame [VG.Proof.CmacTripleDes.X86_64.slot12 S, ⟨S, 48⟩, ⟨St, 8⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S) s₅.mem := by
    rw [m₅]
    exact ((h₁.frame.mono fun r hr => by simp at hr; simp [hr]).trans (f₃.mono fun r hr => by
      simp at hr; simp [hr])).trans (f₄.mono fun r hr => by simp at hr; simp [hr])
  have big : Frame [⟨S, 640⟩, ⟨St, 8⟩] s₀.mem s₅.mem :=
    ((VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ S).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S, 640⟩, by simp, FPre.scrD (by decide)⟩).trans (fAll.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 640⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨S, 640⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨St, 8⟩, by simp, fun _ h => h⟩)
  have hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
    intro d h₁' h₂'
    rw [← m₅]
    refine fAll.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact (hp.st_scr.sub_right (FPre.scrD (by omega))).symm
  refine ⟨⟨VG.Proof.CmacTripleDes.X86_64.restored (S := S) hm ⟨b, c, d, e, f, g⟩ (by rw [rsp₅, g₄ _ (by decide), same₃.rsp,
                                  g₂ _ (by decide), h₁.rsp]), ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_scr
    · exact hp.ret_st
  · intro hk msg hml hne hst
    rw [hW, hSt, hP, hL] at *
    have keyD (r : Region) (hr : Region.Sub r ⟨S, 640⟩) : (⟨W, 384⟩ : Region).Disjoint r :=
      (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right hr
    have f₁ : Frame [⟨S + BitVec.ofNat 64 48, 48⟩, VG.Proof.CmacTripleDes.X86_64.slot12 S] s₀.mem s₁.mem :=
      ((VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ S).mono fun r hr => by simp at hr; simp [hr]).trans
        (h₁.frame.mono fun r hr => by simp at hr; simp [hr])
    have hS' : VG.Proof.CmacTripleDes.X86_64.sch s₂ = Spec.TripleDes.scheduleAt s₀.mem W := by
      rw [VG.Proof.CmacTripleDes.X86_64.sch, g₂ _ (by decide), h₁.r14, m₂]
      exact VG.Proof.CmacTripleDes.X86_64.scheduleAt_frame f₁ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyD _ (FPre.scrD (by decide))
        · exact keyD _ (FPre.scrD (by decide))
    have hst₁ : le8 (s₁.mem.readW St 64) = Spec.Aes.bytesAt s₀.mem St 8 := by
      rw [le8_readW]
      exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))) (by decide)
    have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem W)
    have hk' : Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 384) 8 ++
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 =
        (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.X86_64.ciphAt s₀.mem W) 8).1 ++ (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.X86_64.ciphAt s₀.mem W) 8).2 := by
      rw [show W + BitVec.ofNat 64 392 = W + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
        (Offset.add_add W 384 8).symm, ← bytesAt_split]; exact hk
    obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, VG.Proof.CmacTripleDes.X86_64.ciphAt, hks, length_le8])
    show Spec.Aes.bytesAt s₅.mem St 8 = _
    rw [m₅, m₄, ← le8_readW, Mem.readW_writeW_self64, ax₃, ax₂, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
      macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, VG.Proof.CmacTripleDes.X86_64.xor_comm]

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Keys`. -/
section

/-!
# DES's key schedule on x86-64

`roundKeys` only moves bits of the key in `rax` to the round keys it
stores: the kernel checks it over the lane domain (`roundKeys_check`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86_64
  VG.Proof.CmacTripleDes

/-- The round keys' slots, at `rbp`. -/
def kCfg : Cfg := { base := .rbp, slots := 16, ext := .rbp, exts := 0 }

/-- Bit `q` of round key `j`: bit `rkSrc j q` of the key (input word 0). -/
def rkG (j q : Nat) : List Nat := if q < 48 then [rkSrc j q] else []

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 16).all fun j => e.slot j == some (outWord (VG.Proof.CmacTripleDes.X86_64.rkG j))

theorem roundKeys_check : VG.X86_64.Straight.check (lanes 64 6) VG.Proof.CmacTripleDes.X86_64.kCfg (linExt 1) roundKeys (linEnv [(.rax, 0)]) VG.Proof.CmacTripleDes.X86_64.kPost = true := by
  rw [VG.Proof.CmacTripleDes.X86_64.roundKeys_eq]; lit_decide

theorem rkG_lt : ∀ j < 16, ∀ q < 64, ∀ a ∈ VG.Proof.CmacTripleDes.X86_64.rkG j q, a < 2 ^ 6 := by lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.rcx, .rdx, .r9]

/-- Every register `roundKeys` writes is one of `kWrites`: checked once
for every instruction, rather than once for every other register. -/
theorem roundKeys_writes : roundKeys.all (fun i => (i.dst).all kWrites.contains) = true := by
  rw [VG.Proof.CmacTripleDes.X86_64.roundKeys_eq]; lit_decide

theorem roundKeys_kept {r : Reg} (hr : r ∉ VG.Proof.CmacTripleDes.X86_64.kWrites) : roundKeys.all (fun i => i.dst != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have h := List.all_eq_true.mp VG.Proof.CmacTripleDes.X86_64.roundKeys_writes i hi
    cases hd : i.dst with
    | none => rfl
    | some d =>
      rw [hd, Option.all_some] at h
      have hd' : d ∈ VG.Proof.CmacTripleDes.X86_64.kWrites := by simpa using h
      have hne : d ≠ r := fun e => hr (e ▸ hd')
      simpa using hne

/-- The round keys of the DES key in `rax`, in `[rbp + 8 j]`. -/
theorem roundKeys_ok {s : VG.X86_64.State} (hok : Ok VG.Proof.CmacTripleDes.X86_64.kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, s'.mem.readW (wordAddr (s.gpr .rbp) j) 64 =
        ((Spec.TripleDes.expandDesKey (s.gpr .rax)).getD j 0).zeroExtend 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ VG.Proof.CmacTripleDes.X86_64.kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.X86_64.kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.X86_64.roundKeys_check
  let W : Nat → BitVec 64 := fun _ => s.gpr .rax
  have hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) VG.Proof.CmacTripleDes.X86_64.kCfg (linExt 1) (linEnv [(.rax, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => absurd hj (by simp [VG.Proof.CmacTripleDes.X86_64.kCfg])⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h
    have hw : ∀ q < 64, (s'.mem.readW (wordAddr (s.gpr .rbp) j) 64).getLsbD q = xorBits W (VG.Proof.CmacTripleDes.X86_64.rkG j q) := by
      have := outWord_rel (VG.Proof.CmacTripleDes.X86_64.rkG_lt j hj) (p.rel.slot j _ (by simp only [VG.Proof.CmacTripleDes.X86_64.kCfg]; omega) h)
      rwa [p.base] at this
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [hw q hq, BitVec.getLsbD_setWidth, VG.Proof.CmacTripleDes.X86_64.rkG]
    by_cases h48 : q < 48
    · rw [ite_eq_left h48, getLsbD_expandDesKey _ hj h48]
      have := VG.Proof.CmacTripleDes.X86_64.rkSrc_lt j hj q h48
      simp [xorBits, bitOf, W, hq, Nat.mod_eq_of_lt this]
    · rw [ite_eq_right h48, BitVec.getLsbD_of_ge _ _ (by omega)]
      simp
  · have h := VG.Proof.CmacTripleDes.X86_64.roundKeys_kept hr
    simp [h]

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init`. -/
section

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_init`, the key schedule

`initPre` saves the registers and stores the three DES keys, as big-endian
integers, in slots 12–14; each iteration of the loop then writes one DES key's
sixteen round keys (`KInv`).
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.Straight VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes
  VG.Proof.Cmac

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .rdi
abbrev Kl : Nat := (s₀.gpr .rsi).toNat
abbrev O : Addr := s₀.gpr .rdx
abbrev Sc : Addr := s₀.gpr .rcx

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.CmacTripleDes.X86_64.K s₀) (VG.Proof.CmacTripleDes.X86_64.Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 := byteRev64 (s₀.mem.readW (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) j)) 64)

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩]
  wr : s₀.wr = [⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩]
  key_out : (⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩
  key_scr : (⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩
  out_scr : (⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩
  ret_out : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩
  ret_scr : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩
  key_wrap : (VG.Proof.CmacTripleDes.X86_64.K s₀).toNat + VG.Proof.CmacTripleDes.X86_64.Kl s₀ ≤ 2 ^ 64
  out_wrap : (VG.Proof.CmacTripleDes.X86_64.O s₀).toNat + 400 ≤ 2 ^ 64
  scr_wrap : (VG.Proof.CmacTripleDes.X86_64.Sc s₀).toNat + 640 ≤ 2 ^ 64
  valid : VG.Proof.CmacTripleDes.X86_64.Kl s₀ = 16 ∨ VG.Proof.CmacTripleDes.X86_64.Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initX86_64.pre s₀) : VG.Proof.CmacTripleDes.X86_64.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.Sc s₀
  rbx : s.gpr .rbx = VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 (96 + 8 * i)
  rbp : s.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (128 * i)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (3 - i)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 (96 + 8 * j)) 64 = VG.Proof.CmacTripleDes.X86_64.kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀)).getD n 0
  frame : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩, ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 384⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)) s.mem

/-! ## The prologue -/

theorem keyOff_le {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.IPre s₀) {j : Nat} (hj : j < 3) : keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) j + 8 ≤ VG.Proof.CmacTripleDes.X86_64.Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

theorem initA_ok (s : State)
    (hw : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 d) 8)
    (r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) (r8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (save .rcx ++ ([.mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx)] : List Instr) ++
        keyWord 0 12 ++ keyWord 8 13 ++ ([.alu .cmp .rsi (.imm 16)] : List Instr)) s = some s' ∧
      s'.gpr .r15 = s.gpr .rcx ∧ s'.gpr .rbp = s.gpr .rdx ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rsi - BitVec.signExtend 64 (16 : BitVec 32) == 0) ∧
      s'.mem = (((VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .rcx)).writeW (s.gpr .rcx + BitVec.ofNat 64 96)
          (bswap64 ((VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .rcx)).readW (s.gpr .rdi) 64))).writeW (s.gpr .rcx + BitVec.ofNat 64 104)
          (bswap64 (((VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .rcx)).writeW (s.gpr .rcx + BitVec.ofNat 64 96)
            (bswap64 ((VG.Proof.CmacTripleDes.X86_64.savedMem s (s.gpr .rcx)).readW (s.gpr .rdi) 64))).readW
            (s.gpr .rdi + BitVec.ofNat 64 8) 64))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.save_ok s .rcx fun d h₁ h₂ => hw d h₁ (by omega)
  have hw' : ∀ d, 48 ≤ d → d + 8 ≤ 112 → InRegions s₁.wr (s₁.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [g₁, wr₁]; exact hw
  have r0' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 0) 8 := by
    rw [g₁, rd₁, wr₁, BitVec.add_zero]; exact r0
  have r8' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 8) 8 := by
    rw [g₁, rd₁, wr₁]; exact r8
  refine ⟨_, by
    rw [List.append_assoc, List.append_assoc, List.append_assoc, VG.Proof.CmacTripleDes.X86_64.runBlock_append, h₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, BitVec.reduceSignExtend, keyWord, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, execAlu, State.load64, State.store64, State.ea, VG.Proof.CmacTripleDes.X86_64.offset_nat,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      hw' 96 (by decide) (by decide), hw' 104 (by decide) (by decide), r0', r8']
    rfl, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, BitVec.reduceSignExtend, gpr_setReg, gpr_arithFlags, zf_arithFlags,
    mem_arithFlags, rd_arithFlags, wr_arithFlags, g₁, m₁, rd₁, wr₁,
    BitVec.add_zero, and_self]

theorem loadKey_ok (s : State) (d : Nat) (r : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rdi d))] s = some s' ∧
      s'.gpr .rax = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.map_some, r, ite_true]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], rfl, rfl, rfl⟩

theorem initC_ok (s : State) (w : InRegions s.wr (s.gpr .r15 + BitVec.ofNat 64 112) 8) :
    ∃ s', runBlock isa [.bswap .rax, .store (at_ .r15 112) .rax, .mov .rbx (.reg .r15), .alu .add .rbx (.imm 96),
        .mov32 .r10 (.imm 3)] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r15 + BitVec.ofNat 64 112) (byteRev64 (s.gpr .rax)) ∧
      s'.gpr .rbx = s.gpr .r15 + BitVec.ofNat 64 96 ∧ s'.gpr .r10 = BitVec.ofNat 64 3 ∧
      (∀ r, r ∉ [Reg.rax, .rbx, .r10] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      readSrc32, execAlu, State.store64, State.ea, State.setReg32, VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, rd_setReg, wr_setReg, w]
    rfl, ?_⟩
  refine ⟨by simp [mem_setReg, mem_arithFlags, VG.Proof.CmacTripleDes.X86_64.bswap64_eq], by simp [gpr_setReg],
    by simp [gpr_setReg], fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_setReg, hr.1, hr.2.1, hr.2.2]

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) : InRegions s₀.wr (VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.out_wrap; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.X86_64.Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩] s₀.mem m) {d : Nat} (hd : d + 8 ≤ VG.Proof.CmacTripleDes.X86_64.Kl s₀) :
    m.readW (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 d) 64 = s₀.mem.readW (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

end

theorem scrSub {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

theorem initPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.IPre s₀) : WP isa initPre s₀ (VG.Proof.CmacTripleDes.X86_64.KInv s₀ 0) := by
  have sw := hp.scr_wrap
  have kl : 16 ≤ VG.Proof.CmacTripleDes.X86_64.Kl s₀ := by rcases hp.valid with h | h <;> omega
  obtain ⟨s₁, run₁, r15₁, rbp₁, rdi₁, rsp₁, zf₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.initA_ok s₀
    (fun d _ h => hp.inScr (by omega)) (by simpa using hp.inKey (d := 0) (n := 8) (by omega) (by decide))
    (hp.inKey (d := 8) (n := 8) (by omega) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The memory so far.
  have fS : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩] s₀.mem (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)) := (VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, VG.Proof.CmacTripleDes.X86_64.scrSub (by decide)⟩
  have c96 : (⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96) (64 / 8) := by
    simpa using Offset.contains_base (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96) (d := 0) (n := 8) (k := 24) (by decide) (by decide)
  have cAt (d : Nat) (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 120) :
      (⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d) (64 / 8) := by
    rw [show VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d = VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96 + BitVec.ofNat 64 (d - 96) from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₁ : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)) s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW (List.mem_singleton_self _) _
      (cAt 104 (by decide) (by decide))
  have fA : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩] s₀.mem s₁.mem := fS.trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, VG.Proof.CmacTripleDes.X86_64.scrSub (by decide)⟩)
  have cS (d : Nat) (h : d + 8 ≤ 640) : (⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  have kr0 := hp.keyRead fS (d := 0) (by omega)
  have kr8 := hp.keyRead (fS.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _)
    (bswap64 ((VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)).readW (VG.Proof.CmacTripleDes.X86_64.K s₀) 64)) (cS 96 (by decide)))) (d := 8) (by omega)
  simp only [BitVec.add_zero] at kr0
  have k0 : s₁.mem.readW (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96) 64 = VG.Proof.CmacTripleDes.X86_64.kw s₀ 0 := by
    rw [m₁, VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64, VG.Proof.CmacTripleDes.X86_64.bswap64_eq]
    erw [kr0]
    simp [VG.Proof.CmacTripleDes.X86_64.kw, keyOff]
  have k1 : s₁.mem.readW (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 104) 64 = VG.Proof.CmacTripleDes.X86_64.kw s₀ 1 := by
    rw [m₁, Mem.readW_writeW_self64, VG.Proof.CmacTripleDes.X86_64.bswap64_eq]
    erw [kr8]
    simp [VG.Proof.CmacTripleDes.X86_64.kw, keyOff]
  -- The third DES key.
  have hz : isa.eval .e s₁ = some (decide (VG.Proof.CmacTripleDes.X86_64.Kl s₀ = 16)) := by
    show s₁.zf = _
    rw [zf₁, show BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 from rfl,
      show s₀.gpr .rsi = BitVec.ofNat 64 (VG.Proof.CmacTripleDes.X86_64.Kl s₀) by apply BitVec.eq_of_toNat_eq; simp,
      Offset.ofNat_sub_ofNat_beq (by have := (s₀.gpr .rsi).isLt; omega) (by decide)]
  have third : ∀ d, d + 8 ≤ VG.Proof.CmacTripleDes.X86_64.Kl s₀ → keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) 2 = d →
      WP isa (.block [.mov .rax (.mem (at_ .rdi d))]) s₁ fun s₂ =>
        s₂.gpr .rax = s₀.mem.readW (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧
        s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := by
    intro d hd _
    obtain ⟨s₂, run₂, ax₂, g₂, m₂, rd₂, wr₂⟩ := VG.Proof.CmacTripleDes.X86_64.loadKey_ok s₁ d
      (by rw [rdi₁, rd₁, wr₁]; exact hp.inKey (by omega) (by decide))
    exact WP.of_runBlock ⟨s₂, run₂, by rw [ax₂, rdi₁, hp.keyRead fA hd], g₂, m₂, by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.gpr .rax = s₀.mem.readW (VG.Proof.CmacTripleDes.X86_64.K s₀ + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) 2)) 64 ∧
        (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_
      fun s₂ h₂ => ?_)
  · by_cases h16 : VG.Proof.CmacTripleDes.X86_64.Kl s₀ = 16
    · refine WP.ite true (by rw [hz]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by simp [keyOff, h16])
      rwa [show keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [hz]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : VG.Proof.CmacTripleDes.X86_64.Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by simp [keyOff, h24])
      rwa [show keyOff (VG.Proof.CmacTripleDes.X86_64.Kl s₀) 2 = 16 by simp [keyOff, h24]]
  · obtain ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ := h₂
    have r15₂ : s₂.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.Sc s₀ := by rw [g₂ _ (by decide), r15₁]
    obtain ⟨s₃, run₃, m₃, rbx₃, r10₃, g₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.X86_64.initC_ok s₂
      (by rw [wr₂, r15₂]; exact hp.inScr (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (hr : r ∉ [Reg.rax, .rbx, .r10]) : s₃.gpr r = s₁.gpr r := by
      rw [g₃ r hr, g₂ r (by rintro rfl; simp at hr)]
    rw [r15₂, m₂, ax₂] at m₃
    rw [r15₂] at rbx₃
    refine ⟨by rw [gg _ (by decide), r15₁], by rw [rbx₃], by rw [gg _ (by decide), rbp₁]; simp, by rw [r10₃],
      by rw [gg _ (by decide), rsp₁], by rw [rd₃, rd₂], by rw [wr₃, wr₂], fun j hj => ?_,
      fun n hn => absurd hn (by omega), ?_⟩
    · rw [m₃]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k0
      · rw [VG.Proof.CmacTripleDes.X86_64.readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k1
      · rw [Mem.readW_writeW_self64]
    · rw [m₃]
      exact (f₁.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩)
        (by simp) _ (cAt 112 (by decide) (by decide))

/-! ## The round keys -/

theorem loadRbx_ok (s : State) (r : InRegions (s.rd ++ s.wr) (s.gpr .rbx) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .rbx 0))] s = some s' ∧
      s'.gpr .rax = s.mem.readW (s.gpr .rbx) 64 ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
      VG.Proof.CmacTripleDes.X86_64.offset_nat, BitVec.add_zero, Option.map_some, r, ite_true]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], fun r hr => by simp [gpr_setReg, hr], rfl, rfl, rfl⟩

theorem keysTail_ok (s : State) :
    ∃ s', runBlock isa [.alu .add .rbp (.imm 128), .alu .add .rbx (.imm 8), .alu .sub .r10 (.imm 1)] s = some s' ∧
      s'.gpr .rbp = s.gpr .rbp + BitVec.ofNat 64 128 ∧ s'.gpr .rbx = s.gpr .rbx + BitVec.ofNat 64 8 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some ((s.gpr .r10 - 1) == 0) ∧
      (∀ r, r ∉ [Reg.rbp, .rbx, .r10] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_setReg, zf_arithFlags]; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2.1, hr.2.2]

theorem keyStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : VG.Proof.CmacTripleDes.X86_64.KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => s'.zf = some (decide (i + 1 = 3)) ∧ VG.Proof.CmacTripleDes.X86_64.KInv s₀ (i + 1) s' := by
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  have rdwr : s.rd ++ s.wr = [⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩, ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  rw [keysBody, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, ax₁, g₁, m₁, rd₁, wr₁⟩ := VG.Proof.CmacTripleDes.X86_64.loadRbx_ok s (by
    rw [rdwr, h.rbx]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega)))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have rbp₁ : s₁.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (128 * i) := by rw [g₁ _ (by decide), h.rbp]
  have hok : Ok VG.Proof.CmacTripleDes.X86_64.kCfg s₁ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.X86_64.kCfg]), by decide, fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.X86_64.kCfg])⟩
    rw [wr₁, h.wr, hp.wr, show kCfg.base = .rbp from rfl, rbp₁]
    exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, by simp, contains_word (off := 128 * i) (n := 400) rfl
      (by simp only [VG.Proof.CmacTripleDes.X86_64.kCfg] at hk; omega) (by show 400 ≤ 400; decide) (by show 400 < 2 ^ 64; decide)⟩
  obtain ⟨s₂, run₂, rk₂, rd₂, wr₂, g₂, f₂⟩ := VG.Proof.CmacTripleDes.X86_64.roundKeys_ok hok
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, rbp₃, rbx₃, r10₃, zf₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.X86_64.keysTail_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have gk (r : Reg) (h₁ : r ∉ VG.Proof.CmacTripleDes.X86_64.kWrites) (h₂ : r ≠ .rax) : s₂.gpr r = s.gpr r := by rw [g₂ r h₁, g₁ r h₂]
  have slotR : slotRegion VG.Proof.CmacTripleDes.X86_64.kCfg s₁ = ⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .rbp from rfl, rbp₁]; rfl
  rw [slotR] at f₂
  have r10v : s.gpr .r10 = BitVec.ofNat 64 (3 - i) := h.r10
  have dec : BitVec.ofNat 64 (3 - i) - 1 = BitVec.ofNat 64 (3 - (i + 1)) := VG.Proof.CmacTripleDes.X86_64.ofNat_sub_one (by omega) (by omega)
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩⟩
  · rw [zf₃, gk _ (by decide) (by decide), r10v, dec, VG.Proof.CmacTripleDes.X86_64.ofNat_beq_zero (by omega)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.r15]
  · rw [rbx₃, gk _ (by decide) (by decide), h.rbx, Offset.add_add, show 96 + 8 * i + 8 = 96 + 8 * (i + 1) by omega]
  · rw [rbp₃, gk _ (by decide) (by decide), h.rbp, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [r10₃, gk _ (by decide) (by decide), r10v, dec]
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.rsp]
  · rw [rd₃, rd₂, rd₁, h.rd]
  · rw [wr₃, wr₂, wr₁, h.wr]
  · rw [m₃, ← h.keys j hj, ← m₁]
    refine f₂.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 (96 + 8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (VG.Proof.CmacTripleDes.X86_64.scrSub (by omega))
  · rw [m₃]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', ← m₁]
      refine f₂.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := VG.Proof.CmacTripleDes.X86_64.keyOff_le hp hi
      rw [show VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 (8 * (16 * i + j)) = wordAddr (s₁.gpr .rbp) j by
          rw [rbp₁, wordAddr, Offset.add_add, show 128 * i + 8 * j = 8 * (16 * i + j) by omega],
        rk₂ j hj, ax₁, h.rbx, h.keys i hi, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₃]
    rw [m₁] at f₂
    exact h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)

theorem keys_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.X86_64.IPre s₀) {s : State} (h : VG.Proof.CmacTripleDes.X86_64.KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (VG.Proof.CmacTripleDes.X86_64.KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.X86_64.KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ VG.Proof.CmacTripleDes.X86_64.KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.X86_64.keyStep_ok hp hi ht) fun t' ⟨zf', h'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by simp [X86_64.eval, zf', hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by simp [X86_64.eval, zf', hz], 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

theorem initD_ok (s : State) :
    ∃ s', runBlock isa [.mov .r14 (.reg .rbp), .alu .sub .r14 (.imm 384), .mov32 .rax (.imm 0)] s = some s' ∧
      s'.gpr .r14 = s.gpr .rbp - BitVec.ofNat 64 384 ∧ s'.gpr .rax = 0 ∧
      (∀ r, r ∉ [Reg.r14, .rax] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, Option.bind_some,
      Option.map_some, State.setReg32]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, hr.1, hr.2]

theorem dbl_ok (s : State) (d : Nat) (w : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (dbl d) s = some s' ∧
      s'.gpr .rax = dbl64 (s.gpr .rax) ∧
      s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (byteRev64 (dbl64 (s.gpr .rax))) ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      readSrc32, execAlu, execShift, State.store64, State.ea, State.setReg32, VG.Proof.CmacTripleDes.X86_64.offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, rd_setReg, wr_setReg, rd_arithFlags,
      wr_arithFlags, rd_setFlags, wr_setFlags, ite_true, ite_false, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · rw [← dbl64_eq]; simp [gpr_setReg]
  · rw [← dbl64_eq]; simp [mem_setReg, mem_arithFlags, mem_setFlags, VG.Proof.CmacTripleDes.X86_64.bswap64_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_setReg, gpr_setFlags, hr.1, hr.2.1, hr.2.2]

theorem init_wp {s₀ : State} (h0 : initX86_64.pre s₀) :
    WP isa init s₀ fun s' => gprPreserved s₀ s' ∧ initX86_64.post s₀ s' := by
  have hp := IPre.of h0
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.keys_ok hp h₁) fun s₂ h₂ => ?_)
  obtain ⟨s₃, run₃, r14₃, ax₃, g₃, m₃, rd₃, wr₃⟩ := VG.Proof.CmacTripleDes.X86_64.initD_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have r14₃' : s₃.gpr .r14 = VG.Proof.CmacTripleDes.X86_64.O s₀ := by
    rw [r14₃, h₂.rbp, show 128 * 3 = 384 from rfl, BitVec.add_sub_cancel]
  have r15₃ : s₃.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.Sc s₀ := by rw [g₃ _ (by decide), h₂.r15]
  have bp : VG.Proof.CmacTripleDes.X86_64.BlockPre s₃ :=
    { sched := ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, by rw [rd₃, wr₃, h₂.rd, h₂.wr, hp.rd, hp.wr]; simp, by rw [r14₃'],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩, by rw [wr₃, h₂.wr, hp.wr]; simp, by rw [r15₃], by show 48 ≤ 640; decide,
        by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [r14₃', r15₃]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.X86_64.block_ok bp) fun s₄ ⟨same₄, r14₄, ax₄⟩ => ?_)
  -- The key schedule.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (VG.Proof.CmacTripleDes.X86_64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  have xR₃ : VG.Proof.CmacTripleDes.X86_64.xR s₃ = ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 48⟩ := by rw [VG.Proof.CmacTripleDes.X86_64.xR, r15₃]
  have f₄ : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 48⟩] s₂.mem s₄.mem := by rw [← m₃, ← xR₃]; exact same₄.frame
  have outX : ∀ r ∈ [(⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 48⟩ : Region)], (⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  have hsch₄ : Spec.TripleDes.scheduleAt s₄.mem (VG.Proof.CmacTripleDes.X86_64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀) := by
    rw [VG.Proof.CmacTripleDes.X86_64.scheduleAt_frame f₄ outX, hsch₂]
  rw [WP.block_append_iff, WP.block_append_iff]
  have rbp₄ : s₄.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 := by
    rw [same₄.rbp, g₃ _ (by decide), h₂.rbp]
  obtain ⟨s₅, run₅, ax₅, m₅, g₅, rd₅, wr₅⟩ := VG.Proof.CmacTripleDes.X86_64.dbl_ok s₄ 0 (by
    rw [same₄.wr, wr₃, h₂.wr, rbp₄, Offset.add_add]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have rbp₅ : s₅.gpr .rbp = VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 := by rw [g₅ _ (by decide), rbp₄]
  obtain ⟨s₆, run₆, ax₆, m₆, g₆, rd₆, wr₆⟩ := VG.Proof.CmacTripleDes.X86_64.dbl_ok s₅ 8 (by
    rw [wr₅, same₄.wr, wr₃, h₂.wr, rbp₅, Offset.add_add]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have r15₆ : s₆.gpr .r15 = VG.Proof.CmacTripleDes.X86_64.Sc s₀ := by rw [g₆ _ (by decide), g₅ _ (by decide), same₄.r15, r15₃]
  have rdwr₆ : s₆.rd ++ s₆.wr = [⟨VG.Proof.CmacTripleDes.X86_64.K s₀, VG.Proof.CmacTripleDes.X86_64.Kl s₀⟩, ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩] := by
    rw [rd₆, wr₆, rd₅, wr₅, same₄.rd, same₄.wr, rd₃, wr₃, h₂.rd, h₂.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₇, run₇, b, c, d, e, f, g, rsp₇, m₇⟩ := VG.Proof.CmacTripleDes.X86_64.restore_ok s₆ r15₆ fun d _ h₂' => by
    rw [rdwr₆]; exact VG.Proof.CmacTripleDes.X86_64.in_rw (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  -- Memory.
  have sub384 : Region.Sub ⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384, 16⟩ ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩ := Offset.sub_base _ (by decide)
  have c8 : (⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have c0 : (⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have f₆ : Frame [⟨VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅, rbp₅, rbp₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  have fAll : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 96, 24⟩, ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 48⟩] (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)) s₇.mem := by
    rw [m₇]
    refine ((h₂.frame.sub fun r hr => ?_).trans (f₄.mono fun r hr => by simp at hr; simp [hr])).trans
      (f₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, by simp, sub384⟩
  have hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s₆.mem.readW (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d) 64 = (VG.Proof.CmacTripleDes.X86_64.savedMem s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)).readW (VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d) 64 := by
    intro d h₁' h₂'
    rw [← m₇]
    refine fAll.readW (r := ⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (d := d) (e := 96) (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (VG.Proof.CmacTripleDes.X86_64.scrSub (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
  refine ⟨⟨VG.Proof.CmacTripleDes.X86_64.restored hm ⟨b, c, d, e, f, g⟩ (by rw [rsp₇, g₆ _ (by decide), g₅ _ (by decide), same₄.rsp,
                                  g₃ _ (by decide), h₂.rsp]), ?_⟩, ?_, ?_⟩
  · have big : Frame [⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩, ⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩] s₀.mem s₇.mem :=
      ((VG.Proof.CmacTripleDes.X86_64.savedMem_frame s₀ (VG.Proof.CmacTripleDes.X86_64.Sc s₀)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩, by simp, VG.Proof.CmacTripleDes.X86_64.scrSub (by decide)⟩).trans (fAll.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩, by simp, VG.Proof.CmacTripleDes.X86_64.scrSub (by decide)⟩
        · exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.O s₀, 400⟩, by simp, fun _ h => h⟩
        · exact ⟨⟨VG.Proof.CmacTripleDes.X86_64.Sc s₀, 640⟩, by simp, Region.sub_prefix (by decide)⟩)
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_scr
    · exact hp.ret_out
  · show Spec.TripleDes.scheduleAt s₇.mem (VG.Proof.CmacTripleDes.X86_64.O s₀) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀)
    rw [m₇, VG.Proof.CmacTripleDes.X86_64.scheduleAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by decide) (by omega)), hsch₄]
  · show Spec.Aes.bytesAt s₇.mem (VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀))) 8).2
    have hk : VG.Proof.CmacTripleDes.X86_64.sch s₃ = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.X86_64.keyB s₀) := by rw [VG.Proof.CmacTripleDes.X86_64.sch, r14₃', m₃, hsch₂]
    rw [subkeys_tdes, m₇, m₆, rbp₅, ax₅, m₅, rbp₄, ax₄, ax₃, hk,
      show VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0 = VG.Proof.CmacTripleDes.X86_64.O s₀ + BitVec.ofNat 64 384 from BitVec.add_zero _]
    exact bytesAt_store2 _ _ _ _

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Implies`. -/
section

/-!
# TDEA-CMAC on x86-64: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initX86_64.Implies (initScratchContract X86_64.abi 0) := by
  sig_implies [initScratchContract, initScratchSig, Spec.Cmac.tdesInitPre, Spec.Cmac.tdesInitPost,
    VG.Proof.CmacTripleDes.X86_64.initX86_64, X86_64.abi,
    X86_64.argRegs] [initSat] using VG.Proof.CmacTripleDes.X86_64.initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem update_implies : updateX86_64.Implies (updateScratchContract X86_64.abi 0) := by
  sig_implies [updateScratchContract, updateScratchSig, Spec.Cmac.tdesUpdatePost, VG.Proof.CmacTripleDes.X86_64.updateX86_64,
    X86_64.abi,
    X86_64.argRegs] [updSat] using VG.Proof.CmacTripleDes.X86_64.updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finalize_implies : finalizeX86_64.Implies (finalizeScratchContract X86_64.abi 0) := by
  sig_implies [finalizeScratchContract, finalizeScratchSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, VG.Proof.CmacTripleDes.X86_64.finalizeX86_64, X86_64.abi,
    X86_64.argRegs] [finSat] using VG.Proof.CmacTripleDes.X86_64.finSat

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Verified`. -/
section

/-!
# TDEA-CMAC on x86-64: `Verified`

Correctness and constant time under this target's contracts (`Contract.lean`),
and the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which imply them, with no stack: the
functions call nothing.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem update_mx : update.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finalize_mx : finalize.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacTripleDes.X86_64.init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec VG.Proof.CmacTripleDes.X86_64.init_mx he hg, hp⟩

theorem update_correct (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacTripleDes.X86_64.update_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec VG.Proof.CmacTripleDes.X86_64.update_mx he hg, hp⟩

theorem finalize_correct (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := VG.Proof.CmacTripleDes.X86_64.finalize_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec VG.Proof.CmacTripleDes.X86_64.finalize_mx he hg, hp⟩

theorem init_verified : Verified X86_64.target init (initScratchContract X86_64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.X86_64.init_correct VG.Proof.CmacTripleDes.X86_64.init_ct VG.Proof.CmacTripleDes.X86_64.init_implies

theorem update_verified : Verified X86_64.target update (updateScratchContract X86_64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.X86_64.update_correct VG.Proof.CmacTripleDes.X86_64.update_ct VG.Proof.CmacTripleDes.X86_64.update_implies

theorem finalize_verified : Verified X86_64.target finalize (finalizeScratchContract X86_64.abi 0) :=
  Verified.of_correct VG.Proof.CmacTripleDes.X86_64.finalize_correct VG.Proof.CmacTripleDes.X86_64.finalize_ct VG.Proof.CmacTripleDes.X86_64.finalize_implies

end VG.Proof.CmacTripleDes.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.X86_64.Frame`. -/
section

/-!
# TDEA-CMAC on x86-64, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame of 648 bytes that allocates it
(`Verified.stackScratch`): the 640 bytes of working space, and 8 more to keep
`rsp` aligned.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.CmacTripleDes.X86_64.initSat with
                                           wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract X86_64.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using VG.Proof.CmacTripleDes.X86_64.initFrameSat

theorem init_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .rcx init)
    (Spec.Cmac.tdesInitContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre X86_64.abi.ptrBits) (post := Spec.Cmac.tdesInitPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) VG.Proof.CmacTripleDes.X86_64.init_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) VG.Proof.CmacTripleDes.X86_64.initFrameSat_pre

theorem update_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .r8 update)
      (Spec.Cmac.tdesUpdateContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) VG.Proof.CmacTripleDes.X86_64.update_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .r8 finalize)
      (Spec.Cmac.tdesFinalizeContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre X86_64.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) VG.Proof.CmacTripleDes.X86_64.finalize_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))

end VG.Proof.CmacTripleDes.X86_64

end
