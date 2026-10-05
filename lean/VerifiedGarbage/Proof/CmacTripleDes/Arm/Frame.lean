import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.CmacTripleDes.Arm.Round
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit`. -/
section

/-!
# The DES block's 32-bit ARM code as literals, for kernel-evaluated checks

The S-boxes' leaves, the round's parts, `IP`, `IP⁻¹` and the block are each
evaluated once, here: the checks of each part (`Round.lean`, `Block.lean`)
and the literals of the functions that run the block (`Lit.lean`) read these
literals rather than evaluate the S-box leaves and bit permutations again.
-/

namespace VG

materialize_table Impl.CmacTripleDes.Arm.leaf 2 64
materialize_value Impl.CmacTripleDes.Arm.inputs

/-- Half `h`'s tree. -/
abbrev Proof.CmacTripleDes.Arm.sbCode (h : Nat) : List VG.Arm.Instr :=
  Impl.CmacTripleDes.Arm.mux h 6 0 .r0

materialize_table Proof.CmacTripleDes.Arm.sbCode 2
materialize_value Impl.CmacTripleDes.Arm.sboxes
materialize_value Impl.CmacTripleDes.Arm.output
materialize_value Impl.CmacTripleDes.Arm.ipCode
materialize_value Impl.CmacTripleDes.Arm.fpCode
materialize_code Impl.CmacTripleDes.Arm.block

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Round`. -/
section

/-!
# A DES round on 32-bit ARM

Untrusted: everything here is checked by Lean.

As on x86-64 (`Proof/CmacTripleDes/X86_64/Round.lean`): the round's parts are
checked by evaluation (`Straight.check`), the broadcast inputs (`inputs`)
and the output (`output`) over the lane domain, and each half's S-boxes
(`mux`) over the row domain (`Bitslice.rows`), on all 64 values of a box's
input at once. A half's slots hold, at each position, the bits of one box's
input, so each half is checked on its own. `round_ok` composes them: `R` and
`L ⊕ f(R, K)`, with `K` the round key's low word and the low 16 bits of its
high word.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.Arm

/-- The round's memory: the broadcast inputs and half 0's outputs in slots
0–12 at `r10`, and the round key's two words at `r9`. -/
def rCfg : Cfg := { base := .r10, slots := 13, ext := .r9, exts := 2 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : VG.Arm.State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r10) k) 32

/-- The round key's words. -/
abbrev keyLo (s : VG.Arm.State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r9) 0) 32
abbrev keyHi (s : VG.Arm.State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r9) 1) 32

/-- The round key: the low 16 bits of its high word, and its low word. -/
abbrev key48 (s : VG.Arm.State) : BitVec 48 := (VG.Proof.CmacTripleDes.Arm.keyHi s).setWidth 16 ++ VG.Proof.CmacTripleDes.Arm.keyLo s

/-! ## The inputs -/

/-- Bit `b` of the round key, as an atom: of its low word (input word 1) or
its high word (input word 2). -/
def keyAtom (b : Nat) : Nat := if b < 32 then 32 + b else 64 + (b - 32)

/-- Bit `p` of slot `t` (half `t / 6`, input bit `t % 6`): in lane `p / 6`,
below its fifth bit, `R`'s bit (atom `0 … 31`) XOR the key's. -/
def inG (t p : Nat) : List Nat :=
  if p < 24 ∧ p % 6 < 4 then
    [expSrc (24 * (t / 6) + 6 * (p / 6) + t % 6), VG.Proof.CmacTripleDes.Arm.keyAtom (24 * (t / 6) + 6 * (p / 6) + t % 6)]
  else []

def inPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 12).all fun t => e.slot t == some (outWord (VG.Proof.CmacTripleDes.Arm.inG t))

theorem inputs_check :
    VG.Arm.Straight.check (lanes 32 7) VG.Proof.CmacTripleDes.Arm.rCfg (linExt 1) inputs (linEnv [(.r8, 0)]) VG.Proof.CmacTripleDes.Arm.inPost = true := by
  lit_decide

theorem inG_lt : ∀ t < 12, ∀ p < 32, ∀ a ∈ VG.Proof.CmacTripleDes.Arm.inG t p, a < 2 ^ 7 := by lit_decide

/-- The registers the round keeps. -/
def kept : List Reg := [.r9, .r10, .r11, .r12, .lr]

theorem inputs_kept :
    (.r7 :: .r8 :: VG.Proof.CmacTripleDes.Arm.kept).all (fun r => inputs.all fun i => dstOf i != some r) = true := by
  lit_decide

/-- The inputs of `inputs`: `R` and the round key's words. -/
def inW (s : VG.Arm.State) (i : Nat) : BitVec 32 := if i = 0 then s.gpr .r8 else if i = 1 then VG.Proof.CmacTripleDes.Arm.keyLo s else VG.Proof.CmacTripleDes.Arm.keyHi s

theorem inputs_ok {s : VG.Arm.State} (hok : Ok VG.Proof.CmacTripleDes.Arm.rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 12, ∀ p < 32, (VG.Proof.CmacTripleDes.Arm.slotW s' t).getLsbD p = xorBits (VG.Proof.CmacTripleDes.Arm.inW s) (VG.Proof.CmacTripleDes.Arm.inG t p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ .r7 :: .r8 :: VG.Proof.CmacTripleDes.Arm.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.Arm.inputs_check
  have hrel : Rel (LaneRel 7 (assign (VG.Proof.CmacTripleDes.Arm.inW s) (2 ^ 7))) VG.Proof.CmacTripleDes.Arm.rCfg (linExt 1) (linEnv [(.r8, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_, fun _ _ h => by cases h⟩
    · simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel (VG.Proof.CmacTripleDes.Arm.inW s) (i := 0) (by decide)
      · simp at h
    · simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at hj
      simp only [linExt, Option.some.injEq] at h; subst h
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact inWord_rel (VG.Proof.CmacTripleDes.Arm.inW s) (i := 1) (by decide)
      · exact inWord_rel (VG.Proof.CmacTripleDes.Arm.inW s) (i := 2) (by decide)
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun t ht q hq => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost t (List.mem_range.mpr ht)
    simp only [beq_iff_eq] at h
    exact outWord_rel (VG.Proof.CmacTripleDes.Arm.inG_lt t ht) (p.rel.slot t _ (by simp only [VG.Proof.CmacTripleDes.Arm.rCfg]; omega) h) q hq
  · rw [List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.inputs_kept r hr]; decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t % 6` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 32).testBit (t % 6)) 2048

/-- Half `h`'s slots. -/
def sbEnv (h : Nat) : Env Nat :=
  { reg := fun _ => none, slot := fun t => if 6 * h ≤ t ∧ t < 6 * h + 6 then some (VG.Proof.CmacTripleDes.Arm.rowIn t) else none }

theorem sboxes_eq : sboxes = VG.Proof.CmacTripleDes.Arm.sbCode 0 ++ ([.str .r0 .r10 48] : List Instr) ++ VG.Proof.CmacTripleDes.Arm.sbCode 1 := rfl

/-- At bit `6 j + off i b` (`i` the box in lane `j` of half `h`), output bit
`b` of box `i`, on every row. -/
def sbPost (h : Nat) (e : Env Nat) : Bool :=
  match e.reg .r0 with
  | some F => (List.range 4).all fun j => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) ==
        (Proof.TripleDes.outputTable (boxOf h j) b).testBit c
  | none => false

/-- The slots half `h` reads: the broadcast inputs up to its own. -/
def sCfg (h : Nat) : Cfg := { base := .r10, slots := 6 * h + 6, ext := .r9, exts := 0 }

theorem sbox0_check : VG.Arm.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.Arm.sCfg 0) (fun _ => none) (VG.Proof.CmacTripleDes.Arm.sbCode 0) (VG.Proof.CmacTripleDes.Arm.sbEnv 0) (VG.Proof.CmacTripleDes.Arm.sbPost 0) = true := by
  lit_decide

theorem sbox1_check : VG.Arm.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.Arm.sCfg 1) (fun _ => none) (VG.Proof.CmacTripleDes.Arm.sbCode 1) (VG.Proof.CmacTripleDes.Arm.sbEnv 1) (VG.Proof.CmacTripleDes.Arm.sbPost 1) = true := by
  lit_decide

theorem sbox_kept (h : Nat) (hh : h < 2) :
    (.r7 :: .r8 :: VG.Proof.CmacTripleDes.Arm.kept).all (fun r => (VG.Proof.CmacTripleDes.Arm.sbCode h).all fun i => dstOf i != some r) = true := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> lit_decide

/-- The input of the box whose lane of half `h` holds bit `p`, from bit `p`
of the slots. -/
def boxIn (h : Nat) (s : VG.Arm.State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (VG.Proof.CmacTripleDes.Arm.slotW s (6 * h + t)).getLsbD p

theorem off_lt4 : ∀ h < 2, ∀ j < 4, ∀ b < 4, off (boxOf h j) b < 4 := by decide

theorem sbox_ok {h : Nat} (hh : h < 2) {s : VG.Arm.State} (hok : Ok (VG.Proof.CmacTripleDes.Arm.sCfg h) s) :
    ∃ s', runBlock isa (VG.Proof.CmacTripleDes.Arm.sbCode h) s = some s' ∧
      (∀ j < 4, ∀ b < 4, (s'.gpr .r0).getLsbD (6 * j + off (boxOf h j) b) =
        (Spec.TripleDes.sBox (boxOf h j) (VG.Proof.CmacTripleDes.Arm.boxIn h s (6 * j + off (boxOf h j) b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ .r7 :: .r8 :: VG.Proof.CmacTripleDes.Arm.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion (VG.Proof.CmacTripleDes.Arm.sCfg h) s] s.mem s'.mem := by
  have hchk : VG.Arm.Straight.check (rows 32 6) (VG.Proof.CmacTripleDes.Arm.sCfg h) (fun _ => none) (VG.Proof.CmacTripleDes.Arm.sbCode h) (VG.Proof.CmacTripleDes.Arm.sbEnv h) (VG.Proof.CmacTripleDes.Arm.sbPost h) = true := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact VG.Proof.CmacTripleDes.Arm.sbox0_check
    · exact VG.Proof.CmacTripleDes.Arm.sbox1_check
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .r0 = some F ∧ ∀ j < 4, ∀ b < 4, ∀ c < 64,
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) =
        (Spec.TripleDes.sBox (boxOf h j) (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [VG.Proof.CmacTripleDes.Arm.sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun j hj b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost j
        (List.mem_range.mpr hj)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  have key : ∀ p < 32, ∃ s', runBlock isa (VG.Proof.CmacTripleDes.Arm.sbCode h) s = some s' ∧
      VG.Arm.Straight.Post (RowRel p (VG.Proof.CmacTripleDes.Arm.boxIn h s p).toNat) (VG.Proof.CmacTripleDes.Arm.sCfg h) (fun _ => none) e' s s'
        (fun r => ((VG.Proof.CmacTripleDes.Arm.sbCode h).all fun i => dstOf i != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (VG.Proof.CmacTripleDes.Arm.boxIn h s p).isLt) hok
      ⟨fun r a h => by simp [VG.Proof.CmacTripleDes.Arm.sbEnv] at h, fun t a ht h' => ?_, (fun _ _ _ h => by cases h),
        fun _ _ h => by cases h⟩ he
    simp only [VG.Proof.CmacTripleDes.Arm.sbEnv] at h'
    split at h'
    · rename_i ht6
      cases h'
      show (VG.Proof.CmacTripleDes.Arm.rowIn t).testBit (32 * (VG.Proof.CmacTripleDes.Arm.boxIn h s p).toNat + p) = (VG.Proof.CmacTripleDes.Arm.slotW s t).getLsbD p
      have hc := (VG.Proof.CmacTripleDes.Arm.boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 6 * h + u ∧ u < 6 := ⟨t - 6 * h, by omega, by omega⟩
      rw [VG.Proof.CmacTripleDes.Arm.rowIn, testBit_tableOf, decide_eq_true (by omega : 32 * (boxIn h s p).toNat + p < 2048),
        Bool.true_and, show (32 * (VG.Proof.CmacTripleDes.Arm.boxIn h s p).toNat + p) / 32 = (VG.Proof.CmacTripleDes.Arm.boxIn h s p).toNat by omega,
        BitVec.testBit_toNat, VG.Proof.CmacTripleDes.Arm.boxIn, getLsbD_ofBits, show (6 * h + u) % 6 = u by omega,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hp : 6 * j + off (boxOf h j) b < 32 := by have := VG.Proof.CmacTripleDes.Arm.off_lt4 h hh j hj b hb; omega
    obtain ⟨s'', hs'', p₁⟩ := key _ hp
    obtain rfl := run_unique hs'' hs'
    have h' := p₁.rel.reg .r0 F hF
    simp only [RowRel] at h'
    rw [← h', hout j hj b hb _ (VG.Proof.CmacTripleDes.Arm.boxIn h s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.all_eq_true.mp (VG.Proof.CmacTripleDes.Arm.sbox_kept h hh) r hr]; decide

/-! ## The output -/

/-- The atom of output bit `u` of the S-boxes: bit `outPos u` of half 1's
outputs (`r0`, input word 0) or of half 0's (slot 12, input word 3). -/
def sAtom (u : Nat) : Nat := if outHalf u = 0 then 96 + outPos u else outPos u

/-- `r7`: `R` (input word 2). -/
def oG7 (p : Nat) : List Nat := [64 + p]

/-- `r8`: bit `j` of `L` (input word 1) XOR the S-boxes' bit `pSrc j`. -/
def oG8 (p : Nat) : List Nat := if p < 32 then [VG.Proof.CmacTripleDes.Arm.sAtom (pSrc p), 32 + p] else [32 + p]

def oEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .r0 then some (inWord 0) else if r = .r7 then some (inWord 1)
      else if r = .r8 then some (inWord 2) else none,
    slot := fun k => if k = 12 then some (inWord 3) else none }

def oPost (e : Env (Nat × Nat)) : Bool :=
  e.reg .r7 == some (outWord VG.Proof.CmacTripleDes.Arm.oG7) && e.reg .r8 == some (outWord VG.Proof.CmacTripleDes.Arm.oG8)

/-- The slots of the output: half 0's outputs, in slot 12. -/
def oCfg : Cfg := { base := .r10, slots := 13, ext := .r9, exts := 0 }

theorem output_check : VG.Arm.Straight.check (lanes 32 7) VG.Proof.CmacTripleDes.Arm.oCfg (fun _ => none) output VG.Proof.CmacTripleDes.Arm.oEnv VG.Proof.CmacTripleDes.Arm.oPost = true := by
  lit_decide

theorem oG_lt : ∀ p < 32, (∀ a ∈ VG.Proof.CmacTripleDes.Arm.oG7 p, a < 2 ^ 7) ∧ ∀ a ∈ VG.Proof.CmacTripleDes.Arm.oG8 p, a < 2 ^ 7 := by lit_decide

theorem output_kept : kept.all (fun r => output.all fun i => dstOf i != some r) = true := by
  lit_decide

/-- The inputs of `output`. -/
def oW (s : VG.Arm.State) (i : Nat) : BitVec 32 :=
  if i = 0 then s.gpr .r0 else if i = 1 then s.gpr .r7 else if i = 2 then s.gpr .r8 else VG.Proof.CmacTripleDes.Arm.slotW s 12

theorem output_ok {s : VG.Arm.State} (hok : Ok VG.Proof.CmacTripleDes.Arm.oCfg s) :
    ∃ s', runBlock isa output s = some s' ∧
      (∀ p < 32, (s'.gpr .r7).getLsbD p = xorBits (VG.Proof.CmacTripleDes.Arm.oW s) (VG.Proof.CmacTripleDes.Arm.oG7 p)) ∧
      (∀ p < 32, (s'.gpr .r8).getLsbD p = xorBits (VG.Proof.CmacTripleDes.Arm.oW s) (VG.Proof.CmacTripleDes.Arm.oG8 p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.CmacTripleDes.Arm.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.Arm.oCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.Arm.output_check
  have hrel : Rel (LaneRel 7 (assign (VG.Proof.CmacTripleDes.Arm.oW s) (2 ^ 7))) VG.Proof.CmacTripleDes.Arm.oCfg (fun _ => none) VG.Proof.CmacTripleDes.Arm.oEnv s := by
    refine ⟨fun r a h => ?_, fun k a hk h => ?_, (fun _ _ _ h => by cases h), fun _ _ h => by cases h⟩
    · simp only [VG.Proof.CmacTripleDes.Arm.oEnv] at h
      split at h
      · rename_i hr; subst hr; cases h; exact inWord_rel (VG.Proof.CmacTripleDes.Arm.oW s) (i := 0) (by decide)
      · split at h
        · rename_i _ hr; subst hr; cases h; exact inWord_rel (VG.Proof.CmacTripleDes.Arm.oW s) (i := 1) (by decide)
        · split at h
          · rename_i _ _ hr; subst hr; cases h; exact inWord_rel (VG.Proof.CmacTripleDes.Arm.oW s) (i := 2) (by decide)
          · cases h
    · simp only [VG.Proof.CmacTripleDes.Arm.oEnv] at h
      split at h
      · rename_i hk; subst hk; cases h; exact inWord_rel (VG.Proof.CmacTripleDes.Arm.oW s) (i := 3) (by decide)
      · cases h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [VG.Proof.CmacTripleDes.Arm.oPost, Bool.and_eq_true, beq_iff_eq] at hpost
  refine ⟨s', hs', fun q hq => ?_, fun q hq => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · exact outWord_rel (fun p hp => (VG.Proof.CmacTripleDes.Arm.oG_lt p hp).1) (p.rel.reg .r7 _ hpost.1) q hq
  · exact outWord_rel (fun p hp => (VG.Proof.CmacTripleDes.Arm.oG_lt p hp).2) (p.rel.reg .r8 _ hpost.2) q hq
  · rw [List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.output_kept r hr]; decide

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : VG.Arm.State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem wordAddr_eq (b : BitVec 32) {k : Nat} (h : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add h

/-- Word `k` of the slots is outside a frame on the first `n` words. -/
theorem slot_frame {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨State.addr b, 4 * n⟩] m m')
    (hk : n ≤ k) (hb : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [VG.Proof.CmacTripleDes.Arm.wordAddr_eq b (by omega)]
  refine hf.readW (r := ⟨State.addr b + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega) (by omega)

/-- Words `j` and `k` of the slots are apart. -/
theorem slot_word_sep (b : BitVec 32) {j k : Nat} (h : j ≠ k) (hj : b.toNat + 4 * j + 4 ≤ 2 ^ 32)
    (hk : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : Mem.Sep (wordAddr b j) (32 / 8) (wordAddr b k) (32 / 8) := by
  rw [VG.Proof.CmacTripleDes.Arm.wordAddr_eq b (by omega), VG.Proof.CmacTripleDes.Arm.wordAddr_eq b (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : VG.Arm.State}
    (hx : ∀ t < 12, ∀ p < 32, (VG.Proof.CmacTripleDes.Arm.slotW s₁ t).getLsbD p = xorBits (VG.Proof.CmacTripleDes.Arm.inW s) (VG.Proof.CmacTripleDes.Arm.inG t p))
    {h j o : Nat} (hh : h < 2) (hj : j < 4) (ho : o < 4) :
    VG.Proof.CmacTripleDes.Arm.boxIn h s₁ (6 * j + o) = chunk (s.gpr .r8) (VG.Proof.CmacTripleDes.Arm.key48 s) (boxOf h j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega
  have hE := VG.Proof.CmacTripleDes.Arm.expSrc_lt (24 * h + 6 * j + t) (by omega)
  rw [VG.Proof.CmacTripleDes.Arm.boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, hx (6 * h + t) (by omega) _ (by omega),
    getLsbD_chunk _ _ (by simp only [boxOf]; omega) ht, VG.Proof.CmacTripleDes.Arm.inG, ite_eq_left (by omega), hb,
    show (6 * h + t) / 6 = h by omega, show (6 * h + t) % 6 = t by omega, show (6 * j + o) / 6 = j by omega]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.Arm.inW, VG.Proof.CmacTripleDes.Arm.keyAtom]
  rw [Nat.div_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega),
    Nat.mod_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega), ite_eq_left rfl]
  congr 1
  rw [BitVec.getLsbD_append]
  by_cases h32 : 24 * h + 6 * j + t < 32
  · rw [ite_eq_left h32, ite_eq_left h32, show (32 + (24 * h + 6 * j + t)) / 32 = 1 by omega,
      show (32 + (24 * h + 6 * j + t)) % 32 = 24 * h + 6 * j + t by omega]
    rfl
  · rw [ite_eq_right h32, ite_eq_right h32, show (64 + (24 * h + 6 * j + t - 32)) / 32 = 2 by omega,
      show (64 + (24 * h + 6 * j + t - 32)) % 32 = 24 * h + 6 * j + t - 32 by omega,
      BitVec.getLsbD_setWidth, decide_eq_true (by omega : 24 * h + 6 * j + t - 32 < 16), Bool.true_and]
    rfl

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

theorem rCfg_s0 {s : VG.Arm.State} (hok : Ok VG.Proof.CmacTripleDes.Arm.rCfg s) : Ok (VG.Proof.CmacTripleDes.Arm.sCfg 0) s :=
  ⟨fun k hk => hok.slotIn k (by simp only [VG.Proof.CmacTripleDes.Arm.sCfg, VG.Proof.CmacTripleDes.Arm.rCfg] at hk ⊢; omega), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.sCfg]),
    by have := hok.slots; simp only [VG.Proof.CmacTripleDes.Arm.sCfg, VG.Proof.CmacTripleDes.Arm.rCfg] at this ⊢; omega, fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.sCfg])⟩

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on `r7` and `r8`, with the round
key at `r9`. -/
theorem round_ok {s : VG.Arm.State} (hok : Ok VG.Proof.CmacTripleDes.Arm.rCfg s) :
    ∃ s', runBlock isa VG.Impl.CmacTripleDes.Arm.round s = some s' ∧
      s'.gpr .r7 = s.gpr .r8 ∧
      s'.gpr .r8 = s.gpr .r7 ^^^ Spec.TripleDes.roundFunction (s.gpr .r8) (VG.Proof.CmacTripleDes.Arm.key48 s) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ VG.Proof.CmacTripleDes.Arm.kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s] s.mem s'.mem := by
  have hsl := hok.slots
  simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at hsl
  have hb10 : ∀ k ≤ 12, (s.gpr .r10).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by
    have := hok.slots; simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at this; omega
  obtain ⟨s₁, h₁, hx, rd₁, wr₁, sp₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.Arm.inputs_ok hok
  have r10₁ : s₁.gpr .r10 = s.gpr .r10 := k₁ .r10 (by simp [VG.Proof.CmacTripleDes.Arm.kept])
  have hok₁ : Ok VG.Proof.CmacTripleDes.Arm.rCfg s₁ := hok.congr r10₁ (k₁ .r9 (by simp [VG.Proof.CmacTripleDes.Arm.kept])) rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, sp₂, k₂, f₂⟩ := VG.Proof.CmacTripleDes.Arm.sbox_ok (h := 0) (by decide) (VG.Proof.CmacTripleDes.Arm.rCfg_s0 hok₁)
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := (k₂ .r10 (by simp [VG.Proof.CmacTripleDes.Arm.kept])).trans r10₁
  -- The store of half 0's outputs.
  have w48 : InRegions s₂.wr (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) 4 := by
    rw [wr₂, r10₂, ← r10₁]; exact hok₁.slotIn 12 (by decide)
  let s₃ : VG.Arm.State := { s₂ with
                              mem := s₂.mem.writeW (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) (s₂.gpr .r0) }
  have h₃ : runBlock isa [.str .r0 .r10 48] s₂ = some s₃ := by
    rw [runBlock_cons, exec_str (by decide) w48, runStep_some, runBlock_nil]
  have hok₃ : Ok (VG.Proof.CmacTripleDes.Arm.sCfg 1) s₃ :=
    ⟨fun k hk => by
      show InRegions s₂.wr _ 4
      rw [wr₂, show s₃.gpr (VG.Proof.CmacTripleDes.Arm.sCfg 1).base = s₁.gpr .r10 from r10₂.trans r10₁.symm]
      exact hok₁.slotIn k (by simp only [VG.Proof.CmacTripleDes.Arm.sCfg, VG.Proof.CmacTripleDes.Arm.rCfg] at hk ⊢; omega),
     fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.sCfg]),
     by show (s₂.gpr .r10).toNat + 4 * 12 ≤ 2 ^ 32; rw [r10₂]; omega,
     fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.sCfg])⟩
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, sp₄, k₄, f₄⟩ := VG.Proof.CmacTripleDes.Arm.sbox_ok (h := 1) (by decide) hok₃
  have r10₄ : s₄.gpr .r10 = s.gpr .r10 := (k₄ .r10 (by simp [VG.Proof.CmacTripleDes.Arm.kept])).trans r10₂
  have hok₄ : Ok VG.Proof.CmacTripleDes.Arm.oCfg s₄ :=
    ⟨fun k hk => by
      rw [wr₄]; show InRegions s₂.wr _ 4
      rw [wr₂, show s₄.gpr oCfg.base = s₁.gpr .r10 from r10₄.trans r10₁.symm]
      exact hok₁.slotIn k (by simp only [VG.Proof.CmacTripleDes.Arm.oCfg, VG.Proof.CmacTripleDes.Arm.rCfg] at hk ⊢; omega),
     fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.oCfg]),
     by show (s₄.gpr .r10).toNat + 4 * 13 ≤ 2 ^ 32; rw [r10₄]; omega,
     fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.oCfg])⟩
  obtain ⟨s₅, h₅, o7, o8, rd₅, wr₅, sp₅, k₅, f₅⟩ := VG.Proof.CmacTripleDes.Arm.output_ok hok₄
  -- The slots through the S-boxes.
  have slot₃ : ∀ k, 6 ≤ k → k < 12 → VG.Proof.CmacTripleDes.Arm.slotW s₃ k = VG.Proof.CmacTripleDes.Arm.slotW s₁ k := fun k hk₁ hk₂ => by
    show (s₂.mem.writeW _ _).readW (wordAddr (s₂.gpr .r10) k) 32 = _
    rw [Mem.readW_writeW_sep (by
        rw [r10₂]
        have := VG.Proof.CmacTripleDes.Arm.slot_word_sep (s.gpr .r10) (j := k) (k := 12) (by omega) (hb10 k (by omega)) (hb10 12 (by decide))
        rwa [wordAddr] at this) (by decide), r10₂, ← r10₁]
    have := VG.Proof.CmacTripleDes.Arm.slot_frame (n := 6) (k := k) (b := s₁.gpr .r10) f₂ hk₁ (by rw [r10₁]; exact hb10 k (by omega))
    exact this
  have slot12 : VG.Proof.CmacTripleDes.Arm.slotW s₄ 12 = s₂.gpr .r0 := by
    show s₄.mem.readW (wordAddr (s₄.gpr .r10) 12) 32 = _
    rw [r10₄, ← r10₂]
    have := VG.Proof.CmacTripleDes.Arm.slot_frame (n := 12) (k := 12) (b := s₃.gpr .r10) f₄ (by decide) (by rw [r10₂]; exact hb10 12 (by decide))
    rw [show s₃.gpr .r10 = s₂.gpr .r10 from rfl] at this
    rw [this]
    exact Mem.readW_writeW_self32 _ _ _
  have box₄ : ∀ p, VG.Proof.CmacTripleDes.Arm.boxIn 1 s₃ p = VG.Proof.CmacTripleDes.Arm.boxIn 1 s₁ p := fun p => by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [VG.Proof.CmacTripleDes.Arm.boxIn, VG.Proof.CmacTripleDes.Arm.boxIn, getLsbD_ofBits, getLsbD_ofBits, slot₃ (6 * 1 + t) (by omega) (by omega)]
  have r0₄ : s₄.gpr .r7 = s.gpr .r7 ∧ s₄.gpr .r8 = s.gpr .r8 := by
    refine ⟨?_, ?_⟩
    · rw [k₄ .r7 (by simp), show s₃.gpr .r7 = s₂.gpr .r7 from rfl, k₂ .r7 (by simp), k₁ .r7 (by simp)]
    · rw [k₄ .r8 (by simp), show s₃.gpr .r8 = s₂.gpr .r8 from rfl, k₂ .r8 (by simp), k₁ .r8 (by simp)]
  refine ⟨s₅, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [VG.Impl.CmacTripleDes.Arm.round, VG.Proof.CmacTripleDes.Arm.sboxes_eq, VG.Proof.CmacTripleDes.Arm.runBlock_append, VG.Proof.CmacTripleDes.Arm.runBlock_append, h₁, Option.bind_some, VG.Proof.CmacTripleDes.Arm.runBlock_append,
      VG.Proof.CmacTripleDes.Arm.runBlock_append, h₂, Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [o7 p hp, VG.Proof.CmacTripleDes.Arm.oG7]
    simp (config := {decide := true}) only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, VG.Proof.CmacTripleDes.Arm.oW,
      show (64 + p) / 32 = 2 by omega, show (64 + p) % 32 = p by omega, ite_true, ite_false]
    rw [r0₄.2]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := VG.Proof.CmacTripleDes.Arm.pSrc_lt j hj
    rw [o8 j hj, VG.Proof.CmacTripleDes.Arm.oG8, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    have hL : bitOf (VG.Proof.CmacTripleDes.Arm.oW s₄) (32 + j) = (s.gpr .r7).getLsbD j := by
      simp (config := {decide := true}) only [bitOf, VG.Proof.CmacTripleDes.Arm.oW, show (32 + j) / 32 = 1 by omega,
        show (32 + j) % 32 = j by omega, ite_true, ite_false]
      rw [r0₄.1]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb, hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 12.
      have hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      have ho := VG.Proof.CmacTripleDes.Arm.off_lt4 0 (by decide) _ hh b hb
      have hpos : VG.Proof.CmacTripleDes.Arm.sAtom (pSrc j) = 96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [VG.Proof.CmacTripleDes.Arm.sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      have hbit : bitOf (VG.Proof.CmacTripleDes.Arm.oW s₄) (VG.Proof.CmacTripleDes.Arm.sAtom (pSrc j)) =
          (VG.Proof.CmacTripleDes.Arm.slotW s₄ 12).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, VG.Proof.CmacTripleDes.Arm.oW,
          show (96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b)) / 32 = 3 by omega,
          show (96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b)) % 32 =
            6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b by omega, ite_false]
      rw [hbit, slot12, y₂ _ hh b hb, VG.Proof.CmacTripleDes.Arm.boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in `r0`.
      have hh8 : pSrc j / 4 < 8 := by omega
      have hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      have hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega
      have ho := VG.Proof.CmacTripleDes.Arm.off_lt4 1 (by decide) _ hm b hb
      have hpos : VG.Proof.CmacTripleDes.Arm.sAtom (pSrc j) = 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b := by
        rw [VG.Proof.CmacTripleDes.Arm.sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      have hbit : bitOf (VG.Proof.CmacTripleDes.Arm.oW s₄) (VG.Proof.CmacTripleDes.Arm.sAtom (pSrc j)) =
          (s₄.gpr .r0).getLsbD (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, VG.Proof.CmacTripleDes.Arm.oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b < 32 by omega),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b < 32 by omega),
          ite_true]
      rw [hbit, y₄ _ hm b hb, box₄, VG.Proof.CmacTripleDes.Arm.boxIn_eq hx (by decide) hm ho, hi]
      simp only [hbe]
  · rw [rd₅, rd₄]; exact rd₂.trans rd₁
  · rw [wr₅, wr₄]; exact wr₂.trans wr₁
  · rw [sp₅, sp₄]; exact sp₂.trans sp₁
  · rw [k₅ r hr, k₄ r (by simp [hr]), show s₃.gpr r = s₂.gpr r from rfl, k₂ r (by simp [hr]),
      k₁ r (by simp [hr])]
  · have R : ∀ (c : Cfg) (t : VG.Arm.State), c.base = .r10 → c.slots ≤ 13 → t.gpr .r10 = s.gpr .r10 →
        ∀ r ∈ [slotRegion c t], ∃ r' ∈ [slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s], Region.Sub r r' := fun c t hc hn ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [slotRegion, hc, ht]
      exact Region.sub_prefix (by simp only [VG.Proof.CmacTripleDes.Arm.rCfg]; omega)
    have c12 : (slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s).Contains (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) (32 / 8) := by
      rw [r10₂, show (48 : Nat) = 4 * 12 from rfl, ← wordAddr, VG.Proof.CmacTripleDes.Arm.wordAddr_eq _ (by omega)]
      exact Offset.contains_base _ (by simp only [VG.Proof.CmacTripleDes.Arm.rCfg]; omega) (by omega)
    have f₃ : Frame [slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s] s₂.mem s₃.mem :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c12
    exact (((f₁.trans (f₂.sub (R _ _ rfl (by decide) r10₁))).trans f₃).trans
      (f₄.sub (R _ _ rfl (by decide) r10₂))).trans (f₅.sub (R _ _ rfl (by decide) r10₄))

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Block`. -/
section

/-!
# TDEA on 32-bit ARM: the passes and the block

Untrusted: everything here is checked by Lean.

As on AArch64 (`Proof/CmacTripleDes/AArch64/Block.lean`): `block` encrypts
the 64-bit block in `r0:r1` with the key schedule at `r9` (`block_ok`): `IP`
into `r7` and `r8`, three passes of sixteen rounds (`pass_ok`, the round
keys `lr` bytes apart, the halves exchanged after each pass), and `IP⁻¹`.
During the block, `r9` points to slot `kpos p j` of the key schedule before
round `j` of pass `p`. The block uses every register but `r10`.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes
  VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `r9` readable, and the words
0–12 of the scratch buffer at `r10` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ len, (⟨State.addr (s.gpr .r9), len⟩ : Region) ∈ s.rd ++ s.wr ∧ 384 ≤ len ∧
    (s.gpr .r9).toNat + len ≤ 2 ^ 32
  scr : ∃ len, (⟨State.addr (s.gpr .r10), len⟩ : Region) ∈ s.wr ∧ 52 ≤ len ∧
    (s.gpr .r10).toNat + len ≤ 2 ^ 32
  disj : Region.Disjoint ⟨State.addr (s.gpr .r10), 52⟩ ⟨State.addr (s.gpr .r9), 384⟩

/-- The block's words of the scratch buffer. -/
abbrev xR (s₀ : State) : Region := ⟨State.addr (s₀.gpr .r10), 52⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = s₀.gpr .r10
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.Arm.xR s₀] s₀.mem s.mem

theorem Same.refl (s : State) : VG.Proof.CmacTripleDes.Arm.Same s s := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem (State.addr (s₀.gpr .r9))

theorem ok_at {s₀ s : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) (h : VG.Proof.CmacTripleDes.Arm.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) : Ok VG.Proof.CmacTripleDes.Arm.rCfg s := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, fun k hk' j hj => ?_⟩
  · simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at hk'
    rw [h.wr, show rCfg.base = .r10 from rfl, h.r10]
    exact in_off hX hXw (by omega) (by omega)
  · simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at hk'
    rw [h.rd, h.wr, show rCfg.ext = .r9 from rfl, hk, wordAddr, add_ofNat_ofNat]
    exact in_off hR hRw (by omega) (by omega)
  · show (s.gpr .r10).toNat + 4 * 13 ≤ 2 ^ 32
    rw [h.r10]; omega
  · simp only [VG.Proof.CmacTripleDes.Arm.rCfg] at hk' hj
    rw [show rCfg.base = .r10 from rfl, show rCfg.ext = .r9 from rfl, h.r10, hk, wordAddr, wordAddr,
      add_ofNat_ofNat]
    exact hp.disj.sep (contains_off (len := 52) (by omega) (by omega) (by omega))
      (contains_off (len := 384) (by omega) (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) (h : VG.Proof.CmacTripleDes.Arm.Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) : VG.Proof.CmacTripleDes.Arm.key48 s = ((VG.Proof.CmacTripleDes.Arm.sch s₀).getD n 0).setWidth 48 := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  have hW := (s₀.gpr .r9).isLt
  rw [scheduleAt_getD _ _ hn, setWidth48_readW]
  have rd : ∀ d, d + 4 ≤ 384 → s.mem.readW (State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d)) 32 =
      s₀.mem.readW (State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d)) 32 := fun d hd =>
    h.frame.readW (r := ⟨State.addr (s₀.gpr .r9 + BitVec.ofNat 32 d), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine (hp.disj.symm.sub_left ?_)
        rw [addr_add (by omega)]
        exact Offset.sub_base _ (by omega)) (by decide)
  have e0 : wordAddr (s.gpr .r9) 0 = State.addr (s₀.gpr .r9 + BitVec.ofNat 32 (8 * n)) := by
    rw [wordAddr, hk, add_ofNat_ofNat, show 8 * n + 4 * 0 = 8 * n by omega]
  have e1 : wordAddr (s.gpr .r9) 1 = State.addr (s₀.gpr .r9 + BitVec.ofNat 32 (8 * n + 4)) := by
    rw [wordAddr, hk, add_ofNat_ofNat]
  rw [VG.Proof.CmacTripleDes.Arm.key48, VG.Proof.CmacTripleDes.Arm.keyLo, VG.Proof.CmacTripleDes.Arm.keyHi, e0, e1, rd _ (by omega), rd _ (by omega), addr_add (by omega), addr_add (by omega),
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The rounds of a pass -/

theorem roundTail_ok (s : State) :
    ∃ s', runBlock isa roundTail s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 + s.gpr .lr ∧ s'.gpr .r11 = s.gpr .r11 - 1 ∧ s'.z = (s.gpr .r11 - 1 == 0) ∧
      (∀ r, r ≠ .r9 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [roundTail, runBlock_cons, runStep_some, exec,
      Op2.eval, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags, h₁, h₂]

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 32 := if p % 2 = 1 then BitVec.ofNat 32 (2 ^ 32 - 8) else BitVec.ofNat 32 8

theorem kpos_succ_addr (a : BitVec 32) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p j) + VG.Proof.CmacTripleDes.Arm.stride p = a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p (j + 1)) := by
  rw [BitVec.add_assoc, VG.Proof.CmacTripleDes.Arm.stride, VG.Proof.CmacTripleDes.Arm.kpos, VG.Proof.CmacTripleDes.Arm.kpos]
  congr 1
  split
  · rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : VG.Proof.CmacTripleDes.Arm.Same s₀ s
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p j)
  str : s.gpr .lr = VG.Proof.CmacTripleDes.Arm.stride p
  r12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (16 - j)
  halves : (s.gpr .r7, s.gpr .r8) = VG.Proof.CmacTripleDes.rounds (passKeys (VG.Proof.CmacTripleDes.Arm.sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : VG.Proof.CmacTripleDes.Arm.kpos p j < 48 := by
  simp only [VG.Proof.CmacTripleDes.Arm.kpos]; split <;> omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (VG.Proof.CmacTripleDes.Arm.sch s₀) p j = ((VG.Proof.CmacTripleDes.Arm.sch s₀).getD (VG.Proof.CmacTripleDes.Arm.kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, VG.Proof.CmacTripleDes.Arm.kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr j s) :
    WP isa (.block (VG.Impl.CmacTripleDes.Arm.round ++ roundTail)) s fun s' => s'.z = decide (j + 1 = 16) ∧ VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, e7, e8, rd₁, wr₁, sp₁, k₁, f₁⟩ := VG.Proof.CmacTripleDes.Arm.round_ok (VG.Proof.CmacTripleDes.Arm.ok_at hp h.same (VG.Proof.CmacTripleDes.Arm.kpos_lt hp3 hj) h.r9)
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ?_⟩
  obtain ⟨s₂, h₂, t9, t11, tz, tk, tsp, tm, trd, twr⟩ := VG.Proof.CmacTripleDes.Arm.roundTail_ok s₁
  have kk : ∀ r ∈ VG.Proof.CmacTripleDes.Arm.kept, s₁.gpr r = s.gpr r := k₁
  refine ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tz, kk .r11 (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.r11, VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega), VG.Proof.CmacTripleDes.Arm.ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r10 (by decide) (by decide), kk .r10 (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.same.r10]
  · rw [tsp, sp₁, h.same.sp]
  · rw [trd, rd₁, h.same.rd]
  · rw [twr, wr₁, h.same.wr]
  · rw [tm]
    have hr : slotRegion VG.Proof.CmacTripleDes.Arm.rCfg s = VG.Proof.CmacTripleDes.Arm.xR s₀ := by
      simp only [slotRegion, VG.Proof.CmacTripleDes.Arm.xR]; rw [show rCfg.base = .r10 from rfl, h.same.r10]; rfl
    rw [hr] at f₁
    exact h.same.frame.trans f₁
  · rw [t9, kk .r9 (by simp [VG.Proof.CmacTripleDes.Arm.kept]), kk .lr (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.r9, h.str, VG.Proof.CmacTripleDes.Arm.kpos_succ_addr _ hp3 hj]
  · rw [tk .lr (by decide) (by decide), kk .lr (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.str]
  · rw [tk .r12 (by decide) (by decide), kk .r12 (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.r12]
  · rw [t11, kk .r11 (by simp [VG.Proof.CmacTripleDes.Arm.kept]), h.r11, VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [rounds_succ, ← h.halves, tk .r7 (by decide) (by decide), tk .r8 (by decide) (by decide), e7, e8,
      VG.Proof.CmacTripleDes.Arm.key_at hp h.same (VG.Proof.CmacTripleDes.Arm.kpos_lt hp3 hj) h.r9, VG.Proof.CmacTripleDes.Arm.passKeys_at s₀ hj]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : VG.Proof.CmacTripleDes.Arm.Same s₀ s) (h9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p 0))
    (hlr : s.gpr .lr = VG.Proof.CmacTripleDes.Arm.stride p) (h12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p))
    (hh : (s.gpr .r7, s.gpr .r8) = lr) :
    WP isa pass s (VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr 16) := by
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, exec, Op2.eval,
      ]
    rfl, ?_⟩)
  have g : ∀ r, r ≠ .r11 → (s.setReg .r11 16).gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne _ _ hr
  have hI : VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr 0 (s.setReg .r11 16) :=
    ⟨⟨by rw [g _ (by decide), h.r10], h.sp, h.rd, h.wr, h.frame⟩, by rw [g _ (by decide), h9],
      by rw [g _ (by decide), hlr], by rw [g _ (by decide), h12], by rw [gpr_setReg_self]; rfl,
      by rw [g _ (by decide), g _ (by decide), hh]; rfl⟩
  refine WP.loop (M := isa) (body := .block (VG.Impl.CmacTripleDes.Arm.round ++ roundTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ VG.Proof.CmacTripleDes.Arm.PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.roundStep_ok hp hp3 hj ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

theorem passTail_ok (s : State) :
    ∃ s', runBlock isa passTail s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 + (128 - s.gpr .lr) ∧ s'.gpr .lr = 0 - s.gpr .lr ∧
      s'.gpr .r7 = s.gpr .r8 ∧ s'.gpr .r8 = s.gpr .r7 ∧ s'.gpr .r12 = s.gpr .r12 - 1 ∧
      s'.z = (s.gpr .r12 - 1 == 0) ∧
      (∀ r, r ∉ [Reg.r0, .r7, .r8, .r9, .r12, .lr] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [passTail, mov, runBlock_cons, exec,
      Op2.eval]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp [State.setReg, subFlags]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, subFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : VG.Proof.CmacTripleDes.Arm.Same s₀ s
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p 0)
  str : s.gpr .lr = VG.Proof.CmacTripleDes.Arm.stride p
  r12 : s.gpr .r12 = BitVec.ofNat 32 (3 - p)
  halves : (s.gpr .r7, s.gpr .r8) = passes (VG.Proof.CmacTripleDes.Arm.sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : BitVec 32) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos p 16) + (128 - VG.Proof.CmacTripleDes.Arm.stride p) = a + BitVec.ofNat 32 (8 * VG.Proof.CmacTripleDes.Arm.kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - VG.Proof.CmacTripleDes.Arm.stride p = VG.Proof.CmacTripleDes.Arm.stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : VG.Proof.CmacTripleDes.Arm.OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' => s'.z = decide (p + 1 = 3) ∧ VG.Proof.CmacTripleDes.Arm.OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.pass_ok hp hp3 h.same h.r9 h.str h.r12 h.halves) fun s₁ h₁ => ?_)
  obtain ⟨s₂, h₂, t9, tlr, t7, t8, t12, tz, tk, tsp, tm, trd, twr⟩ := VG.Proof.CmacTripleDes.Arm.passTail_ok s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [tz, h₁.r12, VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega), VG.Proof.CmacTripleDes.Arm.ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  · rw [tk .r10 (by decide), h₁.same.r10]
  · rw [tsp, h₁.same.sp]
  · rw [trd, h₁.same.rd]
  · rw [twr, h₁.same.wr]
  · rw [tm]; exact h₁.same.frame
  · rw [t9, h₁.r9, h₁.str, VG.Proof.CmacTripleDes.Arm.kpos_tail_addr _ hp3]
  · rw [tlr, h₁.str, VG.Proof.CmacTripleDes.Arm.stride_succ hp3]
  · rw [t12, h₁.r12, VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega)]
    congr 1
  · rw [t7, t8, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) {x : BitVec 64} {s : State} (h : VG.Proof.CmacTripleDes.Arm.OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (VG.Proof.CmacTripleDes.Arm.OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := VG.Proof.CmacTripleDes.Arm.OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ VG.Proof.CmacTripleDes.Arm.OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.passBody_ok hp hp3 ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- Bit `b` of a block `hi ‖ lo`, as an atom: of `hi` (input word 0) or `lo`
(input word 1). -/
def xAtom (b : Nat) : Nat := if 32 ≤ b then b - 32 else 32 + b

/-- `IP`'s high half into `r7`, its low half into `r8`. -/
def ipG7 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.Arm.xAtom (ipSrc (32 + t))] else []
def ipG8 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.Arm.xAtom (ipSrc t)] else []

/-- No memory. -/
def zCfg : Cfg := { base := .r10, slots := 0, ext := .r9, exts := 0 }

theorem zCfg_ok (s : State) : Ok VG.Proof.CmacTripleDes.Arm.zCfg s :=
  ⟨fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.zCfg]), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.zCfg]),
    by have := (s.gpr zCfg.base).isLt; simp only [VG.Proof.CmacTripleDes.Arm.zCfg] at this ⊢; omega, fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.zCfg])⟩

theorem frame_zCfg {s : State} {m m' : Mem} (h : Frame [slotRegion VG.Proof.CmacTripleDes.Arm.zCfg s] m m') : m' = m := by
  funext a
  exact h a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, VG.Proof.CmacTripleDes.Arm.zCfg, Region.Contains]

theorem ip_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.Arm.zCfg (linExt 2) ipCode (linEnv [(.r0, 0), (.r1, 1)])
      (linPost 6 [(.r7, VG.Proof.CmacTripleDes.Arm.ipG7), (.r8, VG.Proof.CmacTripleDes.Arm.ipG8)]) = true := by
  lit_decide

/-- `IP⁻¹(R ‖ L)` into `r0` (high word) and `r1` (low word), from `R` in `r7`
(input word 0) and `L` in `r8` (input word 1). -/
def fpG0 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.Arm.xAtom (fpSrc (32 + t))] else []
def fpG1 (t : Nat) : List Nat := if t < 32 then [VG.Proof.CmacTripleDes.Arm.xAtom (fpSrc t)] else []

theorem fp_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.Arm.zCfg (linExt 2) fpCode (linEnv [(.r7, 0), (.r8, 1)])
      (linPost 6 [(.r0, VG.Proof.CmacTripleDes.Arm.fpG0), (.r1, VG.Proof.CmacTripleDes.Arm.fpG1)]) = true := by
  lit_decide

theorem ip_kept : [Reg.r9, .r10].all (fun r => ipCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem fp_kept : [Reg.r9, .r10].all (fun r => fpCode.all fun i => dstOf i != some r) = true := by lit_decide

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by lit_decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by lit_decide

/-- A bit of `hi ‖ lo`. -/
theorem bit_xAtom (W : Nat → BitVec 32) {b : Nat} (hb : b < 64) :
    bitOf W (VG.Proof.CmacTripleDes.Arm.xAtom b) = (W 0 ++ W 1).getLsbD b := by
  rw [BitVec.getLsbD_append, VG.Proof.CmacTripleDes.Arm.xAtom]
  by_cases h : 32 ≤ b
  · rw [ite_eq_left h, ite_eq_right (by omega), bitOf, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, ite_eq_left (by omega), bitOf, show (32 + b) / 32 = 1 by omega,
      show (32 + b) % 32 = b by omega]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      (s'.gpr .r7, s'.gpr .r8) = split (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r0 ++ s.gpr .r1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r0 else s.gpr .r1
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.Arm.ip_check (VG.Proof.CmacTripleDes.Arm.zCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.zCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.ip_kept _ (by simp)),
    hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.ip_kept _ (by simp)), VG.Proof.CmacTripleDes.Arm.frame_zCfg hfr⟩
  have hx : W 0 ++ W 1 = s.gpr .r0 ++ s.gpr .r1 := rfl
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · rw [hout .r7 VG.Proof.CmacTripleDes.Arm.ipG7 (by simp) t ht, VG.Proof.CmacTripleDes.Arm.ipG7, ite_eq_left ht, xorBits_cons, xorBits_nil, Bool.xor_false,
      VG.Proof.CmacTripleDes.Arm.bit_xAtom W (VG.Proof.CmacTripleDes.Arm.ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      BitVec.getLsbD_ushiftRight, getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    rfl
  · rw [hout .r8 VG.Proof.CmacTripleDes.Arm.ipG8 (by simp) t ht, VG.Proof.CmacTripleDes.Arm.ipG8, ite_eq_left ht, xorBits_cons, xorBits_nil, Bool.xor_false,
      VG.Proof.CmacTripleDes.Arm.bit_xAtom W (VG.Proof.CmacTripleDes.Arm.ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht, Bool.true_and,
      getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    rfl

theorem fp_ok (s : State) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      s'.gpr .r0 ++ s'.gpr .r1 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r7 ++ s.gpr .r8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r10 = s.gpr .r10 ∧
      s'.mem = s.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r7 else s.gpr .r8
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok VG.Proof.CmacTripleDes.Arm.fp_check (VG.Proof.CmacTripleDes.Arm.zCfg_ok s) W
    (fun r i hri => by
      simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.zCfg]))
  refine ⟨s', hs', ?_, hrd, hwr, hsp, hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.fp_kept _ (by simp)),
    hoth _ (List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.fp_kept _ (by simp)), VG.Proof.CmacTripleDes.Arm.frame_zCfg hfr⟩
  have hx : W 0 ++ W 1 = s.gpr .r7 ++ s.gpr .r8 := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_append, getLsbD_permute _ _ (by decide) hj,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl]
  by_cases h32 : j < 32
  · rw [ite_eq_left h32, hout .r1 VG.Proof.CmacTripleDes.Arm.fpG1 (by simp) j h32, VG.Proof.CmacTripleDes.Arm.fpG1, ite_eq_left h32, xorBits_cons, xorBits_nil,
      Bool.xor_false, VG.Proof.CmacTripleDes.Arm.bit_xAtom W (VG.Proof.CmacTripleDes.Arm.fpSrc_lt _ hj), hx]
  · rw [ite_eq_right h32, hout .r0 VG.Proof.CmacTripleDes.Arm.fpG0 (by simp) (j - 32) (by omega), VG.Proof.CmacTripleDes.Arm.fpG0, ite_eq_left (by omega),
      xorBits_cons, xorBits_nil, Bool.xor_false, show 32 + (j - 32) = j by omega, VG.Proof.CmacTripleDes.Arm.bit_xAtom W (VG.Proof.CmacTripleDes.Arm.fpSrc_lt _ hj), hx]

/-- TDEA encryption of the block in `r0:r1` (its high and low words) with the
key schedule at `r9`, into `r0:r1`. -/
theorem block_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.BlockPre s₀) :
    WP isa VG.Impl.CmacTripleDes.Arm.block s₀ fun s =>
      VG.Proof.CmacTripleDes.Arm.Same s₀ s ∧ s.gpr .r9 = s₀.gpr .r9 ∧
        s.gpr .r0 ++ s.gpr .r1 = tdes (VG.Proof.CmacTripleDes.Arm.sch s₀) (s₀.gpr .r0 ++ s₀.gpr .r1) := by
  obtain ⟨s₁, h₁, hal₁, rd₁, wr₁, sp₁, r9₁, r10₁, m₁⟩ := VG.Proof.CmacTripleDes.Arm.ip_ok s₀
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, h₁, WP.of_runBlock ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      Option.map_some, ite_true]
    rfl, ?_⟩⟩
  have g : ∀ r, r ≠ .r12 → r ≠ .lr → ((s₁.setReg .r12 3).setReg .lr 8).gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h1]
  have hO : VG.Proof.CmacTripleDes.Arm.OInv s₀ (s₀.gpr .r0 ++ s₀.gpr .r1) 0 ((s₁.setReg .r12 3).setReg .lr 8) :=
    ⟨⟨by rw [g _ (by decide) (by decide), r10₁], sp₁, rd₁, wr₁,
      by show Frame [VG.Proof.CmacTripleDes.Arm.xR s₀] s₀.mem s₁.mem; rw [m₁]; exact Frame.refl _ _⟩,
      by rw [g _ (by decide) (by decide), r9₁]; simp [VG.Proof.CmacTripleDes.Arm.kpos],
      by rw [gpr_setReg_self]; rfl,
      by rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_self]; rfl,
      by rw [g _ (by decide) (by decide), g _ (by decide) (by decide), hal₁]; rfl⟩
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.passes_ok hp hO) fun s₃ h₃ => ?_)
  rw [WP.block_append_iff]
  let s₄ := s₃.setReg .r9 (s₃.gpr .r9 - 504)
  have h₄ : runBlock isa [.dp .sub .r9 .r9 (.imm 504)] s₃ = some s₄ := by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
      Option.map_some, ite_true]
    rfl
  obtain ⟨s₅, h₅, ax₅, rd₅, wr₅, sp₅, r9₅, r10₅, m₅⟩ := VG.Proof.CmacTripleDes.Arm.fp_ok s₄
  have g₄ : ∀ r, r ≠ .r9 → s₄.gpr r = s₃.gpr r := fun r hr => gpr_setReg_of_ne _ _ hr
  refine WP.of_runBlock ⟨s₄, h₄, WP.of_runBlock ⟨s₅, h₅, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [r10₅, g₄ _ (by decide), h₃.same.r10]
  · rw [sp₅]; exact h₃.same.sp
  · rw [rd₅]; exact h₃.same.rd
  · rw [wr₅]; exact h₃.same.wr
  · rw [m₅]; exact h₃.same.frame
  · rw [r9₅, gpr_setReg_self, h₃.r9, show 8 * VG.Proof.CmacTripleDes.Arm.kpos 3 0 = 504 from rfl,
      show (504 : BitVec 32) = BitVec.ofNat 32 504 from rfl, BitVec.add_sub_cancel]
  · rw [ax₅, g₄ _ (by decide), g₄ _ (by decide), tdes_eq, ← h₃.halves]

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit`. -/
section

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

namespace VG

materialize_value Impl.CmacTripleDes.Arm.roundKeys

theorem Proof.CmacTripleDes.Arm.roundKeys_eq :
    Impl.CmacTripleDes.Arm.roundKeys = Impl.CmacTripleDes.Arm.roundKeys.lit :=
  Impl.CmacTripleDes.Arm.roundKeys.lit_eq

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit`. -/
section

/-! # TDEA-CMAC's ARMv7 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.Arm.init
materialize_code Impl.CmacTripleDes.Arm.update
materialize_code Impl.CmacTripleDes.Arm.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Contract`. -/
section

/-!
# TDEA-CMAC on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Implies.lean`). The functions call nothing and use no stack; `update` and
`finalize` take `scratch` on the stack.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = r0, key_len = r1, out = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r2), 400⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 640⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 400 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 640 ≤ 2 ^ 32 ∧ Spec.TripleDes.validKey (s.gpr .r1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (State.addr (s.gpr .r2)) = k ∧
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2) + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_triple_des_update(schedule = r0, state = r1, data = r2, n = r3, scratch = [sp])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let state : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
      Spec.Cmac.chain (VG.Proof.CmacTripleDes.Arm.ciphAt s.mem (State.addr (s.gpr .r0))) (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r2)) 8 (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_cmac_triple_des_finalize(key = r0, state = r1, last = r2, last_len = r3, scratch = [sp])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 400⟩
    let state : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let last : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      (s.gpr .r0).toNat + 400 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧
      s.sp.toNat + 4 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat ≤ 8
  post s s' :=
    let ciph := VG.Proof.CmacTripleDes.Arm.ciphAt s.mem (State.addr (s.gpr .r0))
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .r3).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Save`. -/
section

/-!
# TDEA-CMAC on ARMv7: saving and restoring the registers

Untrusted: everything here is checked by Lean. Each function saves our
caller's callee-saved registers to bytes `[52, 88)` of the scratch buffer
(`save`), and restores them from there through `r10`, `r10` last
(`restore`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm
open VG.Proof.MdStream.Arm (saveMem)

theorem saved_bound : ∀ p ∈ saved, 52 ≤ p.2 ∧ p.2 + 4 ≤ 88 := by decide

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem := VG.Arm.Spill.saveMem s₀.mem (State.addr S) s₀.gpr saved

export VG.Arm.Spill (saveMem_congr)

theorem saved_slots : Spill.Slots 52 88 saved := by decide

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨State.addr S + BitVec.ofNat 64 52, 36⟩] s₀.mem (VG.Proof.CmacTripleDes.Arm.savedMem s₀ S) :=
  Spill.saveMem_frame_slots VG.Proof.CmacTripleDes.Arm.saved_slots _ _ _

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Proof.CmacTripleDes.Arm.savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr S) s₀.gpr s₀.mem saved VG.Proof.CmacTripleDes.Arm.saved_slots (r, d) h

/-- The registers but `r10`, and where they are saved. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 52), (.r5, 56), (.r6, 60), (.r7, 64), (.r8, 68), (.r9, 72), (.r11, 76), (.lr, 80)]

theorem saved_eq : saved = VG.Proof.CmacTripleDes.Arm.saved8 ++ [(.r10, 84)] := rfl

/-- `restore` from the scratch buffer at `S`: each register gets its slot. -/
theorem restore_ok {s : State} {S : BitVec 32} (hb : s.gpr .r10 = S) (hS : S.toNat + 88 ≤ 2 ^ 32)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 88 → InRegions (s.rd ++ s.wr) (State.addr S + BitVec.ofNat 64 d) 4) :
    WP isa (.block restore) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore, VG.Proof.CmacTripleDes.Arm.saved_eq, ← List.append_nil (List.map _ _)]
  subst hb
  refine Spill.restoreBase_ok (by decide) (fun p hp => ?_) fun s' hl _ hm hrd hwr hsp => WP.block_nil ⟨hl, hsp, hm, hrd, hwr⟩
  have := saved_slots.bound hp
  exact ⟨by omega, by omega, hr _ this.1 this.2.1⟩

/-- The registers restored from slots that have not changed since they were
saved. -/
theorem restored {s₀ s s' : State} {S : BitVec 32}
    (hm : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacTripleDes.Arm.savedMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32)
    (h : ∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (State.addr S + BitVec.ofNat 64 p.2) 32) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, hsp⟩
  have hk : ∀ r ∈ preserved, r ∈ saved.map Prod.fst := by decide
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hk r hr)
  have hb := VG.Proof.CmacTripleDes.Arm.saved_bound _ hp
  rw [h _ hp, hm p.2 hb.1 hb.2, VG.Proof.CmacTripleDes.Arm.savedMem_slot s₀ S hp]

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Update`. -/
section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_update`

Untrusted: everything here is checked by Lean. The invariant after `k`
blocks (`LInv`): words 28–30 of the scratch buffer hold the state pointer,
the next block and the blocks left, only the state, the block's words and
those three have changed since the registers were saved, and the state is
the chaining value after the first `k` blocks.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldrSp wp_ldr
  wp_str wp_rev saveMem saveList_ok cmp0 ofNat_beq_zero)

theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

/-- The key schedule is unchanged outside a frame. -/
theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) :
    Spec.TripleDes.scheduleAt m' p = Spec.TripleDes.scheduleAt m p := by
  apply Vector.ext
  intro n hn
  rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, scheduleAt_getD _ _ hn]
  exact hf.readW (r := ⟨p + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

section
variable (s₀ : State)

abbrev W : BitVec 32 := s₀.gpr .r0
abbrev St : BitVec 32 := s₀.gpr .r1
abbrev Dp : BitVec 32 := s₀.gpr .r2
abbrev N : Nat := (s₀.gpr .r3).toNat
abbrev S : BitVec 32 := stackArg s₀ 0

abbrev schR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.W s₀), 384⟩
abbrev stR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.St s₀), 8⟩
abbrev dataR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀), 8 * VG.Proof.CmacTripleDes.Arm.N s₀⟩
abbrev scrR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀), 640⟩
abbrev argsR : Region := ⟨stackArgAddr s₀ 0, 4⟩

/-- The cipher. -/
abbrev ciph : Spec.Cmac.Cipher := VG.Proof.CmacTripleDes.Arm.ciphAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.W s₀))

/-- The message blocks. -/
abbrev blks : List (List Byte) := Spec.Cmac.blocksAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀)) 8 (VG.Proof.CmacTripleDes.Arm.N s₀)

/-- What changes after the registers are saved. -/
abbrev chg : List Region :=
  [VG.Proof.CmacTripleDes.Arm.stR s₀, ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀), 52⟩, ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩]

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.Arm.schR s₀, VG.Proof.CmacTripleDes.Arm.dataR s₀, VG.Proof.CmacTripleDes.Arm.argsR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.Arm.stR s₀, VG.Proof.CmacTripleDes.Arm.scrR s₀]
  sch_st : (VG.Proof.CmacTripleDes.Arm.schR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.stR s₀)
  sch_scr : (VG.Proof.CmacTripleDes.Arm.schR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.scrR s₀)
  data_st : (VG.Proof.CmacTripleDes.Arm.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.stR s₀)
  data_scr : (VG.Proof.CmacTripleDes.Arm.dataR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.scrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.Arm.stR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.scrR s₀)
  st_args : (VG.Proof.CmacTripleDes.Arm.stR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.argsR s₀)
  scr_args : (VG.Proof.CmacTripleDes.Arm.scrR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.argsR s₀)
  sch_fit : (VG.Proof.CmacTripleDes.Arm.W s₀).toNat + 384 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacTripleDes.Arm.St s₀).toNat + 8 ≤ 2 ^ 32
  data_fit : (VG.Proof.CmacTripleDes.Arm.Dp s₀).toNat + 8 * VG.Proof.CmacTripleDes.Arm.N s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.Arm.S s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem UPre.of {s₀ : State} (h : updateArm.pre s₀) : VG.Proof.CmacTripleDes.Arm.UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- The loop invariant, after `k` blocks. -/
structure LInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = VG.Proof.CmacTripleDes.Arm.W s₀
  r10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  st : s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112) 32 = VG.Proof.CmacTripleDes.Arm.St s₀
  dp : s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 116) 32 = VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * k)
  left : s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 120) 32 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - k)
  frame : Frame (VG.Proof.CmacTripleDes.Arm.chg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) s.mem
  state : Spec.Aes.bytesAt s.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8 =
    Spec.Cmac.chain (VG.Proof.CmacTripleDes.Arm.ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8) ((VG.Proof.CmacTripleDes.Arm.blks s₀).take k)

/-! ## Regions -/

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀)
include hp

theorem UPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem UPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (VG.Proof.CmacTripleDes.Arm.S s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem UPre.sched {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.Arm.chg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) m) :
    Spec.TripleDes.scheduleAt m (State.addr (VG.Proof.CmacTripleDes.Arm.W s₀)) = Spec.TripleDes.scheduleAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.W s₀)) := by
  rw [VG.Proof.CmacTripleDes.Arm.scheduleAt_frame hf fun r hr => ?_]
  · exact VG.Proof.CmacTripleDes.Arm.scheduleAt_frame (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.sch_st
    · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.sch_scr.sub_right (Offset.sub_base _ (by decide))

theorem UPre.data {m : Mem} (hf : Frame (VG.Proof.CmacTripleDes.Arm.chg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) m) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.Arm.N s₀) :
    Spec.Aes.bytesAt m (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k)) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k)) 8 := by
  have hsub : Region.Sub ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k), 8⟩ (VG.Proof.CmacTripleDes.Arm.dataR s₀) :=
    Offset.sub_base _ (by omega)
  rw [bytesAt_frame hf (fun r hr => ?_) (by decide)]
  · exact bytesAt_frame (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.data_st.sub_left hsub
    · exact (hp.data_scr.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · exact (hp.data_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))

/-- The block's precondition, with the registers and regions of the function. -/
theorem UPre.block {s : State} (h9 : s.gpr .r9 = VG.Proof.CmacTripleDes.Arm.W s₀) (h10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : VG.Proof.CmacTripleDes.Arm.BlockPre s where
  sched := ⟨384, by rw [hrd, hwr, hp.rd, h9]; simp, Nat.le_refl _, by rw [h9]; exact hp.sch_fit⟩
  scr := ⟨640, by rw [hwr, hp.wr, h10]; simp, by decide, by rw [h10]; exact hp.scr_fit⟩
  disj := by
    rw [h9, h10]
    exact hp.sch_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-! ## One block -/

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.Arm.N s₀) :
    (VG.Proof.CmacTripleDes.Arm.blks s₀).take (k + 1) =
      (VG.Proof.CmacTripleDes.Arm.blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k)) 8] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-- The two words at `a` XORed, as a big-endian integer. -/
theorem rev_xor_append (a₀ a₁ b₀ b₁ : BitVec 32) :
    rev (a₀ ^^^ b₀) ++ rev (a₁ ^^^ b₁) = byteRev64 ((a₁ ++ a₀) ^^^ (b₁ ++ b₀)) := by
  rw [VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq, byteRev32_append, BitVec.xor_append]

theorem add0 (a : BitVec 32) : a + BitVec.ofNat 32 0 = a := BitVec.add_zero a

theorem readW_writeW_far (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  MdStream.Arm.readW_writeW_save m B v hd he h

theorem readW_writeW_far' (m : Mem) (a : Addr) (w : BitVec 32) :
    (m.writeW (a + BitVec.ofNat 64 4) w).readW a 32 = m.readW a 32 := by
  have := VG.Proof.CmacTripleDes.Arm.readW_writeW_far m a w (d := 0) (e := 4) (by decide) (by decide) (by decide)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this

theorem readW_lo_of_hi (m : Mem) (a : Addr) (v w : BitVec 32) :
    ((m.writeW a v).writeW (a + BitVec.ofNat 64 4) w).readW a 32 = v := by
  have := VG.Proof.CmacTripleDes.Arm.readW_writeW_far' (m.writeW a v) a w
  rw [this, Mem.readW_writeW_self32]

theorem body_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.Arm.N s₀) {s : State} (h : VG.Proof.CmacTripleDes.Arm.LInv s₀ k s) :
    WP isa updBody s fun s' => VG.Proof.CmacTripleDes.Arm.LInv s₀ (k + 1) s' ∧ s'.z = decide (VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1) = 0) := by
  have hN : VG.Proof.CmacTripleDes.Arm.N s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  have hsf := hp.scr_fit
  have hdf := hp.data_fit
  have htf := hp.st_fit
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacTripleDes.Arm.schR s₀, VG.Proof.CmacTripleDes.Arm.dataR s₀, VG.Proof.CmacTripleDes.Arm.argsR s₀, VG.Proof.CmacTripleDes.Arm.stR s₀, VG.Proof.CmacTripleDes.Arm.scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have stA : State.addr (VG.Proof.CmacTripleDes.Arm.St s₀ + BitVec.ofNat 32 4) = State.addr (VG.Proof.CmacTripleDes.Arm.St s₀) + BitVec.ofNat 64 4 := addr_add (by omega)
  have dA : State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * k)) = State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k) :=
    addr_add (by omega)
  have dA4 : State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4) =
      State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 4 := by
    rw [Straight.add_ofNat_ofNat, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  have dIn : ∀ d, d + 4 ≤ 8 →
      InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr, Offset.add_add]
      exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.dataR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  -- `chainIn`.
  refine WP.seq (?_ : WP isa (.block chainIn) s _)
  simp only [chainIn]
  refine wp_ldr (by decide) (by rw [h.r10, hp.scrAddr (by decide)]) (scrIn 112 (by decide)) fun s₁ u₁ => ?_
  refine wp_ldr (by decide) (by rw [u₁.other _ (by decide), h.r10, hp.scrAddr (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact scrIn 116 (by decide)) fun s₂ u₂ => ?_
  have r4₂ : s₂.gpr .r4 = VG.Proof.CmacTripleDes.Arm.St s₀ := by rw [u₂.other _ (by decide), u₁.gpr, h.st]
  have r5₂ : s₂.gpr .r5 = VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * k) := by rw [u₂.gpr, u₁.mem, h.dp]
  refine wp_ldr (by decide) (by rw [r4₂, VG.Proof.CmacTripleDes.Arm.add0])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (by rw [u₃.other _ (by decide), r4₂, stA])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_ldr (by decide) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), r5₂, VG.Proof.CmacTripleDes.Arm.add0, dA])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; simpa using dIn 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_ldr (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r5₂,
      dA4])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact dIn 4 (by decide))
    fun s₆ u₆ => ?_
  refine VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₇ u₇ => VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₈ u₈ => wp_rev fun s₉ u₉ =>
    wp_rev fun s₁₀ u₁₀ => WP.block_nil ?_
  -- What `chainIn` leaves.
  have g₁₀ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3, .r4, .r5] → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other _ hr.2.1, u₉.other _ hr.1, u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.2.1,
      u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, u₂.other _ hr.2.2.2.2.2,
      u₁.other _ hr.2.2.2.2.1]
  have m₁₀ : s₁₀.mem = s.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₁₀ : s₁₀.rd = s.rd := by
    rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₁₀ : s₁₀.sp = s.sp := by
    rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have ax₁₀ : s₁₀.gpr .r0 ++ s₁₀.gpr .r1 = byteRev64 (s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 64 ^^^
      s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k)) 64) := by
    rw [u₁₀.gpr, u₁₀.other .r0 (by decide), u₉.gpr, u₉.other .r1 (by decide), u₈.gpr, u₈.other .r0 (by decide),
      u₇.gpr, u₇.other .r1 (by decide), u₇.other .r3 (by decide), u₆.gpr, u₆.other .r0 (by decide),
      u₆.other .r1 (by decide), u₆.other .r2 (by decide), u₅.gpr, u₅.other .r0 (by decide),
      u₅.other .r1 (by decide), u₄.gpr, u₄.other .r0 (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
      u₁.mem, readW64_split, readW64_split s.mem (State.addr (VG.Proof.CmacTripleDes.Arm.Dp s₀) + BitVec.ofNat 64 (8 * k)),
      VG.Proof.CmacTripleDes.Arm.rev_xor_append]
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.block_ok (UPre.block hp (by rw [g₁₀ _ (by decide), h.r9])
    (by rw [g₁₀ _ (by decide), h.r10]) (by rw [rd₁₀, h.rd]) (by rw [wr₁₀, h.wr]))) fun s₁₁ ⟨same, r9₁₁, ax₁₁⟩ => ?_)
  -- The slots past the block's words are unchanged.
  have r10₁₁ : s₁₁.gpr .r10 = VG.Proof.CmacTripleDes.Arm.S s₀ := by rw [same.r10, g₁₀ _ (by decide), h.r10]
  have xR₁₀ : VG.Proof.CmacTripleDes.Arm.xR s₁₀ = ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀), 52⟩ := by rw [VG.Proof.CmacTripleDes.Arm.xR, g₁₀ _ (by decide), h.r10]
  have f₁₁ : Frame [⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀), 52⟩] s.mem s₁₁.mem := by rw [← m₁₀, ← xR₁₀]; exact same.frame
  have slot : ∀ d, 52 ≤ d → d + 4 ≤ 640 →
      s₁₁.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) 32 :=
    fun d h₁ h₂ => f₁₁.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₁₁ : s₁₁.rd ++ s₁₁.wr = [VG.Proof.CmacTripleDes.Arm.schR s₀, VG.Proof.CmacTripleDes.Arm.dataR s₀, VG.Proof.CmacTripleDes.Arm.argsR s₀, VG.Proof.CmacTripleDes.Arm.stR s₀, VG.Proof.CmacTripleDes.Arm.scrR s₀] := by
    rw [same.rd, same.wr, rd₁₀, wr₁₀, rdwr]
  have wr₁₁ : s₁₁.wr = [VG.Proof.CmacTripleDes.Arm.stR s₀, VG.Proof.CmacTripleDes.Arm.scrR s₀] := by rw [same.wr, wr₁₀, h.wr, hp.wr]
  simp only [chainOut]
  refine wp_ldr (by decide) (by rw [r10₁₁, hp.scrAddr (by decide)])
    (by rw [rdwr₁₁]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₁ v₁ => ?_
  refine wp_ldr (by decide) (by rw [v₁.other _ (by decide), r10₁₁, hp.scrAddr (by decide)])
    (by rw [v₁.rd, v₁.wr, rdwr₁₁]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₂ v₂ => ?_
  refine wp_ldr (by decide) (by rw [v₂.other _ (by decide), v₁.other _ (by decide), r10₁₁, hp.scrAddr (by decide)])
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, rdwr₁₁]
        exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun t₃ v₃ => ?_
  have r4₃ : t₃.gpr .r4 = VG.Proof.CmacTripleDes.Arm.St s₀ := by
    rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, slot 112 (by decide) (by decide), h.st]
  have r5₃ : t₃.gpr .r5 = VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, slot 116 (by decide) (by decide), h.dp]
  have r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - k) := by
    rw [v₃.gpr, v₂.mem, v₁.mem, slot 120 (by decide) (by decide), h.left]
  refine wp_rev fun t₄ v₄ => wp_rev fun t₅ v₅ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions t₅.wr (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₁₁]
    exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.stR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [v₅.other _ (by decide), v₄.other _ (by decide), r4₃, VG.Proof.CmacTripleDes.Arm.add0])
    (by simpa using stW 0 (by decide)) fun t₆ w₆ => ?_
  refine wp_str (by decide) (by rw [w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r4₃, stA])
    (by rw [w₆.wr]; exact stW 4 (by decide)) fun t₇ w₇ => ?_
  refine wp_add (op2_imm (by decide)) fun t₈ v₈ => wp_sub (op2_imm (by decide)) fun t₉ v₉ => ?_
  have g₉ : ∀ r, r ∉ [Reg.r0, .r1, .r4, .r5, .r6] → t₉.gpr r = s₁₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₉.other _ hr.2.2.2.2, v₈.other _ hr.2.2.2.1, w₇.gpr, w₆.gpr, v₅.other _ hr.2.1, v₄.other _ hr.1,
      v₃.other _ hr.2.2.2.2, v₂.other _ hr.2.2.2.1, v₁.other _ hr.2.2.1]
  have r10₉ : t₉.gpr .r10 = VG.Proof.CmacTripleDes.Arm.S s₀ := by rw [g₉ _ (by decide), r10₁₁]
  have wr₉ : t₉.wr = [VG.Proof.CmacTripleDes.Arm.stR s₀, VG.Proof.CmacTripleDes.Arm.scrR s₀] := by
    rw [v₉.wr, v₈.wr, w₇.wr, w₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₁₁]
  have scrW : ∀ d, d + 4 ≤ 640 → InRegions t₉.wr (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [wr₉]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [r10₉, hp.scrAddr (by decide)]) (scrW 112 (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_str (by decide) (by rw [w₁₀.gpr, r10₉, hp.scrAddr (by decide)]) (by rw [w₁₀.wr]; exact scrW 116 (by decide))
    fun t₁₁ w₁₁ => ?_
  refine wp_str (by decide) (by rw [w₁₁.gpr, w₁₀.gpr, r10₉, hp.scrAddr (by decide)])
    (by rw [w₁₁.wr, w₁₀.wr]; exact scrW 120 (by decide)) fun t₁₂ w₁₂ =>
      wp_cmp (op2_imm (by decide)) fun t₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  -- The registers stored.
  have r4₉ : t₉.gpr .r4 = VG.Proof.CmacTripleDes.Arm.St s₀ := by
    rw [v₉.other _ (by decide), v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), r4₃]
  have r5₉ : t₉.gpr .r5 = VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [v₉.other _ (by decide), v₈.gpr, w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r5₃,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Straight.add_ofNat_ofNat, show 8 * k + 8 = 8 * (k + 1) by omega]
  have r6₈ : t₈.gpr .r6 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - k) := by
    rw [v₈.other _ (by decide), w₇.gpr, w₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), r6₃]
  have dec : BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - k) - 1 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1)) :=
    VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega)
  have r6₉ : t₉.gpr .r6 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1)) := by rw [v₉.gpr, r6₈, dec]
  -- The memory.
  have m₉ : t₉.mem = (s₁₁.mem.writeW (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) (rev (s₁₁.gpr .r0))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀) + BitVec.ofNat 64 4) (rev (s₁₁.gpr .r1)) := by
    rw [v₉.mem, v₈.mem, w₇.mem, w₆.mem, w₆.gpr, v₅.gpr, v₅.other .r0 (by decide), v₄.gpr, v₅.mem, v₄.mem,
      v₄.other .r1 (by decide), v₃.other .r0 (by decide), v₃.other .r1 (by decide), v₂.other .r0 (by decide),
      v₂.other .r1 (by decide), v₁.other .r0 (by decide), v₁.other .r1 (by decide), v₃.mem, v₂.mem, v₁.mem]
  have m₁₂ : t₁₂.mem = ((t₉.mem.writeW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112) (VG.Proof.CmacTripleDes.Arm.St s₀)).writeW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 116)
      (VG.Proof.CmacTripleDes.Arm.Dp s₀ + BitVec.ofNat 32 (8 * (k + 1)))).writeW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 120)
      (BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1))) := by
    rw [w₁₂.mem, w₁₁.mem, w₁₀.mem, w₁₁.gpr, w₁₀.gpr, r4₉, r5₉, r6₉]
  have g₁₃ : t₁₃.gpr = t₉.gpr := by rw [f₁₃.gpr, w₁₂.gpr, w₁₁.gpr, w₁₀.gpr]
  have mem₁₃ : t₁₃.mem = t₁₂.mem := f₁₃.mem
  -- The state.
  have hS : VG.Proof.CmacTripleDes.Arm.sch s₁₀ = Spec.TripleDes.scheduleAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.W s₀)) := by
    rw [VG.Proof.CmacTripleDes.Arm.sch, g₁₀ _ (by decide), h.r9, m₁₀]; exact UPre.sched hp h.frame
  have hD := UPre.data hp h.frame hk
  have stSep : ∀ d, 112 ≤ d → d + 4 ≤ 124 → (VG.Proof.CmacTripleDes.Arm.stR s₀).Disjoint ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩ := fun d h₁ h₂ =>
    hp.st_scr.sub_right (Offset.sub_base _ (by omega))
  have stFrame : Spec.Aes.bytesAt t₁₂.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8 = Spec.Aes.bytesAt t₉.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8 := by
    rw [m₁₂]
    refine bytesAt_frame (rs := [⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩]) ?_ (fun r hr => ?_) (by decide)
    · have c : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
          (⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
        rw [show State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d = State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112 + BitVec.ofNat 64 (d - 112) from
          (Offset.add_add_eq _ (by omega)).symm]
        exact Offset.contains_base _ (by omega) (by omega)
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c 116 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (c 120 (by decide) (by decide))
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g₁₃, g₉ _ (by decide), r9₁₁, g₁₀ _ (by decide), h.r9]
  · rw [g₁₃, r10₉]
  · rw [f₁₃.sp, w₁₂.sp, w₁₁.sp, w₁₀.sp, v₉.sp, v₈.sp, w₇.sp, w₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, same.sp,
      sp₁₀, h.sp]
  · rw [f₁₃.rd, w₁₂.rd, w₁₁.rd, w₁₀.rd, v₉.rd, v₈.rd, w₇.rd, w₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, same.rd,
      rd₁₀, h.rd]
  · rw [f₁₃.wr, w₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉, ← hp.wr, ← h.wr]
  · rw [mem₁₃, m₁₂, VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, Mem.readW_writeW_self32]
  · rw [mem₁₃, m₁₂, m₉]
    have c4 : (VG.Proof.CmacTripleDes.Arm.stR s₀).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀) + BitVec.ofNat 64 4) (32 / 8) :=
      Offset.contains_base _ (by decide) (by omega)
    have c0 : (VG.Proof.CmacTripleDes.Arm.stR s₀).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) (32 / 8) := by
      simpa using Offset.contains_base (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    have cs : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
        (⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => by
      rw [show State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d = State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112 + BitVec.ofNat 64 (d - 112) from
        (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by omega) (by omega)
    exact (((((h.frame.trans (f₁₁.mono fun r hr => by simp at hr; simp [hr])).writeW (r := VG.Proof.CmacTripleDes.Arm.stR s₀) (by simp) _
      c0).writeW (r := VG.Proof.CmacTripleDes.Arm.stR s₀) (by simp) _ c4).writeW (by simp) _ (cs 112 (by decide) (by decide))).writeW
      (by simp) _ (cs 116 (by decide) (by decide))).writeW (by simp) _ (cs 120 (by decide) (by decide))
  · rw [mem₁₃, stFrame, m₉, ← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.Arm.readW_lo_of_hi, VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq,
      byteRev32_append, ax₁₁, ax₁₀, hS, ← tdesWith_le8, le8_xor, le8_readW, le8_readW, h.state, hD,
      VG.Proof.CmacTripleDes.Arm.take_succ_blks s₀ hk, chain_append, chain_single]
  · rw [z₁₃, show t₁₂.gpr .r6 = t₉.gpr .r6 by rw [w₁₂.gpr, w₁₁.gpr, w₁₀.gpr], r6₉]
    exact cmp0 (by omega)

theorem loop_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) {k : Nat} (hk : k < VG.Proof.CmacTripleDes.Arm.N s₀) {s : State}
    (h : VG.Proof.CmacTripleDes.Arm.LInv s₀ k s) : WP isa (.loop updBody .ne) s (VG.Proof.CmacTripleDes.Arm.LInv s₀ (VG.Proof.CmacTripleDes.Arm.N s₀)) := by
  refine WP.loop (M := isa) (body := updBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.Arm.LInv s₀ (VG.Proof.CmacTripleDes.Arm.N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = VG.Proof.CmacTripleDes.Arm.N s₀ - j ∧ j < VG.Proof.CmacTripleDes.Arm.N s₀ ∧ VG.Proof.CmacTripleDes.Arm.LInv s₀ j t) ?_ (VG.Proof.CmacTripleDes.Arm.N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.body_ok hp hk h) fun s' ⟨h', z'⟩ => ?_
  by_cases hz : VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], ?_⟩
    rwa [show VG.Proof.CmacTripleDes.Arm.N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], VG.Proof.CmacTripleDes.Arm.N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-! ## The whole function -/

theorem UPre.arg_in {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.argsR s₀) (by simp) (Region.contains_self _ _)

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem prologue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) :
    WP isa (.block updPre) s₀ fun s => VG.Proof.CmacTripleDes.Arm.LInv s₀ 0 s ∧ s.z = decide (VG.Proof.CmacTripleDes.Arm.N s₀ = 0) := by
  have hsc := hp.scr_fit
  have hN : VG.Proof.CmacTripleDes.Arm.N s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  rw [show updPre = .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    ([mov .r10 .r12, mov .r9 .r0, .str .r1 .r10 112, .str .r2 .r10 116, .str .r3 .r10 120,
      .cmp .r3 (.imm 0)] : List Instr)) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.CmacTripleDes.Arm.S s₀ := u₁.gpr
  refine VG.Arm.Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := VG.Proof.CmacTripleDes.Arm.saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  have hm₂ : s₂.mem = VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀) := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacTripleDes.Arm.savedMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (VG.Proof.CmacTripleDes.Arm.saved_ne_r12 p hp')
  simp only [mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have r10₄ : s₄.gpr .r10 = VG.Proof.CmacTripleDes.Arm.S s₀ := by rw [u₄.other _ (by decide), u₃.gpr, g₂, h12]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂, u₁.wr]
  refine wp_str (by decide) (by rw [r10₄, hp.scrAddr (by decide)]) (by rw [wr₄]; exact hp.inScr (by decide) (by decide))
    fun s₅ w₅ => ?_
  refine wp_str (by decide) (by rw [w₅.gpr, r10₄, hp.scrAddr (by decide)])
    (by rw [w₅.wr, wr₄]; exact hp.inScr (by decide) (by decide)) fun s₆ w₆ => ?_
  refine wp_str (by decide) (by rw [w₆.gpr, w₅.gpr, r10₄, hp.scrAddr (by decide)])
    (by rw [w₆.wr, w₅.wr, wr₄]; exact hp.inScr (by decide) (by decide)) fun s₇ w₇ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  have g₈ : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s₈.gpr r = s₀.gpr r := fun r h9 h10 h12' => by
    rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, u₄.other _ h9, u₃.other _ h10, g₂, u₁.other _ h12']
  have r1₄ : s₄.gpr .r1 = VG.Proof.CmacTripleDes.Arm.St s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have r2₄ : s₄.gpr .r2 = VG.Proof.CmacTripleDes.Arm.Dp s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have r3₄ : s₄.gpr .r3 = s₀.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  have m₈ : s₈.mem = (((VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)).writeW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112) (VG.Proof.CmacTripleDes.Arm.St s₀)).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 116) (VG.Proof.CmacTripleDes.Arm.Dp s₀)).writeW (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 120)
      (s₀.gpr .r3) := by
    rw [f₈.mem, w₇.mem, w₆.mem, w₅.mem, u₄.mem, u₃.mem, hm₂, w₆.gpr, w₅.gpr, r1₄, r2₄, r3₄]
  have cs : ∀ d, 112 ≤ d → d + 4 ≤ 124 →
      (⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩ : Region).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d)
        (32 / 8) := fun d h₁ h₂ => by
    rw [show State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d = State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112 +
      BitVec.ofNat 64 (d - 112) from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have fr₈ : Frame [⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 112, 12⟩] (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) s₈.mem := by
    rw [m₈]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 112 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 116 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cs 120 (by decide) (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, r10₄]
  · rw [f₈.sp, w₇.sp, w₆.sp, w₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₈.rd, w₇.rd, w₆.rd, w₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₈.wr, w₇.wr, w₆.wr, w₅.wr, wr₄]
  · rw [m₈, VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide),
      VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m₈, VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.Arm.add0]
  · rw [m₈, Mem.readW_writeW_self32, Nat.sub_zero]; simp [VG.Proof.CmacTripleDes.Arm.N]
  · exact fr₈.mono fun r hr => by simp at hr; simp [hr]
  · rw [List.take_zero, show Spec.Cmac.chain (VG.Proof.CmacTripleDes.Arm.ciph s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8) [] =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8 from rfl]
    rw [bytesAt_frame fr₈ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)]
    exact bytesAt_frame (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.S s₀)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [z₈, show s₇.gpr .r3 = s₀.gpr .r3 by rw [w₇.gpr, w₆.gpr, w₅.gpr, r3₄]]
    have : s₀.gpr .r3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.N s₀) := by simp [VG.Proof.CmacTripleDes.Arm.N]
    rw [this]; exact cmp0 hN

theorem mid_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) {s₁ : State} (h : VG.Proof.CmacTripleDes.Arm.LInv s₀ 0 s₁) (hz : s₁.z = decide (VG.Proof.CmacTripleDes.Arm.N s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop updBody .ne)) s₁ (VG.Proof.CmacTripleDes.Arm.LInv s₀ (VG.Proof.CmacTripleDes.Arm.N s₀)) := by
  have ev : isa.eval .eq s₁ = some (decide (VG.Proof.CmacTripleDes.Arm.N s₀ = 0)) := by show some s₁.z = _; rw [hz]
  by_cases hn : VG.Proof.CmacTripleDes.Arm.N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact VG.Proof.CmacTripleDes.Arm.loop_ok hp (by omega) h

theorem epilogue_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.UPre s₀) {s₂ : State} (h₂ : VG.Proof.CmacTripleDes.Arm.LInv s₀ (VG.Proof.CmacTripleDes.Arm.N s₀) s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hsc := hp.scr_fit
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.restore_ok h₂.r10 (by omega) fun d h₁ h₂' => ?_) fun s' ⟨hl, sp', m', _, _⟩ => ⟨?_, ?_⟩
  · rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.scrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))
  · refine VG.Proof.CmacTripleDes.Arm.restored (S := VG.Proof.CmacTripleDes.Arm.S s₀) (fun d h₁ h₂' => ?_) hl (by rw [sp', h₂.sp])
    refine h₂.frame.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (d := d) (e := 112) (by omega) (by omega) (by omega)
  · show Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.CmacTripleDes.Arm.St s₀)) 8 = Spec.Cmac.chain (VG.Proof.CmacTripleDes.Arm.ciph s₀) _ (VG.Proof.CmacTripleDes.Arm.blks s₀)
    rw [m', h₂.state, List.take_of_length_le (by simp [Spec.Cmac.blocksAt])]

theorem update_wp {s₀ : State} (h0 : updateArm.pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ updateArm.post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.prologue_wp hp) fun s₁ ⟨h₁, z₁⟩ =>
    WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.mid_wp hp h₁ z₁) fun _ h₂ => VG.Proof.CmacTripleDes.Arm.epilogue_wp hp h₂))

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Keys`. -/
section

/-!
# DES's key schedule on 32-bit ARM

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key in `r0:r1` (its high and low words)
to the round keys' words it stores: the kernel checks it over the lane
domain (`roundKeys_check`), and `getLsbD_expandDesKey` says the bits are the
specification's.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.Arm
  VG.Proof.CmacTripleDes

/-- The round keys' words, at `r2`. -/
def kCfg : Cfg := { base := .r2, slots := 32, ext := .r2, exts := 0 }

/-- Bit `q` of word `w` (0 low, 1 high) of round key `j`: bit `rkSrc j (32 w + q)`
of the key. -/
def rkG (k q : Nat) : List Nat :=
  if q < (if k % 2 = 0 then 32 else 16) then [VG.Proof.CmacTripleDes.Arm.xAtom (rkSrc (k / 2) (32 * (k % 2) + q))] else []

theorem rkG_lo {j q : Nat} (hq : q < 32) : VG.Proof.CmacTripleDes.Arm.rkG (2 * j) q = [VG.Proof.CmacTripleDes.Arm.xAtom (rkSrc j q)] := by
  simp [VG.Proof.CmacTripleDes.Arm.rkG, hq, show 2 * j / 2 = j by omega]

theorem rkG_hi {j q : Nat} (hq : q < 16) : VG.Proof.CmacTripleDes.Arm.rkG (2 * j + 1) q = [VG.Proof.CmacTripleDes.Arm.xAtom (rkSrc j (32 + q))] := by
  simp [VG.Proof.CmacTripleDes.Arm.rkG, hq, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

theorem rkG_hi0 {j q : Nat} (hq : 16 ≤ q) : VG.Proof.CmacTripleDes.Arm.rkG (2 * j + 1) q = [] := by
  simp [VG.Proof.CmacTripleDes.Arm.rkG, show (2 * j + 1) % 2 = 1 by omega, show ¬ q < 16 by omega]

def kPost (e : Env (Nat × Nat)) : Bool := (List.range 32).all fun k => e.slot k == some (outWord (VG.Proof.CmacTripleDes.Arm.rkG k))

theorem roundKeys_check :
    VG.Arm.Straight.check (lanes 32 6) VG.Proof.CmacTripleDes.Arm.kCfg (linExt 2) roundKeys (linEnv [(.r0, 0), (.r1, 1)]) VG.Proof.CmacTripleDes.Arm.kPost = true := by
  rw [VG.Proof.CmacTripleDes.Arm.roundKeys_eq]; lit_decide

theorem rkG_lt : ∀ k < 32, ∀ q < 32, ∀ a ∈ VG.Proof.CmacTripleDes.Arm.rkG k q, a < 2 ^ 6 := by lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` writes. -/
def kWrites : List Reg := [.r6, .r7, .r8]

/-- Every register `roundKeys` writes is one of `kWrites`: checked once
for every instruction, rather than once for every other register. -/
theorem roundKeys_writes : roundKeys.all (fun i => (dstOf i).all kWrites.contains) = true := by
  rw [VG.Proof.CmacTripleDes.Arm.roundKeys_eq]; lit_decide

theorem roundKeys_kept {r : Reg} (hr : r ∉ VG.Proof.CmacTripleDes.Arm.kWrites) : roundKeys.all (fun i => dstOf i != some r) = true :=
  List.all_eq_true.mpr fun i hi => by
    have h := List.all_eq_true.mp VG.Proof.CmacTripleDes.Arm.roundKeys_writes i hi
    cases hd : dstOf i with
    | none => rfl
    | some d =>
      rw [hd, Option.all_some] at h
      have hd' : d ∈ VG.Proof.CmacTripleDes.Arm.kWrites := by simpa using h
      have hne : d ≠ r := fun e => hr (e ▸ hd')
      simpa using hne

/-- The round keys of the DES key in `r0:r1`, in `[r2 + 8 j]` and `[r2 + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok VG.Proof.CmacTripleDes.Arm.kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .r2) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (s.gpr .r0 ++ s.gpr .r1)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .r2) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ VG.Proof.CmacTripleDes.Arm.kWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.CmacTripleDes.Arm.kCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.CmacTripleDes.Arm.roundKeys_check
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr .r0 else s.gpr .r1
  have hrel : Rel (LaneRel 6 (assign W (2 ^ 6))) VG.Proof.CmacTripleDes.Arm.kCfg (linExt 2) (linEnv [(.r0, 0), (.r1, 1)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun j a hj h => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.kCfg])),
      fun _ _ h => by cases h⟩
    simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
    split at h
    · rename_i hr
      simp only [beq_iff_eq] at hr; subst hr
      simp only [Option.some.injEq, exists_eq_left'] at h; subst h
      exact inWord_rel W (i := 0) (by decide)
    · split at h
      · rename_i _ hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel W (i := 1) (by decide)
      · simp at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  have hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .r2) k) 32).getLsbD q = xorBits W (VG.Proof.CmacTripleDes.Arm.rkG k q) := by
    intro k hk q hq
    have h := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at h
    have := outWord_rel (VG.Proof.CmacTripleDes.Arm.rkG_lt k hk) (p.rel.slot k _ (by simp only [VG.Proof.CmacTripleDes.Arm.kCfg]; omega) h)
    rw [p.base] at this
    exact this q hq
  have hx : W 0 ++ W 1 = s.gpr .r0 ++ s.gpr .r1 := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_append, getLsbD_expandDesKey _ hj hq]
    have hs := VG.Proof.CmacTripleDes.Arm.rkSrc_lt j hj q hq
    by_cases h32 : q < 32
    · rw [ite_eq_left h32, hw (2 * j) (by omega) q h32, VG.Proof.CmacTripleDes.Arm.rkG_lo h32, xorBits_cons, xorBits_nil,
        Bool.xor_false, VG.Proof.CmacTripleDes.Arm.bit_xAtom W hs, hx]
    · rw [ite_eq_right h32, BitVec.getLsbD_setWidth, decide_eq_true (by omega : q - 32 < 16), Bool.true_and,
        hw (2 * j + 1) (by omega) (q - 32) (by omega), VG.Proof.CmacTripleDes.Arm.rkG_hi (by omega), show 32 + (q - 32) = q by omega,
        xorBits_cons, xorBits_nil, Bool.xor_false, VG.Proof.CmacTripleDes.Arm.bit_xAtom W hs, hx]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_ushiftRight]
    by_cases hq' : 16 + q < 32
    · rw [hw (2 * j + 1) (by omega) (16 + q) hq', VG.Proof.CmacTripleDes.Arm.rkG_hi0 (by omega)]
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp
  · have h := VG.Proof.CmacTripleDes.Arm.roundKeys_kept hr
    simp [h]

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Init`. -/
section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[88, 112)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldr wp_str wp_rev saveMem saveList_ok sub_beq)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := s₀.gpr .r0
abbrev Kl : Nat := (s₀.gpr .r1).toNat
abbrev O : BitVec 32 := s₀.gpr .r2
abbrev Sc : BitVec 32 := s₀.gpr .r3

abbrev ikeyR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.K s₀), VG.Proof.CmacTripleDes.Arm.Kl s₀⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀), 400⟩
abbrev iscrR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀), 640⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀)) (VG.Proof.CmacTripleDes.Arm.Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀), 52⟩, ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88, 28⟩, VG.Proof.CmacTripleDes.Arm.outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.Arm.ikeyR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.Arm.outR s₀, VG.Proof.CmacTripleDes.Arm.iscrR s₀]
  key_out : (VG.Proof.CmacTripleDes.Arm.ikeyR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.outR s₀)
  key_scr : (VG.Proof.CmacTripleDes.Arm.ikeyR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.iscrR s₀)
  out_scr : (VG.Proof.CmacTripleDes.Arm.outR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.iscrR s₀)
  key_fit : (VG.Proof.CmacTripleDes.Arm.K s₀).toNat + VG.Proof.CmacTripleDes.Arm.Kl s₀ ≤ 2 ^ 32
  out_fit : (VG.Proof.CmacTripleDes.Arm.O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.Arm.Sc s₀).toNat + 640 ≤ 2 ^ 32
  valid : VG.Proof.CmacTripleDes.Arm.Kl s₀ = 16 ∨ VG.Proof.CmacTripleDes.Arm.Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) : VG.Proof.CmacTripleDes.Arm.IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨a, b, c, d, e, f, g, h, i⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀
  r4 : s.gpr .r4 = VG.Proof.CmacTripleDes.Arm.Sc s₀ + BitVec.ofNat 32 (88 + 8 * i)
  r2 : s.gpr .r2 = VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 (128 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (3 - i)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 (88 + 8 * j)) 32 ++
    s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 (92 + 8 * j)) 32 = VG.Proof.CmacTripleDes.Arm.kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀)).getD n 0
  frame : Frame [⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88, 24⟩, ⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀), 384⟩]
    (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀) {j : Nat} (hj : j < 3) : keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) j + 8 ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega))

theorem IPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem IPre.keyAddr {d : Nat} (h : d < VG.Proof.CmacTripleDes.Arm.Kl s₀) :
    State.addr (VG.Proof.CmacTripleDes.Arm.K s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega)

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀) :
    m.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d) 32 = s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) j)) 32) ++
      rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) j + 4)) 32) = VG.Proof.CmacTripleDes.Arm.kw s₀ j := by
  rw [VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq, byteRev32_append, VG.Proof.CmacTripleDes.Arm.kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀) (hd' : d < 4096) (ho : o + 4 ≤ 640)
    (h0 : s.gpr .r0 = VG.Proof.CmacTripleDes.Arm.K s₀) (h10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .r4 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 o)
        (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.ldr .r4 .r0 d :: .rev .r4 .r4 :: .str .r4 .r10 o :: rest)) s Q
  refine wp_ldr hd' (by rw [h0, hp.keyAddr (by omega)]) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_rev fun s₂ u₂ => ?_
  refine wp_str (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h10, hp.scrAddr (by omega)])
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) (by rw [w₃.sp, u₂.sp, u₁.sp]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[88, 112)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 88 ≤ d) (h₂ : d + 4 ≤ 112) :
    (⟨S + BitVec.ofNat 64 88, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 88 + BitVec.ofNat 64 (d - 88) from
    (Offset.add_add_eq _ (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

theorem initPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀) : WP isa initPre s₀ (VG.Proof.CmacTripleDes.Arm.KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (s₀.gpr .r3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  have kl : 16 ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀ := by rcases hp.valid with h | h <;> omega
  rw [show initPre = .seq (.block (saved.map (fun p => Instr.str p.1 .r3 p.2) ++
      (mov .r10 .r3 :: (keyWord 0 88 ++ (keyWord 4 92 ++ (keyWord 8 96 ++ (keyWord 12 100 ++
        ([.cmp .r1 (.imm 16)] : List Instr))))))))
      (.seq (.ite .eq (.block [.ldr .r4 .r0 0, .ldr .r5 .r0 4]) (.block [.ldr .r4 .r0 16, .ldr .r5 .r0 20]))
        (.block [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r10 104, .str .r5 .r10 108,
          .dp .add .r4 .r10 (.imm 88), .mov .r5 (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine VG.Arm.Spill.saveList_ok saved s₀ _ (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb := VG.Proof.CmacTripleDes.Arm.saved_bound p hp'
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have m₂ : s₂.mem = VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀) := by rw [u₂.mem, m₁]; rfl
  have g₂ : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [u₂.other _ hr, g₁]
  have r10₂ : s₂.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by rw [u₂.gpr, g₁]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, rd₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, wr₁]
  have sp₂ : s₂.sp = s₀.sp := by rw [u₂.sp, sp₁]
  have sv : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) := (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.CmacTripleDes.Arm.iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have scrC : ∀ d, d + 4 ≤ 640 → (VG.Proof.CmacTripleDes.Arm.iscrR s₀).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  -- The four words of the first two DES keys.
  refine VG.Proof.CmacTripleDes.Arm.keyWord_wp hp (by omega) (by decide) (by decide) (g₂ _ (by decide)) r10₂ rd₂ wr₂ (by rw [m₂]; exact sv)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  have F₃ : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem s₃.mem := by
    rw [m₃, m₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 88 (by decide))
  refine VG.Proof.CmacTripleDes.Arm.keyWord_wp hp (by omega) (by decide) (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₃ _ (by decide), r10₂]) (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂]) F₃ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  have F₄ : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem s₄.mem := by
    rw [m₄]; exact F₃.writeW (List.mem_singleton_self _) _ (scrC 92 (by decide))
  refine VG.Proof.CmacTripleDes.Arm.keyWord_wp hp (by omega) (by decide) (by decide)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]) (by rw [g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₄, rd₃, rd₂]) (by rw [wr₄, wr₃, wr₂]) F₄ fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  have F₅ : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact F₄.writeW (List.mem_singleton_self _) _ (scrC 96 (by decide))
  refine VG.Proof.CmacTripleDes.Arm.keyWord_wp hp (by omega) (by decide) (by decide)
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)])
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), r10₂])
    (by rw [rd₅, rd₄, rd₃, rd₂]) (by rw [wr₅, wr₄, wr₃, wr₂]) F₅ fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => ?_
  have F₆ : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  have g₆' : ∀ r, r ≠ .r4 → r ≠ .r10 → s₆.gpr r = s₀.gpr r := fun r h4 h10 => by
    rw [g₆ _ h4, g₅ _ h4, g₄ _ h4, g₃ _ h4, g₂ _ h10]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂]
  have sp₆' : s₆.sp = s₀.sp := by rw [sp₆, sp₅, sp₄, sp₃, sp₂]
  refine wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  have r1 : s₀.gpr .r1 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.Kl s₀) := by simp [VG.Proof.CmacTripleDes.Arm.Kl]
  have ev : isa.eval .eq s₇ = some (decide (VG.Proof.CmacTripleDes.Arm.Kl s₀ = 16)) := by
    show some s₇.z = _
    rw [z₇, g₆' _ (by decide) (by decide), r1, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      sub_beq (s₀.gpr .r1).isLt (by decide)]
  -- The third DES key.
  have third : ∀ d, d + 8 ≤ VG.Proof.CmacTripleDes.Arm.Kl s₀ → d + 4 < 4096 →
      WP isa (.block [.ldr .r4 .r0 d, .ldr .r5 .r0 (d + 4)]) s₇ fun s₈ =>
        s₈.gpr .r4 = s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 d) 32 ∧
        s₈.gpr .r5 = s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
        s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp := by
    intro d hd hl
    have r0₇ : s₇.gpr .r0 = VG.Proof.CmacTripleDes.Arm.K s₀ := by rw [f₇.gpr, g₆' _ (by decide) (by decide)]
    refine wp_ldr (by omega) (by rw [r0₇, hp.keyAddr (by omega)])
      (by rw [f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega) (by decide)) fun s₈ u₈ => ?_
    refine wp_ldr (by omega) (by rw [u₈.other _ (by decide), r0₇, hp.keyAddr (by omega)])
      (by rw [u₈.rd, u₈.wr, f₇.rd, f₇.wr, rd₆', wr₆']; exact hp.inKey (by omega) (by decide))
      fun s₉ u₉ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.gpr, f₇.mem, hp.keyRead F₆ (by omega)]
    · rw [u₉.gpr, u₈.mem, f₇.mem, hp.keyRead F₆ (by omega)]
    · rw [u₉.other _ h5, u₈.other _ h4]
    · rw [u₉.mem, u₈.mem, f₇.mem]
    · rw [u₉.rd, u₈.rd, f₇.rd, rd₆']
    · rw [u₉.wr, u₈.wr, f₇.wr, wr₆']
    · rw [u₉.sp, u₈.sp, f₇.sp, sp₆']
  refine WP.seq (WP.mono (Q := fun (s₈ : State) =>
      s₈.gpr .r4 = s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2)) 32 ∧
      s₈.gpr .r5 = s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₈.gpr r = s₇.gpr r) ∧ s₈.mem = s₆.mem ∧ s₈.rd = s₀.rd ∧
      s₈.wr = s₀.wr ∧ s₈.sp = s₀.sp) ?_ fun s₈ h₈ => ?_)
  · by_cases h16 : VG.Proof.CmacTripleDes.Arm.Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by decide)
      rwa [show keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : VG.Proof.CmacTripleDes.Arm.Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by decide)
      rwa [show keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₄, ax₅, g₈, m₈, rd₈, wr₈, sp₈⟩ := h₈
  have r10₈ : s₈.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by
    rw [g₈ _ (by decide) (by decide), f₇.gpr, g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      g₃ _ (by decide), r10₂]
  refine wp_rev fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  have r10₁₀ : s₁₀.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), r10₈]
  refine wp_str (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 104) (by decide) (by rw [r10₁₀, hp.scrAddr (by decide)])
    (by rw [u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_str (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 108) (by decide)
    (by rw [w₁₁.gpr, r10₁₀, hp.scrAddr (by decide)])
    (by rw [w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]; exact hp.inScr (by decide) (by decide)) fun s₁₂ w₁₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₁₃ u₁₃ => wp_mov (op2_imm (by decide)) fun s₁₄ u₁₄ => WP.block_nil ?_
  have mem₁₄ : s₁₄.mem = ((((((VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)).writeW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88)
      (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 0) 32))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 92) (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 4) 32))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 96) (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 8) 32))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 100)
        (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 12) 32))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 104)
        (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2)) 32))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 108)
        (rev (s₀.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.K s₀) + BitVec.ofNat 64 (keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 2 + 4)) 32)) := by
    rw [u₁₄.mem, u₁₃.mem, w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .r4 (by decide), u₉.gpr,
      u₁₀.mem, u₉.mem, u₉.other .r5 (by decide), ax₄, ax₅, m₈, m₆, m₅, m₄, m₃, m₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, r10₁₀]
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, w₁₂.gpr, w₁₁.gpr, r10₁₀]; rfl
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), g₈ _ (by decide) (by decide), f₇.gpr, g₆' _ (by decide) (by decide), VG.Proof.CmacTripleDes.Arm.add0]
  · rw [u₁₄.gpr]; rfl
  · rw [u₁₄.sp, u₁₃.sp, w₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, sp₈]
  · rw [u₁₄.rd, u₁₃.rd, w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, rd₈]
  · rw [u₁₄.wr, u₁₃.wr, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  · rw [mem₁₄, ← VG.Proof.CmacTripleDes.Arm.kw_eq (s₀ := s₀) j]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [VG.Proof.CmacTripleDes.Arm.readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (VG.Proof.CmacTripleDes.Arm.Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [VG.Proof.CmacTripleDes.Arm.readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [VG.Proof.CmacTripleDes.Arm.readW_writeW_far, Mem.readW_writeW_self32]
  · rw [mem₁₄]
    have c : ∀ d, 88 ≤ d → d + 4 ≤ 112 → (⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88, 24⟩ : Region).Contains
        (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => VG.Proof.CmacTripleDes.Arm.keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 88 (by decide) (by decide))).writeW (by simp) _
      (c 92 (by decide) (by decide))).writeW (by simp) _ (c 96 (by decide) (by decide))).writeW (by simp) _
      (c 100 (by decide) (by decide))).writeW (by simp) _ (c 104 (by decide) (by decide))).writeW (by simp) _
      (c 108 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : VG.Proof.CmacTripleDes.Arm.KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => VG.Proof.CmacTripleDes.Arm.KInv s₀ (i + 1) s' ∧ s'.z = decide (3 - (i + 1) = 0) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  have rdwr : s.rd ++ s.wr = [VG.Proof.CmacTripleDes.Arm.ikeyR s₀, VG.Proof.CmacTripleDes.Arm.outR s₀, VG.Proof.CmacTripleDes.Arm.iscrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have scrIn : ∀ d, d + 4 ≤ 640 → InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.iscrR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  rw [keysBody, List.append_assoc]
  refine wp_ldr (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 (88 + 8 * i)) (by decide)
    (by rw [h.r4, VG.Proof.CmacTripleDes.Arm.add0, hp.scrAddr (by omega)]) (scrIn _ (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 (92 + 8 * i)) (by decide)
    (by rw [u₁.other _ (by decide), h.r4, Straight.add_ofNat_ofNat, hp.scrAddr (by omega),
      show 88 + 8 * i + 4 = 92 + 8 * i by omega])
    (by rw [u₁.rd, u₁.wr]; exact scrIn _ (by omega)) fun s₂ u₂ => ?_
  have ax₂ : s₂.gpr .r0 ++ s₂.gpr .r1 = VG.Proof.CmacTripleDes.Arm.kw s₀ i := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, h.keys i hi]
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s.gpr r := fun r h0 h1 => by rw [u₂.other _ h1, u₁.other _ h0]
  have r2₂ : s₂.gpr .r2 = VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 (128 * i) := by rw [g₂ _ (by decide) (by decide), h.r2]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  have oA : State.addr (VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 (128 * i)) = State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (128 * i) :=
    addr_add (by omega)
  have r2n : (VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (VG.Proof.CmacTripleDes.Arm.O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have wA : ∀ k < 32, wordAddr (s₂.gpr .r2) k = State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by
      rw [r2₂, VG.Proof.CmacTripleDes.Arm.wordAddr_eq _ (by rw [r2n]; omega), oA, Offset.add_add]
  have hok : Ok VG.Proof.CmacTripleDes.Arm.kCfg s₂ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.kCfg]), ?_, fun k _ j hj => absurd hj (by simp [VG.Proof.CmacTripleDes.Arm.kCfg])⟩
    · rw [show kCfg.base = .r2 from rfl, wA k hk, wr₂]
      exact hp.inOut (by simp only [VG.Proof.CmacTripleDes.Arm.kCfg] at hk; omega) (by decide)
    · show (s₂.gpr .r2).toNat + 4 * 32 ≤ 2 ^ 32
      rw [r2₂, r2n]; omega
  obtain ⟨s₃, run₃, rk₃, hi₃, rd₃, wr₃, sp₃, g₃, f₃⟩ := VG.Proof.CmacTripleDes.Arm.roundKeys_ok hok
  show WP isa (.block (roundKeys ++ ([.dp .add .r2 .r2 (.imm 128), .dp .add .r4 .r4 (.imm 8),
    .subs .r5 .r5 (.imm 1)] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have gk : ∀ r, r ∉ VG.Proof.CmacTripleDes.Arm.kWrites → r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s.gpr r := fun r hk h0 h1 => by
    rw [g₃ r hk, g₂ r h0 h1]
  have slotR : slotRegion VG.Proof.CmacTripleDes.Arm.kCfg s₂ = ⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .r2 from rfl, r2₂, oA]; rfl
  rw [slotR, u₂.mem, u₁.mem] at f₃
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have r5₃ : s₃.gpr .r5 = BitVec.ofNat 32 (3 - i) := by rw [gk _ (by decide) (by decide) (by decide), h.r5]
  have dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := VG.Proof.CmacTripleDes.Arm.ofNat_sub_one (by omega) (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      gk _ (by decide) (by decide) (by decide), h.r10]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), gk _ (by decide) (by decide) (by decide), h.r4,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Straight.add_ofNat_ofNat,
      show 88 + 8 * i + 8 = 88 + 8 * (i + 1) by omega]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, gk _ (by decide) (by decide) (by decide), h.r2,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Straight.add_ofNat_ofNat,
      show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, dec]
  · rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [m₆, ← h.keys j hj]
    have keep : ∀ d, 88 ≤ d → d + 4 ≤ 112 → s₃.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) 32 =
        s.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ => by
      rw [f₃.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (Offset.sub_base _ (by omega)))
        (by decide)]
    rw [keep _ (by omega) (by omega), keep _ (by omega) (by omega)]
  · rw [m₆]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₃.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := VG.Proof.CmacTripleDes.Arm.keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega,
        ← wA (2 * j + 1) (by omega), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega, ← wA (2 * j) (by omega),
        append_of_hi _ _ (hi₃ j hj), rk₃ j hj, ax₂, VG.Proof.CmacTripleDes.Arm.kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₆]
    exact h.frame.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀), 384⟩, by simp, Offset.sub_base _ (by omega)⟩)
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), r5₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    simp only [decide_eq_decide]; omega

theorem keys_ok {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.IPre s₀) {s : State} (h : VG.Proof.CmacTripleDes.Arm.KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (VG.Proof.CmacTripleDes.Arm.KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := VG.Proof.CmacTripleDes.Arm.KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ VG.Proof.CmacTripleDes.Arm.KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [VG.Proof.CmacTripleDes.Arm.eval_ne, z']; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `r0:r1` and stores it, as bytes, at `[r2 + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop} (hd : d + 4 < 4096)
    (ha : State.addr (s.gpr .r2 + BitVec.ofNat 32 d) = a)
    (ha4 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (d + 4)) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .r0 ++ s'.gpr .r1 = dbl64 (s.gpr .r0 ++ s.gpr .r1) →
      s'.mem = (s.mem.writeW a (rev (s'.gpr .r0))).writeW (a + BitVec.ofNat 64 4) (rev (s'.gpr .r1)) →
      (∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .r3 (.shifted .r0 .lsr 31) :: .mov .r4 (.imm 0) :: .dp .sub .r3 .r4 (.reg .r3) ::
    .dp .and .r3 .r3 (.imm 0x1b) :: .mov .r4 (.shifted .r1 .lsr 31) :: .mov .r0 (.shifted .r0 .lsl 1) ::
    .dp .orr .r0 .r0 (.reg .r4) :: .mov .r1 (.shifted .r1 .lsl 1) :: .dp .eor .r1 .r1 (.reg .r3) ::
    .rev .r3 .r0 :: .str .r3 .r2 d :: .rev .r3 .r1 :: .str .r3 .r2 (d + 4) :: rest)) s Q
  refine wp_mov (op2_lsr (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_sub (op2_reg _ _) fun s₃ u₃ => wp_and (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_lsr (by decide)) fun s₅ u₅ => wp_mov (op2_lsl (by decide)) fun s₆ u₆ =>
    wp_orr (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ =>
    VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ => ?_
  have g₁₀ : ∀ r, r ∉ [Reg.r0, .r1, .r3, .r4] → s₁₀.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₀.other _ hr.2.2.1, u₉.other _ hr.2.1, u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.1,
      u₅.other _ hr.2.2.2, u₄.other _ hr.2.2.1, u₃.other _ hr.2.2.1, u₂.other _ hr.2.2.2, u₁.other _ hr.2.2.1]
  have m₁₀ : s₁₀.mem = s.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have wr₁₀ : s₁₀.wr = s.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r2₁₀ : s₁₀.gpr .r2 = s.gpr .r2 := g₁₀ _ (by decide)
  refine wp_str (by omega) (by rw [r2₁₀, ha]) (by rw [wr₁₀]; exact w0) fun s₁₁ w₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  refine wp_str (by omega) (by rw [u₁₂.other _ (by decide), w₁₁.gpr, r2₁₀, ha4])
    (by rw [u₁₂.wr, w₁₁.wr, wr₁₀]; exact w4) fun s₁₃ w₁₃ => ?_
  have r0f : s₁₃.gpr .r0 = s₉.gpr .r0 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  have r1f : s₁₃.gpr .r1 = s₉.gpr .r1 := by
    rw [w₁₃.gpr, u₁₂.other _ (by decide), w₁₁.gpr, u₁₀.other _ (by decide)]
  refine k s₁₃ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_
  · have a3 : s₈.gpr .r3 = ((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr]
    have a0 : s₉.gpr .r0 = s.gpr .r0 <<< 1 ||| s.gpr .r1 >>> 31 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.gpr,
        u₅.other _ (by decide), u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        u₁.other _ (by decide)]
    have a1 : s₉.gpr .r1 = s.gpr .r1 <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .r0 >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₉.gpr, a3, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₃.mem, u₁₂.mem, w₁₁.mem, m₁₀, u₁₂.gpr, w₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), r0f, r1f]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [w₁₃.gpr, u₁₂.other _ hr.2.2.1, w₁₁.gpr, g₁₀ _ (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [w₁₃.rd, u₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₃.wr, u₁₂.wr, w₁₁.wr, wr₁₀]
  · rw [w₁₃.sp, u₁₂.sp, w₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.keys_ok hp h₁) fun s₂ h₂ => ?_)
  have rdwr₂ : s₂.rd ++ s₂.wr = [VG.Proof.CmacTripleDes.Arm.ikeyR s₀, VG.Proof.CmacTripleDes.Arm.outR s₀, VG.Proof.CmacTripleDes.Arm.iscrR s₀] := by rw [h₂.rd, h₂.wr, hp.rd, hp.wr]; rfl
  -- The key schedule is in place.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀)) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  refine WP.seq ?_
  refine wp_str (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [h₂.r10, hp.scrAddr (by decide)])
    (by rw [h₂.wr]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_sub (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have g₆ : ∀ r, r ∉ [Reg.r0, .r1, .r9] → s₆.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2, w₃.gpr]
  have r9₆ : s₆.gpr .r9 = VG.Proof.CmacTripleDes.Arm.O s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, h₂.r2,
      show (384 : BitVec 32) = BitVec.ofNat 32 (128 * 3) from rfl, BitVec.add_sub_cancel]
  have r10₆ : s₆.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by rw [g₆ _ (by decide), h₂.r10]
  have ax₆ : s₆.gpr .r0 ++ s₆.gpr .r1 = (0 : BitVec 64) := by rw [u₆.other _ (by decide), u₅.gpr, u₆.gpr]; rfl
  have m₆ : s₆.mem = s₂.mem.writeW (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112) (VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 384) := by
    rw [u₆.mem, u₅.mem, u₄.mem, w₃.mem, h₂.r2]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, w₃.rd, h₂.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, w₃.wr, h₂.wr]
  have c112 : (VG.Proof.CmacTripleDes.Arm.iscrR s₀).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega)
  have F₆ : Frame [VG.Proof.CmacTripleDes.Arm.iscrR s₀] s₂.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c112
  have outScr : ∀ r ∈ [VG.Proof.CmacTripleDes.Arm.iscrR s₀], (⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀), 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
  have hsch₆ : VG.Proof.CmacTripleDes.Arm.sch s₆ = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₆.mem (State.addr (s₆.gpr .r9)) = _
    rw [r9₆, VG.Proof.CmacTripleDes.Arm.scheduleAt_frame F₆ outScr, hsch₂]
  have bp : VG.Proof.CmacTripleDes.Arm.BlockPre s₆ :=
    { sched := ⟨400, by rw [r9₆, rd₆, wr₆, hp.rd, hp.wr]; simp, by decide, by rw [r9₆]; exact of⟩
      scr := ⟨640, by rw [r10₆, wr₆, hp.wr]; simp, by decide, by rw [r10₆]; exact sf⟩
      disj := by
        rw [r9₆, r10₆]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.block_ok bp) fun s₇ ⟨same₇, r9₇, ax₇⟩ => ?_)
  rw [ax₆, hsch₆] at ax₇
  have r10₇ : s₇.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by rw [same₇.r10, r10₆]
  have xR₆ : VG.Proof.CmacTripleDes.Arm.xR s₆ = ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀), 52⟩ := by rw [VG.Proof.CmacTripleDes.Arm.xR, r10₆]
  have f₇ : Frame [⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀), 52⟩] s₆.mem s₇.mem := by rw [← xR₆]; exact same₇.frame
  have wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  have rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  show WP isa (.block (.ldr .r2 .r10 112 :: (dbl 0 ++ (dbl 8 ++ restore)))) s₇ _
  refine wp_ldr (a := State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112) (by decide) (by rw [r10₇, hp.scrAddr (by decide)])
    (by rw [rd₇, wr₇, hp.rd, hp.wr]
        exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.iscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega))) fun s₈ u₈ => ?_
  have r2₈ : s₈.gpr .r2 = VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 384 := by
    rw [u₈.gpr, f₇.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega)) (by decide), m₆, Mem.readW_writeW_self32]
  have oA : ∀ d, d < 16 → State.addr (VG.Proof.CmacTripleDes.Arm.O s₀ + BitVec.ofNat 32 384 + BitVec.ofNat 32 d) =
      State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [Straight.add_ofNat_ofNat, addr_add (by omega)]
  have wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, wr₇]; exact hp.inOut (by omega) (by decide)
  have a4 : ∀ d, State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine VG.Proof.CmacTripleDes.Arm.dbl_wp (a := State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + 0)) (by decide) (by rw [r2₈, oA 0 (by decide)])
    (by rw [r2₈, oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ sp₉ => ?_
  refine VG.Proof.CmacTripleDes.Arm.dbl_wp (a := State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + 8)) (by decide)
    (by rw [g₉ _ (by decide), r2₈, oA 8 (by decide)]) (by rw [g₉ _ (by decide), r2₈, oA 12 (by decide), a4])
    (by rw [wr₉]; exact wO 8 (by decide)) (by rw [wr₉, a4]; exact wO 12 (by decide))
    fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ sp₁₀ => ?_
  have r10₁₀ : s₁₀.gpr .r10 = VG.Proof.CmacTripleDes.Arm.Sc s₀ := by rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), r10₇]
  have rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [VG.Proof.CmacTripleDes.Arm.ikeyR s₀, VG.Proof.CmacTripleDes.Arm.outR s₀, VG.Proof.CmacTripleDes.Arm.iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, same₇.rd, same₇.wr, u₆.rd, u₅.rd, u₄.rd, w₃.rd, u₆.wr, u₅.wr, u₄.wr,
      w₃.wr, rdwr₂]
  -- What changed since the registers were saved.
  have oC : ∀ d, d + 4 ≤ 16 → (VG.Proof.CmacTripleDes.Arm.outR s₀).Contains (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega) (by omega)
  have F₁₀ : Frame (VG.Proof.CmacTripleDes.Arm.ichg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) s₁₀.mem := by
    have F₂ : Frame (VG.Proof.CmacTripleDes.Arm.ichg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88, 28⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨VG.Proof.CmacTripleDes.Arm.outR s₀, by simp, Region.sub_prefix (by decide)⟩
    have F₆' : Frame (VG.Proof.CmacTripleDes.Arm.ichg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) s₆.mem := by
      rw [m₆]
      refine F₂.writeW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88, 28⟩) (by simp) _ ?_
      rw [show State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 112 = State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 88 +
        BitVec.ofNat 64 (112 - 88) from (Offset.add_add_eq _ (by omega)).symm]
      exact Offset.contains_base _ (by decide) (by decide)
    have F₇ : Frame (VG.Proof.CmacTripleDes.Arm.ichg s₀) (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.Sc s₀)) s₇.mem :=
      F₆'.trans (f₇.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, a4, a4]
    exact (((F₇.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.restore_ok r10₁₀ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.iscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨VG.Proof.CmacTripleDes.Arm.restored (S := VG.Proof.CmacTripleDes.Arm.Sc s₀) (fun d h₁' h₂' => ?_) hl ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.Sc s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega))).symm
  · rw [sp', sp₁₀, sp₉, u₈.sp, same₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, h₂.sp]
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀)) = Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀)
    rw [m', ← hsch₂]
    refine VG.Proof.CmacTripleDes.Arm.scheduleAt_frame (rs := [VG.Proof.CmacTripleDes.Arm.iscrR s₀, ⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
      rw [m₁₀, m₉, u₈.mem, a4, a4]
      exact ((((F₆.mono (by simp)).trans (f₇.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.CmacTripleDes.Arm.iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide)) |>.writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.CmacTripleDes.Arm.O s₀) + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (VG.Proof.CmacTripleDes.Arm.keyB s₀))) 8).2
    rw [subkeys_tdes, m', bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem]
    simp (disch := decide) only [Offset.add_add, VG.Proof.CmacTripleDes.Arm.readW_writeW_far, Mem.readW_writeW_self32]
    rw [VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .r0 (by decide), u₈.other .r1 (by decide), ax₇]

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Finalize`. -/
section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize`, the last block

Untrusted: everything here is checked by Lean. The steps that form the last
block `Mₙ` (§6.2 step 4) in `r4:r5` as little-endian words (`BPost`):
`Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a byte at a time
onto the zeroed bytes `[124, 132)` of the scratch buffer, `0x80` after it,
XORed with `K2`.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldrSp wp_ldr
  wp_str wp_rev wp_ldrb wp_strb saveMem saveList_ok cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev FW : BitVec 32 := s₀.gpr .r0
abbrev FSt : BitVec 32 := s₀.gpr .r1
abbrev FP : BitVec 32 := s₀.gpr .r2
abbrev FL : Nat := (s₀.gpr .r3).toNat
abbrev FS : BitVec 32 := stackArg s₀ 0

abbrev keyR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀), 400⟩
abbrev fstR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀), 8⟩
abbrev lastR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀), VG.Proof.CmacTripleDes.Arm.FL s₀⟩
abbrev fscrR : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀), 640⟩
abbrev fargsR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.CmacTripleDes.Arm.keyR s₀, VG.Proof.CmacTripleDes.Arm.lastR s₀, VG.Proof.CmacTripleDes.Arm.fargsR s₀]
  wr : s₀.wr = [VG.Proof.CmacTripleDes.Arm.fstR s₀, VG.Proof.CmacTripleDes.Arm.fscrR s₀]
  key_st : (VG.Proof.CmacTripleDes.Arm.keyR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fstR s₀)
  key_scr : (VG.Proof.CmacTripleDes.Arm.keyR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fscrR s₀)
  last_st : (VG.Proof.CmacTripleDes.Arm.lastR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fstR s₀)
  last_scr : (VG.Proof.CmacTripleDes.Arm.lastR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fscrR s₀)
  st_scr : (VG.Proof.CmacTripleDes.Arm.fstR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fscrR s₀)
  st_args : (VG.Proof.CmacTripleDes.Arm.fstR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fargsR s₀)
  scr_args : (VG.Proof.CmacTripleDes.Arm.fscrR s₀).Disjoint (VG.Proof.CmacTripleDes.Arm.fargsR s₀)
  key_fit : (VG.Proof.CmacTripleDes.Arm.FW s₀).toNat + 400 ≤ 2 ^ 32
  st_fit : (VG.Proof.CmacTripleDes.Arm.FSt s₀).toNat + 8 ≤ 2 ^ 32
  last_fit : (VG.Proof.CmacTripleDes.Arm.FP s₀).toNat + VG.Proof.CmacTripleDes.Arm.FL s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.CmacTripleDes.Arm.FS s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32
  len : VG.Proof.CmacTripleDes.Arm.FL s₀ ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : VG.Proof.CmacTripleDes.Arm.FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- The bytes where a partial last block is formed. -/
abbrev mnR (s₀ : State) : Region := ⟨State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀) + BitVec.ofNat 64 124, 8⟩

/-- What the first block leaves. -/
structure P1 (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.FS s₀
  r9 : s.gpr .r9 = VG.Proof.CmacTripleDes.Arm.FW s₀
  r1 : s.gpr .r1 = VG.Proof.CmacTripleDes.Arm.FSt s₀
  r2 : s.gpr .r2 = VG.Proof.CmacTripleDes.Arm.FP s₀
  r3 : s.gpr .r3 = s₀.gpr .r3
  sp : s.sp = s₀.sp
  mem : s.mem = VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the branch on the length leaves: `Mₙ` in `r4:r5`. -/
structure BPost (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = VG.Proof.CmacTripleDes.Arm.FS s₀
  r9 : s.gpr .r9 = VG.Proof.CmacTripleDes.Arm.FW s₀
  r1 : s.gpr .r1 = VG.Proof.CmacTripleDes.Arm.FSt s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.CmacTripleDes.Arm.mnR s₀] (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) s.mem
  blk : le8 (s.gpr .r5 ++ s.gpr .r4) = VG.Proof.CmacTripleDes.Arm.mn s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀)) (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀)

section
variable {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.FPre s₀)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fscrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.keyR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ VG.Proof.CmacTripleDes.Arm.FL s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.lastR s₀) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

theorem FPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem FPre.keyAddr {d : Nat} (h : d < 400) :
    State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀ + BitVec.ofNat 32 d) = State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega)

theorem FPre.arg_in : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fargsR s₀) (by simp) (Region.contains_self _ _)

/-- Saving the registers leaves the key unchanged. -/
theorem FPre.keyBytes {d : Nat} (h : d + 8 ≤ 400) :
    Spec.Aes.bytesAt (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 d) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 d) 8 :=
  bytesAt_frame (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))) (by decide)

theorem FPre.lastBytes :
    Spec.Aes.bytesAt (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀) :=
  bytesAt_frame (VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))) (by have := hp.len; omega)

end

/-! ## The prologue -/

theorem fpre1_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.FPre s₀) :
    WP isa (.block (([.ldrSp .r12 0] : List Instr) ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)))
      s₀ fun s => VG.Proof.CmacTripleDes.Arm.P1 s₀ s ∧ s.z = decide (VG.Proof.CmacTripleDes.Arm.FL s₀ = 8) := by
  have hsc := hp.scr_fit
  have hL := hp.len
  rw [show [Instr.ldrSp .r12 0] ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr) =
    .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.CmacTripleDes.Arm.FS s₀ := u₁.gpr
  refine VG.Arm.Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := VG.Proof.CmacTripleDes.Arm.saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  have hm₂ : s₂.mem = VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀) := by
    rw [m₂, u₁.mem, h12, VG.Proof.CmacTripleDes.Arm.savedMem]
    exact VG.Arm.Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (VG.Proof.CmacTripleDes.Arm.saved_ne_r12 p hp')
  simp only [mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₅.gpr, u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide),
      show s₀.gpr .r3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.FL s₀) by simp [VG.Proof.CmacTripleDes.Arm.FL], show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      MdStream.Arm.sub_beq (by omega) (by decide)]

/-! ## A complete last block -/

theorem full_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.FPre s₀) (hL : VG.Proof.CmacTripleDes.Arm.FL s₀ = 8) {s : State} (h : VG.Proof.CmacTripleDes.Arm.P1 s₀ s) :
    WP isa (.block full) s (VG.Proof.CmacTripleDes.Arm.BPost s₀) := by
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  simp only [full]
  refine wp_ldr (by decide) (by rw [h.r2, VG.Proof.CmacTripleDes.Arm.add0]) (by rw [hrw]; simpa using hp.inLast (d := 0) (n := 4) (by omega) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.other _ (by decide), h.r2]; exact addr_add (by omega))
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.inLast (d := 4) (n := 4) (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9,
      hp.keyAddr (by decide)])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₅ u₅ => VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.2, u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  have mem : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [g _ (by decide), h.r10], by rw [g _ (by decide), h.r9], by rw [g _ (by decide), h.r1],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [mem, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [u₆.gpr, u₆.other .r4 (by decide), u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr,
    u₄.other .r4 (by decide), u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide),
    u₃.other .r5 (by decide), u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 388 = State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 384 4).symm, ← readW64_split, h.mem, le8_xor, le8_readW, le8_readW,
    hp.keyBytes (by decide)]
  have lb := hp.lastBytes
  rw [hL] at lb
  rw [lb]
  simp only [VG.Proof.CmacTripleDes.Arm.mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
  exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem eval_ne' (s : State) : isa.eval .ne s = some !s.z := rfl

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 8)
    (h7 : s.gpr .r7 = p) (h6 : s.gpr .r6 = c) (h8 : s.gpr .r8 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 8 ≤ 2 ^ 32)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (State.addr c + BitVec.ofNat 64 i) 1)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 8⟩) :
    WP isa copy s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r4 .r7 0, .strb .r4 .r6 0, .dp .add .r7 .r7 (.imm 1),
      .dp .add .r6 .r6 (.imm 1), .subs .r8 .r8 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r7 = p + BitVec.ofNat 32 i ∧
      t.gpr .r6 = c + BitVec.ofNat 32 i ∧ t.gpr .r8 = BitVec.ofNat 32 (L - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; exact (BitVec.add_zero p).symm, by rw [h6]; exact (BitVec.add_zero c).symm,
      by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x7, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x6, BitVec.add_zero, aC]) (by rw [u₁.wr, wr]; exact hw i (by omega))
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (VG.WriteBytes.writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = VG.WriteBytes.writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, VG.Proof.CmacTripleDes.Arm.byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have x8' : t₅.gpr .r8 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    rw [VG.Proof.CmacTripleDes.Arm.eval_ne', z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      VG.Proof.CmacTripleDes.Arm.ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t₅.gpr r = s.gpr r := fun r h₄ h₆ h₇ h₈ => by
    rw [u₅.other _ h₈, u₄.other _ h₆, u₃.other _ h₇, v₂.gpr, u₁.other _ h₄, g r h₄ h₆ h₇ h₈]
  have x6' : t₅.gpr .r6 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x7' : t₅.gpr .r7 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x7', x6', x8', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.FPre s₀) (hL : VG.Proof.CmacTripleDes.Arm.FL s₀ < 8) {s : State} (h : VG.Proof.CmacTripleDes.Arm.P1 s₀ s) :
    WP isa partialBlock s (VG.Proof.CmacTripleDes.Arm.BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  let C : Addr := State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀) + BitVec.ofNat 64 124
  have hC : State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 124) = C := hp.scrAddr (by decide)
  have hC4 : State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 128) = C + BitVec.ofNat 64 4 := by
    rw [hp.scrAddr (by decide)]; exact (Offset.add_add _ 124 4).symm
  have cIn : ∀ i < 8, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [Offset.add_add]; exact hp.inScr (by omega) (by decide)
  -- Zero the bytes.
  refine WP.seq ?_
  simp only [zero, mov]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (by decide) (by rw [u₁.other _ (by decide), h.r10, hC])
    (by rw [u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₂ w₂ => ?_
  refine wp_str (by decide) (by rw [w₂.gpr, u₁.other _ (by decide), h.r10, hC4])
    (by rw [w₂.wr, u₁.wr, h.wr]; rw [Offset.add_add]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _)
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  let m₁ := ((VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
  have mem₇ : s₇.mem = m₁ := by
    rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, w₃.mem, w₂.mem, w₂.gpr, u₁.gpr, u₁.mem, h.mem]
  have g₇ : ∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other _ hr.2.2.2, u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, w₃.gpr, w₂.gpr, u₁.other _ hr.1]
  have r6₇ : s₇.gpr .r6 = VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 124 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r10]; rfl
  have r7₇ : s₇.gpr .r7 = VG.Proof.CmacTripleDes.Arm.FP s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r2]
  have r8₇ : s₇.gpr .r8 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.FL s₀) := by
    rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r3]; simp [VG.Proof.CmacTripleDes.Arm.FL]
  have z7 : s₇.z = decide (VG.Proof.CmacTripleDes.Arm.FL s₀ = 0) := by
    rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr,
      u₁.other _ (by decide), h.r3, show s₀.gpr .r3 = BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.FL s₀) by simp [VG.Proof.CmacTripleDes.Arm.FL]]
    exact cmp0 (by omega)
  have rd₇ : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, w₃.rd, w₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, w₃.wr, w₂.wr, u₁.wr, h.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, w₂.sp, u₁.sp, h.sp]
  have dPC : (VG.Proof.CmacTripleDes.Arm.lastR s₀).Disjoint ⟨C, 8⟩ := hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have lastM₁ : Spec.Aes.bytesAt m₁ (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀) = Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀) := by
    rw [← hp.lastBytes]
    refine bytesAt_frame (rs := [⟨C, 8⟩]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    simpa using Offset.contains_base C (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (t : State) =>
      t.mem = VG.WriteBytes.writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀)) ∧
      t.gpr .r6 = VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 124 + BitVec.ofNat 32 (VG.Proof.CmacTripleDes.Arm.FL s₀) ∧
      (∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → t.gpr r = s.gpr r) ∧
      t.sp = s₀.sp ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr) ?_ fun t ht => ?_)
  · by_cases hL0 : VG.Proof.CmacTripleDes.Arm.FL s₀ = 0
    · refine WP.ite true (by show some s₇.z = _; rw [z7, hL0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₇, hL0]; simp [Spec.Aes.bytesAt, VG.WriteBytes.writeBytes_nil], by rw [r6₇, hL0]; exact (BitVec.add_zero _).symm, g₇, sp₇, rd₇, wr₇⟩
    · refine WP.ite false (by show some s₇.z = _; rw [z7]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (VG.Proof.CmacTripleDes.Arm.copy_wp (p := VG.Proof.CmacTripleDes.Arm.FP s₀) (c := VG.Proof.CmacTripleDes.Arm.FS s₀ + BitVec.ofNat 32 124) (by omega) (by omega) r7₇ r6₇ r8₇
        (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (fun i hi => by rw [rd₇, wr₇]; exact hp.inLast (by omega) (by decide))
        (fun i hi => by rw [wr₇, hC]; exact cIn i hi) (by rw [hC]; exact dPC)) ?_
      rintro t ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, mem₇, hC, lastM₁], r6₂, fun r hr => by
        rw [g₂ r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
          (fun h => hr (by simp [h])), g₇ r hr], by rw [sp₂, sp₇], by rw [rd₂, rd₇], by rw [wr₂, wr₇]⟩
  obtain ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩ := ht
  have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀)).length = VG.Proof.CmacTripleDes.Arm.FL s₀ := Proof.Cmac.bytesAt_length _ _ _
  have cL : State.addr (t.gpr .r6 + BitVec.ofNat 32 0) = C + BitVec.ofNat 64 (VG.Proof.CmacTripleDes.Arm.FL s₀) := by
    rw [r6₂, VG.Proof.CmacTripleDes.Arm.add0, Straight.add_ofNat_ofNat, addr_add (by omega)]
    show _ = State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀) + BitVec.ofNat 64 124 + BitVec.ofNat 64 (VG.Proof.CmacTripleDes.Arm.FL s₀)
    rw [Offset.add_add]
  have trw : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂]
  simp only [padK2]
  refine wp_mov (op2_imm (by decide)) fun t₁ v₁ => ?_
  refine wp_strb (by decide) (by rw [v₁.other _ (by decide), cL]) (by rw [v₁.wr, wr₂]; exact cIn _ hL)
    fun t₂ v₂ => ?_
  refine wp_ldr (by decide) (by rw [v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10, hC])
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact VG.Proof.CmacTripleDes.Arm.wr_in (hp.inScr (by decide) (by decide))) fun t₃ v₃ => ?_
  refine wp_ldr (by decide) (by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10,
      hC4])
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw, Offset.add_add]
        exact VG.Proof.CmacTripleDes.Arm.wr_in (hp.inScr (by decide) (by decide))) fun t₄ v₄ => ?_
  refine wp_ldr (by decide) (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide),
      g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact hp.inKey (by decide) (by decide))
    fun t₅ v₅ => ?_
  refine wp_ldr (by decide) (by rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr,
      v₁.other _ (by decide), g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]
        exact hp.inKey (by decide) (by decide)) fun t₆ v₆ => ?_
  refine VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun t₇ v₇ => VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun t₈ v₈ => WP.block_nil ?_
  let m₃ := (VG.WriteBytes.writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀))).writeW
    (C + BitVec.ofNat 64 (VG.Proof.CmacTripleDes.Arm.FL s₀)) (0x80 : Byte)
  have mem₂ : t₂.mem = m₃ := by rw [v₂.mem, v₁.mem, m₂, v₁.gpr, VG.Proof.CmacTripleDes.Arm.b80]
  have g₈ : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8] → t₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₈.other _ hr.2.1, v₇.other _ hr.1, v₆.other _ hr.2.2.2.1, v₅.other _ hr.2.2.1, v₄.other _ hr.2.1,
      v₃.other _ hr.1, v₂.gpr, v₁.other _ hr.1, g₂ r (by simp [hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  -- The frame.
  have cR : ∀ d n, d + n ≤ 8 → (VG.Proof.CmacTripleDes.Arm.mnR s₀).Contains (C + BitVec.ofNat 64 d) n := fun d n h =>
    Offset.contains_base _ h (by omega)
  have fr : Frame [VG.Proof.CmacTripleDes.Arm.mnR s₀] (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)) m₃ := by
    refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (cR 4 4 (by decide))).trans (VG.WriteBytes.writeBytes_frame _ _ _ ?_)).writeW (List.mem_singleton_self _) _
      (cR _ 1 (by omega))
    · simpa using cR 0 4 (by decide)
    · rw [hlen]; simpa using cR 0 (VG.Proof.CmacTripleDes.Arm.FL s₀) (by omega)
  -- The block.
  have kD : (⟨State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint (VG.Proof.CmacTripleDes.Arm.mnR s₀) :=
    (hp.key_scr.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
  have k2 : Spec.Aes.bytesAt m₃ (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392) 8 := by
    rw [bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
      hp.keyBytes (by decide)]
  have pad : Spec.Aes.bytesAt m₃ C 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀) ++ [0x80] ++ Spec.Cmac.zeros (8 - VG.Proof.CmacTripleDes.Arm.FL s₀ - 1) := by
    have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
      rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.Arm.readW_lo_of_hi]; decide
    have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FP s₀)) (VG.Proof.CmacTripleDes.Arm.FL s₀)) (by rw [hlen]; exact hL) hz
    rw [hlen] at this
    exact this
  refine ⟨by rw [g₈ _ (by decide), h.r10], by rw [g₈ _ (by decide), h.r9], by rw [g₈ _ (by decide), h.r1],
    by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp₂],
    by rw [v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₂],
    by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₂],
    by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, mem₂]; exact fr, ?_⟩
  rw [v₈.gpr, v₈.other .r4 (by decide), v₇.gpr, v₇.other .r5 (by decide), v₇.other .r7 (by decide), v₆.gpr,
    v₆.other .r4 (by decide), v₆.other .r5 (by decide), v₆.other .r6 (by decide), v₅.gpr, v₅.other .r4 (by decide),
    v₅.other .r5 (by decide), v₄.gpr, v₄.other .r4 (by decide), v₃.gpr, v₅.mem, v₄.mem, v₃.mem, mem₂,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 396 = State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 392 4).symm, ← readW64_split, le8_xor, le8_readW, le8_readW, pad, k2]
  simp only [VG.Proof.CmacTripleDes.Arm.mn, Spec.Cmac.lastBlock, hlen, show VG.Proof.CmacTripleDes.Arm.FL s₀ ≠ 8 by omega, ite_false]
  exact Proof.Cmac.xor_comm _ _

theorem finPre_wp {s₀ : State} (hp : VG.Proof.CmacTripleDes.Arm.FPre s₀) : WP isa finPre s₀ (VG.Proof.CmacTripleDes.Arm.BPost s₀) := by
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.fpre1_wp hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  by_cases hL : VG.Proof.CmacTripleDes.Arm.FL s₀ = 8
  · exact WP.ite true (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun _ => VG.Proof.CmacTripleDes.Arm.full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun h => by cases h)
      (fun _ => VG.Proof.CmacTripleDes.Arm.partial_wp hp (by have := hp.len; omega) h₁)

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.CT`. -/
section

/-!
# TDEA-CMAC on ARMv7: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/Arm/Taint.lean`) checks that only the arguments, which are
public, decide branches and addresses. The functions keep their pointers
and counts in words 28–30 of the scratch buffer, the second writable
region: the analysis knows `r10` points at it (copied from `r3` in `init`,
loaded from the stack argument in the others), so the words stored there
through `r10` are public, and stores through other pointers come before
the pointers are stored back.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm
open VG.Proof.MdStream.Arm (addr_toNat)

/-- `init`'s initial taint: the arguments are public; `r2` and `r3` point at
the output and the scratch buffer. -/
def initTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [400, 640], bases := [(.r2, 0), (.r3, 1)] }

/-- `update`'s and `finalize`'s: the arguments are public; `r1` points at
the state, and the stack argument at the scratch buffer. -/
def streamTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [8, 640], bases := [(.r1, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem initTaint_wf {s : State} (h : initArm.pre s) : VG.Arm.Taint.Wf VG.Proof.CmacTripleDes.Arm.initTaint s := by
  have hp := IPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.CmacTripleDes.Arm.initTaint], ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_scr
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.out_fit; have := hp.scr_fit
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [VG.Proof.CmacTripleDes.Arm.initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem streamTaint_wf {s : State} (hwr : s.wr = [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (stackArg s 0), 640⟩])
    (st_scr : Region.Disjoint ⟨State.addr (s.gpr .r1), 8⟩ ⟨State.addr (stackArg s 0), 640⟩)
    (st_args : Region.Disjoint ⟨State.addr (s.gpr .r1), 8⟩ ⟨stackArgAddr s 0, 4⟩)
    (scr_args : Region.Disjoint ⟨State.addr (stackArg s 0), 640⟩ ⟨stackArgAddr s 0, 4⟩)
    (st_fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32) (scr_fit : (stackArg s 0).toNat + 640 ≤ 2 ^ 32)
    (sp_fit : s.sp.toNat + 4 ≤ 2 ^ 32) : VG.Arm.Taint.Wf VG.Proof.CmacTripleDes.Arm.streamTaint s := by
  have e : (⟨State.addr s.sp, 4⟩ : Region) = ⟨stackArgAddr s 0, 4⟩ := by simp [stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hwr, VG.Proof.CmacTripleDes.Arm.streamTaint], ?_, ?_⟩, fun p hp' => ?_, fun _ => ⟨sp_fit, ?_⟩, ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact st_scr
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · simp only [VG.Proof.CmacTripleDes.Arm.streamTaint, List.mem_singleton] at hp'; subst hp'
    simp [VG.Arm.Taint.region, hwr]
  · simp only [VG.Proof.CmacTripleDes.Arm.streamTaint, e, hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact st_args.symm
    · exact scr_args.symm
  · intro p hp'
    simp only [VG.Proof.CmacTripleDes.Arm.streamTaint, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem argByte_eq (s : State) (k : Nat) : VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

/-- Two runs agree on `streamTaint` when they agree on the arguments. -/
theorem streamTaint_agree {s t : State} (hs : VG.Arm.Taint.Wf VG.Proof.CmacTripleDes.Arm.streamTaint s) (ht : VG.Arm.Taint.Wf VG.Proof.CmacTripleDes.Arm.streamTaint t)
    (hws : s.wr = [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (stackArg s 0), 640⟩])
    (hwt : t.wr = [⟨State.addr (t.gpr .r1), 8⟩, ⟨State.addr (stackArg t 0), 640⟩])
    (hsp : s.sp = t.sp) (h0 : s.gpr .r0 = t.gpr .r0) (h1 : s.gpr .r1 = t.gpr .r1) (h2 : s.gpr .r2 = t.gpr .r2)
    (h3 : s.gpr .r3 = t.gpr .r3) (ha : stackArg s 0 = stackArg t 0) : VG.Arm.Taint.Agree VG.Proof.CmacTripleDes.Arm.streamTaint s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp, fun k hk => ?_⟩
  · simp only [VG.Proof.CmacTripleDes.Arm.streamTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hws, hwt, h1, ha]
  · rw [VG.Proof.CmacTripleDes.Arm.argByte_eq, VG.Proof.CmacTripleDes.Arm.argByte_eq, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.CmacTripleDes.Arm.initTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.CmacTripleDes.Arm.initTaint_wf hs, VG.Proof.CmacTripleDes.Arm.initTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [VG.Proof.CmacTripleDes.Arm.initTaint])⟩
  · simp only [VG.Proof.CmacTripleDes.Arm.initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [(IPre.of hs).wr, (IPre.of ht).wr, VG.Proof.CmacTripleDes.Arm.outR, VG.Proof.CmacTripleDes.Arm.outR, VG.Proof.CmacTripleDes.Arm.iscrR, VG.Proof.CmacTripleDes.Arm.iscrR, VG.Proof.CmacTripleDes.Arm.O, VG.Proof.CmacTripleDes.Arm.O, VG.Proof.CmacTripleDes.Arm.Sc, VG.Proof.CmacTripleDes.Arm.Sc, h2, h3]

theorem update_ct : ConstantTime isa updateArm.pre updateArm.pub update := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.CmacTripleDes.Arm.streamTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  have ps := UPre.of hs
  have pt := UPre.of ht
  exact VG.Proof.CmacTripleDes.Arm.streamTaint_agree
    (VG.Proof.CmacTripleDes.Arm.streamTaint_wf ps.wr ps.st_scr ps.st_args ps.scr_args ps.st_fit ps.scr_fit ps.sp_fit)
    (VG.Proof.CmacTripleDes.Arm.streamTaint_wf pt.wr pt.st_scr pt.st_args pt.scr_args pt.st_fit pt.scr_fit pt.sp_fit)
    ps.wr pt.wr hsp h0 h1 h2 h3 ha

theorem finalize_ct : ConstantTime isa finalizeArm.pre finalizeArm.pub finalize := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.CmacTripleDes.Arm.streamTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  have ps := FPre.of hs
  have pt := FPre.of ht
  exact VG.Proof.CmacTripleDes.Arm.streamTaint_agree
    (VG.Proof.CmacTripleDes.Arm.streamTaint_wf ps.wr ps.st_scr ps.st_args ps.scr_args ps.st_fit ps.scr_fit ps.sp_fit)
    (VG.Proof.CmacTripleDes.Arm.streamTaint_wf pt.wr pt.st_scr pt.st_args pt.scr_args pt.st_fit pt.scr_fit pt.sp_fit)
    ps.wr pt.wr hsp h0 h1 h2 h3 ha

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.FinalizeCorrect`. -/
section

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `r4:r5` holds `Mₙ` (`BPost`); the function saves the state pointer,
XORs in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as
the state, the MAC (`macFull_split8`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_str wp_rev)

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  have hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.finPre_wp hp) fun s₁ h₁ => ?_)
  have rdwr₁ : s₁.rd ++ s₁.wr = [VG.Proof.CmacTripleDes.Arm.keyR s₀, VG.Proof.CmacTripleDes.Arm.lastR s₀, VG.Proof.CmacTripleDes.Arm.fargsR s₀, VG.Proof.CmacTripleDes.Arm.fstR s₀, VG.Proof.CmacTripleDes.Arm.fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid]
  refine wp_str (by decide) (by rw [h₁.r10, hp.scrAddr (by decide)]) (by rw [h₁.wr]; exact hp.inScr (by decide) (by decide))
    fun s₂ w₂ => ?_
  refine wp_ldr (by decide) (by rw [w₂.gpr, h₁.r1, VG.Proof.CmacTripleDes.Arm.add0]) (by rw [w₂.rd, w₂.wr]; simpa using stIn 0 (by decide))
    fun s₃ u₃ => ?_
  refine wp_ldr (a := State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.other _ (by decide), w₂.gpr, h₁.r1]; exact addr_add (by omega))
    (by rw [u₃.rd, u₃.wr, w₂.rd, w₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₅ u₅ => VG.Proof.CmacTripleDes.Arm.wp_eor (op2_reg _ _) fun s₆ u₆ => wp_rev fun s₇ u₇ =>
    wp_rev fun s₈ u₈ => WP.block_nil ?_
  have g₈ : ∀ r, r ∉ [Reg.r0, .r1, .r4, .r5, .r6, .r7] → s₈.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₈.other _ hr.2.1, u₇.other _ hr.1, u₆.other _ hr.2.2.2.1, u₅.other _ hr.2.2.1, u₄.other _ hr.2.2.2.2.2,
      u₃.other _ hr.2.2.2.2.1, w₂.gpr]
  let A := State.addr (VG.Proof.CmacTripleDes.Arm.FS s₀)
  have mem₈ : s₈.mem = s₁.mem.writeW (A + BitVec.ofNat 64 112) (VG.Proof.CmacTripleDes.Arm.FSt s₀) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, w₂.mem, h₁.r1]
  have stSep : ∀ d, d + 4 ≤ 8 →
      (s₁.mem.writeW (A + BitVec.ofNat 64 112) (VG.Proof.CmacTripleDes.Arm.FSt s₀)).readW (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 d) 32 =
        s₁.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 d) 32 := fun d hd =>
    Mem.readW_writeW_sep ((hp.st_scr.sub_right (Offset.sub_base _ (by decide))).sub_left
      (Offset.sub_base _ (by omega)) |>.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
  have ax₈ : s₈.gpr .r0 ++ s₈.gpr .r1 =
      byteRev64 ((s₁.gpr .r5 ++ s₁.gpr .r4) ^^^ s₁.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀)) 64) := by
    have e0 := stSep 0 (by decide)
    have e4 := stSep 4 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at e0
    rw [u₈.gpr, u₈.other .r0 (by decide), u₇.gpr, u₇.other .r5 (by decide), u₆.gpr, u₆.other .r4 (by decide),
      u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr, u₄.other .r4 (by decide),
      u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide), u₃.other .r5 (by decide),
      u₃.mem, w₂.mem, w₂.gpr, h₁.r1, e0, e4, VG.Proof.CmacTripleDes.Arm.rev_xor_append, readW64_split s₁.mem]
  have r9₈ : s₈.gpr .r9 = VG.Proof.CmacTripleDes.Arm.FW s₀ := by rw [g₈ _ (by decide), h₁.r9]
  have r10₈ : s₈.gpr .r10 = VG.Proof.CmacTripleDes.Arm.FS s₀ := by rw [g₈ _ (by decide), h₁.r10]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, h₁.rd]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr]
  have bp : VG.Proof.CmacTripleDes.Arm.BlockPre s₈ :=
    { sched := ⟨400, (by rw [r9₈, rd₈, wr₈, hp.rd]; simp), (by decide), (by rw [r9₈]; exact kf)⟩
      scr := ⟨640, (by rw [r10₈, wr₈, hp.wr]; simp), (by decide), (by rw [r10₈]; exact sf)⟩
      disj := by
        rw [r9₈, r10₈]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.Arm.block_ok bp) fun s₉ ⟨same₉, r9₉, ax₉⟩ => ?_)
  have r10₉ : s₉.gpr .r10 = VG.Proof.CmacTripleDes.Arm.FS s₀ := by rw [same₉.r10, g₈ _ (by decide), h₁.r10]
  have xR₈ : VG.Proof.CmacTripleDes.Arm.xR s₈ = ⟨A, 52⟩ := by rw [VG.Proof.CmacTripleDes.Arm.xR, g₈ _ (by decide), h₁.r10]
  have f₉ : Frame [⟨A, 52⟩] s₈.mem s₉.mem := by rw [← xR₈]; exact same₉.frame
  have outBlock : ∀ d, 52 ≤ d → d + 4 ≤ 640 →
      s₉.mem.readW (A + BitVec.ofNat 64 d) 32 = s₈.mem.readW (A + BitVec.ofNat 64 d) 32 := fun d h₁' h₂' =>
    f₉.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have rdwr₉ : s₉.rd ++ s₉.wr = [VG.Proof.CmacTripleDes.Arm.keyR s₀, VG.Proof.CmacTripleDes.Arm.lastR s₀, VG.Proof.CmacTripleDes.Arm.fargsR s₀, VG.Proof.CmacTripleDes.Arm.fstR s₀, VG.Proof.CmacTripleDes.Arm.fscrR s₀] := by
    rw [same₉.rd, same₉.wr, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, w₂.rd, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr,
      u₃.wr, w₂.wr, rdwr₁]
  have wr₉ : s₉.wr = [VG.Proof.CmacTripleDes.Arm.fstR s₀, VG.Proof.CmacTripleDes.Arm.fscrR s₀] := by
    rw [same₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂.wr, h₁.wr, hp.wr]
  rw [WP.block_append_iff]
  refine wp_ldr (by decide) (by rw [r10₉, hp.scrAddr (by decide)])
    (by rw [rdwr₉]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fscrR s₀) (by simp) (Offset.contains_base _ (by decide) (by omega)))
    fun s₁₀ u₁₀ => ?_
  have r2₁₀ : s₁₀.gpr .r2 = VG.Proof.CmacTripleDes.Arm.FSt s₀ := by
    rw [u₁₀.gpr, outBlock 112 (by decide) (by decide), mem₈, Mem.readW_writeW_self32]
  refine wp_rev fun s₁₁ u₁₁ => wp_rev fun s₁₂ u₁₂ => ?_
  have stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₂.wr (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
    exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fstR s₀) (by simp) (Offset.contains_base _ hd (by omega))
  refine wp_str (by decide) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀, VG.Proof.CmacTripleDes.Arm.add0])
    (by simpa using stW 0 (by decide)) fun s₁₃ w₁₃ => ?_
  refine wp_str (a := State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), r2₁₀]; exact addr_add (by omega))
    (by rw [w₁₃.wr]; exact stW 4 (by decide)) fun s₁₄ w₁₄ => WP.block_nil ?_
  have r10₁₄ : s₁₄.gpr .r10 = VG.Proof.CmacTripleDes.Arm.FS s₀ := by
    rw [w₁₄.gpr, w₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), r10₉]
  have mem₁₄ : s₁₄.mem = (s₉.mem.writeW (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀)) (rev (s₉.gpr .r0))).writeW
      (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 4) (rev (s₉.gpr .r1)) := by
    rw [w₁₄.mem, w₁₃.mem, w₁₃.gpr, u₁₂.gpr, u₁₂.other .r0 (by decide), u₁₁.gpr, u₁₂.mem, u₁₁.mem,
      u₁₁.other .r1 (by decide), u₁₀.other .r0 (by decide), u₁₀.other .r1 (by decide), u₁₀.mem]
  have rdwr₁₄ : s₁₄.rd ++ s₁₄.wr = [VG.Proof.CmacTripleDes.Arm.keyR s₀, VG.Proof.CmacTripleDes.Arm.lastR s₀, VG.Proof.CmacTripleDes.Arm.fargsR s₀, VG.Proof.CmacTripleDes.Arm.fstR s₀, VG.Proof.CmacTripleDes.Arm.fscrR s₀] := by
    rw [w₁₄.rd, w₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, w₁₄.wr, w₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, rdwr₉]
  -- The slots of the saved registers.
  have slots : ∀ d, 52 ≤ d → d + 4 ≤ 88 →
      s₁₄.mem.readW (A + BitVec.ofNat 64 d) 32 = (VG.Proof.CmacTripleDes.Arm.savedMem s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    have sd : ∀ e, e + 4 ≤ 8 → Mem.Sep (A + BitVec.ofNat 64 d) (32 / 8) (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀) + BitVec.ofNat 64 e) (32 / 8) :=
      fun e he => (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm.sub_right (Offset.sub_base _ (by omega))
        |>.sep (Region.contains_self _ _) (Region.contains_self _ _)
    have sd0 := sd 0 (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at sd0
    rw [mem₁₄, Mem.readW_writeW_sep (sd 4 (by decide)) (by decide), Mem.readW_writeW_sep sd0 (by decide),
      outBlock d (by omega) (by omega), mem₈, VG.Proof.CmacTripleDes.Arm.readW_writeW_far _ _ _ (by omega) (by decide) (by omega)]
    refine h₁.frame.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.mono (VG.Proof.CmacTripleDes.Arm.restore_ok r10₁₄ (by omega) fun d h₁' h₂' => by
      rw [rdwr₁₄]; exact VG.Proof.CmacTripleDes.Arm.in_rw (r := VG.Proof.CmacTripleDes.Arm.fscrR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega)))
    fun s' ⟨hl, sp', m', _, _⟩ => ⟨VG.Proof.CmacTripleDes.Arm.restored slots hl (by
      rw [sp', w₁₄.sp, w₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, same₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, w₂.sp,
        h₁.sp]), ?_⟩
  intro hk msg hml hne hst
  have scrSub : ∀ r ∈ [VG.Proof.CmacTripleDes.Arm.mnR s₀], ∃ r' ∈ [VG.Proof.CmacTripleDes.Arm.fscrR s₀], Region.Sub r r' := fun r hr => ⟨VG.Proof.CmacTripleDes.Arm.fscrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩
  have F₁ : Frame [VG.Proof.CmacTripleDes.Arm.fscrR s₀] s₀.mem s₁.mem :=
    ((VG.Proof.CmacTripleDes.Arm.savedMem_frame s₀ (VG.Proof.CmacTripleDes.Arm.FS s₀)).sub fun r hr => ⟨VG.Proof.CmacTripleDes.Arm.fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub scrSub)
  have F₈ : Frame [VG.Proof.CmacTripleDes.Arm.fscrR s₀] s₀.mem s₈.mem := by
    rw [mem₈]; exact F₁.writeW (r := VG.Proof.CmacTripleDes.Arm.fscrR s₀) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
  have hS' : VG.Proof.CmacTripleDes.Arm.sch s₈ = Spec.TripleDes.scheduleAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀)) := by
    show Spec.TripleDes.scheduleAt s₈.mem (State.addr (s₈.gpr .r9)) = _
    rw [r9₈]
    exact VG.Proof.CmacTripleDes.Arm.scheduleAt_frame F₈ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  have hst₁ : le8 (s₁.mem.readW (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀)) 64) = Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀)) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  have hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀)))
  have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.Arm.ciphAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀))) 8).1 ++
        (Spec.Cmac.subkeys (VG.Proof.CmacTripleDes.Arm.ciphAt s₀.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀))) 8).2 := by
    rw [show State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 392 =
        State.addr (VG.Proof.CmacTripleDes.Arm.FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, VG.Proof.CmacTripleDes.Arm.ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem (State.addr (VG.Proof.CmacTripleDes.Arm.FSt s₀)) 8 = _
  rw [m', mem₁₄, ← le8_readW, readW64_split, Mem.readW_writeW_self32, VG.Proof.CmacTripleDes.Arm.readW_lo_of_hi, VG.Proof.CmacTripleDes.Arm.rev_eq, VG.Proof.CmacTripleDes.Arm.rev_eq,
    byteRev32_append, ax₉, ax₈, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Implies`. -/
section

/-!
# TDEA-CMAC on ARMv7: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`.

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 400⟩, ⟨0x4000, 640⟩]

theorem init_implies : initArm.Implies (initScratchContract Arm.abi 0) := by
  sig_implies [initScratchContract, initScratchSig, Spec.Cmac.tdesInitPre, Spec.Cmac.tdesInitPost,
    VG.Proof.CmacTripleDes.Arm.initArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat] using VG.Proof.CmacTripleDes.Arm.initSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition (with no
blocks, and the scratch buffer at 0). -/
def updSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0, 640⟩]

theorem update_implies : updateArm.Implies (VG.Proof.CmacTripleDes.updateScratchContract Arm.abi 0) := by
  sig_implies [VG.Proof.CmacTripleDes.updateScratchContract, VG.Proof.CmacTripleDes.updateScratchSig, Spec.Cmac.tdesUpdatePost, VG.Proof.CmacTripleDes.Arm.updateArm,
    Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacTripleDes.Arm.updSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition (with no
last bytes, and the scratch buffer at 0). -/
def finSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0, 640⟩]

theorem finalize_implies : finalizeArm.Implies (VG.Proof.CmacTripleDes.finalizeScratchContract Arm.abi 0) := by
  sig_implies [VG.Proof.CmacTripleDes.finalizeScratchContract, VG.Proof.CmacTripleDes.finalizeScratchSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, VG.Proof.CmacTripleDes.Arm.finalizeArm, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.CmacTripleDes.Arm.finSat

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Verified`. -/
section

/-!
# TDEA-CMAC on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time under this target's contracts (`Contract.lean`), and the shared
contracts with the working space as an argument
(`Proof/CmacTripleDes/Scratch.lean`), which imply them, with no
stack: the functions call nothing, and save our caller's registers in the
scratch buffer.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm

theorem init_verified : Verified Arm.target init (initScratchContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.Arm.init_wp hs) VG.Proof.CmacTripleDes.Arm.init_ct VG.Proof.CmacTripleDes.Arm.init_implies

theorem update_verified : Verified Arm.target update (VG.Proof.CmacTripleDes.updateScratchContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.Arm.update_wp hs) VG.Proof.CmacTripleDes.Arm.update_ct VG.Proof.CmacTripleDes.Arm.update_implies

theorem finalize_verified : Verified Arm.target finalize (VG.Proof.CmacTripleDes.finalizeScratchContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => VG.Proof.CmacTripleDes.Arm.finalize_wp hs) VG.Proof.CmacTripleDes.Arm.finalize_ct VG.Proof.CmacTripleDes.Arm.finalize_implies

end VG.Proof.CmacTripleDes.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.CmacTripleDes.Arm.Frame`. -/
section

/-!
# TDEA-CMAC on ARMv7, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it. Their other arguments are
all in registers. `init`'s working space is its fourth argument, in `r3`: its
frame is the 640 bytes of working space (`Verified.regScratch`). That of
`update` and `finalize` is their fifth, on the stack: their frames hold the
saved registers too, 648 bytes (`Verified.stackScratch`).
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { VG.Proof.CmacTripleDes.Arm.initSat with
                                           wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract Arm.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using VG.Proof.CmacTripleDes.Arm.initFrameSat

/-- A state satisfying `vg_cmac_triple_des_update`'s precondition, without
the working space (and with no blocks). -/
def updFrameSat : State :=
  { VG.Proof.CmacTripleDes.Arm.updSat with
                rd := [⟨0x1000, 384⟩, ⟨0x3000, 0⟩], wr := [⟨0x2000, 8⟩] }

theorem updFrameSat_pre : ∃ s, (Spec.Cmac.tdesUpdateContract Arm.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesUpdateContract, Spec.Cmac.tdesUpdateSig, Spec.Cmac.tdesUpdatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updFrameSat, updSat] using VG.Proof.CmacTripleDes.Arm.updFrameSat

/-- A state satisfying `vg_cmac_triple_des_finalize`'s precondition, without
the working space (and with no last bytes). -/
def finFrameSat : State :=
  { VG.Proof.CmacTripleDes.Arm.finSat with
                rd := [⟨0x1000, 400⟩, ⟨0x3000, 0⟩], wr := [⟨0x2000, 8⟩] }

theorem finFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinalizeContract Arm.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesFinalizeContract, Spec.Cmac.tdesFinalizeSig, Spec.Cmac.tdesFinalizePre,
    Spec.Cmac.tdesFinalizePost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [finFrameSat, finSat] using VG.Proof.CmacTripleDes.Arm.finFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 640 .r3 init)
    (Spec.Cmac.tdesInitContract Arm.abi 640) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre Arm.abi.ptrBits) (post := Spec.Cmac.tdesInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 0) VG.Proof.CmacTripleDes.Arm.init_verified (by decide) (by decide) (by decide) VG.Proof.CmacTripleDes.Arm.initFrameSat_pre

theorem update_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 648 0 update)
    (Spec.Cmac.tdesUpdateContract Arm.abi 648) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost Arm.abi.ptrBits)
    (wa := false) (stack := 0) (m := 0) VG.Proof.CmacTripleDes.Arm.update_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (VG.Proof.CmacTripleDes.updatePost_local _)
    VG.Proof.CmacTripleDes.Arm.updFrameSat_pre

theorem finalize_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 648 0 finalize)
    (Spec.Cmac.tdesFinalizeContract Arm.abi 648) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre Arm.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost Arm.abi.ptrBits)
    (wa := false) (stack := 0) (m := 0) VG.Proof.CmacTripleDes.Arm.finalize_verified (by decide) (by decide) (by decide)
    (by decide) (finalizePre_local _) (VG.Proof.CmacTripleDes.finalizePost_local _) VG.Proof.CmacTripleDes.Arm.finFrameSat_pre

end VG.Proof.CmacTripleDes.Arm

end
