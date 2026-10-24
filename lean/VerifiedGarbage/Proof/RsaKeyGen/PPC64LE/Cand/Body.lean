module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Main
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the body

`bodyMid_ok`: `out` zeroed, then 0 if `rand` is shorter than a candidate, else
`main_ok`. `code_correct`: the whole function, as the contract states its
results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (geFlag)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- `geFlag r5 r27 r24`: `r5 := 1` if `r27 ≥ r24`, else 0. -/
theorem geFlag27_ok {s : State} {x y : Nat} (h27 : s.gpr .r27 = BitVec.ofNat 64 x)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 y) (hx : x < 2 ^ 64) (hy : y < 2 ^ 63) :
    WP isa (.block (geFlag .r5 .r27 .r24)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if y ≤ x then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.r5, .r0] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [geFlag]
  prun [h27, h24, VG.Proof.MillerRabin.PPC64LE.Search.ge_val hx hy]

/-- Too few octets for a candidate. -/
theorem cOp_none {s0 : State} {w : Nat} (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w) (h : ¬ oL s0 ≤ rL s0) :
    cOp s0 = none := by
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega),
    VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_length]; omega)]

theorem bodyMid_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (hT : TabOk s0)
    (hb : Bx s0 s) (hr : Regs s0 s) (sy : s.syms = s0.syms) :
    WP isa (mid trial R.name R.code) s fun u => Bx s0 u ∧ CQ s0 (u.gpr .r3) u.mem := by
  have hp := hb.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have hfo := hp.fo
  obtain ⟨w, hw⟩ : ∃ w, oL s0 = 8 * w := ⟨oL s0 / 8, by simp only [oL]; omega⟩
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  have eR : rL s0 = (PPC64LE.stackArg s0 0).toNat := rfl
  unfold mid
  refine WP.seq (WP.mono_syms (zeroOut_ok (L := oL s0) hr.r23 (by rw [hr.r24, eO, ofNat_toNat64]) (by omega)
    (by omega) (fun i hi => ⟨cO s0, by rw [hb.wr, bodyWr, hp.wr]; simp,
      Offset.contains_base _ (d := i) (by simp only [oL] at hi; omega) (by omega)⟩) (by omega))
    fun t₁ ⟨z₁, o₁, k₁⟩ sy₁ => ?_)
  have c₁ : Ctx s0 t₁ := by
    refine ⟨hb.step k₁.sp k₁.rd k₁.wr ((frame_of_outside (Z := oL s0) o₁ (by omega)).mono (by simp)) (k₁.gpr _ (by decide)),
      (k₁.gpr _ (by decide)).trans hr.r23, (k₁.gpr _ (by decide)).trans hr.r24,
      (k₁.gpr _ (by decide)).trans hr.r25, ?_⟩
    apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
    intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    exact z₁ i h1
  refine WP.seq (WP.mono_syms (geFlag27_ok (x := rL s0) (y := oL s0) ((k₁.gpr _ (by decide)).trans
      (hr.r27.trans (ofNat_toNat64 _).symm)) ((k₁.gpr _ (by decide)).trans (hr.r24.trans (ofNat_toNat64 _).symm))
      (by omega) (by omega))
    fun t₂ ⟨⟨a5, m₂⟩, k₂⟩ sy₂ => ?_)
  have c₂ := c₁.keep k₂ m₂
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) a5) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact finNone_post c₂ (cOp_none hw (by omega) hav)
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    have K := k₁.trans k₂
    exact main_ok D R ⟨c₂, (K.gpr _ (by decide)).trans hr.r21, (K.gpr _ (by decide)).trans hr.r30,
      (K.gpr _ (by decide)).trans hr.r18, (K.gpr _ (by decide)).trans hr.r19, (K.gpr _ (by decide)).trans hr.r26,
      (K.gpr _ (by decide)).trans hr.r27, (K.gpr _ (by decide)).trans hr.r31, (K.gpr _ (by decide)).trans hr.r11,
      hav, sy₂.trans (sy₁.trans sy), hT⟩

/-- The whole function: its results are the contract's. -/
theorem code_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 : State} (h : CIn s0)
    (hT : TabOk s0) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) s0
      fun t => abiPreserved s0 t ∧ CQ s0 (t.gpr .r3) t.mem :=
  code_ok h fun _ hb hr sy => bodyMid_ok D R hT hb hr sy

end VG.Proof.RsaKeyGen.PPC64LE.Cand
