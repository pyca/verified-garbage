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

/-- The body's state, with the registers the entry set. -/
structure BR (s0 s : State) : Prop where
  ctx : Ctx s0 s
  regs : Regs s0 s
  syms : s.syms = s0.syms

theorem BR.keep {s0 s t : State} {rs : List Reg} (h : BR s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hs : t.syms = s.syms)
    (hr : ∀ r ∈ [Reg.r2, .r23, .r24, .r25, .r21, .r30, .r18, .r19, .r26, .r27, .r31, .r11, .r28], r ∉ rs := by decide) :
    BR s0 t :=
  ⟨h.ctx.keep k hm (fun r h' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl | rfl | rfl <;> simp)), ⟨(k.gpr _ (hr _ (by simp))).trans h.regs.r23, (k.gpr _ (hr _ (by simp))).trans h.regs.r24,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r25, (k.gpr _ (hr _ (by simp))).trans h.regs.r21,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r30, (k.gpr _ (hr _ (by simp))).trans h.regs.r18,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r19, (k.gpr _ (hr _ (by simp))).trans h.regs.r26,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r27, (k.gpr _ (hr _ (by simp))).trans h.regs.r31,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r11, (k.gpr _ (hr _ (by simp))).trans h.regs.r28⟩, hs.trans h.syms⟩

theorem zeroS {s0 s : State} (hb : Bx s0 s) (hr : Regs s0 s) (sy : s.syms = s0.syms) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Candidate.zeroOut s (BR s0) := by
  have hp := hb.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have hfo := hp.fo
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  refine WP.mono_syms (zeroOut_ok (L := oL s0) hr.r23 (by rw [hr.r24, eO, ofNat_toNat64]) (by omega)
    (by omega) (fun i hi => ⟨cO s0, by rw [hb.wr, bodyWr, hp.wr]; simp,
      Offset.contains_base _ (d := i) (by simp only [oL] at hi; omega) (by omega)⟩) (by omega))
    fun t₁ ⟨z₁, o₁, k₁⟩ sy₁ => ?_
  have c₁ : Ctx s0 t₁ := by
    refine ⟨hb.step k₁.sp k₁.rd k₁.wr ((frame_of_outside (Z := oL s0) o₁ (by omega)).mono (by simp)) (k₁.gpr _ (by decide)),
      (k₁.gpr _ (by decide)).trans hr.r23, (k₁.gpr _ (by decide)).trans hr.r24,
      (k₁.gpr _ (by decide)).trans hr.r25, ?_⟩
    apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
    intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    exact z₁ i h1
  exact ⟨c₁, ⟨(k₁.gpr _ (by decide)).trans hr.r23, (k₁.gpr _ (by decide)).trans hr.r24,
    (k₁.gpr _ (by decide)).trans hr.r25, (k₁.gpr _ (by decide)).trans hr.r21, (k₁.gpr _ (by decide)).trans hr.r30,
    (k₁.gpr _ (by decide)).trans hr.r18, (k₁.gpr _ (by decide)).trans hr.r19, (k₁.gpr _ (by decide)).trans hr.r26,
    (k₁.gpr _ (by decide)).trans hr.r27, (k₁.gpr _ (by decide)).trans hr.r31, (k₁.gpr _ (by decide)).trans hr.r11,
    (k₁.gpr _ (by decide)).trans hr.r28⟩, sy₁.trans sy⟩

/-- The body's state with the test of `rand`'s length. -/
def BF (s0 s : State) : Prop :=
  BR s0 s ∧ s.gpr .r5 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0)

theorem flagS {s0 s : State} (h : BR s0 s) :
    WP isa (.block (geFlag .r5 .r27 .r24)) s (BF s0) := by
  have hp := h.ctx.bx.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  exact WP.mono_syms (geFlag27_ok (x := rL s0) (y := oL s0) (h.regs.r27.trans (ofNat_toNat64 _).symm)
      (h.regs.r24.trans (ofNat_toNat64 _).symm) (by simp only [rL]; omega) (by simp only [oL]; omega))
    fun t₂ ⟨⟨a5, m₂⟩, k₂⟩ sy₂ => ⟨h.keep k₂ m₂ sy₂, a5⟩

theorem iteS {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (hT : TabOk s0)
    (h : BF s0 s) :
    WP isa (.ite (.zero .d .r5) VG.Impl.RsaKeyGen.PPC64LE.Candidate.finNone
      (VG.Impl.RsaKeyGen.PPC64LE.Candidate.main trial R.name R.code)) s
      fun u => Bx s0 u ∧ CQ s0 (u.gpr .r3) u.mem := by
  obtain ⟨⟨c₂, hr, sy⟩, a5⟩ := h
  have hp := c₂.bx.pre
  obtain ⟨hw, hw4, -⟩ := cw_facts hp
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) a5) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact finNone_post c₂ (cOp_none hw (by omega) hav)
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact main_ok D R ⟨c₂, hr.r21, hr.r30, hr.r18, hr.r19, hr.r26, hr.r27, hr.r31, hr.r11, hav, sy, hT⟩

theorem bodyMid_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (hT : TabOk s0)
    (hb : Bx s0 s) (hr : Regs s0 s) (sy : s.syms = s0.syms) :
    WP isa (mid trial R.name R.code) s fun u => Bx s0 u ∧ CQ s0 (u.gpr .r3) u.mem := by
  unfold mid
  exact WP.seq (WP.mono (zeroS hb hr sy) fun t₁ h₁ => WP.seq (WP.mono (flagS h₁) fun t₂ h₂ => iteS D R hT h₂))

/-- The whole function: its results are the contract's. -/
theorem code_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 : State} (h : CIn s0)
    (hT : TabOk s0) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) s0
      fun t => abiPreserved s0 t ∧ CQ s0 (t.gpr .r3) t.mem :=
  code_ok h fun _ hb hr sy => bodyMid_ok D R hT hb hr sy

end VG.Proof.RsaKeyGen.PPC64LE.Cand
