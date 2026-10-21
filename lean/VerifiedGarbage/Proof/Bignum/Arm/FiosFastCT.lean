module

public import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Bignum.Arm.FiosArgs
import VerifiedGarbage.Proof.Bignum.Arm.FiosCT
import VerifiedGarbage.Proof.Bignum.Arm.FiosTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.FiosFast
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Bignum.Arm.FiosTaint

/-! The fused scan's addresses and branches depend only on public pointers and counts. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm.Fios
open VG.Proof.X25519.Arm (wp_ldr)

private theorem keeping_r0 {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s t, P s t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    {hint : VG.Taint.Hint VG.Arm.Taint.T}
    (hc : ((FiosTaint.analysis.check (Taint.ofRegs rs) c hint).map
      fun τ => (RegSet.ofList [.r0]).subset τ.regs) = some true) :
    RelCT isa P c (fun s t => s.gpr .r0 = t.gpr .r0) := by
  intro s t tr₁ tr₂ u v h ex ey
  obtain ⟨τ, ht, ho⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨trace, final⟩ := VG.Taint.check_sound ht (Taint.agree_ofRegs (hp s t h)) ex ey
  exact ⟨trace, final.rf.1 .r0 (RegSet.mem_of_subset ho (RegSet.mem_ofList.mpr (by simp)))⟩

theorem code_relCT : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .lr = t.gpr .lr)
    VG.Impl.Bignum.Arm.FiosFast.code (fun s t => s.gpr .r0 = t.gpr .r0) := by
  apply keeping_r0 [.r0,.r12,.r4,.lr] ?_ (by taint_decide)
  intro s t h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem round_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t)
      VG.Impl.Bignum.Arm.FiosFast.round (fun _ _ => True) := by
  let P := RoundReady base size tmp a b mod acc n i
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 b ∧ s.gpr .r4 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block VG.Impl.Bignum.Arm.Fios.args)
      (fun _ _ => True) := args_ct.mono
    (fun _ _ h => ⟨h.1.stage,h.2.stage⟩) (fun _ _ h => h)
  have wp (s : State) (h : P s) : WP isa (.block VG.Impl.Bignum.Arm.Fios.args) s Q := by
    obtain ⟨inv,hdr,_⟩ := h.secret
    refine WP.mono (args_ok s h.ctx hdr hi h.ptr) ?_
    rintro t ⟨_,p0,p12,p4,_,count,_⟩
    exact ⟨p0,p12,p4,count⟩
  have scan : RelCT isa (fun s t => Q s ∧ Q t) VG.Impl.Bignum.Arm.FiosFast.code
      (fun s t => s.gpr .r0 = t.gpr .r0) := code_relCT.mono
    (fun _ _ h => ⟨h.1.1.trans h.2.1.symm,h.1.2.1.trans h.2.2.1.symm,
      h.1.2.2.1.trans h.2.2.2.1.symm,h.1.2.2.2.trans h.2.2.2.2.symm⟩)
    (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0)
      (.block roundFinish) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h)
  exact (pair_posts ct wp).seq (scan.seq finish)

end VG.Proof.Bignum.Arm.FiosFast
