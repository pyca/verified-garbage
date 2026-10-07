import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)

theorem nafStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hj : j<256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j+1)) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (j+1)) :
    WP isa (Naf.step K) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧
      t.gpr .x19=BitVec.ofNat 64 j := by
  rw [Naf.step]
  apply WP.seq
  refine WP.mono (decCounter_ok s (by omega) (by omega) h19) fun a ⟨a19,ka⟩ => ?_
  have ca := h.of_keeps ka (by decide)
  apply WP.assoc
  apply WP.seq
  refine WP.mono (nafDoubleCore_ok hL hJ hAl hm hC ha hP ca) fun b ⟨kb,cb⟩ => ?_
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := by
    rw [kb.gpr _ (x19_not_clob _),a19,Nat.add_sub_cancel]
  refine WP.mono (nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by omega) hP cb b19)
    fun t ⟨kt,ct⟩ => ⟨?_,ct,?_⟩
  · have kp := kb.trans kt
    refine ⟨(Keeps.regs ka).mono (by simp) |>.trans
      ((⟨kp.gpr,kp.rd,kp.wr,kp.sp⟩ : KeepRegs (clob K.M.n) a t).mono
        (fun _ hr => List.mem_cons_of_mem _ hr)),?_⟩
    simpa only [ka.mem,jacLoopWrites] using kp.unch
  · rw [kt.gpr _ (x19_not_clob _),b19]

theorem nafLoop_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k 256) s)
    (h19 : s.gpr .x19=256) :
    WP isa (.loop (Naf.step K) (.nonzero .x .x19)) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .x19=0 := by
  let I := fun j t => JacLoopKeep K base s t ∧
    NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv:=I) (n:=256) (by decide)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have he : j-1+1=j := by omega
    have cp : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j-1+1)) a := he.symm ▸ ca
    have ap : a.gpr .x19=BitVec.ofNat 64 (j-1+1) := he.symm ▸ a19
    refine WP.mono (nafStep_ok hL hJ hAl hm hC ha hOne hTbl hBits (by omega) hP cp ap)
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    exact ⟨kt,ct,t19⟩
  · decide
  · exact ⟨JacLoopKeep.refl K base s,h,h19⟩

/-- Seed bit256 directly, then execute the remaining 256 public digits. -/
theorem nafRun_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hk : k<2^256)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) 0 s) (h19 : s.gpr .x19=256) :
    WP isa (.seq (Naf.digit K) (.loop (Naf.step K) (.nonzero .x .x19))) s fun t =>
      JacLoopKeep K base s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .x19=0 := by
  have he : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
  apply WP.seq
  refine WP.mono (nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (he.symm ▸ h) h19)
    fun a ⟨ka,ca⟩ => ?_
  have a19 : a.gpr .x19=256 := (ka.gpr _ (x19_not_clob _)).trans h19
  refine WP.mono (nafLoop_ok hL hJ hAl hm hC ha hOne hTbl hBits hP ca a19) fun t ⟨kt,ct,t19⟩ => ⟨?_,ct,t19⟩
  have kp : JacLoopKeep K base s a := ⟨(⟨ka.gpr,ka.rd,ka.wr,ka.sp⟩ : KeepRegs (clob K.M.n) s a).mono
    (fun _ hr => List.mem_cons_of_mem _ hr),ka.unch⟩
  exact kp.trans kt

end VG.Proof.Weierstrass.AArch64
