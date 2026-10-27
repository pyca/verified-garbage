module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ContinueTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ExtraBoth
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
import VerifiedGarbage.Proof.MlKem.Arith

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem load_resume {w16 : Bool} {s : State} {L : List Zq} {B : Nat→Byte} {aP : Addr}
    (h : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (hc : Rej8.Constants s) :
    WP isa (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) s fun t =>
      Only [.x3,.x4] s t ∧ ResumeW w16 L B aP t := by
  have h0 : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 0) 8 := by rw [ptr_zero]; exact h.out0
  refine WP.mono (load_checkpoint s (r:=.x1) (slot:=0) (by decide) (by decide) (in_rd_wr h0)
    (in_rd_wr h.out1)) fun t ⟨kt,hv,t3,t4⟩ => ?_
  refine ⟨kt,?_,?_,h.len,?_,?_,?_⟩
  · rw [kt.get .x20]
    exact h.env.transfer kt.mem kt.rd kt.wr (kt.get .x16)
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · rw [kt.mem]; exact h.coeffs
  · rw [t3,ptr_zero]; exact h.saved.1
  · rw [t4]; exact h.saved.2

theorem extra_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {L : List Zq} {aP : Addr}
    (ps : ReadyW w16 L B (s.gpr .x20) (s.gpr .x1) aP s) (pu : ReadyW w16 L B (u.gpr .x20) (u.gpr .x1) aP u)
    (cs : Rej8.Constants s) (cu : Rej8.Constants u)
    (hsp : s.sp=u.sp) (h20 : s.gpr .x20=u.gpr .x20) (h1 : s.gpr .x1=u.gpr .x1)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16)
      (fun a b=>ExtraPostW w16 L B aP (s.gpr .x1) s a ∧ ExtraPostW w16 L B aP (u.gpr .x1) u b) := by
  let R := fun a b=>ResumeW w16 L B aP a ∧ ResumeW w16 L B aP b ∧
    a.sp=b.sp ∧ a.gpr .x20=b.gpr .x20 ∧ a.gpr .x1=b.gpr .x1 ∧ a.gpr .x16=b.gpr .x16
  have start : RelCT isa (fun a b=>a=s ∧ b=u) (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) R := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,pa⟩ := exec_post (load_resume ps cs) ea
    obtain ⟨kb,pb⟩ := exec_post (load_resume pu cu) eb
    refine ⟨cursor_ct s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; rw [List.mem_singleton.mp hr]; exact h1)) ea eb,
      pa,pb,ka.sp.trans (hsp.trans kb.sp.symm),?_,?_,?_⟩
    · rw [ka.get .x20,kb.get .x20,h20]
    · rw [ka.get .x1,kb.get .x1,h1]
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject w16) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.ite ?_ ?_ ?_)
    · intro a b h
      have he : a.gpr .x4=b.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.x4.trans h.2.1.x4.symm)
      change some (a.gpr .x4 == 0)=some (b.gpr .x4 == 0)
      rw [he]
    · intro a b tr ur a' b' h ea eb
      have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
          (.block [.movz .x .x0 1 0]) :=
        VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
      exact ⟨ct a b tr ur a' b' trivial trivial (agree_of h.1.2.2.1 (by simp)) ea eb,trivial⟩
    · apply RelCT.assoc
      refine RelCT.seq (R:=fun a b : State=>a.sp=b.sp ∧ a.gpr .x1=b.gpr .x1) ?_ ?_
      · intro a b tr ur a' b' h ea eb
        exact continue_relCT h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2
          a b tr ur a' b' ⟨rfl,rfl⟩ ea eb
      · intro a b tr ur a' b' h ea eb
        exact ⟨storeCursor_ct a b tr ur a' b' trivial trivial
          (agree_of h.1 (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.2)) ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,
    exec_post (extra_ok s ps.env cs ps.len ps.coeffs ps.saved ps.out0 ps.out1 ps.apart) ea,
    exec_post (extra_ok u pu.env cu pu.len pu.coeffs pu.saved pu.out0 pu.out1 pu.apart) eb⟩

end VG.Proof.MlKem.AArch64.Paired
