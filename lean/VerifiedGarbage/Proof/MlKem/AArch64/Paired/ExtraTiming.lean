module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ContinueTiming
public import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ExtraReadyW (w16 : Bool) (L : List Zq) (B : Nat→Byte) (buf slot : Nat) (aP : Addr) (s : State) : Prop where
  env : Rej8.EnvW w16 56 B (s.gpr .x19+BitVec.ofNat 64 buf) aP s
  constants : Rej8.Constants s
  len : L.length≤256
  coeffs : Rej8.Scalar.CoeffsW w16 s.mem aP L
  saved : checkpointW w16 (s.gpr .x19+BitVec.ofNat 64 slot) aP L s.mem
  out0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8
  out1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8
  apart : (polyRegion aP).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩

abbrev ExtraReady := ExtraReadyW false

theorem load_resume {w16 : Bool} {s : State} {L : List Zq} {B : Nat→Byte} {buf slot : Nat} {aP : Addr}
    (ho : slot+8<32768) (ha : slot%8=0) (h : ExtraReadyW w16 L B buf slot aP s) :
    WP isa (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) s fun t =>
      Only [.x3,.x4] s t ∧ ResumeW w16 L B buf aP t := by
  refine WP.mono (load_checkpoint s ho ha (in_rd_wr h.out0) (in_rd_wr h.out1)) fun t ⟨kt,hv,t3,t4⟩ => ?_
  refine ⟨kt,?_,?_,h.len,?_,t3.trans h.saved.1,?_⟩
  · rw [kt.get .x19]
    exact h.env.transfer kt.mem kt.rd kt.wr (kt.get .x16)
  · exact ⟨by rw [hv]; exact h.constants.index,by rw [hv]; exact h.constants.mask,
      by simpa only [hv] using h.constants.q,by simpa only [hv] using h.constants.weights,
      by simpa only [hv] using h.constants.zero⟩
  · rw [kt.mem]; exact h.coeffs
  · rw [t4,show s.gpr .x19+BitVec.ofNat 64 (slot+8)=s.gpr .x19+BitVec.ofNat 64 slot+8 by
      rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl]
    exact h.saved.2

theorem storeFlag_ct (slot : Nat) (flag : Reg) (hf : flag≠.x19) :
    ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
      (.block [VG.Impl.MlKem.AArch64.mov flag .x0,.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]) := by
  cases flag <;> first
    | contradiction
    | exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem extra_relCT {w16 : Bool} {s u : State} {buf slot : Nat} (hb : buf<4096)
    (ho : slot+8<32768) (ha : slot%8=0) {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19)
    {B : Nat→Byte} {L : List Zq} {aP : Addr}
    (ps : ExtraReadyW w16 L B buf slot aP s) (pu : ExtraReadyW w16 L B buf slot aP u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.extraReject buf slot flag w16)
      (fun a b=>ExtraPostW w16 L B aP (s.gpr .x19+BitVec.ofNat 64 slot) flag s a ∧
        ExtraPostW w16 L B aP (u.gpr .x19+BitVec.ofNat 64 slot) flag u b) := by
  let R := fun a b=>ResumeW w16 L B buf aP a ∧ ResumeW w16 L B buf aP b ∧
    a.sp=b.sp ∧ a.gpr .x19=b.gpr .x19 ∧ a.gpr .x16=b.gpr .x16
  have start : RelCT isa (fun a b=>a=s ∧ b=u)
      (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) R := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha',hb'⟩
    subst a; subst b
    obtain ⟨ka,pa⟩ := exec_post (load_resume ho ha ps) ea
    obtain ⟨kb,pb⟩ := exec_post (load_resume ho ha pu) eb
    refine ⟨loadCheckpoint_ct slot s u tr ur a' b' trivial trivial
      (agree_of hsp (by intro r hr; simpa only [List.mem_singleton] using (show r=.x19 from List.mem_singleton.mp hr) ▸ h19)) ea eb,
      pa,pb,ka.sp.trans (hsp.trans kb.sp.symm),?_,?_⟩
    · rw [ka.get .x19,kb.get .x19,h19]
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace : RelCT isa (fun a b=>a=s ∧ b=u)
      (Impl.MlKem.AArch64.Paired.extraReject buf slot flag w16) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.ite ?_ ?_ ?_)
    · intro a b h
      have he : a.gpr .x4=b.gpr .x4 := BitVec.eq_of_toNat_eq (h.1.x4.trans h.2.1.x4.symm)
      change some (a.gpr .x4 == 0)=some (b.gpr .x4 == 0)
      rw [he]
    · intro a b tr ur a' b' h ea eb
      have ct : ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
          (.block [.movz .x flag 1 0]) := by
        cases flag <;> exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs []) (fun _ _ _ _ h=>h) (hc:=.block []) rfl
      exact ⟨ct a b tr ur a' b' trivial trivial (agree_of h.1.2.2.1 (by simp)) ea eb,trivial⟩
    · apply RelCT.assoc
      refine RelCT.seq (R:=fun a b : State=>a.sp=b.sp ∧ a.gpr .x19=b.gpr .x19) ?_ ?_
      · intro a b tr ur a' b' h ea eb
        exact continue_relCT hb h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2
          a b tr ur a' b' ⟨rfl,rfl⟩ ea eb
      · intro a b tr ur a' b' h ea eb
        refine ⟨storeFlag_ct slot flag hf.2.2 a b tr ur a' b' trivial trivial
          (agree_of h.1 ?_) ea eb,trivial⟩
        intro r hr; rw [List.mem_singleton.mp hr]; exact h.2
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha',hb'⟩
  subst a; subst b
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,
    exec_post (extra_ok s hb ho ha hf ps.env ps.constants ps.len ps.coeffs ps.saved ps.out0 ps.out1 ps.apart) ea,
    exec_post (extra_ok u hb ho ha hf pu.env pu.constants pu.len pu.coeffs pu.saved pu.out0 pu.out1 pu.apart) eb⟩

end VG.Proof.MlKem.AArch64.Paired
