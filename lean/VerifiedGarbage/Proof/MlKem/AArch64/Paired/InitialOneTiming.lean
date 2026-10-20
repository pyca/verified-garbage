module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitialOne
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure OneReadyW (w16 : Bool) (B : Nat→Byte) (buf out slot : Nat) (s : State) : Prop where
  env : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) s
  constants : Rej8.Constants s
  out0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8
  out1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8
  apart : (polyRegion (s.gpr .x28+BitVec.ofNat 64 out)).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩

theorem OneReadyW.wp {w16 : Bool} {s : State} {B : Nat→Byte} {buf out slot : Nat} {flag : Reg}
    (hb : buf<4096) (ho : out<65536) (hslot : slot+8<32768) (ha : slot%8=0)
    (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19) (h : OneReadyW w16 B buf out slot s) :
    WP isa (initialOne buf out slot flag w16) s
      (InitialOnePostW w16 B (s.gpr .x28+BitVec.ofNat 64 out) (s.gpr .x19+BitVec.ofNat 64 slot) flag s) :=
  initialOne_ok s hb ho hslot ha hf h.env h.constants h.out0 h.out1 h.apart

theorem checkpoint_ct (slot : Nat) :
    ConstantTime isa (fun _=>True) (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
      (.block [.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h=>h) (hc:=.block []) rfl

theorem initialOne_relCT {w16 : Bool} {s u : State} {B : Nat→Byte} {buf out slot : Nat} {flag : Reg}
    (hb : buf<4096) (ho : out<65536) (hslot : slot+8<32768) (ha : slot%8=0)
    (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19) (ps : OneReadyW w16 B buf out slot s) (pu : OneReadyW w16 B buf out slot u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h28 : s.gpr .x28=u.gpr .x28) (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun t v=>t=s ∧ v=u) (initialOne buf out slot flag w16)
      (fun t v=>InitialOnePostW w16 B (s.gpr .x28+BitVec.ofNat 64 out) (s.gpr .x19+BitVec.ofNat 64 slot) flag s t ∧
        InitialOnePostW w16 B (u.gpr .x28+BitVec.ofNat 64 out) (u.gpr .x19+BitVec.ofNat 64 slot) flag u v) := by
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (initialOne buf out slot flag w16) (fun _ _=>True) := by
    refine RelCT.seq (reject_relCT hb ho ⟨hf.1,hf.2.1⟩ ps.env pu.env ps.constants pu.constants hsp h19 h28 h16) ?_
    intro t v tr ur t' v' h et ev
    have hx : t.gpr .x19=v.gpr .x19 := by
      rw [h.1.keep.get .x19 (by simp [hf.2.2.symm]),h.2.keep.get .x19 (by simp [hf.2.2.symm]),h19]
    exact ⟨checkpoint_ct slot t v tr ur t' v' trivial trivial
      (agree_of (h.1.keep.sp.trans (hsp.trans h.2.keep.sp.symm)) (by
        intro r hr; rw [List.mem_singleton.mp hr]; exact hx)) et ev,trivial⟩
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (ps.wp hb ho hslot ha hf) et,exec_post (pu.wp hb ho hslot ha hf) ev⟩

end VG.Proof.MlKem.AArch64.Paired
