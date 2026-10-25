module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastPrepare
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

theorem lastStart_relCT {w16 : Bool} {s u : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (ps : LastInput sb ss off p seed out table s) (pu : LastInput sb ss off p seed out table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedEq : seedBytes s.mem seed a k=seedBytes u.mem seed a k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sb ss a k off w16)
      (fun t v=>LastStartPostW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
        LastStartPostW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v) := by
  let R := fun t v : State=>LastPreparedW w16 (xofByte (seedBytes s.mem seed a k)) p out table s t ∧
    LastPreparedW w16 (xofByte (seedBytes u.mem seed a k)) p out table u v
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (prepareCode sb ss a a k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨prepare_ct sb ss a a k s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (lastPrepare_ok hss hsb h8 hk hk256 ps) et,
      exec_post (lastPrepare_ok hss hsb h8 hk hk256 pu) ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (prepareCode sb ss a a k) (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    have ht28 := h.1.keep.get .x28
    have hv28 := h.2.keep.get .x28
    have rr := reject_relCT (by decide) hoff (by decide : Reg.x22≠.x3 ∧ Reg.x22≠.x4)
      (by rw [h.1.pointer,ht28,ps.outPtr]; exact h.1.env)
      (by rw [h.2.pointer,hv28,pu.outPtr]; rw [seedEq]; exact h.2.env)
      h.1.constants h.2.constants
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm)) (h.1.pointer.trans h.2.pointer.symm)
      (by rw [ht28,hv28,base]) (h.1.tablePtr.trans h.2.tablePtr.symm)
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev
    exact ⟨rr.1,trivial⟩
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (lastStartCode sb ss a k off w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (lastStart_ok hss hsb h8 hoff hk hk256 ps.ptr ps.seedPtr ps.outPtr ps.readable ps.separate ps.context ps.symbol) et,
    exec_post (lastStart_ok hss hsb h8 hoff hk hk256 pu.ptr pu.seedPtr pu.outPtr pu.readable pu.separate pu.context pu.symbol) ev⟩

end VG.Proof.MlKem.AArch64.Paired
