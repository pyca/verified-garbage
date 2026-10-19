module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBoth
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroTiming

/-! # The paired failure cleanup depends only on the public accepted lengths -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem ZeroReadyW.frame {w16 : Bool} {s u : State} {L : List Zq} {p : Addr} {slot : Nat} {rs : List Region}
    (h : ZeroReadyW w16 L slot p s) (hr : u.rd=s.rd) (hw : u.wr=s.wr) (hx : u.gpr .x19=s.gpr .x19)
    (hf : Frame rs s.mem u.mem) (hd : ∀r∈rs,(polyRegion p).Disjoint r)
    (hc : ∀r∈rs,(Region.mk (s.gpr .x19+BitVec.ofNat 64 slot) 16).Disjoint r) : ZeroReadyW w16 L slot p u := by
  refine ⟨h.len,coeffs_frame h.coeffs h.len hf hd,?_,?_,?_,?_⟩
  · rw [hx]; exact checkpoint_frame h.saved hf hc
  · simpa only [hr,hw,hx] using h.read0
  · simpa only [hr,hw,hx] using h.read1
  · simpa only [hw] using h.writable

theorem zeroBoth_relCT {w16 : Bool} {s u : State} {a b : Addr} {L M : List Zq}
    (sa : ZeroReadyW w16 L 1680 a s) (sb : ZeroReadyW w16 M 1696 b s)
    (ua : ZeroReadyW w16 L 1680 a u) (ub : ZeroReadyW w16 M 1696 b u)
    (hab : (polyRegion a).Disjoint (polyRegion b))
    (hcp : (Region.mk (s.gpr .x19+1696) 16).Disjoint (polyRegion a))
    (hsp : s.sp=u.sp) (hx : s.gpr .x19=u.gpr .x19) :
    RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (Impl.MlKem.AArch64.Paired.zeroExtra 1680 w16) (Impl.MlKem.AArch64.Paired.zeroExtra 1696 w16))
      (fun _ _=>True) := by
  let R := fun t v : State=>ZeroReadyW w16 M 1696 b t ∧ ZeroReadyW w16 M 1696 b v ∧
    t.sp=v.sp ∧ t.gpr .x19=v.gpr .x19
  refine RelCT.seq (R:=R) ?_ ?_
  · intro t v tr ur t' v' h et ev
    rcases h with ⟨ht0,hv0⟩
    subst t; subst v
    have ht := exec_post (zeroExtra_ok s (by decide) (by decide) sa.len sa.coeffs sa.saved sa.read0 sa.read1 sa.writable) et
    have hu := exec_post (zeroExtra_ok u (by decide) (by decide) ua.len ua.coeffs ua.saved ua.read0 ua.read1 ua.writable) ev
    refine ⟨(zeroExtra_relCT (by decide) (by decide) sa ua hsp hx s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
      sb.frame ht.1.rd ht.1.wr (ht.1.get .x19) ht.2.1 ?_ ?_,
      ub.frame hu.1.rd hu.1.wr (hu.1.get .x19) hu.2.1 ?_ ?_,
      ht.1.sp.trans (hsp.trans hu.1.sp.symm),?_⟩
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hcp
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hab.symm
    · intro r hr; rw [List.mem_singleton.mp hr,←hx]; exact hcp
    · rw [ht.1.get .x19,hu.1.get .x19,hx]
  · intro t v tr ur t' v' h et ev
    exact ⟨(zeroExtra_relCT (by decide) (by decide) h.1 h.2.1 h.2.2.1 h.2.2.2
      t v tr ur t' v' ⟨rfl,rfl⟩ et ev).1,trivial⟩

end VG.Proof.MlKem.AArch64.Paired
