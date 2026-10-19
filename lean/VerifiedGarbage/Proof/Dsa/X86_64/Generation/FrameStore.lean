module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega))

theorem frameStore_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < nW) (r : Reg) :
    WP isa (.block [.store (sp (8 * k)) r]) s fun t =>
      Rep t.mem F S V (upd W k (s.gpr r)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (s.gpr r))
    (by xrun [ea_sp, hsp, hw]) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (off S i)) (fun k => word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.X86_64.Generation
