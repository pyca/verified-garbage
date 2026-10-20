module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.RsaOaep
public import VerifiedGarbage.Impl.Bignum.AArch64
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.RsaOaep

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (VG.Proof.Bignum.off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega))

theorem frameStore_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) {k : Nat} (hk : k < nW) (r : Reg) :
    WP isa (.block [.strSp r (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k (s.gpr r)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  have hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (s.gpr r))
    (by brun [exec_storeSp (by unfold nW frameBytes at hk; omega : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hw, VG.Proof.Bignum.off]) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (VG.Proof.Bignum.off S i)) (fun k => VG.Proof.Bignum.word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.AArch64.Generation
