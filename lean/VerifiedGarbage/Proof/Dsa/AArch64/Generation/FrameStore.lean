module
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic

import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (VG.Proof.Bignum.off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega))

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (VG.Proof.Bignum.off S i)) (fun k => VG.Proof.Bignum.word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.AArch64.Generation
