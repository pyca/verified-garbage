module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
public import VerifiedGarbage.Proof.Sha512.Arm.Lit
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Sha256.Arm.Lit

import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes
public import VerifiedGarbage.Proof.Sha256.Arm.Shared
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Md5.Arm.Shared
public import VerifiedGarbage.Proof.Sha1.Arm.Shared
public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
public import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Proof.Sha512.Arm.Shared
public import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes
import VerifiedGarbage.Proof.Sha1.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Shared
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Common
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.Sha512.Arm.Shared
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# SHA-256's streaming functions on 32-bit ARM

`HashOK` for SHA-256 (`sha256OK`): its streaming functions
(`vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize`, whose
contracts for `update` and `finalize` hold from any initial hash value).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)

/-- SHA-256's functions: a 96-byte streaming state, 20 words of working
space and a 32-byte digest. -/
def sha256H : Hash := ⟨64, 96, 32, 32, 20, "vg_sha256_init", Impl.Sha256.Arm.Stream.init,
  "vg_sha256_update_scratch", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize_scratch", Impl.Sha256.Arm.Stream.finalize⟩

def sha256OK : HashOK sha256H where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := Hmac.Generic.Common.sha256_repr
  init := Proof.Sha256.Arm.Stream.init_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

end VG.Proof.Pbkdf2.Stream.Arm
