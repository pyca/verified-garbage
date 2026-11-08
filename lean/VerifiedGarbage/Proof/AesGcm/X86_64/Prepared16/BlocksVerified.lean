module

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.Gcm.Prepared16Contract
public import VerifiedGarbage.Proof.Gcm.PreparedContract

import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
public import VerifiedGarbage.Spec.Gcm.Precomputed
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

/-! # Sixteen prepared powers: Whole-block functions with prepared contexts -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem preparedPowers16Repr_zero (p : Addr) : Spec.Gcm.PreparedPowers16Repr (fun _ => 0) p := by
  intro k hk
  have z : ∀ q : Addr, Spec.Gcm.blockAt (fun _ => 0) q = 0 := fun q => by
    simp [Spec.Gcm.blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]; decide
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  simp only [Spec.Gcm.ctxH, z, hpow_zero_succ, w]
  constructor <;> decide

end VG.Proof.AesGcm.X86_64
