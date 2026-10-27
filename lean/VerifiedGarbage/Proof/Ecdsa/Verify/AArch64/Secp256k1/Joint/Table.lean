module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.TableLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Inputs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Moves

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev Table (base : Addr) (P Q : Point C) (m : Nat) (s : State) : Prop :=
  ∀ d,1 ≤ d → d ≤ m → PointAt base s (tablePt d) (pair P Q (d%4) (d/4))

theorem entry_from_generator : CopyLayout entry gSource := ⟨by decide,by decide,by decide,by decide,by decide⟩
theorem entry_from_peer : CopyLayout entry qSource := ⟨by decide,by decide,by decide,by decide,by decide⟩

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
