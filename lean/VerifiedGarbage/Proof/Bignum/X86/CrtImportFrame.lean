module
public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Imports change only component slots and preserve every source byte -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

def componentValue (m : Mem) (args : Nat → BitVec 32) (i : Nat) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat)

theorem import_frame {base : Addr} {n dst k bytes : Nat} {m m' : Mem}
    (O : Outside base (slot n dst) (8 * k) m m') (hd : dst < 20)
    (hk : k ≤ 2 * n) (hz : size n ≤ bytes) : Outside base 64 (bytes - 64) m m' := by
  have B := slot_bound (n := n) hd
  have H := slot_header n dst
  unfold stride at B
  exact O.mono (by omega) (by omega)

theorem Inputs.component_keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State} {m : Mem}
    (h : Inputs base bytes len args s) (O : Outside base 0 bytes s.mem m) (i : Nat)
    (hi : i ∈ componentArguments) : componentValue m args i = componentValue s.mem args i := by
  unfold componentValue
  rw [scratch_bytes O (by have := (args (i + 1)).isLt; omega) (h.apart i hi)]

end VG.Proof.Bignum.X86.Crt
