module

public import VerifiedGarbage.Proof.Bignum.X86.CrtPost
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Scratch work preserves the complete private RSA specification input -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont

theorem Inputs.spec_keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s : State} {m : Mem}
    (h : Inputs base bytes len args s) (O : Outside base 0 bytes s.mem m) :
    specResult m args = specResult s.mem args := by
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt m (byteAddr (args i)) (args (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (args i)) (args (i + 1)).toNat :=
    VG.Proof.Bignum.scratch_bytes O (by have := (args (i + 1)).isLt; omega) (h.apart i hi)
  unfold specResult
  rw [B 2 (by decide), B 4 (by decide), B 6 (by decide), B 8 (by decide),
    B 10 (by decide), B 12 (by decide), B 14 (by decide)]

end VG.Proof.Bignum.X86.Crt
