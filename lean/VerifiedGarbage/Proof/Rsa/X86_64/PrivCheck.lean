module
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl

import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_private_checked` on x86-64: what follows the CRT

`check_ok` runs everything after the call of the CRT, from any state the
frame allows: whatever `M` holds and whatever the CRT returned (`r₁`), it
releases `M` to `out` (and returns 1) only if `r₁` is odd, `n` is a valid
modulus and the public operation of `M` with `e`, within BoringSSL's
limits, is the input; otherwise `out` is zeros. This is the fault tolerance
of the check: a faulted exponentiation releases nothing that fails it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem bytes_wo (m : Mem) (base : Addr) {d a n : Nat} (v : BitVec 64) (h : d + 8 ≤ a ∨ a + n ≤ d)
    (ha : a + n ≤ 4096) (hd : d + 8 ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW (off base d) v) (off base a) n = Spec.Rsa.bytesAt m (off base a) n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact writeW_outside m base v (by omega_arith) _ (by rw [ofs_off base (by omega_arith)]; omega_arith)

theorem bytes_wo0 (m : Mem) (base : Addr) {a n : Nat} (v : BitVec 64) (h : 8 ≤ a) (ha : a + n ≤ 4096) :
    Spec.Rsa.bytesAt (m.writeW base v) (off base a) n = Spec.Rsa.bytesAt m (off base a) n := by
  have := bytes_wo m base (d := 0) v (.inl h) ha (by decide)
  simpa only [off, BitVec.add_zero] using this

end VG.Proof.Rsa.X86_64
