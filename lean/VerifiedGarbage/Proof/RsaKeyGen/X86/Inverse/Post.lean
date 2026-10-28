module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
import VerifiedGarbage.Proof.Framework.Sig

/-! # What `vg_rsa_keygen_inverse`'s postcondition tells its caller -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Proof.Rsa.X86.Keys (num)

theorem post_of {s t : State} (post : contract.post s t) :
    (∀ i, i < size s → ¬ Spec.RsaKeyGen.inverseWrites (len s) i →
      t.mem (base s + BitVec.ofNat 64 i) = s.mem (base s + BitVec.ofNat 64 i)) ∧
    num t.mem (base s) (kw (len s)) 1 =
      Nat.gcd (num s.mem (base s) (kw (len s)) 0) (num s.mem (base s) (kw (len s)) 8) ∧
    (num s.mem (base s) (kw (len s)) 8 : Int) ∣
      (num t.mem (base s) (kw (len s)) 3 : Int) * num s.mem (base s) (kw (len s)) 0 -
        num t.mem (base s) (kw (len s)) 1 ∧
    num t.mem (base s) (kw (len s)) 3 < num s.mem (base s) (kw (len s)) 8 := by
  sig_post [contract, inverseStack, Spec.RsaKeyGen.inverseContract, Spec.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes] at post
  simp only [← inverseNum_num]
  exact post

end VG.Proof.RsaKeyGen.X86.Inverse
