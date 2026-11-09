module

public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.TCB.X86_64.State

/-!
# RSAEP on x86-64: helpers for the shared contracts

What the proofs of `pubContract`'s callers against their shared contracts
(`vg_rsa_public_checked`'s, `PubChecked.lean`) share: the stack arguments,
a state meeting `pubContract.pre`, and the leak of `n` and `e`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- The leak of `n` and `e`, as bytes, determines each when `n`'s length is
the same. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  exact List.append_inj hi hl

end VG.Proof.Bignum.X86_64
