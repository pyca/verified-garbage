module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Body
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes

/-!
# DSA signing on PPC64LE: constant time

`sign_ct`: two runs from states that satisfy `sContract` and agree on its
public data (the arguments' registers, the stack's arguments, the key's
public part and the result) leak the same trace. The entry (`sentry_rel`),
the checks of the key, shared with verification (`sizes_rel`,
`oddsTail_rel`, for signing's public data `SG`), the signing (`sbody_rel`)
or the zeroing of `out` (`zero_rel`), and `restore` follow one another;
each branch of the checks depends only on the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

theorem scheckKey_rel :
    RelCT isa (Two fun v s => S0 v s ∧ SG v) (checkKey Sign.body Sign.zeroOut) (Two End) :=
  sizes_rel (oddsTail_rel sbody_rel fun _ h => zero_rel h) fun _ h => zero_rel h

theorem sign_rel : RelCT isa (Two SC0) Sign.sign fun _ _ => True := by
  unfold Sign.sign
  exact RelCT.seq sentry_rel (RelCT.seq scheckKey_rel (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `svdOf`. -/
theorem svdOf_eq {s t : State} (hs : sContract.pre s) (hp : sContract.pub s t) : svdOf s = svdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, hl⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkl, -⟩ := hs
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h5, ← h6, ← h7, ← h9, Nat.min_eq_right (by omega)] at e
  simp only [svdOf, slayOf, ← h3, ← h5, ← h7, ← h8, ← h9, ← h10, ← a0, ← a1, ← a2, e]

theorem sign_ct : ConstantTime isa sContract.pre sContract.pub Sign.sign :=
  RelCT.constantTime (sign_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨svdOf s, ⟨hs, rfl⟩, ⟨ht, (svdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
