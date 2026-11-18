module

public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub

/-!
# DSA on AArch64, without secret residue

The postconditions of `vg_dsa_validate_public_key` and
`vg_dsa_validate_private_key` do not read the memory on return, and that of
`vg_dsa_parameter_search` reads it only within its outputs
(`Ffdh.AArch64.Scrub.bytesAt_of`, `wordsAt_of`; `ScrubAll.ScrubAllOk`, as
x86-64's `Proof/Dsa/X86_64/Scrub.lean` proves them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

theorem validatePublicKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePublicKeyContract abi stack) stack
      (Spec.Dsa.validatePublicKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePublicKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.validatePrivateKeyContract abi stack) stack
      (Spec.Dsa.validatePrivateKeySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.validatePrivateKeySig) (Nat.le_of_ble_eq_true rfl) fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem parameterSearchOk (stack : Nat) :
    ScrubAllOk (Spec.Dsa.parameterSearchContract abi stack) stack
      (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Dsa.parameterSearchSig) (Nat.le_of_ble_eq_true rfl) fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Dsa.parameterSearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw outLen


end VG.Proof.Dsa.AArch64.Scrub
