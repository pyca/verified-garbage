module

public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub

/-!
# DSA on x86-64, without secret residue

The postconditions of DSA's key and signature functions read the memory on
return only within their outputs (`X86_64.Scrub.PostOut`): the validations
and verification not at all, the others the octets at `out` and the word at
`used` (`Ffdh.X86_64.Scrub.bytesAt_of`, `wordsAt_of`). Each implementation
returns with its whole stack wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Ffdh.X86_64.Scrub

theorem validatePublicKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePublicKeyContract abi stack) (Spec.Dsa.validatePublicKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePrivateKeyContract abi stack) (Spec.Dsa.validatePrivateKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem verifyPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.verifyPrevalidatedContract abi stack) (Spec.Dsa.verifySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem randomSignPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.randomSignPrevalidatedContract abi stack) (Spec.Dsa.randomSignSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw [] outLen

theorem generateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.generateKeyContract abi stack) (Spec.Dsa.generateKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1]
      · exact h
      · exact toNat_sw [] outLen

theorem deriveKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.deriveKeyContract abi stack) (Spec.Dsa.deriveKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX]
      · exact h
      · exact toNat_sw [] outLen

theorem parameterSearchOut (stack : Nat) :
    PostOut (Spec.Dsa.parameterSearchContract abi stack) (Spec.Dsa.parameterSearchSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw [] outLen

end VG.Proof.Dsa.X86_64.Scrub
