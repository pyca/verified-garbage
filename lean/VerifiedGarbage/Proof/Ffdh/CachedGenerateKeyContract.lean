module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! # The contract of `vg_ffdh_generate_key_cached`

One key-generation attempt with a reusable public comb context. Only verified
code calls it (the cached key search), so it is an internal function and its
contract is here, not in `Spec/`. -/

@[expose] public section
namespace VG.Proof.Ffdh
open VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod scratchWords)

/-- Appending the context preserves every existing attempt argument's index. -/
def cachedGenerateKeySig : Sig :=
  { generateKeySig with params := generateKeySig.params ++ [("ctx", .slice false .u64 "ctx_len")] }

/-- One attempt: `vettedScalarOfOctets` of the random bytes, its status
(`keyStatus`) and, for status 1, the scalar and public value; zeros otherwise. -/
def cachedGenerateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Proof.Ffdh.cachedGenerateKeySig.contract A
    (pre := fun _x xLen _y yLen domain domainLen pLen _rand randLen _scratch scratchLen ctx ctxLen m =>
      let dom := bytesAt m domain domainLen.toNat
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
      xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧ randLen.toNat = pLen.toNat ∧
      scratchWords pLen.toNat ≤ scratchLen.toNat ∧ domainValid pLen.toNat dom ∧
      generationContextAt m ctx ctxLen.toNat pLen.toNat dom)
    (post := fun x _xLen y _yLen domain domainLen pLen rand randLen _scratch _scratchLen _ctx _ctxLen m m' r =>
      let a := domainOf pLen.toNat (bytesAt m domain domainLen.toNat)
      let s := vettedScalarOfOctets a (bytesAt m rand randLen.toNat)
      r.toNat = keyStatus a s ∧
        if keyStatus a s = 1 then
          bytesAt m' x pLen.toNat = i2osp s pLen.toNat ∧
            bytesAt m' y pLen.toNat = i2osp (powMod a.g s a.p) pLen.toNat
        else bytesAt m' x pLen.toNat = List.replicate pLen.toNat 0 ∧
          bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _x _xLen _y _yLen domain domainLen pLen rand randLen _scratch _scratchLen _ctx _ctxLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      dom.map (·.toNat) ++ [keyStatus a (vettedScalarOfOctets a (bytesAt m rand randLen.toNat))])

end VG.Proof.Ffdh
