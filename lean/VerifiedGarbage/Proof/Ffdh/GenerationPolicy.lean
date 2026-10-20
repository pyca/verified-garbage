module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract

/-! A proof-side policy index shares the native controller across the two
reviewed sampling contracts. These definitions are convertible to those
contracts and introduce no additional trusted policy. -/

@[expose] public section
namespace VG.Proof.Ffdh

inductive GenerationPolicy where
  | full
  | vetted

namespace GenerationPolicy
open VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp powMod scratchWords)

def scalar : GenerationPolicy → Parameters → List Byte → Nat
  | .full => scalarOfOctets
  | .vetted => vettedScalarOfOctets

def search : GenerationPolicy → Parameters → Nat → KeyRetries → List Byte → KeySearchResult
  | .full => keySearch
  | .vetted => vettedKeySearch

def attemptContract (policy : GenerationPolicy) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateKeySig.contract A
    (pre := fun _x xLen _y yLen _domain domainLen pLen _rand randLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧ randLen.toNat = pLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun x _xLen y _yLen domain domainLen pLen rand randLen _scratch _scratchLen m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let s := policy.scalar a (bytesAt m rand randLen.toNat)
      domainValid pLen.toNat dom →
        r.toNat = keyStatus a s ∧
          if keyStatus a s = 1 then
            bytesAt m' x pLen.toNat = i2osp s pLen.toNat ∧
              bytesAt m' y pLen.toNat = i2osp (powMod a.g s a.p) pLen.toNat
          else bytesAt m' x pLen.toNat = List.replicate pLen.toNat 0 ∧
            bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun _x _xLen _y _yLen domain domainLen pLen rand randLen _scratch _scratchLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      dom.map (·.toNat) ++ [keyStatus a (policy.scalar a (bytesAt m rand randLen.toNat))])

def searchContract (policy : GenerationPolicy) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  keySearchSig.contract A
    (pre := fun _x xLen _y yLen _used domain domainLen pLen _rand _randLen _scratch scratchLen state m =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
      xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧
      Spec.Rsa.scratchWords pLen.toNat ≤ scratchLen.toNat ∧
      domainValid pLen.toNat (bytesAt m domain domainLen.toNat) ∧
      (m.readW state 64).toNat ≤ 128 ∧ (m.readW (state + 8) 64).toNat ≤ 128 ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 pLen.toNat)
    (post := fun x _xLen y _yLen used domain domainLen pLen rand randLen _scratch _scratchLen state m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let result := policy.search a pLen.toNat
        ⟨(m.readW state 64).toNat, (m.readW (state + 8) 64).toNat⟩ (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      (match result.outcome with
        | .accepted sx sy => bytesAt m' x pLen.toNat = i2osp sx pLen.toNat ∧
            bytesAt m' y pLen.toNat = i2osp sy pLen.toNat
        | _ => bytesAt m' x pLen.toNat = List.replicate pLen.toNat 0 ∧
            bytesAt m' y pLen.toNat = List.replicate pLen.toNat 0) ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.retries.keys,
        BitVec.ofNat 64 result.retries.scalars, BitVec.ofNat 64 pLen.toNat,
        BitVec.ofNat 64 (if result.status = 0 then pLen.toNat else 0)] ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _x _xLen _y _yLen _used domain domainLen pLen rand randLen _scratch _scratchLen state m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let retries := KeyRetries.mk (m.readW state 64).toNat (m.readW (state + 8) 64).toNat
      dom.map (·.toNat) ++ (wordsAt m state 4).map (·.toNat) ++
        (policy.search a pLen.toNat retries (bytesAt m rand randLen.toNat)).statuses)

theorem attemptContract_full {M : ISA} (A : Abi M) (stack : Nat) :
    attemptContract .full A stack = generateKeyContract A stack := rfl

theorem attemptContract_vetted {M : ISA} (A : Abi M) (stack : Nat) :
    attemptContract .vetted A stack = vettedGenerateKeyContract A stack := rfl

theorem searchContract_full {M : ISA} (A : Abi M) (stack : Nat) :
    searchContract .full A stack = keySearchContract A stack := rfl

theorem searchContract_vetted {M : ISA} (A : Abi M) (stack : Nat) :
    searchContract .vetted A stack = vettedKeySearchContract A stack := rfl

end GenerationPolicy
end VG.Proof.Ffdh
