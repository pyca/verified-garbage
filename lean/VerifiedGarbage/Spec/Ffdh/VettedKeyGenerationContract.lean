module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract

/-!
# Native contracts for vetted-group short-exponent key generation

**Trusted.** Separate entry points preserve all existing full-width contracts.
Only scalar sampling changes; buffer sizes, output conventions, rejection
budgets, entropy refills and permitted status leakage are unchanged.
-/

@[expose] public section
namespace VG.Spec.Ffdh

open VG.Spec.Rsa (bytesAt wordsAt os2ip i2osp powMod scratchWords)

def vettedGenerateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateKeySig.contract A
    (pre := fun _x xLen _y yLen _domain domainLen pLen _rand randLen _scratch scratchLen _ =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
        xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧ randLen.toNat = pLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun x _xLen y _yLen domain domainLen pLen rand randLen _scratch _scratchLen m m' r =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let s := vettedScalarOfOctets a (bytesAt m rand randLen.toNat)
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
      dom.map (·.toNat) ++ [keyStatus a (vettedScalarOfOctets a (bytesAt m rand randLen.toNat))])

def vettedGenerateKeyApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_vetted"
  sig := generateKeySig
  writeArgs := true
  contracts := some fun A stack => vettedGenerateKeyContract A stack
  summary := "One native finite-field Diffie–Hellman key-generation attempt using \
    `generationScalarBits`: RFC 7919 recommended shorter exponents for exact vetted \
    RFC 3526/7919 safe-prime groups, and full-width sampling for all other domains. \
    Takes `p_len` random bytes; rejects out-of-range samples and invalid public values \
    with the same status and output conventions as `vg_ffdh_generate_key`. \
    Contract: `VG.Spec.Ffdh.vettedGenerateKeyContract`. Timing may depend on the \
    public domain, lengths and returned status, not otherwise on the random bytes \
    or scalar. A shorter exponentiation schedule uses the public maximum width, \
    including secret leading zeros."
  safety := domainSafety ++ ["`x_len`, `y_len` and `rand_len` must be `p_len`.",
    checkedSafety] ++ scratchSafety

def vettedKeySearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
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
      let result := vettedKeySearch a pLen.toNat
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
        (vettedKeySearch a pLen.toNat retries (bytesAt m rand randLen.toNat)).statuses)

def vettedKeySearchApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_search_vetted"
  sig := keySearchSig
  writeArgs := true
  contracts := some fun A stack => vettedKeySearchContract A stack
  summary := "Generate a finite-field Diffie–Hellman key pair using vetted-group short exponents and native rejection sampling. \
    Owns both range-rejection and degenerate-public-value retry budgets. Returns 1 \
    with the key pair, 3 when a budget is exhausted, or 0 to request more entropy. \
    On 0, discard `used` bytes from `rand`, preserve the suffix and extend it \
    to `state[3]` bytes before calling again. On 0 and 3, both outputs are zero. \
    Contract: `VG.Spec.Ffdh.vettedKeySearchContract`. Timing may depend on the public domain, \
    controller policy and sequence of attempt statuses, not otherwise on secret scalar bytes."
  safety := domainSafety ++ ["`domain` must be one that `vg_ffdh_check_domain` accepted \
      (returned 1 for): the attempts' statuses, which the controller branches on, are \
      specified only for such a domain.",
    "`state` must be initialized by `vg_ffdh_key_generation_init` for `p_len`, or be the \
      state returned by this routine.",
    "`x_len` and `y_len` must be `p_len`."] ++ scratchSafety

end VG.Spec.Ffdh
