module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # Native RSA prime-search controller contracts -/

@[expose] public section

namespace VG.Spec.RsaKeyGen

open VG.Spec.Rsa (bytesAt wordsAt i2osp scratchWords)

def primeInitSig : Sig where
  params := [("state", .array true .u64 4), ("prime_len", .int .usize true),
    ("e", .slice false .u8 "e_len")]
  ret := some .u32

def primeInitContract {M : ISA} (A : Abi M) : Contract M :=
  primeInitSig.contract A
    (post := fun state primeLen e eLen m m' r =>
      match primeInit primeLen.toNat (bytesAt m e eLen.toNat) with
      | none => r.toNat = 0 ∧ wordsAt m' state 4 = List.replicate 4 0
      | some values => r.toNat = 1 ∧ wordsAt m' state 4 = values.map (BitVec.ofNat 64))
    (leak := some fun _state _primeLen e eLen m =>
      (bytesAt m e eLen.toNat).map (·.toNat))

def primeInitApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_prime_generation_init"
  sig := primeInitSig
  contracts := some fun A _ => primeInitContract A
  summary := "Initialize an RSA prime-generation controller. Returns 1 with four public \
    words: counted candidates remaining, prime width, entropy cap and initial request. \
    Returns 0 and clears all four words for an unsupported width or exponent encoding. \
    The public exponent is not secret. Contract: `VG.Spec.RsaKeyGen.primeInitContract`."
  safety := []

def primeSearchSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("e", .slice false .u8 "e_len"), ("p", .slice false .u8 "p_len"),
    ("rand", .slice false .u8 "rand_len"), ("scratch", .slice true .u64 "scratch_len"),
    ("state", .array true .u64 4)]
  ret := some .u32

def primeSearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  primeSearchSig.contract A
    (pre := fun _out outLen _used e eLen _p pLen _rand randLen _scratch scratchLen state m =>
      primeLenValid outLen.toNat ∧ 1 ≤ eLen.toNat ∧ eLen.toNat ≤ 8 ∧
      (pLen.toNat = 0 ∨ pLen.toNat = outLen.toNat) ∧
      scratchWords outLen.toNat ≤ scratchLen.toNat ∧
      (m.readW state 64).toNat ≤ primeLimit (8 * outLen.toNat)
        (Rsa.os2ip (bytesAt m e eLen.toNat)) ∧
      m.readW (state + 8) 64 = BitVec.ofNat 64 outLen.toNat ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 (primeEntropy outLen.toNat) ∧
      randLen.toNat ≤ primeEntropy outLen.toNat)
    (post := fun out outLen used e eLen p pLen rand randLen _scratch _scratchLen state m m' r =>
      let result := primeSearch outLen.toNat (bytesAt m e eLen.toNat)
        (bytesAt m p pLen.toNat) (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      r.toNat = result.status ∧
      bytesAt m' out outLen.toNat =
        (match result with
          | .accepted c _ _ => i2osp c outLen.toNat
          | _ => List.replicate outLen.toNat 0) ∧
      wordsAt m' used 1 = [BitVec.ofNat 64 result.used] ∧
      wordsAt m' state 4 = [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 outLen.toNat,
        BitVec.ofNat 64 (primeEntropy outLen.toNat), BitVec.ofNat 64 result.requested])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out outLen _used e eLen p pLen rand randLen _scratch _scratchLen state m =>
      let result := primeSearch outLen.toNat (bytesAt m e eLen.toNat)
        (bytesAt m p pLen.toNat) (m.readW state 64).toNat (bytesAt m rand randLen.toNat)
      (bytesAt m e eLen.toNat).map (·.toNat) ++ (wordsAt m state 4).map (·.toNat) ++
        [result.status, result.used, result.requested] ++ result.trace)

def primeSearchApi : Api where
  module := "rsa_keygen"
  name := "vg_rsa_generate_prime"
  sig := primeSearchSig
  writeArgs := true
  contracts := some fun A stack => primeSearchContract A stack
  summary := "Search for an RSA probable prime, owning candidate retries and entropy \
    requests in verified code. Uses the existing candidate and blinded Miller–Rabin \
    policies. Returns 1 with the prime, 3 on candidate or entropy-budget exhaustion, \
    or 0 for more entropy. On 0, discard exactly used bytes, preserve the remaining \
    suffix, extend it to state[3] bytes with fresh independent random bytes and retry. \
    The output is zero for 0 and 3. The tape and other prime remain secret: timing \
    may depend only on public controller words, e, consumption, requests and the \
    composed existing candidateLeak trace. \
    Contract: `VG.Spec.RsaKeyGen.primeSearchContract`."
  safety := ["state must come from vg_rsa_prime_generation_init for out_len and e, \
      or a previous call for the same e and other prime p.",
    "out_len must be a multiple of 8 in 32..=512; e_len must be in 1..=8; \
      p_len must be 0 or out_len.",
    "rand_len must not exceed state[2]; supply the preserved suffix before fresh bytes.",
    "scratch_len must be at least 16*out_len + 32 words; destroy scratch and entropy \
      buffers after use, including on failure."]

end VG.Spec.RsaKeyGen
