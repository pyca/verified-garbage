module

public import VerifiedGarbage.Spec.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration

/-!
# Contracts for FFDH key generation with a reusable public comb context

**Trusted.** These are new APIs. Existing full-width and vetted entry points
are unchanged. The context is initialized once for checked parameters and
reused for attempts and rejection searches. Their results and entropy-refill
protocol are those of `vettedScalarOfOctets` and `vettedKeySearch`.
-/

@[expose] public section
namespace VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod scratchWords)

/-- Initialize public data only; the caller has already checked the domain. -/
def generationPrecomputeSig : Sig where
  params := [("ctx", .slice true .u64 "ctx_len"),
    ("domain", .slice false .u8 "domain_len"), ("p_len", .int .usize true),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def generationPrecomputeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generationPrecomputeSig.contract A
    (pre := fun _ctx ctxLen domain domainLen pLen _scratch scratchLen m =>
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
      ctxLen.toNat = generationPrecomputedWords pLen.toNat ∧
      scratchWords pLen.toNat ≤ scratchLen.toNat ∧
      domainValid pLen.toNat (bytesAt m domain domainLen.toNat))
    (post := fun ctx ctxLen domain domainLen pLen _scratch _scratchLen m m' r =>
      r = 1 ∧ generationPrecompute pLen.toNat (bytesAt m domain domainLen.toNat) =
        some (wordsAt m' ctx ctxLen.toNat))
    (writeArgs := true) (stack := stack)
    (leak := some fun _ctx _ctxLen domain domainLen _pLen _scratch _scratchLen m =>
      (bytesAt m domain domainLen.toNat).map (·.toNat))

def generationPrecomputeApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_precompute"
  sig := generationPrecomputeSig
  writeArgs := true
  contracts := some fun A stack => generationPrecomputeContract A stack
  summary := "Initialize a reusable public fixed-base context for finite-field Diffie–Hellman \
    key generation. The checked domain is p, g and optional q, each p_len bytes. \
    Writes generationPrecompute: three public metadata words followed by RSA's \
    modulus/R-squared values and 32 five-tooth comb entries. Returns 1. Word 0 is \
    generationScalarBits, word 1 is its byte length and word 2 is the comb row count. \
    The context has no pointers and is independent of the arithmetic backend. \
    Contract: VG.Spec.Ffdh.generationPrecomputeContract. Timing may depend on the \
    public domain, pointers and lengths."
  safety := domainSafety ++ ["domain must be one that vg_ffdh_check_domain accepted.",
    "ctx_len must be generationPrecomputedWords(p_len), namely 3 + 34 * ceil(p_len / 8)."] ++ scratchSafety

/-- Appending the context preserves every existing attempt argument's index. -/
def cachedGenerateKeySig : Sig :=
  { generateKeySig with params := generateKeySig.params ++ [("ctx", .slice false .u64 "ctx_len")] }

/-- A cached operation receives exactly the context initialized for its domain. -/
def generationContextAt (m : Mem) (ctx : Addr) (ctxLen pLen : Nat) (dom : List Byte) : Prop :=
  ctxLen = generationPrecomputedWords pLen ∧
    generationPrecompute pLen dom = some (wordsAt m ctx ctxLen)

def cachedGenerateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cachedGenerateKeySig.contract A
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

def generationContextSafety : List String :=
  ["domain must be one that vg_ffdh_check_domain accepted.",
   "ctx_len must be generationPrecomputedWords(p_len). ctx must contain the unchanged \
    words written by vg_ffdh_generate_key_precompute for these parameters."]

def cachedGenerateKeyApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_cached"
  sig := cachedGenerateKeySig
  writeArgs := true
  contracts := some fun A stack => cachedGenerateKeyContract A stack
  summary := "One native finite-field Diffie–Hellman key-generation attempt using a reusable \
    public five-tooth comb context. Takes p_len random bytes and implements the same \
    vettedScalarOfOctets, keyStatus and output conventions as vg_ffdh_generate_key_vetted \
    for checked parameters. The context's public maximum width fixes the schedule, \
    including secret leading zeros. Contract: VG.Spec.Ffdh.cachedGenerateKeyContract. \
    Timing may depend on the public domain, pointers, lengths and returned status, \
    not otherwise on the random bytes or private scalar."
  safety := domainSafety ++ generationContextSafety ++
    ["x_len, y_len and rand_len must be p_len."] ++ scratchSafety

/-- Appending the context also preserves every existing search argument's index. -/
def cachedKeySearchSig : Sig :=
  { keySearchSig with params := keySearchSig.params ++ [("ctx", .slice false .u64 "ctx_len")] }

def cachedKeySearchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cachedKeySearchSig.contract A
    (pre := fun _x xLen _y yLen _used domain domainLen pLen _rand _randLen _scratch scratchLen state ctx ctxLen m =>
      let dom := bytesAt m domain domainLen.toNat
      pLenValid pLen.toNat ∧ domainLenValid pLen.toNat domainLen.toNat ∧
      xLen.toNat = pLen.toNat ∧ yLen.toNat = pLen.toNat ∧
      scratchWords pLen.toNat ≤ scratchLen.toNat ∧ domainValid pLen.toNat dom ∧
      (m.readW state 64).toNat ≤ 128 ∧ (m.readW (state + 8) 64).toNat ≤ 128 ∧
      m.readW (state + 16) 64 = BitVec.ofNat 64 pLen.toNat ∧
      generationContextAt m ctx ctxLen.toNat pLen.toNat dom)
    (post := fun x _xLen y _yLen used domain domainLen pLen rand randLen _scratch _scratchLen state _ctx _ctxLen m m' r =>
      let a := domainOf pLen.toNat (bytesAt m domain domainLen.toNat)
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
    (leak := some fun _x _xLen _y _yLen _used domain domainLen pLen rand randLen _scratch _scratchLen state _ctx _ctxLen m =>
      let dom := bytesAt m domain domainLen.toNat
      let a := domainOf pLen.toNat dom
      let retries := KeyRetries.mk (m.readW state 64).toNat (m.readW (state + 8) 64).toNat
      dom.map (·.toNat) ++ (wordsAt m state 4).map (·.toNat) ++
        (vettedKeySearch a pLen.toNat retries (bytesAt m rand randLen.toNat)).statuses)

def cachedKeySearchApi : Api where
  module := "ffdh"
  name := "vg_ffdh_generate_key_search_cached"
  sig := cachedKeySearchSig
  writeArgs := true
  contracts := some fun A stack => cachedKeySearchContract A stack
  summary := "Generate a finite-field Diffie–Hellman key pair using a reusable public \
    five-tooth comb context and the existing vettedKeySearch rejection policy. \
    Returns 1 with a key pair, 3 when a budget is exhausted, or 0 to request entropy. \
    On 0, discard used bytes, preserve the suffix and extend it to state[3] bytes \
    before calling again. On 0 and 3 both outputs are zero. Entropy consumption, \
    retry budgets and statuses are unchanged. Contract: VG.Spec.Ffdh.cachedKeySearchContract. \
    Timing may depend on the public domain, pointers, lengths, controller policy \
    and sequence of attempt statuses, not otherwise on private scalar bytes."
  safety := domainSafety ++ generationContextSafety ++
    ["state must be initialized by vg_ffdh_key_generation_init for p_len, or be the \
      state returned by this routine.", "x_len and y_len must be p_len."] ++ scratchSafety

end VG.Spec.Ffdh
