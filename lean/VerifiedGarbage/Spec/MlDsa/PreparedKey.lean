module

public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# Optional ML-DSA keys with cached key-polynomial NTTs

Trusted specifications, separate from their implementations. A prepared key
contains the ordinary encoded key followed by canonical little-endian `u32`
NTT coefficients. No expanded matrix is cached. Preparation pays the decoding
and transforms once; operations retain the ordinary signing, verification,
message-formatting, failure and leakage semantics. Existing key formats and
contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Encoded public key followed by `k` polynomials, each `256 * 4` bytes. -/
def preparedPublicKeyBytes (p : Params) : Nat := p.pkLen + 4 * n * p.k

/-- Encoded secret key followed by `l + 2k` polynomials in `s1, s2, t0` order. -/
def preparedSecretKeyBytes (p : Params) : Nat := p.skLen + 4 * n * (p.ℓ + 2 * p.k)

/-- The public-key polynomial transforms used by FIPS 204 Algorithm 8. -/
def preparedPublicPolys (p : Params) (pk : List Byte) : List Poly :=
  (pkDecode p pk).2.map fun t => ntt (t.map fun c => ofInt (c * 2 ^ d : Nat))

/-- The private-key polynomial transforms used by FIPS 204 Algorithm 7. -/
def preparedSecretPolys (p : Params) (sk : List Byte) : List Poly :=
  let (_, _, _, s1, s2, t0) := skDecode p sk
  (s1 ++ s2 ++ t0).map fun s => ntt (toRq s)

/-- The cached public coefficients are canonical and derived from this key's
encoded prefix, not independent caller-controlled precomputation. -/
def PreparedPublicKey (p : Params) (m : Mem) (key : Addr) : Prop :=
  ∀ i < p.k, PolyIs m (key + BitVec.ofNat 64 (p.pkLen + 4 * n * i))
    (preparedPublicPolys p (bytesAt m key p.pkLen))[i]!

/-- The cached secret coefficients are canonical and derived from this key's
encoded prefix. All bytes of this object are private key material to destroy. -/
def PreparedSecretKey (p : Params) (m : Mem) (key : Addr) : Prop :=
  ∀ i < p.ℓ + 2 * p.k, PolyIs m (key + BitVec.ofNat 64 (p.skLen + 4 * n * i))
    (preparedSecretPolys p (bytesAt m key p.skLen))[i]!

def preparePublicKeySig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen),
    ("prepared", .array true .u8 (preparedPublicKeyBytes p)),
    ("scratch", .array true .u64 128)]

def prepareSecretKeySig (p : Params) : Sig where
  params := [("sk", .array false .u8 p.skLen),
    ("prepared", .array true .u8 (preparedSecretKeyBytes p)),
    ("scratch", .array true .u64 128)]

/-- Copy the encoded key and prepare its public-polynomial transforms. -/
def preparePublicKeyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparePublicKeySig p).contract A
    (post := fun pk prepared _scratch m m' _ =>
      bytesAt m' prepared p.pkLen = bytesAt m pk p.pkLen ∧ PreparedPublicKey p m' prepared)
    (writeArgs := true) (stack := stack)

/-- Copy the encoded key and prepare its secret-polynomial transforms.
Preparation is constant time in the key bytes, including malformed encodings,
and does not validate or change the ordinary key-decoding semantics. -/
def prepareSecretKeyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (prepareSecretKeySig p).contract A
    (post := fun sk prepared _scratch m m' _ =>
      bytesAt m' prepared p.skLen = bytesAt m sk p.skLen ∧ PreparedSecretKey p m' prepared)
    (writeArgs := true) (stack := stack)

def preparedSignSig (p : Params) : Sig where
  params := [("sk", .array false .u8 (preparedSecretKeyBytes p)), ("mu", .array false .u8 64),
    ("rnd", .array false .u8 32), ("sig", .array true .u8 p.sigLen),
    ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

def preparedSignContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedSignSig p).contract A
    (pre := fun sk _mu _rnd _sig _scratch m => PreparedSecretKey p m sk)
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

def preparedVerifySig (p : Params) : Sig where
  params := [("pk", .array false .u8 (preparedPublicKeyBytes p)), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

def preparedVerifyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedVerifySig p).contract A
    (pre := fun pk _mu _sig _scratch m => PreparedPublicKey p m pk)
    (post := fun pk mu sig _scratch m _m' r =>
      let v := fun b => verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

def preparedSignMessageSig (p : Params) : Sig where
  params := [("sk", .array false .u8 (preparedSecretKeyBytes p)), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("rnd", .array false .u8 32),
    ("sig", .array true .u8 p.sigLen), ("scratch", .array true .u64 (messageScratchWords p))]
  ret := some .u32

def preparedSignMessageContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedSignMessageSig p).contract A
    (pre := fun sk _msg _msgLen _ctx _ctxLen _rnd _sig _scratch m => PreparedSecretKey p m sk)
    (post := fun sk msg msgLen ctx ctxLen rnd sig _scratch m m' r =>
      match formatMessage (bytesAt m ctx ctxLen.toNat) (bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        Outcome (fun b => signInternal p b (bytesAt m sk p.skLen) M' (bytesAt m rnd 32)) r
          (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk msg msgLen ctx ctxLen rnd _sig _scratch m =>
      signMessageLeak p (bytesAt m sk p.skLen) (bytesAt m msg msgLen.toNat)
        (bytesAt m ctx ctxLen.toNat) (bytesAt m rnd 32))

def preparedVerifyMessageSig (p : Params) : Sig where
  params := [("pk", .array false .u8 (preparedPublicKeyBytes p)), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .array false .u8 p.sigLen),
    ("scratch", .array true .u64 (messageScratchWords p)), ("tr", .array false .u8 64)]
  ret := some .u32

/-- Preserve the existing cached-digest verifier's semantics as well as its
`tr = H(pk)` invariant; only the key's polynomial representation is prepared. -/
def preparedVerifyMessageContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparedVerifyMessageSig p).contract A
    (pre := fun pk _msg _msgLen _ctx _ctxLen _sig _scratch tr m =>
      PreparedPublicKey p m pk ∧ bytesAt m tr 64 = pkTr (bytesAt m pk p.pkLen))
    (post := fun pk msg msgLen ctx ctxLen sig _scratch _tr m _m' r =>
      match formatMessage (bytesAt m ctx ctxLen.toNat) (bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        let v := fun b => verifyInternal p b (bytesAt m pk p.pkLen) M' (bytesAt m sig p.sigLen)
        (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk msg msgLen ctx ctxLen sig _scratch _tr m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m msg msgLen.toNat ++
        bytesAt m ctx ctxLen.toNat ++ bytesAt m sig p.sigLen))

/-- Preparation APIs have no secret-dependent timing and accept arbitrary
initial output and scratch bytes. They do not cache the expanded matrix. -/
def preparePublicKeyApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_prepare_verifying_key"
  sig := preparePublicKeySig p
  writeArgs := true
  contracts := some fun A stack => preparePublicKeyContract p A stack
  summary := s!"Prepares {label} verification key polynomials, copying the encoded key and caching its canonical NTT coefficients."
  safety := []

def prepareSecretKeyApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_prepare_signing_key"
  sig := prepareSecretKeySig p
  writeArgs := true
  contracts := some fun A stack => prepareSecretKeyContract p A stack
  summary := s!"Prepares {label} signing key polynomials, copying the encoded key and caching its canonical NTT coefficients."
  safety := ["The prepared key and scratch contain private key material and must be destroyed after use."]

def preparedSignApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_sign_prepared"
  sig := preparedSignSig p
  writeArgs := true
  contracts := some fun A stack => preparedSignContract p A stack
  summary := s!"Signs a message representative with a prepared {label} key; results and permitted leakage are those of signContract."
  safety := "The encoded key prefix and appended canonical NTTs must satisfy PreparedSecretKey." ::
    ([s!"The encoded secret-key prefix must have been written by `vg_{module}_keygen`.",
      "All bytes of the prepared key contain private key material and must be destroyed after use."] ++
      (signApi p module label).safety.drop 1)

def preparedVerifyApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_verify_prepared"
  sig := preparedVerifySig p
  writeArgs := true
  contracts := some fun A stack => preparedVerifyContract p A stack
  summary := s!"Verifies a message representative with a prepared {label} key; results and permitted leakage are those of verifyContract."
  safety := ["The encoded key prefix and appended canonical NTTs must satisfy PreparedPublicKey.",
    keyScratchSafety]

def preparedSignMessageApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_sign_message_prepared"
  sig := preparedSignMessageSig p
  writeArgs := true
  contracts := some fun A stack => preparedSignMessageContract p A stack
  summary := s!"Signs a message and context with a prepared {label} key; formatting, results and permitted leakage are those of signMessageContract."
  safety := "The encoded key prefix and appended canonical NTTs must satisfy PreparedSecretKey." ::
    ([s!"The encoded secret-key prefix must have been written by `vg_{module}_keygen`.",
      "All bytes of the prepared key contain private key material and must be destroyed after use."] ++
      (signMessageApi p module label).safety.drop 1)

def preparedVerifyMessageApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_verify_message_prepared"
  sig := preparedVerifyMessageSig p
  writeArgs := true
  contracts := some fun A stack => preparedVerifyMessageContract p A stack
  summary := s!"Verifies a message and context with a prepared {label} key and cached public-key digest; formatting, results and permitted leakage match verifyMessageCachedContract."
  safety := ["The encoded key prefix and appended canonical NTTs must satisfy PreparedPublicKey.",
    "The cached digest must equal SHAKE256 of the encoded public-key prefix, 64 bytes.",
    keyScratchSafety]

/-- Canonical secret transforms in a separate read-only buffer. This is the
same cache as `PreparedSecretKey`, without its encoded-prefix storage choice. -/
def CachedSecretPolys (p : Params) (m : Mem) (cache : Addr) (sk : List Byte) : Prop :=
  ∀ i < p.ℓ + 2 * p.k, PolyIs m (cache + BitVec.ofNat 64 (4 * n * i))
    (preparedSecretPolys p sk)[i]!

/-- Canonical public transforms in a separate read-only buffer. -/
def CachedPublicPolys (p : Params) (m : Mem) (cache : Addr) (pk : List Byte) : Prop :=
  ∀ i < p.k, PolyIs m (cache + BitVec.ofNat 64 (4 * n * i))
    (preparedPublicPolys p pk)[i]!

/-- Private common-kernel interface. The optional slice lets ordinary and
prepared entry points share one implementation without changing either API. -/
def signWithCacheSig (p : Params) : Sig :=
  { signSig p with params := (signSig p).params ++
      [("cache", .slice false .u8 "cache_len")] }

def signWithCacheContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (signWithCacheSig p).contract A
    (pre := fun sk _mu _rnd _sig _scratch cache cacheLen m =>
      cacheLen = 0 ∨
      (cacheLen.toNat = 4 * n * (p.ℓ + 2 * p.k) ∧
        CachedSecretPolys p m cache (bytesAt m sk p.skLen)))
    (post := fun sk mu rnd sig _scratch _cache _cacheLen m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch _cache _cacheLen m =>
      signLeak p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

def verifyWithCacheSig (p : Params) : Sig :=
  { verifySig p with params := (verifySig p).params ++
      [("cache", .slice false .u8 "cache_len")] }

def verifyWithCacheContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (verifyWithCacheSig p).contract A
    (pre := fun pk _mu _sig _scratch cache cacheLen m =>
      cacheLen = 0 ∨
      (cacheLen.toNat = 4 * n * p.k ∧
        CachedPublicPolys p m cache (bytesAt m pk p.pkLen)))
    (post := fun pk mu sig _scratch _cache _cacheLen m _m' r =>
      let v := fun b => verifyMu p b (bytesAt m pk p.pkLen) (bytesAt m mu 64) (bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch _cache _cacheLen m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m mu 64 ++ bytesAt m sig p.sigLen))

def signWithCacheApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_sign_with_cache"
  sig := signWithCacheSig p
  writeArgs := true
  contracts := some fun A stack => signWithCacheContract p A stack
  summary := s!"Private common {label} signing kernel with an optional canonical key-polynomial cache. Results and permitted leakage are those of signContract."
  safety := ["An absent cache has zero length; its pointer is valid for that empty slice. Otherwise the length must be exactly the secret polynomial-cache size and CachedSecretPolys must hold for the encoded key.",
    "Cached secret coefficients contain private key material and must be destroyed after use."] ++
    (signApi p module label).safety

def verifyWithCacheApi (p : Params) (module label : String) : Api where
  module := module
  name := s!"vg_{module}_verify_with_cache"
  sig := verifyWithCacheSig p
  writeArgs := true
  contracts := some fun A stack => verifyWithCacheContract p A stack
  summary := s!"Private common {label} verification kernel with an optional canonical key-polynomial cache. Results and permitted leakage are those of verifyContract."
  safety := ["An absent cache has zero length; its pointer is valid for that empty slice. Otherwise the length must be exactly the public polynomial-cache size and CachedPublicPolys must hold for the encoded key.",
    keyScratchSafety]

end VG.Spec.MlDsa
