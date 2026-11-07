module

public import VerifiedGarbage.Spec.MlDsa.CachedVerify

/-!
# ML-DSA with prepared keys, for keys that sign or verify many messages

`vg_mldsa*_prepare_signing_key` and `vg_mldsa*_prepare_verifying_key` copy an
encoded key and append the NTTs of the key polynomials that signing (FIPS 204
Algorithm 7, lines 1–5) and verification (Algorithm 8, lines 1–9) compute
from it on every call: `NTT(s₁)`, `NTT(s₂)` and `NTT(t₀)` for a private key,
`NTT(t₁ · 2^d)` for a public key. `vg_mldsa*_sign_message_prepared` and
`vg_mldsa*_verify_message_prepared` take such a prepared key in place of the
encoded key, and are otherwise `vg_mldsa*_sign_message` and
`vg_mldsa*_verify_message_cached`: the same results, failures and permitted
leakage. A caller that keeps a key for many signatures or verifications
prepares it once, so that each of them does not decode and transform the key
again. Nothing here changes the encoded keys or the existing contracts; the
expanded matrix `Â` is not cached.
-/

@[expose] public section

namespace VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Prepared keys -/

/-- The size of a prepared public key, in bytes: the encoded public key
followed by `k` polynomials of `256` `u32` coefficients. -/
def preparedPublicKeyBytes (p : Params) : Nat := p.pkLen + 4 * n * p.k

/-- The size of a prepared private key, in bytes: the encoded private key
followed by `ℓ + 2k` polynomials of `256` `u32` coefficients. -/
def preparedSecretKeyBytes (p : Params) : Nat := p.skLen + 4 * n * (p.ℓ + 2 * p.k)

/-- The polynomials a prepared public key holds: `NTT(t₁ · 2^d)` (FIPS 204
Algorithm 8, line 9), for the `k` polynomials `t₁` of the public key `pk`. -/
def preparedPublicPolys (p : Params) (pk : List Byte) : List Poly :=
  (pkDecode p pk).2.map fun t => ntt (t.map fun c => ofInt (c * 2 ^ d : Nat))

/-- The polynomials a prepared private key holds: `ŝ₁`, `ŝ₂` and `t̂₀`
(FIPS 204 Algorithm 7, lines 2–4), in that order, for the private key `sk`. -/
def preparedSecretPolys (p : Params) (sk : List Byte) : List Poly :=
  let (_, _, _, s1, s2, t0) := skDecode p sk
  (s1 ++ s2 ++ t0).map fun s => ntt (toRq s)

/-- The polynomial `f` of `T_q` is stored at `p` as `[u32; 256]`:
coefficient `i` is the native (little-endian) `u32` at `p + 4i`, its
representative in `[0, q)`. -/
def PolyStored (m : Mem) (p : Addr) (f : Poly) : Prop :=
  ∀ i (h : i < n), (m.readW (p + BitVec.ofNat 64 (4 * i)) 32).toNat = (f[i]'h).val

/-- The `preparedPublicKeyBytes p` bytes at `key` are a prepared public key:
the encoded public key, followed by the polynomials `preparedPublicPolys` of
that encoded key. -/
def PreparedPublicKey (p : Params) (m : Mem) (key : Addr) : Prop :=
  ∀ i < p.k, PolyStored m (key + BitVec.ofNat 64 (p.pkLen + 4 * n * i))
    (preparedPublicPolys p (bytesAt m key p.pkLen))[i]!

/-- The `preparedSecretKeyBytes p` bytes at `key` are a prepared private key:
the encoded private key, followed by the polynomials `preparedSecretPolys`
of that encoded key. -/
def PreparedSecretKey (p : Params) (m : Mem) (key : Addr) : Prop :=
  ∀ i < p.ℓ + 2 * p.k, PolyStored m (key + BitVec.ofNat 64 (p.skLen + 4 * n * i))
    (preparedSecretPolys p (bytesAt m key p.skLen))[i]!

/-! ## Preparing keys -/

/-- `vg_mldsa*_prepare_verifying_key(pk: *const [u8; pkLen],
prepared: *mut [u8; preparedPublicKeyBytes], scratch: *mut [u64; 128])`.
`scratch` is working space. -/
def preparePublicKeySig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen),
    ("prepared", .array true .u8 (preparedPublicKeyBytes p)),
    ("scratch", .array true .u64 128)]

/-- With the public key at `pk`, writes the prepared public key of it to
`prepared`: the encoded key, then its polynomials (`PreparedPublicKey`).
Constant time. -/
def preparePublicKeyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (preparePublicKeySig p).contract A
    (post := fun pk prepared _scratch m m' _ =>
      bytesAt m' prepared p.pkLen = bytesAt m pk p.pkLen ∧ PreparedPublicKey p m' prepared)
    (writeArgs := true) (stack := stack)

/-- `vg_mldsa*_prepare_signing_key(sk: *const [u8; skLen],
prepared: *mut [u8; preparedSecretKeyBytes], scratch: *mut [u64; 128])`.
`scratch` is working space. -/
def prepareSecretKeySig (p : Params) : Sig where
  params := [("sk", .array false .u8 p.skLen),
    ("prepared", .array true .u8 (preparedSecretKeyBytes p)),
    ("scratch", .array true .u64 128)]

/-- With the private key at `sk`, writes the prepared private key of it to
`prepared`: the encoded key, then its polynomials (`PreparedSecretKey`).
Constant time, for any bytes at `sk`. -/
def prepareSecretKeyContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (prepareSecretKeySig p).contract A
    (post := fun sk prepared _scratch m m' _ =>
      bytesAt m' prepared p.skLen = bytesAt m sk p.skLen ∧ PreparedSecretKey p m' prepared)
    (writeArgs := true) (stack := stack)

/-! ## Signing and verifying with prepared keys -/

/-- `vg_mldsa*_sign_message_prepared(sk: *const [u8; preparedSecretKeyBytes],
msg: *const u8, msg_len: usize, ctx: *const u8, ctx_len: usize,
rnd: *const [u8; 32], sig: *mut [u8; sigLen],
scratch: *mut [u64; messageScratchWords]) -> u32`: `signMessageSig` with a
prepared private key. -/
def preparedSignMessageSig (p : Params) : Sig where
  params := [("sk", .array false .u8 (preparedSecretKeyBytes p)), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("rnd", .array false .u8 32),
    ("sig", .array true .u8 p.sigLen), ("scratch", .array true .u64 (messageScratchWords p))]
  ret := some .u32

/-- With a prepared private key at `sk` (a precondition), `signMessageContract`
of its encoded key: the same result, signature and permitted leakage. -/
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

/-- `vg_mldsa*_verify_message_prepared(pk: *const [u8; preparedPublicKeyBytes],
msg: *const u8, msg_len: usize, ctx: *const u8, ctx_len: usize,
sig: *const [u8; sigLen], scratch: *mut [u64; messageScratchWords],
tr: *const [u8; 64]) -> u32`: `verifyMessageCachedSig` with a prepared public
key. -/
def preparedVerifyMessageSig (p : Params) : Sig where
  params := [("pk", .array false .u8 (preparedPublicKeyBytes p)), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .array false .u8 p.sigLen),
    ("scratch", .array true .u64 (messageScratchWords p)), ("tr", .array false .u8 64)]
  ret := some .u32

/-- With a prepared public key at `pk` and `tr = H(pk, 64)` of its encoded key
at `tr` (preconditions), `verifyMessageCachedContract` of its encoded key: the
same result and permitted leakage. -/
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

/-! ## The functions -/

/-- `vg_<module>_prepare_verifying_key` for the parameter set `p` named `name`. -/
def preparePublicKeyApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_prepare_verifying_key"
  sig := preparePublicKeySig p
  writeArgs := true
  contracts := some fun A stack => preparePublicKeyContract p A stack
  summary := s!"{name} public-key preparation: with the public key `*pk`, writes to `*prepared` \
    the key, followed by the `k` polynomials `NTT(t₁ · 2^d)` that verification \
    (FIPS 204 Algorithm 8, line 9) computes from it, for `vg_{module}_verify_message_prepared`.\n\n\
    Contract: `VG.Spec.MlDsa.preparePublicKeyContract`. Constant time."
  safety := [keyScratchSafety]

/-- `vg_<module>_prepare_signing_key` for the parameter set `p` named `name`. -/
def prepareSecretKeyApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_prepare_signing_key"
  sig := prepareSecretKeySig p
  writeArgs := true
  contracts := some fun A stack => prepareSecretKeyContract p A stack
  summary := s!"{name} private-key preparation: with the private key `*sk`, writes to \
    `*prepared` the key, followed by the `ℓ + 2k` polynomials `NTT(s₁)`, `NTT(s₂)` and \
    `NTT(t₀)` that signing (FIPS 204 Algorithm 7, lines 2–4) computes from it, for \
    `vg_{module}_sign_message_prepared`.\n\n\
    Contract: `VG.Spec.MlDsa.prepareSecretKeyContract`. Constant time."
  safety := [
    "`*prepared` holds private key material, which the caller must destroy (FIPS 204 §3.6.3).",
    keyScratchSafety]

/-- `vg_<module>_sign_message_prepared` for the parameter set `p` named `name`. -/
def preparedSignMessageApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_sign_message_prepared"
  sig := preparedSignMessageSig p
  writeArgs := true
  contracts := some fun A stack => preparedSignMessageContract p A stack
  summary := s!"{name} signing with a prepared private key: `vg_{module}_sign_message` (with \
    its results, timing and leakage) of the private key that `*sk` begins with.\n\n\
    Contract: `VG.Spec.MlDsa.preparedSignMessageContract`."
  safety := [
    "`sk` must have been written by `" ++ s!"vg_{module}_prepare_signing_key" ++ "` from a \
      private key written by `" ++ s!"vg_{module}_keygen" ++ "`, and not changed since.",
    "`*sk` holds private key material, which the caller must destroy (FIPS 204 §3.6.3).",
    "`rnd` must be fresh random bytes (FIPS 204 §3.6.1), or 32 zero bytes for deterministic \
      signing.",
    keyScratchSafety]

/-- `vg_<module>_verify_message_prepared` for the parameter set `p` named `name`. -/
def preparedVerifyMessageApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_verify_message_prepared"
  sig := preparedVerifyMessageSig p
  writeArgs := true
  contracts := some fun A stack => preparedVerifyMessageContract p A stack
  summary := s!"{name} verification with a prepared public key: \
    `vg_{module}_verify_message_cached` (with its results, timing and leakage) of the public \
    key that `*pk` begins with.\n\n\
    Contract: `VG.Spec.MlDsa.preparedVerifyMessageContract`."
  safety := [
    "`pk` must have been written by `" ++ s!"vg_{module}_prepare_verifying_key" ++ "`, and not \
      changed since.",
    "`*tr` must equal SHAKE256 of the public key that `*pk` begins with, 64 bytes.",
    keyScratchSafety]

end VG.Spec.MlDsa
