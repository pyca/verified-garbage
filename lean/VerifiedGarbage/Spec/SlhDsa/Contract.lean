module

public import VerifiedGarbage.Spec.SlhDsa
public import VerifiedGarbage.TCB.Artifact

/-!
# SLH-DSA: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of SLH-DSA's key
generation, signing and verification, for each parameter set `p` of
Table 2, in terms of `Spec/SlhDsa.lean`, for any target: `A` is the target's
calling convention. The signatures fix where the arguments are, the memory
each function may access, disjointness, and that the pointers are public
(see `TCB/Sig.lean`); the contracts add the postconditions and what the
functions may leak.

Key generation is `slh_keygen_internal` (Algorithm 18) on the three seeds
`SK.seed`, `SK.prf` and `PK.seed` that the caller generates (`slh_keygen`,
Algorithm 21, is this on `3n` fresh random bytes from an approved RBG,
§3.1). Signing and verification are the pure `slh_sign` and `slh_verify`
(Algorithms 22 and 24): they format the message with its context string
themselves, and signing takes the randomness `addrnd` from the caller
(Algorithm 22, line 5), or `PK.seed` for the deterministic variant (line 6),
which the caller passes by pointing `addrnd` at bytes `2n` to `3n - 1` of
the private key. A context string longer than 255 bytes makes signing return
2, the error indication `⊥` of Algorithm 22, lines 1–3, and verification
return 0 (Algorithm 24, lines 1–3): its length is public, as every slice
length is.

Everything is secret in key generation and signing but what the contracts
declare they may leak (`Sig.contract`'s `leak`): the public key; and, in
signing, the message digest `H_msg(R, PK.seed, PK.root, M′)` (Algorithm 19,
line 6), from which the FORS indices, `idx_tree`, `idx_leaf` and the WOTS⁺
digits of every layer follow, and the signature, which contains `R` and
every value the verifier recomputes (`signLeak`). The contents of the
message and the context string are otherwise secret, and only their lengths
are public. Verification's inputs are all public, and it may leak them. The
working space `scratch` holds intermediate values on return, which the
caller must destroy (§3.1: the private key values are as secret as the
private key): 64 KiB (`scratchWords`).

The functions may overwrite their arguments passed in memory, where the
calling convention allows it (`writeArgs`), to pass arguments to the
functions they call, and take the number of bytes of stack below the stack
pointer that their calls and frames use (`stack`, see `Sig.contract`),
which depends on the target.
-/

@[expose] public section

namespace VG.Spec.SlhDsa

open Sha3 (bytesAt)

/-- The numbers a contract declares that a function may leak: the bytes `bs`. -/
def leakBytes (bs : List Byte) : List Nat := bs.map (·.toNat)

/-- The size of the working space, in `u64`s: 64 KiB. -/
def scratchWords : Nat := 8192

/-! ## Key generation -/

/-- `vg_slhdsa_*_keygen(seeds: *const [u8; 3n], sk: *mut [u8; 4n], pk: *mut [u8; 2n], scratch: *mut [u64; scratchWords])`.
`seeds` holds `SK.seed ‖ SK.prf ‖ PK.seed`; `scratch` is working space. -/
def keyGenSig (p : Params) : Sig where
  params := [("seeds", .array false .u8 (3 * p.n)), ("sk", .array true .u8 p.skLen),
    ("pk", .array true .u8 p.pkLen), ("scratch", .array true .u64 scratchWords)]

/-- With `SK.seed ‖ SK.prf ‖ PK.seed` at `seeds` (`n` bytes each): writes the
private and public keys of `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`
(Algorithm 18) of the parameter set `p` to `sk` and `pk`. May leak the
public key. -/
def keyGenContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (keyGenSig p).contract A
    (post := fun seeds sk pk _scratch m m' _ =>
      let s := bytesAt m seeds (3 * p.n)
      (bytesAt m' sk p.skLen, bytesAt m' pk p.pkLen) =
        keyGenInternal p (chunk s p.n 0) (chunk s p.n 1) (chunk s p.n 2))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seeds _sk _pk _scratch m =>
      let s := bytesAt m seeds (3 * p.n)
      leakBytes (keyGenInternal p (chunk s p.n 0) (chunk s p.n 1) (chunk s p.n 2)).2)

/-! ## Signing -/

/-- What `slh_sign_internal(M′, SK, addrnd)` (Algorithm 19) may leak: the
public key in `SK` (its last `2n` bytes), the message digest
`H_msg(R, PK.seed, PK.root, M′)` (`signDigest`), and the signature. -/
def signLeak (p : Params) (M' sk addrnd : List Byte) : List Nat :=
  leakBytes ((sk.drop (2 * p.n)).take p.pkLen ++ signDigest p M' sk addrnd ++ signInternal p M' sk addrnd)

/-- What `slh_sign(M, ctx, SK)` (Algorithm 22) on the randomness `addrnd` may
leak: nothing if the context string `ctx` is longer than 255 bytes (lines
1–3; its length is public); otherwise what `slh_sign_internal(M′, SK, addrnd)`
may leak for the formatted message `M′` (line 8): `signLeak`. -/
def signMessageLeak (p : Params) (sk M ctx addrnd : List Byte) : List Nat :=
  match formatMessage ctx M with
  | none => []
  | some M' => signLeak p M' sk addrnd

/-- `vg_slhdsa_*_sign(sk: *const [u8; 4n], msg: *const u8, msg_len: usize, ctx: *const u8, ctx_len: usize, addrnd: *const [u8; n], sig: *mut [u8; sigLen], scratch: *mut [u64; scratchWords]) -> u32`.
`addrnd` is the randomness; `scratch` is working space. -/
def signSig (p : Params) : Sig where
  params := [("sk", .array false .u8 p.skLen), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("addrnd", .array false .u8 p.n),
    ("sig", .array true .u8 p.sigLen), ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- With the private key at `sk`, the message `M` of `msg_len` bytes at
`msg`, the context string `ctx` of `ctx_len` bytes at `ctx` and the `n`
bytes `addrnd` at `addrnd`: returns 2 if `ctx` is longer than 255 bytes
(`slh_sign(M, ctx, SK)`, Algorithm 22, lines 1–3, returns `⊥`), and leaves
`sig` as it was; otherwise writes the signature
`slh_sign_internal(M′, SK, addrnd)` (Algorithm 19) of the parameter set `p`,
for the formatted message `M′ = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ M`
(`formatMessage`, Algorithm 22, line 8), to `sig`, and returns 1. May leak
what `signMessageLeak` says. -/
def signContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk msg msgLen ctx ctxLen addrnd sig _scratch m m' r =>
      match formatMessage (bytesAt m ctx ctxLen.toNat) (bytesAt m msg msgLen.toNat) with
      | none => r = 2 ∧ bytesAt m' sig p.sigLen = bytesAt m sig p.sigLen
      | some M' =>
        r = 1 ∧ bytesAt m' sig p.sigLen = signInternal p M' (bytesAt m sk p.skLen) (bytesAt m addrnd p.n))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk msg msgLen ctx ctxLen addrnd _sig _scratch m =>
      signMessageLeak p (bytesAt m sk p.skLen) (bytesAt m msg msgLen.toNat)
        (bytesAt m ctx ctxLen.toNat) (bytesAt m addrnd p.n))

/-! ## Verification -/

/-- `vg_slhdsa_*_verify(pk: *const [u8; 2n], msg: *const u8, msg_len: usize, ctx: *const u8, ctx_len: usize, sig: *const u8, sig_len: usize, scratch: *mut [u64; scratchWords]) -> u32`.
`scratch` is working space. -/
def verifySig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .slice false .u8 "sig_len"),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- With the public key at `pk`, the message `M` of `msg_len` bytes at `msg`,
the context string `ctx` of `ctx_len` bytes at `ctx` and the signature of
`sig_len` bytes at `sig`: returns 1 if `slh_verify(M, SIG, ctx, PK)`
(Algorithm 24) of the parameter set `p` is true, and 0 if it is false
(which it is if `ctx` is longer than 255 bytes, or the signature is not of
`sigLen` bytes). May leak its inputs. -/
def verifyContract (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifySig p).contract A
    (post := fun pk msg msgLen ctx ctxLen sig sigLen _scratch m _m' r =>
      r = if verify p (bytesAt m msg msgLen.toNat) (bytesAt m sig sigLen.toNat)
        (bytesAt m ctx ctxLen.toNat) (bytesAt m pk p.pkLen) then 1 else 0)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun pk msg msgLen ctx ctxLen sig sigLen _scratch m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m msg msgLen.toNat ++ bytesAt m ctx ctxLen.toNat ++
        bytesAt m sig sigLen.toNat))

/-! ## The functions on every target -/

/-- What the documentation says of the working space. -/
def scratchSafety : String :=
  "`scratch` is working space: on return it holds intermediate values, which the caller must \
    destroy (FIPS 205 §3.1)."

/-- `vg_<module>_keygen` for the parameter set `p` named `name`. -/
def keyGenApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_keygen"
  sig := keyGenSig p
  writeArgs := true
  contracts := some fun A stack => keyGenContract p A stack
  summary := s!"{name} key generation from seeds, `slh_keygen_internal(SK.seed, SK.prf, PK.seed)` \
    (FIPS 205 Algorithm 18): with `SK.seed ‖ SK.prf ‖ PK.seed` at `seeds`, writes the private \
    key to `*sk` and the public key to `*pk`.\n\n\
    Contract: `VG.Spec.SlhDsa.keyGenContract`. Constant time: timing may depend on the \
    pointers and on the public key, but not on `SK.seed` or `SK.prf`."
  safety := [
    "`seeds` must be random bytes from an approved RBG (FIPS 205 §3.1), or seeds so generated \
      before.",
    scratchSafety]

/-- `vg_<module>_sign` for the parameter set `p` named `name`. -/
def signApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_sign"
  sig := signSig p
  writeArgs := true
  contracts := some fun A stack => signContract p A stack
  summary := s!"{name} signing, `slh_sign(M, ctx, SK)` (FIPS 205 Algorithm 22) on the \
    randomness `*addrnd` (line 5): with the private key `*sk`, the `msg_len` bytes of the \
    message at `msg` and the `ctx_len` bytes of the context string at `ctx`, writes the \
    signature of the formatted message `M′ = 0 ‖ ctx_len ‖ ctx ‖ M` (line 8), \
    `slh_sign_internal(M′, SK, addrnd)` (Algorithm 19), to `*sig`, and returns 1. Returns 2 if \
    `ctx_len` is greater than 255 (FIPS 205 returns the error indication `⊥`): `*sig` is then \
    unchanged.\n\n\
    Contract: `VG.Spec.SlhDsa.signContract`. Constant time but for what the signature reveals: \
    timing may depend on the pointers, on `msg_len` and `ctx_len`, on the public key (the last \
    `2n` bytes of `*sk`), on the message digest `H_msg(R, PK.seed, PK.root, M′)` and on the \
    signature (`signLeak`), but not on anything else of the key, the message, the context \
    string or the randomness."
  safety := [
    "`sk` must have been written by `" ++ s!"vg_{module}_keygen" ++ "`.",
    "`addrnd` must point to fresh random bytes (FIPS 205 §3.1), or to bytes `2n` to `3n - 1` of \
      `*sk` (`PK.seed`) for deterministic signing.",
    scratchSafety]

/-- `vg_<module>_verify` for the parameter set `p` named `name`. -/
def verifyApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_verify"
  sig := verifySig p
  writeArgs := true
  contracts := some fun A stack => verifyContract p A stack
  summary := s!"{name} verification, `slh_verify(M, SIG, ctx, PK)` (FIPS 205 Algorithm 24): \
    with the public key `*pk`, the `msg_len` bytes of the message at `msg`, the `ctx_len` \
    bytes of the context string at `ctx` and the `sig_len` bytes of the signature at `sig`, \
    returns 1 if the signature is valid, and 0 if it is not, if `ctx_len` is greater than 255, \
    or if `sig_len` is not the length of a signature.\n\n\
    Contract: `VG.Spec.SlhDsa.verifyContract`. Not constant time: timing may depend on the \
    public key, the message, the context string and the signature."
  safety := [scratchSafety]

/-- `vg_slhdsa_sha2_128s_keygen` on every target. -/
def keyGenSha2_128sApi : Api := keyGenApi sha2_128s "slhdsa_sha2_128s" "SLH-DSA-SHA2-128s"
/-- `vg_slhdsa_sha2_128s_sign` on every target. -/
def signSha2_128sApi : Api := signApi sha2_128s "slhdsa_sha2_128s" "SLH-DSA-SHA2-128s"
/-- `vg_slhdsa_sha2_128s_verify` on every target. -/
def verifySha2_128sApi : Api := verifyApi sha2_128s "slhdsa_sha2_128s" "SLH-DSA-SHA2-128s"
/-- `vg_slhdsa_sha2_128f_keygen` on every target. -/
def keyGenSha2_128fApi : Api := keyGenApi sha2_128f "slhdsa_sha2_128f" "SLH-DSA-SHA2-128f"
/-- `vg_slhdsa_sha2_128f_sign` on every target. -/
def signSha2_128fApi : Api := signApi sha2_128f "slhdsa_sha2_128f" "SLH-DSA-SHA2-128f"
/-- `vg_slhdsa_sha2_128f_verify` on every target. -/
def verifySha2_128fApi : Api := verifyApi sha2_128f "slhdsa_sha2_128f" "SLH-DSA-SHA2-128f"
/-- `vg_slhdsa_sha2_192s_keygen` on every target. -/
def keyGenSha2_192sApi : Api := keyGenApi sha2_192s "slhdsa_sha2_192s" "SLH-DSA-SHA2-192s"
/-- `vg_slhdsa_sha2_192s_sign` on every target. -/
def signSha2_192sApi : Api := signApi sha2_192s "slhdsa_sha2_192s" "SLH-DSA-SHA2-192s"
/-- `vg_slhdsa_sha2_192s_verify` on every target. -/
def verifySha2_192sApi : Api := verifyApi sha2_192s "slhdsa_sha2_192s" "SLH-DSA-SHA2-192s"
/-- `vg_slhdsa_sha2_192f_keygen` on every target. -/
def keyGenSha2_192fApi : Api := keyGenApi sha2_192f "slhdsa_sha2_192f" "SLH-DSA-SHA2-192f"
/-- `vg_slhdsa_sha2_192f_sign` on every target. -/
def signSha2_192fApi : Api := signApi sha2_192f "slhdsa_sha2_192f" "SLH-DSA-SHA2-192f"
/-- `vg_slhdsa_sha2_192f_verify` on every target. -/
def verifySha2_192fApi : Api := verifyApi sha2_192f "slhdsa_sha2_192f" "SLH-DSA-SHA2-192f"
/-- `vg_slhdsa_sha2_256s_keygen` on every target. -/
def keyGenSha2_256sApi : Api := keyGenApi sha2_256s "slhdsa_sha2_256s" "SLH-DSA-SHA2-256s"
/-- `vg_slhdsa_sha2_256s_sign` on every target. -/
def signSha2_256sApi : Api := signApi sha2_256s "slhdsa_sha2_256s" "SLH-DSA-SHA2-256s"
/-- `vg_slhdsa_sha2_256s_verify` on every target. -/
def verifySha2_256sApi : Api := verifyApi sha2_256s "slhdsa_sha2_256s" "SLH-DSA-SHA2-256s"
/-- `vg_slhdsa_sha2_256f_keygen` on every target. -/
def keyGenSha2_256fApi : Api := keyGenApi sha2_256f "slhdsa_sha2_256f" "SLH-DSA-SHA2-256f"
/-- `vg_slhdsa_sha2_256f_sign` on every target. -/
def signSha2_256fApi : Api := signApi sha2_256f "slhdsa_sha2_256f" "SLH-DSA-SHA2-256f"
/-- `vg_slhdsa_sha2_256f_verify` on every target. -/
def verifySha2_256fApi : Api := verifyApi sha2_256f "slhdsa_sha2_256f" "SLH-DSA-SHA2-256f"
/-- `vg_slhdsa_shake_128s_keygen` on every target. -/
def keyGenShake_128sApi : Api := keyGenApi shake_128s "slhdsa_shake_128s" "SLH-DSA-SHAKE-128s"
/-- `vg_slhdsa_shake_128s_sign` on every target. -/
def signShake_128sApi : Api := signApi shake_128s "slhdsa_shake_128s" "SLH-DSA-SHAKE-128s"
/-- `vg_slhdsa_shake_128s_verify` on every target. -/
def verifyShake_128sApi : Api := verifyApi shake_128s "slhdsa_shake_128s" "SLH-DSA-SHAKE-128s"
/-- `vg_slhdsa_shake_128f_keygen` on every target. -/
def keyGenShake_128fApi : Api := keyGenApi shake_128f "slhdsa_shake_128f" "SLH-DSA-SHAKE-128f"
/-- `vg_slhdsa_shake_128f_sign` on every target. -/
def signShake_128fApi : Api := signApi shake_128f "slhdsa_shake_128f" "SLH-DSA-SHAKE-128f"
/-- `vg_slhdsa_shake_128f_verify` on every target. -/
def verifyShake_128fApi : Api := verifyApi shake_128f "slhdsa_shake_128f" "SLH-DSA-SHAKE-128f"
/-- `vg_slhdsa_shake_192s_keygen` on every target. -/
def keyGenShake_192sApi : Api := keyGenApi shake_192s "slhdsa_shake_192s" "SLH-DSA-SHAKE-192s"
/-- `vg_slhdsa_shake_192s_sign` on every target. -/
def signShake_192sApi : Api := signApi shake_192s "slhdsa_shake_192s" "SLH-DSA-SHAKE-192s"
/-- `vg_slhdsa_shake_192s_verify` on every target. -/
def verifyShake_192sApi : Api := verifyApi shake_192s "slhdsa_shake_192s" "SLH-DSA-SHAKE-192s"
/-- `vg_slhdsa_shake_192f_keygen` on every target. -/
def keyGenShake_192fApi : Api := keyGenApi shake_192f "slhdsa_shake_192f" "SLH-DSA-SHAKE-192f"
/-- `vg_slhdsa_shake_192f_sign` on every target. -/
def signShake_192fApi : Api := signApi shake_192f "slhdsa_shake_192f" "SLH-DSA-SHAKE-192f"
/-- `vg_slhdsa_shake_192f_verify` on every target. -/
def verifyShake_192fApi : Api := verifyApi shake_192f "slhdsa_shake_192f" "SLH-DSA-SHAKE-192f"
/-- `vg_slhdsa_shake_256s_keygen` on every target. -/
def keyGenShake_256sApi : Api := keyGenApi shake_256s "slhdsa_shake_256s" "SLH-DSA-SHAKE-256s"
/-- `vg_slhdsa_shake_256s_sign` on every target. -/
def signShake_256sApi : Api := signApi shake_256s "slhdsa_shake_256s" "SLH-DSA-SHAKE-256s"
/-- `vg_slhdsa_shake_256s_verify` on every target. -/
def verifyShake_256sApi : Api := verifyApi shake_256s "slhdsa_shake_256s" "SLH-DSA-SHAKE-256s"
/-- `vg_slhdsa_shake_256f_keygen` on every target. -/
def keyGenShake_256fApi : Api := keyGenApi shake_256f "slhdsa_shake_256f" "SLH-DSA-SHAKE-256f"
/-- `vg_slhdsa_shake_256f_sign` on every target. -/
def signShake_256fApi : Api := signApi shake_256f "slhdsa_shake_256f" "SLH-DSA-SHAKE-256f"
/-- `vg_slhdsa_shake_256f_verify` on every target. -/
def verifyShake_256fApi : Api := verifyApi shake_256f "slhdsa_shake_256f" "SLH-DSA-SHAKE-256f"

end VG.Spec.SlhDsa
