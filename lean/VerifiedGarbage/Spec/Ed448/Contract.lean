module

public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.TCB.Artifact

/-!
# Ed448: contracts on every target

**Trusted** (as every file in `Spec/`). The signatures determine memory
validity, separation, and public pointers and lengths through `Sig.contract`.
Key derivation and signing keep all buffer contents secret, the context's
included. Verification may leak its inputs; it returns exactly 0 or 1. There
are no failure or retry allowances for key derivation or signing. Signing
requires a context of at most 255 bytes (RFC 8032 §5.2: `dom4` encodes its
length in one byte); verification takes a context of any length, and
nothing verifies with one longer than 255 bytes.

The contracts also specify the hashing, so that an assembly caller can be
verified end to end.

All functions take 8 KiB of scratch space, whose contents are unspecified on
return and must be destroyed by callers handling secrets. `stack` describes
the space used below the stack pointer. `writeArgs` allows calls to reuse
the ABI's argument slots, including on 32-bit targets.
-/

@[expose] public section

namespace VG.Spec.Ed448

/-- Bytes in a buffer, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s, shared by all target signatures. -/
def scratchWords : Nat := 1024

def scratchSafety : String :=
  "The contents of `scratch` on return are unspecified and may contain secrets; the caller \
    must destroy them after use."

def seedSafety : String :=
  "`seed` must originate from a cryptographically secure random generator."

/-! ## Complete operations -/

/-- `(out: *mut [u8; 57], seed: *const [u8; 57], scratch: *mut [u64; 1024])`. -/
def publicKeySig : Sig where
  params := [("out", .array true .u8 57), ("seed", .array false .u8 57),
    ("scratch", .array true .u64 scratchWords)]

/-- Derive the public key from a private key, including SHAKE256 and
pruning. -/
def publicKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  publicKeySig.contract A
    (post := fun out seed _scratch m m' _ => bytesAt m' out 57 = publicKey (bytesAt m seed 57))
    (writeArgs := true) (stack := stack)

/-- `(out: *mut [u8; 114], seed: *const [u8; 57], pk: *const [u8; 57], context: *const u8, ctxlen: usize, message: *const u8, len: usize, scratch: *mut [u64; 1024])`. -/
def signCachedSig : Sig where
  params := [("out", .array true .u8 114), ("seed", .array false .u8 57),
    ("pk", .array false .u8 57), ("context", .slice false .u8 "ctxlen"),
    ("message", .slice false .u8 "len"), ("scratch", .array true .u64 scratchWords)]

/-- Sign with the public key corresponding to the private key, which RFC
8032 §5.2.6 uses (`A`, derived in §5.2.5); a caller may keep it rather than
derive it again for every signature. The postcondition is the same complete
signing algorithm, `sign`, for that private key alone. No buffer
contents may affect timing, the cached public key's included. -/
def signCachedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signCachedSig.contract A
    (pre := fun _out seed pk _context ctxlen _message _len _scratch m =>
      bytesAt m pk 57 = publicKey (bytesAt m seed 57) ∧ ctxlen.toNat ≤ 255)
    (post := fun out seed _pk context ctxlen message len _scratch m m' _ =>
      bytesAt m' out 114 = sign (bytesAt m seed 57) (bytesAt m context ctxlen.toNat)
        (bytesAt m message len.toNat))
    (writeArgs := true) (stack := stack)

/-- `(pk: *const [u8; 57], context: *const u8, ctxlen: usize, message: *const u8, len: usize, signature: *const [u8; 114], scratch: *mut [u64; 1024]) -> u32`. -/
def verifySig : Sig where
  params := [("pk", .array false .u8 57), ("context", .slice false .u8 "ctxlen"),
    ("message", .slice false .u8 "len"), ("signature", .array false .u8 114),
    ("scratch", .array true .u64 scratchWords)]
  ret := some .u32

/-- Verify the signature, including the message hash. All inputs are public. -/
def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (post := fun pk context ctxlen message len signature _scratch m _m' r =>
      r = if verify (bytesAt m pk 57) (bytesAt m context ctxlen.toNat)
        (bytesAt m message len.toNat) (bytesAt m signature 114) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun pk context ctxlen message len signature _scratch m =>
      (bytesAt m pk 57 ++ bytesAt m context ctxlen.toNat ++ bytesAt m message len.toNat ++
        bytesAt m signature 114).map (·.toNat))

/-! ## Emitted API documentation -/

def publicKeyApi : Api where
  module := "ed448"
  name := "vg_ed448_public_key"
  sig := publicKeySig
  writeArgs := true
  contracts := some fun A stack => publicKeyContract A stack
  summary := "Ed448 public-key derivation (RFC 8032 §5.2.5): writes the 57-byte public key \
    to `*out`, from the 57-byte private key at `seed`, including SHAKE256 and pruning. \
    Contract: `VG.Spec.Ed448.publicKeyContract`. Constant time: only pointers may affect \
    timing."
  safety := [seedSafety, scratchSafety]

def signCachedApi : Api where
  module := "ed448"
  name := "vg_ed448_sign_cached"
  sig := signCachedSig
  writeArgs := true
  contracts := some fun A stack => signCachedContract A stack
  summary := "Ed448 signing (RFC 8032 §5.2.6): writes the 114-byte signature to `*out`, for \
    the `len` bytes at `message`, the `ctxlen` bytes of context at `context` and the 57-byte \
    private key at `seed`, using its cached public key at `pk`. Includes all hashing, \
    pruning and scalar/group operations. Uses Ed448 with a context, not Ed448ph (no \
    prehash); the context is empty for plain Ed448. \
    Contract: `VG.Spec.Ed448.signCachedContract`. Constant time: only pointers and the \
    context and message lengths may affect timing, not any buffer contents."
  safety := [
    "The 57 bytes at `pk` must equal the public key derived from the 57 bytes at `seed` by \
      RFC 8032 §5.2.5 (`VG.Spec.Ed448.publicKey`).",
    "`ctxlen` must be at most 255.", seedSafety, scratchSafety]

def verifyApi : Api where
  module := "ed448"
  name := "vg_ed448_verify"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyContract A stack
  summary := "Ed448 verification (RFC 8032 §5.2.7): returns 1 if the 114-byte signature at \
    `signature` verifies for the 57-byte public key at `pk`, the `ctxlen` bytes of context \
    at `context` and the `len` bytes at `message`, and 0 otherwise (always 0 for a context \
    longer than 255 bytes). Uses Ed448 with a context, not Ed448ph (no prehash). Checks \
    canonical point encodings, S < L, and the cofactored equation `[4][S]B = [4]R + [4][k]A` \
    with the challenge k = SHAKE256(dom4(0, C) || R || A || M, 114) reduced modulo L. No \
    additional subgroup or small-order check is imposed. \
    Contract: `VG.Spec.Ed448.verifyContract`. Not constant time: timing may depend on the \
    public key, context, message and signature."
  safety := [scratchSafety]

end VG.Spec.Ed448
