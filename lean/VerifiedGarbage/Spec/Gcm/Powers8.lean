module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM with eight GHASH powers kept apart from the key context

**Trusted.** A 128-byte buffer holding the first eight prepared powers of a
key's hash subkey, kept apart from its 256-byte key context (`KeyRepr`): pair
`k`, at byte `32 k`, is `preparedPower(H^(2k+2))` then
`preparedPower(H^(2k+1))`, each stored little-endian. This is the layout of
bytes 256 through 383 of `PreparedPowersRepr`'s 1024-byte format, in a buffer
of its own. It is a storage convention, not a change to GCM's field
arithmetic (NIST SP 800-38D §6.3).

No function computes the buffer on its own. Each `*_store_powers` function is
a plain function (`vg_aes_gcm_seal`, `vg_aes_gcm_open`, or GHASH over whole blocks), with its
unchanged postcondition, that also writes to a 128-byte buffer the powers of
the hash subkey that it computes for its own GHASH. `vg_aes_gcm_seal_store_powers`
and `vg_aes_gcm_open_store_powers` require the lengths of a TLS record (a
12-byte nonce, at most 16 bytes of additional data and, for `open`, a
supported tag length: `storePowersOk`), the calls whose GHASH computes the
powers. A caller uses it for the call that first needs
them; every other call takes the plain functions or the `*_with_powers`
ones, which read the key context and the powers through two pointers, so
that nothing copies the key context.

Both families keep the existing GCM postconditions, memory bounds,
disjointness, leakage (`openLeak`) and secrecy guarantees. The powers are
secret, as the key context is. The `*_with_powers` functions require the
powers of the hash subkey of the key context passed with them
(`Powers8Repr m pw (ctxH m ctx)`), so they have names of their own.
Existing specifications and contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- The 8 prepared powers of `H` at `pw`: pair `k`, at byte `32 k`, holds the
encoded `H^(2k+2)` then `H^(2k+1)`, each as a little-endian 128-bit word. The
4 pairs occupy bytes 0 through 127. -/
def Powers8Repr (m : Mem) (pw : Addr) (H : Block) : Prop :=
  ∀ k < 4,
    m.readW (pw + BitVec.ofNat 64 (32 * k)) 128 = preparedPower (hpow H (2 * k + 2)) ∧
    m.readW (pw + BitVec.ofNat 64 (16 + 32 * k)) 128 = preparedPower (hpow H (2 * k + 1))

/-- The powers' buffer written by the `*_store_powers` functions. -/
def storePowersParam : String × Param := ("pw", .array true .u64 16)

/-- The powers' buffer read by the `*_with_powers` functions. -/
def withPowersParam : String × Param := ("pw", .array false .u64 16)

/-- Documentation shared by the `*_store_powers` functions. -/
def storePowersSummary (name contract : String) : String :=
  "`" ++ name ++ "`, which also writes to `*pw` the 8 prepared powers of its hash subkey `H`: " ++
  "at byte `32*k`, for `k` from 0 to 3, `preparedPower(H^(2*k+2))` then " ++
  "`preparedPower(H^(2*k+1))`, as two little-endian 128-bit words " ++
  "(`VG.Spec.Gcm.Powers8Repr`, `VG.Spec.Gcm.preparedPower`). Its other results are those of `" ++
  name ++ "`. The powers are secret, as the hash subkey is: they may not affect timing. " ++
  "Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-- Documentation shared by the `*_with_powers` functions. -/
def withPowersSummary (name contract : String) : String :=
  "`" ++ name ++ "` with the 8 prepared powers of the hash subkey of the key context at `*pw` " ++
  "(`VG.Spec.Gcm.Powers8Repr`), which it may read instead of computing them. Computes the same " ++
  "result as `" ++ name ++ "`. The powers are secret, as the key context is: they may not " ++
  "affect timing; all other memory, aliasing and constant-time requirements are unchanged. " ++
  "Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-- What `*pw` must hold for the `*_with_powers` functions. -/
def withPowersSafety : String :=
  "`*pw` must be what a `*_store_powers` function wrote for the same key context (the \
    contract's precondition: `VG.Spec.Gcm.Powers8Repr` of `pw` and its hash subkey)."

/-! ## Writing the powers -/

/-- What `vg_aes_gcm_seal_store_powers` and `vg_aes_gcm_open_store_powers`
require beyond the plain functions: a 12-byte nonce and at most 16 bytes of
additional data. -/
def storePowersOk {pb : Nat} (nonceLen aadLen : BitVec pb) : Prop :=
  nonceLen.toNat = 12 ∧ aadLen.toNat ≤ 16

/-- `storePowersOk` in the safety documentation. -/
def storePowersSafety : String :=
  "`nonce_len` must be 12 and `aad_len` at most 16 (`VG.Spec.Gcm.storePowersOk`)."

/-- `vg_aes_gcm_seal_store_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16], pw: *mut [u64; 16])`:
`sealSig` and the powers' buffer. -/
def sealStorePowersSig : Sig where
  params := sealSig.params ++ [storePowersParam]

/-- `sealPost`, and the powers of the key context's hash subkey at `pw`. -/
def sealStorePowersPost (pb : Nat) : sealStorePowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag pw m m' r =>
    sealPost pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r ∧
      Powers8Repr m' pw (ctxH m ctx)

/-- `sealPre` and `storePowersOk`, and `sealStorePowersPost`. -/
def sealStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealStorePowersSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _pw m =>
      sealPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag m ∧
        storePowersOk nonceLen aadLen)
    (post := sealStorePowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_store_powers` on every target. -/
def sealStorePowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_store_powers"
  sig := sealStorePowersSig
  writeArgs := true
  contracts := some fun A stack => sealStorePowersContract A stack
  summary := storePowersSummary "vg_aes_gcm_seal" "sealStorePowersContract"
  safety := sealApi.safety ++ [storePowersSafety]

/-- `vg_aes_gcm_open_store_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize, pw: *mut [u64; 16]) -> u32`:
`openSig` and the powers' buffer. -/
def openStorePowersSig : Sig where
  params := openSig.params ++ [storePowersParam]
  ret := some .u32

/-- `openPost`, and the powers of the key context's hash subkey at `pw`,
whether or not the tag matches: they depend only on the key. -/
def openStorePowersPost (pb : Nat) : openStorePowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw m m' r =>
    openPost pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r ∧
      Powers8Repr m' pw (ctxH m ctx)

/-- `openPre`, `storePowersOk` and a supported tag length (`tagLenOk`),
`openStorePowersPost`, and what `openContract` may leak. -/
def openStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openStorePowersSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw m =>
      openPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen m ∧
        storePowersOk nonceLen aadLen ∧ tagLenOk tagLen.toNat)
    (post := openStorePowersPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `vg_aes_gcm_open_store_powers` on every target. -/
def openStorePowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_store_powers"
  sig := openStorePowersSig
  writeArgs := true
  contracts := some fun A stack => openStorePowersContract A stack
  summary := storePowersSummary "vg_aes_gcm_open" "openStorePowersContract" ++
    " It writes the powers whether or not the tag matches: they depend only on the key."
  safety := openApi.safety ++ [storePowersSafety,
    "`tag_len` must be between 4 and 16 (`VG.Spec.Gcm.tagLenOk`)."]

/-- `vg_aes_gcm_seal_with_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16], pw: *const [u64; 16])`:
`sealSig` and the powers' buffer. -/
def sealWithPowersSig : Sig where
  params := sealSig.params ++ [withPowersParam]

/-- `sealPre`, and the powers of the key context's hash subkey at `pw`. -/
def sealWithPowersPre (pb : Nat) : Curry (sealWithPowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag pw m =>
    sealPre pb ctx rounds nonce nonceLen aad aadLen data len tag m ∧
      Powers8Repr m pw (ctxH m ctx)

/-- `sealPost`, which does not depend on `pw`. -/
def sealWithPowersPost (pb : Nat) : sealWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag _pw m m' r =>
    sealPost pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r

/-- `sealWithPowersPre` and `sealWithPowersPost`. -/
def sealWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealWithPowersSig.contract A (pre := sealWithPowersPre A.ptrBits)
    (post := sealWithPowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_with_powers` on every target. -/
def sealWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_with_powers"
  sig := sealWithPowersSig
  writeArgs := true
  contracts := some fun A stack => sealWithPowersContract A stack
  summary := withPowersSummary "vg_aes_gcm_seal" "sealWithPowersContract"
  safety := sealApi.safety ++ [withPowersSafety]

/-- `vg_aes_gcm_open_with_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize, pw: *const [u64; 16]) -> u32`:
`openSig` and the powers' buffer. -/
def openWithPowersSig : Sig where
  params := openSig.params ++ [withPowersParam]
  ret := some .u32

/-- `openPre`, and the powers of the key context's hash subkey at `pw`. -/
def openWithPowersPre (pb : Nat) : Curry (openWithPowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw m =>
    openPre pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m ∧
      Powers8Repr m pw (ctxH m ctx)

/-- `openPost`, which does not depend on `pw`. -/
def openWithPowersPost (pb : Nat) : openWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw m m' r =>
    openPost pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r

/-- `openLeak`, which does not depend on `pw`. -/
def openWithPowersLeak (pb : Nat) : Curry (openWithPowersSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw =>
    openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen

/-- `openWithPowersPre`, `openWithPowersPost`, and what `openContract` may
leak (`openWithPowersLeak`). -/
def openWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openWithPowersSig.contract A (pre := openWithPowersPre A.ptrBits)
    (post := openWithPowersPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openWithPowersLeak A.ptrBits))

/-- `vg_aes_gcm_open_with_powers` on every target. -/
def openWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_with_powers"
  sig := openWithPowersSig
  writeArgs := true
  contracts := some fun A stack => openWithPowersContract A stack
  summary := withPowersSummary "vg_aes_gcm_open" "openWithPowersContract"
  safety := openApi.safety ++ [withPowersSafety]

/-! ## GHASH -/

/-- `vg_ghash_store_powers(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32], pw: *mut [u64; 16])`:
`scratch` is working space. -/
def ghashStorePowersSig : Sig where
  params := [("h", .array false .u8 16), ("y", .array true .u8 16),
    ("data", .slice false (.array .u8 16) "n"), ("scratch", .array true .u64 32),
    storePowersParam]

/-- With the hash subkey `H` at `h` and a block `Y` at `y`: replaces `Y`
with `GHASH_H` continued from `Y` over the `n` blocks at `data`
(`Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H`), and writes the powers of `H` at `pw`. The hash
subkey, `Y`, the data and the powers are secret. -/
def ghashStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashStorePowersSig.contract A
    (post := fun h y data n _scratch pw m m' _ =>
      blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat) ∧
        Powers8Repr m' pw (blockAt m h))
    (stack := stack)

/-- `vg_ghash_store_powers` on every target. -/
def ghashStorePowersApi : Api where
  module := "gcm"
  name := "vg_ghash_store_powers"
  sig := ghashStorePowersSig
  contracts := some fun A stack => ghashStorePowersContract A stack
  summary := "GHASH (NIST SP 800-38D §6.4) continued over whole blocks: with the hash subkey `H` \
    the block at `h`, replaces the block `Y` at `*y` with `Yₙ`, where `Y₀ = Y` and \
    `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H` for the `n` 16-byte blocks `X₁ … Xₙ` starting at `data` (blocks \
    big-endian, `•` the multiplication of §6.3); it also writes to `*pw` the 8 prepared powers \
    of `H`: at byte `32*k`, for `k` from 0 to 3, `preparedPower(H^(2*k+2))` then \
    `preparedPower(H^(2*k+1))`, as two little-endian 128-bit words \
    (`VG.Spec.Gcm.Powers8Repr`, `VG.Spec.Gcm.preparedPower`).\n\n\
    Contract: `VG.Spec.Gcm.ghashStorePowersContract`. Constant time: only the pointers and `n` \
    may affect timing, not `H`, `Y`, the data or the powers."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.Gcm
