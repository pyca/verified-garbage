module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace
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

`vg_aes_gcm_store_powers` computes the buffer from a key context alone, when
the key is set up. The `*_with_powers` functions, `vg_aes_gcm_seal`,
`vg_aes_gcm_open` and `vg_aes_gcm_open_to` that also read the buffer, take
the key context and the powers through two pointers, so that nothing copies
the key context.

They keep the existing GCM postconditions, memory bounds, disjointness,
leakage (`openLeak`, `openToLeak`) and secrecy guarantees. The powers are secret, as the
key context is. The `*_with_powers` functions require the
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

/-- The powers' buffer written by `vg_aes_gcm_store_powers`. -/
def storePowersParam : String × Param := ("pw", .array true .u64 16)

/-- The powers' buffer read by the `*_with_powers` functions. -/
def withPowersParam : String × Param := ("pw", .array false .u64 16)

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

/-- `vg_aes_gcm_store_powers(ctx: *const [u64; 32], pw: *mut [u64; 16])`:
a key context and the powers' buffer. -/
def storePowersSig : Sig where
  params := [("ctx", .array false .u64 32), storePowersParam]

/-- The powers of the hash subkey of the key context at `ctx` (its bytes
240–255, `ctxH`) at `pw`. -/
def storePowersPost (pb : Nat) : storePowersSig.Post pb := fun ctx pw m m' _ =>
  Powers8Repr m' pw (ctxH m ctx)

/-- No precondition: the powers are those of whatever hash subkey the
context holds, as for `prepareContract`. -/
def storePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  storePowersSig.contract A (post := storePowersPost A.ptrBits) (stack := stack)

/-- `vg_aes_gcm_store_powers` on every target. -/
def storePowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_store_powers"
  sig := storePowersSig
  contracts := some fun A stack => storePowersContract A stack
  summary := "Writes to `*pw` the 8 prepared powers of the hash subkey `H` of the key context \
    `*ctx` of `vg_aes_gcm_init` (its bytes 240 to 255, `VG.Spec.Gcm.ctxH`): at byte `32*k`, \
    for `k` from 0 to 3, `preparedPower(H^(2*k+2))` then `preparedPower(H^(2*k+1))`, as two \
    little-endian 128-bit words (`VG.Spec.Gcm.Powers8Repr`, `VG.Spec.Gcm.preparedPower`), \
    as the `*_with_powers` functions require for that key context. It reads only `*ctx` \
    and writes only `*pw`. The key context and the powers are secret: only the pointers may \
    affect timing.\n\n\
    Contract: `VG.Spec.Gcm.storePowersContract`."
  safety := []

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

/-! ## Decryption out of place -/

/-- `vg_aes_gcm_open_to_with_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const u8, tag_len: usize, pw: *const [u64; 16]) -> u32`:
`openToSig` and the powers' buffer. -/
def openToWithPowersSig : Sig where
  params := openToSig.params ++ [withPowersParam]
  ret := some .u32

/-- `openToPre`, and the powers of the key context's hash subkey at `pw`. -/
def openToWithPowersPre (pb : Nat) : Curry (openToWithPowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen pw m =>
    openToPre pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m ∧
      Powers8Repr m pw (ctxH m ctx)

/-- `openToPost`, which does not depend on `pw`. -/
def openToWithPowersPost (pb : Nat) : openToWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _pw m m' r =>
    openToPost pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m m' r

/-- `openToLeak`, which does not depend on `pw`. -/
def openToWithPowersLeak (pb : Nat) : Curry (openToWithPowersSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen _pw =>
    openToLeak pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen

/-- `openToWithPowersPre`, `openToWithPowersPost`, and what `openToContract`
may leak (`openToWithPowersLeak`). -/
def openToWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToWithPowersSig.contract A (pre := openToWithPowersPre A.ptrBits)
    (post := openToWithPowersPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some (openToWithPowersLeak A.ptrBits))

/-- `vg_aes_gcm_open_to_with_powers` on every target. -/
def openToWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_to_with_powers"
  sig := openToWithPowersSig
  writeArgs := true
  contracts := some fun A stack => openToWithPowersContract A stack
  summary := withPowersSummary "vg_aes_gcm_open_to" "openToWithPowersContract"
  safety := openToApi.safety ++ [withPowersSafety]

end VG.Spec.Gcm
