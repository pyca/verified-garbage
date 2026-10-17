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

No function computes the buffer on its own. Each `*_store_powers` function is
a plain function (`vg_aes_gcm_seal`, `vg_aes_gcm_open`,
`vg_aes_gcm_seal_gather`, `vg_ghash`), with its unchanged postcondition, that
also writes to a 128-byte buffer the powers of the hash subkey that it
computes for its own GHASH. A caller uses it for the call that first needs
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

/-- `vg_aes_gcm_seal_store_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16], pw: *mut [u64; 16])`:
`sealSig` and the powers' buffer. -/
def sealStorePowersSig : Sig where
  params := sealSig.params ++ [storePowersParam]

/-- `sealPost`, and the powers of the key context's hash subkey at `pw`. -/
def sealStorePowersPost (pb : Nat) : sealStorePowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag pw m m' r =>
    sealPost pb ctx rounds nonce nonceLen aad aadLen data len tag m m' r ∧
      Powers8Repr m' pw (ctxH m ctx)

/-- `sealPre`, and `sealStorePowersPost`. -/
def sealStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealStorePowersSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _pw =>
      sealPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (post := sealStorePowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_store_powers` on every target. -/
def sealStorePowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_store_powers"
  sig := sealStorePowersSig
  writeArgs := true
  contracts := some fun A stack => sealStorePowersContract A stack
  summary := storePowersSummary "vg_aes_gcm_seal" "sealStorePowersContract"
  safety := sealApi.safety

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

/-- `openPre`, `openStorePowersPost`, and what `openContract` may leak. -/
def openStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openStorePowersSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw =>
      openPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
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
  safety := openApi.safety

/-- `vg_aes_gcm_seal_gather_store_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16], pw: *mut [u64; 16])`:
`sealGatherSig` and the powers' buffer. -/
def sealGatherStorePowersSig : Sig where
  params := sealGatherSig.params ++ [storePowersParam]

/-- `sealGatherPost`, and the powers of the key context's hash subkey at `pw`. -/
def sealGatherStorePowersPost (pb : Nat) : sealGatherStorePowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag pw m m' r =>
    sealGatherPost pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' r ∧
      Powers8Repr m' pw (ctxH m ctx)

/-- `sealGatherPre`, and `sealGatherStorePowersPost`. -/
def sealGatherStorePowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherStorePowersSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _pw =>
      sealGatherPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := sealGatherStorePowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_store_powers` on every target. -/
def sealGatherStorePowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_store_powers"
  sig := sealGatherStorePowersSig
  writeArgs := true
  contracts := some fun A stack => sealGatherStorePowersContract A stack
  summary := storePowersSummary "vg_aes_gcm_seal_gather" "sealGatherStorePowersContract"
  safety := sealGatherApi.safety

/-! ## Reading the powers -/

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

/-- `vg_aes_gcm_seal_gather_with_powers(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16], pw: *const [u64; 16])`:
`sealGatherSig` and the powers' buffer. -/
def sealGatherWithPowersSig : Sig where
  params := sealGatherSig.params ++ [withPowersParam]

/-- `sealGatherPre`, and the powers of the key context's hash subkey at `pw`. -/
def sealGatherWithPowersPre (pb : Nat) :
    Curry (sealGatherWithPowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag pw m =>
    sealGatherPre pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m ∧
      Powers8Repr m pw (ctxH m ctx)

/-- `sealGatherPost`, which does not depend on `pw`. -/
def sealGatherWithPowersPost (pb : Nat) : sealGatherWithPowersSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _pw m m' r =>
    sealGatherPost pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' r

/-- `sealGatherWithPowersPre` and `sealGatherWithPowersPost`. -/
def sealGatherWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherWithPowersSig.contract A (pre := sealGatherWithPowersPre A.ptrBits)
    (post := sealGatherWithPowersPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_with_powers` on every target. -/
def sealGatherWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_with_powers"
  sig := sealGatherWithPowersSig
  writeArgs := true
  contracts := some fun A stack => sealGatherWithPowersContract A stack
  summary := withPowersSummary "vg_aes_gcm_seal_gather" "sealGatherWithPowersContract"
  safety := sealGatherApi.safety ++ [withPowersSafety]

/-! ## GHASH -/

/-- `vg_ghash_store_powers(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32], pw: *mut [u64; 16])`:
`ghashSig` and the powers' buffer. `scratch` is working space. -/
def ghashStorePowersSig : Sig where
  params := ghashSig.params ++ [storePowersParam]

/-- `ghashContract`'s postcondition, and the powers of the hash subkey at `h`
at `pw`. -/
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
  summary := storePowersSummary "vg_ghash" "ghashStorePowersContract" ++
    " Only the pointers and `n` may affect timing."
  safety := ghashApi.safety

/-- `vg_ghash_with_powers(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32], pw: *const [u64; 16])`:
`ghashSig` and the powers' buffer. `scratch` is working space. -/
def ghashWithPowersSig : Sig where
  params := ghashSig.params ++ [withPowersParam]

/-- `ghashContract`'s postcondition, given the powers of the hash subkey at
`h` at `pw`. -/
def ghashWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ghashWithPowersSig.contract A
    (pre := fun h _y _data _n _scratch pw m => Powers8Repr m pw (blockAt m h))
    (post := fun h y data n _scratch _pw m m' _ =>
      blockAt m' y = ghashFrom (blockAt m h) (blockAt m y) (blocksAt m data n.toNat))
    (stack := stack)

/-- `vg_ghash_with_powers` on every target. -/
def ghashWithPowersApi : Api where
  module := "gcm"
  name := "vg_ghash_with_powers"
  sig := ghashWithPowersSig
  contracts := some fun A stack => ghashWithPowersContract A stack
  summary := "`vg_ghash` with the 8 prepared powers of the hash subkey `H` at `h` at `*pw` \
    (`VG.Spec.Gcm.Powers8Repr`), which it may read instead of computing them. Replaces the \
    block `Y` at `*y` with `Yₙ`, where `Y₀ = Y` and `Yᵢ = (Yᵢ₋₁ ⊕ Xᵢ) • H` for the `n` \
    16-byte blocks `X₁ … Xₙ` starting at `data` (NIST SP 800-38D §6.4). The hash subkey, its \
    powers, `Y` and the data are secret.\n\n\
    Contract: `VG.Spec.Gcm.ghashWithPowersContract`. Constant time: only the pointers and `n` \
    may affect timing."
  safety := ghashApi.safety ++ ["`*pw` must be what a `*_store_powers` function wrote for the \
      hash subkey at `h` (the contract's precondition: `VG.Spec.Gcm.Powers8Repr` of `pw` and \
      that subkey)."]

end VG.Spec.Gcm
