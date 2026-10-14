module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM blocks with a public block index

**Trusted** (as every file in `Spec/`). `vg_aes_gcm_encrypt_blocks_to_prepared_iv96`
and `vg_aes_gcm_decrypt_blocks_prepared_iv96` are
`vg_aes_gcm_encrypt_blocks_to_prepared` and `vg_aes_gcm_decrypt_blocks_prepared`
(`encryptBlocksToPreparedContract`, `decryptBlocksPreparedContract`) with one
more argument, `index`: the rightmost 32 bits of the counter block, as an
integer (`int(LSB₃₂(CB₁))`, §6.2), which the precondition requires them to
be. Their postconditions are those functions' postconditions, unchanged.

`index` is public; the counter block, the key context, `Y` and the data stay
secret, so the other 96 bits of the counter block (with a 96-bit IV, the IV
itself) stay secret. An implementation may branch on `index` and `n`, e.g. to
handle the 32-bit counter wrapping around separately.

`index` is public because, for a 96-bit IV, it is determined by the lengths:
`J₀ = IV ‖ 0³¹ ‖ 1` (NIST SP 800-38D §7.1 step 2, §7.2 step 2), so the
counter block of the plaintext's `i`th block (from 0) has rightmost 32 bits
`2 + i` (§7.1 step 3, `GCTR_K(inc₃₂(J₀), P)`), a function of the position
in the message alone, which the seal and open contracts already make public
(the lengths, `n`). A caller passes `index` only where that holds; with an
IV of any other length, `J₀ = GHASH_H(…)` (§7.1 step 2) depends on the hash
subkey, so its rightmost 32 bits are secret and the caller must use the
functions without `index`.

Existing specifications and contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- `int(LSB₃₂(X))`, the rightmost 32 bits of the block `X` as an integer
(§6.2): what `inc₃₂` increments. -/
def ctrIndex (x : Block) : BitVec 32 := x.extractLsb' 0 32

/-- `vg_aes_gcm_encrypt_blocks_to_prepared`'s parameters, then `index: u32`,
public. -/
def encryptBlocksToPreparedIv96Sig : Sig where
  params := encryptBlocksToPreparedSig.params ++ [("index", .int .u32 true)]

/-- `encryptBlocksToPreparedPre`, and `index` is the rightmost 32 bits of
the counter block. -/
def encryptBlocksToPreparedIv96Pre (pb : Nat) :
    Curry (encryptBlocksToPreparedIv96Sig.words pb) (Mem → Prop) :=
  fun ctx rounds counter y src n dst dstN scratch index m =>
    encryptBlocksToPreparedPre pb ctx rounds counter y src n dst dstN scratch m ∧
      ctrIndex (blockAt m counter) = index

/-- `encryptBlocksToPost`, unchanged. -/
def encryptBlocksToPreparedIv96Post (pb : Nat) : encryptBlocksToPreparedIv96Sig.Post pb :=
  fun ctx rounds counter y src n dst dstN scratch _index =>
    encryptBlocksToPost pb ctx rounds counter y src n dst dstN scratch

/-- For `encryptBlocksToPreparedIv96Pre`: `encryptBlocksToPost`. The key
context, the counter block, `Y` and the data are secret; `rounds`, `n` and
`index` are public. -/
def encryptBlocksToPreparedIv96Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksToPreparedIv96Sig.contract A (pre := encryptBlocksToPreparedIv96Pre A.ptrBits)
    (post := encryptBlocksToPreparedIv96Post A.ptrBits) (stack := stack)

/-- Documents `index`, for both functions. -/
def iv96Summary (name contract : String) : String :=
  "`" ++ name ++ "` with one more argument, `index`, which must be the rightmost 32 bits of " ++
  "the counter block `*counter` as a big-endian integer (`int(LSB₃₂(CB₁))`, NIST SP 800-38D " ++
  "§6.2). Computes the same result. `index` is public and may affect timing; the counter " ++
  "block itself, and so a 96-bit IV, the key context, `Y` and the data stay secret. With a " ++
  "96-bit IV, `index` is `2 + i` for a message's `i`th block (§7.1 steps 2 and 3), a function " ++
  "of the public lengths; with an IV of another length it depends on the hash subkey, and " ++
  "the function without `index` must be used. Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-- `index` must be the counter block's rightmost 32 bits. -/
def iv96Safety : String :=
  "`index` must equal the last 4 bytes of `*counter`, read as a big-endian integer."

/-- `vg_aes_gcm_encrypt_blocks_to_prepared_iv96` on every target. -/
def encryptBlocksToPreparedIv96Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_to_prepared_iv96"
  sig := encryptBlocksToPreparedIv96Sig
  contracts := some fun A stack => encryptBlocksToPreparedIv96Contract A stack
  summary := iv96Summary "vg_aes_gcm_encrypt_blocks_to_prepared"
    "encryptBlocksToPreparedIv96Contract"
  safety := encryptBlocksToPreparedApi.safety ++ [iv96Safety]

/-- `vg_aes_gcm_decrypt_blocks_prepared`'s parameters, then `index: u32`,
public. -/
def decryptBlocksPreparedIv96Sig : Sig where
  params := cryptBlocksPreparedSig.params ++ [("index", .int .u32 true)]

/-- `cryptBlocksPreparedPre`, and `index` is the rightmost 32 bits of the
counter block. -/
def decryptBlocksPreparedIv96Pre (pb : Nat) :
    Curry (decryptBlocksPreparedIv96Sig.words pb) (Mem → Prop) :=
  fun ctx rounds counter y data n scratch index m =>
    cryptBlocksPreparedPre pb ctx rounds counter y data n scratch m ∧
      ctrIndex (blockAt m counter) = index

/-- For `decryptBlocksPreparedIv96Pre`: `decryptBlocksPreparedContract`'s
postcondition, unchanged. The key context, the counter block, `Y` and the
data are secret; `rounds`, `n` and `index` are public. -/
def decryptBlocksPreparedIv96Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptBlocksPreparedIv96Sig.contract A (pre := decryptBlocksPreparedIv96Pre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch _index m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `vg_aes_gcm_decrypt_blocks_prepared_iv96` on every target. -/
def decryptBlocksPreparedIv96Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_decrypt_blocks_prepared_iv96"
  sig := decryptBlocksPreparedIv96Sig
  contracts := some fun A stack => decryptBlocksPreparedIv96Contract A stack
  summary := iv96Summary "vg_aes_gcm_decrypt_blocks_prepared" "decryptBlocksPreparedIv96Contract"
  safety := decryptBlocksPreparedApi.safety ++ [iv96Safety]

end VG.Spec.Gcm
