module

public import VerifiedGarbage.Spec.Gcm
public import VerifiedGarbage.Spec.Sm4.Ctr

/-!
# SM4-GCM: GCM with SM4

**Trusted** (as every file in `Spec/`). SM4-GCM is GCM (NIST SP 800-38D,
`Spec/Gcm.lean`, defined for any 128-bit block cipher) with SM4's forward
function (draft-ribose-cfrg-sm4-10 §7.1, `Spec/Sm4.lean`) as `CIPH_K`: the
`AEAD_SM4_GCM` of RFC 8998 §3.5.1 ("works as specified in [GCM], using SM4
as the block cipher"), with a 16-byte key. `gcmEncrypt` and `gcmDecrypt`
are GCM-AE and GCM-AD (§7.1, §7.2) for it; `Spec/Sm4/Gcm/Contract.lean`
has the contracts of its functions.
-/

@[expose] public section

namespace VG.Spec.Sm4

/-- `CIPH_K` for GCM: SM4's forward function under the schedule `k`, on GCM's
128-bit blocks (the first byte the most significant, `Gcm.toBytes`). -/
def gcmCipher (k : Schedule) (x : Gcm.Block) : Gcm.Block := Gcm.ofBytes (cipher k (Gcm.toBytes x))

/-- `CIPH_K` for GCM under the 16-byte SM4 key `key` (§7.3's key schedule). -/
def gcmCipherOfKey (key : List Byte) : Gcm.Block → Gcm.Block :=
  gcmCipher (expandKey (Vector.ofFn fun i => key.getD i.val 0))

/-- SM4-GCM authenticated encryption (RFC 8998 §3.5.1, GCM-AE of SP 800-38D
§7.1) under the 16-byte key `key`, with a tag of `t` bytes. -/
def gcmEncrypt (key : List Byte) (t : Nat) (iv p a : List Byte) : List Byte × List Byte :=
  Gcm.encrypt (gcmCipherOfKey key) t iv p a

/-- SM4-GCM authenticated decryption (RFC 8998 §3.5.1, GCM-AD of SP 800-38D
§7.2) under the 16-byte key `key`, with a tag of `t` bytes. -/
def gcmDecrypt (key : List Byte) (t : Nat) (iv c a tag : List Byte) : Option (List Byte) :=
  Gcm.decrypt (gcmCipherOfKey key) t iv c a tag

end VG.Spec.Sm4
