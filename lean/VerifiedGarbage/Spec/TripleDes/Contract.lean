module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.Artifact

/-!
# Triple DES ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, round keys and data are secret.
The schedule has 48 little-endian 64-bit slots (384 bytes), in encryption
order for K1, K2 and K3. Expansion zero-extends each 48-bit round key.
The block functions' scratch contents are unspecified on return; key
expansion and ECB keep their working space on the stack. `stack` accounts
for frames and calls; ECB permits writes to ABI argument areas to call block
primitives.

The Rust wrapper will buffer partial blocks, reject invalid key lengths
before key expansion, and reject incomplete input at finalization. It will
not add or remove padding. Empty ECB input is supported.
-/

@[expose] public section

namespace VG.Spec.TripleDes

def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u8 384)]

def expandKeyPre (pb : Nat) : Curry (expandKeySig.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _ => validKey keyLen.toNat

def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key keyLen schedule m m' _ =>
  scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat)

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (pre := expandKeyPre A.ptrBits) (post := expandKeyPost A.ptrBits)
    (stack := stack)

def expandKeyApi : Api where
  module := "triple_des"
  name := "vg_triple_des_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "Triple DES key expansion (FIPS 46-3 Appendix 1): expands a 16- or 24-byte key \
    into three encryption-order DES schedules, each containing sixteen 48-bit round keys \
    zero-extended into little-endian 64-bit slots. For a 16-byte key, K3 repeats K1. \
    Parity bits are ignored and weak or repeated component keys are accepted.\n\n\
    Contract: `VG.Spec.TripleDes.expandKeyContract`. Constant time: only pointers and \
    `key_len` may affect timing, not key bytes."
  safety := ["`key_len` must be 16 or 24."]

def blockSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .array true .u8 8),
    ("scratch", .array true .u64 64)]

def encryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = encryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def encryptBlockApi : Api where
  module := "triple_des"
  name := "vg_triple_des_encrypt_block"
  sig := blockSig
  contracts := some fun A stack => encryptBlockContract A stack
  summary := "Triple DES block encryption (FIPS 46-3): transforms the 8 bytes at `data` \
    in place under the three DES schedules at `schedule`. Each schedule contains sixteen \
    encryption-order 48-bit round keys in little-endian 64-bit slots; upper bits are ignored.\n\n\
    Contract: `VG.Spec.TripleDes.encryptBlockContract`. Constant time: only pointers \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

def decryptBlockContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  blockSig.contract A
    (post := fun schedule data _scratch m m' _ =>
      blockAt m' data = decryptBlock (scheduleAt m schedule) (blockAt m data))
    (stack := stack)

def decryptBlockApi : Api where
  module := "triple_des"
  name := "vg_triple_des_decrypt_block"
  sig := blockSig
  contracts := some fun A stack => decryptBlockContract A stack
  summary := "Triple DES block decryption (FIPS 46-3): transforms the 8 bytes at `data` \
    in place under the three DES schedules at `schedule`. Each schedule contains sixteen \
    encryption-order 48-bit round keys in little-endian 64-bit slots; upper bits are ignored.\n\n\
    Contract: `VG.Spec.TripleDes.decryptBlockContract`. Constant time: only pointers \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := ["The contents of `scratch` on return are unspecified."]

def ecbSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .slice true (.array .u8 8) "n")]

def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule data n m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) direction (blocksAt m data n.toNat)

def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (post := ecbPost direction A.ptrBits) (writeArgs := true) (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbEncryptApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_encrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "Triple DES ECB encryption (SP 800-38A §6.1) of `n` complete 8-byte \
    blocks at `data`, in place, under the schedule written by `vg_triple_des_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbEncryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := []

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

def ecbDecryptApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_decrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "Triple DES ECB decryption (SP 800-38A §6.1) of `n` complete 8-byte \
    blocks at `data`, in place, under the schedule written by `vg_triple_des_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbDecryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := []

/-! ## ECB with its working space as an argument

The ECB functions above keep their working space in a frame of their own. The
same computation with the working space passed in (`scratch`, 1024 bytes,
whatever it holds) is a function of its own, so that the ECB functions of a
target, each with its own wide loop for the blocks it handles at a time, can
call one copy of the code for the blocks left. -/

def ecbCoreSig : Sig where
  params := [("schedule", .array false .u8 384), ("data", .slice true (.array .u8 8) "n"),
    ("scratch", .array true .u64 128)]

/-- `ecbContract`, whatever `scratch` is. -/
def ecbCoreContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbCoreSig.contract A
    (post := fun schedule data n _scratch => ecbPost direction A.ptrBits schedule data n)
    (writeArgs := true) (stack := stack)

def ecbEncryptCoreContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbCoreContract A .encrypt stack

def ecbDecryptCoreContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbCoreContract A .decrypt stack

def ecbEncryptCoreApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_encrypt_core"
  sig := ecbCoreSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptCoreContract A stack
  summary := "Triple DES ECB encryption (SP 800-38A §6.1) of `n` complete 8-byte blocks at \
    `data`, in place, under the schedule written by `vg_triple_des_expand_key`, with the \
    1024 bytes at `scratch` as working space: `vg_triple_des_ecb_encrypt` without its own \
    frame. No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbEncryptCoreContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := ["The contents of `scratch` on return are unspecified."]

def ecbDecryptCoreApi : Api where
  module := "triple_des"
  name := "vg_triple_des_ecb_decrypt_core"
  sig := ecbCoreSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptCoreContract A stack
  summary := "Triple DES ECB decryption (SP 800-38A §6.1) of `n` complete 8-byte blocks at \
    `data`, in place, under the schedule written by `vg_triple_des_expand_key`, with the \
    1024 bytes at `scratch` as working space: `vg_triple_des_ecb_decrypt` without its own \
    frame. No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.TripleDes.ecbDecryptCoreContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data."
  safety := ["The contents of `scratch` on return are unspecified."]

end VG.Spec.TripleDes
