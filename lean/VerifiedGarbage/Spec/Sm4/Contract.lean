module

public import VerifiedGarbage.Spec.Sm4
public import VerifiedGarbage.TCB.Artifact

/-!
# SM4 ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, round keys and data are secret.
The schedule has 32 little-endian 32-bit round keys (128 bytes),
`rk_0`, …, `rk_31`. `stack` accounts for frames and calls; ECB
permits writes to ABI argument areas to call block primitives.

The Rust wrapper will reject input that is not a whole number of 16-byte
blocks. It will not add or remove padding. Empty ECB input is supported.
-/

@[expose] public section

namespace VG.Spec.Sm4

def expandKeySig : Sig where
  params := [("key", .array false .u8 16), ("schedule", .array true .u8 128)]

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A
    (post := fun key schedule m m' _ => scheduleAt m' schedule = expandKey (blockAt m key))
    (stack := stack)

def expandKeyApi : Api where
  module := "sm4"
  name := "vg_sm4_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "SM4 key expansion (draft-ribose-cfrg-sm4-10 §7.3): expands the 16-byte key at `key` into \
    the 32 round keys, written to `schedule` as 32 \
    little-endian 32-bit words `rk_0`, …, `rk_31`.\n\n\
    Contract: `VG.Spec.Sm4.expandKeyContract`. Constant time: only pointers may affect \
    timing, not key bytes."
  safety := []

def ecbSig : Sig where
  params := [("schedule", .array false .u8 128), ("data", .slice true (.array .u8 16) "n")]

def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule data n m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) direction (blocksAt m data n.toNat)

def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (post := ecbPost direction A.ptrBits) (writeArgs := true) (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbEncryptApi : Api where
  module := "sm4"
  name := "vg_sm4_ecb_encrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "SM4 ECB encryption (draft-ribose-cfrg-sm4-10 §7.1, SP 800-38A §6.1) of `n` complete 16-byte \
    blocks at `data`, in place, under the schedule written by `vg_sm4_expand_key`. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Sm4.ecbEncryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := []

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

def ecbDecryptApi : Api where
  module := "sm4"
  name := "vg_sm4_ecb_decrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "SM4 ECB decryption (draft-ribose-cfrg-sm4-10 §7.2, SP 800-38A §6.1) of `n` complete 16-byte \
    blocks at `data`, in place, under the schedule written by `vg_sm4_expand_key`: the \
    encryption procedure with the round keys in reverse order. No padding is added or \
    removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Sm4.ecbDecryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including S-box inputs."
  safety := []

end VG.Spec.Sm4
