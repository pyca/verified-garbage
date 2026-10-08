import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.TCB.Artifact

/-!
# Blowfish ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, the expanded key and data are
secret: in particular the S-box indices, which are secret bytes of the
data and of the key schedule's intermediate blocks.

The schedule is 4168 bytes: 1042 little-endian 32-bit words, the P-array
P₁…P₁₈ and then the S-boxes S₁…S₄ (`Spec/Blowfish.lean`). Key expansion
and ECB keep their working space on the stack; `stack` accounts for their
frames and calls. ECB permits writes to ABI argument areas, to call
primitives of its own.

The Rust wrapper buffers partial blocks, rejects invalid key lengths
before key expansion, and rejects incomplete input at finalization. It
does not add or remove padding. Empty ECB input is supported.
-/

namespace VG.Spec.Blowfish

/-- `vg_blowfish_expand_key(key: *const u8, key_len: usize,
schedule: *mut [u32; 1042])`. -/
def expandKeySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("schedule", .array true .u32 1042)]

def expandKeyPre (pb : Nat) : Curry (expandKeySig.words pb) (Mem → Prop) :=
  fun _key keyLen _schedule _ => validKey keyLen.toNat

def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key keyLen schedule m m' _ =>
  scheduleAt m' schedule = expandKey (bytesAt m key keyLen.toNat)

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (pre := expandKeyPre A.ptrBits) (post := expandKeyPost A.ptrBits)
    (stack := stack)

def expandKeyApi : Api where
  module := "blowfish"
  name := "vg_blowfish_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "Blowfish key expansion (Schneier, FSE 1994): initializes the P-array and \
    S-boxes with the digits of π, XORs the `key_len` bytes at `key` into the P-array, \
    and replaces the P-array and S-boxes with 521 successive encryptions, writing the \
    1042 words (P₁…P₁₈, then S₁…S₄) to `*schedule`. Weak keys are accepted.\n\n\
    Contract: `VG.Spec.Blowfish.expandKeyContract`. Constant time: only pointers and \
    `key_len` may affect timing, not the key, including the S-box indices of the \
    key schedule's encryptions."
  safety := ["`key_len` must be in 4..=56."]

/-- `(schedule: *const [u32; 1042], data: *mut [[u8; 8]], n: usize)`. -/
def ecbSig : Sig where
  params := [("schedule", .array false .u32 1042), ("data", .slice true (.array .u8 8) "n")]

def ecbPost (direction : Direction) (pb : Nat) : ecbSig.Post pb := fun schedule data n m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) direction (blocksAt m data n.toNat)

def ecbContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (post := ecbPost direction A.ptrBits) (writeArgs := true) (stack := stack)

def ecbEncryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .encrypt stack

def ecbEncryptApi : Api where
  module := "blowfish"
  name := "vg_blowfish_ecb_encrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbEncryptContract A stack
  summary := "Blowfish ECB encryption (SP 800-38A §6.1's construction) of `n` complete \
    8-byte blocks at `data`, in place, under the schedule written by \
    `vg_blowfish_expand_key`. No padding is added or removed. For `n = 0`, no data is \
    transformed.\n\n\
    Contract: `VG.Spec.Blowfish.ecbEncryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including the S-box indices."
  safety := []

def ecbDecryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbContract A .decrypt stack

def ecbDecryptApi : Api where
  module := "blowfish"
  name := "vg_blowfish_ecb_decrypt"
  sig := ecbSig
  writeArgs := true
  contracts := some fun A stack => ecbDecryptContract A stack
  summary := "Blowfish ECB decryption (SP 800-38A §6.1's construction) of `n` complete \
    8-byte blocks at `data`, in place, under the schedule written by \
    `vg_blowfish_expand_key`. No padding is added or removed. For `n = 0`, no data is \
    transformed.\n\n\
    Contract: `VG.Spec.Blowfish.ecbDecryptContract`. Constant time: only pointers and `n` \
    may affect timing, not the schedule or data, including the S-box indices."
  safety := []

end VG.Spec.Blowfish
