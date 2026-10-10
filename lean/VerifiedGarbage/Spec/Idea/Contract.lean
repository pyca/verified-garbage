module

public import VerifiedGarbage.Spec.Idea
public import VerifiedGarbage.TCB.Artifact

/-!
# IDEA ECB: contracts on every target

**Trusted.** `Sig.contract` supplies validity, separation, permitted writes
and public pointers/lengths. Key bytes, subkeys and data are secret. A
subkey schedule is 52 little-endian 16-bit words (104 bytes), `Z₁ … Z₅₂`:
`vg_idea_expand_key` writes the encryption subkeys of a key, and
`vg_idea_invert_key` the decryption subkeys of encryption subkeys.
`vg_idea_ecb` runs the cipher under either: it encrypts under encryption
subkeys and decrypts under decryption subkeys, so ECB encryption and
decryption are the one function. The functions keep their working space
on the stack, which `stack` accounts for.

The Rust wrapper will buffer partial blocks and reject incomplete input at
finalization. It will not add or remove padding. Empty ECB input is
supported.
-/

@[expose] public section

namespace VG.Spec.Idea

/-- `vg_idea_expand_key(key: *const [u8; 16], schedule: *mut [u8; 104])`. -/
def expandKeySig : Sig where
  params := [("key", .array false .u8 16), ("schedule", .array true .u8 104)]

def expandKeyPost (pb : Nat) : expandKeySig.Post pb := fun key schedule m m' _ =>
  scheduleAt m' schedule = expandKey (keyAt m key)

def expandKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  expandKeySig.contract A (post := expandKeyPost A.ptrBits) (stack := stack)

def expandKeyApi : Api where
  module := "idea"
  name := "vg_idea_expand_key"
  sig := expandKeySig
  contracts := some fun A stack => expandKeyContract A stack
  summary := "IDEA encryption key schedule (Lai, 1992, §3.3): writes the 52 encryption \
    subkeys of the 16-byte key at `key` (as eight big-endian 16-bit words, rotated left by \
    25 bits after every eight subkeys) to `*schedule`, as little-endian 16-bit words.\n\n\
    Contract: `VG.Spec.Idea.expandKeyContract`. Constant time: only pointers may affect \
    timing, not the key."
  safety := []

/-- `vg_idea_invert_key(schedule: *const [u8; 104], inverse: *mut [u8; 104])`. -/
def invertKeySig : Sig where
  params := [("schedule", .array false .u8 104), ("inverse", .array true .u8 104)]

def invertKeyPost (pb : Nat) : invertKeySig.Post pb := fun schedule inverse m m' _ =>
  scheduleAt m' inverse = invertKey (scheduleAt m schedule)

def invertKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  invertKeySig.contract A (post := invertKeyPost A.ptrBits) (stack := stack)

def invertKeyApi : Api where
  module := "idea"
  name := "vg_idea_invert_key"
  sig := invertKeySig
  contracts := some fun A stack => invertKeyContract A stack
  summary := "IDEA decryption key schedule (Lai, 1992, §3.3): writes to `*inverse` the 52 \
    decryption subkeys of the 52 encryption subkeys at `schedule` (both as little-endian \
    16-bit words, as `vg_idea_expand_key` writes them): the multiplicative inverses modulo \
    2^16 + 1 (with 0 standing for 2^16), additive inverses modulo 2^16 and copies of the \
    encryption subkeys, in reverse round order.\n\n\
    Contract: `VG.Spec.Idea.invertKeyContract`. Constant time: only pointers may affect \
    timing, not the subkeys, including those that are 0 or 1."
  safety := []

/-- `vg_idea_ecb(schedule: *const [u8; 104], data: *mut [[u8; 8]], n: usize)`. -/
def ecbSig : Sig where
  params := [("schedule", .array false .u8 104), ("data", .slice true (.array .u8 8) "n")]

def ecbPost (pb : Nat) : ecbSig.Post pb := fun schedule data n m m' _ =>
  blocksAt m' data n.toNat = ecb (scheduleAt m schedule) (blocksAt m data n.toNat)

def ecbContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (post := ecbPost A.ptrBits) (stack := stack)

def ecbApi : Api where
  module := "idea"
  name := "vg_idea_ecb"
  sig := ecbSig
  contracts := some fun A stack => ecbContract A stack
  summary := "IDEA in ECB mode (Lai, 1992, §3.3; SP 800-38A §6.1) on `n` complete 8-byte \
    blocks at `data`, in place, under the 52 subkeys at `schedule`: encryption under the \
    subkeys `vg_idea_expand_key` writes, decryption under those `vg_idea_invert_key` writes. \
    No padding is added or removed. For `n = 0`, no data is transformed.\n\n\
    Contract: `VG.Spec.Idea.ecbContract`. Constant time: only pointers and `n` may affect \
    timing, not the subkeys or data, including words or subkeys that are 0."
  safety := []

end VG.Spec.Idea
