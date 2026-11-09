module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# CAST5: the contracts on the subkeys and the number of rounds they are given

Not trusted: the contracts that the proofs of CAST5's ECB, CBC, CFB64 and
OFB functions are written against, for the subkeys and the number of rounds
they are given, whatever key the subkeys came from. The shared contracts in
`Spec/` are stated for every key whose subkeys are in memory with the
number of rounds of its length (`Spec.Cast5.KeySchedule`), and follow from
these (`Verified.post_mono`).
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG.Spec
open VG.Spec.Cast5

def ecbRoundsPost (direction : Direction) (pb : Nat) : ecbSig.Post pb :=
  fun schedule rounds data n _scratch m m' _ =>
    blocksAt m' data n.toNat =
      ecb (scheduleAt m schedule) rounds.toNat direction (blocksAt m data n.toNat)

/-- For `rounds` of 12 or 16: replaces the `n` blocks at `data` with their
encryption or decryption under the subkeys at `schedule`. -/
def ecbRoundsContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) : Contract M :=
  ecbSig.contract A (pre := ecbPre A.ptrBits) (post := ecbRoundsPost direction A.ptrBits)
    (stack := stack)

def ecbEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbRoundsContract A .encrypt stack

def ecbDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ecbRoundsContract A .decrypt stack

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the
`n` blocks at `data` with their CBC encryption (§6.2) by CAST5, from the
chaining value at `iv`, and the chaining value with the last ciphertext
block (unchanged if `n = 0`), as `Cbc.aesEncryptContract` does. -/
def cbcEncryptChainedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (pre := fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := Cbc.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8)
        (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the
`n` blocks at `data` with their CBC decryption (§6.2) by CAST5, from the
chaining value at `iv`, and the chaining value with the last ciphertext
block, the last block at `data` on entry (unchanged if `n = 0`), as
`Cbc.aesDecryptContract` does. -/
def cbcDecryptChainedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcChainedSig.contract A
    (pre := fun _schedule rounds _iv _data _n _ => rounds.toNat = 12 ∨ rounds.toNat = 16)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat =
          Cbc.decrypt (invCipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CFB64 encryption (§6.3) by CAST5, from the block
at `iv`, and that block with the last ciphertext block (unchanged if
`n = 0`). -/
def cfbEncryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := Cfb.encrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat)
      cbcBlocksAt m' data n.toNat = cs ∧ Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their CFB64 decryption (§6.3) by CAST5, from the block
at `iv`, and that block with the last ciphertext block, the last block at
`data` on entry (unchanged if `n = 0`). -/
def cfbDecryptRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cfbSig.contract A (pre := cfbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let cs := cbcBlocksAt m data n.toNat
      cbcBlocksAt m' data n.toNat = Cfb.decrypt (cipher (scheduleAt m schedule) rounds.toNat) (Aes.bytesAt m iv 8) cs ∧
        Aes.bytesAt m' iv 8 = Cbc.next (Aes.bytesAt m iv 8) cs)
    (writeArgs := true) (stack := stack)

/-- For `rounds` of 12 or 16, with the subkeys at `schedule`: replaces the `n`
blocks at `data` with their OFB encryption or decryption (§6.4) by CAST5,
from the block at `iv`, and that block with the last output block `Oₙ`
(unchanged if `n = 0`). -/
def ofbRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  ofbSig.contract A (pre := ofbPre A.ptrBits)
    (post := fun schedule rounds iv data n m m' _ =>
      let ciph := cipher (scheduleAt m schedule) rounds.toNat
      cbcBlocksAt m' data n.toNat = Ofb.crypt ciph (Aes.bytesAt m iv 8) (cbcBlocksAt m data n.toNat) ∧
        Aes.bytesAt m' iv 8 = Ofb.next ciph (Aes.bytesAt m iv 8) n.toNat)
    (writeArgs := true) (stack := stack)

/-- `Spec.Cast5.ecbEncryptContract` from `ecbEncryptRoundsContract`. -/
theorem ecbEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ecbEncryptRoundsContract A stack)) : Verified T c (Spec.Cast5.ecbEncryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only [ecbRoundsPost, Spec.Cast5.ecbPost] at hp ⊢
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.ecbDecryptContract` from `ecbDecryptRoundsContract`. -/
theorem ecbDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ecbDecryptRoundsContract A stack)) : Verified T c (Spec.Cast5.ecbDecryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only [ecbRoundsPost, Spec.Cast5.ecbPost] at hp ⊢
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.cbcEncryptChainedContract` from `cbcEncryptChainedRoundsContract`. -/
theorem cbcEncryptChained_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cbcEncryptChainedRoundsContract A stack)) : Verified T c (Spec.Cast5.cbcEncryptChainedContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.cbcDecryptChainedContract` from `cbcDecryptChainedRoundsContract`. -/
theorem cbcDecryptChained_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cbcDecryptChainedRoundsContract A stack)) : Verified T c (Spec.Cast5.cbcDecryptChainedContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.cfbEncryptContract` from `cfbEncryptRoundsContract`. -/
theorem cfbEncrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbEncryptRoundsContract A stack)) : Verified T c (Spec.Cast5.cfbEncryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.cfbDecryptContract` from `cfbDecryptRoundsContract`. -/
theorem cfbDecrypt_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (cfbDecryptRoundsContract A stack)) : Verified T c (Spec.Cast5.cfbDecryptContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

/-- `Spec.Cast5.ofbContract` from `ofbRoundsContract`. -/
theorem ofb_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (ofbRoundsContract A stack)) : Verified T c (Spec.Cast5.ofbContract A stack) :=
  h.post_mono fun _ _ _ _ _ _ _ _ hp key ⟨_, hr, hw⟩ => by
    dsimp only at hp
    rw [hw, hr] at hp
    exact hp

end VG.Proof.Cast5
