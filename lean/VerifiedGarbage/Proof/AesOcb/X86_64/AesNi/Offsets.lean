module

public import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.AesOcb.X86_64.LNtz
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks
-- separate module: the one-pass proofs are a chain of modules (`Offsets`, `Setup`, `Pass`, `Front`, `Top`), so that a change rebuilds only the modules after it

/-!
# One-pass AES-OCB with AES-NI on x86-64: the offsets of a group

Untrusted: everything here is checked by Lean. The blocks `8k + t` of a
pass, for `t` from 1 to 7, have the offsets `Offset_{8k} ⊕ C[t]`
(`offAt_group`), where `C[t]` (`cAt`) is the XOR of `L_0`, `L_1` and `L_2`
that `ntz(8k + t)` gives: 0, 1, 0, 2, 0, 1, 0. The eighth's is
`Offset_{8k} ⊕ L_2 ⊕ L_{3 + ntz(k + 1)}` (`offAt_eighth`), and
`L_{3 + m}` is `L_3` doubled `m` times (`lAt_three_add`). AES on a block
register (`aesWith_rv`, `aesInvWith_rv`) is OCB's `ENCIPHER` and `DECIPHER`
on its block (`rv`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64
open VG.Spec.Ocb (Block lAt ntz double aesWith aesInvWith blockAtMem)
open VG.Proof.Ocb (offAt ntz_odd ntz_even)
open VG.Proof.AesOcb.X86_64 (rv blockAtMem_eq blockAtMem_writeW)

/-- `C[t]`, for `t` from 1 to 7: the XOR of the `L_{ntz(8k + u)}`, `u` from
1 to `t`. -/
def cAt (l : Block) : Nat → Block
  | 1 => lAt l 0
  | 2 => lAt l 0 ^^^ lAt l 1
  | 3 => lAt l 1
  | 4 => lAt l 1 ^^^ lAt l 2
  | 5 => lAt l 0 ^^^ lAt l 1 ^^^ lAt l 2
  | 6 => lAt l 0 ^^^ lAt l 2
  | 7 => lAt l 2
  | _ => 0

theorem lAt_succ (l : Block) (j : Nat) : lAt l (j + 1) = double (lAt l j) := rfl

/-- `L_{3 + m}` is `L_3` doubled `m` times. -/
theorem lAt_three_add (l : Block) (m : Nat) : lAt l (3 + m) = Nat.repeat double m (lAt l 3) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, lAt_succ, ih]; rfl

theorem ntz_8k_odd (k u : Nat) (hu : u % 2 = 1) : ntz (8 * k + u) = 0 := ntz_odd (by omega_arith)

theorem ntz_8k2 (k : Nat) : ntz (8 * k + 2) = 1 := by
  rw [ntz_even (by omega_arith) (by omega_arith), show (8 * k + 2) / 2 = 2 * (2 * k) + 1 by omega_arith,
    ntz_odd (by omega_arith)]

theorem ntz_8k6 (k : Nat) : ntz (8 * k + 6) = 1 := by
  rw [ntz_even (by omega_arith) (by omega_arith), show (8 * k + 6) / 2 = 2 * (2 * k + 1) + 1 by omega_arith,
    ntz_odd (by omega_arith)]

theorem ntz_8k4 (k : Nat) : ntz (8 * k + 4) = 2 := by
  rw [ntz_even (by omega_arith) (by omega_arith), show (8 * k + 4) / 2 = 4 * k + 2 by omega_arith,
    ntz_even (by omega_arith) (by omega_arith), show (4 * k + 2) / 2 = 2 * k + 1 by omega_arith,
    ntz_odd (by omega_arith)]

theorem ntz_8k8 (k : Nat) : ntz (8 * k + 8) = 3 + ntz (k + 1) := by
  rw [ntz_even (by omega_arith) (by omega_arith), show (8 * k + 8) / 2 = 4 * k + 4 by omega_arith,
    ntz_even (by omega_arith) (by omega_arith), show (4 * k + 4) / 2 = 2 * k + 2 by omega_arith,
    ntz_even (by omega_arith) (by omega_arith), show (2 * k + 2) / 2 = k + 1 by omega_arith]
  omega_arith

theorem offAt_succ (o0 l : Block) (i : Nat) : offAt o0 l (i + 1) = offAt o0 l i ^^^ lAt l (ntz (i + 1)) := rfl

/-- The offsets of the blocks `8k + t` of a group, `t` from 1 to 7. -/
theorem offAt_group (o0 l : Block) (k : Nat) :
    ∀ t, 1 ≤ t → t ≤ 7 → offAt o0 l (8 * k + t) = offAt o0 l (8 * k) ^^^ cAt l t := by
  have h1 : offAt o0 l (8 * k + 1) = offAt o0 l (8 * k) ^^^ cAt l 1 := by
    rw [offAt_succ, ntz_8k_odd k 1 (by decide)]; rfl
  have h2 : offAt o0 l (8 * k + 2) = offAt o0 l (8 * k) ^^^ cAt l 2 := by
    rw [offAt_succ, show 8 * k + 1 + 1 = 8 * k + 2 by omega_arith, ntz_8k2, h1]
    simp only [cAt, BitVec.xor_assoc]
  have h3 : offAt o0 l (8 * k + 3) = offAt o0 l (8 * k) ^^^ cAt l 3 := by
    rw [offAt_succ, show 8 * k + 2 + 1 = 8 * k + 3 by omega_arith, ntz_8k_odd k 3 (by decide), h2]
    simp only [cAt, BitVec.xor_assoc, BitVec.xor_comm (lAt l 1), ← BitVec.xor_assoc (lAt l 0),
      BitVec.xor_self, BitVec.zero_xor]
  have h4 : offAt o0 l (8 * k + 4) = offAt o0 l (8 * k) ^^^ cAt l 4 := by
    rw [offAt_succ, show 8 * k + 3 + 1 = 8 * k + 4 by omega_arith, ntz_8k4, h3]
    simp only [cAt, BitVec.xor_assoc]
  have h5 : offAt o0 l (8 * k + 5) = offAt o0 l (8 * k) ^^^ cAt l 5 := by
    rw [offAt_succ, show 8 * k + 4 + 1 = 8 * k + 5 by omega_arith, ntz_8k_odd k 5 (by decide), h4]
    simp only [cAt, BitVec.xor_assoc, BitVec.xor_comm (lAt l 2) (lAt l 0),
      ← BitVec.xor_assoc (lAt l 1) (lAt l 0), BitVec.xor_comm (lAt l 1) (lAt l 0)]
  have h6 : offAt o0 l (8 * k + 6) = offAt o0 l (8 * k) ^^^ cAt l 6 := by
    rw [offAt_succ, show 8 * k + 5 + 1 = 8 * k + 6 by omega_arith, ntz_8k6, h5]
    simp only [cAt, BitVec.xor_assoc, BitVec.xor_comm (lAt l 2) (lAt l 1),
      ← BitVec.xor_assoc (lAt l 1) (lAt l 1), BitVec.xor_self, BitVec.zero_xor]
  have h7 : offAt o0 l (8 * k + 7) = offAt o0 l (8 * k) ^^^ cAt l 7 := by
    rw [offAt_succ, show 8 * k + 6 + 1 = 8 * k + 7 by omega_arith, ntz_8k_odd k 7 (by decide), h6]
    simp only [cAt, BitVec.xor_assoc, BitVec.xor_comm (lAt l 2) (lAt l 0),
      ← BitVec.xor_assoc (lAt l 0) (lAt l 0), BitVec.xor_self, BitVec.zero_xor]
  intro t ht ht'
  rcases (by omega_arith : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4, h5, h6, h7]

/-- The offset of the eighth block of the group `k`. -/
theorem offAt_eighth (o0 l : Block) (k : Nat) :
    offAt o0 l (8 * (k + 1)) = offAt o0 l (8 * k) ^^^ (lAt l 2 ^^^ lAt l (3 + ntz (k + 1))) := by
  rw [show 8 * (k + 1) = 8 * k + 7 + 1 by omega_arith, offAt_succ, offAt_group o0 l k 7 (by decide) (by decide),
    show 8 * k + 7 + 1 = 8 * k + 8 by omega_arith, ntz_8k8]
  simp only [cAt, BitVec.xor_assoc]

/-! ## AES on a block register -/

/-- AES-NI's `cipher` of a block register is `ENCIPHER` of its block. -/
theorem aesWith_rv {nr : Nat} {w : List Byte} {v v' : BitVec 128}
    (h : Proof.Aes.X86_64.AesNi.st v' = Spec.Aes.cipher nr w (Proof.Aes.X86_64.AesNi.st v)) :
    aesWith nr w (rv v) = rv v' := by
  have e := Proof.Ocb.blockAtMem_of_state (m := Mem.writeW (fun _ => 0) 0 v) (m' := Mem.writeW (fun _ => 0) 0 v') (p := 0)
    (Spec.Aes.cipher nr w) (by
      rw [Proof.Aes.X86_64.AesNi.stateAt_eq, Proof.Aes.X86_64.AesNi.stateAt_eq,
        Mem.readW_writeW_self _ _ 16 _ (by decide), Mem.readW_writeW_self _ _ 16 _ (by decide), h])
  rw [blockAtMem_writeW, blockAtMem_writeW] at e
  exact e.symm

/-- AES-NI's `invCipher` of a block register is `DECIPHER` of its block. -/
theorem aesInvWith_rv {nr : Nat} {w : List Byte} {v v' : BitVec 128}
    (h : Proof.Aes.X86_64.AesNi.st v' = Spec.Aes.invCipher nr w (Proof.Aes.X86_64.AesNi.st v)) :
    aesInvWith nr w (rv v) = rv v' := by
  have e := Proof.Ocb.blockAtMem_of_state (m := Mem.writeW (fun _ => 0) 0 v) (m' := Mem.writeW (fun _ => 0) 0 v') (p := 0)
    (Spec.Aes.invCipher nr w) (by
      rw [Proof.Aes.X86_64.AesNi.stateAt_eq, Proof.Aes.X86_64.AesNi.stateAt_eq,
        Mem.readW_writeW_self _ _ 16 _ (by decide), Mem.readW_writeW_self _ _ 16 _ (by decide), h])
  rw [blockAtMem_writeW, blockAtMem_writeW] at e
  exact e.symm

end VG.Proof.AesOcb.X86_64.AesNi
