module

public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Spec.Blowfish.Cbc
import Mathlib.Tactic.SplitIfs

/-!
# Blowfish's blocks as the modes see them

What every target's core for the modes (`Proof/Blowfish/<Target>/ModeCore.lean`)
needs: a block's bytes as the modes read them (`bytesAt_eq`,
`cbcBlocksAt_eq`) and the cipher of a direction on them (`dirCipher`,
`dirCipher_bytes`).
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 8 = (blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, blockAt]

theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    cbcBlocksAt m p n = Modes.blocksOf 8 m p n := by
  simp only [cbcBlocksAt, blocksAt, Modes.blocksOf, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-- A block's encryption (`up`) or decryption. -/
def dirBlock (k : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock k b else decryptBlock k b

/-- The cipher of the direction `up`: `CIPH_K` or `CIPH⁻¹_K`. -/
def dirCipher (up : Bool) (k : Schedule) : Spec.Cbc.Cipher :=
  if up then cipher k else invCipher k

theorem dirCipher_bytes (up : Bool) (k : Schedule) (m : Mem) (p : Addr) :
    dirCipher up k (Spec.Aes.bytesAt m p 8) = (dirBlock k up (blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 8 => (Spec.Aes.bytesAt m p 8).getD i.val 0) = blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, blockAt]
  cases up <;> simp only [dirCipher, dirBlock, cipher, invCipher, h, ite_true, Bool.false_eq_true, ite_false]

theorem dirCipher_len (up : Bool) (k : Schedule) (b : List Byte) : (dirCipher up k b).length = 8 := by
  cases up <;> simp [dirCipher, cipher, invCipher]

end VG.Proof.Blowfish
