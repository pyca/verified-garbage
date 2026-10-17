module

public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Proof.Modes.Steps

/-!
# CAST5's cipher for the modes, on any target

The cipher of each direction (`dirCipher`: `Spec.Cast5.cipher` or
`invCipher`), the 8 bytes at `p` as the block there (`bytesAt_eq`,
`ofFn_bytesAt`), and CAST5-CBC's blocks as the modes' (`cbcBlocksAt_eq`).
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG

/-- Encryption (`up`) or decryption under the subkeys `k` with `n` rounds. -/
def dirCipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cbc.Cipher :=
  if up then Spec.Cast5.cipher k n else Spec.Cast5.invCipher k n

theorem dirCipher_length (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : List Byte) :
    (dirCipher up k n b).length = 8 := by
  cases up <;> simp [dirCipher, Spec.Cast5.cipher, Spec.Cast5.invCipher]

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 8 = (Spec.Cast5.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, Spec.Cast5.blockAt]

theorem ofFn_bytesAt (m : Mem) (p : Addr) :
    (Vector.ofFn fun i : Fin 8 => (Spec.Aes.bytesAt m p 8).getD i.val 0) = Spec.Cast5.blockAt m p := by
  ext i hi; simp [Spec.Aes.bytesAt, Spec.Cast5.blockAt]

theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Cast5.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.Cast5.cbcBlocksAt, Spec.Cast5.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

end VG.Proof.Cast5
