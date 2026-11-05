module
public import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Rc2.Contract

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # CBC over lists of blocks: concatenation, and decryption block by block -/

@[expose] public section

namespace VG.Proof.Rc2

open VG

theorem cbc_append (k : Spec.Rc2.Schedule) (d : Spec.Rc2.Direction) (iv : Spec.Rc2.Block)
    (A B : List Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k d iv (A ++ B) =
      ((Proof.Rc2.cbcBlocks k d iv A).1 ++ (Proof.Rc2.cbcBlocks k d (Proof.Rc2.cbcBlocks k d iv A).2 B).1,
        (Proof.Rc2.cbcBlocks k d (Proof.Rc2.cbcBlocks k d iv A).2 B).2) := by
  induction A generalizing iv with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, Proof.Rc2.cbcBlocks, ih]

/-- Decryption: each block decrypted and XORed with the ciphertext block before it. -/
theorem cbc_decrypt (k : Spec.Rc2.Schedule) (iv : Spec.Rc2.Block) (cs : List Spec.Rc2.Block) :
    Proof.Rc2.cbcBlocks k .decrypt iv cs =
      (List.zipWith (fun c p => Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock k c) p) cs (iv :: cs),
        (iv :: cs).getLast (List.cons_ne_nil _ _)) := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih =>
    simp only [Proof.Rc2.cbcBlocks, Proof.Rc2.cbcStep, ih, List.zipWith_cons_cons, List.getLast_cons_cons]

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rc2.blocksAt m p (a + b) =
      Spec.Rc2.blocksAt m p a ++ Spec.Rc2.blocksAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  simp only [Spec.Rc2.blocksAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add, Nat.mul_add]

theorem blocksAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.blocksAt m p n).length = n := by
  simp [Spec.Rc2.blocksAt]

theorem blocksAt_getElem (m : Mem) (p : Addr) {n i : Nat} (hi : i < (Spec.Rc2.blocksAt m p n).length) :
    (Spec.Rc2.blocksAt m p n)[i] = Spec.Rc2.blockAt m (p + BitVec.ofNat 64 (8 * i)) := by
  simp [Spec.Rc2.blocksAt]

end VG.Proof.Rc2
