module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group
import VerifiedGarbage.Proof.AesCbc.Decrypt
import VerifiedGarbage.Proof.Cmac.Spec

/-! # The indexed register invariant is CBC decryption -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem list_getD {α : Type} {xs : List α} {k : Nat} {d : α} (hk : k < xs.length) :
    xs.getD k d = xs[k] := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some]

theorem vector_listD (v : Spec.Aes.State) (i : Nat) (hi : i < 16) :
    v.toList.getD i 0 = v.getD i 0 := by
  rw [list_getD (by simpa using hi),Vector.getElem_toList]
  simp [Vector.getD,hi]

theorem chaining_bytes (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    (st (chaining s₀ k)).toList = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
  cases k with
  | zero => simp only [chaining,st_readW,List.take_zero]; exact (bytesAt_toList _ _).symm
  | succ k =>
    rw [next_take_succ _ _ k (by rw [length_blocksAt]; omega),
      list_getD (by rw [length_blocksAt]; omega),getElem_blocksAt (hk := by omega)]
    exact (congrArg Vector.toList (st_readW _ _)).trans (bytesAt_toList _ _).symm

theorem block_bytes (s₀ : State) (k : Nat) (hk : k < N s₀) :
    (output s₀ k).toList =
      (Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)).getD k [] := by
  rw [decrypt_getD _ _ _ k (by rw [length_blocksAt]; exact hk),
    list_getD (by rw [length_blocksAt]; exact hk),getElem_blocksAt (hk := hk),
    aesInvWith_state,← chaining_bytes _ _ (Nat.le_of_lt hk)]
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [vector_listD _ _ hi]
  rw [xor_eq,Proof.Cmac.getD_xor (by simp) (by simpa using hi)]
  rw [vector_listD _ _ hi,vector_listD _ _ hi]
  rw [getD_st _ hi]
  exact getD_ofFn hi

theorem data_done {s₀ : State} {m : Mem}
    (hI : EcbInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  have hs := statesAt_of_ecbInv hI
  have he : Spec.Cbc.blocksAt m (Dp s₀) (N s₀) =
      ((Spec.Aes.statesAt m (Dp s₀) (N s₀)).map Vector.toList) := by
    simp only [Spec.Cbc.blocksAt,Spec.Aes.statesAt,List.map_map,Function.comp_def]
    exact List.map_congr_left fun _ _ => bytesAt_toList _ _
  rw [he,hs,List.map_map]
  apply List.ext_getElem
  · simp [length_decrypt,length_blocksAt]
  · intro k hk _
    have hk' : k < N s₀ := by simpa using hk
    simp only [List.getElem_map,List.getElem_range,Function.comp_def]
    rw [block_bytes _ _ hk',list_getD (by simp [length_decrypt,length_blocksAt]; omega)]

end VG.Proof.AesCbc.AArch64.Decrypt
