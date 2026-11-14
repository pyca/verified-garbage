module

public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.CbcMemory
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Streaming RC2-CBC: the contracts from memory facts

Target-independent lemmas that reduce the postcondition of `vg_rc2_cbc_init`
(`Spec.Rc2.cbcInitContract`) to facts about the memory an implementation
leaves, for implementations that check the lengths in order, and on success
copy the IV to `ctx + 128` and expand the key into `ctx` (`init_post`,
`init_post_error`).
-/

@[expose] public section

namespace VG.Proof.Rc2

open VG

theorem getD_of_lt {α : Type} (l : List α) {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rc2.bytesAt m p (a + b) = Spec.Rc2.bytesAt m p a ++ Spec.Rc2.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rc2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Rc2.bytesAt m p (i + 1) = Spec.Rc2.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Rc2.bytesAt, List.range_succ]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hn : n ≤ 2 ^ 64) (hd : ∀ r ∈ rs, (Region.mk p n).Disjoint r) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  simp only [Spec.Rc2.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hn (List.mem_range.mp hi)

/-- Bytes written with `writeBytes` read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, WriteBytes.writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [h, h₂]), h₂, ite_true]
    rw [getD_of_lt _ _ h₂]

theorem bytesAt_eight (m : Mem) (p : Addr) :
    Spec.Rc2.bytesAt m p 8 = (Spec.Rc2.blockAt m p).toList := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, Spec.Rc2.blockAt, List.getElem_map, List.getElem_range,
      Vector.getElem_toList, Vector.getElem_ofFn]

/-! ## `cbcBlocks` is CBC

`Spec.Cbc.encrypt` and `Spec.Cbc.decrypt` work on blocks as lists of bytes;
the internal functions' contracts, with `cbcBlocks` on vectors. -/

theorem ofFn_getD_toList (b : Spec.Rc2.Block) : (Vector.ofFn fun i => b.toList.getD i.val 0) = b := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rw [getD_of_lt _ _ (by simpa using hi), Vector.getElem_toList]

theorem xor_toList (a b : Spec.Rc2.Block) : Spec.Cbc.xor a.toList b.toList = (xorBlock a b).toList := by
  apply List.ext_getElem
  · simp [Spec.Cbc.xor]
  · intro i h₁ h₂
    simp only [Spec.Cbc.xor, List.getElem_zipWith, Vector.getElem_toList, xorBlock, Vector.getElem_ofFn]
    rfl

theorem cbc_encrypt_eq (k : Spec.Rc2.Schedule) (iv : Spec.Rc2.Block) (bs : List Spec.Rc2.Block) :
    (cbcBlocks k .encrypt iv bs).1.map Vector.toList =
      Spec.Cbc.encrypt (Spec.Rc2.cipher k) iv.toList (bs.map Vector.toList) ∧
    (cbcBlocks k .encrypt iv bs).2 = (cbcBlocks k .encrypt iv bs).1.getLastD iv := by
  induction bs generalizing iv with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨h₁, h₂⟩ := ih (Spec.Rc2.encryptBlock k (xorBlock b iv))
    simp only [cbcBlocks, cbcStep, List.map_cons, Spec.Cbc.encrypt, Spec.Rc2.cipher, xor_toList,
      ofFn_getD_toList, h₁, h₂, true_and]
    cases h : (cbcBlocks k .encrypt (Spec.Rc2.encryptBlock k (xorBlock b iv)) bs).1 <;> rfl

theorem cbc_decrypt_eq (k : Spec.Rc2.Schedule) (iv : Spec.Rc2.Block) (bs : List Spec.Rc2.Block) :
    (cbcBlocks k .decrypt iv bs).1.map Vector.toList =
      Spec.Cbc.decrypt (Spec.Rc2.invCipher k) iv.toList (bs.map Vector.toList) ∧
    (cbcBlocks k .decrypt iv bs).2 = bs.getLastD iv := by
  induction bs generalizing iv with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    obtain ⟨h₁, h₂⟩ := ih b
    simp only [cbcBlocks, cbcStep, List.map_cons, Spec.Cbc.decrypt, Spec.Rc2.invCipher, xor_toList,
      ofFn_getD_toList, h₁, h₂, true_and]
    cases bs <;> rfl

/-! ## `init` -/

/-- The context `init` writes, from the schedule at `ctx` and the IV at
`ctx + 128`. -/
theorem init_post {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hk : 1 ≤ keyLen ∧ keyLen ≤ 128) (he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) (hi : ivLen = 8)
    (hr : r = 0)
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen) effectiveBits)
    (hiv : Spec.Rc2.blockAt m' (ctx + 128) = Spec.Rc2.blockAt m iv) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  subst hi
  have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv 8)
      direction effectiveBits = .ok (Spec.Rc2.Context.mk (Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen)
        effectiveBits) direction (Vector.ofFn fun i => (Spec.Rc2.bytesAt m iv 8).getD i 0) []) := by
    simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk),
      ite_eq_left_of_eq_true _ _ (eq_true he)]
    rfl
  rw [hc]
  refine ⟨hr, ?_⟩
  simp only [Spec.Rc2.contextAt, hs, hiv, Spec.Rc2.Context.mk.injEq, true_and]
  refine ⟨?_, by simp [Spec.Rc2.bytesAt]⟩
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, Vector.getElem_ofFn, Spec.Rc2.bytesAt]
  rw [getD_of_lt _ _ (by simp; omega_using [hi]), List.getElem_map, List.getElem_range]

/-- The error `init` returns for invalid lengths, in order. -/
theorem init_post_error {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hr : r.toNat = if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
      else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else 3)
    (hbad : ¬((1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) ∧ ivLen = 8)) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  by_cases hk : 1 ≤ keyLen ∧ keyLen ≤ 128
  · by_cases he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024
    · have hi : ivLen ≠ 8 := fun h => hbad ⟨hk, he, h⟩
      have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidIvLength := by
        simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true he), ite_eq_right_of_eq_false _ _ (eq_false hi)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
    · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidEffectiveBits := by
        simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_right_of_eq_false _ _ (eq_false he)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
  · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
        direction effectiveBits = .error .invalidKeyLength := by
      simp only [Spec.Rc2.initWithEffectiveBits, bytesAt_length, ite_eq_right_of_eq_false _ _ (eq_false hk)]
      rfl
    rw [hc]; simpa [hk, Spec.Rc2.Error.code] using hr

end VG.Proof.Rc2
