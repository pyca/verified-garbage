import VerifiedGarbage.Spec.Rsa

/-!
# OS2IP and I2OSP are inverse

For the octet strings of a fixed length `k` and the integers below
`256^k`: `i2osp_os2ip` and `os2ip_i2osp`, so `i2osp x k = em` exactly when
`x = os2ip em` (`i2osp_eq_iff`). And `powMod` is below its modulus.
-/

namespace VG.Proof.RsaPkcs1Sig

open Spec.Rsa

/-- Induction on octet strings from their last octet. -/
theorem snoc_induction {P : List Byte → Prop} (nil : P [])
    (snoc : ∀ bs b, P bs → P (bs ++ [b])) (bs : List Byte) : P bs := by
  have h : ∀ l : List Byte, P l.reverse := by
    intro l
    induction l with
    | nil => exact nil
    | cons b l ih => rw [List.reverse_cons]; exact snoc _ _ ih
  simpa using h bs.reverse

theorem os2ip_append_singleton (bs : List Byte) (b : Byte) :
    os2ip (bs ++ [b]) = 256 * os2ip bs + b.toNat := by
  simp [os2ip, List.foldl_append]

theorem i2osp_length (x k : Nat) : (i2osp x k).length = k := by simp [i2osp]

theorem i2osp_succ (x k : Nat) : i2osp x (k + 1) = i2osp (x / 256) k ++ [BitVec.ofNat 8 x] := by
  unfold i2osp
  rw [List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi : i < k := List.mem_range.1 hi
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    congr 3
    omega
  · simp

theorem os2ip_lt (bs : List Byte) : os2ip bs < 256 ^ bs.length := by
  induction bs using snoc_induction with
  | nil => decide
  | snoc bs b ih =>
    rw [os2ip_append_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    have := b.isLt
    omega

theorem i2osp_os2ip (bs : List Byte) : i2osp (os2ip bs) bs.length = bs := by
  induction bs using snoc_induction with
  | nil => rfl
  | snoc bs b ih =>
    have hb := b.isLt
    rw [List.length_append, List.length_singleton, i2osp_succ, os2ip_append_singleton,
      show (256 * os2ip bs + b.toNat) / 256 = os2ip bs by omega, ih]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

theorem os2ip_i2osp (x k : Nat) (hx : x < 256 ^ k) : os2ip (i2osp x k) = x := by
  induction k generalizing x with
  | zero => simp [i2osp, os2ip]; omega
  | succ k ih =>
    rw [i2osp_succ, os2ip_append_singleton, ih (x / 256) (by rw [Nat.pow_succ] at hx; omega),
      BitVec.toNat_ofNat]
    omega

theorem i2osp_eq_iff {x k : Nat} {em : List Byte} (hx : x < 256 ^ k) (hem : em.length = k) :
    i2osp x k = em ↔ x = os2ip em := by
  constructor
  · rintro rfl; exact (os2ip_i2osp x k hx).symm
  · rintro rfl; rw [← hem]; exact i2osp_os2ip em

theorem powMod_lt (a e m : Nat) (hm : 0 < m) : powMod a e m < m := by
  unfold powMod
  split
  · exact Nat.mod_lt _ hm
  · dsimp only
    split <;> exact Nat.mod_lt _ hm

end VG.Proof.RsaPkcs1Sig
