module

public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Read preserved words from the shared round's contract -/

@[expose] public section

namespace VG.Proof.MillerRabin

open VG VG.Proof.Bignum

theorem keeps_word {L : Proof.MillerRabin.Round.Workspace} {B : Addr} {n w d : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps L B n w m m') (hd : d + 8 ≤ 8 * n)
    (hh : ∀ k ∈ [L.flag, L.value, L.words, L.windows, L.digit], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d)
    (ha : ∀ j ∈ [2, 3, 5, 6, L.base],
      d + 8 ≤ Proof.Rsa.Mont.arrAt w j ∨ Proof.Rsa.Mont.arrAt w j + 8 * (w + 2) ≤ d)
    (ht : d + 8 ≤ Proof.Rsa.Mont.arrAt w L.table ∨ Proof.Rsa.Mont.arrAt w (L.table + 16) ≤ d) :
    word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  rw [off, Offset.add_ofNat_add_ofNat]
  apply h (d + i) (by omega_arith)
  · intro k hk
    have := hh k hk
    omega_arith
  · intro j hj
    have := ha j hj
    omega_arith
  · omega_arith

theorem keeps_wv {L : Proof.MillerRabin.Round.Workspace} {B : Addr} {n w d k : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps L B n w m m') (hd : d + 8 * k ≤ 8 * n)
    (hh : ∀ j ∈ [L.flag, L.value, L.words, L.windows, L.digit], d + 8 * k ≤ 8 * j ∨ 8 * j + 8 ≤ d)
    (ha : ∀ j ∈ [2, 3, 5, 6, L.base],
      d + 8 * k ≤ Proof.Rsa.Mont.arrAt w j ∨ Proof.Rsa.Mont.arrAt w j + 8 * (w + 2) ≤ d)
    (ht : d + 8 * k ≤ Proof.Rsa.Mont.arrAt w L.table ∨ Proof.Rsa.Mont.arrAt w (L.table + 16) ≤ d) :
    wv m' B d k = wv m B d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wv, wv, ih (by omega_arith) (fun j hj => by have := hh j hj; omega_arith)
      (fun j hj => by have := ha j hj; omega_arith) (by omega_arith)]
    rw [keeps_word h (by omega_arith)
      (fun j hj => by have := hh j hj; omega_arith)
      (fun j hj => by have := ha j hj; omega_arith) (by omega_arith)]

def mutRanges (L : Proof.MillerRabin.Round.Workspace) (w : Nat) : List (Nat × Nat) :=
  [L.flag, L.value, L.words, L.windows, L.digit].map (fun k => (8 * k, 8)) ++
    ([2, 3, 5, 6, L.base].map (fun j => (Proof.Rsa.Mont.arrAt w j, 8 * (w + 2))) ++
      [(Proof.Rsa.Mont.arrAt w L.table, 16 * (8 * (w + 2)))])

theorem keeps_to_frm {L : Proof.MillerRabin.Round.Workspace} {B : Addr} {n w : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps L B n w m m') (hf : Frame [⟨B, 8 * n⟩] m m') :
    Frm B (mutRanges L w) m m' := by
  intro x hx
  by_cases hd : ofs B x < 8 * n
  · have haddr : B + BitVec.ofNat 64 (ofs B x) = x := by
      simp only [ofs]
      bv_omega
    rw [← haddr]
    apply h (ofs B x) hd
    · intro k hk
      exact hx (8 * k, 8) (List.mem_append_left _ (List.mem_map_of_mem hk))
    · intro j hj
      exact hx (Proof.Rsa.Mont.arrAt w j, 8 * (w + 2))
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hj)))
    · have ht := hx (Proof.Rsa.Mont.arrAt w L.table, 16 * (8 * (w + 2)))
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
      simpa only [Proof.Rsa.Mont.arrAt, Nat.add_mul, Nat.add_assoc] using ht
  · apply hf x
    intro r hr hc
    simp only [List.mem_singleton] at hr
    subst r
    change (x - B).toNat + 1 ≤ 8 * n at hc
    simp only [ofs] at hd
    omega_arith

theorem keeps_to_work {L : Proof.MillerRabin.Round.Workspace} {B : Addr} {n w : Nat}
    {extra : List Region} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps L B n w m m')
    (hf : Frame ([⟨B, 8 * n⟩] ++ extra) m m') :
    WorkFrame B (mutRanges L w) extra m m' := by
  intro x he hx
  by_cases hd : ofs B x < 8 * n
  · have haddr : B + BitVec.ofNat 64 (ofs B x) = x := by
      simp only [ofs]
      bv_omega
    rw [← haddr]
    apply h (ofs B x) hd
    · intro k hk
      exact hx (8 * k, 8) (List.mem_append_left _ (List.mem_map_of_mem hk))
    · intro j hj
      exact hx (Proof.Rsa.Mont.arrAt w j, 8 * (w + 2))
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hj)))
    · have ht := hx (Proof.Rsa.Mont.arrAt w L.table, 16 * (8 * (w + 2)))
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
      simpa only [Proof.Rsa.Mont.arrAt, Nat.add_mul, Nat.add_assoc] using ht
  · apply hf x
    intro r hr hc
    rcases List.mem_append.mp hr with hw | ha
    · simp only [List.mem_singleton] at hw
      subst r
      change (x - B).toNat + 1 ≤ 8 * n at hc
      simp only [ofs] at hd
      omega_arith
    · exact he r ha hc

theorem keeps_write_flag {L : Proof.MillerRabin.Round.Workspace} {B : Addr} {n w : Nat} {m m' : Mem}
    (h : Proof.MillerRabin.Round.Keeps L B n w m m') (hn : 8 * n ≤ 2 ^ 64)
    (hl : 8 * L.flag + 8 ≤ 2 ^ 64) (v : BitVec 64) :
    Proof.MillerRabin.Round.Keeps L B n w m (m'.writeW (off B (8 * L.flag)) v) := by
  intro i hi hh ha ht
  have hx : ofs B (B + BitVec.ofNat 64 i) < 8 * L.flag ∨
      8 * L.flag + 8 ≤ ofs B (B + BitVec.ofNat 64 i) := by
    simpa only [ofs, Mem.sub_ofNat_toNat B (by omega_arith : i < 2 ^ 64)] using
      hh L.flag (List.mem_cons_self ..)
  exact (writeW_outside m' B v hl _ hx).trans (h i hi hh ha ht)

end VG.Proof.MillerRabin
