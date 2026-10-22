module
public import VerifiedGarbage.Impl.Bignum.AArch64.WordIO
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.AArch64.WordIOBytes
import VerifiedGarbage.Proof.Bignum.AArch64.WordIOLoad
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Words into big-endian bytes, a word at a time, on AArch64

`storeWords` writes the `w` words of an array, and'ed with a mask `x15`, as
the `k = 8 w` bytes ending at `out + k`: after `j` words, the last `8 j`
bytes hold bytes `0, …, 8 j - 1` of the masked number (`SWInv`). `storeW`
takes it or `storeBE` by `k mod 8` (`storeW_ok`, with `storeBE_ok`'s
statement but for the bytes' one region).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WordIO

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.ByteDigits
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero)

theorem masked_digit (m : Mem) (B : Addr) (ed w : Nat) {j : Nat} (hj : j < w) (c : Bool) :
    word m B (ed + 8 * j) &&& mask c = BitVec.ofNat 64 ((if c then wv m B ed w else 0) / 256 ^ (8 * j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_toNat, word_of_wv _ _ _ _ hj, BitVec.toNat_ofNat, pow256]
  cases c <;> simp

/-- After `j` words of `storeWords` from `s`. -/
structure SWInv (s : State) (B out : Addr) (ed k Y : Nat) (j : Nat) (t : State) : Prop where
  wr : t.wr = s.wr
  rd : t.rd = s.rd
  keep : Keep [.x1, .x3, .x5, .x9] s t
  x1 : t.gpr .x1 = out + BitVec.ofNat 64 (k - 8 * j)
  x5 : t.gpr .x5 = off B (ed + 8 * j)
  x9 : t.gpr .x9 = BitVec.ofNat 64 (k - 8 * j)
  bytes : ∀ z < 8 * j, t.mem (out + BitVec.ofNat 64 (k - 1 - z)) = BitVec.ofNat 8 (Y / 256 ^ z)
  frame : ∀ x, (∀ z < 8 * j, x ≠ out + BitVec.ofNat 64 (k - 1 - z)) → t.mem x = s.mem x

theorem storeWordsStep_ok {s t : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (h15 : s.gpr .x15 = mask c) (hk : k = 8 * w) (hk' : k < 2 ^ 31) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i < k, Z ≤ ofs B (out + BitVec.ofNat 64 i))
    {j : Nat} (hj : j < w) (h : SWInv s B out ed k (if c then wv s.mem B ed w else 0) j t) :
    WP isa (.block [ld .x3 .x5, .logic .and .x .x3 .x3 .x15, .rev .x3 .x3, .subImm .x .x1 .x1 8, st .x3 .x1, next .x5,
        .subImm .x .x9 .x9 8]) t fun u =>
      SWInv s B out ed k (if c then wv s.mem B ed w else 0) (j + 1) u ∧ ((u.gpr .x9).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hn := hs.nowrap
  have hwd : word t.mem B (ed + 8 * j) = word s.mem B (ed + 8 * j) := by
    apply Mem.readW_congr
    intro b hb
    apply h.frame
    intro z hz he
    have hsep' := hsep (k - 1 - z) (by omega)
    rw [← he, ofs_off B (by omega)] at hsep'
    omega
  have hread : InRegions (t.rd ++ t.wr) (off B (ed + 8 * j)) 8 := by
    rw [h.rd, h.wr]; exact hs.ld (by omega)
  have hwrite : InRegions t.wr (out + BitVec.ofNat 64 (k - 8 * (j + 1))) 8 := by
    rw [h.wr]; exact VG.CallLay.inRegions_sub hout (by omega) (by omega)
  have hx1 : out + BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = out + BitVec.ofNat 64 (k - 8 * (j + 1)) := by
    rw [VG.Offset.add_ofNat_sub out (by omega)]; congr 2
  have hx5 : off B (ed + 8 * j) + BitVec.ofNat 64 8 = off B (ed + 8 * (j + 1)) := by
    rw [off_add, show ed + 8 * j + 8 = ed + 8 * (j + 1) by omega]
  have hx9 : BitVec.ofNat 64 (k - 8 * j) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (k - 8 * (j + 1)) := by
    rw [VG.Offset.ofNat_sub_ofNat (by omega)]; congr 1
  have h15' : t.gpr .x15 = mask c := (h.keep.gpr .x15 (by decide)).trans h15
  refine WP.mono (WP.keep [.x1, .x3, .x5, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 (k - 8 * (j + 1)))
      (rev64 (BitVec.ofNat 64 ((if c then wv s.mem B ed w else 0) / 256 ^ (8 * j)))) ∧
    u.gpr .x1 = out + BitVec.ofNat 64 (k - 8 * (j + 1)) ∧ u.gpr .x5 = off B (ed + 8 * (j + 1)) ∧
    u.gpr .x9 = BitVec.ofNat 64 (k - 8 * (j + 1))) ?_ (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨hm, h1, h5, h9⟩, ku⟩ => ?_
  · brun [h.x1, h.x5, h.x9, hread, exec_rev, h15', hwd, masked_digit _ _ _ _ hj c, hx1, hx5, hx9, hwrite]
  · refine ⟨⟨ku.wr.trans h.wr, ku.rd.trans h.rd, (h.keep.trans ku).mono (by decide), h1, h5, h9, fun z hz => ?_,
      fun x hx => ?_⟩, ?_⟩
    · rw [hm]
      have hd : ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat =
          k - 1 - z - (k - 8 * (j + 1)) := VG.Offset.sub_toNat out (by omega) (by omega)
      change (if ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat < 8 then
        (rev64 (BitVec.ofNat 64 ((if c then wv s.mem B ed w else 0) / 256 ^ (8 * j)))).extractLsb'
          (8 * ((out + BitVec.ofNat 64 (k - 1 - z)) - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat) 8
        else t.mem (out + BitVec.ofNat 64 (k - 1 - z))) = _
      rw [hd]
      by_cases hzold : z < 8 * j
      · rw [ite_eq_right (by omega)]; exact h.bytes z hzold
      · rw [ite_eq_left (by omega), rev64_byte _ (by omega), extract_nat _ (by omega), Nat.div_div_eq_div_mul,
          ← Nat.pow_add]
        congr 3; omega
    · rw [hm]
      apply Eq.trans (Mem.write_apply ?_) (h.frame x (fun z hz => hx z (by omega)))
      intro hin
      let b := (x - (out + BitVec.ofNat 64 (k - 8 * (j + 1)))).toNat
      have hb : b < 8 := hin
      have he : x = out + BitVec.ofNat 64 (k - 8 * (j + 1) + b) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        change x = (out + BitVec.ofNat 64 (k - 8 * (j + 1))) + BitVec.ofNat 64 b
        simp only [b, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_comm (out + BitVec.ofNat 64 (k - 8 * (j + 1))) _, BitVec.sub_add_cancel]
      apply hx (8 * (j + 1) - 1 - b) (by omega)
      rw [he]
      congr 2; omega
    · rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega

theorem storeWords_ok {s : State} {B out : Addr} {Z ed k w : Nat} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h1 : s.gpr .x1 = out + BitVec.ofNat 64 k)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 k) (h15 : s.gpr .x15 = mask c)
    (hk : k = 8 * w) (hk1 : 0 < k) (hk' : k < 2 ^ 31) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k) (hsep : ∀ i < k, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa storeWords s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.x1, .x3, .x5, .x9] s t := by
  unfold storeWords
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off B ed ∧ t.mem = s.mem)
    (by brun [h8]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h5, hm⟩, ka⟩ => ?_)
  have hs' := hs.congr ka.wr
  have hm' : wv a.mem B ed w = wv s.mem B ed w := by rw [hm]
  have h0 : SWInv a B out ed k (if c then wv s.mem B ed w else 0) 0 a :=
    ⟨rfl, rfl, Keep.refl _ _, by rw [(ka.gpr .x1 (by decide)).trans h1, Nat.mul_zero, Nat.sub_zero],
      by rw [h5, Nat.mul_zero, Nat.add_zero], by rw [(ka.gpr .x9 (by decide)).trans h9, Nat.mul_zero, Nat.sub_zero],
      fun z hz => absurd hz (by omega), fun _ _ => rfl⟩
  have hr : InRegions a.wr out k := by rw [ka.wr]; exact hout
  refine WP.mono (count_loop (cr := .x9) (n := w) (by omega)
    (SWInv a B out ed k (if c then wv s.mem B ed w else 0))
    (fun j hj t h => by
      rw [← hm'] at h ⊢
      exact storeWordsStep_ok hs' ((ka.gpr .x15 (by decide)).trans h15) hk hk' hed hr hsep hj h) h0)
    fun t h => ⟨?_, ?_, h.wr.trans ka.wr, h.rd.trans ka.rd, (ka.trans h.keep).mono (by decide)⟩
  · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
    intro i hi _
    have hik : i < k := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, Spec.Rsa.i2osp]
    have hb := h.bytes (k - 1 - i) (by omega)
    rwa [show k - 1 - (k - 1 - i) = i by omega] at hb
  · intro x hx
    rw [h.frame x (fun i hi => hx _ (by omega)), hm]

/-- `storeW`: `storeBE` (`storeBE_ok`), for bytes in one region. -/
theorem storeW_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h1 : s.gpr .x1 = out + BitVec.ofNat 64 k)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 k) (h15 : s.gpr .x15 = mask c) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : InRegions s.wr out k)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa storeW s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.x1, .x2, .x3, .x5, .x6, .x9] s t := by
  unfold storeW
  refine WP.seq (WP.mono (WP.keep [.x2, .x6] (Q := fun a => a.gpr .x2 = BitVec.ofNat 64 k &&& (BitVec.ofNat 16 7).setWidth 64 ∧
      a.mem = s.mem) (by brun [h9]) (by decide) (by decide) (by decide +kernel)) fun a ⟨⟨h2, hm⟩, ka⟩ => ?_)
  have hs' := hs.congr ka.wr
  have hr : InRegions a.wr out k := by rw [ka.wr]; exact hout
  have a1 := (ka.gpr .x1 (by decide)).trans h1
  have a8 := (ka.gpr .x8 (by decide)).trans h8
  have a9 := (ka.gpr .x9 (by decide)).trans h9
  have a15 := (ka.gpr .x15 (by decide)).trans h15
  refine WP.ite (decide (k % 8 = 0)) (by rw [eval_zero, h2, and7_zero (by omega)]) ?_ ?_
  · intro h8'
    have h8' := of_decide_eq_true h8'
    refine WP.mono (storeWords_ok hs' a8 a1 a9 a15 (w := w) (by omega) (by omega) hk' hed hr hsep)
      fun t ⟨hv, ho, hw', hr', kt⟩ => ⟨by simpa only [hm] using hv, fun x hx => (ho x hx).trans (congrFun hm x),
        hw'.trans ka.wr, hr'.trans ka.rd, (ka.trans kt).mono (by decide)⟩
  · intro _
    refine WP.mono (storeBE_ok hs' a8 a1 a9 a15 hk1 hk' hw hed
      (fun i hi => VG.CallLay.inRegions_sub hr (by omega) (by omega)) hsep)
      fun t ⟨hv, ho, hw', hr', kt⟩ => ⟨by simpa only [hm] using hv, fun x hx => (ho x hx).trans (congrFun hm x),
        hw'.trans ka.wr, hr'.trans ka.rd, (ka.trans kt).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WordIO
