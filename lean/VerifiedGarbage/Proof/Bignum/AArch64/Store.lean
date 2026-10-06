import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Multiword arithmetic on AArch64: words into big-endian bytes

`storeBE` writes the `w` words of an array, and'ed with a mask `x15` (all
ones or zero), as `k` bytes most significant first (`storeBE_ok`): after
`p` bytes, the bytes `k - 1, …, k - p` from the end hold bytes `0, …, p - 1`
of the masked number `Y_m`, and `x3` holds the rest of the word being
written (`SInv`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.WriteBytes (writeW8_apply)

/-- After `p` bytes of `storeBE` from `s`. -/
structure SInv (s : State) (out : Addr) (k : Nat) (Ym : Nat) (p : Nat) (t : State) : Prop where
  wr : t.wr = s.wr
  rd : t.rd = s.rd
  keep : Keep [.x1, .x2, .x3, .x5, .x6, .x9] s t
  x2 : t.gpr .x2 = BitVec.ofNat 64 p
  x1 : t.gpr .x1 = out + BitVec.ofNat 64 (k - p)
  x6 : t.gpr .x6 = 7#64
  x3 : p % 8 ≠ 0 → (t.gpr .x3).toNat = Ym / 256 ^ p % 256 ^ (8 - p % 8)
  bytes : ∀ j < p, t.mem (out + BitVec.ofNat 64 (k - 1 - j)) = BitVec.ofNat 8 (Ym / 256 ^ j)
  frame : ∀ x, (∀ j < p, x ≠ out + BitVec.ofNat 64 (k - 1 - j)) → t.mem x = s.mem x

theorem storeStep_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h15 : s.gpr .x15 = mask c) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    {p : Nat} (hp : p < k) {t : State}
    (hI : SInv s out k (if c then wv s.mem B ed w else 0) p t) :
    WP isa (.seq (.block [.logic .and .x .x5 .x2 .x6])
      (.seq (.ite (.zero .x .x5) (.block [.add .x .x5 .x8 .x2, ld .x3 .x5, .logic .and .x .x3 .x3 .x15]) (.block []))
        (.block [.subImm .x .x1 .x1 1, .strb .x3 .x1 0, .lsr .x .x3 .x3 8, .addImm .x .x2 .x2 1,
          .subImm .x .x9 .x9 1]))) t fun t' =>
      SInv s out k (if c then wv s.mem B ed w else 0) (p + 1) t' ∧ t'.gpr .x9 = t.gpr .x9 - BitVec.ofNat 64 1 := by
  have hn := hs.nowrap
  have t8 : t.gpr .x8 = off B ed := (hI.keep.gpr .x8 (by decide)).trans h8
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  refine WP.seq (WP.mono (WP.keep [.x5] (Q := fun t₁ => t₁.gpr .x5 = BitVec.ofNat 64 p &&& 7#64 ∧ t₁.mem = t.mem)
    (by brun [hI.x2, hI.x6]) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h5₁, hm₁⟩, k₁⟩ => ?_)
  have hz5 : (t₁.gpr .x5 == 0) = decide (p % 8 = 0) := by
    rw [eq_zero_iff, h5₁, and7_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
  -- After the optional load: `x3` holds bytes `p, …` of `Y_m` up to the word's end.
  have hload : WP isa (.ite (.zero .x .x5) (.block [.add .x .x5 .x8 .x2, ld .x3 .x5,
      .logic .and .x .x3 .x3 .x15]) (.block [])) t₁ fun t₂ =>
      (t₂.gpr .x3).toNat = (if c then wv s.mem B ed w else 0) / 256 ^ p % 256 ^ (8 - p % 8) ∧ t₂.mem = t.mem ∧
      Keep [.x3, .x5] t₁ t₂ := by
    by_cases hz : p % 8 = 0
    · refine WP.ite true (by rw [eval_zero, hz5, decide_eq_true hz]) (fun _ => ?_) (by simp)
      have t₁2 : t₁.gpr .x2 = BitVec.ofNat 64 p := (k₁.gpr .x2 (by decide)).trans hI.x2
      have t₁8 : t₁.gpr .x8 = off B ed := (k₁.gpr .x8 (by decide)).trans t8
      have t₁15 : t₁.gpr .x15 = mask c := (k₁.gpr .x15 (by decide)).trans t15
      have hq : p / 8 < w := by omega
      have hwd : word t₁.mem B (ed + 8 * (p / 8)) = word s.mem B (ed + 8 * (p / 8)) := by
        rw [hm₁]
        exact Mem.readW_congr fun i hi => (hI.frame _ fun j hj => by
          intro he
          have h1 := hsep (k - 1 - j) (by omega)
          rw [← he, ofs_off B (by omega)] at h1
          omega).symm |>.symm
      have hp8 : ed + p = ed + 8 * (p / 8) := by omega
      refine WP.mono (WP.keep [.x3, .x5] (Q := fun t₂ =>
          t₂.gpr .x3 = word s.mem B (ed + 8 * (p / 8)) &&& mask c ∧ t₂.mem = t₁.mem) (by
        brun [t₁2, t₁8, t₁15, off_add, hp8,
          (by rw [k₁.rd, k₁.wr, hI.rd, hI.wr]; exact hs.ld (show ed + 8 * (p / 8) + 8 ≤ Z by omega) :
            InRegions (t₁.rd ++ t₁.wr) (off B (ed + 8 * (p / 8))) 8)]
        exact congrArg (· &&& mask c) hwd) (by decide) (by decide) (by decide +kernel))
        fun t₂ ⟨⟨hax, hm₂⟩, k₂⟩ => ⟨?_, hm₂.trans hm₁, k₂⟩
      rw [hax, and_mask_toNat, word_of_wv _ _ _ _ hq, show 8 - p % 8 = 8 by omega, VG.Proof.Bignum.pow256_8,
        show 64 * (p / 8) = 8 * p by omega, show (256 : Nat) ^ p = 2 ^ (8 * p) by
          rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]]
      cases c <;> simp
    · refine WP.ite false (by rw [eval_zero, hz5, decide_eq_false hz]) (by simp) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [k₁.gpr .x3 (by decide)]; exact hI.x3 hz, hm₁, Keep.refl _ _⟩
  refine WP.seq (WP.mono hload fun t₂ ⟨hax₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have t₂1 : t₂.gpr .x1 = out + BitVec.ofNat 64 (k - p) := (k12.gpr .x1 (by decide)).trans hI.x1
  have t₂2 : t₂.gpr .x2 = BitVec.ofNat 64 p := (k12.gpr .x2 (by decide)).trans hI.x2
  have e1 : out + BitVec.ofNat 64 (k - p) - BitVec.ofNat 64 1 = out + BitVec.ofNat 64 (k - 1 - p) := by
    rw [Offset.add_ofNat_sub out (by omega), show k - p - 1 = k - 1 - p by omega]
  have hst : InRegions t₂.wr (out + BitVec.ofNat 64 (k - 1 - p)) 1 := by
    rw [k12.wr, hI.wr]; exact hout _ (by omega)
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x9] (Q := fun t' =>
      t'.mem = t₂.mem.write (out + BitVec.ofNat 64 (k - 1 - p)) 1 ((t₂.gpr .x3).setWidth 8) ∧
      t'.gpr .x3 = t₂.gpr .x3 >>> 8 ∧ t'.gpr .x2 = BitVec.ofNat 64 p + BitVec.ofNat 64 1 ∧
      t'.gpr .x1 = out + BitVec.ofNat 64 (k - 1 - p) ∧ t'.gpr .x9 = t₂.gpr .x9 - BitVec.ofNat 64 1) (by
    brun [t₂1, t₂2, e1, hst, off_zero]) (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨hm', hax', hdx', h1', h9'⟩, k'⟩ => ⟨?_, by rw [h9', k12.gpr .x9 (by decide)]⟩
  have hbyte : (t₂.gpr .x3).setWidth 8 = BitVec.ofNat 8 ((if c then wv s.mem B ed w else 0) / 256 ^ p) := by
    rw [← BitVec.ofNat_toNat, hax₂]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ ⟨256 ^ (8 - p % 8 - 1), by
      rw [Nat.mul_comm, ← Nat.pow_succ]; congr 1; omega⟩]
  have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
  refine ⟨k'.wr.trans (k12.wr.trans hI.wr), k'.rd.trans (k12.rd.trans hI.rd),
    ((hI.keep.trans k12).trans k').mono (by decide), by rw [hdx', ← BitVec.ofNat_add],
    by rw [h1']; congr 2; omega, by rw [k'.gpr .x6 (by decide), k12.gpr .x6 (by decide), hI.x6], ?_, ?_, ?_⟩
  · intro hz
    rw [hax', shr8_toNat, hax₂, show 8 - p % 8 = 1 + (8 - (p + 1) % 8) by omega, Nat.pow_add,
      Nat.pow_one, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · intro j hj
    rw [hm', hm₂, hw8, writeW8_apply]
    by_cases hjp : j = p
    · subst hjp; simp [hbyte]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes j (by omega)
  · intro x hx
    rw [hm', hm₂, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx p (by omega)))]
    exact hI.frame x fun j hj => hx j (by omega)

/-- `storeBE`: the number at `x8` (`w` words), masked by `x15 = mask c`, as
`k` bytes ending at `x1`, most significant first: I2OSP of it, or of 0. -/
theorem storeBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {out : Addr} {c : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B ed) (h1 : s.gpr .x1 = out + BitVec.ofNat 64 k)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 k) (h15 : s.gpr .x15 = mask c) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa storeBE s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B ed w else 0) k ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ Keep [.x1, .x2, .x3, .x5, .x6, .x9] s t := by
  unfold storeBE
  refine WP.seq (WP.mono (WP.keep [.x2, .x6] (Q := fun t => t.gpr .x2 = BitVec.ofNat 64 0 ∧
      t.gpr .x6 = 7#64 ∧ t.mem = s.mem) (by brun) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h2, h6, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := k) (by omega) (by omega)
    (SInv s out k (if c then wv s.mem B ed w else 0)) (fun p hp t hI _ =>
      storeStep_ok hs h8 h15 hk' hw hed hout hsep hp hI)
    ⟨k₁.wr, k₁.rd, k₁.mono (by decide), h2, by rw [k₁.gpr .x1 (by decide), h1, Nat.sub_zero], h6,
      fun h => absurd rfl h, fun j hj => absurd hj (by omega), fun x _ => by rw [hm₁]⟩
    (by rw [k₁.gpr .x9 (by decide), h9])) fun t hI => ⟨?_, ?_, hI.wr, hI.rd, hI.keep⟩
  · apply List.ext_getElem (by simp [Spec.Rsa.i2osp])
    intro i h1 h2
    have hik : i < k := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Spec.Rsa.i2osp]
    have := hI.bytes (k - 1 - i) (by omega)
    rwa [show k - 1 - (k - 1 - i) = i by omega] at this
  · intro x hx
    exact hI.frame x fun j hj => hx _ (by omega)

end VG.Proof.Bignum.AArch64
