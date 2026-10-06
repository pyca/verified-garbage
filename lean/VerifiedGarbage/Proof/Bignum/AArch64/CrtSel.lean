import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith

/-!
# Multiword arithmetic on AArch64: a masked selection

`selLoop`: `[x17] := mask ? [x16] : [x17]` over `w` words, each word
`T ^ ((E ^ T) & mask)` (`sel_mask`), with no address or branch depending on
the mask (`selLoop_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem sel_mask (c : Bool) (t e : BitVec 64) : t ^^^ ((e ^^^ t) &&& mask c) = if c then e else t := by
  cases c
  · simp [mask_false]
  · rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm t e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rfl

/-- After `j` words of `selLoop`. -/
structure SelLInv (s₀ : State) (B : Addr) (Z eA eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eo + 8 * j)
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j = if lt then wv s₀.mem B eA j else wv s₀.mem B eo j

/-- `selLoop`: `[x17] := mask ? [x16] : [x17]` over `w` words. -/
theorem selLoop_ok {s : State} {B : Addr} {Z w eA eo : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eo) (h14 : s.gpr .x14 = BitVec.ofNat 64 w)
    {lt : Bool} (h15 : s.gpr .x15 = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) :
    WP isa selLoop s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eo w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold selLoop
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (SelLInv s B Z eA eo lt) ?_
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by cases lt <;> rfl⟩ h14)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j hj t hI _
  have t15 : t.gpr .x15 = mask lt := (hI.keep.gpr .x15 (by decide)).trans h15
  have hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eo + 8 * j) = word s.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (word t.mem B (eo + 8 * j) ^^^ ((word t.mem B (eA + 8 * j) ^^^ word t.mem B (eo + 8 * j)) &&& mask lt)) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eo + 8 * j + 8)) (by
      brun [hI.x16, hI.x17, t15, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
        hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16', h17'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val, sel_mask, hx, hy]
    cases lt <;> simp [wv]

end VG.Proof.Bignum.AArch64
