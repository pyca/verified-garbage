module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Divstep.MredWords
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Divstep.RowWord
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the batched inverse's Montgomery word

`mredP a m o`: `[o] := mredRaw ([a])` for the signed `[a]` of `n + 1`
words (`mredP_ok`): `[a]` sign-extended by a word (`mredMid_ok`, which also
takes the digit `k = a₀ (-m⁻¹)`), `k m` added modulo `2^(64 (n + 2))`
(`mulAddRowMod_ok`: `mulAddRow` when the sum may wrap), and its words above
the lowest copied down (`copyLoop_ok`; `[o]` may be `[a]`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- Two words plus a carry and its carry, modulo `2^128`. -/
theorem addc2_mod (X Y c : BitVec 64) :
    (X + c).toNat + 2 ^ 64 * (Y + BitVec.ofNat 64 (decide (2 ^ 64 ≤ X.toNat + c.toNat)).toNat).toNat =
      (X.toNat + c.toNat + 2 ^ 64 * Y.toNat) % 2 ^ 128 := by
  have hX := X.isLt; have hY := Y.isLt; have hc := c.isLt
  by_cases h : 2 ^ 64 ≤ X.toNat + c.toNat <;>
  simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, BitVec.toNat_add,
    BitVec.toNat_ofNat] <;> omega

/-- `(a + P b) mod P Q`, for `a < P`. -/
theorem add_mul_mod_mul {a b P Q : Nat} (ha : a < P) : (a + P * b) % (P * Q) = a + P * (b % Q) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt ha, Nat.zero_add]

/-- The value after `rowTop`, modulo `2^(64 (w + 2))`. -/
theorem rowTop_valMod (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64) :
    wv ((m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)).writeW
        (off B (eA + 8 * w + 8)) (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
          (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat))
        B eA (w + 2) =
      (wv m B eA w + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat)) % 2 ^ (64 * (w + 2)) := by
  have o1 := writeW_outside m B (word m B (eA + 8 * w) + c) (d := eA + 8 * w) (by omega)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)) B
    (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat)
    (d := eA + 8 * w + 8) (by omega)
  have hc := addc2_mod (word m B (eA + 8 * w)) (word m B (eA + 8 * w + 8)) c
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega,
    word_writeW_self, o2.word (Or.inl (Nat.le_refl _)) (by omega), word_writeW_self,
    o2.wv (Or.inl (by omega)) (by omega), o1.wv (Or.inl (Nat.le_refl _)) (by omega), pow64_succ,
    show 2 ^ (64 * (w + 1 + 1)) = 2 ^ (64 * w) * 2 ^ 128 by rw [← Nat.pow_add]; congr 1,
    add_mul_mod_mul (wv_lt m B eA w), ← hc]
  grind

/-- `acc += x1 · B` modulo `2^(64 (w + 2))` (`mulAddRow`). -/
theorem mulAddRowMod_ok {s : State} {B : Addr} {Z w eA eb : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eb) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) :
    WP isa mulAddRow s fun t =>
      wv t.mem B eA (w + 2) = (wv s.mem B eA (w + 2) + (s.gpr .x1).toNat * wv s.mem B eb w) % 2 ^ (64 * (w + 2)) ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold mulAddRow
  refine WP.seq (WP.mono (WP.keep [.x2, .x14, .x16, .x17] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x17 = off B eb ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [h8, h9, h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, h2, hcf, hm₁⟩, k₁⟩ => ?_)
  have s₁7 : s₁.gpr .x7 = 0 := (k₁.gpr .x7 (by decide)).trans h7
  have s₁1 : s₁.gpr .x1 = s.gpr .x1 := k₁.gpr .x1 (by decide)
  have h0 : RowInv s₁ B Z eA eb 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _,
      by simp only [carry, h2, hcf, Bool.toNat_false]; rfl,
      by simp only [carry, h2, hcf, Bool.toNat_false]; decide⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (RowInv s₁ B Z eA eb)
    (fun j hj t hI _ => rowStep_ok s₁7 (by omega) hb (by omega) hj hI) h0 h14) fun u hI => ?_)
  have u7 : u.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans s₁7
  refine WP.seq (WP.mono (carryOut_ok u u7 hI.carry_lt) fun t ⟨⟨hm, hcarry⟩, kc⟩ => ?_)
  have t7 : t.gpr .x7 = 0 := (kc.gpr .x7 (by decide)).trans u7
  refine WP.mono (rowTop_ok (hI.scr.congr kc.wr)
    ((kc.gpr .x16 (by decide)).trans hI.x16) t7 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hm, hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hm, hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁, s₁1, ← hcarry, ← hm] at hval
  have e2 := wv_top2 s.mem B eA w
  refine ⟨?_, ?_, (((k₁.trans hI.keep).trans kc).trans k').mono (by decide)⟩
  · have hc := hI.carry_lt
    rw [hm', rowTop_valMod t.mem B hn (show eA + 8 * w + 16 ≤ Z by omega) _, hX, hY, e2]
    congr 1
    grind
  · rw [hm']
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega)]
    rw [hm]
    exact (hI.out x (by omega)).trans (by rw [hm₁])
end VG.Proof.Bignum.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The middle of `mredP`'s head: the digit `k = a₀ x5` into `x1`, and word
`n + 1` of `[x8]` the sign mask of its word `n`. -/
theorem mredMid_ok (s : State) {B : Addr} {Z eA n : Nat} (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n < 2 ^ 24) (hA : eA + 8 * (n + 2) ≤ Z) :
    WP isa (.block ([ld .x3 .x8, .mul .x .x1 .x3 .x5, .lsl .x .x6 .x12 3, .add .x .x6 .x8 .x6, ld .x3 .x6,
      .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x3 .x7 .x3, st .x3 .x6 8] : List Instr)) s fun t =>
      (t.gpr .x1 = word s.mem B eA * s.gpr .x5 ∧ t.gpr .x7 = 0 ∧
        t.mem = s.mem.writeW (off B (eA + 8 * n + 8)) (0#64 - (word s.mem B (eA + 8 * n) >>> 63))) ∧
      Keep [.x1, .x3, .x6, .x7] s t := by
  have hn' := hs.nowrap
  refine WP.keep [.x1, .x3, .x6, .x7] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h8, h12, shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega), hs.ld (show eA + 8 ≤ Z by omega),
    show off B eA + BitVec.ofNat 64 (n * 2 ^ 3) = off B (eA + 8 * n) by rw [off_add]; congr 2; omega,
    hs.ld (show eA + 8 * n + 8 ≤ Z by omega), hs.st (show eA + 8 * n + 8 + 8 ≤ Z by omega),
    show BitVec.setWidth 64 0#16 = 0#64 from rfl]

/-- After `j` words of `copyBody`. -/
structure CopyInv (s₀ : State) (B : Addr) (Z eS eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eS + 8 * j)
  x17 : t.gpr .x17 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : wv t.mem B eO j = wv s₀.mem B eS j

/-- `L` words of `[x16]` to `[x17]`, ascending: `[x16]` may be `[x17]` plus
some words. -/
theorem copyLoop_ok {s : State} {B : Addr} {Z L eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (h14 : s.gpr .x14 = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 32) (hS : eS + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sep : eO ≤ eS ∨ eS + 8 * L ≤ eO) :
    WP isa (countLoop .x14 copyBody) s (CopyInv s B Z eS eO L) := by
  have hn := hs.nowrap
  have h0 : CopyInv s B Z eS eO 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, rfl⟩
  refine wp_countdown (N := L) (by omega) (by omega) (CopyInv s B Z eS eO) (fun j hj t hI _ => ?_) h0 h14
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eO + 8 * j)) (word t.mem B (eS + 8 * j)) ∧
      t₁.gpr .x16 = off B (eS + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eO + 8 * j + 8))
    (by unfold copyBody; brun [hI.x16, hI.x17, hI.scr.ld (show eS + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eO + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16', h17'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) (word t.mem B (eS + 8 * j)) := hm'.trans hm
  have hx : word t.mem B (eS + 8 * j) = word s.mem B (eS + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), hI.val, hx]
    rfl
/-- `mredP a m o`: `[o] := mredRaw [a]` modulo `2^(64 (n + 1))`, `-m⁻¹` from lane 1 of `v18`. -/
theorem mredP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iO : Nat}
    (hA : iA < 16) (hM : iM < 16) (hO : iO < 16) (dAM : iA ≠ iM) (dOM : iO ≠ iM)
    (hm : ((wv s.mem B (slot w iM) n : Int) * ((s.v .v18).extractLsb' 64 64).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (seqs (mredP iA iM iO)) s fun t =>
      (wv t.mem B (slot w iO) (n + 1) : Int) = Divstep.mredRaw (wv s.mem B (slot w iM) n)
        ((s.v .v18).extractLsb' 64 64).toNat (Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1))) %
          2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sO := Nat.le_trans (slot_lt (w := w) hO) hZ
  have pAM := slot_sep (w := w) dAM
  have pOM := slot_sep (w := w) dOM
  have sep : slot w iO ≤ slot w iA + 8 ∨ slot w iA + 8 + 8 * (n + 1) ≤ slot w iO := by
    by_cases h : iO = iA
    · subst h; exact .inl (by omega)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (seqs (mredP iA iM iO)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [mredP, seqs, mulAddRow, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (seqs (mredP iA iM iO)) s fun t =>
      (wv t.mem B (slot w iO) (n + 1) : Int) = Divstep.mredRaw (wv s.mem B (slot w iM) n)
        ((s.v .v18).extractLsb' 64 64).toNat (Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1))) %
          2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [mredP, seqs, List.append_assoc]
  -- The head: `x5 := -m⁻¹`, `x8 := A`, the digit and the sign extension, `x9 := M`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x5] (Q := fun t =>
      t.gpr .x5 = (s.v .v18).extractLsb' 64 64 ∧ t.mem = s.mem)
      (by brun [exec_umov_x, Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h5, m₁⟩, k₁⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h8, m₂, _⟩, k₂⟩ => WP.block_append_iff.mpr (WP.mono (mredMid_ok s₂ (hs.congr (k₁.trans k₂).wr) h8
      (((k₁.trans k₂).gpr .x12 (by decide)).trans h12) (by omega) (by omega))
    fun s₃ ⟨⟨h1, h7, m₃⟩, k₃⟩ => WP.mono (base_ok iM .x9 (((k₁.trans k₂).trans k₃ |>.gpr .x0 (by decide)).trans h0)
      (((k₁.trans k₂).trans k₃ |>.gpr .x11 (by decide)).trans h11))
    fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have e8 : s₄.gpr .x8 = off B (slot w iA) := (k₄.gpr .x8 (by decide)).trans ((k₃.gpr .x8 (by decide)).trans h8)
  have e7 : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans h7
  have e1 : s₄.gpr .x1 = word s₂.mem B (slot w iA) * s₂.gpr .x5 := (k₄.gpr .x1 (by decide)).trans h1
  have e12 : s₄.gpr .x12 = BitVec.ofNat 64 n := (k14.gpr .x12 (by decide)).trans h12
  have hm₄ : s₄.mem = s.mem.writeW (off B (slot w iA + 8 * n + 8))
      (0#64 - (word s.mem B (slot w iA + 8 * n) >>> 63)) := by rw [m₄, m₃, m₂, m₁]
  -- `[a] += k m`.
  refine WP.seq (WP.mono (mulAddRowMod_ok (hs.congr k14.wr) e8 h9 e12 e7 hn1 (by omega) (by omega) (by omega)
    (by omega)) fun s₅ ⟨hv₅, o₅, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x16 ((k15.gpr .x0 (by decide)).trans h0)
      ((k15.gpr .x11 (by decide)).trans h11))
    fun s₆ ⟨⟨h16, m₆, _⟩, k₆⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x16] (Q := fun t =>
      t.gpr .x16 = off B (slot w iA + 8) ∧ t.mem = s₆.mem) (by brun [h16]) (by decide) (by decide)
      (by decide +kernel))
    fun s₇ ⟨⟨h16', m₇⟩, k₇⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iO .x17
      (((k15.trans k₆).trans k₇ |>.gpr .x0 (by decide)).trans h0)
      (((k15.trans k₆).trans k₇ |>.gpr .x11 (by decide)).trans h11))
    fun s₈ ⟨⟨h17, m₈, _⟩, k₈⟩ => WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.mem = s₈.mem)
      (by brun [((((k15.trans k₆).trans k₇).trans k₈).gpr .x12 (by decide)).trans h12, cntL]
          exact BitVec.ofNat_add_ofNat (n := 64) n 1) (by decide) (by decide) (by decide +kernel))
    fun s₉ ⟨⟨h14, m₉⟩, k₉⟩ => ?_))))
  have hm₉ : s₉.mem = s₅.mem := by rw [m₉, m₈, m₇, m₆]
  refine WP.mono (copyLoop_ok (hs.congr ((((k15.trans k₆).trans k₇).trans k₈).trans k₉).wr)
    ((k₉.gpr .x16 (by decide)).trans ((k₈.gpr .x16 (by decide)).trans h16')) ((k₉.gpr .x17 (by decide)).trans h17)
    h14 (by omega) (by omega) (by omega) (by omega) sep) fun t hI => ⟨?_, ?_, ?_⟩
  · have hO := hI.val
    rw [hm₉] at hO
    -- The sign extension.
    have hS := wv_lt s.mem B (slot w iA) n
    have hsl := (word s.mem B (slot w iA + 8 * n)).isLt
    have hW₁ : wv s₄.mem B (slot w iA) (n + 2) = wv s.mem B (slot w iA) (n + 1) + 2 ^ (64 * (n + 1)) *
        (if wv s.mem B (slot w iA) (n + 1) < 2 ^ (64 * (n + 1) - 1) then 0 else 2 ^ 64 - 1) := by
      rw [hm₄, show slot w iA + 8 * n + 8 = slot w iA + 8 * (n + 1) by omega,
        wv_writeW_top _ _ _ _ _ (by omega), Divstep.signMask_eq]
      rw [wv]; simp only [Divstep.top_sign hS hsl]
      split <;> rfl
    have hM₄ : wv s₄.mem B (slot w iM) n = wv s.mem B (slot w iM) n := by
      rw [hm₄]; exact (writeW_outside _ B _ (by omega)).wv (by omega) (by omega)
    have hk : (s₄.gpr .x1).toNat = (wv s.mem B (slot w iA) (n + 1) % 2 ^ 64) *
        ((s.v .v18).extractLsb' 64 64).toNat % 2 ^ 64 := by
      have e5 : s₂.gpr .x5 = (s.v .v18).extractLsb' 64 64 := (k₂.gpr .x5 (by decide)).trans h5
      rw [e1, BitVec.toNat_mul, e5, m₂, m₁, wv_mod64 _ _ _ (by omega)]
    rw [hW₁, hM₄, show n + 2 = n + 1 + 1 from rfl] at hv₅
    have hsplit := wv_add s₅.mem B (slot w iA) 1 (n + 1)
    rw [show 1 + (n + 1) = n + 2 by omega] at hsplit
    refine Divstep.mredSext_words (L := n + 1) (W₂ := wv s₅.mem B (slot w iA) (n + 2)) (by omega) hm
      (k := ((s₄.gpr .x1).toNat : Int)) ?_ ?_ ?_
    · exact_mod_cast hk
    · exact_mod_cast hv₅
    · rw [hsplit, ← hO, Nat.mul_one]
      have := wv_lt s₅.mem B (slot w iA) 1
      rw [Nat.mul_one] at this
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
  · have f1 : Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem s₄.mem := by
      rw [hm₄]
      exact Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 2)) (writeW_outside _ B _ (by omega))
        (by omega) (by omega)) (by simp)
    have f3 : Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s₅.mem t.mem := by
      rw [← hm₉]; exact Frm.of_outside hI.out (by simp)
    exact (f1.trans (Frm.of_outside o₅ (by simp))).trans f3
  · exact ((((((k15.trans k₆).trans k₇).trans k₈).trans k₉).trans hI.keep)).mono (by decide)
end VG.Proof.Rsa.AArch64
