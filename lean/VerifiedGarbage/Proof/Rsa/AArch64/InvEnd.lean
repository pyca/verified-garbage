module
-- separate module: the end pieces build in parallel with the batches (`InvLoop`, `InvInit`)

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Rsa.AArch64.InvPieces
import VerifiedGarbage.Proof.Rsa.AArch64.InvMred
import VerifiedGarbage.Proof.Divstep.RowWord
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the pieces of the batched inverse's end

`cnegP_ok`: `[x] := -[x]` where a mask says so, by `cnegBody` in place
(`cnegLoop_ok`); `addIfNeg_ok`: `[a] += m` if `[a]` is negative (the masked
addition in place, then the top word); `csubP_ok`: `[a] mod m` for
`[a] < 2 m` (`subMod`, `selectAcc` in place: `selectAccIP_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of `cnegBody`'s value: `(x ^ m) + C`. -/
theorem xor_mask (x : BitVec 64) (neg : Bool) :
    (x ^^^ mask neg).toNat = if neg then 2 ^ 64 - 1 - x.toNat else x.toNat := by
  cases neg
  · simp [mask_false]
  · simp only [mask_true, ite_true, BitVec.xor_allOnes, BitVec.toNat_not]

/-- After `j` words of `cnegBody` in place. -/
structure CnegInv (s₀ : State) (B : Addr) (Z eX : Nat) (neg : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  out : Outside B eX (8 * j) s₀.mem t.mem
  val : wv t.mem B eX j + 2 ^ (64 * j) * t.c.toNat =
    (if neg then 2 ^ (64 * j) - 1 - wv s₀.mem B eX j else wv s₀.mem B eX j) + neg.toNat

theorem cnegLoop_ok {s : State} {B : Addr} {Z L eX : Nat} {neg : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h14 : s.gpr .x14 = BitVec.ofNat 64 L) (h15 : s.gpr .x15 = mask neg)
    (h7 : s.gpr .x7 = 0) (hc : s.c = neg) (hL : 1 ≤ L) (hL' : L < 2 ^ 32) (hX : eX + 8 * L ≤ Z) :
    WP isa (countLoop .x14 cnegBody) s (CnegInv s B Z eX neg L) := by
  have hn := hs.nowrap
  have h0 : CnegInv s B Z eX neg 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, by cases neg <;> simp [wv, hc]⟩
  refine wp_countdown (N := L) (by omega) (by omega) (CnegInv s B Z eX neg) (fun j hj t hI _ => ?_) h0 h14
  have t15 : t.gpr .x15 = mask neg := (hI.keep.gpr .x15 (by decide)).trans h15
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) ((word t.mem B (eX + 8 * j) ^^^ mask neg) + 0 +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j) ^^^ mask neg).toNat + (0 : BitVec 64).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8))
    (by unfold cnegBody; brun [hI.x16, t15, t7, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word s.mem B (eX + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc'', hc']
    have hval := hI.val
    have xm := xor_mask (word s.mem B (eX + 8 * j)) neg
    rw [hx]
    simp only [wv]
    have hW := wv_lt s.mem B eX j
    have hw := (word s.mem B (eX + 8 * j)).isLt
    rw [pow64_succ]
    have ad := adcs_toNat (word s.mem B (eX + 8 * j) ^^^ mask neg) 0 t.c
    rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at ad
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.add_zero, Nat.mul_assoc, Nat.add_assoc,
      ← Nat.mul_add, ad, xm]
    generalize hP : 2 ^ (64 * j) = P at *
    have hP1 : 1 ≤ P := by rw [← hP]; exact Nat.one_le_two_pow
    have hc1 := Bool.toNat_le t.c
    cases neg
    · simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero] at hval ⊢
      rw [Nat.mul_add]; omega
    · simp only [ite_true, Bool.toNat_true] at hval ⊢
      have e1 : P * (2 ^ 64 - 1 - (word s.mem B (eX + 8 * j)).toNat + t.c.toNat) =
          P * 2 ^ 64 - P - P * (word s.mem B (eX + 8 * j)).toNat + P * t.c.toNat := by
        rw [Nat.mul_add, Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have e2 : P * (word s.mem B (eX + 8 * j)).toNat ≤ P * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_sub, Nat.mul_one] at e2
      have e3 : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      rw [e1]; omega

/-- `cnegP x`: `[x] := -[x]` (`n + 1` words) where `x15` is the mask of `neg`. -/
theorem cnegP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iX : Nat} (hX : iX < 16) {neg : Bool}
    (h15 : s.gpr .x15 = mask neg) :
    WP isa (cnegP iX) s fun t =>
      wv t.mem B (slot w iX) (n + 1) + 2 ^ (64 * (n + 1)) * t.c.toNat =
        (if neg then 2 ^ (64 * (n + 1)) - 1 - wv s.mem B (slot w iX) (n + 1) else wv s.mem B (slot w iX) (n + 1)) +
          neg.toNat ∧
      Outside B (slot w iX) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x7, .x14, .x16] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sX := Nat.le_trans (slot_lt (w := w) hX) hZ
  have hvn : (cnegP iX).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [cnegP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t => wv t.mem B (slot w iX) (n + 1) + 2 ^ (64 * (n + 1)) * t.c.toNat =
        (if neg then 2 ^ (64 * (n + 1)) - 1 - wv s.mem B (slot w iX) (n + 1) else wv s.mem B (slot w iX) (n + 1)) +
          neg.toNat ∧
      Outside B (slot w iX) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x7, .x14, .x16] s t) ?_ hvn)
    fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold cnegP
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iX .x16 h0 h11) fun s₁ ⟨⟨h16, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.gpr .x7 = 0 ∧
      t.c = neg ∧ t.mem = s₁.mem)
      (by
        brun [(k₁.gpr .x12 (by decide)).trans h12, (k₁.gpr .x15 (by decide)).trans h15, cntL]
        exact ⟨BitVec.ofNat_add_ofNat (n := 64) n 1, by cases neg <;> decide⟩) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (cnegLoop_ok (hs.congr k12.wr) ((k₂.gpr .x16 (by decide)).trans h16) h14
    ((k12.gpr .x15 (by decide)).trans h15) h7 hc (by omega) (by omega) (by omega)) fun t hI => ⟨?_, ?_, ?_⟩
  · have := hI.val; rw [m₂, m₁] at this; exact this
  · rw [← m₁, ← m₂]; exact hI.out
  · exact (k12.trans hI.keep).mono (by decide)

/-- The sign mask of word `n` as a `mask`. -/
theorem zero_add64' (x y : BitVec 64) : x + 0 + y = x + y := by rw [add_zero64]

theorem signMask_mask (x : BitVec 64) : 0#64 - (x >>> 63) = mask (decide (2 ^ 63 ≤ x.toNat)) := by
  rw [Divstep.signMask_eq]
  by_cases h : x.toNat < 2 ^ 63
  · rw [ite_eq_left h, decide_eq_false (by omega)]; rfl
  · rw [ite_eq_right h, decide_eq_true (by omega)]; rfl

/-- `addIfNeg a m`: `[a] += m` (`n + 1` words, `m` of `n`) if word `n` of `[a]`
is negative, modulo `2^(64 (n + 1))`. -/
theorem addIfNeg_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM : Nat} (hA : iA < 16) (hM : iM < 16)
    (dAM : iA ≠ iM) :
    WP isa (seqs (addIfNeg iA iM)) s fun t =>
      wv t.mem B (slot w iA) (n + 1) = (wv s.mem B (slot w iA) (n + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat then wv s.mem B (slot w iM) n else 0)) %
          2 ^ (64 * (n + 1)) ∧
      Outside B (slot w iA) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sepAM := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dAM (by omega) (by omega)
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  have hvn : (seqs (addIfNeg iA iM)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [addIfNeg, seqs, signMask, topAt, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t => wv t.mem B (slot w iA) (n + 1) = (wv s.mem B (slot w iA) (n + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat then wv s.mem B (slot w iM) n else 0)) %
          2 ^ (64 * (n + 1)) ∧
      Outside B (slot w iA) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [addIfNeg, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (signMask_ok hs iA h0 h11 h12 hn hw hA hZ)
    fun s₁ ⟨⟨h15, h7, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false ∧ t.mem = s₁.mem)
      (by brun [(k₁.gpr .x12 (by decide)).trans h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, hc, m₂⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h10, m₃, c₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h8, m₄, c₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (base_ok iA .x5 ((k14.gpr .x0 (by decide)).trans h0)
    ((k14.gpr .x11 (by decide)).trans h11)) fun s₅ ⟨⟨h5, m₅, c₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  refine WP.seq (WP.mono (addMIP_ok (N := n) (c := decide (2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat))
    (hs.congr k15.wr) ((k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans h10))
    ((k₅.gpr .x8 (by decide)).trans h8) h5
    ((k₅.gpr .x14 (by decide)).trans ((k₄.gpr .x14 (by decide)).trans ((k₃.gpr .x14 (by decide)).trans h14)))
    (by rw [(k₅.gpr .x15 (by decide)).trans ((k₄.gpr .x15 (by decide)).trans ((k₃.gpr .x15 (by decide)).trans
      ((k₂.gpr .x15 (by decide)).trans h15))), signMask_mask])
    (by rw [c₅, c₄, c₃, hc]) hn1 (by omega) (by omega) (by omega) (by omega) (by rcases sepAM with h | h <;> omega)
    (.inl (Nat.le_refl _))) fun s₆ ⟨e₆, h5', o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  have g7 : s₆.gpr .x7 = 0 := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆ |>.gpr .x7 (by decide)).trans h7
  have An : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  have Mn : wv s₅.mem B (slot w iM) n = wv s.mem B (slot w iM) n := by rw [hm₅]
  rw [An, Mn] at e₆
  have top₆ : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
    rw [o₆.word (by omega) (by omega), hm₅]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₆.mem.writeW (off B (slot w iA + 8 * n))
      (word s.mem B (slot w iA + 8 * n) + 0 + BitVec.ofNat 64 s₆.c.toNat))
    (by brun [h5', g7, (hs.congr k16.wr).ld (show slot w iA + 8 * n + 8 ≤ Z by omega),
      (hs.congr k16.wr).st (show slot w iA + 8 * n + 8 ≤ Z by omega), top₆]) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k16.trans k).mono (by decide)⟩
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega), zero_add64', wv]
    have hW := wv_lt s₆.mem B (slot w iA) n
    have ad : (word s.mem B (slot w iA + 8 * n) + BitVec.ofNat 64 s₆.c.toNat).toNat =
        ((word s.mem B (slot w iA + 8 * n)).toNat + s₆.c.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s₆.c.toNat < 2 ^ 64 by
        have := Bool.toNat_le s₆.c; omega)]
    rw [ad, show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add,
      ← add_mul_mod_mul (Q := 2 ^ 64) hW]
    congr 1
    simp only [decide_eq_true_eq] at e₆
    rw [Nat.mul_add, ← Nat.add_assoc, Nat.add_right_comm, e₆]
    ac_rfl
  · rw [hm, ← hm₅]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega)]
    exact Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₆ (Nat.le_refl _) (by omega) x hx
/-- `selectAcc`, its output possibly its accumulator. -/
theorem selectAccIP_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h6 : s.gpr .x6 = off B eT) (h5 : s.gpr .x5 = off B eo)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) {lt : Bool} (hc : s.c = !lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = s.c ∧ t.mem = s.mem) (by brun [h8, h12])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SelInv s₁ B Z eA eT eo lt 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [k₁.gpr .x6 (by decide), h6]; rfl,
      by rw [k₁.gpr .x5 (by decide), h5]; rfl, hc₁.trans hc, Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (SelInv s₁ B Z eA eT eo lt) ?_ h0 h14)
    fun t hI => ⟨by rw [hI.val, hm₁], by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  intro j hj t hI _
  have hx : word t.mem B (eA + 8 * j) = word s₁.mem B (eA + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eT + 8 * j) = word s₁.mem B (eT + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if t.c then word t.mem B (eT + 8 * j) else word t.mem B (eA + 8 * j)) ∧ t₁.c = t.c ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x6 = off B (eT + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8)) (by
      brun [hI.x16, hI.x6, hI.x5, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16', h6', h5'⟩, k₁'⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ =>
    ⟨?_, by rw [h14', k₁'.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁'.wr), (hI.keep.trans (k₁'.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x6 (by decide), h6', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5', Nat.mul_succ, Nat.add_assoc], by rw [hc'', hc', hI.c], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hI.val, hI.c, hx, hy]
    cases lt <;> simp [wv]


/-- `csubP a m t`: `[a] := [a] mod m` for `[a] < 2 m` (`n + 1` words, `m` of
`n`), through `[t]`, and word `n` of `[a]` cleared. -/
theorem csubP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (csubP iA iM iT)) s fun t =>
      (wv s.mem B (slot w iA) (n + 1) < 2 * wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) (n + 1) = wv s.mem B (slot w iA) (n + 1) % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have hvn : (seqs (csubP iA iM iT)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [csubP, seqs, zeroTop, topAt, selectAcc, Code.allInstrs_eq, instrs, List.all_append,
      base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t =>
      (wv s.mem B (slot w iA) (n + 1) < 2 * wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) (n + 1) = wv s.mem B (slot w iA) (n + 1) % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x13, .x14, .x16, .x17] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [csubP, seqs, List.append_assoc]
  have pAT := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAT (by omega) (by omega)
  have pMT := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dMT (by omega) (by omega)
  have pAM := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAM (by omega) (by omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 h0 h11) fun s₁ ⟨⟨h8, m₁, _⟩, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h10, m₂, _⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iT .x6 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h6, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iA .x5 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h5, m₄, _⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun s₅ ⟨⟨h7, m₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  refine WP.seq (WP.mono (subMod_ok (w := n) (hs.congr k15.wr)
    ((k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans ((k₃.gpr .x8 (by decide)).trans
      ((k₂.gpr .x8 (by decide)).trans h8))))
    ((k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans ((k₃.gpr .x10 (by decide)).trans h10)))
    ((k₅.gpr .x6 (by decide)).trans ((k₄.gpr .x6 (by decide)).trans h6)) ((k15.gpr .x12 (by decide)).trans h12) h7
    hn1 (by omega) (by omega) (by omega) (by omega) (by rcases pAT with h | h <;> omega)
    (by rcases pMT with h | h <;> omega)) fun s₆ ⟨c, hc, hD, o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.seq (WP.mono (selectAccIP_ok (w := n) (hs.congr k16.wr)
    ((k₆.gpr .x8 (by decide)).trans ((k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans
      ((k₃.gpr .x8 (by decide)).trans ((k₂.gpr .x8 (by decide)).trans h8)))))
    ((k₆.gpr .x6 (by decide)).trans ((k₅.gpr .x6 (by decide)).trans ((k₄.gpr .x6 (by decide)).trans h6)))
    ((k₆.gpr .x5 (by decide)).trans ((k₅.gpr .x5 (by decide)).trans h5)) ((k16.gpr .x12 (by decide)).trans h12)
    hc hn1 (by omega) (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by rcases pAT with h | h <;> omega))
    fun s₇ ⟨hv₇, o₇, k₇⟩ => ?_)
  have k17 := k16.trans k₇
  refine WP.mono (zeroTop_ok (hs.congr k17.wr) iA ((k17.gpr .x0 (by decide)).trans h0)
    ((k17.gpr .x11 (by decide)).trans h11) ((k17.gpr .x12 (by decide)).trans h12) hn hw hA hZ)
    fun t ⟨⟨m₈, _, _⟩, k₈⟩ => ⟨fun hlt => ?_, ?_, (k17.trans k₈).mono (by decide)⟩
  · have A6 : wv s₆.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by
      rw [o₆.wv (by rcases pAT with h | h <;> omega) (by omega), hm₅]
    have Aw : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
      rw [o₆.word (by rcases pAT with h | h <;> omega) (by omega), hm₅]
    rw [hm₅] at hD
    have hp := wv_lt s.mem B (slot w iM) n
    have cs := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w iA) n)
      (Tw := (word s.mem B (slot w iA + 8 * n)).toNat) (Tw1 := 0) (D := wv s₆.mem B (slot w iT) n)
      (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n)) (c := c.toNat) hp (wv_lt _ _ _ _) (Bool.toNat_le c)
      (wv_lt _ _ _ _) (by rw [Nat.mul_zero, Nat.add_zero]; rw [wv] at hlt; omega) hD
    rw [hm₅] at hv₇
    rw [m₈, wv_writeW_top _ _ _ _ _ (by omega), hv₇, A6]
    rw [Nat.mul_zero, Nat.add_zero] at cs
    rw [wv, ← cs]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    by_cases h : (word s.mem B (slot w iA + 8 * n)).toNat < c.toNat <;> simp [h]
  · have f6 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₅.mem s₆.mem := Frm.of_outside o₆ (by simp)
    have f7 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₆.mem s₇.mem :=
      Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₇ (Nat.le_refl _) (by omega)) (by simp)
    have f8 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₇.mem t.mem := by
      rw [m₈]; exact Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1))
        (writeW_outside _ B _ (by omega)) (by omega) (by omega)) (by simp)
    rw [← hm₅]; exact (f6.trans f7).trans f8

/-- `dblP a m t s`: `[a] := 2 [a] mod m` (`n` words, `[a] < m`), the double in
`[t]` and the difference in `[s]`. -/
theorem dblP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT iS : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (hS : iS < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dAS : iA ≠ iS) (dMT : iM ≠ iT)
    (dMS : iM ≠ iS) (dTS : iT ≠ iS) :
    WP isa (dblP iA iM iT iS) s fun t =>
      (wv s.mem B (slot w iA) n < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) n = 2 * wv s.mem B (slot w iA) n % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt (w := w) hj) hZ
  have sA := sl _ hA; have sM := sl _ hM; have sT := sl _ hT; have sS := sl _ hS
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (n + 1) ≤ slot w k ∨ slot w k + 8 * (n + 1) ≤ slot w j :=
    fun h => slot_apart (w := w) h (by omega) (by omega)
  have hvn : (dblP iA iM iT iS).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [dblP, selectAcc, countLoop, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t =>
      (wv s.mem B (slot w iA) n < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) n = 2 * wv s.mem B (slot w iA) n % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold dblP
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x5 h0 h11) fun s₁ ⟨⟨h5, m₁, _⟩, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h10, m₂, _⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iT .x8 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iS .x6 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h6, m₄, _⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (WP.keep [.x7, .x14, .x16, .x17, .x3] (Q := fun t => t.gpr .x7 = 0 ∧
      t.gpr .x17 = off B (slot w iA) ∧ t.gpr .x16 = off B (slot w iT) ∧ t.gpr .x14 = BitVec.ofNat 64 n ∧
      t.c = false ∧ t.mem = s₄.mem)
    (by brun [(k₄.gpr .x5 (by decide)).trans ((k₃.gpr .x5 (by decide)).trans ((k₂.gpr .x5 (by decide)).trans h5)),
      (k₄.gpr .x8 (by decide)).trans h8, (k14.gpr .x12 (by decide)).trans h12])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨h7, h17, h16, h14, hc₅, m₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  have e5 : s₅.gpr .x5 = off B (slot w iA) :=
    (k₅.gpr .x5 (by decide)).trans ((k₄.gpr .x5 (by decide)).trans ((k₃.gpr .x5 (by decide)).trans
      ((k₂.gpr .x5 (by decide)).trans h5)))
  have e10 : s₅.gpr .x10 = off B (slot w iM) :=
    (k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans ((k₃.gpr .x10 (by decide)).trans h10))
  have e8 : s₅.gpr .x8 = off B (slot w iT) := (k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans h8)
  have e6 : s₅.gpr .x6 = off B (slot w iS) := (k₅.gpr .x6 (by decide)).trans h6
  have e12 : s₅.gpr .x12 = BitVec.ofNat 64 n := (k15.gpr .x12 (by decide)).trans h12
  have pTA := sp (Ne.symm dAT); have pTS := sp dTS; have pMS := sp dMS; have pAS := sp dAS
  have pAM := sp dAM; have pMT := sp dMT
  have hs₅ := hs.congr k15.wr
  have h0' : DblInv s₅ B Z (slot w iT) (slot w iA) 0 s₅ :=
    ⟨hs₅, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by rw [hc₅]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega) (by omega)
    (DblInv s₅ B Z (slot w iT) (slot w iA))
    (fun j hj t hI _ => dblStep_ok (w := n) (by omega) (by omega)
      (by rcases pTA with h | h <;> omega) hj hI) h0' h14) fun s₆ hI => ?_)
  have hval := hI.val
  have s₆7 : s₆.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₆.mem.writeW (off B (slot w iT + 8 * n)) (BitVec.ofNat 64 s₆.c.toNat))
    (by brun [hI.x16, s₆7, hI.scr.st (show slot w iT + 8 * n + 8 ≤ Z by omega)]
        simp only [add_zero64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨hm₇, k₇⟩ => ?_)
  have hs₇ := hI.scr.congr k₇.wr
  have k57 := hI.keep.trans k₇
  have o7 : Outside B (slot w iT) (8 * (n + 1)) s₅.mem s₇.mem := by
    rw [hm₇]
    intro x hx
    rw [writeW_outside s₆.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₅] at o7
  have fM : wv s₇.mem B (slot w iM) n = wv s.mem B (slot w iM) n :=
    o7.wv (by rcases pMT with h | h <;> omega) (by omega)
  have hTl : wv s₇.mem B (slot w iT) n = wv s₆.mem B (slot w iT) n := by
    rw [hm₇]; exact (writeW_outside s₆.mem B _ (by omega)).wv (Or.inl (by omega)) (by omega)
  have hTw : (word s₇.mem B (slot w iT + 8 * n)).toNat = s₆.c.toNat := by
    rw [hm₇, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le s₆.c; omega)]
  refine WP.seq (WP.mono (subMod_ok (w := n) hs₇ ((k57.gpr .x8 (by decide)).trans e8)
    ((k57.gpr .x10 (by decide)).trans e10) ((k57.gpr .x6 (by decide)).trans e6)
    ((k57.gpr .x12 (by decide)).trans e12) ((k57.gpr .x7 (by decide)).trans h7) hn1 (by omega) (by omega)
    (by omega) (by omega) (by rcases pTS with h | h <;> omega) (by rcases pMS with h | h <;> omega))
    fun s₈ ⟨c', hc₈, hD, o₈, k₈⟩ => ?_)
  have k58 := k57.trans k₈
  refine WP.mono (selectAcc_ok (w := n) (hs₇.congr k₈.wr) ((k58.gpr .x8 (by decide)).trans e8)
    ((k58.gpr .x6 (by decide)).trans e6) ((k58.gpr .x5 (by decide)).trans e5)
    ((k58.gpr .x12 (by decide)).trans e12) hc₈ hn1 (by omega) (by omega) (by omega) (by omega)
    (by rcases pTA with h | h <;> omega) (by rcases pAS with h | h <;> omega)) fun t ⟨hv', hot, k₉⟩ => ?_
  have hT₈ : wv s₈.mem B (slot w iT) n = wv s₇.mem B (slot w iT) n :=
    o₈.wv (by rcases pTS with h | h <;> omega) (by omega)
  rw [fM] at hD
  have fA : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  rw [fA] at hval
  refine ⟨fun hlt => ?_, ?_, ((k15.trans k58).trans k₉).mono (by decide)⟩
  · rw [hv', hT₈, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₇.mem B (slot w iT) n) (Tw := s₆.c.toNat) (Tw1 := 0)
      (D := wv s₈.mem B (slot w iS) n) (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n))
      (c := c'.toNat) (wv_lt s.mem B (slot w iM) n) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : s₆.c.toNat < c'.toNat <;> simp [h, hTl]
  · have f7 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem s₇.mem :=
      Frm.of_outside o7 (by simp)
    have f8 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₇.mem s₈.mem :=
      Frm.of_outside o₈ (by simp)
    have f9 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₈.mem t.mem :=
      Frm.of_outside hot (by simp)
    exact (f7.trans f8).trans f9
end VG.Proof.Rsa.AArch64