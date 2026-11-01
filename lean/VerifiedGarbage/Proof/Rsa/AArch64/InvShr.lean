module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Divstep.RowWord
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the batched inverse's shift by 59

`shrP s o`: `[o] := [s] >> 59` as signed numbers of `n + 1` words
(`shrP_ok`), by `shr59Body` a word at a time (`shrWord_ok`, invariant
`Shr59Inv`: `Divstep.shr_step`) and the top word from the sign
(`shrTop_ok`, `Divstep.shr_final`). `[o]` may be `[s]`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of the shift: words `j` and `j + 1` of `[x16]` into word `j` of `[x17]`. -/
theorem shrWord_ok (s : State) {B : Addr} {Z eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (hS : eS + 16 ≤ Z) (hO : eO + 8 ≤ Z) :
    WP isa (.block shr59Body) s fun t => ∃ o : BitVec 64, t.mem = s.mem.writeW (off B eO) o ∧
      o.toNat = (word s.mem B eS).toNat / 2 ^ 59 + 2 ^ 5 * ((word s.mem B (eS + 8)).toNat % 2 ^ 59) ∧
      t.gpr .x16 = off B (eS + 8) ∧ t.gpr .x17 = off B (eO + 8) := by
  unfold shr59Body
  brun [h16, h17, hs.ld (show eS + 8 ≤ Z by omega), hs.ld (show eS + 8 + 8 ≤ Z by omega), hs.st hO, exec_extr_x]
  exact ⟨_, rfl, Divstep.extr59 _ _⟩

/-- The top word of the shift, from the sign. -/
theorem shrTop_ok (s : State) {B : Addr} {Z eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (hS : eS + 8 ≤ Z) (hO : eO + 8 ≤ Z) :
    WP isa (.block shrTop) s fun t => ∃ o : BitVec 64, t.mem = s.mem.writeW (off B eO) o ∧
      o.toNat = (word s.mem B eS).toNat / 2 ^ 59 +
        2 ^ 5 * ((if (word s.mem B eS).toNat < 2 ^ 63 then 0 else 2 ^ 64 - 1) % 2 ^ 59) := by
  unfold shrTop
  brun [h16, h17, hs.ld hS, hs.st hO, exec_extr_x, show BitVec.setWidth 64 0#16 = 0#64 from rfl]
  refine ⟨_, rfl, ?_⟩
  rw [Divstep.extr59, Divstep.signMask_eq]
  split <;> rfl

/-- After `j` words of the shift: the `j + 1` words read are the low 59 bits
of word 0, `2^59` times the `j` words written, and the rest of word `j`. -/
structure Shr59Inv (s₀ : State) (B : Addr) (Z eS eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eS + 8 * j)
  x17 : t.gpr .x17 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : wv s₀.mem B eS (j + 1) = (word s₀.mem B eS).toNat % 2 ^ 59 + 2 ^ 59 * wv t.mem B eO j +
    2 ^ (64 * j) * 2 ^ 59 * ((word s₀.mem B (eS + 8 * j)).toNat / 2 ^ 59)

theorem shr59Step_ok {s₀ : State} {B : Addr} {Z n eS eO : Nat} (hS : eS + 8 * (n + 1) ≤ Z)
    (hO : eO + 8 * (n + 1) ≤ Z) (sep : eO ≤ eS ∨ eS + 8 * (n + 1) ≤ eO)
    {j : Nat} (hj : j < n) {t : State} (hI : Shr59Inv s₀ B Z eS eO j t) :
    WP isa (.block (shr59Body ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      Shr59Inv s₀ B Z eS eO (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (shrWord_ok t hI.scr hI.x16 hI.x17 (by omega) (by omega))
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨o, hm, ho, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) o := hm'.trans hm
  have h0 : word t.mem B (eS + 8 * j) = word s₀.mem B (eS + 8 * j) := hI.out.word (by omega) (by omega)
  have h1 : word t.mem B (eS + 8 * j + 8) = word s₀.mem B (eS + 8 * j + 8) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B o (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega)]
    rw [h0, h1] at ho
    have st := Divstep.shr_step (P := 2 ^ (64 * j)) hI.val ho
    rw [wv, pow64_succ, show eS + 8 * (j + 1) = eS + 8 * j + 8 by omega]
    exact st

/-- `shrP s o`: `[o] := [s] >> 59`, arithmetic, `n + 1` words: as signed
numbers `2^59 [o] + ([s] mod 2^59) = [s]`. `[o]` may be `[s]`. -/
theorem shrP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iS iO : Nat} (hS : iS < 16) (hO : iO < 16) :
    WP isa (shrP iS iO) s fun t =>
      2 ^ 59 * Divstep.sgn (n + 1) (wv t.mem B (slot w iO) (n + 1)) + (wv s.mem B (slot w iS) (n + 1) % 2 ^ 59 : Nat) =
        Divstep.sgn (n + 1) (wv s.mem B (slot w iS) (n + 1)) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sS := Nat.le_trans (slot_lt (w := w) hS) hZ
  have sO := Nat.le_trans (slot_lt (w := w) hO) hZ
  have sep : slot w iO ≤ slot w iS ∨ slot w iS + 8 * (n + 1) ≤ slot w iO := by
    by_cases h : iO = iS
    · subst h; exact .inl (Nat.le_refl _)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (shrP iS iO).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [shrP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (shrP iS iO) s fun t =>
      2 ^ 59 * Divstep.sgn (n + 1) (wv t.mem B (slot w iO) (n + 1)) + (wv s.mem B (slot w iS) (n + 1) % 2 ^ 59 : Nat) =
        Divstep.sgn (n + 1) (wv s.mem B (slot w iS) (n + 1)) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold shrP
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base2_ok iS iO .x16 .x17 h0 h11)
    fun s₁ ⟨⟨h16, h17, m₁, _⟩, k₁⟩ => WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.mem = s₁.mem)
      (by brun [(k₁.gpr .x12 (by decide)).trans h12]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, m₂⟩, k₂⟩ => ?_))
  have hm : s₂.mem = s.mem := m₂.trans m₁
  have I0 : Shr59Inv s₂ B Z (slot w iS) (slot w iO) 0 s₂ :=
    ⟨hs.congr (k₁.trans k₂).wr, Keep.refl _ _, by rw [k₂.gpr .x16 (by decide), h16]; rfl,
      by rw [k₂.gpr .x17 (by decide), h17]; rfl, Outside.refl _ _ _ _, by
        simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_zero]
        omega⟩
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega) (by omega) (Shr59Inv s₂ B Z (slot w iS) (slot w iO))
    (fun j hj t hI _ => shr59Step_ok (by omega) (by omega) sep hj hI) I0 h14) fun u hI => ?_)
  refine WP.mono (WP.keep [.x3, .x4, .x13] (shrTop_ok u hI.scr hI.x16 hI.x17 (by omega) (by omega))
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨o, hmt, ho⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · have hsn : word u.mem B (slot w iS + 8 * n) = word s₂.mem B (slot w iS + 8 * n) :=
      hI.out.word (by omega) (by omega)
    rw [hsn] at ho
    have st := Divstep.shr_step (P := 2 ^ (64 * n)) hI.val ho
    have hW := wv_lt s₂.mem B (slot w iS) n
    have hsl := (word s₂.mem B (slot w iS + 8 * n)).isLt
    have fin := Divstep.shr_final (L := n + 1) (S := wv s₂.mem B (slot w iS) (n + 1))
      (O := wv t.mem B (slot w iO) (n + 1)) (by omega) (wv_lt _ _ _ _) (wv_lt _ _ _ _) (Nat.mod_lt _ (by decide))
      (M := if (word s₂.mem B (slot w iS + 8 * n)).toNat < 2 ^ 63 then 0 else 2 ^ 64 - 1)
      (by rw [wv]; simp only [Divstep.top_sign hW hsl]) (by
        rw [hmt, wv_writeW_top _ _ _ _ _ (by omega), pow64_succ]
        rw [wv] at st ⊢
        exact st)
    rw [← hm, ← fin, ← wv_mod64 _ _ _ (show 1 ≤ n + 1 by omega), Nat.mod_mod_of_dvd _ (by decide)]
  · rw [← hm, hmt]
    refine fun x hx' => ?_
    rw [writeW_outside u.mem B o (by omega) x (by omega)]
    exact hI.out x (by omega)
  · exact (((k₁.trans k₂).trans hI.keep).trans kt).mono (by decide)
end VG.Proof.Rsa.AArch64
