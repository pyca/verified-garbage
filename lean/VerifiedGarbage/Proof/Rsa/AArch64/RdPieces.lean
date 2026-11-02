module

public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtRows
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Framework.Contract
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

/-!
# `vg_rsa_recover_primes_det` on AArch64: shared pieces

`M = d e` by `Crt.mulRows` (`prod_ok`), the mask of a zero register
(`zeroMask_ok`), and the subtraction loop (`subLoop_ok`, `subSet_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The registers `prod` writes. -/
def prodRegs : List Reg := [.x1, .x2, .x3, .x4, .x5, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x16, .x17]

theorem slot_aM1 (w : Nat) : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by
  simp only [slot, hdrBytes, aM]; omega_arith

/-- `prod`'s block: the bases of `e`, `d` and `M`, `w`, and the words of
`e`. -/
abbrev prodBlk : List Instr := ws ++ base aE .x5 ++ base aD .x9 ++ base aM .x8 ++
  [mov .x11 .x5, ldh .x3 Public.sElen, .addImm .x .x3 .x3 7, .lsr .x .x13 .x3 3, movi .x7 0]

theorem prod_eq : prod = [zeroA aM, zeroA (aM + 1), .block prodBlk, VG.Impl.Rsa.AArch64.Crt.mulRows] := rfl

theorem prodBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block prodBlk) s fun t =>
      (t.gpr .x0 = B ∧ t.gpr .x11 = off B (slot w aE) ∧ t.gpr .x9 = off B (slot w aD) ∧
        t.gpr .x8 = off B (slot w aM) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
        t.gpr .x13 = BitVec.ofNat 64 ((el + 7) / 8) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x3, .x5, .x7, .x8, .x9, .x11, .x12, .x13] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have e : prodBlk = ws ++ ((base aE .x5 ++ base aD .x9 ++ base aM .x8) ++
      [mov .x11 .x5, ldh .x3 Public.sElen, .addImm .x .x3 .x3 7, .lsr .x .x13 .x3 3, movi .x7 0]) := by
    simp only [prodBlk, List.append_assoc]
  rw [e]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₃ ⟨⟨h12, h11, m₃, _⟩, k₃⟩ =>
    WP.block_append_iff.mpr (WP.mono (base3_ok aE aD aM .x5 .x9 .x8 ((k₃.gpr .x0 (by decide)).trans h.x0) h11)
      fun s₄ ⟨⟨h5, h9, h8, m₄, _⟩, k₄⟩ => ?_))
  have hs₄ := h.scr.congr (k₃.trans k₄).wr
  have h0₄ : s₄.gpr .x0 = B := ((k₃.trans k₄).gpr .x0 (by decide)).trans h.x0
  refine WP.mono (WP.keep [.x11, .x3, .x13, .x7] (Q := fun t => t.gpr .x11 = off B (slot w aE) ∧
      t.gpr .x13 = BitVec.ofNat 64 ((el + 7) / 8) ∧ t.gpr .x7 = 0 ∧ t.mem = s₄.mem) (by
    brun [h5, h0₄, hdr_enc (show Public.sElen < 32 by decide), hs₄.ld (d := 8 * Public.sElen) (by
      simp only [Public.sElen, sFn]; omega_arith), m₄, m₃, hel, shr3_w el hel'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h11₅, h13₅, h7₅, m₅⟩, k₅⟩ => ?_
  exact ⟨⟨(k₅.gpr .x0 (by decide)).trans h0₄, h11₅, (k₅.gpr .x9 (by decide)).trans h9,
    (k₅.gpr .x8 (by decide)).trans h8, ((k₄.trans k₅).gpr .x12 (by decide)).trans h12, h13₅, h7₅,
    by rw [m₅, m₄, m₃]⟩, ((k₃.trans k₄).trans k₅).mono (by decide)⟩

/-- `prod`'s block and rows, from `M = 0`. -/
theorem prodLoop_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hE : wv s.mem B (slot w aE) w < 2 ^ (64 * ((el + 7) / 8)))
    (hz : wv s.mem B (slot w aM) (2 * (w + 2)) = 0) :
    WP isa (.seq (.block prodBlk) VG.Impl.Rsa.AArch64.Crt.mulRows) s fun t =>
      wv t.mem B (slot w aM) (2 * (w + 2)) = wv s.mem B (slot w aD) w * wv s.mem B (slot w aE) w ∧
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧ Keep prodRegs s t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sE := slot_lt (w := w) (show aE < 16 by decide)
  have sD := slot_lt (w := w) (show aD < 16 by decide)
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 := slot_aM1 w
  have eDM : slot w aD + 8 * (w + 2) = slot w aM := by simp only [slot, hdrBytes, aD, aM]; omega_arith
  have eEM : slot w aE + 8 * (w + 2) = slot w aD := by simp only [slot, hdrBytes, aE, aD]; omega_arith
  refine WP.seq (WP.mono (prodBlk_ok h hel (by omega_arith)) fun s₅ ⟨⟨_, h11₅, h9, h8, h12₅, h13₅, h7₅, m₅⟩, k₅⟩ => ?_)
  have hs₅ := h.scr.congr k₅.wr
  have hew : (el + 7) / 8 ≤ w := by omega_arith
  have eD : wv s₅.mem B (slot w aD) w = wv s.mem B (slot w aD) w := by rw [m₅]
  have eE : wv s₅.mem B (slot w aE) ((el + 7) / 8) = wv s.mem B (slot w aE) w := by
    rw [m₅]; exact wv_low_of_lt hew hE
  have eA : wv s₅.mem B (slot w aM) ((el + 7) / 8 + w + 2) = 0 := by
    rw [m₅]
    have := wv_add s.mem B (slot w aM) ((el + 7) / 8 + w + 2) (2 * (w + 2) - ((el + 7) / 8 + w + 2))
    rw [show (el + 7) / 8 + w + 2 + (2 * (w + 2) - ((el + 7) / 8 + w + 2)) = 2 * (w + 2) by omega_arith, hz] at this
    omega_arith
  refine WP.mono (mulRows_ok (wa := (el + 7) / 8) (wb := w) hs₅ h11₅ h9 h13₅ h12₅ h8 h7₅ (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)) (Or.inl (by omega_arith))
    (by rw [eA]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₆⟩ => ?_
  have o' : Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem := fun x hx => by
    rw [o x (by omega_arith), m₅]
  refine ⟨?_, o', (k₅.trans k₆).mono (by decide)⟩
  -- The words above the product are still zero.
  have hz' : ∀ q < 2 * (w + 2), word s.mem B (slot w aM + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz
  have e2 := wv_add t.mem B (slot w aM) ((el + 7) / 8 + w + 2) (2 * (w + 2) - ((el + 7) / 8 + w + 2))
  rw [show (el + 7) / 8 + w + 2 + (2 * (w + 2) - ((el + 7) / 8 + w + 2)) = 2 * (w + 2) by omega_arith] at e2
  rw [e2, wv_zero (n := 2 * (w + 2) - ((el + 7) / 8 + w + 2)) fun q hq => by
      rw [o.word (by omega_arith) (by omega_arith), m₅, Nat.add_assoc, ← Nat.mul_add]; exact hz' _ (by omega_arith),
    hv, eA, eE, eD]
  simp [Nat.mul_comm]

/-- `prod`: `M = d e` over `M`'s two arrays, for `e` of `⌈e_len / 8⌉` words. -/
theorem prod_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hE : wv s.mem B (slot w aE) w < 2 ^ (64 * ((el + 7) / 8))) :
    WP isa (seqs prod) s fun t =>
      wv t.mem B (slot w aM) (2 * (w + 2)) = wv s.mem B (slot w aD) w * wv s.mem B (slot w aE) w ∧
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧ Keep prodRegs s t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have sE := slot_lt (w := w) (show aE < 16 by decide)
  have sD := slot_lt (w := w) (show aD < 16 by decide)
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have eM1 := slot_aM1 w
  have eDM : slot w aD + 8 * (w + 2) = slot w aM := by simp only [slot, hdrBytes, aD, aM]; omega_arith
  have eEM : slot w aE + 8 * (w + 2) = slot w aD := by simp only [slot, hdrBytes, aE, aD]; omega_arith
  have h20 : 8 * Public.sElen + 8 ≤ slot w aM := hdr_lt_slot w aM (show Public.sElen < 32 by decide)
  rw [prod_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := aM) (by decide)) fun s₁ ⟨z₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₁ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := aM + 1) (by decide)) fun s₂ ⟨z₂, o₂, _, _, _, k₂⟩ => ?_)
  have h₂ := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₂ (by decide)
  -- Memory but `M` as on entry.
  have o12 : Outside B (slot w aM) (16 * (w + 2)) s.mem s₂.mem := fun x hx => by
    rw [o₂ x (by omega_arith), o₁ x (by omega_arith)]
  have hel₂ : word s₂.mem B (8 * Public.sElen) = BitVec.ofNat 64 el := by
    rw [o12.word (Or.inl h20) (by omega_arith)]; exact hel
  have hz : wv s₂.mem B (slot w aM) (2 * (w + 2)) = 0 := by
    rw [show 2 * (w + 2) = (w + 2) + (w + 2) by omega_arith, wv_add, ← eM1, z₂,
      o₂.wv (Or.inl (by omega_arith)) (by omega_arith), z₁, Nat.mul_zero]
  refine WP.mono (prodLoop_ok h₂ hel₂ he1 he2 (by rw [o12.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hE) hz)
    fun t ⟨hv, o, k₃⟩ => ⟨by rw [hv, o12.wv (Or.inl (by omega_arith)) (by omega_arith), o12.wv (Or.inl (by omega_arith)) (by omega_arith)],
      fun x hx => by rw [o x hx, o12 x hx], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

end VG.Proof.Rsa.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word's low bit, as a word. -/
theorem and_one (x : BitVec 64) : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega_arith)]

/-- The mask of an even word, from its low bit. -/
theorem low_sub_one (x : BitVec 64) :
    (x &&& BitVec.setWidth 64 1#16) - BitVec.ofNat 64 1 = mask (decide (x.toNat % 2 = 0)) := by
  rw [and_one]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- `zeroMask`: `x15` the mask of `x9 = 0`, and `x7 = 0`. -/
theorem zeroMask_ok (s : State) :
    WP isa (.block zeroMask) s fun t =>
      (t.gpr .x15 = mask (decide (s.gpr .x9 = 0)) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x7, .x15] s t :=
  WP.keep [.x3, .x4, .x7, .x15] (by brun [zeroMask, borrowMask, csel_mask', subs_one_c, Bool.not_not])
    (by decide) (by decide) (by decide +kernel)

end VG.Proof.Rsa.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)

/-- The bases of a subtraction `[c] := [a] - [b]` over `w` words, from the
carry set. -/
theorem subSet_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (a b c : Nat) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17 ++
      base c .x13)) s fun t =>
      (t.gpr .x16 = off B (slot w a) ∧ t.gpr .x17 = off B (slot w b) ∧ t.gpr .x13 = off B (slot w c) ∧
        t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ t.c = true ∧
        t.mem = s.mem) ∧ Keep [.x3, .x7, .x11, .x12, .x13, .x14, .x16, .x17] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧
      t.c = true ∧ t.mem = t₁.mem) (by brun [h12]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  rw [← List.append_assoc]
  refine WP.mono (base3_ok a b c .x16 .x17 .x13 h0₂ ((k₂.gpr .x11 (by decide)).trans h11))
    fun t ⟨⟨h16, h17, h13, m₃, c₃⟩, k₃⟩ => ⟨⟨h16, h17, h13, (k₃.gpr .x14 (by decide)).trans h14,
      (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12), (k₃.gpr .x7 (by decide)).trans h7,
      c₃.trans hc, by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- The loop of `subBody`: `[x13] := [x16] - [x17]` over `N` words, from the
carry set. -/
theorem subLoop_ok {s : State} {B : Addr} {Z N eA eN eT : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eN) (h13 : s.gpr .x13 = off B eT)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (hc : s.c = true) (hN1 : 1 ≤ N) (hN : N < 2 ^ 31)
    (hA : eA + 8 * N ≤ Z) (hNz : eN + 8 * N ≤ Z) (hT : eT + 8 * N ≤ Z)
    (sA : eT + 8 * N ≤ eA ∨ eA + 8 * N ≤ eT) (sN : eT + 8 * N ≤ eN ∨ eN + 8 * N ≤ eT) :
    WP isa (countLoop .x14 subBody) s fun t =>
      wv t.mem B eT N + wv s.mem B eN N = wv s.mem B eA N + 2 ^ (64 * N) * (!t.c).toNat ∧
      Outside B eT (8 * N) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t := by
  unfold countLoop subBody
  refine WP.mono (wp_countdown (N := N) (by omega_arith) (by omega_arith) (SubInv s B Z eA eN eT)
    (fun j hj t hI _ => subStep_ok hA hNz hT sA sN hj hI)
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; rfl⟩ h14) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

end VG.Proof.Rsa.AArch64
