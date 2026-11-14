module

public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.WordStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Bignum.LongDivision
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: division by words with the quotient

`RecoverDet.qDiv e`: at the wide width `W = 2 h + 4`, the dividend's
`L = 2 h + e - 1` words `A` divided by a normalized divisor `M` of `h` words.
After the words above `c`, the remainder is `⌊A / 2^(64 c)⌋ mod M` and the
quotient `⌊⌊A / 2^(64 c)⌋ / M⌋ 2^(64 c)` (`QSt`); a step brings down word
`c - 1` by `WordReduce.step` (`stepQ_ok`) and stores its digit
(`LongDivision.div_step`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Words -/

/-- The top `L - c` of `L` words. -/
def pre (m : Mem) (B : Addr) (e L c : Nat) : Nat := wv m B (e + 8 * c) (L - c)

theorem pre_step (m : Mem) (B : Addr) {e L c : Nat} (hc : 1 ≤ c) (hcL : c ≤ L) :
    pre m B e L (c - 1) = pre m B e L c * 2 ^ 64 + (word m B (e + 8 * (c - 1))).toNat := by
  unfold pre
  rw [show L - (c - 1) = 1 + (L - c) by omega_arith, wv_add]
  simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.zero_add, Nat.one_mul]
  rw [show e + 8 * (c - 1) + 8 * 1 = e + 8 * c by omega_arith]
  grind

theorem pre_zero (m : Mem) (B : Addr) (e L : Nat) : pre m B e L 0 = wv m B e L := by simp [pre]

/-! ## The pieces -/

theorem hOf_val {W : Nat} (hW : 4 ≤ W) (hW' : W < 2 ^ 63) :
    BitVec.ofNat 64 W >>> 1 - 2 = BitVec.ofNat 64 (W / 2 - 2) := by
  rw [shr1_ofNat W (by omega_arith)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (2 : BitVec 64).toNat = 2 from rfl]
  omega_arith

/-- `qLoad`: the window's and the dividend's bases, and the count. -/
theorem qLoad_ok {s : State} {B : Addr} {Z W c : Nat} (h : Ws s B Z W)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) :
    WP isa (.block qLoad) s fun t =>
      t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 W ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2)) ∧
      t.gpr .rbp = off B (slot W qV) ∧ t.gpr .r11 = off B (slot W qA) ∧ t.gpr .rcx = BitVec.ofNat 64 c ∧
      t.mem = s.mem ∧ Keep [.r12, .r9, .rbp, .r11, .rcx] s t := by
  rw [show qLoad = ws ++ ((base qV .rbp ++ base qA .r11) ++ [.mov .rcx (.mem (hdr sCt))]) by
    simp only [qLoad, List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok qV qA (r₁ := .rbp) (r₂ := .r11) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun t₂ ⟨hbp, h11, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  have h256 := h.h256
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 c ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, ((k₁.trans k₂).gpr (by decide) : t₂.gpr .rdi = _), h.rdi, hdrOff,
      hs.ld (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), hm₂, hm₁, hc]) rfl) fun t ⟨⟨hcx, hm⟩, k₃⟩ => ?_
  exact ⟨(((k₁.trans k₂).trans k₃).gpr (by decide)).trans h.rdi,
    ((k₂.trans k₃).gpr (by decide)).trans h12, ((k₂.trans k₃).gpr (by decide)).trans h9,
    (k₃.gpr (by decide)).trans hbp, (k₃.gpr (by decide)).trans h11, hcx, by rw [hm, hm₂, hm₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

theorem ofInt8 : BitVec.ofInt 64 8 = BitVec.ofNat 64 8 := rfl

/-- `qDigit`: the digit `[qA][c - 1]` into the window's word 1; the step's bases and `h`. -/
theorem qDigit_ok {s : State} {B : Addr} {Z W c : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2))) (h12 : s.gpr .r12 = BitVec.ofNat 64 W)
    (hbp : s.gpr .rbp = off B (slot W qV)) (h11 : s.gpr .r11 = off B (slot W qA))
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (hW : 4 ≤ W) (hW' : W < 2 ^ 32) (hAz : slot W qA + 8 * c ≤ Z) (hVz : slot W qV + 16 ≤ Z) :
    WP isa (.block qDigit) s fun t =>
      t.gpr .rbx = off B (slot W qR) ∧ t.gpr .r10 = off B (slot W qD) ∧ t.gpr .r8 = off B (slot W qT) ∧
      t.gpr .rbp = off B (slot W qV) ∧ t.gpr .r12 = BitVec.ofNat 64 (W / 2 - 2) ∧
      t.mem = s.mem.writeW (off B (slot W qV + 8)) (word s.mem B (slot W qA + 8 * (c - 1))) ∧
      Keep [.rcx, .rdx, .rbx, .r10, .r8, .r12] s t := by
  have hn := hs.nowrap
  rw [show qDigit = [.alu .sub .rcx (.imm 1), .mov .rdx (.mem (ix .r11 .rcx)),
      .store { base := .rbp, disp := 8 } .rdx] ++ ((base qR .rbx ++ (base qD .r10 ++ base qT .r8)) ++ hOf) by
    simp only [qDigit, List.append_assoc], WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off B (slot W qV + 8)) (word s.mem B (slot W qA + 8 * (c - 1)))) (by
    xrun [State.ea, ix, hbp, h11, hcx, ofInt8, off_addN, ofNat64_pred hc (by omega_arith),
      addr0 (rfl : off B (slot W qA) = _) (rfl : BitVec.ofNat 64 (c - 1) = _), hs.st (d := slot W qV + 8) (by omega_arith),
      hs.ld (d := slot W qA + 8 * (c - 1)) (by omega_arith)]) rfl) fun t₁ ⟨hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base3_ok qR qD qT (r₁ := .rbx) (r₂ := .r10) (r₃ := .r8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hdi) ((k₁.gpr (by decide)).trans h9) (by decide) (by decide))
    fun t₂ ⟨hbx, h10, h8, hm₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (W / 2 - 2) ∧ t.mem = t₂.mem)
    (by unfold hOf; xrun [((k₁.trans k₂).gpr (by decide) : t₂.gpr .r12 = _), h12, hOf_val hW (by omega_arith)]) rfl)
    fun t ⟨⟨h12', hm₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans hbx, (k₃.gpr (by decide)).trans h10, (k₃.gpr (by decide)).trans h8,
    ((k₁.trans k₂).trans k₃ |>.gpr (by decide)).trans hbp, h12', by rw [hm₃, hm₂, hm₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `qPos`: `rax := c`, `[qQ]`'s base. -/
theorem qPos_ok {s : State} {B : Addr} {Z W c : Nat} (h : Ws s B Z W)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) :
    WP isa (.block qPos) s fun t =>
      t.gpr .rbx = off B (slot W qQ) ∧ t.gpr .rax = BitVec.ofNat 64 c ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .rax] s t := by
  rw [show qPos = ws ++ (base qQ .rbx ++ [.mov .rax (.mem (hdr sCt))]) by simp only [qPos, List.append_assoc],
    WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok qQ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun t₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  have h256 := h.h256
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 c ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, ((k₁.trans k₂).gpr (by decide) : t₂.gpr .rdi = _), h.rdi, hdrOff,
      hs.ld (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), hm₂, hm₁, hc]) rfl) fun t ⟨⟨hax, hm⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans hbx, hax, by rw [hm, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `qStore`'s tail: the digit `rcx + r11` to word `c - 1` of `[qQ]`, the count less one. -/
theorem qTail_ok {s : State} {B : Addr} {Z W c : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hbx : s.gpr .rbx = off B (slot W qQ)) (hax : s.gpr .rax = BitVec.ofNat 64 c) (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (hQz : slot W qQ + 8 * c ≤ Z) (h256 : 256 ≤ Z) :
    WP isa (.block qTail) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      t.mem = (s.mem.writeW (off B (slot W qQ + 8 * (c - 1))) (s.gpr .rcx + s.gpr .r11)).writeW
        (off B (8 * sCt)) (BitVec.ofNat 64 (c - 1)) ∧ Keep [.rcx, .rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (c - 1) ∧
      t.zf = some (decide (c = 1)) ∧
      t.mem = (s.mem.writeW (off B (slot W qQ + 8 * (c - 1))) (s.gpr .rcx + s.gpr .r11)).writeW
        (off B (8 * sCt)) (BitVec.ofNat 64 (c - 1))) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold qTail
  xrun [State.ea, ix, hdr, hdi, hdrOff, hbx, hax, ofNat64_pred hc (by omega_arith),
    addr0 (rfl : off B (slot W qQ) = _) (rfl : BitVec.ofNat 64 (c - 1) = _), hs.st (d := slot W qQ + 8 * (c - 1)) (by omega_arith),
    hs.st (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith),
    ofNat64_beq_zero (show c - 1 < 2 ^ 64 by omega_arith)]
  simp only [show (c - 1 = 0) ↔ c = 1 by omega_arith]

/-! ## A step -/

/-- The arrays of `qDiv e qA qQ qR qD qT qV` at the wide width `W = 2 h + 4`. -/
structure QLay (W h e : Nat) : Prop where
  hW : W = 2 * h + 4
  h8 : 8 ≤ h
  e1 : 1 ≤ e
  e3 : e ≤ 3

/-- The arrays' offsets, linear in `W`. -/
theorem qSlots (W : Nat) : slot W qA = 256 + 9 * (8 * (W + 2)) ∧ slot W qQ = 256 + 11 * (8 * (W + 2)) ∧
    slot W qR = 256 + 12 * (8 * (W + 2)) ∧ slot W qD = 256 + 8 * (8 * (W + 2)) ∧
    slot W qT = 256 + 13 * (8 * (W + 2)) ∧ slot W qV = 256 + 14 * (8 * (W + 2)) ∧
    slot W 16 = 256 + 16 * (8 * (W + 2)) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What a step writes: the step's working space and remainder, the window's
digit, the quotient's word `c - 1` and the count. -/
def qRs (W h c : Nat) : List (Nat × Nat) :=
  [(slot W qT, 8 * (h + 1)), (slot W qR, 8 * h), (slot W qV + 8, 8), (slot W qQ + 8 * (c - 1), 8), (8 * sCt, 8)]

macro "q_sep" : tactic =>
  `(tactic| (
    intro r hr
    simp only [qRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (try simp only) <;> omega_arith))

macro "q_omega" : tactic =>
  `(tactic| ((try simp only [qRs, sCt, sFn, List.mem_cons, List.not_mem_nil, or_false]); omega_arith))

theorem qBody_ok {s : State} {B : Addr} {Z W h e c : Nat} (hw : Ws s B Z W)
    (L : QLay W h e) (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c)
    (hc1 : 1 ≤ c) (hcN : c ≤ h + e)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W qD + 8 * (h - 1))).toNat)
    (hv : (word s.mem B (slot W qV)).toNat = (2 ^ 128 - 1) / (word s.mem B (slot W qD + 8 * (h - 1))).toNat - 2 ^ 64)
    (hx : wv s.mem B (slot W qR) h < wv s.mem B (slot W qD) h) :
    WP isa qBody s fun t =>
      wv t.mem B (slot W qR) h = (wv s.mem B (slot W qR) h * 2 ^ 64 + (word s.mem B (slot W qA + 8 * (c - 1))).toNat) %
        wv s.mem B (slot W qD) h ∧
      (word t.mem B (slot W qQ + 8 * (c - 1))).toNat =
        (wv s.mem B (slot W qR) h * 2 ^ 64 + (word s.mem B (slot W qA + 8 * (c - 1))).toNat) /
          wv s.mem B (slot W qD) h ∧
      word t.mem B (8 * sCt) = BitVec.ofNat 64 (c - 1) ∧
      t.gpr .rax = BitVec.ofNat 64 (c - 1) ∧ t.zf = some (decide (c = 1)) ∧
      Frm B (qRs W h c) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have h256 := hw.h256
  obtain ⟨hW, h8, e1, e3⟩ := L
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots W
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  have hw2 := hw.w2
  unfold qBody
  change WP isa (.seq (.block (qLoad ++ qDigit)) (.seq Impl.Rsa.X86_64.WordReduce.step
    (.block (qPos ++ qTail)))) s _
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (qLoad_ok hw hc)
    fun s₁ ⟨hdi₁, h12₁, h9₁, hbp₁, h11₁, hcx₁, hm₁, k₁⟩ => WP.mono (qDigit_ok
      (hw.scr.congr k₁.2.2) hdi₁ h9₁ h12₁ hbp₁ h11₁ hcx₁ hc1 (by q_omega) (by q_omega) (by q_omega) (by q_omega)
      (by q_omega)) fun s₂ ⟨hbx₂, h10₂, h8₂, hbp₂, h12₂, hm₂, k₂⟩ => ?_))
  rw [hm₁] at hm₂
  have hs₂ := hw.scr.congr (k₁.trans k₂).2.2
  -- The step's inputs, in `s₂`.
  have eh : W / 2 - 2 = h := by omega_arith
  rw [eh] at h12₂
  have wD : ∀ i < h, word s₂.mem B (slot W qD + 8 * i) = word s.mem B (slot W qD + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem B _ (by q_omega)).word (by q_omega) (by q_omega)
  have wR : ∀ i < h, word s₂.mem B (slot W qR + 8 * i) = word s.mem B (slot W qR + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem B _ (by q_omega)).word (by q_omega) (by q_omega)
  have vD : wv s₂.mem B (slot W qD) h = wv s.mem B (slot W qD) h := wv_congr wD
  have vR : wv s₂.mem B (slot W qR) h = wv s.mem B (slot W qR) h := wv_congr wR
  have tD : word s₂.mem B (slot W qD + 8 * (h - 1)) = word s.mem B (slot W qD + 8 * (h - 1)) := wD _ (by omega_arith)
  have rV : word s₂.mem B (slot W qV) = word s.mem B (slot W qV) := by
    rw [hm₂]; exact (writeW_outside s.mem B _ (by q_omega)).word (by q_omega) (by q_omega)
  have dV : word s₂.mem B (slot W qV + 8) = word s.mem B (slot W qA + 8 * (c - 1)) := by
    rw [hm₂, word_writeW_self]
  refine WP.seq (WP.mono (WordReduce.stepQ_ok hs₂ hbx₂ h10₂ h8₂ h12₂ hbp₂ (by omega_arith) (by omega_arith)
    (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega)
    (by rw [tD]; exact hd) (by rw [rV, tD]; exact hv) (by rw [vR, vD]; exact hx))
    fun s₃ ⟨v₃, f₃, k₃, hq₃⟩ => ?_)
  rw [vR, vD, dV] at v₃ hq₃
  have hs₃ := hs₂.congr k₃.2.2
  have hw₂ : Ws s₂ B Z W := hw.congrP (P := fun y => slot W qV + 8 ≤ y ∧ y < slot W qV + 16)
    (by rw [hm₂]; exact FrmP.of_writeW _ (by q_omega) fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => .inl (by omega_arith)) (k₁.trans k₂) (by decide)
  have hw₃ : Ws s₃ B Z W := hw₂.congr f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl (by q_omega)) k₃ (by decide)
  have c₃ : word s₃.mem B (8 * sCt) = BitVec.ofNat 64 c := by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> q_omega) (by q_omega), hm₂]
    rw [(writeW_outside s.mem B _ (by q_omega)).word (by q_omega) (by q_omega), hc]
  rw [WP.block_append_iff]
  refine WP.mono (qPos_ok hw₃ c₃) fun s₄ ⟨hbx₄, hax₄, hm₄, k₄⟩ => ?_
  refine WP.mono (qTail_ok (hs₃.congr k₄.2.2) ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
    (((k₁.trans k₂).gpr (by decide)).trans hw.rdi))) hbx₄ hax₄ hc1 (by q_omega) (by q_omega) (by q_omega))
    fun t ⟨hax, hz, hm, k₅⟩ => ?_
  have hd₄ : s₄.gpr .rcx + s₄.gpr .r11 = s₃.gpr .rcx + s₃.gpr .r11 := by
    rw [k₄.gpr (by decide), k₄.gpr (by decide)]
  rw [hd₄, hm₄] at hm
  refine ⟨?_, ?_, ?_, hax, hz, ?_, ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp [mmRegs])⟩
  · rw [hm, (writeW_outside _ B _ (by q_omega)).wv (Or.inr (by q_omega)) (by q_omega),
      (writeW_outside _ B _ (by q_omega)).wv (by q_omega) (by q_omega)]
    exact v₃
  · rw [hm, (writeW_outside _ B _ (by q_omega)).word (by q_omega) (by q_omega), word_writeW_self]
    exact hq₃
  · rw [hm, word_writeW_self]
  · intro x hx
    rw [hm]
    have a4 := hx (8 * sCt, 8) (by simp [qRs])
    have a1 := hx (slot W qT, 8 * (h + 1)) (by simp [qRs])
    have a2 := hx (slot W qR, 8 * h) (by simp [qRs])
    have a5 := hx (slot W qV + 8, 8) (by simp [qRs])
    have aQ := hx (slot W qQ + 8 * (c - 1), 8) (by simp [qRs])
    rw [writeW_outside _ B _ (by q_omega) x (by simp only at a4; omega_arith),
      writeW_outside _ B _ (by q_omega) x (by simp only at aQ; omega_arith),
      f₃ x (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact a1
        · exact a2), hm₂, writeW_outside _ B _ (by q_omega) x (by simp only at a5; omega_arith)]

/-! ## The loop -/


/-- A region of an array other than the step's writes misses them. -/
theorem qRs_out {W h c j o d k : Nat} (hd : d = slot W j + o) (hW : W = 2 * h + 4) (hc1 : 1 ≤ c)
    (hc : c ≤ h + 3) (hj : j ≠ qT ∧ j ≠ qR ∧ j ≠ qQ) (hjV : j = qV → o + 8 * k ≤ 8)
    (hok : o + 8 * k ≤ 8 * (W + 2)) :
    ∀ r ∈ qRs W h c, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  subst hd
  obtain ⟨hT, hR, hQ⟩ := hj
  have pT := slot_sep (w := W) hT
  have pR := slot_sep (w := W) hR
  have pQ := slot_sep (w := W) hQ
  have s256 : 256 ≤ slot W j := by simp only [slot, hdrBytes]; omega_using []
  intro r hr
  simp only [qRs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simp only; omega_using [pT, hok, hW]
  · simp only; omega_using [pR, hok, hW]
  · simp only
    by_cases e : j = qV
    · subst e; have := hjV rfl; omega_using [this]
    · have pV := slot_sep (w := W) e; omega_using [pV, hok, hW]
  · simp only; omega_using [pQ, hok, hW, hc, hc1]
  · simp only [sCt, sFn]; omega_using [s256]

/-- `qRs_out` for one word. -/
theorem qRs_out1 {W h c j o d : Nat} (hd : d = slot W j + o) (hW : W = 2 * h + 4) (hc1 : 1 ≤ c)
    (hc : c ≤ h + 3) (hj : j ≠ qT ∧ j ≠ qR ∧ j ≠ qQ) (hjV : j = qV → o + 8 ≤ 8)
    (hok : o + 8 ≤ 8 * (W + 2)) :
    ∀ r ∈ qRs W h c, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  have := qRs_out (k := 1) hd hW hc1 hc hj (by simpa using hjV) (by simpa using hok)
  simpa using this


/-- A number whose word `i`, zero before, changed to `V`, and no other. -/
theorem wv_word_set {m m' : Mem} {B : Addr} {d n i V : Nat} (hi : i < n)
    (hz : word m B (d + 8 * i) = 0) (hv : (word m' B (d + 8 * i)).toNat = V)
    (ho : ∀ j < n, j ≠ i → word m' B (d + 8 * j) = word m B (d + 8 * j)) :
    wv m' B d n = wv m B d n + 2 ^ (64 * i) * V := by
  rw [show n = i + (1 + (n - i - 1)) by omega_arith, wv_add, wv_add, wv_add m B d i (1 + (n - i - 1)),
    wv_add m B (d + 8 * i) 1 (n - i - 1)]
  have e1 : wv m' B d i = wv m B d i := wv_congr fun j hj => ho j (by omega_arith) (by omega_arith)
  have e2 : wv m' B (d + 8 * i + 8 * 1) (n - i - 1) = wv m B (d + 8 * i + 8 * 1) (n - i - 1) :=
    wv_congr fun j hj => by
      have := ho (i + 1 + j) (by omega_arith) (by omega_arith)
      rwa [show d + 8 * (i + 1 + j) = d + 8 * i + 8 * 1 + 8 * j by omega_arith] at this
  have e3 : wv m' B (d + 8 * i) 1 = V := by
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add, hv]
  have e4 : wv m B (d + 8 * i) 1 = 0 := by simp only [wv, Nat.mul_zero, Nat.add_zero, hz]; rfl
  rw [e1, e2, e3, e4]
  grind

/-- What the loop writes. -/
def qRsAll (W h : Nat) : List (Nat × Nat) :=
  [(slot W qT, 8 * (h + 1)), (slot W qR, 8 * h), (slot W qV + 8, 8), (slot W qQ, 8 * W), (8 * sCt, 8)]

/-- A number that is a multiple of `2^(64 c)` has its word `c - 1` zero. -/
theorem word_zero_of_mul {m : Mem} {B : Addr} {d n c X : Nat} (hv : wv m B d n = X * 2 ^ (64 * c))
    (hc1 : 1 ≤ c) (hcn : c ≤ n) : word m B (d + 8 * (c - 1)) = 0 := by
  have hs := wv_add m B d c (n - c)
  rw [show c + (n - c) = n by omega_arith, hv] at hs
  have hl := wv_lt m B d c
  have h0 : wv m B d c = 0 := by
    have := congrArg (· % 2 ^ (64 * c)) hs
    simp only [Nat.mul_mod_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl] at this
    exact this.symm
  exact (wv_eq_zero_iff m B d c).mp h0 (c - 1) (by omega_arith)

/-- The loop's invariant with `c` words left. -/
structure QInv (s₀ : State) (B : Addr) (Z W h e M c : Nat) (t : State) : Prop where
  ws : Ws t B Z W
  cnt : word t.mem B (8 * sCt) = BitVec.ofNat 64 c
  top : word t.mem B (slot W qD + 8 * (h - 1)) = word s₀.mem B (slot W qD + 8 * (h - 1))
  recip : word t.mem B (slot W qV) = word s₀.mem B (slot W qV)
  dv : wv t.mem B (slot W qD) h = M
  divd : ∀ j < 2 * h + e - 1, word t.mem B (slot W qA + 8 * j) = word s₀.mem B (slot W qA + 8 * j)
  rem : wv t.mem B (slot W qR) h = pre s₀.mem B (slot W qA) (2 * h + e - 1) c % M
  quo : wv t.mem B (slot W qQ) W = pre s₀.mem B (slot W qA) (2 * h + e - 1) c / M * 2 ^ (64 * c)
  frm : Frm B (qRsAll W h) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

theorem qIter_ok {s₀ t : State} {B : Addr} {Z W h e M c : Nat}
    (L : QLay W h e) (hI : QInv s₀ B Z W h e M c t)
    (hc1 : 1 ≤ c) (hcN : c ≤ h + e) (hMpos : 0 < M)
    (hd : 2 ^ 63 ≤ (word s₀.mem B (slot W qD + 8 * (h - 1))).toNat)
    (hv : (word s₀.mem B (slot W qV)).toNat =
      (2 ^ 128 - 1) / (word s₀.mem B (slot W qD + 8 * (h - 1))).toNat - 2 ^ 64) :
    WP isa qBody t fun t' => QInv s₀ B Z W h e M (c - 1) t' ∧
      t'.gpr .rax = BitVec.ofNat 64 (c - 1) ∧ t'.zf = some (decide (c = 1)) := by
  have hw := hI.ws
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  have L' := L
  obtain ⟨hW, h8, e1, e3⟩ := L'
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots W
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  refine WP.mono (qBody_ok hw L hI.cnt hc1 hcN (by rw [hI.top]; exact hd)
      (by rw [hI.recip, hI.top]; exact hv) (by rw [hI.rem, hI.dv]; exact Nat.mod_lt _ hMpos))
    fun t' ⟨r', q', c', a', z', f', k'⟩ => ⟨?_, a', z'⟩
  rw [hI.dv, hI.rem, hI.divd (c - 1) (by omega_arith)] at r' q'
  have hpre := pre_step s₀.mem B (e := slot W qA) (L := 2 * h + e - 1) (c := c) hc1 (by omega_arith)
  have fo : ∀ {d k : Nat}, (∀ r ∈ qRs W h c, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 8 * k ≤ Z →
      wv t'.mem B d k = wv t.mem B d k := fun hd hz => f'.wv_eq hd (by omega_arith)
  have fw : ∀ {d : Nat}, (∀ r ∈ qRs W h c, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 8 ≤ Z →
      word t'.mem B d = word t.mem B d := fun hd hz => f'.word_eq hd (by omega_arith)
  have hz := word_zero_of_mul hI.quo hc1 (by omega_arith)
  refine ⟨?_, c', ?_, ?_, ?_, ?_, ?_, ?_, ?_, (hI.keep.trans k').mono (by simp [mmRegs])⟩
  · exact hw.congrP (P := fun y => ∃ r ∈ qRs W h c, r.1 ≤ y ∧ y < r.1 + r.2)
      (fun x hx => f' x fun r hr => by
        by_contra cc
        exact hx ⟨r, hr, by omega_arith, by omega_arith⟩)
      (fun y ⟨r, hr, h1, h2⟩ => by
        simp only [qRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        unfold DOk
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only at h1 h2 <;> omega_arith) k' (by decide)
  · rw [fw (qRs_out1 (j := qD) (o := 8 * (h - 1)) rfl hW hc1 (by omega_arith) (by decide)
      (fun e => absurd e (by decide)) (by omega_arith)) (by omega_arith)]
    exact hI.top
  · rw [fw (qRs_out1 (j := qV) (o := 0) (by simp) hW hc1 (by omega_arith) (by decide)
      (fun _ => by omega_arith) (by omega_arith)) (by omega_arith)]
    exact hI.recip
  · rw [fo (qRs_out (j := qD) (o := 0) (by simp) hW hc1 (by omega_arith) (by decide)
      (fun e => absurd e (by decide)) (by omega_arith)) (by omega_arith)]
    exact hI.dv
  · intro j hj
    rw [fw (qRs_out1 (j := qA) (o := 8 * j) rfl hW hc1 (by omega_arith) (by decide)
      (fun e => absurd e (by decide)) (by omega_arith)) (by omega_arith)]
    exact hI.divd j hj
  · rw [r', hpre]; exact (LongDivision.mod_step _ _ _).symm
  · rw [wv_word_set (n := W) (i := c - 1) (by omega_arith) hz q' (fun j hj hne => fw (by
        intro r hr
        simp only [qRs, List.mem_cons, List.not_mem_nil, or_false] at hr
        have pR := slot_sep (w := W) (show qQ ≠ qR by decide)
        have pT := slot_sep (w := W) (show qQ ≠ qT by decide)
        have pV := slot_sep (w := W) (show qQ ≠ qV by decide)
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · simp only; omega_using [pT, hW, hj]
        · simp only; omega_using [pR, hW, hj]
        · simp only; omega_using [pV, hW, hj]
        · simp only; omega_using [hne, hj]
        · simp only [sCt, sFn]; omega_using [sQ]) (by omega_arith)), hI.quo, hpre]
    have ep : 2 ^ (64 * c) = 2 ^ 64 * 2 ^ (64 * (c - 1)) := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    rw [ep, LongDivision.div_step (pre s₀.mem B (slot W qA) (2 * h + e - 1) c)]
    generalize pre s₀.mem B (slot W qA) (2 * h + e - 1) c / M = X
    generalize 2 ^ (64 * (c - 1)) = P
    generalize (_ * 2 ^ 64 + _) / M = D
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm D P]
  · intro x hx
    refine (f' x ?_).trans (hI.frm x hx)
    intro r hr
    simp only [qRs, List.mem_cons, List.not_mem_nil, or_false] at hr
    have x1 := hx (slot W qT, 8 * (h + 1)) (by simp [qRsAll])
    have x2 := hx (slot W qR, 8 * h) (by simp [qRsAll])
    have x3 := hx (slot W qV + 8, 8) (by simp [qRsAll])
    have x4 := hx (slot W qQ, 8 * W) (by simp [qRsAll])
    have x5 := hx (8 * sCt, 8) (by simp [qRsAll])
    simp only at x1 x2 x3 x4 x5
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact x1
    · exact x2
    · exact x3
    · simp only; omega_arith
    · exact x5

/-- The loop: `h + e` steps from the seed. -/
theorem qLoop_ok {s₀ t : State} {B : Addr} {Z W h e M : Nat}
    (L : QLay W h e) (hI : QInv s₀ B Z W h e M (h + e) t) (hMpos : 0 < M)
    (hd : 2 ^ 63 ≤ (word s₀.mem B (slot W qD + 8 * (h - 1))).toNat)
    (hv : (word s₀.mem B (slot W qV)).toNat =
      (2 ^ 128 - 1) / (word s₀.mem B (slot W qD + 8 * (h - 1))).toNat - 2 ^ 64)
    (ha : t.gpr .rax = BitVec.ofNat 64 (h + e)) :
    WP isa (.loop qBody .ne) t fun t' => QInv s₀ B Z W h e M 0 t' := by
  have hw2 := hI.ws.w2
  obtain ⟨hW, h8, e1, e3⟩ := L
  refine wp_countdown (cnt := .rax) (N := h + e) (by omega_arith) (by omega_arith)
    (fun i s => QInv s₀ B Z W h e M (h + e - i) s) ?_ (fun s hs => by simpa using hs) hI ha
  intro i hi s hs hc
  refine WP.mono (qIter_ok ⟨hW, h8, e1, e3⟩ hs (by omega_arith) (by omega_arith) hMpos hd hv)
    fun s' ⟨h1, h2, h3⟩ => ⟨?_, ?_, ?_⟩
  · rwa [show h + e - (i + 1) = h + e - i - 1 by omega_arith]
  · rw [h2, hc, ofNat64_pred (by omega_arith) (by omega_arith)]
  · rw [h3, hc, ofNat64_pred (by omega_arith) (by omega_arith),
      ofNat64_beq_zero (by omega_arith)]
    congr 1; exact decide_eq_decide.mpr (by omega_arith)

/-! ## The setup -/

theorem ofNat_shl3 {a : Nat} (h : 8 * a < 2 ^ 64) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_arith)]
  rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm]

/-- `qSeed`'s registers: the source `[qA] + 8 (h + e)`, and `h - 1` words. -/
theorem qSeedT_ok {s : State} {B : Addr} {W h e : Nat} (L : QLay W h e) (hw2 : W < 2 ^ 24)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 W) (hsi : s.gpr .rsi = off B (slot W qA)) :
    WP isa (.block (hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3,
      .alu .add .rsi (.reg .rax), .alu .sub .r12 (.imm 1)] : List Instr))) s fun t =>
      t.gpr .rsi = off B (slot W qA + 8 * (h + e)) ∧ t.gpr .r12 = BitVec.ofNat 64 (h - 1) ∧ t.mem = s.mem ∧
        Keep [.rsi, .r12, .rax] s t := by
  obtain ⟨hW, h8, e1, e3⟩ := L
  refine WP.mono (WP.keep [.rsi, .r12, .rax] (Q := fun t => t.gpr .rsi = off B (slot W qA + 8 * (h + e)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (h - 1) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨a, k⟩ => ⟨a.1, a.2.1, a.2.2, k⟩
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 e) = BitVec.ofNat 64 e := by
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega_arith
    all_goals decide
  have hh : W / 2 - 2 = h := by omega_arith
  simp only [hOf, List.cons_append, List.nil_append]
  xrun [h12, hsi, hOf_val (W := W) (by omega_arith) (by omega_arith)]
  rw [se, hh, ← BitVec.ofNat_add, ofNat_shl3 (by omega_arith), off_addN,
    ofNat64_pred (by omega_arith) (by omega_arith)]
  exact ⟨rfl, rfl⟩

/-- `qDiv`'s count: `h + e` into the count and `rax`. -/
theorem qCnt_ok {s : State} {B : Addr} {Z W h e : Nat} (hw : Ws s B Z W) (L : QLay W h e) :
    WP isa (.block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)),
      .store (hdr sCt) .rax] : List Instr))) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (h + e) ∧ t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (h + e)) ∧
        Keep [.r12, .r9, .rax] s t := by
  obtain ⟨hW, h8, e1, e3⟩ := L
  have hw2 := hw.w2
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  have hs := hw.scr.congr k₁.2.2
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 e) = BitVec.ofNat 64 e := by
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega_arith
    all_goals decide
  refine WP.mono (WP.keep [.r12, .rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (h + e) ∧
      t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (h + e))) ?_ rfl)
    fun t ⟨a, k⟩ => ⟨a.1, a.2, (k₁.trans k).mono (by simp)⟩
  simp only [hOf, List.cons_append, List.nil_append]
  xrun [h12, State.ea, hdr, (k₁.gpr (by decide) : t₁.gpr .rdi = _), hw.rdi, hdrOff,
    hOf_val (W := W) (by omega_arith) (by omega_arith), hs.st (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), m₁]
  rw [se, show W / 2 - 2 = h by omega_arith, ← BitVec.ofNat_add]
  exact ⟨rfl, rfl⟩

/-- `qDiv`'s reciprocal's registers. -/
theorem qRcp_ok {s : State} {B : Addr} {Z W h e : Nat} (hw : Ws s B Z W) (L : QLay W h e) :
    WP isa (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) s fun t =>
      t.gpr .r10 = off B (slot W qD) ∧ t.gpr .r8 = off B (slot W qV) ∧ t.gpr .r12 = BitVec.ofNat 64 h ∧
        t.mem = s.mem ∧ Keep [.r12, .r9, .r10, .r8] s t := by
  obtain ⟨hW, h8, e1, e3⟩ := L
  have hw2 := hw.w2
  rw [show ws ++ base qD .r10 ++ base qV .r8 ++ hOf = ws ++ ((base qD .r10 ++ base qV .r8) ++ hOf) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok qD qV (r₁ := .r10) (r₂ := .r8) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun t₂ ⟨h10, h8', m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 h ∧ t.mem = t₂.mem)
    (by unfold hOf; xrun [((k₂).gpr (by decide) : t₂.gpr .r12 = _), h12, hOf_val (W := W) (by omega_arith) (by omega_arith),
      show W / 2 - 2 = h by omega_arith]) rfl) fun t ⟨⟨h12', m₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans h10, (k₃.gpr (by decide)).trans h8', h12', by rw [m₃, m₂, m₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `qSeed`'s block: the source and destination bases, `h - 1`. -/
theorem qSeedB_ok {s : State} {B : Addr} {Z W h e : Nat} (hw : Ws s B Z W) (L : QLay W h e) :
    WP isa (.block (ws ++ base qA .rsi ++ base qR .rbx ++ hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
      .alu .sub .r12 (.imm 1)] : List Instr))) s fun t =>
      t.gpr .rsi = off B (slot W qA + 8 * (h + e)) ∧ t.gpr .rbx = off B (slot W qR) ∧
        t.gpr .r12 = BitVec.ofNat 64 (h - 1) ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .rsi, .rbx, .rax] s t := by
  rw [show ws ++ base qA .rsi ++ base qR .rbx ++ hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
      .alu .sub .r12 (.imm 1)] : List Instr) = ws ++ ((base qA .rsi ++ base qR .rbx) ++ (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
      .alu .sub .r12 (.imm 1)] : List Instr))) by simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun u₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok qA qR (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun u₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_
  refine WP.mono (qSeedT_ok L hw.w2 ((k₂.gpr (by decide)).trans h12) hsi) fun u₃ ⟨hsi', h12', m₃, k₃⟩ => ?_
  exact ⟨hsi', (k₃.gpr (by decide)).trans hbx, h12', by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The arrays `qDiv` changes, and the count. -/
def qDivRs (W : Nat) : List (Nat × Nat) :=
  [(slot W qQ, 8 * (W + 2)), (slot W qR, 8 * (W + 2)), (slot W qT, 8 * (W + 2)), (slot W qV, 8 * (W + 2)), (8 * sCt, 8)]

/-- `qDiv e`'s setup: the four arrays cleared, the remainder seeded with the
dividend's top `h - 1` words, the reciprocal and the count: the loop's
invariant before its first step. -/
theorem qPre_ok {s : State} {B : Addr} {Z W h e : Nat} (hw : Ws s B Z W) (L : QLay W h e)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W qD + 8 * (h - 1))).toNat) :
    WP isa (seqs [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))]) s fun t =>
      QInv t B Z W h e (wv s.mem B (slot W qD) h) (h + e) t ∧ t.gpr .rax = BitVec.ofNat 64 (h + e) ∧
      word t.mem B (slot W qD + 8 * (h - 1)) = word s.mem B (slot W qD + 8 * (h - 1)) ∧
      (word t.mem B (slot W qV)).toNat =
        (2 ^ 128 - 1) / (word t.mem B (slot W qD + 8 * (h - 1))).toNat - 2 ^ 64 ∧
      wv t.mem B (slot W qA) (2 * h + e - 1) = wv s.mem B (slot W qA) (2 * h + e - 1) ∧
      (∀ j, h - 1 ≤ j → j < W + 2 → word t.mem B (slot W qR + 8 * j) = 0) ∧
      (∀ j, W ≤ j → j < W + 2 → word t.mem B (slot W qQ + 8 * j) = 0) ∧
      Frm B (qDivRs W) s.mem t.mem ∧ Keep mmRegs s t := by
  have L' := L
  obtain ⟨hW, h8, e1, e3⟩ := L'
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots W
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok hw (j := qQ) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := hw.congrO o1 (by omega_arith) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := qR) (by decide)) fun t₂ ⟨z2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by omega_arith) k2 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := qT) (by decide)) fun t₃ ⟨_, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by omega_arith) k3 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₃ (j := qV) (by decide)) fun t₄ ⟨_, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by omega_arith) k4 (by simp)
  -- the seed
  unfold qSeed
  refine WP.seq (WP.seq (WP.mono (qSeedB_ok h₄ L) fun u ⟨hsi, hbx, h12, mu, ku⟩ => ?_))
  have hsu := h₄.scr.congr ku.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hsu.ld (by omega_arith)) (fun i hi => hsu.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t₅ ⟨v5, _, o5, k5⟩ => ?_
  rw [mu] at v5 o5
  have k45 := ku.trans k5
  have h₅ := h₄.congrO o5 (by omega_arith) k45 (by simp)
  -- the words of `[qD]`, unchanged so far
  have topD : word t₅.mem B (slot W qD + 8 * (h - 1)) = word s.mem B (slot W qD + 8 * (h - 1)) := by
    rw [o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
      o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
  -- the reciprocal
  refine WP.seq (WP.seq (WP.mono (qRcp_ok h₅ L) fun u ⟨h10, h8', h12, mu, ku⟩ =>
    WP.mono (R2w.recip_ok (h₅.scr.congr ku.2.2) h10 h12 h8' (w := h) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [mu, topD]; exact hd)) fun t₆ ⟨m6, k6⟩ => ?_))
  rw [mu] at m6
  have k56 := ku.trans k6
  have o6 : Outside B (slot W qV) 8 t₅.mem t₆.mem := by rw [m6]; exact writeW_outside _ _ _ (by omega_arith)
  have h₆ := h₅.congrO o6 (by omega_arith) k56 (by simp)
  -- the count
  refine WP.mono (qCnt_ok h₆ L) fun t₇ ⟨ha, m7, k7⟩ => ?_
  have h₇ := h₆.congrW m7 (by unfold DOk; simp only [sCt, sFn]; omega_arith) (by decide) k7 (by simp)
  have o7 : Outside B (8 * sCt) 8 t₆.mem t₇.mem := by rw [m7]; exact writeW_outside _ _ _ (by omega_arith)
  -- below `[qQ]`, nothing changed
  have back : ∀ d, 256 ≤ d → d + 8 ≤ slot W qQ → word t₇.mem B d = word s.mem B d := fun d h1 h2 => by
    rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith),
      o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
      o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
  have backV : ∀ d k, 256 ≤ d → d + 8 * k ≤ slot W qQ → wv t₇.mem B d k = wv s.mem B d k := fun d k h1 h2 =>
    wv_congr fun i hi => back _ (by omega_arith) (by omega_arith)
  have top₇ : word t₇.mem B (slot W qD + 8 * (h - 1)) = word s.mem B (slot W qD + 8 * (h - 1)) :=
    back _ (by omega_arith) (by omega_arith)
  have dv₇ : wv t₇.mem B (slot W qD) h = wv s.mem B (slot W qD) h := backV _ _ (by omega_arith) (by omega_arith)
  have A₇ : wv t₇.mem B (slot W qA) (2 * h + e - 1) = wv s.mem B (slot W qA) (2 * h + e - 1) :=
    backV _ _ (by omega_arith) (by omega_arith)
  -- the seed: the dividend's top `h - 1` words, below `M`
  have seed : wv t₇.mem B (slot W qR) h = wv t₇.mem B (slot W qA + 8 * (h + e)) (h - 1) := by
    have zw : word t₇.mem B (slot W qR + 8 * (h - 1)) = 0 := by
      rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith),
        o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
        o3.word (by omega_arith) (by omega_arith)]
      exact (wv_eq_zero_iff _ _ _ _).mp z2 (h - 1) (by omega_arith)
    have lo : wv t₇.mem B (slot W qR) (h - 1) = wv t₅.mem B (slot W qR) (h - 1) := by
      rw [o7.wv (by omega_arith) (by omega_arith), o6.wv (by omega_arith) (by omega_arith)]
    have src : wv t₇.mem B (slot W qA + 8 * (h + e)) (h - 1) = wv t₄.mem B (slot W qA + 8 * (h + e)) (h - 1) := by
      rw [backV _ _ (by omega_arith) (by omega_arith), o4.wv (by omega_arith) (by omega_arith),
        o3.wv (by omega_arith) (by omega_arith), o2.wv (by omega_arith) (by omega_arith),
        o1.wv (by omega_arith) (by omega_arith)]
    have sp := wv_add t₇.mem B (slot W qR) (h - 1) 1
    rw [show h - 1 + 1 = h by omega_arith] at sp
    rw [sp, lo, v5, ← src]
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, zw]
    rfl
  have Mge : 2 ^ (64 * (h - 1)) ≤ wv s.mem B (slot W qD) h := by
    have := wv_add s.mem B (slot W qD) (h - 1) 1
    rw [show h - 1 + 1 = h by omega_arith] at this
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at this
    have hp := Nat.two_pow_pos (64 * (h - 1))
    have : 2 ^ (64 * (h - 1)) * 1 ≤ 2 ^ (64 * (h - 1)) * (word s.mem B (slot W qD + 8 * (h - 1))).toNat :=
      Nat.mul_le_mul_left _ (by omega_arith)
    omega_arith
  have pre₇ : pre t₇.mem B (slot W qA) (2 * h + e - 1) (h + e) = wv t₇.mem B (slot W qA + 8 * (h + e)) (h - 1) := by
    unfold pre; rw [show 2 * h + e - 1 - (h + e) = h - 1 by omega_arith]
  have preLt : pre t₇.mem B (slot W qA) (2 * h + e - 1) (h + e) < wv s.mem B (slot W qD) h :=
    pre₇ ▸ Nat.lt_of_lt_of_le (wv_lt _ _ _ _) Mge
  have qz : wv t₇.mem B (slot W qQ) W = 0 := by
    rw [o7.wv (by omega_arith) (by omega_arith), o6.wv (by omega_arith) (by omega_arith),
      o5.wv (by omega_arith) (by omega_arith), o4.wv (by omega_arith) (by omega_arith),
      o3.wv (by omega_arith) (by omega_arith), o2.wv (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => (wv_eq_zero_iff _ _ _ _).mp z1 q (by omega_arith)
  have rcp : word t₇.mem B (slot W qV) = BitVec.ofNat 64
      ((2 ^ 128 - 1) / (word s.mem B (slot W qD + 8 * (h - 1))).toNat - 2 ^ 64) := by
    rw [o7.word (by omega_arith) (by omega_arith), m6, word_writeW_self, topD]
  refine ⟨⟨h₇, by rw [m7, word_writeW_self], rfl, rfl, dv₇, fun _ _ => rfl, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩,
    ha, top₇, ?_, A₇, fun j h1 h2 => ?_, fun j h1 h2 => ?_, ?_, ?_⟩
  · rw [seed, ← pre₇, Nat.mod_eq_of_lt preLt]
  · rw [qz, Nat.div_eq_of_lt preLt, Nat.zero_mul]
  · rw [rcp, top₇, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (WordDivide.reciprocal_lt hd)]
  · rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith),
      o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
      o3.word (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mp z2 j (by omega_arith)
  · rw [o7.word (by omega_arith) (by omega_arith), o6.word (by omega_arith) (by omega_arith),
      o5.word (by omega_arith) (by omega_arith), o4.word (by omega_arith) (by omega_arith),
      o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mp z1 j (by omega_arith)
  · have sub : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∃ r ∈ qDivRs W, r.1 ≤ o ∧ o + n ≤ r.1 + r.2) →
        Frm B (qDivRs W) m m' := fun ho hc =>
      WordDivide.cover (Frm.of_outside ho (List.mem_singleton_self _)) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hc
    refine (((((((sub o1 ?_).trans (sub o2 ?_)).trans (sub o3 ?_)).trans (sub o4 ?_)).trans (sub o5 ?_)).trans
      (sub o6 ?_)).trans (sub o7 ?_))
    · exact ⟨(slot W qQ, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot W qR, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot W qT, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot W qV, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(slot W qR, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, by simp only; omega_arith⟩
    · exact ⟨(slot W qV, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, by simp only; omega_arith⟩
    · exact ⟨(8 * sCt, 8), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩
  · exact ((((((k1.trans k2).trans k3).trans k4).trans k45).trans k56).trans k7).mono (by simp [mmRegs])

/-- `qDiv e`: `[qQ] := A / M` and `[qR] := A mod M` over their `W + 2` words,
for the dividend `A` of `2 h + e - 1` words of `[qA]` and the normalized
divisor `M` of `h` words of `[qD]`. -/
theorem qDiv_ok {s : State} {B : Addr} {Z W h e : Nat} (hw : Ws s B Z W) (L : QLay W h e)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W qD + 8 * (h - 1))).toNat) :
    WP isa (seqs (qDiv e)) s fun t =>
      wv t.mem B (slot W qR) (W + 2) = wv s.mem B (slot W qA) (2 * h + e - 1) % wv s.mem B (slot W qD) h ∧
      wv t.mem B (slot W qQ) (W + 2) = wv s.mem B (slot W qA) (2 * h + e - 1) / wv s.mem B (slot W qD) h ∧
      Ws t B Z W ∧ Frm B (qDivRs W) s.mem t.mem ∧ Keep mmRegs s t := by
  have L' := L
  obtain ⟨hW, h8, e1, e3⟩ := L'
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots W
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  have hMpos : 0 < wv s.mem B (slot W qD) h := by
    have := wv_add s.mem B (slot W qD) (h - 1) 1
    rw [show h - 1 + 1 = h by omega_arith] at this
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at this
    have hp := Nat.two_pow_pos (64 * (h - 1))
    have : 0 < 2 ^ (64 * (h - 1)) * (word s.mem B (slot W qD + 8 * (h - 1))).toNat :=
      Nat.mul_pos hp (by omega_arith)
    omega_arith
  refine wp_seqs_append (a := [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))]) (b := [.loop qBody .ne]) (by simp) (by simp) ?_
  refine WP.mono (qPre_ok hw L hd) fun t₀ ⟨hI, ha, top₀, rcp₀, A₀, zR, zQ, f₀, k₀⟩ => ?_
  simp only [seqs]
  refine WP.mono (qLoop_ok L hI hMpos (by rw [top₀]; exact hd) rcp₀ ha) fun t hJ => ?_
  have fl := hJ.frm
  have far : ∀ j, (∀ r ∈ qRsAll W h, j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ j) → j + 8 ≤ Z → word t.mem B j = word t₀.mem B j :=
    fun j h1 h2 => fl.word_eq h1 (by omega_arith)
  have hiR : wv t.mem B (slot W qR + 8 * h) (W + 2 - h) = 0 := by
    apply wv_zero
    intro k hk
    rw [far _ (by
      intro r hr
      simp only [qRsAll, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [sCt, sFn] <;> omega_arith) (by omega_arith),
      show slot W qR + 8 * h + 8 * k = slot W qR + 8 * (h + k) by omega_arith]
    exact zR _ (by omega_arith) (by omega_arith)
  have hiQ : wv t.mem B (slot W qQ + 8 * W) 2 = 0 := by
    apply wv_zero
    intro k hk
    rw [far _ (by
      intro r hr
      simp only [qRsAll, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [sCt, sFn] <;> omega_arith) (by omega_arith),
      show slot W qQ + 8 * W + 8 * k = slot W qQ + 8 * (W + k) by omega_arith]
    exact zQ _ (by omega_arith) (by omega_arith)
  have eA : pre t₀.mem B (slot W qA) (2 * h + e - 1) 0 = wv s.mem B (slot W qA) (2 * h + e - 1) := by
    rw [pre_zero, A₀]
  refine ⟨?_, ?_, hJ.ws, ?_, (k₀.trans hJ.keep).mono (by simp [mmRegs])⟩
  · have sp := wv_add t.mem B (slot W qR) h (W + 2 - h)
    rw [show h + (W + 2 - h) = W + 2 by omega_arith, hiR, Nat.mul_zero, Nat.add_zero] at sp
    rw [sp, hJ.rem, eA, Nat.add_zero]
  · have sp := wv_add t.mem B (slot W qQ) W 2
    rw [hiQ, Nat.mul_zero, Nat.add_zero] at sp
    rw [sp, hJ.quo, eA, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  · refine f₀.trans (WordDivide.cover fl fun r hr => ?_)
    simp only [qRsAll, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(slot W qT, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, by simp only; omega_arith⟩
    · exact ⟨(slot W qR, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, by simp only; omega_arith⟩
    · exact ⟨(slot W qV, 8 * (W + 2)), by simp [qDivRs], by simp only; omega_arith, by simp only; omega_arith⟩
    · exact ⟨(slot W qQ, 8 * (W + 2)), by simp [qDivRs], Nat.le_refl _, by simp only; omega_arith⟩
    · exact ⟨(8 * sCt, 8), by simp [qDivRs], Nat.le_refl _, Nat.le_refl _⟩

end VG.Proof.Rsa.X86_64.Rd
