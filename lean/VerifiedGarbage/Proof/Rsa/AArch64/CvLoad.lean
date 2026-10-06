import VerifiedGarbage.Proof.Rsa.AArch64.CvHead

/-!
# `vg_rsa_crt_values` on AArch64: what the pieces keep, and the masks

`CvS`: what every piece of `main` keeps (the working space, the arguments,
the inputs' bytes, and memory outside the working space), from a frame of
ranges `Mut` allows (`CvS.step`). The pieces that compare arrays and and
masks into `sMask` (`eqA_ok`, `andZero_ok`, `andOdd_ok`), and that set and
decrement words (`setOneA_ok`, `decA_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The inputs of `vg_rsa_crt_values` and where they are. -/
structure CvIn where
  B : Addr
  Z : Nat
  k : Nat
  pl : Nat
  ql : Nat
  dl : Nat
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pN : Addr
  pP : Addr
  pQ : Addr
  pD : Addr
  nb : List Byte
  pb : List Byte
  qb : List Byte
  db : List Byte
  W : List Region

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure CvS (I : CvIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z (wk I.k)
  args : CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem
  wr : s.wr = I.W

theorem CvS.step {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {rs : List (Nat × Nat)}
    (hf : Frm I.B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CvS I m₀ t :=
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf hz
  ⟨h.ws.congr hf hm k hr, h.args.congr (argSlot_frm hf hm), h.n.congrK hi k, h.p.congrK hi k, h.q.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr⟩

/-- `CvS` after a piece that changes only array `j`'s first `n` bytes. -/
theorem CvS.arr {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (wk I.k + 2)) (ho : Outside I.B (slot (wk I.k) j) n s.mem t.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : .x0 ∉ regs) : CvS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega) k hr

/-! ## Masks -/

/-- `eqA a b`: `x9 = 0` iff `[a] = [b]` over `w` words. -/
theorem eqA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqA a b)) s fun t =>
      (t.gpr .x9 = 0 ↔ wv s.mem B (slot w a) w = wv s.mem B (slot w b) w) ∧ t.mem = s.mem ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
        Keep [.x11, .x12, .x9, .x14, .x16, .x17, .x3, .x4] s t := by
  have hn := h.scr.nowrap
  have sa := h.sl ha
  have sb := h.sl hb
  simp only [eqA, seqs]
  refine WP.seq (WP.mono (WP.keep [.x11, .x12, .x9, .x14] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x9 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧
      t.mem = s.mem) (by
        have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
          h.scr.ld (by have := h.h256; omega)
        brun [ws, h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sStride < 32 by decide),
          hl sW (by decide), hl sStride (by decide), h.hw, h.hS])
      (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h12, h11, h9, h14, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (base2_ok a b .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.mono (xor_ok (h.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14)
    (by have := h.w1; omega) (by have := h.w2; omega) (by omega) (by omega)) fun t ⟨hv, mt, _, k₃⟩ => ?_
  rw [(k₂.gpr .x9 (by decide)).trans h9, m₂, m₁] at hv
  refine ⟨by rw [hv]; simp, by rw [mt, m₂, m₁], (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12),
    (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans h11), (k12.trans k₃).mono (by simp)⟩

/-- `subs x3, x9, #1`'s carry: no borrow iff `x9 ≠ 0`. -/
theorem lt_one_flag (x : BitVec 64) :
    (!decide (2 ^ 64 ≤ x.toNat + (~~~(BitVec.setWidth 64 1#16 : BitVec 64)).toNat + 1)) = decide (x = 0) := by
  rw [BitVec.toNat_not, show (BitVec.setWidth 64 1#16 : BitVec 64).toNat = 1 from rfl]
  have hx := x.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_le]
  constructor
  · intro hlt; apply BitVec.eq_of_toNat_eq; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · rintro rfl; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega

/-- `andZero`: the mask of `x9 = 0` and'ed into `sMask`. -/
theorem andZero_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c) {z : Prop} [Decidable z] (hz : s.gpr .x9 = 0 ↔ z) :
    WP isa (.block andZero) s fun t =>
      (t.mem = s.mem.writeW (off B (8 * Public.sMask)) (mask (decide z && c)) ∧ t.gpr .x7 = 0) ∧
        Keep [.x3, .x4, .x7, .x15] s t := by
  have hl := h.scr.ld (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega)
  have hst := h.scr.st (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega)
  have e : (!decide (2 ^ 64 ≤ (s.gpr .x9).toNat + (~~~(BitVec.setWidth 64 1#16 : BitVec 64)).toNat + 1)) =
      decide z := (lt_one_flag _).trans (decide_eq_decide.mpr hz)
  refine WP.keep [.x3, .x4, .x7, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  unfold andZero
  brun [borrowMask, h.x0, Bool.toNat_true, csel_mask', e, hdr_enc (show Public.sMask < 32 by decide), hl, hst, hm,
    mask_and']

/-- `andOdd j`: the mask of `[j]` odd and'ed into `sMask`. -/
theorem andOdd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) {c : Bool}
    (hm : word s.mem B (8 * Public.sMask) = mask c) :
    WP isa (.block (andOdd j)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Public.sMask)) (mask (decide (wv s.mem B (slot w j) w % 2 = 1) && c)) ∧
        Keep [.x11, .x12, .x16, .x3, .x4, .x7, .x15] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hst := h.scr.st (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega)
  unfold andOdd
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  have h0₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  have e0 : (s.mem.readW (off B (slot w j)) 64).toNat % 2 = wv s.mem B (slot w j) w % 2 := by
    rw [← wv_mod64 s.mem B (slot w j) (n := w) (by have := h.w1; omega), Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Public.sMask))
      (mask (decide (wv s.mem B (slot w j) w % 2 = 1) && c))) (by
    brun [h16, h0₂, oddMask, hdr_enc (show Public.sMask < 32 by decide), hs₂.ld (d := slot w j) (by omega),
      hs₂.ld (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega),
      hs₂.st (d := 8 * Public.sMask) (by have := h.h256; unfold Public.sMask sFn; omega), m₂, m₁, hm,
      mask_low', e0, mask_and'])
    rfl rfl rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `setOneA j`: word 0 of `[j]` := 1. -/
theorem setOneA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (setOneA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64) ∧ Keep [.x11, .x12, .x16, .x3] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold setOneA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64)) (by
    brun [h16, hs₂.st (d := slot w j) (by omega), m₂, m₁]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `decA j`: word 0 of `[j]` minus one. -/
theorem decA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (decA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (word s.mem B (slot w j) - 1) ∧ Keep [.x11, .x12, .x16, .x3] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold decA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (word s.mem B (slot w j) - 1)) (by
    brun [h16, hs₂.ld (d := slot w j) (by omega), hs₂.st (d := slot w j) (by omega), m₂, m₁]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

end VG.Proof.Rsa.AArch64
