module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecKdk
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: a block of IRPRF

The blocks of `prfBody` that set registers and the counter, and one block of
IRPRF (`prfBody_ok`): `HMAC(KDK, I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2))` to
`scratch + dst + 32 i`, the counter `i` in its slot advanced.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)

/-- Slot `d` of our frame. -/
abbrev sl (s t : State) (d : Nat) : BitVec 64 := t.mem.readW (fb s + BitVec.ofNat 64 d) 64

section
variable {s : State} {R : BitVec 64} {EM : List Byte}

theorem prfHead_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block (fp :: scr .r9 sMsg ++ ([.load .d .r11 .r12 oI, .load .d .r8 .r12 oK] : List Instr))) t
      fun u => (u.mem = t.mem ∧ u.gpr .r9 = scA s sMsg ∧ u.gpr .r11 = sl s t oI ∧ u.gpr .r8 = s.gpr .r7) ∧
        Keep [.r12, .r9, .r11, .r8] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have c3 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c4 : sMsg < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oI) (by decide) (by decide)
  have i3 := slot_rd hc (d := oK) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, i1, i2, i3, hc.sl.scr, hc.sl.k,
    exec_addi (show Reg.r9 ≠ .r0 by decide) c4]

theorem prfUpdArgs_ok {t : State} (hc : Post s R EM t) {n : Nat} (hn : n < 2 ^ 15) :
    WP isa (.block (prfUpdArgs n)) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = BitVec.ofNat 64 64 ∧ u.gpr .r5 = scA s sMsg ∧ u.gpr .r6 = BitVec.ofNat 64 n ∧
      u.gpr .r7 = scA s sWork) ∧ Keep [.r12, .r3, .r4, .r5, .r6, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : sSt < 2 ^ 15 := by decide
  have c3 : sMsg < 2 ^ 15 := by decide
  have c4 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold prfUpdArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, hn, i1, hc.sl.scr, exec_addi (show Reg.r3 ≠ .r0 by decide) c2,
    exec_addi (show Reg.r5 ≠ .r0 by decide) c3, exec_addi (show Reg.r7 ≠ .r0 by decide) c4]

theorem prfFinArgs_ok {t : State} (hc : Post s R EM t) {n dst : Nat} (hn : 64 + n < 2 ^ 15) (hd : dst < 2 ^ 15) :
    WP isa (.block (prfFinArgs n dst)) t fun u => (u.mem = t.mem ∧ u.gpr .r3 = scA s sSt ∧
      u.gpr .r4 = scA s sOuter ∧ u.gpr .r5 = BitVec.ofNat 64 (64 + n) ∧
      u.gpr .r6 = (sl s t oI <<< 5) + scA s dst ∧ u.gpr .r7 = scA s sWork) ∧
      Keep [.r12, .r3, .r4, .r5, .r6, .r10, .r7] t u := by
  have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
  have c2 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have c3 : sSt < 2 ^ 15 := by decide
  have c4 : sOuter < 2 ^ 15 := by decide
  have c5 : sWork < 2 ^ 15 := by decide
  have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
  have i2 := slot_rd hc (d := oI) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold prfFinArgs scr
  prun [fp, exec_addSp0, hc.sp, c1, c2, c3, c4, c5, hn, hd, i1, i2, hc.sl.scr,
    exec_addi (show Reg.r3 ≠ .r0 by decide) c3, exec_addi (show Reg.r4 ≠ .r0 by decide) c4,
    exec_addi (show Reg.r10 ≠ .r0 by decide) hd, exec_addi (show Reg.r7 ≠ .r0 by decide) c5]

theorem incrCL_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block (incr [.li .r9 8])) t fun u =>
      (u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s t oI + 1) ∧
        u.gpr .r9 = BitVec.ofNat 64 8 - (sl s t oI + 1)) ∧ Keep [.r12, .r11, .r9] t u := by
  have c2 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have i2 := slot_rd hc (d := oI) (by decide) (by decide)
  have o2 := slotOut (u := t) hc.wr (d := oI) (by decide) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold incr
  prun [fp, exec_addSp0, hc.sp, c2, i2, o2, exec_addi (show Reg.r11 ≠ .r0 by decide) (show 1 < 2 ^ 15 by decide)]
  exact ⟨rfl, rfl⟩

theorem incrAM_ok {t : State} (hc : Post s R EM t) :
    WP isa (.block (incr [.load .d .r9 .r12 oNB])) t fun u =>
      (u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s t oI + 1) ∧
        u.gpr .r9 = sl s t oNB - (sl s t oI + 1)) ∧ Keep [.r12, .r11, .r9] t u := by
  have c2 : oI < 2 ^ 15 ∧ oI % 4 = 0 := by decide
  have c3 : oNB < 2 ^ 15 ∧ oNB % 4 = 0 := by decide
  have i2 := slot_rd hc (d := oI) (by decide) (by decide)
  have i3 := slot_rd hc (d := oNB) (by decide) (by decide)
  have o2 := slotOut (u := t) hc.wr (d := oI) (by decide) (by decide)
  have e : ∀ v : BitVec 64, (t.mem.writeW (fb s + BitVec.ofNat 64 oI) v).readW (fb s + BitVec.ofNat 64 oNB) 64 =
      sl s t oNB := fun v =>
    Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold incr
  prun [fp, exec_addSp0, hc.sp, c2, c3, i2, i3, o2, e,
    exec_addi (show Reg.r11 ≠ .r0 by decide) (show 1 < 2 ^ 15 by decide)]
  exact ⟨rfl, rfl⟩

end

/-- A slot of our frame stays through a call working in `scratch`, on the
stack below the frame. -/
theorem slot_call {s : State} (h : DPre s) {m m' : Mem} {ws : List Region} {n : Nat}
    (hn : n ≤ Impl.Rsa.PPC64LE.Priv.frameBytes) (hf : Frame (ws ++ [below (fb s) n]) m m')
    (hs : ∀ r ∈ ws, Region.Sub r (SC s)) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    m'.readW (fb s + BitVec.ofNat 64 d) 64 = m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ((h.ks.sub_left (frame_sub s hd)).sub_right (sc_sub h)).sub_right (hs r hr)
    · rw [List.mem_singleton.mp hr]; exact (fr_low s hd).sub_right (low_sub s hn)) (by decide)

/-- After block `i` of IRPRF from `t`: the block `blk` at `scratch + o`, the
counter advanced, the blocks left in `r9` (from `C`), and every other range
of `scratch` from 1040 on as in `t`. -/
structure PrfStep (s : State) (R : BitVec 64) (EM : List Byte) (nbv : BitVec 64) (o : Nat) (blk : List Byte)
    (C : BitVec 64) (i : Nat) (t w : State) : Prop where
  post : Post s R EM w
  ctr : sl s w oI = BitVec.ofNat 64 (i + 1)
  nb : sl s w oNB = nbv
  out : Spec.Rsa.bytesAt w.mem (scA s o) 32 = blk
  r9 : w.gpr .r9 = C - BitVec.ofNat 64 (i + 1)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + 32 ≤ a) →
    Spec.Rsa.bytesAt w.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l

theorem shl5 (i dst : Nat) (scr : Addr) :
    (BitVec.ofNat 64 i <<< 5) + (scr + BitVec.ofNat 64 dst) = scr + BitVec.ofNat 64 (dst + 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

theorem prfBody_ok {label : List Nat} {len count : List Instr} {dst : Nat} {t : State} {i : Nat}
    {kd text : List Byte} {nbv C : BitVec 64} (hc : Post s R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd) (hctr : sl s t oI = BitVec.ofNat 64 i)
    (hnb : sl s t oNB = nbv) (hi : i < 256) (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes)
    (hdst : dst < 2 ^ 15) (hn : label.length + 4 ≤ 16) (htl : text.length = label.length + 4)
    (hmsg : ∀ u, Post s R EM u → u.gpr .r9 = scA s sMsg → u.gpr .r11 = BitVec.ofNat 64 i →
      u.gpr .r8 = s.gpr .r7 → WP isa (.block (msgBytes label len)) u fun w =>
        (Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧
          Spec.Rsa.bytesAt w.mem (scA s sMsg) (label.length + 4) = text) ∧ Keep [.r10] u w)
    (hcount : ∀ u, Post s R EM u → sl s u oNB = nbv → WP isa (.block (incr count)) u fun w =>
      (w.mem = u.mem.writeW (fb s + BitVec.ofNat 64 oI) (sl s u oI + 1) ∧
        w.gpr .r9 = C - (sl s u oI + 1)) ∧ Keep [.r12, .r11, .r9] u w) :
    WP isa (prfBody label len dst count) t
      (PrfStep s R EM nbv (dst + 32 * i) (Spec.Hmac.hmac Spec.Hmac.sha256 kd text) C i t) := by
  have e₁ : H.S = 96 := rfl
  have e₂ : H.W = 160 := rfl
  have e₃ : H.D = 32 := rfl
  have e₄ : H.FD = 32 := rfl
  -- The message.
  refine WP.seq (WP.mono (prfHead_ok hc) fun t₁ ⟨⟨m₁, x9, x11, x8⟩, k₁⟩ => ?_)
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  rw [hctr] at x11
  refine WP.seq (WP.mono (hmsg t₁ hc₁ x9 x11 x8) fun t₂ ⟨⟨F₂, hm₂⟩, k₂'⟩ => ?_)
  have hc₂ : Post s R EM t₂ := hc₁.step h k₂'.rd k₂'.wr k₂'.sp (fun r hr => k₂'.gpr r (by revert r; decide)) F₂
    fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))
  have k₂ : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₂.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l := fun a l h₁ h₂ => by
    rw [bytes_frame F₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD h (.inr (by unfold sMsg; omega)) h₂ (by decide))
      (by unfold scrBytes at h₂; omega), m₁]
  have sl₂ : ∀ d, d + 8 ≤ frameBytes → sl s t₂ d = sl s t d := fun d hd => by
    show t₂.mem.readW _ 64 = t.mem.readW _ 64
    rw [F₂.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ((h.ks.sub_left (frame_sub s hd)).sub_right (sc_sub h)).sub_right (scSub (by decide))) (by decide), m₁]
  -- HMAC's `init` with `KDK`.
  refine WP.seq (WP.mono (macInitArgs_ok hc₂ (key := sKDK) (by decide)) fun t₃ ⟨⟨m₃, y3, y4, y5, y6, y7⟩, k₃⟩ => ?_)
  have hc₃ : Post s R EM t₃ := hc₂.regs k₃.rd k₃.wr k₃.sp m₃ fun r hr => k₃.gpr r (by revert r; decide)
  refine WP.seq (macInit_call h hc₃ (by decide) (by decide) y3 y4 y5 y6 y7 fun u hu hI hO hfu => ?_)
  have hkd₃ : Spec.Sha256.bytesAt t₃.mem (scA s sKDK) 32 = kd := by
    show Spec.Rsa.bytesAt _ _ _ = _
    rw [m₃, k₂ _ _ (by decide) (by decide), hkd]
  rw [hkd₃] at hI hO
  have hk0 : (Spec.Hmac.blockKey hH.SH.H kd).length = 64 :=
    blockKey_length (by rw [← hkd]; simp [Spec.Rsa.bytesAt])
  have ku : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt u.mem (scA s a) l = Spec.Rsa.bytesAt t₃.mem (scA s a) l := fun a l h₁ h₂ =>
    keep_call h (by decide) hfu h₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scD h (.inr (by unfold sSt sOuter sWork at *; omega)) h₂ (by decide)
  have slu : ∀ d, d + 8 ≤ frameBytes → sl s u d = sl s t₃ d := fun d hd =>
    slot_call h (by decide) hfu (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scSub (by decide)) hd
  -- `update` with the message.
  refine WP.seq (WP.mono (prfUpdArgs_ok hu (n := label.length + 4) (by omega))
    fun t₄ ⟨⟨m₄, z3, z4, z5, z6, z7⟩, k₄⟩ => ?_)
  have hc₄ : Post s R EM t₄ := hu.regs k₄.rd k₄.wr k₄.sp m₄ fun r hr => k₄.gpr r (by revert r; decide)
  have hmsg₄ : Spec.Rsa.bytesAt t₄.mem (scA s sMsg) (label.length + 4) = text := by
    rw [m₄, keep_call h (by decide) hfu (by unfold sMsg scrBytes; omega) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide)),
      m₃, hm₂]
  refine WP.seq (upd_call h hc₄ (len := label.length + 4) z3 z5 (by rw [z6, BitVec.toNat_ofNat]; omega) z7
    (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
    (scD h (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
    (lowD h (by decide) (by unfold sMsg scrBytes; omega)) (scCovR h hc₄.wr (by unfold sMsg scrBytes; omega))
    fun t₅ hc₅ hI₅ hf₅ => ?_)
  have hI₅' := hI₅ _ (by rw [m₄]; exact hI) (by rw [z4, Proof.RsaPkcs1Enc.PPC64LE.Dec.xorPad_length, hk0])
  rw [hmsg₄] at hI₅'
  have hO₅ : hH.SH.Repr t₅.mem (scA s sOuter) (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H kd) Spec.Hmac.opad) := by
    refine hH.repr_keep hf₅ (by rw [xorPad_length, hk0]; rfl) (fun r hr => ?_) (by rw [m₄]; exact hO)
    simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact scD h (by decide) (by decide) (by decide)
    · exact scD h (by decide) (by decide) (by decide)
    · exact (lowD h (by decide) (by decide)).symm
  have k₅ : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₅.mem (scA s a) l = Spec.Rsa.bytesAt t₄.mem (scA s a) l := fun a l h₁ h₂ =>
    keep_call h (by decide) hf₅ h₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact scD h (.inr (by unfold sSt sWork at *; omega)) h₂ (by decide)
  have sl₅ : ∀ d, d + 8 ≤ frameBytes → sl s t₅ d = sl s t₄ d := fun d hd =>
    slot_call h (by decide) hf₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact scSub (by decide)) hd
  have ct₅ : sl s t₅ oI = BitVec.ofNat 64 i := by
    rw [sl₅ _ (by decide)]; show t₄.mem.readW _ 64 = _
    rw [m₄]; refine (slu _ (by decide)).trans ?_; show t₃.mem.readW _ 64 = _
    rw [m₃]; exact (sl₂ _ (by decide)).trans hctr
  -- HMAC's `finalize` to the block.
  refine WP.seq (WP.mono (prfFinArgs_ok hc₅ (n := label.length + 4) (dst := dst) (by omega) hdst)
    fun t₆ ⟨⟨m₆, w3, w4, w5, w6, w7⟩, k₆⟩ => ?_)
  have hc₆ : Post s R EM t₆ := hc₅.regs k₆.rd k₆.wr k₆.sp m₆ fun r hr => k₆.gpr r (by revert r; decide)
  rw [ct₅, shl5 i dst] at w6
  refine WP.seq (macFin_call h hc₆ (o := dst + 32 * i) (by omega) hd2 w3 w4 w6 w7 fun t₇ hc₇ hmac hf₇ => ?_)
  have hb₇ := hmac _ text hk0 (by rw [hk0, htl]; omega) (by rw [m₆]; exact hI₅') (by rw [w5, htl])
    (by rw [m₆]; exact hO₅)
  have k₇ : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes → (a + l ≤ dst + 32 * i ∨ dst + 32 * i + 32 ≤ a) →
      Spec.Rsa.bytesAt t₇.mem (scA s a) l = Spec.Rsa.bytesAt t₆.mem (scA s a) l := fun a l h₁ h₂ h₃ =>
    keep_call h (by decide) hf₇ h₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scD h (.inr (by unfold sSt at *; omega)) h₂ (by decide)
      · exact scD h (h₃.imp id fun h' => by rw [e₃]; omega) h₂ hd2
      · exact scD h (.inr (by unfold sWork at *; omega)) h₂ (by decide)
  have sl₇ : ∀ d, d + 8 ≤ frameBytes → sl s t₇ d = sl s t₆ d := fun d hd =>
    slot_call h (by decide) hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scSub (by decide)
      · exact scSub hd2
      · exact scSub (by decide)) hd
  -- The counter.
  have nb₇ : sl s t₇ oNB = nbv := by
    rw [sl₇ _ (by decide)]; show t₆.mem.readW _ 64 = _
    rw [m₆]; refine (sl₅ _ (by decide)).trans ?_; show t₄.mem.readW _ 64 = _
    rw [m₄]; refine (slu _ (by decide)).trans ?_; show t₃.mem.readW _ 64 = _
    rw [m₃]; exact (sl₂ _ (by decide)).trans hnb
  have ct₇ : sl s t₇ oI = BitVec.ofNat 64 i := by
    rw [sl₇ _ (by decide)]; show t₆.mem.readW _ 64 = _
    rw [m₆]; exact ct₅
  refine WP.mono (hcount t₇ hc₇ nb₇) fun w ⟨⟨mw, xw⟩, kw⟩ => ?_
  have Fw : Frame [⟨fb s + BitVec.ofNat 64 oI, 8⟩] t₇.mem w.mem := by
    rw [mw]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcw := hc₇.step h kw.rd kw.wr kw.sp (fun r hr => kw.gpr r (by revert r; decide)) Fw
    fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, show oI + 8 ≤ oLr by decide, rfl⟩)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have kw' : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt w.mem (scA s a) l = Spec.Rsa.bytesAt t₇.mem (scA s a) l := fun a l h₂ =>
    bytes_frame Fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (((h.ks.sub_left (frame_sub s (by decide))).sub_right (sc_sub h)).sub_right (scSub h₂)).symm)
      (by unfold scrBytes at h₂; omega)
  refine ⟨hcw, ?_, ?_, ?_, ?_, fun a l h₁ h₂ h₃ => ?_⟩
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_self64, ct₇, one]
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact nb₇
  · rw [kw' _ _ hd2]; exact hb₇
  · rw [xw, ct₇, one]
  · rw [kw' _ _ h₂, k₇ _ _ h₁ h₂ h₃, m₆, k₅ _ _ h₁ h₂, m₄, ku _ _ h₁ h₂, m₃, k₂ _ _ h₁ h₂]

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
