module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT1
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT3
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecFin
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCT3
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecFin
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time from the mask on

The mask, the alternative length, the scan and the output, by the taint
analysis from the registers correctness fixes; the blocks that load a
pointer from a slot and use it are split there (`rel_split`). With the
earlier parts, the function (`code_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (bitMask)

section
variable {e : Env}

/-- A block split where a pointer it loads is used: the first part's taint
from `rs₁`, the second's from `rs₂`, which `X` fixes. -/
theorem rel_split {P Q X : State → State → Prop} {l₁ l₂ : List Instr} (rs₁ rs₂ : List Reg)
    {hc₁ : VG.Taint.Hint T} (ht₁ : (taint.check (ofRegs rs₁) (.block l₁) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint T} (ht₂ : (taint.check (ofRegs rs₂) (.block l₂) hc₂).isSome = true)
    (hpin₁ : ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs₁ a b) (hpin₂ : ∀ a b, X e.s₁ a → X e.s₂ b → AgreeOn rs₂ a b)
    (hw₁ : ∀ s u, DPre s → P s u → WP isa (.block l₁) u (X s))
    (hw : ∀ s u, DPre s → P s u → WP isa (.block (l₁ ++ l₂)) u (Q s)) :
    RelCT isa (Rel e P) (.block (l₁ ++ l₂)) (Rel e Q) :=
  RelCT.block_append (RelCT.seq
    (rel_step (P' := fun s u => X s u ∧ WP isa (.block l₂) u (Q s)) rs₁ ht₁ hpin₁
      fun s u h hu => WP.and (hw₁ s u h hu) (WP.block_append_iff.mp (hw s u h hu)))
    (rel_step rs₂ ht₂ (fun a b ha hb => hpin₂ a b ha.1 hb.1) fun _ _ _ hu => hu.2))

/-! ## The mask and the alternative length -/

def PM (s u : State) : Prop := PP s u ∧ u.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) ∧
  u.gpr .r8 = BitVec.ofNat 64 0
def PMK (s u : State) : Prop := PP s u ∧ u.gpr .r8 = BitVec.ofNat 64 (bitMask ((s.gpr .r7).toNat - 11)) ∧
  u.gpr .r9 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11)
def PA (s u : State) : Prop := PMK s u ∧ u.gpr .r11 = scA s sCL ∧ u.gpr .r7 = BitVec.ofNat 64 128 ∧
  u.gpr .r6 = BitVec.ofNat 64 0
def PAL (s u : State) : Prop := PP s u ∧ ∃ al, u.gpr .r6 = BitVec.ofNat 64 al

omit e in
theorem k11 {s : State} (h : DPre s) : s.gpr .r7 - BitVec.ofNat 64 11 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 11) := by
  have := h.k1; have := h.k2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem maskPart_ct : RelCT isa (Rel e PP) maskPart (Rel e PMK) := by
  unfold maskPart
  refine RelCT.seq (rel_step (P' := PM) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha hb, fun _ h => nomatch h⟩)
    fun s u h hu => WP.mono (pp_block hu [.r12, .r9, .r8] (X := fun v => v.gpr .r9 = s.gpr .r7 - BitVec.ofNat 64 11 ∧
      v.gpr .r8 = BitVec.ofNat 64 0) fun _ _ hc => by
        have c1 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
        have i1 := slot_rd hc (d := oK) (by decide) (by decide)
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold maskInit
        prun [fp, exec_addSp0, hc.sp, c1, i1, hc.sl.k])
      fun v ⟨hv, _, x9, x8⟩ => ⟨hv, by rw [x9, k11 h], x8⟩) ?_
  refine rel_step [.r8, .r9] (by taint_decide) (fun a b ⟨ha, a9, a8⟩ ⟨hb, b9, b8⟩ => ⟨pp_sp ha hb, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a8, b8]
    · rw [a9, b9, e.r]⟩) fun s u h ⟨⟨R, EM, hu⟩, u9, u8⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  exact WP.mono (maskLoop_ok (x := (s.gpr .r7).toNat - 11) (by omega) (by omega) u8 u9) fun v ⟨vm, kv, v8⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, v8,
      (kv.gpr _ (by decide)).trans u9⟩

theorem alPart_ct : RelCT isa (Rel e PMK) alPart (Rel e PAL) := by
  unfold alPart
  refine RelCT.seq (rel_step (P' := PA) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    fun s u h ⟨hu, u8, u9⟩ => WP.mono (pp_block hu [.r12, .r11, .r7, .r6] (X := fun v => v.gpr .r11 = scA s sCL ∧
      v.gpr .r7 = BitVec.ofNat 64 128 ∧ v.gpr .r6 = BitVec.ofNat 64 0 ∧ v.gpr .r8 = u.gpr .r8 ∧
      v.gpr .r9 = u.gpr .r9) fun _ _ hc => by
        have c1 : oScr < 2 ^ 15 ∧ oScr % 4 = 0 := by decide
        have c2 : sCL < 2 ^ 15 := by decide
        have i1 := slot_rd hc (d := oScr) (by decide) (by decide)
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold alInit scr
        prun [fp, exec_addSp0, hc.sp, c1, c2, i1, hc.sl.scr, exec_addi (show Reg.r11 ≠ .r0 by decide) c2])
      fun v ⟨hv, _, x11, x7, x6, x8, x9⟩ => ⟨⟨hv, by rw [x8, u8], by rw [x9, u9]⟩, x11, x7, x6⟩) ?_
  refine rel_step [.r11, .r7] (by taint_decide) (fun a b ⟨⟨ha, _⟩, a11, a7, _⟩ ⟨⟨hb, _⟩, b11, b7, _⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.scA_eq]
      · rw [a7, b7]⟩) fun s u h ⟨⟨⟨R, EM, hu⟩, u8, u9⟩, u11, u7, u6⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .r7).toNat - 11) (by omega)
  exact WP.mono (alLoop_ok (x := (s.gpr .r7).toNat - 11) (CL := Spec.Rsa.bytesAt u.mem (scA s sCL) 256)
    (by omega) rfl (by omega) (fun i hi => (bytes_getD _ _ hi).symm)
    (fun i hi => by rw [Offset.add_add]; exact scInR h hu.wr (a := sCL + i) (n := 1) (by unfold sCL scrBytes; omega))
    u8 u9 u11 u7 u6) fun v ⟨vm, kv, v6⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, _, v6⟩

/-! ## The scan -/

def PSI (s u : State) : Prop := PAL s u ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
  u.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ u.gpr .r4 = BitVec.ofNat 64 2 ∧ u.gpr .r5 = 0 ∧
  u.gpr .r3 = 0 ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64
def PSC (s u : State) : Prop := PP s u ∧ (∃ al, u.gpr .r6 = BitVec.ofNat 64 al) ∧ (∃ f, u.gpr .r5 = bm f) ∧
  (∃ sep, u.gpr .r3 = BitVec.ofNat 64 sep ∧ sep < 2 ^ 63) ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64

omit e in
theorem k2' {s : State} (h : DPre s) : s.gpr .r7 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) := by
  have := h.k1; have := h.k2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem scanPart_ct : RelCT isa (Rel e PAL) scanPart (Rel e PSC) := by
  unfold scanPart
  refine RelCT.seq (rel_step (P' := PSI) [] (by taint_decide) (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    fun s u h ⟨hu, al, u6⟩ => WP.mono (pp_block hu [.r12, .r11, .r7, .r4, .r5, .r3, .r0, .r8]
      (X := fun v => v.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
        v.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ v.gpr .r4 = BitVec.ofNat 64 2 ∧ v.gpr .r5 = 0 ∧
        v.gpr .r3 = 0 ∧ v.gpr .r0 = 0 ∧ v.gpr .r8 = BitVec.allOnes 64 ∧ v.gpr .r6 = u.gpr .r6) fun _ _ hc => by
        have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
        have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
        have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
        have i2 := slot_rd hc (d := oK) (by decide) (by decide)
        have e7 := k2' h
        refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
        unfold scanInit
        prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, e7,
          exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide),
          exec_subi (show Reg.r7 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide),
          exec_subi (show Reg.r8 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
        exact ⟨rfl, rfl, rfl, by decide⟩)
      fun v ⟨hv, _, x11, x7, x4, x5, x3, x0, x8, x6⟩ => ⟨⟨hv, al, by rw [x6, u6]⟩, x11, x7, x4, x5, x3, x0, x8⟩) ?_
  refine rel_step [.r11, .r7] (by taint_decide) (fun a b ⟨⟨ha, _⟩, a11, a7, _⟩ ⟨⟨hb, _⟩, b11, b7, _⟩ =>
    ⟨pp_sp ha hb, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a7, b7, e.r]⟩) fun s u h ⟨⟨⟨R, EM, hu⟩, al, u6⟩, u11, u7, u4, u5, u3, u0, u8⟩ => ?_
  have hk := h.k1; have hk' := h.k2
  have hs := sep_lt (Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat) (k := (s.gpr .r7).toNat) (by omega)
  exact WP.mono (scanLoop_ok (O := s.gpr .r3) (EM := Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r7).toNat)
    (k := (s.gpr .r7).toNat) (by omega) (by omega) (fun i hi => (bytes_getD' _ _ hi _).symm)
    (fun i hi => outIn h hu hi) u11 u7 u4 u5 u3 u0 u8) fun v ⟨vm, kv, v5, v3⟩ =>
    ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩,
      ⟨al, by rw [kv.gpr _ (by decide), u6]⟩, ⟨_, v5⟩,
      ⟨_, v3, by omega⟩,
      by rw [kv.gpr _ (by decide), u0], by rw [kv.gpr _ (by decide), u8]⟩

/-! ## The output -/

def PV (s u : State) : Prop := PP s u ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧ u.gpr .r12 = fb s ∧
  u.gpr .r0 = 0
def PO (s u : State) : Prop := (∃ R, Fr3 s R u) ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 0 ∧
  u.gpr .r10 = scA s sAM + BitVec.ofNat 64 0 ∧ u.gpr .r7 = s.gpr .r7 ∧ u.gpr .r0 = 0

omit e in
theorem selLoop_run {s : State} (h : DPre s) {R : BitVec 64} {t : State} (hc : Fr3 s R t)
    (h11 : t.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 0) (h10 : t.gpr .r10 = scA s sAM + BitVec.ofNat 64 0)
    (h7 : t.gpr .r7 = s.gpr .r7) (h0 : t.gpr .r0 = 0) : WP isa selLoop t fun u => Fr3 s R u := by
  have hk := h.k2
  have hk64 := h.k1
  have := h.ws; have := scr_le h
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := (s.gpr .r7).toNat) (by omega) (by omega)
    (fun j u => Fr3 s R u ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 j ∧ u.gpr .r10 = scA s sAM + BitVec.ofNat 64 j ∧
      u.gpr .r0 = 0) (fun i hi u ⟨hu, u11, u10, u0⟩ _ => ?_) ⟨hc, h11, h10, h0⟩
    (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun u hu => hu.1
  have he : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [u11, BitVec.add_zero]
    obtain ⟨r, hr, hcr⟩ := outW h hu.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .r10 + BitVec.ofNat 64 0) 1 := by
    rw [u10, BitVec.add_zero, Offset.add_add]
    exact scInR h hu.wr (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega)
  rw [selBody_eq, WP.block_append_iff]
  refine WP.mono (selA_ok he ha u0) fun w ⟨⟨wm, _⟩, kw⟩ => ?_
  have hw : InRegions w.wr (w.gpr .r11 + BitVec.ofNat 64 0) 1 := by
    rw [kw.wr, kw.gpr _ (by decide), u11, BitVec.add_zero]; exact outW h hu.wr hi
  refine WP.mono (selB_ok hw) fun x ⟨⟨xm, _, x11, x10, x7⟩, kx⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kw.gpr _ (by decide), u11, BitVec.add_zero, wm] at xm
    have hf : Frame [⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hwo := h.wo; rw [h.h4] at hwo
    have hsub : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]; exact Offset.sub_base _ (by omega)
    have kk : Keep [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] u x :=
      (kw.mono (by decide)).trans' (kx.mono (by decide))
    exact hu.store h kk.rd kk.wr kk.sp (fun r hr => kk.gpr r (by revert r; decide)) (.inl rfl) hsub hf
  · rw [x11, kw.gpr _ (by decide), u11, Offset.add_add]
  · rw [x10, kw.gpr _ (by decide), u10, Offset.add_add]
  · rw [kx.gpr _ (by decide), kw.gpr _ (by decide), u0]
  · rw [x7, kw.gpr _ (by decide)]

theorem selPart_ct : RelCT isa (Rel e PSC) selPart (Rel e fun _ _ => True) := by
  unfold selPart
  refine RelCT.seq (rel_split (X := fun s u => u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r12 = fb s ∧ u.sp = fb s) (Q := PV)
    (l₁ := [fp, .load .d .r11 .r12 oOut, .load .d .r7 .r12 oK]) [] [.r11, .r12] (by taint_decide) (by taint_decide)
    (fun a b ha hb => ⟨pp_sp ha.1 hb.1, fun _ h => nomatch h⟩)
    (fun a b ⟨a11, a12, asp⟩ ⟨b11, b12, bsp⟩ => ⟨by rw [asp, bsp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a12, b12, e.fb_eq]⟩)
    (fun s u h ⟨⟨R, EM, hu⟩, _⟩ => by
      have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
      have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
      have i1 := slot_rd hu (d := oOut) (by decide) (by decide)
      have i2 := slot_rd hu (d := oK) (by decide) (by decide)
      prun [fp, exec_addSp0, hu.sp, c1, c2, i1, i2, hu.sl.out, hu.sl.k])
    fun s u h ⟨⟨R, EM, hu⟩, ⟨al, u6⟩, ⟨f, u5⟩, ⟨sep, u3, hsep⟩, u0, u8⟩ => by
      have hk := h.k1
      exact WP.mono (validBlock_ok hu (outIn h hu (by omega)) (outIn h hu (by omega)) u5 u3 u6 u0 u8 hsep hu.rb)
        fun v ⟨⟨vm, v11, v7, _, _, _, _, v12⟩, kv⟩ =>
          ⟨⟨R, EM, hu.regs kv.rd kv.wr kv.sp vm fun r hr => kv.gpr r (by revert r; decide)⟩, v11, v7, v12,
            by rw [kv.gpr _ (by decide), u0]⟩) ?_
  refine RelCT.seq (rel_split (X := fun s u => u.gpr .r10 = s.gpr .r5 ∧ u.gpr .r12 = fb s ∧ u.sp = fb s) (Q := PO)
    (l₁ := [.load .d .r10 .r12 oML]) [.r12] [.r10, .r12] (by taint_decide) (by taint_decide)
    (fun a b ⟨ha, _, _, a12, _⟩ ⟨hb, _, _, b12, _⟩ => ⟨pp_sp ha hb, fun r hr => by
      rw [List.mem_singleton.mp hr, a12, b12, e.fb_eq]⟩)
    (fun a b ⟨a10, a12, asp⟩ ⟨b10, b12, bsp⟩ => ⟨by rw [asp, bsp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a10, b10, e.r]
      · rw [a12, b12, e.fb_eq]⟩)
    (fun s u h ⟨⟨R, EM, hu⟩, _, _, u12, _⟩ => by
      have c1 : oML < 2 ^ 15 ∧ oML % 4 = 0 := by decide
      have i1 := slot_rd hu (d := oML) (by decide) (by decide)
      prun [u12, c1, i1, hu.sl.ml]
      exact hu.sp)
    fun s u h ⟨⟨R, EM, hu⟩, u11, u7, u12, u0⟩ => WP.mono (outInit_ok h hu.fr3 u12)
      fun v ⟨⟨vm, v10, _⟩, kv⟩ => ?_) ?_
  · have hY : Region.Sub ⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩ (mlR s) := by rw [BitVec.add_zero]; exact fun _ h => h
    have F : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 0, 8⟩] u.mem v.mem := by
      rw [vm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact ⟨⟨R, hu.fr3.store h kv.rd kv.wr kv.sp (fun r hr => kv.gpr r (by revert r; decide)) (.inr rfl) hY F⟩,
      by rw [kv.gpr _ (by decide), u11, BitVec.add_zero], by rw [v10, BitVec.add_zero],
      by rw [kv.gpr _ (by decide), u7], by rw [kv.gpr _ (by decide), u0]⟩
  refine RelCT.seq (rel_step (P' := fun s u => ∃ R, Fr3 s R u) [.r11, .r10, .r7] (by taint_decide)
    (fun a b ⟨⟨_, ha⟩, a11, a10, a7, _⟩ ⟨⟨_, hb⟩, b11, b10, b7, _⟩ => ⟨by rw [ha.sp, hb.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a11, b11, e.r]
      · rw [a10, b10, e.scA_eq]
      · rw [a7, b7, e.r]⟩)
    fun s u h ⟨⟨R, hu⟩, u11, u10, u7, u0⟩ => WP.mono (selLoop_run h hu u11 u10 u7 u0) fun v hv => ⟨R, hv⟩) ?_
  exact rel_step [] (by taint_decide) (fun a b ⟨_, ha⟩ ⟨_, hb⟩ => ⟨by rw [ha.sp, hb.sp, e.fb_eq], fun _ h => nomatch h⟩)
    fun s u h ⟨R, hu⟩ => WP.mono (finish_ok hu) fun _ _ => trivial

theorem body_ct : RelCT isa (Rel e PEnt) body fun _ _ => True := by
  unfold body
  refine RelCT.seq setup_ct ?_
  refine RelCT.seq priv_ct ?_
  refine RelCT.seq dBuild_ct ?_
  refine RelCT.seq (hashD_ct.mono (fun a b ⟨⟨_, _, ha⟩, _, _, hb⟩ => ⟨⟨_, _, ha.post⟩, _, _, hb.post⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq kdkMac_ct ?_
  refine RelCT.seq clLoop_ct ?_
  refine RelCT.seq amLoop_ct ?_
  refine RelCT.seq maskPart_ct ?_
  refine RelCT.seq alPart_ct ?_
  refine RelCT.seq scanPart_ct ?_
  exact selPart_ct.mono (fun _ _ h => h) fun _ _ _ => trivial

end

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub code :=
  RelCT.constantTime (RelCT.alloc (fun _ _ ⟨_, _, hp⟩ => (same_of (pub_data hp)).sp)
    ((RelCT.exists_ fun e : Env => body_ct (e := e)).mono
      (fun _ _ ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ => ⟨⟨s, t, dPre_of hs, dPre_of ht, same_of (pub_data hp)⟩, ea, eb⟩)
      fun _ _ h => h))

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
