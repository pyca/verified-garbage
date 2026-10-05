import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT

/-!
# RSAES-OAEP decryption on x86-64: the points between the pieces

What the constant-time proof needs to know of one run between the pieces of
`decMain`: in the frame, with the argument slots as the prologue stored them
(`DW`), and MGF1's slots too before MGF1 (`DWM`). Each piece's step is its
correctness lemma, of which only this is kept.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

/-- In the frame, with the argument slots as the prologue stored them. -/
structure DW (s t : State) : Prop where
  he : EnvD s t
  L : Lay t (fb s) (stackArg s 15)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 15) V W ∧ ArgsD s W

/-- Before MGF1, with its slots set. -/
structure DWM (s t : State) (src srcLen dst dstLen : Nat) : Prop where
  he : EnvD s t
  L : Lay t (fb s) (stackArg s 15)
  rep : ∃ V W, Rep t.mem (fb s) (stackArg s 15) V W ∧ ArgsD s W ∧
    MArgs W (stackArg s 15) src srcLen dst dstLen

theorem decKs_lt : ∀ k ∈ decKs, k < nW := by decide

section
variable {s t : State} (hp : DPre s)
include hp

/-- The frame and the other writable regions. -/
theorem EnvD.frv (he : EnvD s t) : FrV 3 (fb s) [outR s, mlR s, scrD s] t where
  rsp := he.rsp
  wr := he.wr
  two := rfl
  pw := by
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil)))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.dKO.sub_left (frame_subD s)
      · exact hp.dKM.sub_left (frame_subD s)
      · exact hp.dKs.sub_left (frame_subD s)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dOM
      · exact hp.dOs
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.dMs
  len r hr := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Nat.le_of_lt (BitVec.isLt _)
    · show 8 ≤ 2 ^ 64; decide
    · have := hp.wS; simp only [scrD]; omega

omit hp in
theorem DW.words (h : DW s t) : ∀ k ∈ decKs, word t.mem (fb s) (8 * k) = decW s k := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  intro k hk
  rw [R.fr k (decKs_lt k hk)]
  exact hW k hk

omit hp in
theorem DWM.dw {src srcLen dst dstLen : Nat} (h : DWM s t src srcLen dst dstLen) : DW s t :=
  let ⟨V, W, R, hW, _⟩ := h.rep; ⟨h.he, h.L, V, W, R, hW⟩

/-- The label, where `hashLabel` finds it. -/
theorem DW.lab (h : DW s t) {W : Nat → BitVec 64} (hW : ArgsD s W) :
    LabAt t (fb s) (stackArg s 15) W (stackArg s 11) (stackArg s 12).toNat := by
  obtain ⟨-, -, -, -, -, -, -, w27, w28, -⟩ := hW.w
  have hsl := hp.hsl
  have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega)
  exact ⟨w27, by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 12).isLt,
    Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.he.rd, hp.hrd]; simp),
    hp.dlbs.sub_right sS, hp.dKlb.sub_left (ret_subD s)⟩

end

/-! ## The steps -/

section
variable {s : State} (hp : DPre s)
include hp

theorem dw_hashLabel {Hm : Hash} (hH : HashOK Hm) (KH : Callees Hm) (mH : MgfLink Hm hH) {t : State}
    (h : DW s t) : WP isa (hashLabel Hm.stream oLh) t (DW s) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  exact WP.mono (wp_good (hashLabel_good (HGood.of hH KH) oLh)
    (hashLabel_ok hH.stream (Hs := mH.G) mH.hash h.L R (h.lab hp hW) (Or.inr rfl)))
    fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, R3, _, _⟩, sp3, mx3, f3⟩ =>
      ⟨h.he.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3, L3, V3, W, R3, hW⟩

omit hp in
theorem dw_seedArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .r8).toNat) {t : State}
    (h : DW s t) : WP isa (.block (seedArgs Hm)) t fun t' =>
      DWM s t' (oEm + 1 + Hm.D) ((s.gpr .r8).toNat - (Hm.D + 1)) (oEm + 1) Hm.D := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (seedArgs_good _) (seedArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by have := decKs_iff hk; omega)).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem dw_dbArgs {Hm : Stream} (hD : Hm.D < 2 ^ 30) (hkD : Hm.D + 1 ≤ (s.gpr .r8).toNat) {t : State}
    (h : DW s t) : WP isa (.block (dbArgs Hm)) t fun t' =>
      DWM s t' (oEm + 1) Hm.D (oEm + 1 + Hm.D) ((s.gpr .r8).toNat - (Hm.D + 1)) := by
  obtain ⟨V, W, R, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  exact WP.mono (wp_good (dbArgs_good _) (dbArgs_ok (H := Hm) h.L R
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hD hkD))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1, L1, _, _, R1,
        fun k hk => (mW_other (by have := decKs_iff hk; omega)).trans (hW k hk), mW_args _ _ _ _ _ _⟩

omit hp in
theorem dw_mgf {Gm : Hash} (hG : HashOK Gm) (KG : Callees Gm) (mG : MgfLink Gm hG) {src srcLen dst dstLen : Nat}
    (hf : MFit src srcLen dst dstLen) {t : State} (h : DWM s t src srcLen dst dstLen) :
    WP isa (mgfXor lay Gm.stream) t (DW s) := by
  obtain ⟨V, W, R, hW, A⟩ := h.rep
  exact WP.mono (wp_good (mgfXor_good (HGood.of hG KG)) (mgfXor_ok hG.stream mG.hash mG.len
    (valid_of_link hG mG) h.L R hf A))
    fun t1 ⟨⟨L1, rd1, wr1, cs1, V1, W1, R1, hW1, _⟩, sp1, mx1, f1⟩ =>
      ⟨h.he.step rd1 wr1 sp1 (fun r hr _ => cs1 r hr) mx1 f1, L1, V1, W1, R1, fun k hk => by
        have := decKs_iff hk
        rw [hW1 k (decKs_lt k hk) (by omega) (by omega)]
        exact hW k hk⟩

/-- `lHash'`'s check, the scan, and `T` shifted into the buffer. -/
def tail1 (Hm : Stream) : Prog isa := .seq (.seq (.seq (.seq (accLh Hm) (scan Hm)) (clearBuf Hm)) copyT) shift

theorem dw_tail1 {Hm : Stream} (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) (hkD : 2 * Hm.D + 2 ≤ (s.gpr .r8).toNat)
    {t : State} (h : DW s t) : WP isa (tail1 Hm) t (DW s) := by
  have hk2 := hp.lv.2
  obtain ⟨V5, W5, R5, hW⟩ := h.rep
  obtain ⟨-, -, -, w23, -⟩ := hW.w
  have w5k : W5 23 = BitVec.ofNat 64 (s.gpr .r8).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold tail1
  refine WP.seq (WP.seq (WP.seq (WP.seq ?_)))
  refine WP.mono (wp_good (accLh_good _) (accLh_ok (Hm := Hm) h.L R5 hD hD64))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_
  have he6 : EnvD s t6 := h.he.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  refine WP.mono (wp_good (scan_good _) (scan_ok (Hm := Hm) L6 R6
    (by simp only [upd]; rw [ifn (by decide)]; exact w5k) hkD hk2 hD64))
    fun t7 ⟨⟨L7, k7, R7⟩, sp7, mx7, f7⟩ => ?_
  have he7 : EnvD s t7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  generalize hW7 : upd (upd (upd W5 31 (accL V5 Hm.D Hm.D)) 31 _) 32 _ = W7 at R7
  have w7 : ∀ j, j ≠ 31 → j ≠ 32 → W7 j = W5 j := fun j h1 h2 => by
    rw [← hW7]; simp only [upd, ifn h1, ifn h2]
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V5 Hm.D) (upd W5 31 (accL V5 Hm.D Hm.D) 31)
    ((s.gpr .r8).toNat - (2 * Hm.D + 1))
  have h32 : W7 32 = BitVec.ofNat 64 idx := by rw [← hW7]; simp only [upd]; exact hidx
  refine WP.mono (wp_good (clearBuf_good _) (clearBuf_ok (Hm := Hm) L7 R7 (k := (s.gpr .r8).toNat)
    (by rw [w7 23 (by decide) (by decide)]; exact w5k) hkD hD64))
    fun t8 ⟨⟨L8, k8, hsi8, h108, hcx8, R8⟩, sp8, mx8, f8⟩ => ?_
  have he8 : EnvD s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  refine WP.mono (wp_good copyT_good (copyT_ok (Hm := Hm) L8 R8 hsi8 h108 hcx8 hkD hk2 hD64))
    fun t9 ⟨⟨L9, k9, hcx9, R9⟩, sp9, mx9, f9⟩ => ?_
  have he9 : EnvD s t9 := he8.step k9.2.1 k9.2.2 sp9 (keep_cs3 k9 (by decide)) mx9 f9
  refine WP.mono (wp_good shift_good (shift_ok L9 R9 hcx9 (idx := idx) h32 (by omega) (fun x h1 h2 => by
      simp only [cpV, clrV]
      rw [ifn (by omega), ifp (by omega)])))
    fun t10 ⟨⟨L10, k10, V10, W10, R10, hW10, _, _⟩, sp10, mx10, f10⟩ => ?_
  refine ⟨he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10, L10, V10, W10, R10,
    hW.of fun j hj => ?_⟩
  have := decKs_iff hj
  rw [hW10 j (decKs_lt j hj) (by omega) (by omega) (by omega), w7 j (by omega) (by omega)]

/-- `ok` and the buffer to `out`. -/
theorem dw_tail2 {t : State} (h : DW s t) : WP isa (.seq (.block okMask) outLoop) t (DW s) := by
  have hk1 := hp.lv.1; have hk2 := hp.lv.2; have hsl := hp.hsl
  obtain ⟨V, W, R, hW⟩ := h.rep
  refine WP.seq (WP.mono (wp_good (block_good _ rfl) (okMask_ok h.L R))
    fun t11 ⟨⟨L11, k11, _, R11⟩, sp11, mx11, f11⟩ => ?_)
  have he11 : EnvD s t11 := h.he.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  have hW11 : ArgsD s (upd W 33 (okW W)) := hW.of fun j hj => by
    have := decKs_iff hj; simp only [upd]; rw [ifn (by omega)]
  obtain ⟨-, x21, -, x23, -⟩ := hW11.w
  have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega)
  have hout : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by simp [outR, hp.hsi]
  have aO : Apart (fb s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by
    rw [hout]; exact ⟨hp.dKO.sub_left (frame_subD s), hp.dOs.symm.sub_left sS, hp.dKO.sub_left (ret_subD s)⟩
  exact WP.mono (wp_good outLoop_good (outLoop_ok L11 R11 x21
    (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega) hk2 (by rw [he11.wr, hout]; simp)
    (by have := hp.wO; rw [hp.hsi] at this; exact this) aO))
    fun t12 ⟨⟨L12, k12, R12, _, _⟩, sp12, mx12, f12⟩ =>
      ⟨he11.step k12.2.1 k12.2.2 sp12 (keep_cs3 k12 (by decide)) mx12 f12, L12, _, _, R12, hW11⟩

end

end VG.Proof.RsaOaep.X86_64
