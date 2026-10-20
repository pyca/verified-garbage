module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega

/-! # Sums and differences of the key workspace's arrays at a run-time width

`chain`: the setup of three pointers and the count, `CrtRt.chainLoop`, and
`edi` set back. A difference (`chainSub_ok`) or a sum (`chainAdd_ok`) of `K`
words, `K = w` or `w + 1`, any two arrays being the same or apart, with the
borrow or the carry as a mask in `ecx`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S arr_mono arr_end)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The words of an operation: `w`, or `w + 1` with `extra`. -/
abbrev kk (len : Nat) (extra : Bool) : Nat := kw len + extra.toNat

/-- An array's words start at or past another's, or end before it. -/
theorem arr_order (w o a : Nat) {K : Nat} (hK : K ≤ 4 * (w + 2)) : arr w o ≤ arr w a ∨ arr w a + K ≤ arr w o := by
  by_cases h : o ≤ a
  · exact .inl (arr_mono h)
  · have := arr_end (w := w) (j := a) (k := o) (by omega); simp only [S] at this; exact .inr (by omega)

theorem RtWs.rt {s : State} (h : RtWs L s B Z len N) : Rt.Ws s B Z :=
  ⟨h.ws.workspace.wr, h.ws.workspace.nowrap⟩

theorem RtWs.edi_eq {s : State} (h : RtWs L s B Z len N) : s.gpr .edi = BitVec.ofNat 32 B.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := h.ws.hdr_le
  have := h.ws.workspace.nowrap
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at *
  rw [h.edi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem RtWs.kw_pos {s : State} (h : RtWs L s B Z len N) : 0 < kw len := h.ws.wpos

/-- The setup of `chain`: the pointers at `a`, `b` and `o`, the count, no carry. -/
theorem chainSetup_ok {s : State} (h : RtWs L s B Z len N)
    {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N) (extra : Bool) :
    WP isa (.block (arrPtr L .ebp a .edx ++ arrPtr L .ebx b .edx ++ arrPtr L .edi o .edx ++ count L .edx extra ++
      ([.mov .ecx (.imm 0)] : List Instr))) s fun u =>
      Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u ∧ u.mem = s.mem ∧ PtrAt u B .ebp (arr (kw len) a) ∧
      PtrAt u B .ebx (arr (kw len) b) ∧ PtrAt u B .edi (arr (kw len) o) ∧
      (u.gpr .edx).toNat = 4 * kk len extra ∧ u.gpr .ecx = cmask false := by
  have hn := h.ws.workspace.nowrap
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have fo := h.ws.arr_fit ho
  have hl := lenSrc h
  have hle := h.lenLe
  simp only [S] at fa fb fo
  simp only [List.append_assoc]
  refine arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have hl₁ := (src_keep K₁ (by decide) m₁).trans hl
  have edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok hl₁ hle edi₁ (by decide) (by decide) (by omega) fun u₂ K₂ m₂ p₂ _ => ?_
  have hl₂ := (src_keep K₂ (by decide) m₂).trans hl₁
  have edi₂ : (u₂.gpr .edi).toNat = B.toNat := by rw [K₂.1 _ (by decide)]; exact edi₁
  refine arrPtr_ok hl₂ hle edi₂ (by decide) (by decide) (by omega) fun u₃ K₃ m₃ p₃ _ => ?_
  have hl₃ := (src_keep K₃ (by decide) m₃).trans hl₂
  refine count_ok hl₃ hle fun u₄ K₄ m₄ c₄ => wp_movS rfl fun u U _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s u :=
    ((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (U.keeps.mono (by decide))
  refine ⟨K, by rw [U.mem, m₄, m₃, m₂, m₁], ?_, ?_, ?_, ?_, U.gpr⟩
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂
  · rw [PtrAt, U.other _ (by decide), K₄.1 _ (by decide)]; exact p₃
  · rw [U.other _ (by decide)]; exact c₄

/-- What `chain` keeps of the context, from the loop's frame and `edi` set back. -/
theorem chain_frame {s t : State} (h : RtWs L s B Z len N) {o : Nat} (ho : o < N) {K : Nat}
    (hK : 4 * K ≤ 4 * (kw len + 2)) (O : Outside B (arr (kw len) o) (4 * K) s.mem t.mem)
    (Kt : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t) (edi : t.gpr .edi = BitVec.ofNat 32 B.toNat) :
    RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fo := h.ws.arr_fit ho
  have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) Kt (edi.trans h.edi_eq.symm)
  exact ⟨h.keep K' (by decide) (by decide) (O.mono (Nat.zero_le _) (by simp only [S] at fo; omega)),
    Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega) (by simp), K'⟩

/-- `[o] = [a] - [b]`, `K` words, the borrow as a mask in `ecx`. -/
theorem chainSub_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N)
    (extra : Bool) :
    WP isa (chain L .sbb o a b extra) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (arr (kw len) o) (kk len extra) + val32 s.mem B (arr (kw len) b) (kk len extra) =
          val32 s.mem B (arr (kw len) a) (kk len extra) + 2 ^ (32 * kk len extra) * c.toNat) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have fo := h.ws.arr_fit ho
  have hK : 4 * kk len extra ≤ 4 * (kw len + 2) := by
    have := Bool.toNat_le extra; simp only [kk]; omega
  simp only [S] at fa fb fo
  unfold VG.Impl.Rsa.X86.KeyRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h ho ha hb extra) fun u ⟨K, m, pa, pb, po, e, c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok (h.rt.of_keeps K) (N := kk len extra)
    (by have := h.kw_pos; simp only [kk]; omega) (by omega) (by omega) (by omega) (arr_order _ _ _ hK)
    (arr_order _ _ _ hK) pa pb po e c) fun t ⟨O, _, V, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kp, Kr⟩ := chain_frame h ho hK (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  obtain ⟨c, ec, V⟩ := V
  exact ⟨F, Kp, ⟨c, by rw [U.other _ (by decide)]; exact ec, by rw [U.mem]; exact V⟩, Kr⟩

/-- `[o] = [a] + [b]`, `K` words, the carry as a mask in `ecx`. -/
theorem chainAdd_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N)
    (extra : Bool) :
    WP isa (chain L .adc o a b extra) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      (∃ c : Bool, t.gpr .ecx = cmask c ∧
        val32 t.mem B (arr (kw len) o) (kk len extra) + 2 ^ (32 * kk len extra) * c.toNat =
          val32 s.mem B (arr (kw len) a) (kk len extra) + val32 s.mem B (arr (kw len) b) (kk len extra)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have fo := h.ws.arr_fit ho
  have hK : 4 * kk len extra ≤ 4 * (kw len + 2) := by
    have := Bool.toNat_le extra; simp only [kk]; omega
  simp only [S] at fa fb fo
  unfold VG.Impl.Rsa.X86.KeyRt.chain
  refine WP.seq (WP.mono (chainSetup_ok h ho ha hb extra) fun u ⟨K, m, pa, pb, po, e, c⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.CrtRt.addLoop_ok (h.rt.of_keeps K) (N := kk len extra)
    (by have := h.kw_pos; simp only [kk]; omega) (by omega) (by omega) (by omega) (arr_order _ _ _ hK)
    (arr_order _ _ _ hK) pa pb po e c) fun t ⟨O, _, _, V, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  obtain ⟨F, Kp, Kr⟩ := chain_frame h ho hK (by rw [U.mem]; exact O) (KK.trans (U.keeps.mono (by decide))) U.gpr
  obtain ⟨c, ec, V⟩ := V
  exact ⟨F, Kp, ⟨c, by rw [U.other _ (by decide)]; exact ec, by rw [U.mem]; exact V⟩, Kr⟩

end VG.Proof.Rsa.X86.KeyRt
