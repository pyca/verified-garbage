module

public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: loading a precomputed value

`loadPre j po` (`loadPre_ok`) sets array `j` of a workspace to the `w` words
at word `d` of `pre` (`po` computes `d`), or to 0 unless they are below the
workspace's modulus: what follows is safe whatever `pre` holds.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

theorem loadPre_ok {s : State} {B P : Addr} {Z w d : Nat} {minv : BitVec 64} {j : Nat} {po : List Instr}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hj : j < 8) (hjN : j ≠ aN)
    (ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 12) 8) (hP : s.mem.readW (stackArgAddr s 12) 64 = P)
    (hpo : ∀ t : State, Keep mmRegs s t → Outside B (slot w j) (8 * (w + 2)) s.mem t.mem →
      WP isa (.block po) t fun t' => t'.gpr .rax = BitVec.ofNat 64 d ∧ t'.mem = t.mem ∧ Keep [.rax, .rdx] t t')
    (hrd : ∀ i < w, InRegions (s.rd ++ s.wr) (off P (8 * d + 8 * i)) 8)
    (hsep : ∀ i < w, ∀ b < 8, ofs B (off P (8 * d + 8 * i) + BitVec.ofNat 64 b) < slot w j ∨
      slot w j + 8 * (w + 2) ≤ ofs B (off P (8 * d + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (seqs (Crt.loadPre j po)) s fun t =>
      wv t.mem B (slot w j) w = (if wv s.mem P (8 * d) w < wv s.mem B (slot w aN) w then
        wv s.mem P (8 * d) w else 0) ∧
      Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sj := Nat.le_trans (slot_le (w := w) hj) hZ
  have e13 : off (s.gpr .rsp) (8 * 13) = stackArgAddr s 12 := rfl
  unfold Crt.loadPre
  simp only [seqs]
  -- `pre`, and the array cleared.
  refine WP.seq (WP.seq (WP.mono (WP.keep [.rsi, .r8, .r12] (Q := fun t => t.gpr .rsi = P ∧
      t.gpr .r8 = off B (slot w j) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [Crt.stk, State.ea, hdr, hg.rdi, hdrOff, e13, ha, hP, hl (sArr j) (by unfold sArr; omega_arith),
      hl sW (by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun s₁ ⟨⟨hsi, h8, h12, hm₁⟩, k₁⟩ => ?_))
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (zeroAccLoop_ok hs₁ h8 h12 hw hw' (by omega_arith)) fun s₂ ⟨_, ho₂, k₂⟩ => ?_
  rw [hm₁] at ho₂
  have k02 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  have hH₂ : Hdr s₂.mem B w minv := (Arrays.of_outside (js := [j]) (List.mem_singleton_self _) ho₂
    (Nat.le_refl _) (Nat.le_refl _)).hdr hg.hdr
  -- The source: `pre + 8 d`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (hpo s₂ k02 ho₂) fun s₃ ⟨hax, hm₃, k₃⟩ => ?_
  have k03 : Keep mmRegs s s₃ := (k02.trans k₃).mono (by decide)
  have hg₃ : Good s₃ B Z w minv := ⟨hg.scr.congr k03.2.2, (k03.gpr (by decide)).trans hg.rdi, hm₃ ▸ hH₂⟩
  have hsi₃ : s₃.gpr .rsi = P := ((k₂.trans k₃).gpr (by decide)).trans hsi
  have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have h8d : BitVec.ofNat 64 d + BitVec.ofNat 64 d + (BitVec.ofNat 64 d + BitVec.ofNat 64 d) +
      (BitVec.ofNat 64 d + BitVec.ofNat 64 d + (BitVec.ofNat 64 d + BitVec.ofNat 64 d)) = BitVec.ofNat 64 (8 * d) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have ep : P + BitVec.ofNat 64 (8 * d) = off P (8 * d) := rfl
  refine WP.mono (WP.keep [.rax, .rsi, .r12, .rbx] (Q := fun t => t.gpr .rsi = off P (8 * d) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w j) ∧ t.mem = s₃.mem)
    (by xrun [State.ea, hdr, hg₃.rdi, hdrOff, hax, hsi₃, h8d, ep, hl₃ (sArr j) (by unfold sArr; omega_arith),
      hl₃ sW (by decide), hg₃.hdr.harr j hj, hg₃.hdr.hw]) rfl) fun s₄ ⟨⟨hsi₄, h12₄, hbx₄, hm₄⟩, k₄⟩ => ?_
  have k04 : Keep mmRegs s s₄ := (k03.trans k₄).mono (by decide)
  have hs₄ := hg.scr.congr k04.2.2
  -- `[j] := pre`'s words.
  refine WP.seq (WP.mono (copyWords_ok hsi₄ hbx₄ h12₄ hw hw' (by omega_arith)
    (fun i hi => by rw [k04.2.1, k04.2.2]; exact hrd i hi) (fun i hi => hs₄.st (by omega_arith))
    (fun i hi b hb => by rcases hsep i hi b hb with h | h <;> [exact .inl h; exact .inr (by omega_arith)]))
    fun s₅ ⟨hv₅, _, ho₅, k₅⟩ => ?_)
  have hpre : wv s₄.mem P (8 * d) w = wv s.mem P (8 * d) w := by
    rw [hm₄, hm₃]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => ho₂ _ (hsep i hi b hb)
  rw [hpre] at hv₅
  have k05 : Keep mmRegs s s₅ := (k04.trans k₅).mono (by decide)
  have ho05 : Outside B (slot w j) (8 * (w + 2)) s.mem s₅.mem := by
    rw [hm₄, hm₃] at ho₅; exact ho₂.trans (ho₅.mono (Nat.le_refl _) (by omega_arith))
  have hH₅ : Hdr s₅.mem B w minv := (Arrays.of_outside (js := [j]) (List.mem_singleton_self _) ho05
    (Nat.le_refl _) (Nat.le_refl _)).hdr hg.hdr
  have hg₅ : Good s₅ B Z w minv := ⟨hg.scr.congr k05.2.2, (k05.gpr (by decide)).trans hg.rdi, hH₅⟩
  have hl₅ : ∀ i < 32, InRegions (s₅.rd ++ s₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₅.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hNv : wv s₅.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    have := slot_sep (w := w) hjN
    exact ho05.wv (by omega_arith) (by omega_arith)
  -- The mask of `[j] < [aN]`.
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w j) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .rbp = mask false ∧
      t.mem = s₅.mem)
    (by xrun [State.ea, hdr, hg₅.rdi, hdrOff, hl₅ (sArr j) (by unfold sArr; omega_arith),
      hl₅ (sArr aN) (by unfold sArr aN; omega_arith), hl₅ sW (by decide), hg₅.hdr.harr j hj,
      hg₅.hdr.harr aN (by decide), hg₅.hdr.hw, mask_false]) rfl) fun s₆ ⟨⟨h12₆, hbx₆, h10₆, hbp₆, hm₆⟩, k₆⟩ => ?_)
  have hs₆ := hg.scr.congr ((k05.trans k₆).mono (rs' := mmRegs) (by decide)).2.2
  refine WP.seq (WP.mono (cmpLoop_ok hs₆ hbx₆ h10₆ h12₆ hbp₆ hw hw' (by omega_arith) (by omega_arith))
    fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_)
  rw [hm₆, hv₅, hNv] at hbp₇
  generalize hc : decide (wv s.mem P (8 * d) w < wv s.mem B (slot w aN) w) = c at hbp₇
  -- `[j] &= mask`.
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask c ∧ t.mem = s₇.mem)
    (by xrun [hbp₇]) rfl) fun s₈ ⟨⟨h15₈, hm₈⟩, k₈⟩ => ?_)
  have k68 := k₇.trans k₈
  have hbx₈ : s₈.gpr .rbx = off B (slot w j) := (k68.gpr (by decide)).trans hbx₆
  have h12₈ : s₈.gpr .r12 = BitVec.ofNat 64 w := (k68.gpr (by decide)).trans h12₆
  have k08 : Keep mmRegs s s₈ := ((((k05.trans k₆).trans k₇).trans k₈)).mono (by decide)
  have hs₈ := hg.scr.congr k08.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₈.mem → Keep [.r14] s₈ t → t.cf = s₈.cf →
      MaskInv s₈ B Z (slot w j) c 0 t := fun t h14 hm k _ =>
    ⟨hs₈.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' (MaskInv s₈ B Z (slot w j) c) h0
    (fun i _ hi t hI => maskStep_ok hbx₈ h15₈ h12₈ (by omega_arith) (by omega_arith) hi hI)) fun t hI => ?_
  have hd := hI.done
  have ho := hI.out
  rw [hm₈, hm₇, hm₆] at hd ho
  refine ⟨?_, ho05.trans (ho.mono (Nat.le_refl _) (by omega_arith)), (k08.trans hI.keep).mono (by decide)⟩
  cases c
  · have h' : ¬wv s.mem P (8 * d) w < wv s.mem B (slot w aN) w := by simpa using hc
    simp only [h', ↓reduceIte]
    exact (wv_eq_zero_iff _ _ _ _).mpr fun i hi => by rw [hd i hi, mask_false]; exact BitVec.and_zero
  · have h' : wv s.mem P (8 * d) w < wv s.mem B (slot w aN) w := by simpa using hc
    simp only [h', ↓reduceIte]
    rw [← hv₅]
    exact wv_congr fun i hi => by rw [hd i hi, mask_true, BitVec.and_allOnes]

end VG.Proof.Bignum.X86_64
