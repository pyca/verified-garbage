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
    (hpo : ∀ t : State, t.mem = s.mem → Keep [.rsi] s t →
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
  have h8d : BitVec.ofNat 64 d + BitVec.ofNat 64 d + (BitVec.ofNat 64 d + BitVec.ofNat 64 d) +
      (BitVec.ofNat 64 d + BitVec.ofNat 64 d + (BitVec.ofNat 64 d + BitVec.ofNat 64 d)) = BitVec.ofNat 64 (8 * d) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have ep : P + BitVec.ofNat 64 (8 * d) = off P (8 * d) := rfl
  unfold Crt.loadPre
  simp only [seqs]
  -- `pre`, the offset, the source `pre + 8 d`, and the array cleared.
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = P ∧ t.mem = s.mem)
    (by xrun [Crt.stk, State.ea, hdrOff, e13, ha, hP]) rfl) fun s₀ ⟨⟨hsi₀, hm₀⟩, k₀⟩ => ?_
  refine WP.mono (hpo s₀ hm₀ k₀) fun s₀' ⟨hax, hm₀', k₀'⟩ => ?_
  have k00 := k₀.trans k₀'
  have hm00 : s₀'.mem = s.mem := hm₀'.trans hm₀
  have hdi : s₀'.gpr .rdi = B := (k00.gpr (by decide)).trans hg.rdi
  have hl' : ∀ i < 32, InRegions (s₀'.rd ++ s₀'.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k00.2.1, k00.2.2]; exact hl i hi
  have hsi' : s₀'.gpr .rsi = P := (k₀'.gpr (by decide)).trans hsi₀
  refine WP.mono (WP.keep [.rax, .rsi, .r8, .r12] (Q := fun t => t.gpr .rsi = off P (8 * d) ∧
      t.gpr .r8 = off B (slot w j) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hax, hsi', h8d, ep, hl' (sArr j) (by unfold sArr; omega_arith),
      hl' sW (by decide), hm00, hg.hdr.harr j hj, hg.hdr.hw]) rfl) fun s₁ ⟨⟨hsi, h8, h12, hm₁⟩, k₁'⟩ => ?_
  have k₁ := k00.trans k₁'
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (zeroAccLoop_ok hs₁ h8 h12 hw hw' (by omega_arith)) fun s₂ ⟨_, ho₂, k₂⟩ => ?_
  rw [hm₁] at ho₂
  have k02 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  -- `rbx := r8`.
  refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off B (slot w j) ∧ t.mem = s₂.mem)
    (by xrun [(k₂.gpr (by decide)).trans h8]) rfl) fun s₄ ⟨⟨hbx₄, hm₄⟩, k₄⟩ => ?_)
  have hsi₄ : s₄.gpr .rsi = off P (8 * d) := ((k₂.trans k₄).gpr (by decide)).trans hsi
  have h12₄ : s₄.gpr .r12 = BitVec.ofNat 64 w := ((k₂.trans k₄).gpr (by decide)).trans h12
  have k04 : Keep mmRegs s s₄ := (k02.trans k₄).mono (by decide)
  have hs₄ := hg.scr.congr k04.2.2
  -- `[j] := pre`'s words.
  refine WP.seq (WP.mono (copyWords_ok hsi₄ hbx₄ h12₄ hw hw' (by omega_arith)
    (fun i hi => by rw [k04.2.1, k04.2.2]; exact hrd i hi) (fun i hi => hs₄.st (by omega_arith))
    (fun i hi b hb => by rcases hsep i hi b hb with h | h <;> [exact .inl h; exact .inr (by omega_arith)]))
    fun s₅ ⟨hv₅, _, ho₅, k₅⟩ => ?_)
  have hpre : wv s₄.mem P (8 * d) w = wv s.mem P (8 * d) w := by
    rw [hm₄]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => ho₂ _ (hsep i hi b hb)
  rw [hpre] at hv₅
  have k05 : Keep mmRegs s s₅ := (k04.trans k₅).mono (by decide)
  have ho05 : Outside B (slot w j) (8 * (w + 2)) s.mem s₅.mem := by
    rw [hm₄] at ho₅; exact ho₂.trans (ho₅.mono (Nat.le_refl _) (by omega_arith))
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
  refine WP.seq (WP.mono (WP.keep [.r10, .rbp] (Q := fun t => t.gpr .r10 = off B (slot w aN) ∧
      t.gpr .rbp = mask false ∧ t.mem = s₅.mem)
    (by xrun [State.ea, hdr, hg₅.rdi, hdrOff, hl₅ (sArr aN) (by unfold sArr aN; omega_arith),
      hg₅.hdr.harr aN (by decide), mask_false]) rfl) fun s₆ ⟨⟨h10₆, hbp₆, hm₆⟩, k₆⟩ => ?_)
  have h12₆ : s₆.gpr .r12 = BitVec.ofNat 64 w := ((k₅.trans k₆).gpr (by decide)).trans h12₄
  have hbx₆ : s₆.gpr .rbx = off B (slot w j) := ((k₅.trans k₆).gpr (by decide)).trans hbx₄
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
