module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.Math

/-! # Witness preparation for a generic shared Miller–Rabin round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

def witnessRanges (w : Nat) : List (Nat × Nat) := witRanges w ++
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aXm, 8 * (w + 2)), (slot w aB, 8 * (w + 2))]

/-- `witnessRanges`'s ranges, in the header and in the arrays. -/
theorem witnessRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(216, 8), (0, 8)]
    [(1, 1), (2, 1), (3, 1), (5, 1), (8, 1)] (witnessRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    witRanges, witnessRanges, Public.aX, Public.aAcc, Public.aTmp, Public.aXm, aX, aAcc, aTmp, aXm, aB, sFn, kU, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩

theorem sharedWitness_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ ([M.mm aXm aX aR2, copyA aB aXm] : List (Prog isa)))) s fun t =>
      MrCtx t B Z w c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aXm) w =
        (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw' : w < 2 ^ 31 := by omega_using [hw128]
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  have sl : ∀ {j : Nat}, j < 16 → slot w j + 8 * (w + 2) ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega_using [hZ, this]
  have sR2 := sl (show aR2 < 16 by decide)
  have sB := sl (show aB < 16 by decide)
  have sY := sl (show aY < 16 by decide)
  have sXm := sl (show aXm < 16 by decide)
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hc hw4 hw128 hodd hb hR hU hK (Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2
  simp only [seqs]
  -- `b R mod c` into `aXm`.
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (M.mm_ok hg₁.1 hg₁.2 hc₁.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨_, hlt₂, hy₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = wt.1 * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₂ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp)
  have hc₂ : MrCtx s₂ B Z w c bm := hc₁.of_frm f₂ (by kmut) k₂ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  -- `[aB] := b R mod c`.
  refine WP.mono (copyA_ok hc₂.ws (o := aB) (a := aXm) (by decide) (by decide) (by decide))
    fun s₃ ⟨hv₃, o₃, _, _, k₃⟩ => ?_
  rw [hXm] at hv₃
  have f₃ : Frm B [(slot w aB, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (o₃.mono (o' := slot w aB) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have hc₃ := hc₂.setB f₃ (by kmut) k₃ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) hv₃
  have f13 : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aXm, 8 * (w + 2)), (slot w aB, 8 * (w + 2))] s₁.mem s₃.mem :=
    (f₂.mono (by simp)).trans (f₃.mono (by simp))
  refine ⟨hc₃, ?_, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [f₃.wv_eq (d := slot w aXm) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_using [hn, sXm])]
    exact hXm
  · rw [f13.wv_eq (d := slot w aR2) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_using [hn, sR2])]
    exact hR2₁
  · rw [f13.word_eq (d := 8 * kU) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kU]; omega_using [])]
    exact hu₁
  · rw [f13.word_eq (d := 8 * kUsed) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_using [])]
    exact hus₁
  · exact (hf₁.mono (fun r hr => List.mem_append_left _ hr)).trans
      (f13.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.RsaKeyGen.AArch64
