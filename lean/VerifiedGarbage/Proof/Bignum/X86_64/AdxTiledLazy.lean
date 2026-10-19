module

import VerifiedGarbage.Proof.Bignum.X86_64.AdxLazy8
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont

/-! The reduction of a raw product `X < R²` and the lazy final subtraction. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- `redcFinish_ok` with the lazy final subtraction, for any raw product
`X < R²`: `o` is congruent to `X R⁻¹` modulo `m`. -/
theorem redcLazy_ok {s s₁ : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {X : Nat} (hX : X < 2 ^ (64 * w) * 2 ^ (64 * w))
    (hv₁ : wv s₁.mem B (slot w aAcc + 16) (2 * w) = X)
    (ho₁ : Outside B (slot w aAcc) (16*w+32) s.mem s₁.mem) (k₁ : Keep mmRegs s s₁) :
    WP isa (AdxTiledProduct.redcLazy co) s₁ fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w = X % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hw1 : 2 ≤ w := by omega
  have hg : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hmpos : 0 < wv s.mem B (slot w aN) w := wv_pos_of_inv (by omega) hinv
  have hH₁ := hH.of_outside ho₁ hg
  have hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega) (by omega)
  unfold AdxTiledProduct.redcLazy
  refine WP.seq (WP.mono (AdxRotate8.redc_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hwN hnN)
    fun s₂ ⟨vred,ho₂,k₂⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := vred (by rw [hn₁]; exact hinv)
  have hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega) (by omega)
  rw [hv₁, hN₁] at heq
  have ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega) (by omega)).trans ho₂
  have hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega) (by omega)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho12 (by unfold slot; omega)
  have hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 ^ (64 * w) + wv s.mem B (slot w aN) w :=
    VG.Proof.Bignum.redc_lt_add hq hX heq
  have hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  have k123 := k12.trans k₃.keep
  have hv₂ : Ops s₂.mem B w ps := hv.of_outside ho12 (by unfold slot sFn hdrBytes; omega)
  refine WP.mono (lazy8V_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hwN hnN hw h10 (k₃.2.1 ▸ hv₂) po ho ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    have hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
      omega_using [h1, h2, hAT])

end VG.Proof.Bignum.X86_64.AdxTiledProduct
