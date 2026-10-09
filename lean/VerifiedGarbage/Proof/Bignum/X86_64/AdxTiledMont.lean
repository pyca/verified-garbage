import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- A product of a word-width number and one below `m`, below `m R`. -/
theorem mul_lt_mont {a b m R : Nat} (ha : a < R) (hb : b < m) : a * b < m * R := by
  have h := Nat.mul_lt_mul'' ha hb
  rw [Nat.mul_comm R] at h
  exact h

/-- The reduction and the final subtraction after a raw product `X` in the
accumulator: what `montMul_ok` and `montSquare_ok` both end with. -/
theorem redcFinish_ok {s s₁ : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {X : Nat} (hX : X < wv s.mem B (slot w aN) w * 2 ^ (64 * w))
    (hv₁ : wv s₁.mem B (slot w aAcc + 16) (2 * w) = X)
    (ho₁ : Outside B (slot w aAcc) (16*w+32) s.mem s₁.mem) (k₁ : Keep mmRegs s s₁) :
    WP isa (AdxTiledProduct.redcFinish co) s₁ fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w = X % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hw1 : 2 ≤ w := by omega
  have hg : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hmpos : 0 < wv s.mem B (slot w aN) w :=
    Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hX; omega
  have hH₁ := hH.of_outside ho₁ hg
  have hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega) (by omega)
  unfold AdxTiledProduct.redcFinish
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
  have hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w :=
    AdxSquare.redc_lt hmpos hq hX heq
  have hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  have k123 := k12.trans k₃.keep
  have hv₂ : Ops s₂.mem B w ps := hv.of_outside ho12 (by unfold slot sFn hdrBytes; omega)
  refine WP.mono (finish8V_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hwN hnN hw h10 (k₃.2.1 ▸ hv₂) po ho ho1 ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [hv]; exact Nat.mod_lt _ hmpos
  · rw [hv, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    have hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h1
      · exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
      omega_using [h1, h2, hAT])

/-- Tiled multiplication preserves the general Montgomery contract: the right
operand is reduced; the left operand may be any word-width value. -/
theorem montMul_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co ca cb o a b : Nat} (po : (co, o) ∈ ps)
    (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ho : o < 8) (ha : a < 8) (hb : b<8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledProduct.montMul co ca cb) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.montMul
  refine WP.seq (WP.mono (rawProduct_ok hs hdi hH hv pa pb hZ hw hwN hnN ha hb ha1 ha2 hb1 hb2)
    fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  exact redcFinish_ok hs hdi hH hZ hwN hnN hw hv po ho ho1 ho2 hinv (mul_lt_mont (wv_lt _ _ _ _) hB) hv₁ ho₁ k₁

end VG.Proof.Bignum.X86_64.AdxTiledProduct
