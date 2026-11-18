module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxLazy8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRowsCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.AdxLazy8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxLazy8
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdx
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdx
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw

/-! ### `Bignum.X86_64.MontFnLazyVerified`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.MontFnLazy`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledLazy`, which only this module used -/

section

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
  obtain hNs := slot_le (w := w) (show aN < 8 by decide)
  obtain hw1 : 2 ≤ w := by omega_using [hwN, hnN]
  obtain hg : hdrBytes ≤ slot w aAcc := by unfold slot; omega_using []
  obtain hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  obtain hmpos : 0 < wv s.mem B (slot w aN) w := wv_pos_of_inv (by omega_using [hw1]) hinv
  obtain hH₁ := hH.of_outside ho₁ hg
  obtain hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  unfold AdxTiledProduct.redcLazy
  refine WP.seq (WP.mono (AdxRotate8.redc_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hwN hnN)
    fun s₂ ⟨vred,ho₂,k₂⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := vred (by rw [hn₁]; exact hinv)
  obtain hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  rw [hv₁, hN₁] at heq
  obtain ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega_using []) (by omega_using [])).trans ho₂
  obtain hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  obtain k12 := k₁.trans k₂
  obtain hs₂ := hs.congr k12.2.2
  obtain hH₂ := hH.of_outside ho12 (by unfold slot; omega_using [])
  obtain hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 ^ (64 * w) + wv s.mem B (slot w aN) w :=
    VG.Proof.Bignum.redc_lt_add hq hX heq
  obtain hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this]), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  obtain k123 := k12.trans k₃.keep
  obtain hv₂ : Ops s₂.mem B w ps := hv.of_outside ho12 (by unfold slot sFn hdrBytes; omega_using [])
  refine WP.mono (lazy8V_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hwN hnN hw h10 (k₃.2.1 ▸ hv₂) po ho ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [Nat.mul_mod, hv, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    obtain h1 := hx aAcc (by simp)
    obtain h2 := hx aTmp (by simp)
    obtain h3 := hx o (by simp)
    obtain hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj
      exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      obtain hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
      omega_using [h1, h2, hAT])

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end


/-!
# `vg_rsa_lazy_mont_mul_adx`: correctness

`mulAdx_ok`'s proof, with the lazy reduction of the tiles
(`AdxTiledProduct.redcLazy_ok`) and `montMul`'s rounds without `[b] < m`
(`mmTailLazy_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- `adxBodyLazy`: `adxBody_ok` without `[b] < m`, and so without `[o] < m`. -/
theorem adxBodyLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hv : Ops s.mem B w (adxOps o a b))
    (hdx : s.gpr .rdx = BitVec.ofNat 64 o) (hcx : s.gpr .rcx = BitVec.ofNat 64 a)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa adxBodyLazy s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t := by
  unfold adxBodyLazy
  refine WP.seq (WP.mono (alignTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hH hv ⊢
  obtain post : ∀ t, (wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      (∃ m, Outside B (8 * sFn 12) 32 s₁.mem m ∧ Arrays B w [aAcc, aTmp, o] m t.mem) ∧ Keep mmRegs s t) :=
    fun t ⟨h2, h3, k⟩ => ⟨h2, ⟨_, Outside.refl _ _ _ _, h3⟩, (k₁.trans k).mono (by decide)⟩
  by_cases h8w : AlignOk w
  · refine WP.ite true (by simp [eval, hz, h8w]) (fun _ => ?_) (by simp)
    obtain ⟨h8w, h8w', -⟩ := h8w
    unfold tiledLazy
    obtain hcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 a := (k₁.gpr (by decide)).trans hcx
    obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 b := (k₁.gpr (by decide)).trans h8
    refine WP.seq (WP.mono (cmpIdx_ok ha hb hcx₁ h8₁) fun s₂ ⟨hz₂, hm₂, _, k₂⟩ => ?_)
    obtain hs₂ := hs₁.congr k₂.2.2
    obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
    rw [← hm₂] at hinv hH hv ⊢
    obtain hwN : w = 8 * (w / 8) := by omega_arith
    obtain hraw : WP isa (.ite .e (AdxTiledSquare.rawSquareBare xA) (AdxTiledProduct.rawProductBare xA xB)) s₂
        fun s₃ => ∃ m, Outside B (8 * sFn 12) 32 s₂.mem m ∧
          wv s₃.mem B (slot w aAcc + 16) (2 * w) = wv s₂.mem B (slot w a) w * wv s₂.mem B (slot w b) w ∧
          Outside B (slot w aAcc) (16 * w + 32) m s₃.mem ∧ Keep mmRegs s₂ s₃ := by
      by_cases hab : a = b
      · subst b
        exact WP.ite true (by simp [eval, hz₂]) (fun _ =>
          AdxTiledSquare.rawSquareBare_ok hs₂ hdi₂ hH hZ hwN (by omega_arith) hw' hv (mem_adxOps_a o a a) ha ha1 ha2)
          (by simp)
      · exact WP.ite false (by simp [eval, hz₂, hab]) (by simp) (fun _ =>
          AdxTiledProduct.rawProductBare_ok hs₂ hdi₂ hH hv (mem_adxOps_a o a b) (mem_adxOps_b o a b) hZ hw' hwN
            (by omega_arith) ha hb ha1 ha2 hb1 hb2)
    refine WP.seq (WP.mono hraw fun s₃ ⟨m, om, hv₃, ho₃, k₃⟩ => ?_)
    have hn := hs.nowrap
    obtain sl : ∀ j < 8, 8 * sFn 12 + 32 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ Z := fun j hj =>
      ⟨by unfold slot sFn hdrBytes; omega_arith, Nat.le_trans (slot_le hj) hZ⟩
    obtain vm : ∀ j < 8, wv m B (slot w j) w = wv s₂.mem B (slot w j) w := fun j hj =>
      om.wv (Or.inr (sl j hj).1) (by have := (sl j hj).2; omega_arith)
    obtain hinvm : ((word m B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [om.word (Or.inr (sl aN (by decide)).1) (by have := (sl aN (by decide)).2; omega_arith)]; exact hinv
    refine WP.mono (AdxTiledProduct.redcLazy_ok (s := {s₂ with mem := m}) (hs₂.congr rfl) hdi₂
      (hH.of_outside_fn om (by unfold sFn; omega_arith)) hZ hwN (by omega_arith) hw'
      (hv.of_outside om (Nat.le_refl _)) (mem_adxOps_o o a b) ho ho1 ho2 hinvm
      (Nat.mul_lt_mul'' (wv_lt _ _ _ _) (wv_lt _ _ _ _)) hv₃ ho₃ k₃)
      fun t ⟨h2, h3, k⟩ => ?_
    dsimp only at h2 h3
    rw [vm aN (by decide)] at h2
    exact ⟨h2, ⟨m, om, h3⟩, ((k₁.trans k₂).trans k).mono (by decide)⟩
  · refine WP.ite false (by simp [eval, hz, h8w]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (basesR_ok hs₁ hdi₁ hH hZ ho ha hb ((k₁.gpr (by decide)).trans hdx)
      ((k₁.gpr (by decide)).trans hcx) ((k₁.gpr (by decide)).trans h8))
      fun s₂ ⟨hbx, h11, h9, h10, h8₂, h12, h15, hsi₂, hm₂, k₂⟩ => ?_)
    rw [← hm₂] at hinv
    refine WP.mono (mmTailLazy_ok (hs₁.congr k₂.2.2) hZ hw hw' (by decide) (by decide) (by decide) ho ha hb
      (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2) hbx h11 h9 h10
      h8₂ h12 h15 hsi₂ hinv) fun t ⟨_, _, h2, h3, k⟩ => ?_
    rw [hm₂] at h2 h3
    exact post t ⟨h2, h3, (k₂.trans k).mono (by decide)⟩

/-- `vg_rsa_lazy_mont_mul_adx`'s code: what `mulAdx_ok` says, but `[o] < m`, without `[b] < m`. -/
theorem mulAdxLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulAdxLazy s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  obtain h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  have hxO : 8 * sArr xO = 8 * sFn 0 := rfl
  obtain sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  obtain s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  obtain hZ32 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 0 (show 31 < 32 by decide); have := sl 0 (by decide); omega_arith
  unfold mulAdxLazy
  refine WP.seq (WP.mono (adxHead_ok hs hdi hH hZ ho ha hb hdx hcx h8) fun s₁ ⟨hm₁, hdx₁, hcx₁, h8₁, k₁, sv, x3, x4, x5, x6, x7⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  obtain ho₁ : Outside B (8 * sArr xO) 24 s.mem s₁.mem := hm₁ ▸ headMem_outside s.mem B w o a b
  obtain vj : ∀ j < 8, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj =>
    ho₁.wv (by have := s0 j; omega_arith) (by have := sl j hj; omega_arith)
  obtain hinv₁ : ((word s₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho₁.word (by have := s0 aN; omega_arith) (by have := sl aN (by decide); omega_arith)]; exact hinv
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (adxBodyLazy_ok hs₁ hdi₁ (hm₁ ▸ headMem_hdr hH o a b) hZ hw hw' ho
    ha hb ho1 ho2 ha1 ha2 hb1 hb2 (hm₁ ▸ headMem_ops s.mem B w o a b) hdx₁ hcx₁ h8₁ hinv₁))
    fun s₂ ⟨⟨heq, ⟨mb, omb, har⟩, k₂⟩, hx₂, _⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.mono (restore_ok hs₂ hdi₂ hZ32 (m₀ := s.mem) (by rw [hx₂, x3]) (by rw [hx₂, x4]) (by rw [hx₂, x5])
    (by rw [hx₂, x6]) (by rw [hx₂, x7]) (sv.of_xmm hx₂))
    fun t ⟨rs, o₃, in₃, inb₃, k₃⟩ => ?_
  obtain hvo : wv t.mem B (slot w o) w = wv s₂.mem B (slot w o) w :=
    o₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> have := s0 o <;> unfold sFn slot hdrBytes at * <;> omega_arith)
      (by have := sl o ho; omega_arith)
  rw [vj aN (by decide), vj a ha, vj b hb] at heq
  refine ⟨by rw [hvo]; exact heq, fun x hx => ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide), ?_⟩
  · by_cases hr : 8 * sFn 0 ≤ ofs B x ∧ ofs B x < 8 * sFn 0 + 48
    · exact in₃ x hr.1 hr.2
    by_cases hb : 8 * sFn 12 ≤ ofs B x ∧ ofs B x < 8 * sFn 12 + 32
    · exact inb₃ x hb.1 hb.2
    obtain hb' : ofs B x < 8 * sFn 12 ∨ 8 * sFn 12 + 32 ≤ ofs B x := by omega_arith
    rw [o₃ x (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> simp only [] <;> omega_arith), har x hx, omb x hb',
      ho₁ x (by rw [hxO]; unfold sFn at *; omega_arith)]
  · exact rs

end VG.Proof.Bignum.X86_64

end

end

/-! ### `Bignum.X86_64.MontFnLazyCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxTiledLazyCT`, which only this module used -/

section

/-!
# The lazy final subtraction: constant time

`lazy8` addresses only from `w` and the bases of `T`, `m` and `o`, which
`lazyLoads` reads from the header; the mask, which is secret, only selects
data.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

/-- After `lazyLoads`: `w` and the bases of `T`, `o` and `m`. -/
def FL (o : Nat) (L : Ws) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = off L.B (slot L.w aTmp) ∧
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w aN)

theorem pins_fl (o : Nat) : Pins (FL o) [.r12, .r8, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- `redcLazy`, for slots and layouts given by any public data `x`. -/
theorem redcLazy_ct {α : Type} {P : α → List (Nat × Nat)} {L : α → Layout} {O : α → Nat} {co : Nat}
    (po : ∀ x, (co, O x) ∈ P x) {h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.lazyLoads co)) h₃).isSome=true) :
    RelCT isa (Two fun x s => GoodV (P x) (L x) s) (AdxTiledProduct.redcLazy co) (fun _ _ => True) := by
  have pins : Pins (fun x s => GoodV (P x) (L x) s) [.rdi] := fun x => pins_goodV (P x) (L x)
  unfold AdxTiledProduct.redcLazy
  refine RelCT.seq redcV_ct' ?_
  refine RelCT.seq (two_piece (Ψ := fun x s => GoodV (P x) (L x) s ∧ s.gpr .r10=off (L x).B (slot (L x).w aN))
    [.rdi] pins (by taint_decide) ?_) ?_
  · rintro x s ⟨⟨mi,hg⟩,hv⟩
    have hZ := (L x).hZ
    have hsrc : readSrc s (.mem (hdr (sArr aN)))=some (off (L x).B (slot (L x).w aN)) := by
      rw [readSrc_word (d := 8*sArr aN) hg.scr (by simp only [State.ea,hdr,hg.rdi,hdrOff])
        (by have := hdr_lt_slot (L x).w 8 (show sArr aN<32 by decide); omega_using [hZ, this]),hg.hdr.harr aN (by decide)]
    exact WP.mono (movMem_ok s (dst := .r10) hsrc) fun _ ⟨p,_,_,k⟩ =>
      ⟨⟨⟨mi,hg.scr.congr k.keep.2.2,(k.keep.gpr (by decide)).trans hg.rdi,k.2.1 ▸ hg.hdr⟩,k.2.1 ▸ hv⟩,p⟩
  unfold Adx.lazy8
  refine RelCT.seq (two_piece (Ψ := fun x => FL (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) [.rdi]
    (fun x s t hs ht => pins x s t hs.1 ht.1) hF ?_)
    (two_taint _ (fun x => pins_fl (O x) ⟨(L x).B,(L x).Z,(L x).w⟩) (by taint_decide))
  rintro x s ⟨⟨⟨mi,hg⟩,hv⟩,p⟩
  exact WP.mono (lazyLoads_ok hg.scr hg.rdi hg.hdr (L x).hZ (hv.at (po x)) (hv.lt (po x)))
    fun _ ⟨p12,p8,pbx,_,k⟩ => ⟨p12,p8,pbx,(k.gpr (by decide)).trans p⟩

end VG.Proof.Bignum.X86_64.AdxTiledProduct

end

end

/-!
# `vg_rsa_lazy_mont_mul_adx`: constant time

`vg_rsa_mont_mul_adx`'s proof, with the lazy reduction of the tiles
(`AdxTiledProduct.redcLazy_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The tiles, with the lazy reduction. -/
theorem tiledLazy_ct : RelCT isa (Two fun d s => (AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) ∧
    isa.eval .e s = some true) tiledLazy fun _ _ => True := by
  unfold tiledLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => (AdxMid d s ∧ AlignOk d.w) ∧ s.zf = some (decide (d.a = d.b)))
    [.rcx, .r8] (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁.1.1 h₂.1.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by taint_decide) ?_) ?_
  · rintro d s ⟨⟨hm, hz⟩, he⟩
    have hA : AlignOk d.w := by simpa only [eval, hz, Option.some.injEq, decide_eq_true_eq] using he
    have ha := hm.1.2.2.2.2.1.2.1
    have hb := hm.1.2.2.2.2.1.2.2.1
    have hcx := hm.1.2.2.2.2.2.2.1
    have h8 := hm.1.2.2.2.2.2.2.2
    exact WP.mono (cmpIdx_ok ha hb hcx h8) fun t ⟨hz', hm', hc', k⟩ =>
      ⟨⟨⟨AdxIn.of_keep hm.1 hm' k hc' (by decide), hm' ▸ hm.2⟩, hA⟩, hz'⟩
  refine RelCT.seq (R := Two TiledMid)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    (AdxTiledProduct.redcLazy_ct (P := fun x : TiledData => adxOps x.1.o x.1.a x.1.b)
      (L := fun x => adxLayout x.1 x.2.1 x.2.2) (O := fun x => x.1.o) (fun x => mem_adxOps_o _ _ _)
      (by taint_decide))
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, z₁⟩, e₁⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hab : d.a = d.b := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using e₁
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, -, -, -, ha1, ha2, -⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledSquare.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) ha ha1 ha2
          (by taint_decide) (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledSquare.rawBare_fw (mem_adxOps_a _ _ _) ha ha1 ha2 (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨d, ⟨⟨⟨h₁, hA⟩, -⟩, -⟩, ⟨⟨h₂, -⟩, -⟩, -⟩ e₁' e₂'
    have hZ := h₁.1.2.2.2.1
    obtain ⟨-, ha, hb, -, -, ha1, ha2, hb1, hb2⟩ := h₁.1.2.2.2.2.1
    obtain ⟨ht, -, u₁, u₂⟩ := two_post (α := Unit)
      (two_map (fun _ => adxLayout d hZ hA) (fun _ _ h => h)
        (AdxTiledProduct.rawBare_ct (ps := adxOps d.o d.a d.b) (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb
          ha1 ha2 hb1 hb2 (by taint_decide) (by taint_decide)))
      (fun _ s h => AdxTiledProduct.rawBare_fw (mem_adxOps_a _ _ _) (mem_adxOps_b _ _ _) ha hb ha1 ha2 hb1 hb2
        (adxLayout d hZ hA) s h)
      _ _ _ _ _ _ ⟨(), goodV_of_mid h₁ hZ hA, goodV_of_mid h₂ hZ hA⟩ e₁' e₂'
    exact ⟨ht, ⟨d, hZ, hA⟩, u₁, u₂⟩

theorem adxBodyLazy_ct : RelCT isa (Two AdxMid) adxBodyLazy fun _ _ => True := by
  unfold adxBodyLazy
  refine RelCT.seq (two_piece (Ψ := fun d s => AdxMid d s ∧ s.zf = some (decide (AlignOk d.w))) [.rdi]
    (fun d s₁ s₂ h₁ h₂ r hr => pins_adxMid d s₁ s₂ h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])) (by taint_decide) ?_)
    (two_ite (fun d s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) tiledLazy_ct fallback_ct)
  rintro d s ⟨hm, hv⟩
  obtain ⟨hs, hdi, ⟨mi, hH⟩, hZ, -⟩ := id hm
  exact WP.mono (alignTest_ok hs hdi hH hZ) fun t ⟨hz, hm', k⟩ =>
    ⟨⟨AdxIn.of_keep hm hm' k (k.gpr (by decide)) (by decide), hm' ▸ hv⟩, hz⟩

/-- `vg_rsa_lazy_mont_mul_adx` after the head. -/
theorem adxTailLazy_ct : RelCT isa (Two AdxMid) (.seq adxBodyLazy (.block restore)) fun _ _ => True :=
  RelCT.seq (RelCT.keepRdi (f := CallData.B) adxBodyLazy_ct (by rw [← Code.allInstrs_eq]; decide +kernel)
    fun _ _ h => h.1.2.1)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))

end VG.Proof.Bignum.X86_64

end

end

/-! # The baseline Montgomery multiplication of `vg_rsa_lazy_mont_mul`, without `[b] < m` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

/-- `mulBase_ok` without `[b] < m`: the baseline is lazy too. -/
theorem mulBaseLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (BaseSquare.tail_ok hs₁ hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hbx h11 h9 h10 h8₁ h12
    h15 hsi₁ hinv) fun s₂ ⟨_, _, heq, har, k₂, hx₂⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_stashed hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  rw [hm₁] at heq har
  rw [← mt] at heq har
  exact ⟨heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

end VG.Proof.Bignum.X86_64.MontFn

end

end

/-!
# Lazy squarings by calls of `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx`

`MontS.fnLazy` and `MontS.fnLazyAdx`: the squarings of `aY` by calls of the
lazy Montgomery multiplications, inlined, whose results are below `R`. A call
of `vg_rsa_lazy_mont_mul`, inlined, is `vg_rsa_mont_mul`'s (`mmFnBase`),
whose timing `Mont.fnBase` already proves.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The call of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def mmFnAdxLazy (o a b : Nat) : Prog isa := (call "vg_rsa_lazy_mont_mul_adx" mulAdxLazy o a b).inline

theorem mmFnAdxLazy_eq (o a b : Nat) : mmFnAdxLazy o a b = .seq (.block (args o a b)) mulAdxLazy := rfl

theorem mmFnAdxLazy_ct {o a b : Nat} (op : Opnds o a b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ slotsIn))) hc).isSome = true) :
    RelCT isa (Two GoodW) (mmFnAdxLazy o a b) fun _ _ => True := by
  rw [mmFnAdxLazy_eq]
  unfold mulAdxLazy
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := fun L s => AdxMid ⟨L.B, L.Z, L.w, o, a, b⟩ s) [.rdi] pins_goodW h
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_map (fun L : Ws => (⟨L.B, L.Z, L.w, o, a, b⟩ : CallData)) (fun _ _ h => h)
      adxTailLazy_ct))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  exact WP.mono (adxHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op.1 op.2.1
    op.2.2.1 hdx hcx h8) fun u ⟨hm', hdx', hcx', h8', k', _⟩ =>
      AdxMid.of_head (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op hm' hdx' hcx' h8' k'

/-- Squarings by calls of `vg_rsa_lazy_mont_mul`, inlined: `vg_rsa_mont_mul`'s
code, whose result is below `R` for any operand below `R`. -/
def MontS.fnLazy : MontS where
  mm := mmFnBase aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnBase_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (MontFn.mulBaseLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr)
      hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hdx hcx h8 hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := Mont.fnBase.ct (.inr (.inl ⟨rfl, rfl, rfl⟩))

/-- Squarings by calls of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def MontS.fnLazyAdx : MontS where
  mm := mmFnAdxLazy aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnAdxLazy_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (mulAdxLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hdx hcx h8 hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by exact mmFnAdxLazy_ct (by unfold Opnds; decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
