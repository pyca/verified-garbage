module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.BaseSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.BaseSquareDiag
import VerifiedGarbage.Proof.Bignum.X86_64.BaseSquareRedc
public import VerifiedGarbage.Impl.Bignum.X86_64.BaseSquare

/-!
# The baseline Montgomery square (x86-64)

`BaseSquare.square`: `[o] ≡ [a]² R⁻¹ (mod m)` from `basesR`'s registers,
below `R`, and below `m` if `[a] < m` (`square_ok`), as `mmTailLazy_ok` says
of `montMul`'s rounds; and `BaseSquare.mulTail`, which takes the square for
`a = b` and the rounds otherwise (`tail_ok`). The square writes the vector
registers `stashed` only.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.BaseSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.BaseSquare VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The vector registers `stash` writes. -/
def stashed : List XReg := [.xmm14, .xmm15, .xmm0, .xmm1, .xmm2, .xmm3]

theorem xmm_setXmm (s : State) (r r' : XReg) (v : BitVec 128) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

theorem stash_ok (s : State) :
    WP isa (.block stash) s fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.mem = s.mem ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2, k⟩
  unfold stash
  xrun [XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm]
  simp only [xmm_setXmm, reduceCtorEq, ite_true, ite_false, true_and]
  intro x hx
  simp only [stashed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp only [hx, ite_false]

/-- `square` up to the reduction: `[a]²` at `aAcc + 16`, over `2 w` words,
the vector registers stashed. -/
theorem sqRaw_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (h9 : s.gpr .r9 = off B (slot w a)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa raw s fun t =>
      wv t.mem B (slot w aAcc + 16) (2 * w) = wv s.mem B (slot w a) w * wv s.mem B (slot w a) w ∧
      wv t.mem B (slot w aAcc + 16 + 8 * (2 * w)) 2 = 0 ∧
      Outside B (slot w aAcc + 16) (8 * (2 * w + 2)) s.mem t.mem ∧ t.gpr .r8 = off B (slot w aAcc + 16) ∧
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  let A := slot w aAcc + 16
  let eb := slot w a
  have hA : A + 8 * (2 * w + 2) ≤ Z := by
    have := slot_le (w := w) (show aTmp < 8 by decide)
    unfold A slot aAcc aTmp at *
    omega
  have hb : eb + 8 * w ≤ Z := by have := slot_le (w := w) ha; omega
  have sb : eb + 8 * w ≤ A ∨ A + 8 * (2 * w + 2) ≤ eb := by
    have := slot_sep (w := w) ha1
    have := slot_sep (w := w) ha2
    unfold A eb slot aAcc aTmp at *
    omega
  unfold raw
  -- The stash, and the cross products' registers.
  have pS : WP isa (.block (stash ++ ([.mov .rbx (.reg .r12), .alu .add .r8 (.imm 16)] : List Instr))) s fun t =>
      t.xmm .xmm14 = (0 : BitVec 64) ++ s.gpr .rbx ∧ t.xmm .xmm15 = (0 : BitVec 64) ++ s.gpr .r15 ∧
      t.xmm .xmm0 = (0 : BitVec 64) ++ s.gpr .r12 ∧ t.xmm .xmm1 = (0 : BitVec 64) ++ s.gpr .r8 ∧
      t.xmm .xmm2 = (0 : BitVec 64) ++ s.gpr .r10 ∧ t.xmm .xmm3 = (0 : BitVec 64) ++ s.gpr .rsi ∧
      (∀ x, x ∉ stashed → t.xmm x = s.xmm x) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B A ∧
      t.mem = s.mem ∧ Keep [.rbx, .r8] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (stash_ok s) fun u ⟨x14, x15, x0, x1, x2, x3, xo, hm, k⟩ => ?_
    refine WP.mono (WP.vecKeep (by decide) (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B A ∧ t.mem = u.mem) (by xrun [(k.gpr (by decide) : u.gpr .r12 = _).trans h12,
        (k.gpr (by decide) : u.gpr .r8 = _).trans h8, off_add16]; rfl) rfl))
      fun t ⟨⟨⟨hbx, h8', hm'⟩, k'⟩, hx, _⟩ => ?_
    rw [hx]
    exact ⟨x14, x15, x0, x1, x2, x3, xo, hbx, h8', hm'.trans hm, (k.trans k').mono (by decide)⟩
  refine WP.seq (WP.mono pS fun s₁ ⟨x14, x15, x0, x1, x2, x3, xo, hbx₁, h8₁, hm₁, k₁⟩ => ?_)
  have h9₁ : s₁.gpr .r9 = off B eb := (k₁.gpr (by decide)).trans h9
  -- The cross products.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (AdxSquare.crossWith_ok row_rowOk (hs.congr k₁.2.2) h8₁ h9₁ hbx₁
    hw (by omega) hA hb sb)) fun s₂ ⟨⟨hv₂, ho₂, hz₂, k₂⟩, hx₂, _⟩ => ?_)
  rw [hm₁] at hv₂ ho₂
  have k12 := k₁.trans k₂
  have h9₂ : s₂.gpr .r9 = off B eb := (k₂.gpr (by decide)).trans h9₁
  have read₂ : ∀ j < w, word s₂.mem B (eb + 8 * j) = word s.mem B (eb + 8 * j) :=
    fun j hj => ho₂.word (by omega) (by omega)
  have lo₂ : wv s₂.mem B A (2 * w) = AdxSquare.crossValue s.mem B eb w := by
    have zero₂ : wv s₂.mem B (A + 8 * (2 * w)) 2 = 0 := wv_zero fun k hk => by
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega]
      exact hz₂ _ (by omega) (by omega)
    rw [wv_add, zero₂, Nat.mul_zero, Nat.add_zero] at hv₂
    exact hv₂
  -- The diagonal's registers.
  have pD : WP isa (.block [.movqR .r8 .xmm1, .alu .add .r8 (.imm 16), .movqR .r10 .xmm0]) s₂ fun t =>
      t.gpr .r8 = off B A ∧ t.gpr .r10 = BitVec.ofNat 64 w ∧ t.mem = s₂.mem ∧ Keep [.r8, .r10] s₂ t := by
    refine WP.mono (WP.keep [.r8, .r10] (Q := fun t => t.gpr .r8 = off B A ∧ t.gpr .r10 = BitVec.ofNat 64 w ∧
      t.mem = s₂.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
    xrun [hx₂, x1, x0, h8, h12, movq_lo, off_add16, RegUpd.xmm_setReg, RegUpd.xmm_setFlags]
    rfl
  refine WP.seq (WP.mono (WP.vecKeep (by decide) pD) fun s₃ ⟨⟨h8₃, h10₃, hm₃, k₃⟩, hx₃, _⟩ => ?_)
  have k13 := k12.trans k₃
  -- The diagonal.
  refine WP.mono (WP.vecKeep (by decide) (AdxSquare.diagonalWith_ok core_coreOk (hs.congr k13.2.2) h8₃
    ((k₃.gpr (by decide)).trans h9₂) h10₃ (by omega) (by omega) (by omega) hb (by omega)))
    fun t ⟨⟨hv, ho, kt⟩, hxt, _⟩ => ?_
  rw [hm₃] at hv ho
  rw [lo₂, AdxSquare.diagonalValue_congr read₂, AdxSquare.square_decomposition] at hv
  have bound : wv s.mem B eb w * wv s.mem B eb w < 2 ^ (128 * w) := by
    have hl := wv_lt s.mem B eb w
    have hp := Nat.mul_lt_mul'' hl hl
    rw [← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega] at hp
    exact hp
  have carry : (t.gpr .r15).toNat = 0 := by
    by_contra hc
    have hc' : 1 ≤ (t.gpr .r15).toNat := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (128 * w)) hc'
    simp only [Nat.mul_one] at hm
    omega
  have hxs : t.xmm = s₁.xmm := by rw [hxt, hx₃, hx₂]
  refine ⟨?_, ?_, ho₂.trans (ho.mono (o' := A) (n' := 8 * (2 * w + 2)) (Nat.le_refl _) (by omega)),
    (kt.gpr (by decide)).trans h8₃, by rw [hxs]; exact x14, by rw [hxs]; exact x15, by rw [hxs]; exact x0,
    by rw [hxs]; exact x1, by rw [hxs]; exact x2, by rw [hxs]; exact x3, fun x hx => by rw [hxs]; exact xo x hx,
    (k13.trans kt).mono (by decide)⟩
  · rw [carry, Nat.mul_zero, Nat.add_zero] at hv
    exact hv
  · exact wv_zero fun k hk => by
      rw [ho.word (by omega) (by omega)]
      rw [show A + 8 * (2 * w) + 8 * k = A + 8 * (2 * w + k) by omega]
      exact hz₂ _ (by omega) (by omega)

theorem unstash_ok {s : State} {B : Addr} {o e : Nat} {w : Nat} {eN : Nat}
    (x0 : s.xmm .xmm0 = (0 : BitVec 64) ++ BitVec.ofNat 64 w) (x1 : s.xmm .xmm1 = (0 : BitVec 64) ++ off B e)
    (x2 : s.xmm .xmm2 = (0 : BitVec 64) ++ off B eN) (x14 : s.xmm .xmm14 = (0 : BitVec 64) ++ off B o) :
    WP isa (.block unstash) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B e ∧ t.gpr .r10 = off B eN ∧ t.gpr .rbx = off B o ∧
        t.mem = s.mem ∧ Keep [.r12, .rsi, .r10, .rbx] s t := by
  refine WP.mono (WP.keep [.r12, .rsi, .r10, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
    t.gpr .rsi = off B e ∧ t.gpr .r10 = off B eN ∧ t.gpr .rbx = off B o ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold unstash
  xrun [x0, x1, x2, x14, movq_lo, RegUpd.xmm_setReg]

/-- `square`: `[o] ≡ [a]² R⁻¹ (mod m)`, below `R`, and below `m` if `[a] < m`, from
`basesR`'s registers, `r9` the base of `a`, as `mmTailLazy_ok` says of the rounds. -/
theorem square_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hbx : s.gpr .rbx = off B (slot w o)) (h9 : s.gpr .r9 = off B (slot w a))
    (h10 : s.gpr .r10 = off B (slot w aN)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = minv) (hsi : s.gpr .rsi = off B (slot w aTmp))
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa square s fun t =>
      wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x) := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hAT : slot w aAcc + 16 + 8 * w = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hNA : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hTs := sl aTmp (by decide)
  have hN0 : 0 < wv s.mem B (slot w aN) w := wv_pos_of_inv (by omega) hinv
  have soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega
  unfold square
  refine WP.seq (WP.mono (sqRaw_ok hs hZ hw hw' ha ha1 ha2 h9 h8 h12)
    fun s₁ ⟨hv₁, _, ho₁, h8₁, x14, x15, x0, x1, x2, x3, xo, k₁⟩ => ?_)
  have hNw : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega) (by omega)
  have hNv : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega) (by omega)
  -- The reduction.
  refine WP.seq (WP.mono (redc_ok (A := slot w aAcc + 16) (eN := slot w aN) (minv := minv)
    (hs.congr k₁.2.2) h8₁ (by rw [x0, h12]) (by rw [x2, h10]) (by rw [x15, h15]) (by rw [x3, hsi, hAT])
    (by omega) (by omega) (by omega) hw' (by rw [hNw]; exact hinv))
    fun s₂ ⟨⟨q, hq, heq⟩, ho₂, h8₂, hx₂, k₂⟩ => ?_)
  rw [hAT, hv₁, hNv] at heq
  rw [hAT] at h8₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  -- The registers of the subtraction and the selection.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (unstash_ok (s := s₂) (B := B) (w := w) (e := slot w aAcc)
    (eN := slot w aN) (o := slot w o) (by rw [hx₂, x0, h12]) (by rw [hx₂, x1, h8]) (by rw [hx₂, x2, h10])
    (by rw [hx₂, x14, hbx]))) fun s₃ ⟨⟨h12₃, hsi₃, h10₃, hbx₃, hm₃, k₃⟩, hx₃, _⟩ => ?_)
  have h8₃ : s₃.gpr .r8 = off B (slot w aTmp) := (k₃.gpr (by decide)).trans h8₂
  -- `T - m`.
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (subMod_ok (hs₂.congr k₃.2.2) h8₃ h10₃ hsi₃ h12₃ (by omega) hw' (by omega)
    (by have := sl aN (by decide); omega) (by have := sl aAcc (by decide); omega) (by omega) (by omega)))
    fun s₄ ⟨⟨c, lt, hbp, hlt, hD, ho₄, k₄⟩, hx₄, _⟩ => ?_)
  rw [hm₃] at hlt hD ho₄
  -- The selection.
  refine WP.mono (WP.vecKeep (by decide) (selectAcc_ok (hs₂.congr (k₃.trans k₄).2.2) ((k₄.gpr (by decide)).trans h8₃)
    ((k₄.gpr (by decide)).trans hsi₃) ((k₄.gpr (by decide)).trans hbx₃) ((k₄.gpr (by decide)).trans h12₃) hbp
    (by omega) hw' (by omega) (by have := sl aAcc (by decide); omega) (by have := sl o ho; omega)
    (by omega) (by omega))) fun t ⟨⟨hv, hot, k₅⟩, hx₅, _⟩ => ?_
  -- The words of `T` (at `aTmp`), as after the reduction.
  have hT₄ : wv s₄.mem B (slot w aTmp) w = wv s₂.mem B (slot w aTmp) w :=
    ho₄.wv (by unfold slot aAcc aTmp; omega) (by omega)
  have hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    (ho₂.wv (by omega) (by omega)).trans hNv
  rw [hN₂] at hD
  have hsel : wv t.mem B (slot w o) w = if (word s₂.mem B (slot w aTmp + 8 * w)).toNat < c.toNat then
      wv s₂.mem B (slot w aTmp) w else wv s₄.mem B (slot w aAcc) w := by
    rw [hv, hT₄, hlt]
    by_cases h : (word s₂.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  have hNR := wv_lt s.mem B (slot w aN) w
  have hAR := wv_lt s.mem B (slot w a) w
  have hR0 : 0 < 2 ^ (64 * w) := Nat.two_pow_pos _
  rw [wv_top2] at heq
  have hTlt : wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
      2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) < wv s.mem B (slot w aN) w + 2 ^ (64 * w) := by
    have := redc_lt_add hq (Nat.mul_lt_mul'' hAR hAR) heq
    omega
  obtain ⟨hlz, hlm⟩ := VG.Proof.Bignum.csub_lazy (Tl := wv s₂.mem B (slot w aTmp) w)
      (Tw := (word s₂.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₄.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      hNR (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _) hTlt hD
  refine ⟨?_, fun hA => ?_, ?_, ?_, ((k12.trans (k₃.trans k₄)).trans k₅).mono (by decide), fun x hx => ?_⟩
  · rw [hsel]; exact hlz
  · have h2m : wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
        2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) < 2 * wv s.mem B (slot w aN) w := by
      generalize wv s₂.mem B (slot w aTmp) w + 2 ^ (64 * w) * ((word s₂.mem B (slot w aTmp + 8 * w)).toNat +
        2 ^ 64 * (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) = T at heq ⊢
      have hX : wv s.mem B (slot w a) w * wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w * 2 ^ (64 * w) :=
        Nat.mul_lt_mul'' hA hAR
      have hqm : q * wv s.mem B (slot w aN) w < 2 ^ (64 * w) * wv s.mem B (slot w aN) w :=
        Nat.mul_lt_mul_of_pos_right hq hN0
      have hb : 2 ^ (64 * w) * T < 2 ^ (64 * w) * (2 * wv s.mem B (slot w aN) w) := by
        rw [heq, Nat.mul_comm (wv s.mem B (slot w aN) w) (2 ^ (64 * w)) ] at *
        rw [show 2 ^ (64 * w) * (2 * wv s.mem B (slot w aN) w) =
          2 ^ (64 * w) * wv s.mem B (slot w aN) w + 2 ^ (64 * w) * wv s.mem B (slot w aN) w by grind]
        omega
      exact Nat.lt_of_mul_lt_mul_left hb
    rw [hsel, VG.Proof.Bignum.csub_result (Tl := wv s₂.mem B (slot w aTmp) w)
      (Tw := (word s₂.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s₂.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₄.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      hNR (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _) h2m hD]
    exact Nat.mod_lt _ hN0
  · rw [hsel, Nat.mul_mod, hlm, ← Nat.mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    rw [hot x (by omega), ho₄ x (by unfold slot aAcc aTmp at *; omega)]
    rw [ho₂ x (by unfold slot aAcc aTmp at *; omega), ho₁ x (by unfold slot aAcc aTmp at *; omega)]
  · rw [hx₅, hx₄, hx₃, hx₂]; exact xo x hx

/-- `cmp r11, r9`: ZF for the bases of `a` and `b`, so for `a = b`. -/
theorem cmpBases_ok {s : State} {B : Addr} {Z w a b : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z)
    (ha : a < 8) (hb : b < 8) (h11 : s.gpr .r11 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w b)) :
    WP isa (.block [.alu .cmp .r11 (.reg .r9)]) s fun t =>
      t.zf = some (decide (a = b)) ∧ t.gpr .r11 = off B (slot w a) ∧ t.mem = s.mem ∧ Keep [.r11] s t := by
  have hn := hs.nowrap
  have hsa := slot_le (w := w) ha
  have hsb := slot_le (w := w) hb
  have hab : decide (slot w a = slot w b) = decide (a = b) := by
    by_cases h : a = b
    · subst h; simp
    · have := slot_sep (w := w) h
      simp only [h, decide_false, decide_eq_false_iff_not]
      omega
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.zf = some (decide (a = b)) ∧ t.gpr .r11 = off B (slot w a) ∧
    t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [h11, h9, off_sub_beq B (show slot w a < 2 ^ 64 by omega) (show slot w b < 2 ^ 64 by omega), hab]

/-- `mulTail`: what `mmTailLazy_ok` says of `montMul`'s rounds, by the rounds or,
for `a = b`, the square, which writes no vector register but `stashed`. -/
theorem tail_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hbx : s.gpr .rbx = off B (slot w o)) (h11 : s.gpr .r11 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w b))
    (h10 : s.gpr .r10 = off B (slot w aN)) (h8 : s.gpr .r8 = off B (slot w aAcc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = minv) (hsi : s.gpr .rsi = off B (slot w aTmp))
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulTail s fun t =>
      wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x) := by
  unfold mulTail
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (cmpBases_ok hs hZ ha hb h11 h9))
    fun s₁ ⟨⟨hz, h11₁, hm₁, k₁⟩, hx₁, _⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  rw [← hm₁] at hinv ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t ∧ (∀ x, x ∉ stashed → t.xmm x = s₁.xmm x)) →
      (wv t.mem B (slot w o) w < 2 ^ (64 * w) ∧
      (wv s₁.mem B (slot w b) w < wv s₁.mem B (slot w aN) w → wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w) ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t ∧ (∀ x, x ∉ stashed → t.xmm x = s.xmm x)) :=
    fun t ⟨h1, h2, h3, h4, k, hx⟩ => ⟨h1, h2, h3, h4, (k₁.trans k).mono (by decide), fun x h => (hx x h).trans
      (by rw [hx₁])⟩
  have r : ∀ {r : Reg}, r ≠ .r11 → s₁.gpr r = s.gpr r := fun h => k₁.gpr (by simp [h])
  by_cases hab : a = b
  · subst b
    refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (by simp)
    exact WP.mono (square_ok hs₁ hZ hw hw' ho ha ho1 ho2 ha1 ha2 ((r (by decide)).trans hbx)
      ((r (by decide)).trans h9) ((r (by decide)).trans h10) ((r (by decide)).trans h8) ((r (by decide)).trans h12)
      ((r (by decide)).trans h15) ((r (by decide)).trans hsi) hinv) post
  · refine WP.ite false (by simp [eval, hz, hab]) (by simp) (fun _ => ?_)
    refine WP.mono (WP.vecKeep (by decide) (mmTailLazy_ok hs₁ hZ hw hw' (by decide) (by decide) (by decide) ho ha
      hb (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1) (by decide) (Ne.symm ho2)
      ((r (by decide)).trans hbx) h11₁ ((r (by decide)).trans h9) ((r (by decide)).trans h10)
      ((r (by decide)).trans h8) ((r (by decide)).trans h12) ((r (by decide)).trans h15) ((r (by decide)).trans hsi)
      hinv)) fun t ⟨⟨h1, h2, h3, h4, k⟩, hx, _⟩ => post t ⟨h1, h2, h3, h4, k, fun x _ => by rw [hx]⟩
end VG.Proof.Bignum.X86_64.BaseSquare
