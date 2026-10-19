module

public import VerifiedGarbage.Impl.Dsa.X86_64.Joint
import VerifiedGarbage.Proof.Dsa.Joint
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # Correctness of a joint two-bit exponentiation window -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure JointTab (m : Mem) (P : Addr) (w n g y : Nat) : Prop where
  tab : word m P (8 * Crt.sTab) = off P (slot w 8)
  lt : ∀ j < 16, wv m P (slot w (8 + j)) w < n
  val : ∀ j < 16, wv m P (slot w (8 + j)) w % n =
    (g ^ (j / 4) * y ^ (j % 4)) * 2 ^ (64 * w) % n

theorem JointTab.of_win {m m' : Mem} {P : Addr} {w n g y : Nat}
    (h : JointTab m P w n g y) (hf : Frm P (crtWinRanges w) m m')
    (hn : P.toNat + (slot w 8 + tabBytes w) ≤ 2 ^ 64) : JointTab m' P w n g y := by
  have he : ∀ j < 16, wv m' P (slot w (8 + j)) w = wv m P (slot w (8 + j)) w := fun j hj =>
    hf.wv_eq (fun r hr => by have := crtWinRanges_ent w j r hr; omega) (by have := ent_le w hj; omega)
  refine ⟨?_, fun j hj => (he j hj).symm ▸ h.lt j hj, fun j hj => (he j hj).symm ▸ h.val j hj⟩
  rw [hf.word_eq (crtWinRanges_hdr w (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by have := hdr_lt_slot w 8 (show Crt.sTab < 32 by decide); omega)]
  exact h.tab

theorem joint_mask (V k : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> k &&& (3 : BitVec 64)) =
      BitVec.ofNat 64 (V / 2 ^ k % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
    Nat.shiftRight_eq_div_pow, show ((3 : BitVec 64)).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem joint_mid_ok {t : State} {P : Addr} {w n xc V : Nat} {minv : BitVec 64}
    (hc : CExpCtx t P w minv n xc)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 60) :
    WP isa (.block Joint.windowIndex) t fun t' =>
      t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (4 * V))).writeW
        (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (4 * (V / 16384 % 4) + V / 64 % 4)) ∧
      Keep [.rax, .rdx, .rcx] t t' := by
  unfold Joint.windowIndex
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t' =>
    t'.mem = (t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (4 * V))).writeW
      (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (4 * (V / 16384 % 4) + V / 64 % 4))) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h, k⟩
  xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sV) (by decide),
    hc.st (i := Crt.sV) (by decide), hc.st (i := Crt.sNib) (by decide), hV,
    joint_mask V 14 (by omega), joint_mask V 6 (by omega), ← BitVec.ofNat_add]
  rw [show V + V + (V + V) = 4 * V by omega]
  congr 2 <;> omega

/-- A Montgomery product adds the two pairs of exponents. -/
theorem joint_mul {out A B g y a b c d R n : Nat} (hR : Nat.Coprime R n)
    (hA : A % n = (g ^ a * y ^ b) * R % n)
    (hB : B % n = (g ^ c * y ^ d) * R % n)
    (h : out * R % n = A * B % n) :
    out % n = (g ^ (a + c) * y ^ (b + d)) * R % n := by
  have hv := VG.Proof.Dsa.mont_product hR hA hB h
  rw [Nat.pow_add, Nat.pow_add]
  rw [hv]
  congr 1
  ac_rfl

/-- The square and table multiply use the same backend and frame as RSA. -/
theorem joint_mont_ok (M : Mont) {t : State} {P : Addr} {w n xc g y a b c d : Nat}
    {minv : BitVec 64} (hc : CExpCtx t P w minv n xc)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    {right : Nat} (hr : right = aY ∨ right = Crt.aT)
    (hB : wv t.mem P (slot w right) w < n)
    (hA : wv t.mem P (slot w aY) w % n = (g ^ a * y ^ b) * 2 ^ (64 * w) % n)
    (hv : wv t.mem P (slot w right) w % n = (g ^ c * y ^ d) * 2 ^ (64 * w) % n) :
    WP isa (M.mm aY aY right) t fun u =>
      CExpCtx u P w minv n xc ∧ wv u.mem P (slot w aY) w < n ∧
      wv u.mem P (slot w aY) w % n = (g ^ (a + c) * y ^ (b + d)) * 2 ^ (64 * w) % n ∧
      (∀ k < 32, word u.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  have hb : right < 8 ∧ right ≠ aAcc ∧ right ≠ aTmp := by rcases hr with rfl | rfl <;> decide
  refine WP.mono (M.ok hc.good (Nat.le_refl _) hw (by omega) (by decide) (by decide) hb.1
    (by decide) (by decide) (by decide) (by decide) hb.2.1 hb.2.2 hc.inv
    (by rw [hc.n]; exact hB)) fun u ⟨_, hl, hm, hf, hk⟩ => ?_
  rw [hc.n] at hl hm
  have f : Frm P (crtWinRanges w) t.mem u.mem := Frm.of_arrays hf (by simp [crtWinRanges])
  exact ⟨hc.of_win f hk.2.2 (hk.gpr (by decide)), hl, joint_mul hR hA hv hm,
    fun k hh => hf.hslot hh, f, hk⟩

/-- A squaring of the accumulator, below `Sq.bd n R` before and after. -/
theorem joint_sq_ok (Sq : MontS) {t : State} {P : Addr} {w n xc g y a b : Nat}
    {minv : BitVec 64} (hc : CExpCtx t P w minv n xc)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hY : wv t.mem P (slot w aY) w < Sq.bd n (2 ^ (64 * w)))
    (hA : wv t.mem P (slot w aY) w % n = (g ^ a * y ^ b) * 2 ^ (64 * w) % n) :
    WP isa Sq.mm t fun u =>
      CExpCtx u P w minv n xc ∧ wv u.mem P (slot w aY) w < Sq.bd n (2 ^ (64 * w)) ∧
      wv u.mem P (slot w aY) w % n = (g ^ (a + a) * y ^ (b + b)) * 2 ^ (64 * w) % n ∧
      (∀ k < 32, word u.mem P (8 * k) = word t.mem P (8 * k)) ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  refine WP.mono (Sq.ok hc.good (Nat.le_refl _) hw (by omega) hc.inv (by rw [hc.n]; exact hY))
    fun u ⟨_, hl, hm, hf, hk⟩ => ?_
  rw [hc.n] at hl hm
  have f : Frm P (crtWinRanges w) t.mem u.mem := Frm.of_arrays hf (by simp [crtWinRanges])
  exact ⟨hc.of_win f hk.2.2 (hk.gpr (by decide)), hl, joint_mul hR hA hA hm,
    fun k hh => hf.hslot hh, f, hk⟩

/-- A pair of two-bit digits advances both exponents with shared squarings. -/
theorem jointWindow_ok (M : Mont) (Sq : MontS) {t : State} {P : Addr} {w n xc g y a b V count : Nat}
    {minv : BitVec 64} (hc : CExpCtx t P w minv n xc) (htab : JointTab t.mem P w n g y)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hY : wv t.mem P (slot w aY) w < n)
    (hYv : wv t.mem P (slot w aY) w % n = (g ^ a * y ^ b) * 2 ^ (64 * w) % n)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 56)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 count) (hb1 : 1 ≤ count) (hb' : count < 2 ^ 31) :
    WP isa (Joint.window Sq.mm M.mm) t fun t' =>
      CExpCtx t' P w minv n xc ∧ JointTab t'.mem P w n g y ∧
      wv t'.mem P (slot w aY) w < n ∧
      wv t'.mem P (slot w aY) w % n =
        (g ^ (4 * a + V / 16384 % 4) * y ^ (4 * b + V / 64 % 4)) * 2 ^ (64 * w) % n ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (4 * V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (count - 1) ∧
      t'.zf = some (decide (count - 1 = 0)) ∧ Frm P (crtWinRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.scrT.nowrap
  have hY0 := slot_le (w := w) (show aY < 8 by decide)
  unfold Joint.window seqs
  have hnR : n ≤ 2 ^ (64 * w) := by rw [← hc.n]; exact Nat.le_of_lt (wv_lt _ _ _ _)
  refine WP.seq (WP.mono (joint_sq_ok Sq hc hw hw' hR (Nat.lt_of_lt_of_le hY (Sq.le hnR)) hYv)
    fun t₁ ⟨hc₁, hY₁, hYv₁, hh₁, f₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (joint_sq_ok Sq hc₁ hw hw' hR hY₁ hYv₁)
    fun t₄ ⟨hc₄, hY₄, hYv₄, hh₄, f₄, k₄⟩ => ?_)
  have hh04 : ∀ k < 32, word t₄.mem P (8 * k) = word t.mem P (8 * k) :=
    fun k hk => (hh₄ k hk).trans (hh₁ k hk)
  have f04 := f₁.trans f₄
  have k04 : Keep mmRegs t t₄ := (k₁.trans k₄).mono (by decide)
  refine WP.seq (WP.mono (joint_mid_ok (V := V) hc₄ (by rw [hh04 _ (by decide)]; exact hV)
    (by omega)) fun t₅ ⟨hm₅, k₅⟩ => ?_)
  have o1 := writeW_outside t₄.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (4 * V)) (by decide)
  have o2 := writeW_outside (t₄.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (4 * V))) P (d := 8 * Crt.sNib)
    (BitVec.ofNat 64 ((4 * (V / 16384 % 4) + V / 64 % 4))) (by decide)
  rw [← hm₅] at o2
  have f₅ : Frm P (crtWinRanges w) t₄.mem t₅.mem :=
    (Frm.of_outside o1 (by simp [crtWinRanges])).trans (Frm.of_outside o2 (by simp [crtWinRanges]))
  have hc₅ := hc₄.of_win f₅ k₅.2.2 (k₅.gpr (by decide))
  have htab₅ : JointTab t₅.mem P w n g y := htab.of_win (f04.trans f₅) hn
  have hY₅ : wv t₅.mem P (slot w aY) w = wv t₄.mem P (slot w aY) w := by
    rw [o2.wv (by have := hdr_lt_slot w aY (show Crt.sNib < 32 by decide); omega_arith) (by omega_arith),
      o1.wv (by have := hdr_lt_slot w aY (show Crt.sV < 32 by decide); omega_arith) (by omega_arith)]
  have hh₅ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sNib → word t₅.mem P (8 * k) = word t.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [hm₅, hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hk (Ne.symm h1),
        hh04 k hk]
  have idx := VG.Proof.Dsa.joint_index (Nat.mod_lt (V / 16384) (by decide)) (Nat.mod_lt (V / 64) (by decide))
  have hv16 := idx.1
  -- `T := T_v`.
  refine WP.seq (WP.mono (tabSel_ok hc₅ hw hw' hv16 (by rw [hh₅ _ (by decide) (by decide) (by decide)]; exact htab.tab)
    (by rw [hm₅, word_writeW_self])) fun t₆ ⟨hc₆, hT₆, f₆, k₆⟩ => ?_)
  have f₆' : Frm P (crtWinRanges w) t₅.mem t₆.mem := f₆.mono (selRanges_sub w)
  have hY₆ : wv t₆.mem P (slot w aY) w = wv t₅.mem P (slot w aY) w :=
    f₆.wv_eq (fun r hr => by
      have := slot_sep (w := w) (show aY ≠ Crt.aT by decide)
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn]; have := hdr_lt_slot w aY (show 31 < 32 by decide); omega_arith
      · simp only [Crt.sJ, sFn]; have := hdr_lt_slot w aY (show 31 < 32 by decide); omega_arith) (by omega_arith)
  have hh₆ : ∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → word t₆.mem P (8 * k) = word t₅.mem P (8 * k) :=
    fun k hk h1 h2 => f₆.word_eq (fun r hr => by
      have := hdr_lt_slot w Crt.aT hk
      simp only [selRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only; omega_arith
      · simp only [Crt.sEnt, sFn] at h1 ⊢; omega_arith
      · simp only [Crt.sJ, sFn] at h2 ⊢; omega_arith) (by omega_arith)
  have htab₆ : JointTab t₆.mem P w n g y := htab₅.of_win f₆' hn
  simp only [seqs]
  -- `Y := Y T`.
  refine WP.seq (WP.mono (joint_mont_ok M (g := g) (y := y) (a := 4 * a) (b := 4 * b)
    (c := V / 16384 % 4) (d := V / 64 % 4) hc₆ hw hw' hR (Or.inr rfl)
    (by rw [hT₆]; exact htab₅.lt _ hv16)
    (by rw [hY₆, hY₅]; simpa only [show a + a + (a + a) = 4 * a by omega,
      show b + b + (b + b) = 4 * b by omega] using hYv₄)
    (by rw [hT₆]; have hv := htab₅.val _ hv16; rw [idx.2.1, idx.2.2] at hv; exact hv))
    fun t₇ ⟨hc₇, hY₇, hYv₇, hh₇, f₇, k₇⟩ => ?_)
  -- The count.
  refine WP.mono (crtBitEnd_ok hc₇ (by
    rw [hh₇ _ (by decide), hh₆ _ (by decide) (by decide) (by decide), hh₅ _ (by decide) (by decide) (by decide)]
    exact hb) hb1 hb') fun t' ⟨hm', hz', k'⟩ => ?_
  have o₈ := writeW_outside t₇.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (count - 1)) (by decide)
  rw [← hm'] at o₈
  have f₈ : Frm P (crtWinRanges w) t₇.mem t'.mem := Frm.of_outside o₈ (by simp [crtWinRanges])
  have fall : Frm P (crtWinRanges w) t.mem t'.mem := (((f04.trans f₅).trans f₆').trans f₇).trans f₈
  refine ⟨hc₇.of_win f₈ k'.2.2 (k'.gpr (by decide)), htab.of_win fall hn, ?_, ?_, ?_, ?_, hz', fall,
    ((((k04.trans k₅).trans k₆).trans k₇).trans k').mono (by decide)⟩
  · rw [o₈.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]; exact hY₇
  · rw [o₈.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_arith) (by omega_arith)]
    exact hYv₇
  · rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hh₇ _ (by decide),
      hh₆ _ (by decide) (by decide) (by decide), hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]
  · rw [hm', word_writeW_self]

end VG.Proof.Dsa.X86_64
