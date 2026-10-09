import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.GMul
import VerifiedGarbage.Impl.Ecdh.P192.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-! # p192 multiplication by the base point -/

namespace VG.Proof.Ecdh.AArch64.P192

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64.P192
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdh.AArch64.P192
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192

theorem ladLayQ : LadLay ladderQ size := by
  constructor
  · refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
    have h : ∀ x ∈ ladSlots ladderQ, ∀ y ∈ ladSlots ladderQ,
        x ≠ y → x + 32 ≤ y ∨ y + 32 ≤ x := by decide +kernel
    exact fun x y hx hy => h x hx y hy
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel
  · decide +kernel
  · decide
  · decide +kernel
  · decide
  · decide
  · decide +kernel

theorem ladAQ : LadA ladderQ where
  sl := by decide +kernel
  mod := MP'_A p192
  bits := by decide
  call := by intro f m h; cases h

theorem ladWQ_eq : ladW ladderQ = ladW ladderCfg := rfl

theorem ladderQ_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {P : Point p192.C} (hP : onCurve p192.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed p192 base g s.mem)
    (hpx : sv p192 base s PX < p192.C.p) (hpy : sv p192 base s PY < p192.C.p)
    (hG : Rep p192.C (tmv p192.C 4 base s (p192.sl PX))
      (tmv p192.C 4 base s (p192.sl PY)) (tmv p192.C 4 base s (p192.sl ONEP)) P)
    {k : Nat} (hkl : k < 2 ^ (64 * p192.n))
    (hrx : sv p192 base s RX = 0) (hry : sv p192 base s RY = p192.mont 1)
    (hrz : sv p192 base s RZ = 0)
    (hb3 : sv p192 base s EXPP = p192.mont (3 * p192.C.b))
    (ht₀ : ∀ t < 64 * p192.n, s.mem (off base (bitsAt p192.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder ladderQ) s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base (ladW ladderQ) s.mem s'.mem ∧ ModOkA p192.MP' size p192.C.p s'.mem base ∧
      (∀ x ∈ [p192.sl RX, p192.sl RY, p192.sl RZ], wordsVal s'.mem base x 4 < p192.C.p) ∧
      Rep p192.C (tmv p192.C 4 base s' (p192.sl RX))
        (tmv p192.C 4 base s' (p192.sl RY))
        (tmv p192.C 4 base s' (p192.sl RZ)) (mul k P) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * p192.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, p192.mont x < p192.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x ∈ ladR ladderQ, wordsVal s.mem base x p192.MP'.n < p192.C.p := by
    intro x hx
    have hx' : x ∈ [AP, EXPP, PX, PY, ONEP, RX, RY, RZ].map p192.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv p192 _ s i < p192.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt hb3 (hmont _)
    · exact hpx
    · exact hpy
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt hrx (by omega)
    · exact lt_of_eq_of_lt hry (hmont _)
    · exact lt_of_eq_of_lt hrz (by omega)
  have hR : Rep p192.C (tmv p192.C p192.n base s (p192.sl RX)) (tmv p192.C p192.n base s (p192.sl RY))
      (tmv p192.C p192.n base s (p192.sl RZ)) (mul (k >>> (64 * p192.n)) P) := by
    show Rep p192.C (toM _ _ (sv p192 _ s RX)) (toM _ _ (sv p192 _ s RY)) (toM _ _ (sv p192 _ s RZ)) _
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  have hstep := step_rep (L := ladderQ) (k := k) hC hP (by
      show toM p192.C.p (2 ^ (64 * p192.n)) (wordsVal s.mem _ (p192.sl AP) p192.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM p192.C.p (2 ^ (64 * p192.n)) (sv p192 base s EXPP) = _
      rw [hb3]; exact toM_cmont hc _) hG
  exact WP.mono (ladder_ok ladLayQ ladAQ hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
    fun _ ⟨K, U, M, L, R⟩ => ⟨K, U, M, L, by rw [Nat.shiftRight_zero] at R; exact R⟩

theorem qMul_ok (hc : BaseCfgOk p192) (hC : Law p192.C)
    {P : Point p192.C} (hP : onCurve p192.C P = true)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size)
    (F : Fixed p192 base g s.mem)
    (hpx : sv p192 base s PX < p192.C.p) (hpy : sv p192 base s PY < p192.C.p)
    (hG : Rep p192.C (tmv p192.C 4 base s (p192.sl PX))
      (tmv p192.C 4 base s (p192.sl PY)) (tmv p192.C 4 base s (p192.sl ONEP)) P)
    {k : Nat} (hkl : k < 2 ^ (64 * p192.n))
    (hrx : sv p192 base s RX = 0) (hry : sv p192 base s RY = p192.mont 1)
    (hrz : sv p192 base s RZ = 0)
    (ht₀ : ∀ t < 64 * p192.n, s.mem (off base (bitsAt p192.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa qMul s fun s' => KeepRegs (powClob 4) s s' ∧
      Unch base (slW p192 gSlots) s.mem s'.mem ∧ ModOkA p192.MP' size p192.C.p s'.mem base ∧
      (∀ x ∈ [p192.sl RX, p192.sl RY, p192.sl RZ], wordsVal s'.mem base x 4 < p192.C.p) ∧
      Rep p192.C (tmv p192.C 4 base s' (p192.sl RX))
        (tmv p192.C 4 base s' (p192.sl RY))
        (tmv p192.C 4 base s' (p192.sl RZ)) (mul k P) ∧
      sv p192 base s' EXPP = p192.mont (3 * p192.C.b) := by
  have hn := hs.nowrap
  refine WP.seq (WP.mono (setConst_ok hs (n := 4) (o := p192.sl EXPP)
    (x := p192.mont (3 * p192.C.b)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨b₁, K₁, O₁⟩ => ?_)
  have U₁ : Unch base (slW p192 [EXPP]) s.mem s₁.mem := O₁.unch
  have hs₁ := hs.of_keepRegs K₁ (by decide)
  have F₁ := F.unch hc.n10 hn (fixedOk_slW (l := [EXPP]) (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EXPP → sv p192 base s₁ i = sv p192 base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa using he))
  have ht₁ : ∀ t < 64 * p192.n, s₁.mem (off base (bitsAt p192.n 0 + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [tbl_unch U₁ hc.n10 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
    exact ht₀ t ht
  have eP : ∀ {i}, i < 45 → i ≠ EXPP →
      tmv p192.C 4 base s₁ (p192.sl i) = tmv p192.C 4 base s (p192.sl i) :=
    fun hi he => congrArg (fun x => toM p192.C.p (2 ^ (64 * p192.n)) x) (e₁ hi he)
  refine WP.mono (ladderQ_ok hc hC hP hs₁ F₁
    (by rw [e₁ (by decide) (by decide)]; exact hpx)
    (by rw [e₁ (by decide) (by decide)]; exact hpy)
    (by rw [eP (by decide) (by decide), eP (by decide) (by decide), eP (by decide) (by decide)]; exact hG) hkl
    ((e₁ (by decide) (by decide)).trans hrx) ((e₁ (by decide) (by decide)).trans hry)
    ((e₁ (by decide) (by decide)).trans hrz) b₁ ht₁) fun s' ⟨K, U, M, L, R⟩ =>
      ⟨(K₁.mono (by decide)).trans K, ?_, M, L, R, ?_⟩
  · rw [ladWQ_eq, ladW_eq] at U
    exact U₁.trans U
  · rw [ladWQ_eq, ladW_eq] at U
    exact (sv_unch U hc.n10 hn (i := EXPP) (by decide) (apart_slW (by decide))).trans b₁

end VG.Proof.Ecdh.AArch64.P192
