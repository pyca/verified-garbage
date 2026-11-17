module

import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Impl.Ecdh.X86.WinJac
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacLoop
import VerifiedGarbage.Proof.Ecdh.X86.JacLayout
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowLayout
public import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState

/-! ### `Ecdh.X86.JacWrites`, which this module and modules that import it used -/

section

/-! Memory written by the Jacobian ECDH multiplier. -/

@[expose] public section

namespace VG.Proof.Ecdh.X86
open VG VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Ecdsa.Verify.X86
variable {c : Cfg}

abbrev jwinW (c : Cfg) : List (Nat × Nat) := windowW c ++ [(5200,2560)]

theorem jwinW_fixed (h4 : c.n=4) : FixedOk c (jwinW c) := by
  refine (windowW_fixed h4).append ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  right
  rw [sl_eq,h4]
  decide

theorem jwinW_apart (h4 : c.n=4) {i : Nat} (hi : i<45) (hw : i∉windowSlots) :
    ∀ w∈jwinW c,c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
  refine apart_append (windowW_apart h4 hi hw) ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  left
  rw [sl_eq,h4]
  dsimp only
  omega_using [hi]

theorem jwinW_table (h4 : c.n=4) {t : Nat} (ht : t<64*c.n) :
    ∀ w∈jwinW c,bitsAt c.n 1+t+1≤w.1 ∨ w.1+w.2≤bitsAt c.n 1+t := by
  refine apart_append (windowW_table h4 ht) ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  left
  rw [bitsAt_eq,h4]
  rw [h4] at ht
  dsimp only
  omega_using [ht]

theorem jwinW_cover (h4 : c.n=4) :
    ∀ w∈JWin.allW (Impl.Ecdh.X86.Cfg.jwinCfg c) (Mont.own c.n),
      ∃ w'∈jwinW c,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  simp only [JWin.allW,JWin.loopW,progW,jwinW,windowW,slW,
    List.map_cons,List.map_nil,List.forall_mem_append,List.forall_mem_map,
    List.forall_mem_cons,Mont.outW]
  jwin_layout h4

end VG.Proof.Ecdh.X86

end

end

/-! ### `Ecdh.X86.JacPrep`, which only this module used -/

section

/-! # Scalar recoding for the x86 P-256 variable-base window -/

@[expose] public section

namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86
variable {c : Impl.Ecdsa.X86.Cfg}

/-- Recoding preserves the original scalar and all existing arithmetic slots. -/
theorem jwinPrep_ok (h4 : c.n = 4) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (Impl.Ecdh.X86.Cfg.jwinPrep c) s fun u =>
      (∀ t < 260, u.mem (off base (Impl.Ecdh.X86.Cfg.windowBits + t)) =
        if (sv c base s K + JacWinCfg.offset 52).testBit t then 1 else 0) ∧
      Keeps [.eax, .ebx, .edx, .esi] s u ∧
      Unch base [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)] s.mem u.mem := by
  obtain hi : K<45 := by decide
  have hn := hs.nowrap
  obtain hv : c.sl K + 32 ≤ 3520 := by rw [sl_eq, h4]; omega_using [hi]
  obtain hvsize : c.sl K + 32 ≤ size := by change _ ≤ 8192; omega_using [hv]
  unfold Impl.Ecdh.X86.Cfg.jwinPrep
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 8 hs (o := 3520) (by decide) hvsize (Or.inr hv))
    fun s₁ ⟨v₁, k₁, O₁⟩ => ?_))
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ (n := 1) (o := 3552) (x := 0)
    (by decide) (by decide)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  obtain padded : wordsVal s₂.mem base 3520 5 = sv c base s K := by
    rw [wordsVal_succ_top]
    obtain top : (word s₂.mem base 3552).toNat = 0 := by
      simpa only [wordsVal, Nat.mul_zero, Nat.add_zero] using v₂
    change wordsVal s₂.mem base 3520 4 + 2 ^ 256 * (word s₂.mem base 3552).toNat = _
    rw [top, Nat.mul_zero, Nat.add_zero, wordsVal_eq_val32,
      O₂.val32 (by omega_using []) (by decide), v₁]
    change _ = wordsVal s.mem base (c.sl K) c.n
    rw [wordsVal_eq_val32, h4]
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₂ (n := 5) (o := 3560) (x := JacWinCfg.offset 52)
    (by decide) (by decide +kernel)) fun s₄ ⟨vb, k₃, O₃⟩ => ?_)
  obtain va : wordsVal s₄.mem base 3520 5 = sv c base s K :=
    (O₃.wordsVal (by omega_using []) (by decide)).trans padded
  obtain k₄ := (k₁.trans k₂).trans k₃
  obtain O₄ : Outside base 3520 120 s.mem s₄.mem :=
    ((O₁.mono (by decide) (by decide)).trans (O₂.mono (by decide) (by decide))).trans
      (O₃.mono (by decide) (by decide))
  obtain hs₄ := hs.of_keeps k₄ (by decide)
  rw [chain_eq]
  refine WP.mono (chainAdd_ok hs₄ (acc := 3600) (a := 3520) (b := 3560) 9
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨O₅, ⟨carry, _, v₅⟩, k₅⟩ => ?_
  obtain ha : val32 s₄.mem base 3520 10 = sv c base s K := by
    rw [← wordsVal_eq_val32 (n := 5)]; exact va
  obtain hb : val32 s₄.mem base 3560 10 = JacWinCfg.offset 52 := by
    rw [← wordsVal_eq_val32 (n := 5)]; exact vb
  rw [ha, hb] at v₅
  obtain hvlt : sv c base s K < 2 ^ 256 := by
    have := wordsVal_lt s.mem base (c.sl K) c.n
    change wordsVal s.mem base (c.sl K) c.n < 2 ^ 256
    rw [h4] at *
    exact this
  obtain hoff : JacWinCfg.offset 52 < 2 ^ 261 := by decide +kernel
  obtain value : wordsVal s₅.mem base 3600 5 = sv c base s K + JacWinCfg.offset 52 := by
    rw [wordsVal_eq_val32]
    obtain hsum : sv c base s K + JacWinCfg.offset 52 < 2 ^ (32 * (9 + 1)) :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add hvlt hoff) (by decide +kernel)
    obtain radix : (2 : Nat) ^ (32 * (9 + 1)) = 2 ^ 256 * 2 ^ 64 := by decide +kernel
    simp only [radix] at v₅ hsum
    cases carry with
    | false => simpa only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using v₅
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one] at v₅
      rw [← v₅] at hsum
      exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left _ _) hsum)
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (bits_ok hs₅ (n := 5) (src := 3600) (dst := Impl.Ecdh.X86.Cfg.windowBits)
    (by decide) (by decide) (by decide) (by decide)) fun u ⟨bits, ku, Ou⟩ => ?_
  refine ⟨fun t ht => ?_, (k₄.trans k₅).mono (by decide) |>.trans ku,
    ((O₄.trans (O₅.mono (by decide) (by decide))).unch).trans (Ou.unch)⟩
  rw [bits t (by omega_using [ht]), value]

end VG.Proof.Ecdh.X86

end

end


/-! # The x86 P-256 variable-base product -/

@[expose] public section

namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.Verify.X86 Spec.Weierstrass
variable {c : Impl.Ecdsa.X86.Cfg}

/-- The Jacobian product is canonical for every scalar and correct for valid scalars. -/
theorem jwinMul_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C) (hM3 : AM3 c.C)
    (hO : PrimeOrder c.C) (hn17 : c.C.n % 32 = 17) (hn64 : 64 ≤ c.C.n)
    {s : State} {base : Addr} {g : Reg → BitVec 32} (hs : Scr s base size) (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true) (hP0 : P ≠ .infinity)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (Impl.Ecdh.X86.Cfg.jwinMul c) s fun u =>
      Keeps powClob s u ∧ Unch base (jwinW c) s.mem u.mem ∧
      ModOkW c.MP' size c.C.p u.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u.mem base x c.n < c.C.p) ∧
      (sv c base s K < c.C.n → Rep c.C (tmv c.C c.n base u (c.sl RX)) (tmv c.C c.n base u (c.sl RY))
        (tmv c.C c.n base u (c.sl RZ)) (mul (sv c base s K) P)) := by
  have hn := hs.nowrap
  have hp := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hpx])
  unfold Impl.Ecdh.X86.Cfg.jwinMul
  refine WP.seq (WP.mono (setConst_ok hs (sl_le c hc.n10 (i := EM) (by decide))
    (Nat.lt_trans (hmont _) hc.p_lt)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_)
  change sv c base s₁ EM = c.mont c.C.b at v₁
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have U₁ : Unch base (slW c [EM]) s.mem s₁.mem := O₁.unch
  obtain F₁ := F.unch hc.n10 hn (fixedOk_slW (by decide)) U₁
  obtain e₁ : ∀ {i}, i < 45 → i ≠ EM → sv c base s₁ i = sv c base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa only [List.mem_singleton] using he))
  refine WP.seq (WP.mono (jwinPrep_ok h4 hs₁) fun s₂ ⟨bits, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₂ := O₂
  obtain ap₂ : ∀ {i}, i < 45 → ∀ w ∈ [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)],
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    left; rw [sl_eq, h4]
    rcases hw with rfl | rfl <;> dsimp only [Impl.Ecdh.X86.Cfg.windowBits] <;> omega_using [hi]
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s₁ i :=
    fun hi => sv_unch U₂ hc.n10 hn hi (ap₂ hi)
  obtain F₂ := F₁.unch hc.n10 hn (show FixedOk c [(3520, 120), (Impl.Ecdh.X86.Cfg.windowBits, 320)] from by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    right; rw [sl_eq, h4]; rcases hw with rfl | rfl <;> decide) U₂
  obtain tv : ∀ {i}, i < 45 → i ≠ EM → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi he
    change toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [e₂ hi, e₁ hi he]
  obtain hlt : ∀ x∈JWin.ro (Impl.Ecdh.X86.Cfg.jwinCfg c),wordsVal s₂.mem base x c.n<c.C.p := by
    intro x hx
    change x ∈ [c.sl AP,c.sl EM,c.sl PX,c.sl PY,c.sl ONEP,c.sl ZERO] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact F₂.ap ▸ hmont _
    · change sv c base s₂ EM < _
      rw [e₂ (by decide),v₁]; exact hmont _
    · change sv c base s₂ PX < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpx
    · change sv c base s₂ PY < _
      rw [e₂ (by decide),e₁ (by decide) (by decide)]; exact hpy
    · rw [F₂.onep]; exact Nat.mod_lt _ (by omega_using [hpx])
    · rw [F₂.zero]; omega_using [hpx]
  obtain hz : tmv c.C c.n base s₂ (c.sl ONEP)=1 := by
    change toM _ _ (wordsVal s₂.mem base (c.sl ONEP) c.n)=1
    rw [F₂.onep]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  obtain hQ₂ : Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY)) 1 P := by
    rw [← hz,tv (by decide) (by decide),tv (by decide) (by decide),tv (by decide) (by decide)]
    exact hQ
  obtain hJ : InvJ c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
      (tmv c.C c.n base s₂ (c.sl ONEP)) P := by
    rw [hz,Rep.eq_affine hC hQ₂]
    exact InvJ.affine hC _ _
  have hoff : JacWinCfg.offset 52 = 16*Window5.geom 52 := Window5.offset_eq.symm
  obtain hb : ∀ t<260,s₂.mem (off base (Impl.Ecdh.X86.Cfg.windowBits+t))=
      if (sv c base s K+16*Window5.geom 52).testBit t then 1 else 0 := by
    intro t ht
    rw [bits t ht,e₁ (by decide) (by decide),hoff]
  obtain hrec : sv c base s K+16*Window5.geom 52<32^52 := by
    apply Window5.recode_lt
    change wordsVal s.mem base (c.sl K) c.n<2^256
    rw [h4]; exact wordsVal_lt _ _ _ 4
  obtain hi : Inv c.MP' base size c.C.p (·∈JWin.slots (Impl.Ecdh.X86.Cfg.jwinCfg c))
      (JWin.ro (Impl.Ecdh.X86.Cfg.jwinCfg c)) (tmv c.C c.n base s₂) s₂ :=
    ⟨hs₂,modP_of hc F₂.mp,fun _ hx => List.mem_append_left _ hx,hlt,fun _ _ => rfl⟩
  refine WP.mono (JWin.window_ok (jwinLay h4) (jwinWk hc h4)
    (unitMod_pow_two hc.p_odd _) hC hM3 hO hP hP0 hn17 hn64 (hmont 1)
    (by change toM c.C.p (2^(64*c.n)) (c.mont 1)=1; exact toM_cmont hc 1)
    hi hJ hz F₂.zero hb hrec) fun u ⟨fu,Lu,qu⟩ => ?_
  obtain UW₁ : Unch base (windowW c) s.mem s₁.mem := U₁.mono (by
    intro w hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, by rw [List.mem_singleton.mp hi]; decide, rfl⟩))
  obtain UW₂ : Unch base (windowW c) s₁.mem s₂.mem := U₂.cover (by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨(2640, 1456), List.mem_append_right _ (by simp), by decide, by decide⟩
    · exact ⟨(Impl.Ecdh.X86.Cfg.windowBits, 320), List.mem_append_right _ (by simp), Nat.le_refl _,
        Nat.le_refl _⟩)
  obtain ku : Keeps powClob s₂ u := ⟨fun r hr => fu.keep.1 r (by simp only [powClob,List.mem_cons] at hr; exact fun h => hr (by simpa only [JWin.clobbers,List.mem_append,List.mem_singleton,or_comm] using h)),fu.keep.2.1,fu.keep.2.2⟩
  obtain UW : Unch base (jwinW c) s.mem s₂.mem :=
    (show Unch base (windowW c) s.mem s₂.mem from fun x hx => (UW₂ x hx).trans (UW₁ x hx)).mono
      (fun _ hx => List.mem_append_left _ hx)
  exact ⟨((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ku,
    fun x hx => (fu.unch.cover (jwinW_cover h4) x hx).trans (UW x hx),fu.mod,Lu,qu⟩

end VG.Proof.Ecdh.X86
