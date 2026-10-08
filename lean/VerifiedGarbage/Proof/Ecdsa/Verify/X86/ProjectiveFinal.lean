import VerifiedGarbage.Proof.Ecdsa.Verify.X86.ProjectiveArithmetic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.ProjectiveFlags

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdh.X86
variable {c : VG.Impl.Ecdsa.X86.Cfg}

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : CfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal c) s fun s' =>
      (∀ rd ∈ VG.Impl.Ecdsa.X86.Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .eax = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  let A := KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
    (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)
  let fx := tmv c.C c.n base s (c.sl RX)
  let fz := tmv c.C c.n base s (c.sl RZ)
  let xo := (fx * fz ^ (c.C.p - 2)).val
  refine hP.keep.withSp hsp ?_
  rw [Impl.Ecdsa.Verify.X86.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,esp,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  have v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slWk hi hl)
  have saved : ∀ rd ∈ Cfg.saved, t.mem.readW (off base rd.2) 32 = s₀.gpr rd.1 := by
    intro rd hr
    have bound : rd.2 + 4 ≤ 16 := by revert rd; decide
    rw [Unch.readW32 U (fun w hw => ?_) (by omega)]
    · exact hP.fixed.saved rd hr
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        left; rw [sl_eq]; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        left
        have := sl_below_wk c (i := FLAG) (by decide)
        rw [sl_eq] at this
        rcases hw with rfl | rfl
        · omega
        · dsimp only [Mont.outW]; omega
  have flag : flagW c base t = mask32 A := by
    rw [flagW, flag_unch U h7 h0 hn (by decide)]
    exact hP.flag
  have wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,esp',U',ret⟩ fr => ?_
  refine ⟨keep, by rw [esp',esp,hP.esp], fr, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
  simp only [v (i := RZ) (by decide) (by decide), v (i := K) (by decide) (by decide), hP.k, mn, wz, xnz] at ret
  have iff : (A ∧ sv c base s RZ ≠ 0 ∧
      (fx = Fin.ofNat c.C.p (sigR c s₀) * fz ∨
        (sigR c s₀ < c.C.p - c.C.n ∧ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz))) ↔
      (A ∧ sv c base s RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mpr hm⟩
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mp hm⟩
  simpa only [iff] using ret

theorem tail_dispatch_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s)
    (hsp : SpOk (Impl.Ecdsa.Verify.X86.Cfg.tail c) c.stk) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.tail c) s fun s' =>
      (∀ rd ∈ VG.Impl.Ecdsa.X86.Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .eax = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.X86.Cfg.tail at hsp ⊢
  by_cases h : c.C.len = 32 ∧ c.C.n < c.C.p ∧ c.C.p ≤ 2 * c.C.n
  · rw [ite_eq_left h] at hsp ⊢
    exact projectiveFinal_ok hc hC h.2.1 h.2.2 hP hsp
  · rw [ite_eq_right h] at hsp ⊢
    exact vtail_ok hc hP hsp.left hsp.right

end VG.Proof.Ecdsa.Verify.X86
