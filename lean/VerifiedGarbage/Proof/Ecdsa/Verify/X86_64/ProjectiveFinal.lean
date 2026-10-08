import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveArithmetic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
variable {c : VG.Impl.Ecdsa.X86_64.Cfg}

/-- The final public comparison needs the canonical X/Z fields and the saved verifier inputs. -/
structure ProjectiveInput (c : VG.Impl.Ecdsa.X86_64.Cfg) (s₀ : State) (base : Addr)
    (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s base size
  fixed : Fixed c base g s.mem
  k : sv c base s K = sigR c s₀
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rx_lt : sv c base s RX < c.C.p
  rz_lt : sv c base s RZ < c.C.p

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_fields_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : ProjectiveInput c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
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
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  have v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slW hl)
  have saved := Saved.unch hP.fixed.saved (fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    show 48 ≤ c.sl i
    rw [sl_eq']; omega) U
  have flag : word t.mem base (c.sl FLAG) = mask A := by
    rw [U.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
    · exact hP.flag
    · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
        (fun h => Or.inl (by have := hc.n0; omega)) Or.inr
  have wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,ret⟩ => ?_
  refine ⟨keep, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
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

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {u v : Nat} {P : Point c.C} {s : State} (hP : Pts c s₀ base g u v P s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 :=
  projectiveFinal_fields_ok hc hC hnp hpn ⟨hP.scr,hP.fixed,hP.k,hP.flag,hP.rx_lt,hP.rz_lt⟩

theorem tail_dispatch_ok (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {u v : Nat} {P : Point c.C} {s : State} (hP : Pts c s₀ base g u v P s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.tail c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.X86_64.Cfg.tail
  split
  · rename_i h
    exact projectiveFinal_ok hc hC h.2.1 h.2.2 hP
  · show WP isa (Code.seq c.pPow.inline (Impl.Ecdsa.Verify.X86_64.Cfg.final c).inline) s _
    rw [pPow_inline, show (Impl.Ecdsa.Verify.X86_64.Cfg.final c).inline = _ from blocks_inline _]
    exact tail_ok hc hP

end VG.Proof.Ecdsa.Verify.X86_64
