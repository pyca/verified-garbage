import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Proof.Weierstrass.X86.InvInit
import VerifiedGarbage.Proof.Weierstrass.X86.InvRun
import VerifiedGarbage.Proof.Divstep.Tc32
import VerifiedGarbage.Proof.Divstep.Iter
import Mathlib.Data.Nat.Prime.Basic

/-! # Soundness of the 256-bit divstep inversion -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem runFacts {p x : Nat} {m : Int} (hp : (p : Int) % 2 = 1) (hp1 : 1 < p)
    (hm : ((p : Int) * m + 1) % 2 ^ 32 = 0) (hx : x < p) {k : Nat} (hk : k < 20) :
    BatchFacts (Divstep.W32.invRun 30 p m x k) p := by
  obtain ⟨hd, hf, hfb, hgb, ha0, ha1, hb0, hb1⟩ :=
    Divstep.W32.invRun_bounds (N := 30) (by decide) hp (by omega) hm (Int.natCast_nonneg x) (by omega) k
  refine ⟨?_, hf, hfb, hgb, ?_, ?_, ?_, ?_⟩
  · push_cast at hd
    omega
  · rw [abs_of_nonneg ha0]
    omega
  · rw [abs_of_nonneg hb0]
    omega
  · exact Divstep.msteps_bnd _ _ _ 30
  · have H := Divstep.msteps_mat (d := (Divstep.W32.invRun 30 p m x k).d)
      (g := (Divstep.W32.invRun 30 p m x k).g) hf 30
    exact ⟨⟨_, H.1.symm⟩, ⟨_, H.2.symm⟩⟩

theorem finish_sign {P : InvCfg} {base : Addr} {s : State} {f : Int}
    (hf : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = f % 2 ^ 288) :
    (f = 1 → (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) = P.C) ∧
    (f = -1 → (if 2 ^ 31 ≤ w32 s.mem base P.sF then P.Cn else P.C) = P.Cn) := by
  have E := low_cong32 hf
  have hb := (s.mem.readW (off base P.sF) 32).isLt
  have E' : (w32 s.mem base P.sF : Int) = f % 2 ^ 32 := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hb)] at E
    exact E
  constructor
  · intro h
    rw [h, Int.emod_eq_of_lt (by decide) (by decide)] at E'
    rw [ite_eq_right (by omega)]
  · intro h
    rw [h, show (-1 : Int) % 2 ^ 32 = 2 ^ 32 - 1 by decide] at E'
    rw [ite_eq_left (by omega)]

theorem invPow_ok {P : InvCfg} {base : Addr} {size p : Nat} [NeZero p]
    (hpr : p.Prime) (hT : InvToM p) (L : InvLay P size) (hp2 : 2 < p)
    (hR : UnitMod p (2 ^ 256)) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size p s.mem base) (hX : val32 s.mem base P.base 8 < p) (hC : InvOk P p) :
    WP isa P.inv s fun z => Keeps invClob s z ∧ Unch base (invW P) s.mem z.mem ∧
      val32 z.mem base P.out 8 < p ∧
      toM p (2 ^ 256) (val32 z.mem base P.out 8) =
        toM p (2 ^ 256) (val32 s.mem base P.base 8) ^ (p - 2) := by
  have hn := hs.nowrap
  have ht := L.tbl_bound; have hmod := L.mod_bound
  have htm := L.tbl_mod; have hmt := L.mod_tmp
  have hm : val32 s.mem base P.M.mo 8 = p := by
    simpa only [L.n4, wordsVal_eq_val32] using hM.val
  have hp256 : p < 2 ^ 256 := by rw [← hm]; exact val32_lt _ _ _ _
  have oddNat : p % 2 = 1 := by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact absurd (hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩) (by omega)
    · omega
  have odd : (p : Int) % 2 = 1 := by exact_mod_cast oddNat
  have hinv := minv32_inv hM.inv
  have hinvI : ((p : Int) * (minv32 P.M).toNat + 1) % 2 ^ 32 = 0 := by exact_mod_cast hinv
  have hCm : P.C < p := by rw [hC.C]; exact Nat.mod_lt _ (by omega)
  have hCnm : P.Cn < p := by rw [hC.Cn]; have := hC.Cpos; omega
  have modU : ∀ {mem' : Mem}, Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem mem' →
      ModOkW P.M size p mem' base := by
    intro mem' U
    refine ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
    rw [L.n4, wordsVal_eq_val32, Outs.val32 U (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      constructor <;> omega) (by omega), hm]
  unfold InvCfg.inv
  refine WP.seq (WP.mono (init_ok hs L hm) fun s₁ ⟨I₁, C₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have U₁ : Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem s₁.mem :=
    fun q hq => O₁ q (hq (P.tbl, 320) (by simp))
  have hm₁ : val32 s₁.mem base P.M.mo 8 = p := by
    simpa only [L.n4, wordsVal_eq_val32] using (modU U₁).val
  refine WP.seq (WP.mono (run_ok hs₁ L.toWorkLay (by omega) hp256 hm₁ hinv I₁ C₁
    (fun _ hk => runFacts odd (by omega) hinvI hX hk)) fun s₂ ⟨I₂, K₂, U₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have U : Unch base [(P.tbl, 320), (P.M.tmp, 32)] s.mem s₂.mem :=
    fun q hq => (U₂ q hq).trans (U₁ q hq)
  refine WP.mono (finish_ok hs₂ L hC hp256 hCm hCnm)
    fun z ⟨V₃, E₃, K₃, U₃⟩ => ⟨?_, ?_, V₃, ?_⟩
  · exact ((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide))
  · intro q hq
    rw [U₃ q hq, U q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hq (P.tbl, 320) (by simp [invW]), hq (P.M.tmp, 32) (by simp [invW])⟩)]
  let X := val32 s.mem base P.base 8
  let I := Divstep.W32.invRun 30 p (minv32 P.M).toNat X 20
  have ha : (val32 s₂.mem base P.sA 8 : Int) = I.a := I₂.a
  have done : (Divstep.divsteps (30 * 20) (1, p, (X : Int))).2.2 = 0 ∧
      (Divstep.divsteps (30 * 20) (1, p, (X : Int))).2.1.natAbs = Int.gcd p X :=
    Divstep.divsteps_words (n := 4) odd (Int.natCast_nonneg _) (by exact_mod_cast hX.le)
      (by exact_mod_cast hp256) (.inl ⟨by decide, by decide⟩)
  have spec : X ≠ 0 → (I.f = 1 ∨ I.f = -1) ∧
      (X : Int) * (I.f * I.a) * 2 ^ 40 ≡ 1 [ZMOD p] := by
    intro hX0
    exact Divstep.W32.invRun_spec (N := 30) (B := 20) (by decide) odd (by omega) hinvI done (by
      rw [Int.gcd_natCast_natCast]
      exact Nat.coprime_of_lt_prime (by omega) hX hpr)
  have signs := finish_sign I₂.f
  refine hT (K := 2 ^ 40) (f := I.f) hp2 hR hX ?_ ?_ ?_ E₃
  · intro hX0
    have Z := (Divstep.W32.invRun_zero (N := 30) (p := p) (m := (minv32 P.M).toNat) (by omega) 20).2
    have ia : I.a = 0 := by
      change (Divstep.W32.invRun 30 p (minv32 P.M).toNat X 20).a = 0
      change X = 0 at hX0
      rw [hX0, Nat.cast_zero]
      exact Z
    have : (val32 s₂.mem base P.sA 8 : Int) = 0 := ha.trans ia
    exact_mod_cast this
  · intro hX0
    have H := (spec hX0).2
    rw [← ha] at H
    exact_mod_cast H
  · intro hX0
    rcases (spec hX0).1 with H | H
    · rw [signs.1 H, hC.C, H]
      push_cast
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · rw [signs.2 H, hC.Cn, H, Nat.cast_sub hCm.le]
      have C : (P.C : Int) ≡ ((2 ^ 40 * (2 ^ 256) ^ 3 : Nat) : Int) [ZMOD p] := by
        rw [hC.C]; push_cast; exact Int.emod_emod_of_dvd _ (dvd_refl _)
      have P0 : (p : Int) ≡ 0 [ZMOD p] := Int.emod_self.trans (Int.zero_emod _).symm
      have H := P0.sub C
      push_cast at H ⊢
      simpa only [Int.ModEq, Int.neg_one_mul, Int.zero_sub] using H

theorem invSound_of_toM {p : Nat} [NeZero p] (hp : p.Prime) (hT : InvToM p) : InvSound p :=
  fun L hp2 hR _ hs hM hX hC => invPow_ok hp hT L hp2 hR hs hM hX hC

end VG.Proof.Weierstrass.X86.Inv
