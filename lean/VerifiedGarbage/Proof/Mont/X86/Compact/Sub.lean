module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

/-! # Subtraction may replace the modulus as well as either operand -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The loop: `[tmp] = [src] - [mo]`, `N` words, and the borrow. -/
theorem subLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {src mo tmp N : Nat} (hN : 0 < N)
    (hs : src + 4 * N ≤ L) (hm : mo + 4 * N ≤ L) (ht : tmp + 4 * N ≤ L)
    (hts : tmp + 4 * N ≤ src ∨ src + 4 * N ≤ tmp) (htm : tmp = mo ∨ tmp + 4 * N ≤ mo ∨ mo + 4 * N ≤ tmp)
    (hebp : PtrAt t₀ W .ebp src) (hesi : PtrAt t₀ W .esi mo) (hebx : PtrAt t₀ W .ebx tmp)
    (hedi : (t₀.gpr .edi).toNat = 4 * N) (hc : t₀.gpr .ecx = cmask false) :
    WP isa (.loop (.block subBody) .ne) t₀ fun u =>
      Outside W tmp (4 * N) t₀.mem u.mem ∧
      (∃ c : Bool, u.gpr .ecx = cmask c ∧
        val32 u.mem W tmp N + val32 t₀.mem W mo N = val32 t₀.mem W src N + 2 ^ (32 * N) * c.toNat) ∧
      PtrAt u W .ebp (src + 4 * N) ∧ Keeps clob7 t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps clob7 t₀ t ∧ PtrAt t W .ebp (src + 4 * j) ∧ PtrAt t W .esi (mo + 4 * j) ∧
    PtrAt t W .ebx (tmp + 4 * j) ∧ (t.gpr .edi).toNat = 4 * (N - j) ∧ Outside W tmp (4 * j) t₀.mem t.mem ∧
    ∃ c : Bool, t.gpr .ecx = cmask c ∧
      val32 t.mem W tmp j + val32 t₀.mem W mo j = val32 t₀.mem W src j + 2 ^ (32 * j) * c.toNat
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, by simpa using hebx,
    by simpa using hedi, Outside.refl _ _ _ _, false, hc, by simp [val32]⟩
  refine WP.mono (WP.loop (M := isa) (Q := I N) (fun m t => ∃ j, m = N - j ∧ j < N ∧ I j t) ?_ N t₀
    ⟨0, by omega, hN, I₀⟩) fun u ⟨K, ebp, _, _, _, O, V⟩ => ⟨O, V, ebp, K⟩
  rintro m t ⟨j, rfl, hj, K, ebp, esi, ebx, edi, O, c, ec, V⟩
  have ht' := hw.of_keeps K
  refine WP.mono (subStep_ok ht' ebp esi ebx edi hj ec (by omega_using [hs, hj]) (by omega_using [hm, hj])
    (by omega_using [ht, hj]))
    fun u ⟨mu, eu, pu, su, bu, du, zu, Ku⟩ => ?_
  have ea : w32 t.mem W (src + 4 * j) = w32 t₀.mem W (src + 4 * j) :=
    O.w32 (by omega_using [hts, hj]) (by omega_using [hs, hj, hn])
  have eb : w32 t.mem W (mo + 4 * j) = w32 t₀.mem W (mo + 4 * j) :=
    O.w32 (by rcases htm with htm | htm <;> omega) (by omega_using [hm, hj, hn])
  have I' : I (j + 1) u := by
    refine ⟨K.trans Ku, pu, su, bu, du, ?_, _, eu, ?_⟩
    · rw [mu]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [ht, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [mu, val32_store hn (by omega_using [ht, hj]), val32_succ t₀.mem W src, val32_succ t₀.mem W mo, pow32_succ]
      have h := sbb_rel (t.mem.readW (off W (src + 4 * j)) 32) (t.mem.readW (off W (mo + 4 * j)) 32) c
      have ea' : (t.mem.readW (off W (src + 4 * j)) 32).toNat = w32 t₀.mem W (src + 4 * j) := ea
      have eb' : (t.mem.readW (off W (mo + 4 * j)) 32).toNat = w32 t₀.mem W (mo + 4 * j) := eb
      rw [ea', eb'] at h
      rw [ea, eb]
      exact chain_sub_step V h
  by_cases hjN : j + 1 = N
  · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
      N - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

end VG.Proof.Mont.X86.Compact
