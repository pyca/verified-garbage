import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem earlyOrs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat} (ha8 : a % 8 = 0) :
    ∀ k, a + 8 * (k + 1) ≤ size →
    WP isa (.block ((List.range k).flatMap fun j =>
        [ld .x3 (a + 8 * (j + 1)), .logic .orr .x .x2 .x2 .x3])) s fun s' =>
      (s'.gpr .x2 = 0 ↔ s.gpr .x2 = 0 ∧ ∀ j < k, word s.mem base (a + 8 * (j + 1)) = 0) ∧
      Keeps [.x2, .x3] s s'
  | 0, _ => WP.block_nil ⟨⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, fun h => h.1⟩,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (earlyOrs_ok hs ha8 k (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := a + 8 * (k + 1)) (by omega) (by omega) .x3) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', or_eq_zero, l₂,
      k₂.gpr .x2 (by decide), e₁, k₁.mem]
    refine ⟨⟨fun ⟨⟨h₀, h⟩, hw⟩ => ⟨h₀, fun j hj => ?_⟩, fun ⟨h₀, h⟩ => ⟨⟨h₀, fun j hj => h j (by omega)⟩,
      h k (by omega)⟩⟩, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge j k with hj' | hj'
      · exact h j hj'
      · obtain rfl : j = k := by omega
        exact hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₂.gpr r (by simpa using hr.2), k₁.gpr r (by simpa using hr)]
    · rw [RegUpd.mem_write, k₂.mem, k₁.mem]
    · rw [RegUpd.rd_write, k₂.rd, k₁.rd]
    · rw [RegUpd.wr_write, k₂.wr, k₁.wr]
    · rw [RegUpd.sp_write, k₂.sp, k₁.sp]

/-- The remainder scan preserves the delta in x1, needed by the fallback batch. -/
theorem earlyCheck_ok {s : State} {base : Addr} {size n a : Nat} (hs : Scr s base size)
    (hn : 0<n) (ha : a+8*n≤size) (ha8 : a%8=0) :
    WP isa (.block ([ld .x2 a] ++ (List.range (n-1)).flatMap fun i =>
      [ld .x3 (a+8*(i+1)),.logic .orr .x .x2 .x2 .x3])) s fun t =>
      (t.gpr .x2=0 ↔ wordsVal s.mem base a n=0) ∧ Keeps [.x2,.x3] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d:=a) (by omega) ha8 .x2) fun b ⟨b2,kb,_⟩ => ?_
  refine WP.mono (earlyOrs_ok (hs.of_keeps kb (by decide)) ha8 (n-1) (by omega))
    fun t ⟨te,kt⟩ => ⟨?_,(kb.mono (by sub_regs)).trans kt⟩
  rw [te,b2,kb.mem,wordsVal_eq_zero_iff]
  constructor
  · intro ⟨h0,h⟩ j hj
    cases j with
    | zero => simpa using h0
    | succ j => exact h j (by omega)
  · intro h
    exact ⟨by simpa using h 0 hn,fun j hj => h (j+1) (by omega)⟩

/-- A zero word representation cannot hide a nonzero signed remainder in range. -/
theorem IInv.g_zero_of_words {P : InvCfg} {base : Addr} {I : Divstep.IState} {s : State}
    (hI : IInv P base I s) (hg : |I.g| < (2 ^ (64 * P.L) : Nat))
    (hz : wordsVal s.mem base P.sG P.L=0) : I.g=0 := by
  have h := hI.g
  rw [hz, Nat.cast_zero, Int.zero_emod] at h
  have hd := Int.dvd_of_emod_eq_zero h.symm
  obtain ⟨k,hk⟩ := hd
  have hpos : (0 : Int) < (2 ^ (64 * P.L) : Nat) := by positivity
  rw [abs_lt] at hg
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have : k≤-1 := by omega
    nlinarith
  · simp only [hk0,mul_zero] at hk
    exact hk
  · have : 1≤k := by omega
    nlinarith

end VG.Proof.Weierstrass.AArch64
