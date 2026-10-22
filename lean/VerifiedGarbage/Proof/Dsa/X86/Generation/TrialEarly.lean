module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialUntilStep

/-! The public trial filter stops on a divisor and retains the exact shared primality policy. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

theorem trial_pairs_until {P : TrialPlan} {initial s : State} {sp : BitVec 32}
    (I : TrialLoopInv P initial sp 0 s)
    (table : ∀ i < P.count, initial.mem.readW (off P.base (P.table + 4 * i)) 32 = BitVec.ofNat 32 (tabWord32 i)) :
    WP isa (.loop trialPairUntil .ne) s fun t =>
      ∃ k ≤ P.count, TrialLoopInv P initial sp k t ∧ (k = P.count ∨ tr (2 * k) (P.number initial) = true) := by
  refine WP.loop (M := isa)
    (fun remaining t => ∃ k, remaining = P.count - k ∧ k < P.count ∧ TrialLoopInv P initial sp k t)
    ?_ P.count s ⟨0, rfl, P.countPositive, I⟩
  rintro remaining t ⟨k, rfl, hk, J⟩
  refine WP.mono (trial_until_step J hk table) fun u ⟨Ju, zf⟩ => ?_
  by_cases done : k + 1 = P.count ∨ tr (2 * (k + 1)) (P.number initial) = true
  · exact Or.inl ⟨by simp only [eval, zf, done, decide_true, Option.map_some, Bool.not_true],
      k + 1, by omega, Ju, done⟩
  · exact Or.inr ⟨by simp only [eval, zf, decide_eq_false done, Option.map_some, Bool.not_false],
      P.count - (k + 1), by omega, k + 1, rfl, by omega, Ju⟩

theorem trial_loop_early {P : TrialPlan} {initial s : State} {sp : BitVec 32} {values : Nat → BitVec 32}
    (h : TrialMachine initial P.base P.bytes sp values s)
    (start : values 0 = P.start) (last : values 1 = P.start + BitVec.ofNat 32 (8 * P.width))
    (ptr : values 2 = P.tableStart) (count : values 3 = BitVec.ofNat 32 P.count)
    (table : ∀ i < P.count, initial.mem.readW (off P.base (P.table + 4 * i)) 32 = BitVec.ofNat 32 (tabWord32 i)) :
    WP isa trialLoopEarly s fun t =>
      (∃ k ≤ P.count, TrialLoopInv P initial sp k t) ∧
      t.gpr .eax = BitVec.ofNat 32 (tr (2 * P.count) (P.number initial)).toNat := by
  unfold trialLoopEarly trialLoopWith
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have hu := h.of_keeps U.keeps (by decide) U.mem
  refine WP.block_append (WP.mono (hu.store (i := 5) (by decide) .eax) ?_)
  rintro v ⟨hv, _⟩
  rw [U.gpr] at hv
  refine WP.block_nil (WP.seq (WP.mono (trial_pairs_until (P := P) (initial := initial) (sp := sp)
    (s := v) ?_ table) ?_))
  · refine ⟨_, hv, start, last, ?_, ?_, ?_⟩
    · change values 2 = P.tableStart + BitVec.ofNat 32 (4 * 0)
      simpa using ptr
    · change values 3 = BitVec.ofNat 32 (P.count - 0)
      simpa using count
    · rfl
  · rintro w ⟨k, hk, ⟨finalValues, I⟩, done⟩
    have flag : tr (2 * k) (P.number initial) = tr (2 * P.count) (P.number initial) := by
      rcases done with rfl | found
      · rfl
      · rw [found, tr_mono_true (Nat.mul_le_mul_left 2 hk) found]
    refine wp_movS (I.machine.read (i := 5) (by decide)) fun t T _ => WP.block_nil ?_
    refine ⟨⟨k, hk, finalValues, I.machine.of_keeps T.keeps (by decide) T.mem,
      I.start, I.last, I.table, I.count, I.flag⟩, ?_⟩
    rw [T.gpr, I.flag, flag]

theorem trial_loop_early_dsa {P : TrialPlan} {initial s : State} {sp : BitVec 32}
    {values : Nat → BitVec 32} {bits : Nat}
    (h : TrialMachine initial P.base P.bytes sp values s)
    (start : values 0 = P.start) (last : values 1 = P.start + BitVec.ofNat 32 (8 * P.width))
    (ptr : values 2 = P.tableStart) (count : values 3 = BitVec.ofNat 32 P.count)
    (table : ∀ i < P.count, initial.mem.readW (off P.base (P.table + 4 * i)) 32 = BitVec.ofNat 32 (tabWord32 i))
    (selected : P.count = if 17 ≤ P.width then 512 else 256)
    (large : 8161 < P.number initial) (policy : 1024 < bits ↔ 16 < P.width) :
    WP isa trialLoopEarly s fun t =>
      (∃ k ≤ P.count, TrialLoopInv P initial sp k t) ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite bits (P.number initial)).toNat := by
  have entries : 2 * P.count = 4 * (if 17 ≤ P.width then 256 else 128) := by
    rw [selected]; split <;> rfl
  refine WP.mono (trial_loop_early h start last ptr count table) fun t ⟨I, value⟩ => ?_
  rw [entries, tr_trialAny, VG.Proof.Dsa.Generation.trialAny_dsa large policy] at value
  exact ⟨I, value⟩

end VG.Proof.Dsa.X86.Generation
