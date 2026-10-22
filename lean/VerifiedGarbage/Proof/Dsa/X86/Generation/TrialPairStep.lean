module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTablePrime

/-! Both primes in a packed word extend the accumulated divisibility flag. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen

theorem trial_pair_step {P : TrialPlan} {initial s : State} {sp : BitVec 32} {k : Nat}
    (I : TrialLoopInv P initial sp k s) (hk : k < P.count)
    (table : ∀ i < P.count, initial.mem.readW (off P.base (P.table + 4 * i)) 32 =
      BitVec.ofNat 32 (tabWord32 i)) :
    WP isa trialPairStep s fun t =>
      TrialLoopInv P initial sp (k + 1) t ∧ t.zf = some (decide (k + 1 = P.count)) := by
  obtain ⟨values, I⟩ := I
  have hk512 : k < 512 := Nat.lt_of_lt_of_le hk P.countBound
  have fits : P.table + 4 * k + 4 ≤ P.bytes := by have := P.tableFits; omega
  have ptr : (values 2).toNat = (P.base.toNat + (P.table + 4 * k)) % 2 ^ 32 := by
    rw [I.table]
    change (BitVec.ofNat 32 (P.base.toNat + P.table) + BitVec.ofNat 32 (4 * k)).toNat = _
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.add_assoc]
  unfold trialPairStep
  refine WP.seq (WP.mono (I.machine.next_pair ptr fits) ?_)
  rintro a ⟨ma, low⟩
  rw [table k hk] at ma low
  rw [trial_low_pair hk512] at low
  refine WP.seq (WP.mono (ma.table_prime (by omega : 2 * k < 1024) low I.start I.last) ?_)
  rintro b ⟨mb, f0⟩
  refine WP.seq (WP.mono mb.accumulate ?_)
  intro c mc
  rw [f0] at mc
  refine WP.seq (WP.mono mc.high_prime ?_)
  rintro d ⟨md, high⟩
  change d.gpr .ebx = BitVec.ofNat 32 (tabWord32 k) >>> 16 at high
  rw [trial_high_pair hk512] at high
  refine WP.seq (WP.mono (md.table_prime (by omega : 2 * k + 1 < 1024) high I.start I.last) ?_)
  rintro e ⟨me, f1⟩
  refine WP.seq (WP.mono me.accumulate ?_)
  intro f mf
  rw [f1] at mf
  refine WP.mono mf.count_down ?_
  rintro t ⟨mt, zf⟩
  refine ⟨⟨_, mt, I.start, I.last, ?_, ?_, ?_⟩, ?_⟩
  · change values 2 + 4 = P.tableStart + BitVec.ofNat 32 (4 * (k + 1))
    rw [I.table, row_ebp]
  · change values 3 - 1 = BitVec.ofNat 32 (P.count - (k + 1))
    rw [I.count, trial_count_word hk]
  · change (values 5 ||| BitVec.ofNat 32 (decide (P.number initial % tabEntry (2 * k) = 0)).toNat) |||
      BitVec.ofNat 32 (decide (P.number initial % tabEntry (2 * k + 1) = 0)).toNat = _
    rw [I.flag, trial_bit_or, trial_bit_or,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega, tr_succ, tr_succ]
  · change t.zf = some (values 3 - 1 == 0) at zf
    rw [I.count, trial_count_word hk, trial_count_flag P.countBound hk] at zf
    exact zf

end VG.Proof.Dsa.X86.Generation
