module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialMachine

/-! Frame operations of the trial-table loop retain the candidate memory. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem TrialMachine.accumulate {initial s : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s) :
    WP isa (.block trialAccumulate) s fun t =>
      TrialMachine initial base size sp
        (fun j => if j = 5 then values 5 ||| s.gpr .eax else values j) t := by
  unfold trialAccumulate
  refine wp_movS (h.read (i := 5) (by decide)) fun u U _ => wp_orS rfl fun v V => ?_
  have hv := (h.of_keeps U.keeps (by decide) U.mem).of_keeps V.keeps (by decide) V.mem
  have sum : v.gpr .edx = values 5 ||| s.gpr .eax := by
    rw [V.gpr, U.gpr, U.other .eax (by decide)]
  refine WP.mono (hv.store (i := 5) (by decide) .edx) ?_
  rintro t ⟨ht, _⟩
  rw [sum] at ht
  exact ht

theorem TrialMachine.high_prime {initial s : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s) :
    WP isa (.block trialHighPrime) s fun t =>
      TrialMachine initial base size sp values t ∧ t.gpr .ebx = values 4 >>> 16 := by
  unfold trialHighPrime
  refine wp_movS (h.read (i := 4) (by decide)) fun u U _ => wp_shr (by decide) fun t T _ => WP.block_nil ?_
  exact ⟨(h.of_keeps U.keeps (by decide) U.mem).of_keeps T.keeps (by decide) T.mem,
    by rw [T.gpr, U.gpr]⟩

theorem TrialMachine.count_down {initial s : State} {base : Addr} {size : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s) :
    WP isa (.block trialCountDown) s fun t =>
      TrialMachine initial base size sp (fun j => if j = 3 then values 3 - 1 else values j) t ∧
      t.zf = some (values 3 - 1 == 0) := by
  unfold trialCountDown
  refine wp_movS (h.read (i := 3) (by decide)) fun u U _ => wp_subS rfl fun v V _ => ?_
  have hv := (h.of_keeps U.keeps (by decide) U.mem).of_keeps V.keeps (by decide) V.mem
  have count : v.gpr .eax = values 3 - 1 := by rw [V.gpr, U.gpr]
  refine WP.block_append (WP.mono (hv.store (i := 3) (by decide) .eax) ?_)
  rintro z ⟨hz, K⟩
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  rw [count] at hz
  exact ⟨hz.of_keeps (T.keeps []) (by simp) T.mem,
    by rw [Z, K.1 .eax (by simp), count]; congr 2; exact BitVec.sub_zero _⟩

end VG.Proof.Dsa.X86.Generation
