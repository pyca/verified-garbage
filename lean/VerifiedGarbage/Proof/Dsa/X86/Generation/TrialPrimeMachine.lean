module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialMachine

/-! A trial-prime call retains the table loop's complete frame invariant. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation

theorem TrialMachine.prime {initial s : State} {base : Addr} {size offset w : Nat} {sp ptr : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    (hp : ptr.toNat = (base.toNat + offset) % 2 ^ 32)
    (fit : offset + 8 * w ≤ size) (small : 8 * w < 2 ^ 32) (nonempty : 0 < w)
    (prime : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (odd : (s.gpr .ebx).toNat % 2 = 1)
    (start : values 0 = ptr) (last : values 1 = ptr + BitVec.ofNat 32 (8 * w)) :
    WP isa (trialPrime trialStart trialEnd) s fun t =>
      TrialMachine initial base size sp values t ∧
      t.gpr .eax = BitVec.ofNat 32
        (decide (val32 initial.mem base offset (2 * w) % (s.gpr .ebx).toNat = 0)).toNat := by
  have readStart := h.read (i := 0) (by decide)
  have readEnd := h.read (i := 1) (by decide)
  rw [start] at readStart
  rw [last] at readEnd
  refine WP.mono (trial_prime h.ws hp fit small nonempty prime odd readStart readEnd) ?_
  rintro t ⟨value, mem, K⟩
  refine ⟨h.of_keeps K (by decide) mem, ?_⟩
  rw [h.number (by omega)] at value
  exact value

end VG.Proof.Dsa.X86.Generation
