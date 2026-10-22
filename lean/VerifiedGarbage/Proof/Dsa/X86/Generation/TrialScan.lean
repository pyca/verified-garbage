module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialScanState

/-! The shared scan computes a bounded residue of the complete candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem trial_scan_initial (s : State) (base : Addr) (offset : Nat)
    (prime : 3 ≤ (s.gpr .ebx).toNat) :
    WP isa (.block [.mov .edi (.imm 0)]) s fun t => TrialScanInv s base offset 0 t := by
  refine wp_movS rfl fun u U _ => WP.block_nil ?_
  refine ⟨U.mem, U.keeps.mono (by decide), ?_, ?_, ?_⟩
  · rw [U.other .ebp (by decide)]; simp
  · rw [U.gpr]; change 0 < 2 * (s.gpr .ebx).toNat; omega
  · rw [U.gpr]
    change 0 * 2 ^ (32 * 0) % _ = 0 % _
    rw [Nat.zero_mul]

theorem trial_scan {s : State} {base : Addr} {size offset n endSlot : Nat}
    (ws : Rt.Ws s base size) (hp : Rt.PtrAt s base .ebp offset)
    (fit : offset + 4 * n ≤ size) (small : 4 * n < 2 ^ 32) (nonempty : 0 < n)
    (prime : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 16 = 0)
    (last : readSrc s (.mem (at_ .esp endSlot)) =
      some (s.gpr .ebp + BitVec.ofNat 32 (4 * n))) :
    WP isa (trialScan endSlot) s fun t => TrialScanInv s base offset n t := by
  unfold trialScan
  refine WP.seq (WP.mono (trial_scan_initial s base offset prime.1) ?_)
  intro u initial
  refine WP.loop (M := isa)
    (fun k t => ∃ j, k = n - j ∧ j < n ∧ TrialScanInv s base offset j t)
    ?_ n u ⟨0, rfl, nonempty, initial⟩
  rintro k v ⟨j, rfl, hj, I⟩
  refine WP.mono (trial_scan_step ws hp fit small hj prime inverse last I) ?_
  rintro t ⟨I', zf⟩
  by_cases done : j + 1 = n
  · exact .inl ⟨by simp only [eval, zf, done, decide_true, Option.map_some, Bool.not_true], done ▸ I'⟩
  · exact .inr ⟨by simp only [eval, zf, decide_eq_false done, Option.map_some, Bool.not_false],
      n - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

end VG.Proof.Dsa.X86.Generation
