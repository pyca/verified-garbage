module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SamplePrepared
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundContext
import VerifiedGarbage.Proof.Framework.Offset

/-! One candidate's reusable state throughout the shared witness loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont
open VG.Spec.Rsa.Mont (wOf numAt arrAt)

structure PrimeState (base : Addr) (n candidate : Nat) (s : State) : Prop where
  context : WitnessContext base n candidate s
  layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536
  core : VG.Proof.MillerRabin.PreparedCore s.mem (off base Layout.arithmetic)
  width : wOf s.mem (off base Layout.arithmetic) = n
  candidate : numAt s.mem (off base Layout.arithmetic) n 0 = candidate

theorem PrimeState.kept {s t : State} {base : Addr} {n candidate : Nat}
    (S : PrimeState base n candidate s) (C : WitnessContext base n candidate t)
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem) :
    PrimeState base n candidate t := by
  have Kw : Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536
      (wOf s.mem (off base Layout.arithmetic)) s.mem t.mem := by
    rw [S.width]; exact K
  obtain ⟨L, core⟩ := S.core.kept S.layout Kw
  obtain ⟨_, width⟩ := VG.Proof.MillerRabin.kept_layout S.layout Kw
  have fit : arrAt n 28 ≤ 12288 := by
    have fit : arrAt (wOf s.mem (off base Layout.arithmetic)) 28 ≤ 12288 := S.layout.2.2.2.2.1
    rw [S.width] at fit; exact fit
  refine ⟨C, L, core, width.trans S.width, ?_⟩
  exact (VG.Proof.MillerRabin.kept_number K fit (j := 0) (.inl rfl)).trans S.candidate

theorem PrimeState.of_keeps {s t : State} {base : Addr} {n candidate : Nat} {regs : List Reg}
    (S : PrimeState base n candidate s) (K : VG.Proof.Mont.X86.Keeps regs s t)
    (edi : .edi ∉ regs) (esp : .esp ∉ regs) (memory : t.mem = s.mem) : PrimeState base n candidate t := by
  have F : Frame [] s.mem t.mem := by rw [memory]; exact Frame.refl _ _
  apply S.kept (S.context.frame_keep K edi esp F (by simp))
  intro i _ _ _ _
  rw [memory]

theorem PrimeState.sample {s t : State} {base : Addr} {n candidate : Nat}
    (S : PrimeState base n candidate s) (C : WitnessContext base n candidate t)
    (F : SampleFrame base s t) : PrimeState base n candidate t :=
  S.kept C (sample_keeps F n)

theorem PrimeState.control {s t : State} {base : Addr} {n candidate : Nat} {regs : List Reg}
    (S : PrimeState base n candidate s) (F : Frame [⟨off base Layout.control, 512⟩] s.mem t.mem)
    (K : VG.Proof.Mont.X86.Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs) :
    PrimeState base n candidate t := by
  have C := S.context.frame_keep K edi esp F (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.base_disjoint base (by decide) (by decide))
  apply S.sample C
  exact F.sub (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base base (by decide)⟩)

theorem PrimeState.encoded {s t : State} {base : Addr} {bytes n candidate : Nat}
    (S : PrimeState base n candidate s) (C : WitnessContext base n candidate t)
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (room : VG.Proof.Mont.X86.CallRoom (s.gpr .esp) base bytes)
    (capacity : 40960 ≤ bytes) (upper : n ≤ 48) : PrimeState base n candidate t :=
  S.kept C (witness_keeps F room capacity upper)

theorem PrimeState.afterRound {s t : State} {base : Addr} {bytes n candidate : Nat}
    (S : PrimeState base n candidate s) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (F : Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem)
    (regs : VG.Proof.Mont.X86.Keeps [.eax, .ecx, .edx] s t)
    (K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem) :
    PrimeState base n candidate t :=
  S.kept (round_context S.context capacity room F regs) K

end VG.Proof.Dsa.X86.Generation
