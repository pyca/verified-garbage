module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Round
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLayout
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory

/-! # The draw, sampler, exponent reload and round share one mutable footprint -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem primeFrame_local {base witness : Addr} {n len size : Nat} {s t : Mem} {rs : List (Nat × Nat)}
    (O : Outs base rs s t) (sub : ∀ r ∈ rs, r ∈ primeWrites n)
    (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) (sizeBound : size ≤ 2 ^ 64) :
    PrimeFrame base n witness len s t := by
  have F := sampleOuts_frame (O.mono sub) (fun r hr => Nat.le_trans (primeWrites_bound width room r hr) sizeBound)
  exact F.mono (by intro r hr; exact List.mem_append_left _ hr)

theorem primeFrame_draw {base witness : Addr} {n len : Nat} {s t : Mem}
    (O : Frame [⟨off base primeUsed, 4⟩, ⟨witness, len⟩] s t) : PrimeFrame base n witness len s t := by
  apply O.mono
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [primeWrites]

theorem primeFrame_sample {base witness : Addr} {n len : Nat} {s t : Mem}
    (O : Frame (sampleWrites base n witness len) s t) : PrimeFrame base n witness len s t := by
  apply O.mono
  intro r hr
  simp only [sampleWrites, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨item, ?_, rfl⟩
    simp only [sampleArithmeticWrites, sampleTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [primeWrites]
  · exact List.mem_append_right _ (by simp)

theorem primeFrame_restore {base witness : Addr} {n len size : Nat} {s t : Mem}
    (O : Outs base [(slot n 8, 8 * n), (roundCount, 4)] s t)
    (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) (sizeBound : size ≤ 2 ^ 64) :
    PrimeFrame base n witness len s t :=
  primeFrame_local O (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [primeWrites]) width room sizeBound

theorem primeFrame_round {base witness : Addr} {n len size : Nat} {s t : Mem}
    (O : Outs base (roundAllWrites n (2 * n)) s t)
    (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size) (sizeBound : size ≤ 2 ^ 64) :
    PrimeFrame base n witness len s t := by
  apply primeFrame_local O ?_ width room sizeBound
  intro r hr
  simp only [roundAllWrites, exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges,
    roundFinishWrites, roundWrites, VG.Proof.Dsa.X86.productRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
    (((rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl) <;>
    simp [primeWrites, show 4 * (2 * n) = 8 * n by omega]
end VG.Proof.Dsa.X86.Generation
