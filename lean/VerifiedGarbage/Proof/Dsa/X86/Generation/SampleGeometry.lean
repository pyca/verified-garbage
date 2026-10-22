module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessContext
public import VerifiedGarbage.Proof.Bignum.OctetFrame
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! Sampling writes stay below the prepared Miller–Rabin workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

def SampleFrame (base : Addr) (s t : State) : Prop :=
  Frame [⟨base, Layout.arithmetic⟩] s.mem t.mem

def SamplingFrame (base : Addr) (n len : Nat) (s t : State) : Prop :=
  Frame [⟨off base (slot n 5), 8 * n⟩, ⟨off base Layout.witness, len⟩,
    ⟨off base witnessUniform, 4⟩] s.mem t.mem

theorem sample_outside {s t : State} {base : Addr} {d len : Nat}
    (F : Outside base d len s.mem t.mem) (fit : d + len ≤ Layout.arithmetic) :
    SampleFrame base s t := by
  have bound : d + len < 2 ^ 64 := Nat.lt_of_le_of_lt fit (by decide)
  apply (F.frameAt bound).sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base base fit⟩

theorem sample_buffer {s t : State} {base : Addr} {d size len : Nat}
    (F : Outside base d size s.mem t.mem) (hlen : len ≤ 384)
    (apart : d + size ≤ Layout.witness ∨ Layout.witness + len ≤ d) :
    Spec.Rsa.bytesAt t.mem (off base Layout.witness) len =
      Spec.Rsa.bytesAt s.mem (off base Layout.witness) len :=
  F.bytesAt apart.symm (by unfold Layout.witness; omega)

theorem forced_context {s t : State} {base : Addr} {n candidate len : Nat}
    (C : WitnessContext base n candidate s) (hlen : len ≤ 384)
    (F : Frame [⟨off base Layout.witness, len⟩] s.mem t.mem)
    (K : Keeps [.eax, .ebx] s t) : WitnessContext base n candidate t := by
  apply C.frame_keep K (by decide) (by decide) F
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.base_disjoint base (by decide : montgomeryBytes ≤ Layout.witness)
    (by unfold Layout.witness; omega)

theorem forced_flag {s t : State} {base : Addr} {len : Nat} (hlen : len ≤ 384)
    (F : Frame [⟨off base Layout.witness, len⟩] s.mem t.mem) :
    w32 t.mem base witnessUniform = w32 s.mem base witnessUniform := by
  unfold w32
  rw [F.readW (r := ⟨off base witnessUniform, 4⟩)
    (by simpa only [off, BitVec.add_zero] using
      Offset.contains_base (off base witnessUniform) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint base (.inr (by unfold Layout.witness witnessUniform Layout.control; omega))
        (by decide) (by unfold Layout.witness; omega)) (by decide)]

theorem forced_frame {s t : State} {base : Addr} {len : Nat} (hlen : len ≤ 384)
    (F : Frame [⟨off base Layout.witness, len⟩] s.mem t.mem) : SampleFrame base s t := by
  apply F.sub
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base base
    (by unfold Layout.witness Layout.arithmetic; omega)⟩

end VG.Proof.Dsa.X86.Generation
