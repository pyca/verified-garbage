module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! Tape cursors and policy counters are retained while a witness is tested. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

def ControlKeeps (base : Addr) (m m' : Mem) : Prop :=
  ∀ d, Layout.control ≤ d → d + 4 ≤ Layout.control + 128 →
    m'.readW (off base d) 32 = m.readW (off base d) 32

theorem ControlKeeps.trans {base : Addr} {m m' m'' : Mem}
    (A : ControlKeeps base m m') (B : ControlKeeps base m' m'') : ControlKeeps base m m'' :=
  fun d lo hi => (B d lo hi).trans (A d lo hi)

theorem buffer_control {s t : State} {base : Addr} {len : Nat}
    (F : Frame [⟨off base Layout.witness, len⟩] s.mem t.mem) (length : len ≤ 384) :
    ControlKeeps base s.mem t.mem := by
  intro d lo hi
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint base (.inr (by simp only [Layout.control, Layout.witness] at lo ⊢; omega))
    (by unfold Layout.control at hi; omega) (by unfold Layout.witness; omega)

theorem sampling_control {s t : State} {base : Addr} {n len : Nat}
    (F : SamplingFrame base n len s t) (upper : n ≤ 48) (length : len ≤ 384) :
    ControlKeeps base s.mem t.mem := by
  intro d lo hi
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by
      simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride, Layout.control] at lo ⊢; omega))
      (by unfold Layout.control at hi; omega)
      (by simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride]; omega)
  · exact Offset.disjoint base (.inr (by simp only [Layout.control, Layout.witness] at lo ⊢; omega))
      (by unfold Layout.control at hi; omega) (by unfold Layout.witness; omega)
  · exact Offset.disjoint base (.inl (Nat.le_trans hi (by decide)))
      (by unfold Layout.control at hi; omega) (by decide)

theorem encoding_control {s t : State} {base : Addr} {bytes n : Nat}
    (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes) (upper : n ≤ 48)
    (F : WitnessFrame base (s.gpr .esp) n s t) : ControlKeeps base s.mem t.mem := by
  intro d lo hi
  unfold Mem.readW
  rw [witness_middle_read (d := d) (size := 4) capacity room upper F
    (Nat.le_trans (by decide : montgomeryBytes ≤ Layout.control) lo)
    (Nat.le_trans hi (by decide))]

theorem called_control {s t : State} {base : Addr} {bytes : Nat}
    (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (F : Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] s.mem t.mem) :
    ControlKeeps base s.mem t.mem := by
  intro d lo hi
  unfold Mem.readW
  rw [round_middle_read (d := d) (size := 4) capacity room F
    (Nat.le_trans hi (by decide))]

end VG.Proof.Dsa.X86.Generation
