module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.EncodeWitness
public import VerifiedGarbage.Proof.MillerRabin.PreparedUpdate
public import VerifiedGarbage.Proof.MillerRabin.ReusableKeeps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Encoding a replacement witness retains the shared prepared-round contract. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt)

theorem witness_read {s t : State} {base : Addr} {bytes n d size : Nat}
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (room : CallRoom (s.gpr .esp) base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48)
    (fit : d + size ≤ Layout.arithmeticBytes)
    (apart : d + size ≤ arrAt n 5 ∨ arrAt n 5 + 8 * n ≤ d) :
    t.mem.read (off (off base Layout.arithmetic) d) size =
      s.mem.read (off (off base Layout.arithmetic) d) size := by
  have targetFit : Layout.arithmetic + d + size ≤ bytes := by
    simp only [Layout.arithmetic, Layout.arithmeticBytes] at fit ⊢; omega
  have address : off (off base Layout.arithmetic) d = off base (Layout.arithmetic + d) := by
    exact Offset.add_add base Layout.arithmetic d
  rw [address]
  apply F.read (r := ⟨off base (Layout.arithmetic + d), size⟩) (Region.contains_self _ _) ?_
    (by unfold Layout.arithmeticBytes at fit; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by
      simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride, Layout.arithmetic]; omega))
      (by simp only [Layout.arithmetic, Layout.arithmeticBytes] at fit ⊢; omega)
      (by simp only [VG.Impl.Mont.X86.Dynamic.slot, VG.Impl.Mont.X86.Dynamic.stride]; omega)
  · exact Offset.disjoint base (.inr (by
      simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes, Layout.arithmetic]; omega))
      (by simp only [Layout.arithmetic, Layout.arithmeticBytes] at fit ⊢; omega)
      (by simp only [montgomeryScratch, Spec.Rsa.MontMul.scratchBytes]; omega)
  · exact Offset.disjoint base (by omega)
      (by simp only [Layout.arithmetic, Layout.arithmeticBytes] at fit ⊢; omega)
      (by simp only [Layout.arithmetic, arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
  · exact (room.apart.sub_right (Offset.sub_base base targetFit)).symm

theorem witness_keeps {s t : State} {base : Addr} {bytes n : Nat}
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (room : CallRoom (s.gpr .esp) base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48) :
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem := by
  intro i hi _ arrays _
  have apart := arrays 5 (by simp)
  have read := witness_read (d := i) (size := 1) F room capacity upper
    (by change i + 1 ≤ 12288; omega) (by rcases apart with h | h <;> omega)
  have value := congrArg (fun x : BitVec (8 * 1) => x.extractLsb' (8 * 0) 8) read
  rw [Mem.extractLsb'_read t.mem _ (by decide : 0 < 1),
    Mem.extractLsb'_read s.mem _ (by decide : 0 < 1)] at value
  simpa only [off, BitVec.add_zero] using value

theorem witness_core {s t : State} {base : Addr} {bytes n : Nat}
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (room : CallRoom (s.gpr .esp) base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : VG.Proof.MillerRabin.PreparedCore s.mem (off base Layout.arithmetic))
    (W : wOf s.mem (off base Layout.arithmetic) = n) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) 1536 ∧
      VG.Proof.MillerRabin.PreparedCore t.mem (off base Layout.arithmetic) ∧
      wOf t.mem (off base Layout.arithmetic) = n := by
  have K : Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536
      (wOf s.mem (off base Layout.arithmetic)) s.mem t.mem := by
    rw [W]
    exact witness_keeps F room capacity upper
  obtain ⟨Lt, Pt⟩ := P.kept L K
  obtain ⟨_, width⟩ := VG.Proof.MillerRabin.kept_layout L K
  exact ⟨Lt, Pt, width.trans W⟩

theorem witness_prepared {s t : State} {base : Addr} {bytes n candidate : Nat}
    (F : WitnessFrame base (s.gpr .esp) n s t)
    (room : CallRoom (s.gpr .esp) base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic))
    (W : wOf s.mem (off base Layout.arithmetic) = n)
    (C : numAt s.mem (off base Layout.arithmetic) n 0 = candidate)
    (witness : numAt t.mem (off base Layout.arithmetic) n 5 < candidate) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) 1536 ∧
      Spec.MillerRabin.Prepared Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) ∧
      wOf t.mem (off base Layout.arithmetic) = n := by
  obtain ⟨Lt, core, width⟩ := witness_core F room capacity upper L (VG.Proof.MillerRabin.prepared_core P) W
  have fit : arrAt n 28 ≤ 12288 := by
    have bound : arrAt (wOf s.mem (off base Layout.arithmetic)) 28 ≤ 12288 := L.2.2.2.2.1
    rw [W] at bound
    exact bound
  have value : numAt t.mem (off base Layout.arithmetic) n 0 = candidate :=
    (VG.Proof.MillerRabin.kept_number (witness_keeps F room capacity upper) fit (j := 0) (.inl rfl)).trans C
  exact ⟨Lt, core.prepared (by rw [width, value]; exact witness), width⟩

end VG.Proof.Dsa.X86.Generation
