module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialAllocated
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialEarly
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Bind the saved caller and argument frame to the shared packed-prime invariant. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem trial_allocated_sp (s : State) : (trialAllocated s).gpr .esp = s.gpr .esp - 40#32 := by
  rw [allocFrame_esp, pushed_esp]
  simp only [List.length_cons, List.length_nil]
  rw [BitVec.sub_sub]; rfl

theorem trial_allocated_fit {s : State} (low : 40 ≤ (s.gpr .esp).toNat) :
    ((trialAllocated s).gpr .esp).toNat + 36 ≤ 2 ^ 32 := by
  rw [trial_allocated_sp, VG.X86.sub_toNat low]
  have := (s.gpr .esp).isLt; omega

theorem trial_allocated_read {s : State} {base : Addr} {bytes d size : Nat}
    (scr : Scr s base bytes) (room : CallRoom (s.gpr .esp) base bytes) (fit : d + size ≤ bytes) :
    (trialAllocated s).mem.read (off base d) size = s.mem.read (off base d) size := by
  change (pushed [.edi] s).mem.read _ _ = _
  apply (pushed_frame (s := s) (rs := [.edi]) (by decide) (by change 4 ≤ (s.gpr .esp).toNat; have := room.low; omega)).read
    (r := ⟨base, bytes⟩) (Offset.contains_base base fit (by have := scr.nowrap; omega)) ?_
    (by have := scr.nowrap; omega)
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (room.apart.sub_left (below_sub (by decide) room.low)).symm

theorem trial_allocated_word {s : State} {base : Addr} {bytes d : Nat}
    (scr : Scr s base bytes) (room : CallRoom (s.gpr .esp) base bytes) (fit : d + 4 ≤ bytes) :
    (trialAllocated s).mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  unfold Mem.readW
  rw [trial_allocated_read (d := d) (size := 4) scr room fit]

theorem trial_allocated_val32 {s : State} {base : Addr} {bytes d count : Nat}
    (scr : Scr s base bytes) (room : CallRoom (s.gpr .esp) base bytes) (fit : d + 4 * count ≤ bytes) :
    val32 (trialAllocated s).mem base d count = val32 s.mem base d count :=
  val32_congr fun _ hi => congrArg BitVec.toNat (trial_allocated_word scr room (by omega))

theorem TrialSetup.machine {s t : State} {base : Addr} {bytes n : Nat}
    (H : TrialSetup s n t) (scr : Scr s base bytes) (room : CallRoom (s.gpr .esp) base bytes) :
    TrialMachine (trialAllocated s) base bytes ((trialAllocated s).gpr .esp)
      (fun i => trialSlot t.mem ((trialAllocated s).gpr .esp) i) t := by
  refine ⟨⟨H.args.keeps.1 .esp (by decide), trial_allocated_fit room.low, ?_⟩,
    ⟨?_, scr.nowrap⟩, ?_, H.args.frame, H.args.keeps.mono (by decide), fun _ _ => rfl⟩
  · rw [H.args.keeps.2.2, allocFrame_wr]; exact List.mem_cons_self ..
  · rw [H.args.keeps.2.2, allocFrame_wr, pushed_wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ scr.wr)
  · rw [trial_allocated_sp]
    exact (room.apart.sub_left (Region.sub_prefix (by decide : 36 ≤ 40))).symm

theorem TrialSetup.argument_values {s t : State} {base : Addr} {bytes n : Nat}
    (H : TrialSetup s n t) (scr : Scr s base bytes) :
    trialSlot t.mem ((trialAllocated s).gpr .esp) 0 = BitVec.ofNat 32 (base.toNat + slot n 0) ∧
      trialSlot t.mem ((trialAllocated s).gpr .esp) 1 = BitVec.ofNat 32 (base.toNat + slot n 0) + BitVec.ofNat 32 (8 * n) ∧
      trialSlot t.mem ((trialAllocated s).gpr .esp) 2 = BitVec.ofNat 32 (base.toNat + trialTableOffset) ∧
      trialSlot t.mem ((trialAllocated s).gpr .esp) 3 = BitVec.ofNat 32 (trialWordCount n) := by
  have edi : (trialAllocated s).gpr .edi = BitVec.ofNat 32 base.toNat := by
    rw [allocFrame_gpr _ _ (by decide), pushed_gpr _ _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [scr.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have bound := (s.gpr .edi).isLt
      rw [scr.edi_toNat] at bound
      exact bound)]
  have value (i : Nat) (hi : i < 4) : trialSlot t.mem ((trialAllocated s).gpr .esp) i =
      trialArgument ((trialAllocated s).gpr .edi) n i := H.args.words i hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [value 0 (by decide)]; simp only [trialArgument, edi, BitVec.ofNat_add]
  · rw [value 1 (by decide)]; simp only [trialArgument, edi, BitVec.ofNat_add, BitVec.add_assoc]
  · rw [value 2 (by decide)]; simp only [trialArgument, edi, BitVec.ofNat_add]
  · exact value 3 (by decide)

def trialPlan (base : Addr) (bytes n : Nat) (capacity : 40960 ≤ bytes) (positive : 0 < n) (upper : n ≤ 48) : TrialPlan where
  base := base
  bytes := bytes
  candidate := slot n 0
  width := n
  table := trialTableOffset
  count := trialWordCount n
  candidateFits := by simp only [slot, stride]; omega
  widthSmall := by omega
  widthPositive := positive
  tableFits := by unfold trialTableOffset trialWordCount; split <;> omega
  countPositive := by unfold trialWordCount; split <;> decide
  countBound := by unfold trialWordCount; split <;> decide

end VG.Proof.Dsa.X86.Generation
