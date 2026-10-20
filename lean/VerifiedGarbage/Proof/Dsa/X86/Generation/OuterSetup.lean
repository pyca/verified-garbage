module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryStart
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SaveFrame
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-! # Allocate the save frame and establish the inner entry after saving registers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def outerBase (s : State) : Addr := (s.gpr .esp - 16#32).setWidth 64

theorem ParameterABI.outerBase_eq {s : State} (A : ParameterABI s) :
    outerBase s = (s.gpr .esp).setWidth 64 - 16#64 :=
  Taint.sub_setWidth (by have := A.stackLow; omega)

theorem ParameterABI.outerFrame {s : State} (A : ParameterABI s) : SaveFrame (allocated 16 s) (outerBase s) := by
  refine ⟨rfl, List.mem_cons_self, ?_⟩
  rw [A.outerBase_eq, BitVec.toNat_sub_of_le (by
    change 16 ≤ ((s.gpr .esp).setWidth 64).toNat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt (by decide))]
    have := A.stackLow; omega)]
  have hi := A.stackBound
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt (by decide))]
  change (s.gpr .esp).toNat - 16 + 16 ≤ 2 ^ 32
  omega

theorem inner_esp {s t : State} (K : Keeps [] (allocated 16 s) t) :
    (allocated 148 t).gpr .esp = entryFrame s := by
  rw [allocated_esp, K.1 _ (by decide), allocated_esp]
  change s.gpr .esp - 16#32 - 148#32 = s.gpr .esp - 164#32
  rw [BitVec.sub_sub]; rfl

theorem afterSave_start {s t : State} (A : ParameterABI s)
    (O : Frame [⟨outerBase s, 16⟩] (allocated 16 s).mem t.mem) (K : Keeps [] (allocated 16 s) t) :
    EntryStart A (allocated 148 t) := by
  have esp := inner_esp K
  have wr : (allocated 148 t).wr =
      ⟨A.geometry.frameBase, 148⟩ :: ⟨outerBase s, 16⟩ :: s.wr := by
    rw [allocated_wr, K.2.2, allocated_wr]
    change (⟨((allocated 148 t).gpr .esp).setWidth 64, 148⟩ : Region) :: _ = _
    rw [esp]; rfl
  refine ⟨esp, K.2.1, by rw [wr]; exact List.mem_cons_self, ?_, ?_, ?_, ?_⟩
  · rw [wr, A.wr]; simp
  · rw [wr, A.wr]; simp
  · rw [wr, A.wr]; simp
  · change Frame _ s.mem t.mem
    apply O.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [A.outerBase_eq]
    exact fun x hx => Offset.below_mono _ (a := 16) (b := 292) (by decide) (by decide) x hx

theorem saved_allocated {s : State} {mem : Mem} (S : SavedRegisters (allocated 16 s) (outerBase s) mem) :
    SavedRegisters s (outerBase s) mem := by
  obtain ⟨b, p, si, di⟩ := S
  exact ⟨b.trans (allocated_gpr _ _ (by decide)), p.trans (allocated_gpr _ _ (by decide)),
    si.trans (allocated_gpr _ _ (by decide)), di.trans (allocated_gpr _ _ (by decide))⟩
end VG.Proof.Dsa.X86.Generation
