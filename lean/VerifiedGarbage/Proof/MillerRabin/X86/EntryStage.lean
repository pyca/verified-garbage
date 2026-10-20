module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryValues
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory

/-! # ABI setup establishes the complete round stage with workspace-only writes -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86

def narrowed (s : State) : State := (entered s).withRegions (entered s).rd [⟨wsOf s, lenOf s⟩]

theorem Entry.narrowed_caller {s : State} (E : Entry s) :
    Caller (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (narrowed s) := by
  have C := E.caller
  refine ⟨C.sp, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1)) = _
  have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1) = argAddr s 1 := Compact.argument_address s 1
  rw [ea]
  have access : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 1) 4 := by
    change InRegions ((entered s).rd ++ _) _ _
    rw [entered, Compact.entered, pushed_rd, E.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    rw [argument_offset E (by decide : 1 < 2)]
    exact Offset.contains_base _ (by decide : 4 * 1 + 4 ≤ 8) (by decide)
  rw [State.load32, ite_eq_left access]
  change some ((entered s).mem.readW (argAddr s 1) 32) = _
  rw [E.pushed_arg (by decide : 1 < 2), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Entry.narrowed_base {s : State} (E : Entry s) :
    WP isa (.block [.mov .edi (.mem (at_ .esp 20))]) (narrowed s) fun t =>
      Stage (geometry s) (arg s 1).toNat (initialValues s 0) ((entered s).gpr .esp)
        (initialValues s) initialArrays (fun _ => 0) [] t ∧
      t.mem = (entered s).mem ∧ Keeps [.edi] (narrowed s) t := by
  have access : readSrc (narrowed s) (.mem (at_ .esp 20)) = some (arg s 0) := by
    change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0)) = _
    have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0) = argAddr s 0 := Compact.argument_address s 0
    rw [ea, State.load32]
    have region : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 0) 4 := by
      change InRegions ((entered s).rd ++ _) _ _
      rw [entered, Compact.entered, pushed_rd, E.rd]
      refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      simpa only [BitVec.add_zero] using
        (Offset.contains_base (argAddr s 0) (by decide : 0 + 4 ≤ 8) (by decide))
    rw [ite_eq_left region]
    exact congrArg some (E.pushed_arg (by decide : 0 < 2))
  refine wp_movS access fun t T _ => WP.block_nil ?_
  have mem : t.mem = (entered s).mem := T.mem
  have workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr := by
    rw [T.wr]
    exact List.mem_singleton_self _
  have base : PtrAt t (wsOf s) .edi 0 := by
    rw [PtrAt, T.gpr, Nat.add_zero, E.ws_toNat]
    exact (Nat.mod_eq_of_lt (arg s 0).isLt).symm
  refine ⟨⟨E.data mem workspace base, E.modulus mem, ?_, ?_⟩, mem, T.keeps⟩
  · apply E.narrowed_caller.keepFrame T.keeps (by decide)
    rw [T.mem]
    exact Frame.refl _ _
  · intro j known
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
