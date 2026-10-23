module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryCore
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs

/-! # Nested calls write below the saved i686 register frame -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem Entry.body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (entered s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (entered s) t ∧
      Frame ([⟨wsOf s, lenOf s⟩] ++ [below ((entered s).gpr .esp) 80]) (entered s).mem t.mem := by
  have writable : Covers [⟨wsOf s, lenOf s⟩] (entered s).wr := by
    apply Covers.of_mem
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    rw [entered, Compact.entered, pushed_wr, E.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  refine WP.narrowSp E.narrowed_body ?_ writable body_noSp ?_ ?_
  · exact Covers.append (Covers.refl _) writable
  · have := E.caller.low
    exact Nat.le_trans body_stack this
  · intro t rd wr F R
    refine ⟨R.1, ⟨R.2.1, rd, wr⟩, ?_⟩
    apply F.sub
    intro r mem
    rcases List.mem_append.mp mem with mem | mem
    · exact ⟨r, List.mem_append_left _ mem, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp mem
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub body_stack E.caller.low⟩

end VG.Proof.MillerRabin.X86
