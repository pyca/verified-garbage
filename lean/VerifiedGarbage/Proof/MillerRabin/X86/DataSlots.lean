module

public import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! # A verified block updates several scratch words without losing array values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont

def slotWrites (slots : List Nat) : List (Nat × Nat) := slots.map fun d => (d, 4)

theorem Data.afterSlots {g : Geometry} (v : g.Valid) {A : Nat → Nat} {Js : List Nat}
    {V V' : Nat → BitVec 32} {Ds : List Nat} {s t : State} (D : Data g A Js V Ds s)
    (C : Context g t) (changed : List Nat)
    (stored : ∀ d ∈ changed, scratchWord d ∧ t.mem.readW (off g.W d) 32 = V' d)
    (unchanged : ∀ d ∈ Ds, d ∉ changed → V' d = V d)
    (O : Outs g.W (slotWrites changed) s.mem t.mem) :
    Data g A Js V' (changed ++ Ds) t := by
  have W := WorkspaceFrame.of_outs C.ws.nowrap O
  refine ⟨C, ?_, ?_⟩
  · intro j known
    obtain ⟨index, read⟩ := D.arrayValues j known
    refine ⟨index, ?_⟩
    rw [W.val32 (v.arrayFit index) (by
      intro r mem
      obtain ⟨d, knownD, rfl⟩ := List.mem_map.mp mem
      right
      exact Nat.le_trans (scratch_fit (stored d knownD).1) (v.arrayHeader j)), read]
  · intro d known
    by_cases changedD : d ∈ changed
    · exact stored d changedD
    · have old : d ∈ Ds := (List.mem_append.mp known).resolve_left changedD
      obtain ⟨scratch, read⟩ := D.slotValues d old
      refine ⟨scratch, ?_⟩
      rw [W.read32 (by have := scratch_fit scratch; have := v.headerFit; omega) (by
        intro r mem
        obtain ⟨e, knownE, rfl⟩ := List.mem_map.mp mem
        exact scratch_apart scratch (stored e knownE).1 (fun eq => changedD (eq ▸ knownE))),
        read, unchanged d old changedD]

end VG.Proof.MillerRabin.X86
