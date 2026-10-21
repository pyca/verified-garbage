module

public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Covers

/-! A shared inlined cdecl boundary for the checker and prevalidated derivation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem inlineInvoke_ok {body : Prog isa} {s : State} {rd wr : List Region} {Q : Mem → BitVec 32 → Prop}
    (safe : NoSp body) (depth : stackUse body≤20) (low : 24≤(s.gpr .esp).toNat)
    (reads : Covers (rd++wr) (s.rd++s.wr)) (writes : Covers wr s.wr)
    (correct : WP isa body ((allocated 4 s).withRegions rd wr) fun u =>
      abiPreserved ((allocated 4 s).withRegions rd wr) u ∧ Q u.mem (u.gpr .eax)) :
    WP isa (VG.Impl.Dsa.X86.Comb.invoke body) s fun u =>
      u.rd=s.rd ∧ u.wr=s.wr ∧ (∀ r∈calleeSaved, u.gpr r=s.gpr r) ∧
      Frame (wr++[below (s.gpr .esp) 24]) s.mem u.mem ∧ Q u.mem (u.gpr .eax) := by
  have readWide : Covers (rd++wr) ((allocated 4 s).rd++(allocated 4 s).wr) :=
    reads.trans (Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr))
  have writeWide : Covers wr (allocated 4 s).wr :=
    writes.trans (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)
  refine WP.alloc (by decide) (by omega) safe ?_
  refine WP.narrowSp correct readWide writeWide safe
    (by rw [allocated_esp,sub_toNat (by omega)]; omega) ?_
  intro v rdv wrv F ⟨ABI,V⟩
  have saved : ∀ r∈calleeSaved, v.gpr r=(allocated 4 s).gpr r := ABI.1
  refine ⟨rdv,?_,?_,?_,?_⟩
  · change v.wr.tail=s.wr
    rw [wrv]; rfl
  · intro r hr
    by_cases esp : r=.esp
    · subst r
      rw [freed_esp,saved .esp hr]
      change s.gpr .esp-4+4=s.gpr .esp
      exact BitVec.sub_add_cancel _ _
    · rw [freed_gpr _ _ esp,saved r hr]
      exact allocated_gpr _ _ esp
  · apply F.sub
    intro r hr
    rcases List.mem_append.mp hr with hr|hr
    · exact ⟨r,List.mem_append_left _ hr,fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),
        below_inner (by omega) low⟩
  · rw [freed_gpr _ _ (by decide)]
    exact V

end VG.Proof.Dsa.X86.KeyRandom
