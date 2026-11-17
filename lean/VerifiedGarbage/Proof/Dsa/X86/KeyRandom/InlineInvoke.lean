module

public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! A shared inlined cdecl boundary for the checker and prevalidated derivation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem inlineInvoke_ok {body : Prog isa} {s : State} {rd wr : List Region} {Q : Mem → BitVec 32 → Prop}
    (safe : NoSp body) (depth : stackUse body≤108) (low : 112≤(s.gpr .esp).toNat)
    (reads : Covers (rd++wr) (s.rd++s.wr)) (writes : Covers wr s.wr)
    (correct : WP isa body ((allocated 4 s).withRegions rd wr) fun u =>
      abiPreserved ((allocated 4 s).withRegions rd wr) u ∧ Q u.mem (u.gpr .eax))
    (hQ : ∀ m m' ax, Frame [below (s.gpr .esp) 112] m m' → Q m ax → Q m' ax) :
    WP isa (VG.Impl.Dsa.X86.Comb.invoke body) s fun u =>
      u.rd=s.rd ∧ u.wr=s.wr ∧ (∀ r∈calleeSaved, u.gpr r=s.gpr r) ∧
      Frame (wr++[below (s.gpr .esp) 112]) s.mem u.mem ∧ Q u.mem (u.gpr .eax) := by
  have readWide : Covers (rd++wr) ((allocated 4 s).rd++(allocated 4 s).wr) :=
    reads.trans (Covers.append (Covers.refl _) (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr))
  have writeWide : Covers wr (allocated 4 s).wr :=
    writes.trans (Covers.of_mem fun _ hr => List.mem_cons_of_mem _ hr)
  refine WP.alloc (by decide) (by omega_using [low]) safe
    (WP.narrowSp correct readWide writeWide safe
      (by rw [allocated_esp,sub_toNat (by omega_using [low])]; omega_using [depth, low])
      (Q := fun v => v.rd = (allocated 4 s).rd ∧ v.wr = (allocated 4 s).wr ∧
        Frame (wr ++ [below ((allocated 4 s).gpr .esp) (stackUse body)]) (allocated 4 s).mem v.mem ∧
        (∀ r ∈ calleeSaved, v.gpr r = (allocated 4 s).gpr r) ∧ Q v.mem (v.gpr .eax))
      fun v rdv wrv F ⟨ABI,V⟩ => ⟨rdv,wrv,F,ABI.1,V⟩)
    fun v m uu ⟨rdv,wrv,F,saved,V⟩ fl => ?_
  have fl' : Frame [below (s.gpr .esp) 112] v.mem m := fl.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_singleton_self _,below_sub (by decide) low⟩
  refine ⟨rdv,?_,?_,?_,?_⟩
  · change v.wr.tail=s.wr
    rw [wrv]; rfl
  · intro r hr
    by_cases esp : r=.esp
    · subst r
      rw [freed_esp]
      change v.gpr .esp + BitVec.ofNat 32 4 = _
      rw [saved .esp hr]
      change s.gpr .esp-4+4=s.gpr .esp
      exact BitVec.sub_add_cancel _ _
    · rw [freed_gpr _ _ esp]
      change v.gpr r = _
      rw [saved r hr]
      exact allocated_gpr _ _ esp
  · show Frame _ s.mem m
    refine (F.sub ?_).trans (fl'.sub ?_)
    · intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · exact ⟨r,List.mem_append_left _ hr,fun _ h => h⟩
      · obtain rfl := List.mem_singleton.mp hr
        exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),
          below_inner (by omega_using [depth]) low⟩
    · intro r hr
      exact ⟨r,List.mem_append_right _ hr,fun _ h => h⟩
  · rw [freed_gpr _ _ (by decide)]
    exact hQ _ _ _ fl' V

end VG.Proof.Dsa.X86.KeyRandom
