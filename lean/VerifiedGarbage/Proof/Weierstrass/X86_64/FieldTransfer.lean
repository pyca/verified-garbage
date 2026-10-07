import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! Consecutive field transfers bridge table-copy memory facts to the field invariant. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def consecutiveFields (o n : Nat) : List Nat := (List.range n).map (fun i => o+32*i)

theorem Inv.transferConsecutiveFields {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n=4)
    {V : List Nat} {E : Nat → Fe C} {s t : State} (hI : Inv M base size C.p Sl V E s)
    {o n : Nat} {src : Nat → Nat} (hD : ∀ x∈consecutiveFields o n,Sl x)
    (hQ : ∀ i<n,src i∈V)
    (hv : ∀ i<n,wordsVal t.mem base (o+32*i) M.n=wordsVal s.mem base (src i) M.n)
    (hk : KeepRegs [.rax,.rcx,.rdx] s t) (ho : Outside base o (32*n) s.mem t.mem) :
    ProgKeep M base (consecutiveFields o n) s t ∧
    Inv M base size C.p Sl (consecutiveFields o n++V) (tmv C M.n base t) t ∧
    ∀ i<n,tmv C M.n base t (o+32*i)=E (src i) := by
  have kp : ProgKeep M base (consecutiveFields o n) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl|rfl|rfl <;> simp [clob]
    · by_contra h
      have hi : (ofs base x-o)/32<n := by omega
      have hm : o+32*((ofs base x-o)/32)∈consecutiveFields o n :=
        List.mem_map.mpr ⟨_,List.mem_range.mpr hi,rfl⟩
      have hf := hx _ hm
      rw [hn] at hf
      omega
  have hlt : ∀ x∈consecutiveFields o n,wordsVal t.mem base x M.n<C.p := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    rw [hv i hi']
    exact hI.lt _ (hQ i hi')
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,fun i hi => ?_⟩
  unfold tmv
  rw [hv i hi,hI.val _ (hQ i hi)]

end VG.Proof.Weierstrass.X86_64
