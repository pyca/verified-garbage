import VerifiedGarbage.Proof.Weierstrass.X86.NafPoint

/-! An exact field environment for point transfers through public addresses. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.X86

def pointTransferEnv {F : Type _} (E : Nat → F) (o q : Pt) (x : Nat) : F :=
  if x=o.x then E q.x else if x=o.y then E q.y else if x=o.z then E q.z else E x

theorem Inv.transferPointFields {FM : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk FM M m size wk Sl)
    {o q : Pt} (hy : o.y=o.x+8*M.n) (hz : o.z=o.x+16*M.n)
    {V : List Nat} {E : Nat → Fin m} {s t : State}
    (hI : Inv M base size m Sl V E s)
    (hD : ∀ x∈jacCoords o, Sl x) (hQ : ∀ x∈jacCoords q, x∈V)
    (vx : wordsVal t.mem base o.x M.n=wordsVal s.mem base q.x M.n)
    (vy : wordsVal t.mem base o.y M.n=wordsVal s.mem base q.y M.n)
    (vz : wordsVal t.mem base o.z M.n=wordsVal s.mem base q.z M.n)
    (hk : KeepRegs [.eax,.ecx,.edx] s t) (ho : Outside base o.x (24*M.n) s.mem t.mem) :
    ProgKeep M base wk (jacCoords o) s t ∧
    Inv M base size m Sl (jacCoords o++V) (pointTransferEnv E o q) t := by
  have kp : ProgKeep M base wk (jacCoords o) s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,fun x hx => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx (o.x,8*M.n) (by simp [progW,jacCoords])
      have hx₁ := hx (o.y,8*M.n) (by simp [progW,jacCoords])
      have hx₂ := hx (o.z,8*M.n) (by simp [progW,jacCoords])
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega
  have hlt : ∀ x∈jacCoords o, wordsVal t.mem base x M.n<m := by
    intro x hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vy]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
    · rw [vz]; exact hI.lt _ (hQ _ (by simp [jacCoords]))
  have hi := hI.of_progKeep hL hW kp hD hlt
  refine ⟨kp,{hi with val := ?_}⟩
  intro x hx
  simp only [pointTransferEnv]
  split
  · subst x
    rw [vx,hI.val _ (hQ _ (by simp [jacCoords]))]
  · split
    · subst x
      rw [vy,hI.val _ (hQ _ (by simp [jacCoords]))]
    · split
      · subst x
        rw [vz,hI.val _ (hQ _ (by simp [jacCoords]))]
      · have hnot : x∉jacCoords o := by simp_all only [jacCoords,List.mem_cons,List.not_mem_nil,or_false,not_false_eq_true]
        have hv : x∈V := (List.mem_append.mp hx).resolve_left hnot
        rw [kp.slot hL hW hI.scr hD (hI.sl x hv) hnot,hI.val x hv]

end VG.Proof.Weierstrass.X86
