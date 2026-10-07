import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField

/-! Canonical cached powers for every table entry, with no scalar validity assumption. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

def cacheEnv {F : Type} [Mul F] (K : WinCfg) (E : Nat → F) : Nat → F :=
  Function.update (Function.update E (K.E.x+96) (E K.R.z*E K.R.z))
    (K.E.x+128) ((E K.R.z*E K.R.z)*E K.R.z)

theorem cacheEnv_readonly {F : Type} [Mul F] (K : WinCfg) (E : Nat → F) {x : Nat}
    (hx : x∉[K.E.x+96,K.E.x+128]) : cacheEnv K E x=E x := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
  simp only [cacheEnv,Function.update_of_ne hx.1,Function.update_of_ne hx.2]

theorem cache_fields_ok {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hn : K.M.n=4) (hL : Lay K.M size Sl)
    (hm : UnitMod m (2^(64*K.M.n)))
    (hz : K.R.z∉[K.E.x+96,K.E.x+128])
    (hSl : Sl (K.E.x+96) ∧ Sl (K.E.x+128))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s)
    (hV : K.R.z∈V) :
    WP isa (Impl.Ecdh.X86_64.Window5.cache K) s fun t =>
      ProgKeep K.M base [K.E.x+96,K.E.x+128] s t ∧
      Inv K.M base size m Sl ([K.E.x+96,K.E.x+128]++V) (cacheEnv K E) t ∧
      cacheEnv K E (K.E.x+96)=cacheEnv K E K.R.z*cacheEnv K E K.R.z ∧
      cacheEnv K E (K.E.x+128)=cacheEnv K E (K.E.x+96)*cacheEnv K E K.R.z := by
  let ops : List FOp := [.mul (K.E.x+96) K.R.z K.R.z,.mul (K.E.x+128) (K.E.x+96) K.R.z]
  have hs : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl|rfl <;>
      simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    · rcases hx with rfl|rfl|rfl
      · exact hSl.1
      · exact hI.sl _ hV
      · exact hI.sl _ hV
    · rcases hx with rfl|rfl|rfl
      · exact hSl.2
      · exact hSl.1
      · exact hI.sl _ hV
  have hr : readsOk ops V=true := by simp [ops,readsOk,FOp.ins,FOp.out,hV]
  have hz1 : K.R.z≠K.E.x+96 := fun h => hz (by simp [h])
  have he : runOps ops E=cacheEnv K E := by
    simp only [ops,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_self,
      Function.update_of_ne hz1,cacheEnv]
  change WP isa (ForwardField.programB K.M ops) s _
  refine WP.mono (ForwardField.programB_ok hn hL hm _ hI hs hr) fun t ⟨kt,it⟩ => ?_
  rw [he] at it
  refine ⟨kt.mono ?_,it.sub ?_,?_,?_⟩
  · intro x hx
    simpa only [ops,List.map_cons,List.map_nil,FOp.out] using hx
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx|hx
    · right
      simpa only [ops,List.map_cons,List.map_nil,FOp.out] using hx
    · exact Or.inl hx
  · rw [cacheEnv_readonly K E hz]
    simp only [cacheEnv,Function.update_of_ne (show K.E.x+96≠K.E.x+128 from by omega),
      Function.update_self]
  · rw [cacheEnv_readonly K E hz]
    simp only [cacheEnv,Function.update_of_ne (show K.E.x+96≠K.E.x+128 from by omega),
      Function.update_self]

end VG.Proof.Ecdh.X86_64.Secret
