import VerifiedGarbage.Proof.P256.EcdhJac.TableMath
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.P256.EcdhJac.Frame

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

 theorem table_raw_field {N : List FOp}
    (hout : ∀op∈N,op.out<13)
    {Rd : List Nat} (hreads : readsOk N Rd=true)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s) (hv : ∀i∈Rd,tblσ i∈V) :
    WP isa (.block ((N.map (FOp.rename tblσ)).flatMap Impl.P256.VerifySparse.op)) s fun t =>
      ProgKeep M base tblW s t ∧
      Inv M base 8192 C.p Sl (validAfter (N.map (FOp.rename tblσ)) V)
        (runOps (N.map (FOp.rename tblσ)) E) t ∧
      ∀i,runOps (N.map (FOp.rename tblσ)) E (tblσ i)=runOps N (fun j => E (tblσ j)) i := by
  have nd : tblW.Nodup := by decide
  have hp : ∀x∈[K.P.x,K.P.y,K.P.z],x∉tblW := by decide
  have inj : ∀op∈N,∀y,tblσ y=tblσ op.out→y=op.out := fun op hop y =>
    getD_append_inj nd hp (hp _ (by simp)) (by simpa [tblW] using hout op hop) y
  have hs : ∀i,Sl (tblσ i) := fun i =>
    (show ∀x∈tblW++[K.P.x,K.P.y,K.P.z],Sl x from by decide +kernel) _
      (getD_append_mem (by simp) i)
  have hsops : ∀op∈N.map (FOp.rename tblσ),∀x∈op.out::op.ins,Sl x := by
    intro op hop
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hop
    cases op <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] <;>
      rintro x (rfl|rfl|rfl) <;> exact hs _
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned (unitMod_pow_two (by decide) _)
    (N.map (FOp.rename tblσ)) hi hsops
    (readsOk_mono (readsOk_rename tblσ hreads) (by
      intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hv i hi))) fun t ⟨kt,it⟩ =>
      ⟨kt.mono ?_,it,fun i => congrFun (runOps_rename tblσ N E inj) i⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  obtain ⟨op,hopN,rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  unfold tblσ
  rw [getD_append_left (by simpa [tblW] using hout op hopN)]
  exact List.getElem_mem _

end VG.Proof.P256.EcdhJac
