import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedArithmetic
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedRaw
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

private theorem slots_joint : ∀ x,Sl x → Ecdsa.Verify.AArch64.Allocated.Sl x := by decide +kernel

 theorem hotField_ok {k : Kind} (cert : VerifyAllocated.Case k)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hslots : ∀ op∈operations k,∀x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hout : ∀x∈Out,x∈validAfter (operations k) V)
    (hobs : ∀x∈Out,∀i<4,VerifyAllocated.observe k (x+8*i)) :
    WP isa (Impl.P256.VerifyAllocated.program k) s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl Out (runOps (operations k) E) t := by
  have hi' : Inv M base 8192 C.p Ecdsa.Verify.AArch64.Allocated.Sl V E s :=
    ⟨hi.scr,hi.mod,fun x hx => slots_joint x (hi.sl x hx),hi.lt,hi.val⟩
  refine WP.mono (Ecdsa.Verify.AArch64.Allocated.field_ok
    Ecdsa.Verify.AArch64.Allocated.raw_correct cert hi'
    (fun op hop x hx => slots_joint x (hslots op hop x hx)) hreads hout hobs)
    fun t ⟨hk,it⟩ => ⟨hk.mono (fun _ h => h) (by decide +kernel),?_,?_,?_,?_,?_⟩
  · exact it.scr
  · exact it.mod
  · intro x hx
    rcases (mem_validAfter _ _).mp (hout x hx) with hh|hh
    · exact hi.sl x hh
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hh
      exact hslots op hop op.out (by simp)
  · exact it.lt
  · exact it.val


theorem hotField_all_ok {k : Kind} (cert : VerifyAllocated.Case k) (hk : k≠.doubleRR)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hslots : ∀op∈operations k,∀x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true) :
    WP isa (Impl.P256.VerifyAllocated.program k) s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl (validAfter (operations k) V) (runOps (operations k) E) t := by
  apply hotField_ok cert hi hslots hreads (fun _ h => h)
  intro x hx i hi4
  have hs : Sl x := by
    rcases (mem_validAfter _ _).mp hx with hv|hv
    · exact hi.sl x hv
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hv
      exact hslots op hop op.out (by simp)
  have hb := (show ∀ x,Sl x → x+32≤5464 from by decide +kernel) x hs
  exact ⟨Or.inl hk,Or.inl (by omega)⟩

 theorem add_ok {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s) (hv : ∀x∈CachedField.inputs,x∈V)
    (h2 : E 5400=E 768*E 768) (h3 : E 5432=E 768*(E 768*E 768)) :
    WP isa Impl.P256.EcdhJac.add s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl ([K.D.x,K.D.y,K.D.z]++V)
        (runOps (CachedField.head++CachedField.tail) E) t ∧
      (runOps (CachedField.head++CachedField.tail) E K.D.x,
       runOps (CachedField.head++CachedField.tail) E K.D.y,
       runOps (CachedField.head++CachedField.tail) E K.D.z)=
        jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hr := readsOk_mono CachedField.reads_full hv
  rw [readsOk_append,Bool.and_eq_true] at hr
  refine WP.seq (WP.mono (hotField_all_ok VerifyAllocated.CachedHead.caseProof (by decide)
    hi (by decide +kernel) hr.1) fun a ⟨ka,ia⟩ => ?_)
  refine WP.mono (hotField_all_ok VerifyAllocated.JacTail.caseProof (by decide)
    ia (by decide +kernel) hr.2) fun t ⟨kt,it⟩ => ⟨ka.trans kt,?_,CachedField.full_values E h2 h3⟩
  rw [runOps_append]
  apply it.sub
  intro x hx
  rw [mem_validAfter]
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inr (CachedField.out_tail x hx)
  · exact Or.inl ((mem_validAfter _ _).mpr (Or.inl hx))

 theorem double_ok (hC : Law C) (ha : AM3 C) {base : Addr} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C}
    (hp : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhJac.double s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) := by
  exact EcdhDouble.Verified.double_ok hC ha hi hp hj

end VG.Proof.P256.EcdhJac
