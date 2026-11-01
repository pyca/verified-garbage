module

public import VerifiedGarbage.Proof.P256.EcdhTable.Dblu
public import VerifiedGarbage.Proof.P256.EcdhTable.Zaddu
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
public import VerifiedGarbage.Proof.P256.EcdhJac.TableMath
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract

/-! ECDH's allocated DBLU and ZADDU blocks on any slot predicate holding their
slots: the raw field programs' contract, carried to the allocated code through
their certificates on the observed slots. -/

@[expose] public section

namespace VG.Proof.P256.VerifyTable
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

abbrev C := Spec.P256.curve
abbrev M := VG.Impl.P256.EcdhJac.K.M

/-- The slots DBLU and ZADDU name. -/
def slots : List Nat := Proof.P256.EcdhJac.tblW ++ [1280,1440,224]

def observe (doubling : Bool) (off : Nat) : Prop :=
  if doubling then Proof.P256.EcdhTable.Dblu.observe off else Proof.P256.EcdhTable.Zaddu.observe off
instance (doubling : Bool) (off : Nat) : Decidable (observe doubling off) := by
  unfold observe; split <;> infer_instance

theorem raw_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hs : ∀ x∈slots,Sl x) (doubling : Bool)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hreads : readsOk (Impl.P256.EcdhTable.operations doubling) V=true) :
    WP isa (.block (Impl.P256.EcdhTable.raw doubling)) s fun t =>
      ProgKeep M base ((Impl.P256.EcdhTable.operations doubling).map FOp.out) s t ∧
      Inv M base 8192 C.p Sl (validAfter (Impl.P256.EcdhTable.operations doubling) V)
        (runOps (Impl.P256.EcdhTable.operations doubling) E) t := by
  have hsl : ∀ op∈Impl.P256.EcdhTable.operations doubling,∀ x∈op.out::op.ins,Sl x := by
    intro op hop x hx
    apply hs
    cases doubling <;>
      exact (show ∀ op∈Impl.P256.EcdhTable.operations _,∀ x∈op.out::op.ins,x∈slots by decide +kernel) op hop x hx
  exact VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned (unitMod_pow_two (by decide) _)
    _ hi hsl hreads

theorem refine (doubling : Bool) {base : Addr} {s : State} (hs : Scr s base 8192)
    {Q : State → Prop} (hq : WP isa (.block (Impl.P256.EcdhTable.raw doubling)) s Q) :
    WP isa (Impl.P256.EcdhTable.program doubling) s fun t => ∃ u,Q u ∧
      (∀ off,observe doubling off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      AllocatedFrame allocatedRegs base Proof.P256.EcdhJac.work s t := by
  cases doubling
  · exact Proof.P256.EcdhTable.Zaddu.refine hs hq
  · exact Proof.P256.EcdhTable.Dblu.refine hs hq

/-- The allocated block's field contract on observed output slots `Out`. -/
theorem program_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hs : ∀ x∈slots,Sl x) (doubling : Bool)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s)
    (hreads : readsOk (Impl.P256.EcdhTable.operations doubling) V=true)
    (hout : ∀ x∈Out,x∈validAfter (Impl.P256.EcdhTable.operations doubling) V)
    (hobs : ∀ x∈Out,∀ i<4,observe doubling (x+8*i)) :
    WP isa (Impl.P256.EcdhTable.program doubling) s fun t =>
      AllocatedFrame allocatedRegs base Proof.P256.EcdhJac.work s t ∧
      Inv M base 8192 C.p Sl Out (runOps (Impl.P256.EcdhTable.operations doubling) E) t := by
  refine WP.mono (refine doubling hi.scr (raw_ok layout aligned hs doubling hi hreads))
    fun t ⟨u,⟨_,hu⟩,ho,hk⟩ => ⟨hk,?_⟩
  have ht := hk.scr allocatedRegs_x0 hi.scr
  have hm := hi.mod.unch hk.unch
    (show ∀ w∈Proof.P256.EcdhJac.work,M.mo+8*M.n≤w.1 ∨ w.1+w.2≤M.mo by decide) hi.scr.nowrap
  refine (hu.sub hout).of_observed ht hm fun x hx i him => ?_
  apply ho (x+8*i) (hobs x hx i him)
  · have ha := aligned.sl x (hu.sl x (hout x hx))
    omega
  · have hb := layout.le x (hu.sl x (hout x hx))
    change i<4 at him
    change x+32≤8192 at hb
    omega

end VG.Proof.P256.VerifyTable
