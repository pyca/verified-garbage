import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.P256.VerifyAllocated.Case
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing

/-! ## `JointLayout` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64

namespace JointLayout

theorem layout : Weierstrass.AArch64.JointLayout P256Joint.cfg 8192 where
  lay := {
    le := by decide +kernel
    apart := by
      have h : ∀ x∈jointSlots P256Joint.cfg,∀ y∈jointSlots P256Joint.cfg,
          x≠y → x+32≤y ∨ y+32≤x := by decide +kernel
      exact fun x y hx hy hxy => h x hx y hy hxy
    mo := by decide +kernel
    tmp := by decide +kernel }
  aligned := ⟨by decide +kernel, MP'_A p256,
    fun _ _ h => nomatch (callOf_small (M := p256.MP') (by decide)).symm.trans h⟩
  n := rfl
  stableBounds := by decide +kernel
  stableSep := by decide +kernel

theorem live_slots : ∀ x∈jointLive P256Joint.cfg,x∈jointSlots P256Joint.cfg := by decide +kernel

theorem work_slots : ∀ x∈jointWork P256Joint.cfg,x∈jointSlots P256Joint.cfg := by decide +kernel

theorem generator_bits : P256Joint.cfg.gBits=1504 := rfl

theorem peer_bits : P256Joint.cfg.K.bits=1824 := rfl

theorem bits_disjoint : P256Joint.cfg.gBits+264≤P256Joint.cfg.K.bits := by decide

theorem gprep_bounds : P256Joint.cfg.gBits<4096 ∧ P256Joint.cfg.gBits%8=0 ∧ P256Joint.cfg.gBits+264≤8192 := by decide

theorem qprep_bounds : P256Joint.cfg.K.bits<4096 ∧ P256Joint.cfg.K.bits%8=0 ∧ P256Joint.cfg.K.bits+264≤8192 := by decide

theorem fixedLayout : JointFixedLayout P256Joint.cfg 8192 where
  layout := layout
  exy := rfl
  entryNodup := by decide
  accumulator := by decide
  oneLive := by decide
  oneApart := by decide
  gBits := by decide
  addApart := ⟨by decide,by decide⟩
  copyApart := ⟨by decide,by decide⟩

end JointLayout
end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedField` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

abbrev cfg := P256Allocated.cfg
abbrev K := cfg.K
abbrev C := Spec.P256.curve
abbrev Sl := (·∈jointSlots cfg)
abbrev Frame := AllocatedFrame allocatedRegs

/-- The sparse compiler's exact arithmetic contract, independent of allocation. -/
def RawCorrect : Prop :=
  ∀ (ops : List FOp) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State},
    Inv K.M base 8192 C.p Sl V E s →
    (∀ op∈ops,∀ x∈op.out::op.ins,Sl x) → readsOk ops V=true →
    WP isa (.block (ops.flatMap VG.Impl.P256.VerifySparse.op)) s fun t =>
      ProgKeep K.M base (ops.map FOp.out) s t ∧
      Inv K.M base 8192 C.p Sl (validAfter ops V) (runOps ops E) t

/-- Only initialized, observed output slots cross the allocation boundary. -/
theorem field_ok (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl V E s)
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hout : ∀ x∈Out,x∈validAfter (operations k) V)
    (hobs : ∀ x∈Out,∀ i<4,Proof.P256.VerifyAllocated.observe k (x+8*i)) :
    WP isa (VG.Impl.P256.VerifyAllocated.program k) s fun t =>
      Frame base Proof.P256.VerifyAllocated.work s t ∧
      Inv K.M base 8192 C.p Sl Out (runOps (operations k) E) t := by
  refine WP.mono (cert.refine hi.scr (raw (operations k) hi hslots hreads))
    fun t ⟨u,⟨_,hu⟩,ho,hk⟩ => ?_
  have hs := hk.scr allocatedRegs_x0 hi.scr
  have hm := hi.mod.unch hk.unch
    (show ∀ w∈Proof.P256.VerifyAllocated.work,K.M.mo+8*K.M.n≤w.1 ∨ w.1+w.2≤K.M.mo by decide)
    hi.scr.nowrap
  refine ⟨hk,(hu.sub hout).of_observed hs hm fun x hx i him => ?_⟩
  apply ho (x+8*i) (hobs x hx i him)
  · have ha := JointLayout.layout.aligned.sl x (hu.sl x (hout x hx))
    omega
  · have hb := JointLayout.layout.lay.le x (hu.sl x (hout x hx))
    change i<4 at him
    change x+32≤8192 at hb
    omega

/-- Addition blocks retain all live field slots, including header temporaries. -/
theorem field_all_ok (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    (hk : k≠.doubleRR) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base 8192 C.p Sl V E s)
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true) :
    WP isa (VG.Impl.P256.VerifyAllocated.program k) s fun t =>
      Frame base Proof.P256.VerifyAllocated.work s t ∧
      Inv K.M base 8192 C.p Sl (validAfter (operations k) V) (runOps (operations k) E) t := by
  apply field_ok raw cert hi hslots hreads (fun _ hx => hx)
  intro x hx i hi4
  have hs : Sl x := by
    rw [mem_validAfter] at hx
    rcases hx with hx | hx
    · exact hi.sl x hx
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
      exact hslots op hop op.out (by simp)
  have bound : ∀ x∈jointSlots cfg,x+32≤6512 := by decide +kernel
  have hb := bound x hs
  exact ⟨Or.inl hk,Or.inl (by omega)⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end

/-! ## `AllocatedFieldTiming` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64.Allocated
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass

theorem field_relCT (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    {base : Addr} {V Out : List Nat} {E : Nat → Fe C}
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hout : ∀ x∈Out,x∈validAfter (operations k) V)
    (hobs : ∀ x∈Out,∀ i<4,Proof.P256.VerifyAllocated.observe k (x+8*i))
    (hct : FieldCT (VG.Impl.P256.VerifyAllocated.program k)) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E) (VG.Impl.P256.VerifyAllocated.program k)
      (FieldPair K.M base 8192 C.p Sl Out (runOps (operations k) E)) :=
  fieldWP_relCT hct fun _ hi => WP.mono (field_ok raw cert hi hslots hreads hout hobs)
    fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩

theorem field_all_relCT (raw : RawCorrect) {k : Kind} (cert : Proof.P256.VerifyAllocated.Case k)
    (hk : k≠.doubleRR) {base : Addr} {V : List Nat} {E : Nat → Fe C}
    (hslots : ∀ op∈operations k,∀ x∈op.out::op.ins,Sl x)
    (hreads : readsOk (operations k) V=true)
    (hct : FieldCT (VG.Impl.P256.VerifyAllocated.program k)) :
    RelCT isa (FieldPair K.M base 8192 C.p Sl V E) (VG.Impl.P256.VerifyAllocated.program k)
      (FieldPair K.M base 8192 C.p Sl (validAfter (operations k) V) (runOps (operations k) E)) :=
  fieldWP_relCT hct fun _ hi => WP.mono (field_all_ok raw cert hk hi hslots hreads)
    fun _ ⟨hk,it⟩ => ⟨it,hk.regs.sp⟩

end VG.Proof.Ecdsa.Verify.AArch64.Allocated

end
