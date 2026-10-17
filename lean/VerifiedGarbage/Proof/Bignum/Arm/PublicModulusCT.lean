module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicValidCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicFailCT
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Modulus validation branches only on the public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicModulusInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  source : s.gpr .r4 = np
  count : s.gpr .r6 = BitVec.ofNat 32 k

structure PublicModulusChecked (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicModulusInput base dst np ep xp len k eLen nb eb xb s where
  flag : s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k

theorem publicModulusArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PcFn.inputs) s (PublicModulusInput base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (pcInputs_ok s h.stack.pcStack) ?_
  rintro t ⟨source, count, mem, rest⟩
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), source, count⟩

theorem publicModulusCheck_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicModulusInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block modulusCheck) s (PublicModulusChecked base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (modulusCheck_ok s h.buffers.minLength h.buffers.maxLength h.buffers.modulus.fits
    h.buffers.modulus.read h.source h.count) ?_
  rintro t ⟨flag, mem, rest⟩
  exact ⟨⟨h.toPublicBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr),
    (rest.gpr .r4 (by simp)).trans h.source, (rest.gpr .r6 (by simp)).trans h.count⟩,
    by rw [h.buffers.modulus.bytes] at flag; exact flag⟩

theorem publicModulus_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.modulus (fun _ _ => True) := by
  let P := fun (s t : State) => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  let Q := fun (s t : State) => s.sp = t.sp ∧ PublicModulusInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicModulusInput base dst np ep xp len k eLen nb eb xb2 t
  have args := ((stackLoads_ct [(.r4, 8), (.r6, 12)]).mono (P' := P)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicModulusArgs_ready s h.1, publicModulusArgs_ready t h.2.1⟩)
  have check : RelCT isa Q (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.source.trans h.2.2.source.symm, h.2.1.count.trans h.2.2.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.1)).wp
    (fun s t h => ⟨publicModulusCheck_ready s h.2.1, publicModulusCheck_ready t h.2.2⟩)
  refine args.seq (ready.seq (RelCT.ite ?_ ?_ ?_))
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.flag, h.2.2.flag]
  · apply (publicValid_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
      (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono ?_ (fun _ _ h => h)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.flag.symm.trans flag
    exact ⟨⟨h.1.2.1.toPublicBodyInput, good, h.1.2.1.source, h.1.2.1.count⟩,
      ⟨h.1.2.2.toPublicBodyInput, good, h.1.2.2.source, h.1.2.2.count⟩, h.1.1⟩
  · apply (publicFail_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
      (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono ?_ (fun _ _ h => h)
    intro s t h
    exact ⟨h.1.2.1.toPublicBodyInput, h.1.2.2.toPublicBodyInput, h.1.1⟩

end VG.Proof.Bignum.Arm
