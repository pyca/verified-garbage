module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBody
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
meta import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Checked public RSA permits different secret inputs with identical leakage -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicExponentInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  exponent : ExponentInput ep eb s

structure PublicExponentResult (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  status : s.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat

structure PublicExponentChecked (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop extends PublicBodyInput base dst np ep xp len k eLen nb eb xb s where
  flag : s.z = !Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)

theorem publicExponentArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicBodyInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PublicFn.exponentArgs) s (PublicExponentInput base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (publicExponentArgs_ok s h.stack) ?_
  rintro t ⟨pointer, count, mem, rest⟩
  have ht := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  have length := ht.buffers.exponent.length
  exact ⟨ht, ⟨⟨by rw [length]; have := ht.buffers.exponentFits; have := ht.buffers.maxLength; omega,
    by rw [length]; exact ht.buffers.exponent.fits,
    by rw [length]; exact ht.buffers.exponent.read, ht.buffers.exponent.byte⟩,
    pointer, by rw [length]; exact count⟩⟩

theorem publicExponentCheck_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicExponentInput base dst np ep xp len k eLen nb eb xb s) :
    WP isa exponentCheck s (PublicExponentResult base dst np ep xp len k eLen nb eb xb) := by
  have e := h.exponent
  refine WP.mono (exponentCheck_ok s (by rw [h.buffers.exponent.length]; exact h.buffers.exponentPositive)
    e.1.countFit e.1.sourceFit e.1.read e.1.bytes e.2.1 e.2.2) ?_
  rintro t ⟨status, mem, rest⟩
  exact ⟨h.toPublicBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp [exponentClobbers])).trans h.ptr), status⟩

theorem publicExponentFlag_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} (h : PublicExponentResult base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block [.subs .r7 .r7 (.imm 0)]) s (PublicExponentChecked base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (exponentFlag_ok s h.status) ?_
  rintro t ⟨flag, mem, rest⟩
  exact ⟨h.toPublicBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), flag⟩

theorem publicBody_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.body (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have positive : 0 < eb.length := by rw [h.1.buffers.exponent.length]; exact h.1.buffers.exponentPositive
  let P := fun (s t : State) => PublicBodyInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicBodyInput base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  let Q := fun (s t : State) => s.sp = t.sp ∧ PublicExponentInput base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicExponentInput base dst np ep xp len k eLen nb eb xb2 t
  let R := fun (s t : State) => s.sp = t.sp ∧ PublicExponentResult base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicExponentResult base dst np ep xp len k eLen nb eb xb2 t
  have args := (publicExponentArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicExponentArgs_ready s h.1, publicExponentArgs_ready t h.2.1⟩)
  have check := (relCT_keep_sp ((exponentCheck_ct positive).mono (P' := Q)
    (fun _ _ h => ⟨h.2.1.exponent, h.2.2.exponent⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨publicExponentCheck_ready s h.2.1, publicExponentCheck_ready t h.2.2⟩)
  have flag : RelCT isa R (.block [.subs .r7 .r7 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp flag (fun _ _ h => h.1)).wp
    (fun s t h => ⟨publicExponentFlag_ready s h.2.1, publicExponentFlag_ready t h.2.2⟩)
  have branch : RelCT isa (fun s t => s.sp = t.sp ∧
      PublicExponentChecked base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicExponentChecked base dst np ep xp len k eLen nb eb xb2 t)
      (.ite .eq PublicFn.fail PublicFn.modulus) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      change some s.z = some t.z
      rw [h.2.1.flag, h.2.2.flag]
    · apply (publicFail_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
        (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono
        (fun _ _ h => ⟨h.1.2.1.toPublicBodyInput, h.1.2.2.toPublicBodyInput, h.1.1⟩) (fun _ _ h => h)
    · apply (publicModulus_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
        (len := len) (k := k) (eLen := eLen) (nb := nb) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono
        (fun _ _ h => ⟨h.1.2.1.toPublicBodyInput, h.1.2.2.toPublicBodyInput, h.1.1⟩) (fun _ _ h => h)
  exact (args.seq (check.seq (ready.seq branch))) s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
