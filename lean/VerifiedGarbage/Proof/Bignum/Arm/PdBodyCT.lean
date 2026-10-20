module
public import VerifiedGarbage.Impl.Bignum.Arm.PdFn
public import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentScanCT

import VerifiedGarbage.Proof.Bignum.Arm.PdImportedCT
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.PdFn
meta import VerifiedGarbage.Proof.Bignum.Arm.PdBodyInput
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentScanCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PdImportedCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheckCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PdFailCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
meta import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Checked public RSA permits different secret inputs with identical leakage -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PdExponentInput (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop extends PdBodyInput base dst np ep xp len k eLen N R eb xb s where
  exponent : ExponentInput ep eb s

structure PdExponentResult (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop extends PdBodyInput base dst np ep xp len k eLen N R eb xb s where
  status : s.gpr .r7 = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)).toNat

structure PdExponentChecked (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop extends PdBodyInput base dst np ep xp len k eLen N R eb xb s where
  flag : s.z = !Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)

theorem pdExponentArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} (h : PdBodyInput base dst np ep xp len k eLen N R eb xb s) :
    WP isa (.block PublicFn.exponentArgs) s (PdExponentInput base dst np ep xp len k eLen N R eb xb) := by
  refine WP.mono (publicExponentArgs_ok s h.stack) ?_
  rintro t ⟨pointer, count, mem, rest⟩
  have ht := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  have length := ht.buffers.exponent.length
  exact ⟨ht, ⟨⟨by rw [length]; have := ht.buffers.exponentFits; have := ht.buffers.maxLength; omega,
    by rw [length]; exact ht.buffers.exponent.fits,
    by rw [length]; exact ht.buffers.exponent.read, ht.buffers.exponent.byte⟩,
    pointer, by rw [length]; exact count⟩⟩

theorem pdExponentCheck_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} (h : PdExponentInput base dst np ep xp len k eLen N R eb xb s) :
    WP isa exponentCheck s (PdExponentResult base dst np ep xp len k eLen N R eb xb) := by
  have e := h.exponent
  refine WP.mono (exponentCheck_ok s (by rw [h.buffers.exponent.length]; exact h.buffers.exponentPositive)
    e.1.countFit e.1.sourceFit e.1.read e.1.bytes e.2.1 e.2.2) ?_
  rintro t ⟨status, mem, rest⟩
  exact ⟨h.toPdBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp [exponentClobbers])).trans h.ptr), status⟩

theorem pdExponentFlag_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} (h : PdExponentResult base dst np ep xp len k eLen N R eb xb s) :
    WP isa (.block [.subs .r7 .r7 (.imm 0)]) s (PdExponentChecked base dst np ep xp len k eLen N R eb xb) := by
  refine WP.mono (exponentFlag_ok s h.status) ?_
  rintro t ⟨flag, mem, rest⟩
  exact ⟨h.toPdBodyInput.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr), flag⟩

theorem pdBody_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdBodyInput base dst np ep xp len k eLen N R eb xb1 s ∧
      PdBodyInput base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PdFn.body (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  have positive : 0 < eb.length := by rw [h.1.buffers.exponent.length]; exact h.1.buffers.exponentPositive
  let P := fun (s t : State) => PdBodyInput base dst np ep xp len k eLen N R eb xb1 s ∧
    PdBodyInput base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp
  let Q := fun (s t : State) => s.sp = t.sp ∧ PdExponentInput base dst np ep xp len k eLen N R eb xb1 s ∧
    PdExponentInput base dst np ep xp len k eLen N R eb xb2 t
  let Phase := fun (s t : State) => s.sp = t.sp ∧ PdExponentResult base dst np ep xp len k eLen N R eb xb1 s ∧
    PdExponentResult base dst np ep xp len k eLen N R eb xb2 t
  have args := (publicExponentArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨pdExponentArgs_ready s h.1, pdExponentArgs_ready t h.2.1⟩)
  have check := (relCT_keep_sp ((exponentCheck_ct positive).mono (P' := Q)
    (fun _ _ h => ⟨h.2.1.exponent, h.2.2.exponent⟩) (fun _ _ h => h)) (fun _ _ h => h.1)).wp
    (fun s t h => ⟨pdExponentCheck_ready s h.2.1, pdExponentCheck_ready t h.2.2⟩)
  have flag : RelCT isa Phase (.block [.subs .r7 .r7 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have ready := (relCT_keep_sp flag (fun _ _ h => h.1)).wp
    (fun s t h => ⟨pdExponentFlag_ready s h.2.1, pdExponentFlag_ready t h.2.2⟩)
  have branch : RelCT isa (fun s t => s.sp = t.sp ∧
      PdExponentChecked base dst np ep xp len k eLen N R eb xb1 s ∧
      PdExponentChecked base dst np ep xp len k eLen N R eb xb2 t)
      (.ite .eq PublicFn.fail PdFn.imported) (fun _ _ => True) := by
    apply RelCT.ite
    · intro s t h
      change some s.z = some t.z
      rw [h.2.1.flag, h.2.2.flag]
    · apply (pdFail_ct (base := base) (dst := dst) (np := np) (ep := ep) (xp := xp)
        (len := len) (k := k) (eLen := eLen) (N := N) (R := R) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono
        (fun _ _ h => ⟨h.1.2.1.toPdBodyInput, h.1.2.2.toPdBodyInput, h.1.1⟩) (fun _ _ h => h)
    · apply (pdImported_ct (base := base) (dst := dst) (pp := np) (ep := ep) (xp := xp)
        (len := len) (k := k) (eLen := eLen) (N := N) (R := R) (eb := eb) (xb1 := xb1) (xb2 := xb2)).mono
        (fun _ _ h => ⟨h.1.2.1.toPdBodyInput, h.1.2.2.toPdBodyInput, h.1.1⟩) (fun _ _ h => h)
  exact (args.seq (check.seq (ready.seq branch))) s t tr1 tr2 u v h e1 e2

end VG.Proof.Bignum.Arm
