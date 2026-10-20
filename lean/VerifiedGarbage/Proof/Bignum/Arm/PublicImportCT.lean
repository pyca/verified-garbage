module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs

/-! # Importing different secret RSA inputs produces identical public traces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PublicImportReady (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  state : PublicArithmetic base dst np ep xp len k eLen nb eb xb s
  source : s.gpr .r4 = xp
  count : s.gpr .r6 = BitVec.ofNat 32 k

theorem publicInputArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicArithmetic base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PublicFn.inputArgs) s (PublicImportReady base dst np ep xp len k eLen nb eb xb) := by
  refine WP.mono (publicInputArgs_ok s h.stack) ?_
  rintro t ⟨source, count, mem, rest⟩
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), source, count⟩

theorem publicImport_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.importInput (fun _ _ => True) := by
  let P := fun (s t : State) => PublicArithmetic base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicArithmetic base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have args := (publicInputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicInputArgs_ready s h.1, publicInputArgs_ready t h.2.1⟩)
  exact args.seq ((importOperand_ct (o := 1) (by decide)).mono
    (fun _ _ h => ⟨h.2.1.state.ready, h.2.2.state.ready, h.2.1.source, h.2.2.source,
      h.2.1.count, h.2.2.count, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
