module

public import VerifiedGarbage.Proof.Bignum.Arm.PdInputImport
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Importing different secret RSA inputs produces identical public traces -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

structure PdImportReady (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  state : PdArithmetic base dst np ep xp len k eLen N R eb xb s
  source : s.gpr .r4 = xp
  count : s.gpr .r6 = BitVec.ofNat 32 k

theorem pdInputArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdArithmetic base dst np ep xp len k eLen N R eb xb s) :
    WP isa (.block PublicFn.inputArgs) s (PdImportReady base dst np ep xp len k eLen N R eb xb) := by
  refine WP.mono (publicInputArgs_ok s h.stack) ?_
  rintro t ⟨source, count, mem, rest⟩
  exact ⟨h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), source, count⟩

theorem pdInputImport_ct {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PdArithmetic base dst np ep xp len k eLen N R eb xb1 s ∧
      PdArithmetic base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp)
      PublicFn.importInput (fun _ _ => True) := by
  let P := fun (s t : State) => PdArithmetic base dst np ep xp len k eLen N R eb xb1 s ∧
    PdArithmetic base dst np ep xp len k eLen N R eb xb2 t ∧ s.sp = t.sp
  have args := (publicInputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨pdInputArgs_ready s h.1, pdInputArgs_ready t h.2.1⟩)
  exact args.seq ((importOperand_ct (o := 1) (by decide)).mono
    (fun _ _ h => ⟨h.2.1.state.ready, h.2.2.state.ready, h.2.1.source, h.2.2.source,
      h.2.1.count, h.2.2.count, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
