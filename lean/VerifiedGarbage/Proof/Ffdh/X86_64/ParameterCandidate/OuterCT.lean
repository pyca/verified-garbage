module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of retained outer state operations -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate

structure OuterPublic where
  B : Addr
  wr : List Region
  out : Addr
  len : Nat
  usedP : Addr
  bits : Nat
  status : Nat
  rand : Addr

def outerSlots (p : OuterPublic) : List (Nat × BitVec 64) :=
  [(oOut, p.out), (oLen, BitVec.ofNat 64 p.len), (oUsedP, p.usedP),
    (oBits, BitVec.ofNat 64 p.bits), (oRandStart, p.rand)]

def outerS : List Nat := [oOut, oLen, oUsedP, oBits, oRandStart]

def OuterHeader (p : OuterPublic) (s : State) : Prop := KW p.B p.wr ∧ HP p.B p.wr (outerSlots p) s

def FinishHeader (p : OuterPublic) (s : State) : Prop := KW p.B p.wr ∧
  HP p.B p.wr (outerSlots p ++ [(oStatus, BitVec.ofNat 64 p.status)]) s

theorem finish_ct : RelCT isa (Two FinishHeader) finish fun _ _ => True :=
  kt_ct OuterPublic.B OuterPublic.wr (outerS ++ [oStatus])
    (fun p => outerSlots p ++ [(oStatus, BitVec.ofNat 64 p.status)]) [] (by decide)
    (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem phaseSetup_ct (q : Bool) : RelCT isa (Two OuterHeader) (phaseSetup q) fun _ _ => True := by
  cases q
  all_goals
    exact kt_ct OuterPublic.B OuterPublic.wr outerS outerSlots [] (by decide)
      (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem shapeOriginal_ct : RelCT isa (Two OuterHeader) shapeOriginal fun _ _ => True :=
  kt_ct OuterPublic.B OuterPublic.wr outerS outerSlots [] (by decide)
    (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem halveOutput_ct : RelCT isa (Two OuterHeader) halveOutput fun _ _ => True :=
  kt_ct OuterPublic.B OuterPublic.wr outerS outerSlots [] (by decide)
    (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide)

theorem consumeCandidate_ct : RelCT isa (Two OuterHeader) (.block consumeCandidate) fun _ _ => True :=
  kt_ct OuterPublic.B OuterPublic.wr outerS outerSlots [] (by decide)
    (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
