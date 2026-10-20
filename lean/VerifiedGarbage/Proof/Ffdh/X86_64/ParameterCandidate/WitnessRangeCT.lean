module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessRange
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of the uniform witness interval -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (copyArr)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.ParameterCandidate

theorem witnessRange_ct : RelCT isa (Two GoodW1) witnessRange fun _ _ => True := by
  unfold witnessRange VG.Impl.Ffdh.X86_64.Domain.rangeTest
  refine RelCT.seqs_append (by simp [VG.Impl.Ffdh.X86_64.Domain.range, VG.Impl.Ffdh.X86_64.Domain.gt1,
    VG.Impl.Ffdh.X86_64.Domain.ltP, ltArr, cmpArr, copyArr]) (by simp) ?_
  refine RelCT.seq (VG.Proof.Ffdh.X86_64.range_ct (a := aXm) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
