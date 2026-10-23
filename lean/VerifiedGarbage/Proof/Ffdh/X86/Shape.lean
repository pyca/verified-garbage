module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Impl.Ffdh.X86.KeyGen
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
public import VerifiedGarbage.Impl.Ffdh.X86.KeySearch
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Rsa.X86.RtShape
public import VerifiedGarbage.TCB.X86.Isa

/-! # FFDH on i686: no instruction writes `esp` -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Shape

open VG VG.X86 VG.Proof.Mont.X86.StaticSquare

theorem checkDomain_spSafe : (Impl.Ffdh.X86.CheckDomain.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem checkPublic_spSafe : (Impl.Ffdh.X86.CheckPublic.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem checkPrivate_spSafe : (Impl.Ffdh.X86.CheckPrivate.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem exchange_spSafe : (Impl.Ffdh.X86.Exchange.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem derivePublic_spSafe :
    (Impl.Ffdh.X86.DerivePublic.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem generateKey_spSafe :
    (Impl.Ffdh.X86.GenerateKey.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem keySearch_spSafe :
    (Impl.Ffdh.X86.KeySearch.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem candidate_spSafe :
    (Impl.Ffdh.X86.Candidate.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

theorem paramSearch_spSafe :
    (Impl.Ffdh.X86.ParamSearch.code).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.Rsa.X86.RtShape.all_spSafe (by rsa_stack_shape)

end VG.Proof.Ffdh.X86.Shape
