module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Impl.Rsa.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Verified
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Terms
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTCode
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Rsa.X86_64.InvInstance
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Verified
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverDet
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Main
import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Rsa.X86_64.CvVerified`, which only this module used -/

section

/-!
# `vg_rsa_crt_values` on x86-64: verified against the shared contract

`cvContract` states the shared contract on the registers and the stack
(`cv_implies`); with correctness (`cvCode_correct`) and constant time
(`cvCode_constantTime`), `CrtValues.code` is verified (`cv_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting `cvContract.pre`: a 512-bit modulus, one-byte factors
and exponent, and the stack arguments at `0x6008`. -/
def cvSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x1100 | .rcx => 1 | .r8 => 0x1200 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6050 then 0x20
    else bif Nat.beq a.toNat 0x6009 then 0x20 else bif Nat.beq a.toNat 0x6010 then 0x40
    else bif Nat.beq a.toNat 0x6019 then 0x30 else bif Nat.beq a.toNat 0x6020 then 1
    else bif Nat.beq a.toNat 0x6029 then 0x31 else bif Nat.beq a.toNat 0x6030 then 1
    else bif Nat.beq a.toNat 0x6039 then 0x32 else bif Nat.beq a.toNat 0x6040 then 1
    else bif Nat.beq a.toNat 0x6049 then 0x80 else bif Nat.beq a.toNat 0x6051 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x6008, 80⟩]
  wr := [⟨0x1000, 1⟩, ⟨0x1100, 1⟩, ⟨0x1200, 1⟩, ⟨0x8000, 8448⟩]

theorem cv_implies : cvContract.Implies (Spec.Rsa.crtValuesContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, cvContract, stackArgs_ten, List.append_eq] [cvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using cvSatState

/-- `vg_rsa_crt_values`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem cv_verified [InvLaw] (hmx : CrtValues.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target CrtValues.code (Spec.Rsa.crtValuesContract abi) :=
  Verified.of_correct (cvCode_correct hmx) cvCode_constantTime cv_implies

end VG.Proof.Rsa.X86_64

end

end

/-! ### `Rsa.X86_64.KeyVerified`, which only this module used -/

section

/-! ### `Rsa.X86_64.KeyImplies`, which only this module used -/

section

/-! ### `Bignum.X86_64.CrtImplies`, which only this module used -/

section

/-!
# RSA with the CRT on x86-64: the shared contract

`crtContract` states the shared contract on the registers and the stack
(`crt_implies`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- A state meeting `crtContract.pre`: a 512-bit modulus, one-byte primes,
exponents and `qInv`, and the stack arguments at `0x6008`. -/
def crtSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6060 then 0x20
    else bif Nat.beq a.toNat 0x6009 then 0x40 else bif Nat.beq a.toNat 0x6010 then 1
    else bif Nat.beq a.toNat 0x6019 then 0x41 else bif Nat.beq a.toNat 0x6020 then 1
    else bif Nat.beq a.toNat 0x6029 then 0x42 else bif Nat.beq a.toNat 0x6030 then 1
    else bif Nat.beq a.toNat 0x6039 then 0x43 else bif Nat.beq a.toNat 0x6040 then 1
    else bif Nat.beq a.toNat 0x6049 then 0x44 else bif Nat.beq a.toNat 0x6050 then 1
    else bif Nat.beq a.toNat 0x6059 then 0x80 else bif Nat.beq a.toNat 0x6061 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x6008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8448⟩]

theorem crt_implies : crtContract.Implies (Proof.Rsa.privateCrtContract abi) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using crtSatState

end VG.Proof.Bignum.X86_64

end

end


/-!
# `vg_rsa_check_key` on x86-64: the shared contract

`keyContract` states the shared contract on the registers and the stack
(`key_implies`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A state meeting `keyContract.pre`: a 512-bit modulus, one-byte `e`, `d`,
primes, exponents and `qInv`, and the stack arguments at `0x6008`. -/
def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6060 then 0x20
    else bif Nat.beq a.toNat 0x6009 then 0x40 else bif Nat.beq a.toNat 0x6010 then 1
    else bif Nat.beq a.toNat 0x6019 then 0x41 else bif Nat.beq a.toNat 0x6020 then 1
    else bif Nat.beq a.toNat 0x6029 then 0x42 else bif Nat.beq a.toNat 0x6030 then 1
    else bif Nat.beq a.toNat 0x6039 then 0x43 else bif Nat.beq a.toNat 0x6040 then 1
    else bif Nat.beq a.toNat 0x6049 then 0x44 else bif Nat.beq a.toNat 0x6050 then 1
    else bif Nat.beq a.toNat 0x6059 then 0x80 else bif Nat.beq a.toNat 0x6061 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x6008, 96⟩]
  wr := [⟨0x8000, 8448⟩]

theorem key_implies : keyContract.Implies (Spec.Rsa.checkKeyContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, keyOf, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hl
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, keyContract, stackArgs_twelve, List.append_eq] [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Rsa.X86_64.Key

end

end


/-!
# `vg_rsa_check_key` on x86-64: verified against the shared contract

Correct (`keyCode_correct`), constant time (`keyCode_constantTime`), and the
contract on the registers and the stack implies the shared one
(`key_implies`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CheckKey

/-- `vg_rsa_check_key`, given that its code never loads MXCSR (which the
registration file evaluates). -/
theorem key_verified (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct (keyCode_correct hmx) keyCode_constantTime key_implies

end VG.Proof.Rsa.X86_64.Key

end

end


/-!
# RSA on x86-64: the proofs `Artifacts/Rsa/X86_64.lean` registers

Each function's `Verified`, made from the proofs of its code and the checks
the kernel evaluates on it (that it inlines, and that every load of MXCSR
restores it).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Instances

open VG.X86_64 VG.Proof.Rsa.X86_64

theorem precompute_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnBase (Proof.Bignum.X86_64.R2Impl.words _)
    (by decide +kernel) rfl (by decide +kernel)

theorem precomputeAdx_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm))
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnAdx (Proof.Bignum.X86_64.R2Impl.adx _)
    (by decide +kernel) rfl (by decide +kernel)

theorem crtValues_verified :
    Verified target (Impl.Rsa.X86_64.Keys.CrtValues.code)
      (Spec.Rsa.crtValuesContract abi) :=
  cv_verified (by decide +kernel)

theorem checkKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckKey.code)
      (Spec.Rsa.checkKeyContract abi) :=
  Key.key_verified (by decide +kernel)

/-- `vg_rsa_recover_primes_det`, with the batched inverse's instance. -/
theorem recoverDet_verified :
    Verified target Impl.Rsa.X86_64.Keys.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Rd.rd_verified (by decide +kernel)

end VG.Proof.Rsa.X86_64.Instances

/-! ## RSA's key functions, without secret residue

Each function as emitted (`Impl.Rsa.X86_64.Fn`), its whole stack wiped by its
cleanup (`X86_64.Scrub.verifiedScrubbedAll`): it meets its contract in
constant time and returns without secret residue. Their postconditions read
the memory on return only within their buffers (`Proof/Rsa/X86_64/Scrub.lean`).
-/

namespace VG.Proof.Rsa.X86_64.Scrubbed

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Rsa.X86_64

theorem publicPrecompute_codeSp :
    (Precompute.code Fn.mmBase).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem publicPrecompute_scrubbed :
    VerifiedScrubbed target Fn.publicPrecompute (Spec.Rsa.publicPrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Precompute.code Fn.mmBase, stack := 8
      verified := Proof.Rsa.X86_64.Instances.precompute_verified, spSafe := publicPrecompute_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.publicPrecomputeOut 8)

theorem publicPrecompute_spSafe : Fn.publicPrecompute.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe publicPrecompute_codeSp

theorem publicPrecomputeAdx_codeSp :
    (Precompute.code Fn.mmAdx (Impl.Bignum.X86_64.R2Adx.choice Fn.mmAdx)).all (fun i => !isa.writesSp i) = true := by
  sp_safe

theorem publicPrecomputeAdx_scrubbed :
    VerifiedScrubbed target Fn.publicPrecomputeAdx (Spec.Rsa.publicPrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Precompute.code Fn.mmAdx (Impl.Bignum.X86_64.R2Adx.choice Fn.mmAdx), stack := 8
      verified := Proof.Rsa.X86_64.Instances.precomputeAdx_verified, spSafe := publicPrecomputeAdx_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.publicPrecomputeOut 8)

theorem publicPrecomputeAdx_spSafe : Fn.publicPrecomputeAdx.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe publicPrecomputeAdx_codeSp

theorem privatePrecompute_codeSp : (PrivPre.code Fn.mmBase).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem privatePrecompute_scrubbed :
    VerifiedScrubbed target Fn.privatePrecompute (Spec.Rsa.privatePrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := PrivPre.code Fn.mmBase, stack := 8
      verified := Proof.Bignum.X86_64.PrivPre.pp_verified, spSafe := privatePrecompute_codeSp }
    .sse (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)

theorem privatePrecompute_spSafe : Fn.privatePrecompute.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe privatePrecompute_codeSp

theorem privatePrecomputeAdx_codeSp : (PrivPre.code Fn.mmAdx).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem privatePrecomputeAdx_scrubbed :
    VerifiedScrubbed target Fn.privatePrecomputeAdx (Spec.Rsa.privatePrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := PrivPre.code Fn.mmAdx, stack := 8
      verified := Proof.Bignum.X86_64.PrivPre.ppAdx_verified, spSafe := privatePrecomputeAdx_codeSp }
    .sse (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)

theorem privatePrecomputeAdx_spSafe : Fn.privatePrecomputeAdx.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe privatePrecomputeAdx_codeSp

theorem crtValues_codeSp : Keys.CrtValues.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem crtValues_scrubbed :
    VerifiedScrubbed target Fn.crtValues (Spec.Rsa.crtValuesApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.crtValuesApi)
    { code := Keys.CrtValues.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.crtValues_verified, spSafe := crtValues_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.crtValuesOut 0)

theorem crtValues_spSafe : Fn.crtValues.all (fun i => !isa.writesSp i) = true := scrubKs_spSafe crtValues_codeSp

theorem recoverPrimesDet_codeSp : Keys.RecoverDet.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem recoverPrimesDet_scrubbed :
    VerifiedScrubbed target Fn.recoverPrimesDet (Spec.Rsa.recoverPrimesDetApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.recoverPrimesDetApi)
    { code := Keys.RecoverDet.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.recoverDet_verified, spSafe := recoverPrimesDet_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.recoverPrimesDetOut 0)

theorem recoverPrimesDet_spSafe : Fn.recoverPrimesDet.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe recoverPrimesDet_codeSp

theorem checkKey_codeSp : CheckKey.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem checkKey_scrubbed :
    VerifiedScrubbed target Fn.checkKey (Spec.Rsa.checkKeyApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.checkKeyApi)
    { code := CheckKey.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.checkKey_verified, spSafe := checkKey_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.checkKeyOut 0)

theorem checkKey_spSafe : Fn.checkKey.all (fun i => !isa.writesSp i) = true := scrubKs_spSafe checkKey_codeSp

end VG.Proof.Rsa.X86_64.Scrubbed
