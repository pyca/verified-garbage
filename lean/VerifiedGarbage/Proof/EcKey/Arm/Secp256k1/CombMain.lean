module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Lit
public import VerifiedGarbage.Impl.EcKey.Secp256k1.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.EcKey.Arm.Main
meta import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Impl.EcKey.Secp256k1.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Spec.EcKey.Secp256k1
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Secp256k1
meta import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `EcKey.Arm.Secp256k1.Verified`, which this module and modules that import it used -/

section

/-! ### `EcKey.Arm.Secp256k1.Contract`, which this module and modules that import it used -/

section

/-!
# secp256k1 public keys on 32-bit ARM: the contract the proof is written against

The facts of `Spec.EcKey.Secp256k1.inst.publicKeyContract` for 32-bit ARM, by
name: `vg_ec_secp256k1_public_key(out, d, scratch)`, with the arguments in
`r0`–`r2` (AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.Secp256k1

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.Secp256k1.curve) :=
  publicKey Spec.Secp256k1.curve (ofBytes (bytesAt m d 32))

def pkArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 65⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r0).toNat + 65 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

end VG.Proof.EcKey.Arm.Secp256k1

end

end

/-!
# secp256k1 public keys on 32-bit ARM: `Verified`

`publicKey_ok` for secp256k1 (`secp256k1_ok`, and `Law` for its group law, which the
registration file supplies) gives the contract's postcondition; `r4`–`r11`
and `lr` are restored and `sp` kept. Constant time by taint tracking from
the arguments' registers: the only branches are on loop counters, and every
address is `r12` (`scratch`) or `lr` (`out`) plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.Secp256k1

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1 Spec.Weierstrass

theorem post_of {u : Bool} {s s' : State} (h : PkPost (secp256k1With u) s s') : pkArm.post s s' := by
  unfold PkPost at h
  simp only [pkArm, BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem (State.addr (s.gpr .r1)) = q
  rw [show Spec.EcKey.publicKey (secp256k1With u).C (dk (secp256k1With u) s) = pk s.mem (State.addr (s.gpr .r1)) from rfl,
    hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

end VG.Proof.EcKey.Arm.Secp256k1

end

end

/-! Public-key generation reuses the signing pipeline's fixed-base comb. -/

@[expose] public section
namespace VG.Proof.EcKey.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1

abbrev combPkSpec : Contract isa :=
  Spec.EcKey.Secp256k1.inst.publicKeyContract (abi.withConsts secp256k1CombConsts)

def combPkPre (u : Bool) (s : State) : Prop :=
  PkPre (secp256k1With u) s (constRegs secp256k1CombConsts s) ∧ ConstsOk secp256k1CombConsts 0 s

theorem pk_spec_pre {u : Bool} {s : State}
    (h : (Spec.EcKey.Secp256k1.inst.publicKeyContract abi).pre s) : PkPre (secp256k1With u) s := by
  sig_pre [Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,_od,os,ds,fo,fd,fs⟩ := h
  exact ⟨rd,wr,os,ds,fo,fd,fs⟩

theorem combPk_pre {u : Bool} {s : State} (h : combPkSpec.pre s) : combPkPre u s := by
  have hp : (Spec.EcKey.Secp256k1.inst.publicKeyContract abi).pre (stripConsts secp256k1CombConsts s) ∧
      ConstsOk secp256k1CombConsts 0 s := pre_consts.mp h
  have p := pk_spec_pre (u := u) hp.1
  refine ⟨⟨?_,p.wr,p.out_sc,p.d_sc,p.out_fit,p.d_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-secp256k1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs secp256k1CombConsts s) p.rd

theorem combPk_ok (hC : Law Spec.Secp256k1.curve) {u : Bool} {s₀ : State} (hp : combPkPre u s₀) :
    WP isa (publicKeySecp256k1CombWith u) s₀ fun t => PkKeep (secp256k1With u) s₀ t ∧ PkPost (secp256k1With u) s₀ t := by
  have member : (secp256k1Comb.tsym,secp256k1CombWords)∈secp256k1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r2,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  exact publicKeyWith_ok (secp256k1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

end VG.Proof.EcKey.Arm.Secp256k1
