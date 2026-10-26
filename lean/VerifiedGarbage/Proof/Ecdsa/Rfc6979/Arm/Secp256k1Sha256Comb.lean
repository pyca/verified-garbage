module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Sha256
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
import VerifiedGarbage.Proof.Framework.Contract

/-! Deterministic secp256k1/SHA-256 signing through the shared fixed-base comb. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Sha256Comb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Secp256k1.Arm

def pack (hL : Weierstrass.Law Spec.Secp256k1.curve) : RfcHash :=
  {Secp256k1Sha256.pack hL with R := secp256k1CombCurve hL}

abbrev rfcCombSpec : Contract isa := Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst.signContract
  (abi.withConsts secp256k1CombConsts) 240

def rfcCombSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x12000,32⟩,⟨0x14000,32⟩,⟨0x100000,151552⟩]
  wr := [⟨0x10000,64⟩,⟨0,8192⟩] }

theorem rfcComb_sat : rfcCombSpec.pre rfcCombSat := by
  have held := combSat_held
  generalize eqs : rfcCombSat=s
  sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.Secp256k1.inst,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,
    abi,argRegs,reduceClassify,Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,by decide,held,by decide,?_,?_,by decide,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,64⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem implies : (rfcArm Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst 240 secp256k1CombConsts).Implies rfcCombSpec where
  pre s h := by
    sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.Secp256k1.inst,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts,
      Abi.constRegions,Abi.constsHeld,stackBelow] at h
    obtain ⟨sp,_spf,drop,held,fit,apart,stk,al,take,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs⟩ := h
    refine ⟨?_,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs,sp,?_⟩
    · rw [← List.take_append_drop (s.rd.length-1) s.rd,take,drop]
      rfl
    · intro c hc
      simp only [secp256k1CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
      subst c
      refine ⟨held,fit,?_,al⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact apart _ (by rw [wr];exact .head _)
      · exact apart _ (by rw [wr];exact .tail _ (.head _))
      · exact stk
  post := by
    sig_implies_post [rfcCombSpec,Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.Secp256k1.inst,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,Abi.withConsts,rfcArm,stkR]
  pub s t _ _ h := by
    sig_pub [rfcCombSpec,Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.Secp256k1.inst,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts] at h
    obtain ⟨sp,sy,leak,h0,h1,h2,h3⟩ := h
    refine ⟨sp,h0,h1,h2,h3,(List.cons.inj leak).1,?_⟩
    intro c hc
    simp only [secp256k1CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    exact sy
  sat := ⟨rfcCombSat,rfcComb_sat⟩

theorem sign_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign rfcCombSpec :=
  Arm.sign_verified (pack hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Sha256Comb
