import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
import VerifiedGarbage.Impl.P224.X86_64.Joint

/-!
# ECDSA verification over P-224 on x86-64: the joint verifier's curve and contract

`p224v` is `p224` with `pubVerify`, which only verification reads: the same
curve, layout and multiplications, so the same facts (`p224v_ok`, from
`p224_ok`), and the contract's precondition gives its own (`pre_of`). The
shared contract makes the key, the digest and the signature public
(`jointPublic_of_spec`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

/-- The comb's data, as `p224.comb` has it. -/
def p224Table : CombData := ⟨7,Impl.P224.p224Comb7,Impl.P224.p224Comb7Start,"VG_P224_COMB",false⟩

theorem p224v_combConsts : p224v.combConsts = [("VG_P224_COMB", p224W)] := p224_combConsts

theorem p224v_ok (hI : InvSounds) : CfgOk p224v := cfgOk_pubVerify (p224_ok hI) true

theorem p224v_tbls (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    CombTbls p224v := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p224v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224v_combConsts, show p224v.C.len = 28 from rfl]; simp only [Abi.constRegions,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p224v_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [Abi.constRegions, List.map_cons, List.map_nil, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts)).pub a b) :
    JointPublic p224v p224Table a b := by
  sig_pub [Spec.Ecdsa.P224.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P224.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p224_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 28,peer_bytes _ _ 28] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (28+28)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (28+28) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> p224v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64.P224
