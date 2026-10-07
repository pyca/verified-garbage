import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Impl.P384.X86_64.Joint

/-!
# ECDSA verification over P-384 on x86-64: the joint verifier's curve and contract

`p384v` and `p384vx` are `p384` and `p384x` with `pubVerify`, which only
verification reads: the same curve, layout and multiplications, so the same
facts (`p384v_ok`, from `p384_ok`), and the contract's precondition gives
theirs (`pre_of`). The shared contract makes the key, the digest and the
signature public (`jointPublic_of_spec`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

/-- The comb's data, as `p384.comb` has it. -/
def p384Table : CombData := ⟨7,Impl.P384.p384Comb7,Impl.P384.p384Comb7Start,"VG_P384_COMB",false⟩

/-! The fields of `p384v` and `p384vx` that are `p384`'s, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p384v_C : p384v.C = p384.C := rfl
theorem p384v_n : p384v.n = p384.n := rfl
theorem p384v_comb : p384v.comb = p384.comb := rfl
theorem p384vx_C : p384vx.C = p384.C := rfl
theorem p384vx_n : p384vx.n = p384.n := rfl
theorem p384vx_comb : p384vx.comb = p384.comb := rfl

theorem p384v_combConsts : p384v.combConsts = [("VG_P384_COMB", p384W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p384v_comb, p384v_C, p384v_n]
  rfl

theorem p384vx_combConsts : p384vx.combConsts = [("VG_P384_COMB", p384W)] := by
  unfold Cfg.combConsts Cfg.combWords Cfg.R
  rw [p384vx_comb, p384vx_C, p384vx_n]
  rfl

theorem p384v_ok (hI : InvSounds) : CfgOk p384v := cfgOk_pubVerify (p384_ok hI) true

theorem p384vx_ok (hI : InvSounds) : CfgOk p384vx := cfgOk_pubVerify (p384x_ok hI) true

theorem p384v_tbls (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384v := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem p384vx_tbls (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384vx := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p384v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384v_combConsts, show p384v.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p384v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem pre_of_x {s : State} (h : verifyX86_64.pre s) : VPre p384vx s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384vx_combConsts, show p384vx.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p384vx_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pub a b) :
    JointPublic p384v p384Table a b := by
  sig_pub [Spec.Ecdsa.P384.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p384_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 48,peer_bytes _ _ 48] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (48+48)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (48+48) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> p384v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64.P384
