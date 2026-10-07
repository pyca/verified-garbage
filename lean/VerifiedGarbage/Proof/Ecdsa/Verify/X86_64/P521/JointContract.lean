import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Impl.P521.X86_64.Joint

/-!
# ECDSA verification over P-521 on x86-64: the joint verifier's contract

`p521` and `p521x` already have `pubVerify`, so the joint verifier runs with
signing's curve facts (`p521_ok`, `p521x_ok`), and the contract's
precondition gives theirs (`pre_of`, `pre_of_x`). The shared contract makes
the key, the digest and the signature public (`jointPublic_of_spec`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64

/-- The comb's data, as `p521.comb` has it. -/
def p521Table : CombData := ⟨7,Impl.P521.p521Comb7,Impl.P521.p521Comb7Start,"VG_P521_COMB",false⟩

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521_combConsts, p521_constRegions, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p521_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem pre_of_x {s : State} (h : verifyX86_64.pre s) : VPre p521x s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521x_combConsts, p521_constRegions, p521x_C, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p521x_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub a b) :
    JointPublic p521 p521Table a b := by
  sig_pub [Spec.Ecdsa.P521.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P521.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p521_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 66,peer_bytes _ _ 66] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (66+66)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (66+66) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> p521.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- `p521x`'s public inputs are `p521`'s: the same curve and shift. -/
theorem jointPublic_x {a b : State} (h : JointPublic p521 p521Table a b) :
    JointPublic p521x p521Table a b := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨h1,h2,h3,?_,?_,?_,?_,?_⟩
  · simpa only [keyX,p521x_C] using h4
  · simpa only [keyY,p521x_C] using h5
  · simpa only [dig,p521x_C,p521x_sh,p521_sh] using h6
  · simpa only [sigR,p521x_C] using h7
  · simpa only [sigS,p521x_C] using h8

end VG.Proof.Ecdsa.Verify.X86_64.P521
