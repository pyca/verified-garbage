module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointChecks
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.P224.X86_64.JointLayout
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
public import VerifiedGarbage.Impl.P224.X86_64.Joint
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Tables
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Verify.X86_64.P224.JointContract`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.X86_64.P224.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA verification over P-224 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p224.combConsts`),
by name: `vg_ecdsa_p224_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_P224_COMB`. This adapter supplies the correctness precondition and
postcondition. The timing proof uses the shared contract directly, including
its public input buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p224)
open VG.Proof.Ecdsa.X86_64.P224 (TblHeld p224W p224W_length p224_combConsts satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P224.curve (bytesAt m pk 57) (hashToInt Spec.P224.curve (bytesAt m digest 28)) (bytesAt m sig 56)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 57⟩
    let digest : Region := ⟨s.gpr .rsi, 28⟩
    let sig : Region := ⟨s.gpr .rdx, 56⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_P224_COMB" = s₂.syms "VG_P224_COMB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 28⟩, ⟨0x3000, 56⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rsi, 28⟩, ⟨s.gpr .rdx, 56⟩,
      ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 28⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 56⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 57⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 28⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 56⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 28 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 56 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P224_COMB").toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p224_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)).pre
    satState := by
  have hl := p224W_length
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (by decide) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    verifyX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p224_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P224.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p224_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.P224

end

end

/-!
# ECDSA verification over P-224 on x86-64: the joint verifier's curve and contract

`p224v` is `p224` with `pubVerify`, which only verification reads: the same
curve, layout and multiplications, so the same facts (`p224v_ok`, from
`p224_ok`), and the contract's precondition gives its own (`pre_of`). The
shared contract makes the key, the digest and the signature public
(`jointPublic_of_spec`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

/-- The comb's data, as `p224.comb` has it. -/
def p224Table : CombData := ⟨7,Impl.P224.p224Comb7,Impl.P224.p224Comb7Start,"VG_P224_COMB",false,false⟩

theorem p224v_combConsts : p224v.combConsts = [("VG_P224_COMB", p224W)] := p224_combConsts

theorem p224v_ok (hI : InvSounds) : CfgOk p224v := cfgOk_pubVerify (p224_ok hI) true

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre p224v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224v_combConsts, show p224v.C.len = 28 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p224v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)).pub a b) :
    JointPublic p224v p224Table a b := by
  sig_pub [Spec.Ecdsa.P224.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
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

end

end

/-! Whole-function timing of P-224's joint verification follows the public-input contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P224.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_p224_public_ct :
    ConstantTime isa (VPre p224v) (JointPublic p224v p224Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p224v publicJoint (Joint.jacDouble publicJoint.K)).inline := by
  have hc := p224v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofComb rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun h => absurd h (by decide)) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP224.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p224_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P224
