module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointChecks
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import VerifiedGarbage.Proof.P521.X86_64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Impl.P521.X86_64.Joint
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Tables
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Ecdsa.Verify.X86_64.P521.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA verification over P-521 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p521.combConsts`),
by name: `vg_ecdsa_p521_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_P521_COMB`. Only the pointers (and the tables' address) are public
here: the proof shows that nothing else affects timing, although the
contract would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p521)
open VG.Proof.Ecdsa.X86_64.P521 (TblHeld p521W p521_constRegions p521_combConsts satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P521.curve (bytesAt m pk 133) (hashToInt Spec.P521.curve (bytesAt m digest 66)) (bytesAt m sig 132)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 133⟩
    let digest : Region := ⟨s.gpr .rsi, 66⟩
    let sig : Region := ⟨s.gpr .rdx, 132⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_P521_COMB", 764928⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_P521_COMB" = s₂.syms "VG_P521_COMB"

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
  rd := [⟨0x1000, 133⟩, ⟨0x2000, 66⟩, ⟨0x3000, 132⟩, ⟨0x100000, 764928⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 133⟩, ⟨s.gpr .rsi, 66⟩, ⟨s.gpr .rdx, 132⟩,
      ⟨s.syms "VG_P521_COMB", 764928⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 133⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 66⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 132⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 133⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 66⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 132⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 133 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 66 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 132 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P521_COMB").toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p521_combConsts,
    Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pre
    satState := by
  have held : ∀ i < p521W.length, satState.mem.readW (satState.syms "VG_P521_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0 := satMem_held
  refine spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (by decide) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    verifyX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p521_combConsts,
      Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p521_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P521.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p521_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.P521

end

end

/-! Whole-function timing of P-521's joint verification follows the public-input contract. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/P521/JointContract.lean`, which only this module imported.
section

/-!
# ECDSA verification over P-521 on x86-64: the joint verifier's contract

`p521` and `p521x` already have `pubVerify`, so the joint verifier runs with
signing's curve facts (`p521_ok`, `p521x_ok`), and the contract's
precondition gives theirs (`pre_of`, `pre_of_x`). The shared contract makes
the key, the digest and the signature public (`jointPublic_of_spec`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64

/-- The comb's data, as `p521.comb` has it. -/
def p521Table : CombData := ⟨7,Impl.P521.p521Comb7,Impl.P521.p521Comb7Start,"VG_P521_COMB",false,false⟩

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
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pub a b) :
    JointPublic p521 p521Table a b := by
  sig_pub [Spec.Ecdsa.P521.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
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
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P521
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P521.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P521 (p521_ok p521x_ok p521_tbls p521x_tbls)

section
variable (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_p521_public_ct :
    ConstantTime isa (VPre p521) (JointPublic p521 p521Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521 publicJoint (Joint.jacDouble publicJoint.K)).inline := by
  have hc := p521_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofComb rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun h => absurd h (by decide)) ps pt pub

theorem jointVerify_p521_adx_public_ct :
    ConstantTime isa (VPre p521x) (JointPublic p521x p521Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521x publicJointAdx
        (Joint.jacDouble publicJointAdx.K)).inline := by
  have hc := p521x_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofComb rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks (fun h => absurd h (by decide)) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP521.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p521_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P521.inst (X86_64.abi.withConsts p521.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP521Adx.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p521_adx_public_ct hL hT hI _ _ _ _ _ _
    (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (jointPublic_x (jointPublic_of_spec pub)) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P521
