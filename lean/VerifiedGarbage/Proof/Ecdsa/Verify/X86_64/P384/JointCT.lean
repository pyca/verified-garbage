module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.P384.X86_64.JointLayout
public import VerifiedGarbage.Impl.P384.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables

/-! ### `Ecdsa.Verify.X86_64.P384.JointContract`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.X86_64.P384.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA verification over P-384 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst` for x86-64, under the
calling convention with the verifier's table of the generator's multiples
(`Abi.withConsts p384v.combConsts`),
by name: `vg_ecdsa_p384_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the table at the address of the
static `VG_P384_GTAB`. This adapter supplies the correctness precondition and
postcondition. The timing proof uses the shared contract directly, including
its public input buffers.
-/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/P384/GTables.lean`, which only this module imported.
section

/-!
# ECDSA verification over P-384 on x86-64: the table of the generator's multiples in a static

What the verifier's contract says of its one table, `p384GTab` (`TblHeldG`):
held at the address of the static `VG_P384_GTAB`, not wrapping around, and
apart from the writable regions and the return address; its length
(`p384GW_length`, from the table's shape alone); and a memory holding it, for
the contract's witness (`satMemG`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (Cfg)
open VG.Impl.P384.X86_64 (p384v p384vx p384GTab)

/-- The words of the verifier's table. -/
abbrev p384GW : List (BitVec 64) := p384v.combWords p384GTab

theorem p384v_gtab : p384v.gtab = some p384GTab := rfl

theorem p384vx_gtab : p384vx.gtab = some p384GTab := rfl

/-- The fields of `p384v` and `p384vx` the tables of constants read,
rewritten rather than compared by unfolding (which would evaluate `R`). -/
theorem p384v_comb : p384v.comb = none := rfl

theorem p384vx_comb : p384vx.comb = none := rfl

theorem p384vx_Cv : p384vx.C = p384v.C := rfl

theorem p384vx_nv : p384vx.n = p384v.n := rfl

theorem p384vx_combWords : p384vx.combWords p384GTab = p384GW := by
  unfold p384GW Cfg.combWords Cfg.R
  rw [p384vx_Cv, p384vx_nv]

theorem p384v_combConsts : p384v.combConsts = [("VG_P384_GTAB", p384GW)] := by
  unfold Cfg.combConsts
  rw [p384v_comb, p384v_gtab]
  rfl

theorem p384vx_combConsts : p384vx.combConsts = [("VG_P384_GTAB", p384GW)] := by
  unfold Cfg.combConsts
  rw [p384vx_comb, p384vx_gtab]
  exact congrArg (fun w => [("VG_P384_GTAB", w)]) p384vx_combWords

/-- The table at the static `VG_P384_GTAB`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < p384GW.length, s.mem.readW (s.syms "VG_P384_GTAB" + BitVec.ofNat 64 (8 * i)) 64 = p384GW.getD i 0) ∧
  (s.syms "VG_P384_GTAB").toNat + 8 * p384GW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P384_GTAB", 8 * p384GW.length⟩ r

/-- `p384GW` has `256 · 12` words. -/
theorem p384GW_length : p384GW.length = 3072 :=
  (Proof.Weierstrass.tcombWords_length (n := p384v.n) (R := p384v.R) (p := p384v.C.p)
    (H := 256) (tbl := Impl.P384.p384G9) Proof.P384.p384G9_length Proof.P384.p384G9_rows).trans rfl

/-- The table's region, `8 · 3072` bytes at the static's address (see
`p384_constRegions`). -/
theorem p384G_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P384_GTAB", p384GW)] = [⟨f "VG_P384_GTAB", 24576⟩] := by
  rw [Proof.Ecdsa.X86_64.constRegions_single, p384GW_length]

/-- The memory of the contract's witness: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMemG : Mem := constMem 0x100000 p384GW

theorem satMemG_held : ∀ i < p384GW.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384GW.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p384GW_length]; omega_using [])

end VG.Proof.Ecdsa.Verify.X86_64.P384
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.P384.X86_64 (p384v)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P384.curve (bytesAt m pk 97) (hashToInt Spec.P384.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 97⟩
    let digest : Region := ⟨s.gpr .rsi, 48⟩
    let sig : Region := ⟨s.gpr .rdx, 96⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_P384_GTAB", 8 * p384GW.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeldG s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_P384_GTAB" = s₂.syms "VG_P384_GTAB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemG
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 97⟩, ⟨s.gpr .rsi, 48⟩, ⟨s.gpr .rdx, 96⟩,
      ⟨s.syms "VG_P384_GTAB", 8 * p384GW.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 97⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 48⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 96⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 97⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 48⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 96⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 96 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeldG s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P384_GTAB").toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pre
    satState := by
  have hl := p384GW_length
  have held : ∀ i < p384GW.length, satState.mem.readW (satState.syms "VG_P384_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = p384GW.getD i 0 := satMemG_held
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
    verifyX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384v_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p384v_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P384.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384v_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.P384

end

end

/-!
# ECDSA verification over P-384 on x86-64: the joint verifier's curve and contract

`p384v` and `p384vx` are `p384` and `p384x` with `pubVerify`, which only
verification reads, and with the table of the generator's multiples in place
of the comb: the same curve, layout and multiplications, so the same facts
(`p384v_ok`, from `p384_ok`), and the contract's precondition gives theirs
(`pre_of`). The shared contract makes the key, the digest and the
signature public (`jointPublic_of_spec`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

/-! The fields of `p384v` and `p384vx` that are `p384`'s, rewritten rather than
compared by unfolding (which would evaluate the order's bits). -/

theorem p384v_ok (hI : InvSounds) : CfgOk p384v := cfgOk_gtab (cfgOk_pubVerify (p384_ok hI) true) _

theorem p384vx_ok (hI : InvSounds) : CfgOk p384vx := cfgOk_gtab (cfgOk_pubVerify (p384x_ok hI) true) _

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
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pub a b) :
    JointPublic p384v p384GTab a b := by
  sig_pub [Spec.Ecdsa.P384.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.P384.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p384v_combConsts,
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

end

end

/-! Whole-function timing of P-384's joint verification follows the public-input contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P384.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start)
    (hI : InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve)
include hL hT hI hO

theorem jointVerify_p384_public_ct :
    ConstantTime isa (VPre p384v) (JointPublic p384v p384GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384v publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := p384v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun _ => ⟨hO,by decide,hc.am3⟩) ps pt pub

theorem jointVerify_p384_adx_public_ct :
    ConstantTime isa (VPre p384vx) (JointPublic p384vx p384GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384vx publicJointAdx
        (jointDoubleAdx publicJointAdx.K)).inline := by
  have hc := p384vx_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks (fun _ => ⟨hO,by decide,hc.am3⟩) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_public_ct hL hT hI hO _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pre
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.P384.inst (X86_64.abi.withConsts p384v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_adx_public_ct hL hT hI hO _ _ _ _ _ _
    (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (show JointPublic p384vx p384GTab s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P384
