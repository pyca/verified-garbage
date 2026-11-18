module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P256.GTable9Shape

/-! ### `Ecdsa.Verify.X86_64.GContract`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.X86_64.Contract`, which only this module used -/

section

/-!
# ECDSA verification over P-256 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p256.combConsts`),
by name: `vg_ecdsa_p256_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_P256_COMB`. This adapter supplies the correctness precondition and postcondition.
The timing proof uses the shared contract directly, including its public
input buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p256)
open VG.Proof.Ecdsa.X86_64 (TblHeld p256W p256W_length p256_combConsts satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P256.curve (bytesAt m pk 65) (hashToInt Spec.P256.curve (bytesAt m digest 32)) (bytesAt m sig 64)

end VG.Proof.Ecdsa.Verify.X86_64

end

end

/-!
# ECDSA verification over P-256 on x86-64: the contract the joint verifier's proof is written against

`Contract.lean`'s adapter, under the calling convention with the joint
verifier's table of the generator's multiples (`Abi.withConsts
p256v.combConsts`) at the address of the static `VG_P256_GTAB` in place of
the comb's tables: the facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst` for
x86-64 by name, the correctness precondition and postcondition.
-/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/GTables.lean`, which only this module imported.
section

/-!
# ECDSA verification over P-256 on x86-64: the table of the generator's multiples in a static

What the verifier's contract says of its one table, `p256GTab` (`TblHeldG`):
held at the address of the static `VG_P256_GTAB`, not wrapping around, and
apart from the writable regions and the return address; its length
(`p256GW_length`, from the table's shape alone); and a memory holding it, for
the contract's witness (`satMemG`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (Cfg)
open VG.Impl.P256.X86_64 (p256v p256vx p256GTab)

/-- The words of the verifier's table. -/
abbrev p256GW : List (BitVec 64) := p256v.combWords p256GTab

theorem p256v_combConsts : p256v.combConsts = [("VG_P256_GTAB", p256GW)] := rfl

/-- The table at the static `VG_P256_GTAB`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < p256GW.length, s.mem.readW (s.syms "VG_P256_GTAB" + BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0) ∧
  (s.syms "VG_P256_GTAB").toNat + 8 * p256GW.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P256_GTAB", 8 * p256GW.length⟩ r

/-- `p256GW` has `256 · 8` words. -/
theorem p256GW_length : p256GW.length = 2048 :=
  (Proof.Weierstrass.tcombWords_length (n := p256v.n) (R := p256v.R) (p := p256v.C.p)
    (H := 256) (tbl := Impl.P256.p256G9) Proof.P256.p256G9_length Proof.P256.p256G9_rows).trans rfl

/-- The table's region, `8 · 2048` bytes at the static's address (see
`p256_constRegions`). -/
theorem p256G_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P256_GTAB", p256GW)] = [⟨f "VG_P256_GTAB", 16384⟩] := by
  rw [Proof.Ecdsa.X86_64.constRegions_single, p256GW_length]

/-- The memory of the contract's witness: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMemG : Mem := constMem 0x100000 p256GW

theorem satMemG_held : ∀ i < p256GW.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p256GW_length]; omega_using [])

end VG.Proof.Ecdsa.Verify.X86_64
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.P256.X86_64 (p256v)

def verifyGX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 65⟩
    let digest : Region := ⟨s.gpr .rsi, 32⟩
    let sig : Region := ⟨s.gpr .rdx, 64⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig, ⟨s.syms "VG_P256_GTAB", 8 * p256GW.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeldG s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_P256_GTAB" = s₂.syms "VG_P256_GTAB"

/-- A state satisfying the precondition. -/
def satStateG : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemG
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩, ⟨0x100000, 16384⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem specG_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 65⟩, ⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 64⟩,
      ⟨s.syms "VG_P256_GTAB", 8 * p256GW.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 65⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 65⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 64⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 65 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 64 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeldG s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P256_GTAB").toNat % 64 = 0) :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem satG_spec : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pre
    satStateG := by
  have hl := p256GW_length
  have held : ∀ i < p256GW.length, satStateG.mem.readW (satStateG.syms "VG_P256_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0 := satMemG_held
  refine specG_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (by decide) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem impliesG :
    verifyGX86_64.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p256v_combConsts, Abi.withConsts, verifyGX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satStateG, satG_spec⟩

/-- The shared contract, but with `verifyGX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyGK₀ : Contract isa :=
  { pre := (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pre
    post := verifyGX86_64.post
    pub := (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pub }

theorem satG_spec8 :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts) 8).pre satStateG := by
  have held : ∀ i < p256GW.length, satStateG.mem.readW (satStateG.syms "VG_P256_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0 := satMemG_held
  sig_pre [Spec.Ecdsa.P256.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
    Abi.withConsts, p256G_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem impliesG8 :
    verifyGK₀.Implies (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => impliesG.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satStateG, satG_spec8⟩⟩

end VG.Proof.Ecdsa.Verify.X86_64

end

end

/-! The existing verification contract makes all inputs to the joint routine public. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Impl.P256.X86_64 (p256v p256vx p256GTab)
open VG.Proof.Weierstrass.X86_64 (InvSounds)

theorem p256v_ok (hI : InvSounds) : CfgOk p256v := cfgOk_gtab (p256_ok hI) _

theorem p256vx_ok (hI : InvSounds) : CfgOk p256vx := cfgOk_gtab (p256x_ok hI) _

theorem preG_of {s : State} (h : verifyGX86_64.pre s) : VPre p256v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256v_combConsts, show p256v.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p256v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem preG_of_x {s : State} (h : verifyGX86_64.pre s) : VPre p256vx s :=
  { preG_of h with }

theorem jointPublic_of_spec {a b : State}
    (pub : (Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst (X86_64.abi.withConsts p256v.combConsts)).pub a b) :
    JointPublic p256v p256GTab a b := by
  sig_pub [Spec.Ecdsa.P256.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.P256.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p256v_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 32,peer_bytes _ _ 32] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (32+32)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (32+32) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> p256v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64
