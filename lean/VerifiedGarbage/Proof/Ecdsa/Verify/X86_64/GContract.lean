module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Contract
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Impl.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Framework.ConstMem

import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P256.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
/-!
# ECDSA verification over P-256 on x86-64: the contract the joint verifier's proof is written against

`Contract.lean`'s adapter, under the calling convention with the joint
verifier's table of the generator's multiples (`Abi.withConsts
p256v.combConsts`) at the address of the static `VG_P256_GTAB` in place of
the comb's tables: the facts of `Spec.Ecdsa.P256.inst.verifyContract` for
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

theorem p256v_gtab : p256v.gtab = some p256GTab := rfl

theorem p256vx_gtab : p256vx.gtab = some p256GTab := rfl

theorem p256v_combConsts : p256v.combConsts = [("VG_P256_GTAB", p256GW)] := rfl

theorem p256vx_combConsts : p256vx.combConsts = [("VG_P256_GTAB", p256GW)] := rfl

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
  exact constMem_held _ _ (by rw [p256GW_length]; omega)

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
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem satG_spec : (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pre
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
    verifyGX86_64.Implies (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
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
    sig_implies_post [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p256v_combConsts, Abi.withConsts, verifyGX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satStateG, satG_spec⟩

/-- The shared contract, but with `verifyGX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyGK₀ : Contract isa :=
  { pre := (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pre
    post := verifyGX86_64.post
    pub := (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pub }

theorem satG_spec8 :
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts) 8).pre satStateG := by
  have held : ∀ i < p256GW.length, satStateG.mem.readW (satStateG.syms "VG_P256_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = p256GW.getD i 0 := satMemG_held
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256v_combConsts,
    Abi.withConsts, p256G_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem impliesG8 :
    verifyGK₀.Implies (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => impliesG.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satStateG, satG_spec8⟩⟩

end VG.Proof.Ecdsa.Verify.X86_64
