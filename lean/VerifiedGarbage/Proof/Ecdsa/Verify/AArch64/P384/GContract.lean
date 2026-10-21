module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.P384.GTable9Shape
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedTable
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# ECDSA verification over P-384 on AArch64 with its own table: the contract

`Contract.lean`'s contract with the verifier's table of `[m]G`, `m = 1 … 256`
(`P384Joint.p384v`, in the static `VG_P384_GTAB`) in place of the comb's: the
facts of `Spec.Ecdsa.P384.inst.verifyContract` with those constants, by name,
and the precondition the proofs are written against (`VPreT`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.Verify.AArch64 (P384Joint.p384v)
open VG.Impl.Ecdsa.AArch64 (p384)

/-- The verifier's table at its static, held, not wrapping around, and apart from the regions
`wr`. -/
def TblHeldG (s : State) (wr : List Region) : Prop :=
  (∀ i < P384Joint.p384v.combWords.length,
    s.mem.readW (s.syms P384Joint.p384v.tsym + BitVec.ofNat 64 (8 * i)) 64 =
      P384Joint.p384v.combWords.getD i 0) ∧
  (s.syms P384Joint.p384v.tsym).toNat + 8 * P384Joint.p384v.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩ r

theorem p384v_combConsts :
    P384Joint.p384v.combConsts = [(P384Joint.p384v.tsym, P384Joint.p384v.combWords)] := rfl

/-- The table has `256 · 12` words. -/
theorem p384v_combWords_length : P384Joint.p384v.combWords.length = 3072 := by
  rw [Joint.p384v_words]
  exact (Proof.Weierstrass.tcombWords_length (n := 6) (R := p384.R) (p := p384.C.p)
    (H := 256) (tbl := Impl.P384.p384G9) Proof.P384.p384G9_length Proof.P384.p384G9_rows).trans rfl

/-- The memory of the contract's witness: the table at `0x100000`. -/
@[irreducible] def satMemG : Mem := constMem 0x100000 P384Joint.p384v.combWords

theorem satMemG_held : ∀ i < P384Joint.p384v.combWords.length,
    satMemG.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = P384Joint.p384v.combWords.getD i 0 := by
  unfold satMemG
  exact constMem_held _ _ (by rw [p384v_combWords_length]; omega)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vfG (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P384.curve (bytesAt m pk 97) (hashToInt Spec.P384.curve (bytesAt m digest 48)) (bytesAt m sig 96)

def verifyGAArch64 : Contract AArch64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 97⟩
    let digest : Region := ⟨s.gpr .x1, 48⟩
    let sig : Region := ⟨s.gpr .x2, 96⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [pk, digest, sig, ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩] ∧
      s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeldG s [scratch]
  post s s' := (s'.gpr .x0).setWidth 32 = if vfG s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧ s₁.syms P384Joint.p384v.tsym = s₂.syms P384Joint.p384v.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_preG {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 97⟩, ⟨s.gpr .x1, 48⟩, ⟨s.gpr .x2, 96⟩,
      ⟨s.syms P384Joint.p384v.tsym, 8 * P384Joint.p384v.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 97⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 48⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 96⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 96 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeldG s [⟨s.gpr .x3, 8192⟩]) :
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2,
    f3⟩

/-- A state satisfying the precondition: the table at `0x100000`. -/
def satStateG : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMemG
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 24576⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_specG :
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre
      satStateG := by
  have hl := p384v_combWords_length
  have held : ∀ i < P384Joint.p384v.combWords.length, satStateG.mem.readW (satStateG.syms P384Joint.p384v.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = P384Joint.p384v.combWords.getD i 0 := satMemG_held
  refine spec_preG (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_singleton]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem impliesG : verifyGAArch64.Implies
    (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    sig_implies_post [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi,
      AArch64.argRegs, p384v_combConsts, Abi.withConsts, verifyGAArch64, vfG]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p384v_combConsts,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, -, h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hsp, hsy⟩
  sat := ⟨satStateG, sat_specG⟩

theorem jacPublicG_of_spec {s₁ s₂ : State}
    (pub : (Spec.Ecdsa.P384.inst.verifyContract
      (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pub s₁ s₂) :
    JacPublicT p384 "VG_P384_GTAB" s₁ s₂ := by
  sig_pub [Spec.Ecdsa.P384.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve,Spec.Ecdsa.scratchWords,AArch64.abi,AArch64.argRegs,p384v_combConsts,
    Abi.withConsts] at pub
  obtain ⟨hsp,hsy,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨⟨hsp,fun r hr => ?_⟩,hsy,?_,?_,?_⟩
  · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.1
  · exact front.2
  · exact parts.2

/-- The precondition the proofs are written against. -/
theorem vpreG_of {s : State} (h : verifyGAArch64.pre s) : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp [show P384Joint.p384v.tsym="VG_P384_GTAB" from rfl],held,fit,hdw _ (by simp)⟩⟩

end VG.Proof.Ecdsa.Verify.AArch64.P384
