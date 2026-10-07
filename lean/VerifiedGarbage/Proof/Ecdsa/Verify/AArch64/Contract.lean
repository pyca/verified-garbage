import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Contract

/-!
# ECDSA verification over P-256 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdsa.P256.inst.verifyContract` for AArch64, by name:
`vg_ecdsa_p256_verify(public = x0, digest = x1, sig = x2, scratch = x3)`,
the result in `w0`. This adapter supplies the correctness precondition and
postcondition. The timing proof uses the shared contract directly, including
its public input buffers.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64 (p256)
open VG.Proof.Ecdsa.AArch64 (TblHeld p256_combConsts p256_combWords_length satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P256.curve (bytesAt m pk 65) (hashToInt Spec.P256.curve (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyAArch64 : Contract AArch64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0, 65⟩
    let digest : Region := ⟨s.gpr .x1, 32⟩
    let sig : Region := ⟨s.gpr .x2, 64⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [pk, digest, sig, ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧
      (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch]
  post s s' := (s'.gpr .x0).setWidth 32 = if vf s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) then 1 else 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧ s₁.syms p256.tsym = s₂.syms p256.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 65⟩, ⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 64⟩,
      ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 65⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 65 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 64 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .x3, 8192⟩]) :
    (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2,
    f3⟩

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_spec :
    (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre satState := by
  have hl := p256_combWords_length
  have held : ∀ i < p256.combWords.length, satState.mem.readW (satState.syms p256.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p256.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_singleton]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)

theorem implies : verifyAArch64.Implies
    (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, -, -, -, h4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, h4, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    sig_implies_post [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi,
      AArch64.argRegs, p256_combConsts, Abi.withConsts, verifyAArch64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, -, h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.AArch64
