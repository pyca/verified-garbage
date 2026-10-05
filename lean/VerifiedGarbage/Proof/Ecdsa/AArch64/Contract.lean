import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables

/-!
# ECDSA over P-256 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdsa.P256.inst.signContract` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p256.combConsts`),
by name: `vg_ecdsa_p256_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `p256.tsym`.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64 (p256)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P256.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.P256.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let d : Region := ⟨s.gpr .x1, 32⟩
    let digest : Region := ⟨s.gpr .x2, 32⟩
    let k : Region := ⟨s.gpr .x3, 32⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms p256.tsym = s₂.syms p256.tsym

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩,
      ⟨s.syms p256.tsym, 8 * p256.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x4, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x1, 32⟩) (h2 : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x2, 32⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x3, 32⟩)
    (h4 : Region.Disjoint ⟨s.gpr .x0, 64⟩ ⟨s.gpr .x4, 8192⟩)
    (h5 : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x4, 8192⟩)
    (h6 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, 8192⟩)
    (h7 : Region.Disjoint ⟨s.gpr .x3, 32⟩ ⟨s.gpr .x4, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 64 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 32 ≤ 2 ^ 64)
    (f4 : (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64) (ht : TblHeld s [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x4, 8192⟩]) :
    (Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts p256.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, h4, h5, h6,
    h7, f0, f1, f2, f3, f4⟩

theorem sat_spec : (Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts p256.combConsts)).pre
    satState := by
  have hl := p256_combWords_length
  have held : ∀ i < p256.combWords.length, satState.mem.readW (satState.syms p256.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p256.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    signAArch64.Implies (Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts p256.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, h4, h5, h6, h7, h8, -, -, -, h9⟩ := h
    refine ⟨?_, hw, h4, h1, h2, h3, h5, h6, h7, h8, h9, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    sig_implies_post [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi,
      AArch64.argRegs, p256_combConsts, Abi.withConsts, signAArch64, sig]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, p256_combConsts,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.AArch64
