import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Contract

/-!
# P-224 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.P224.inst.publicKeyContract` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p224.combConsts`),
by name: `vg_ec_p224_public_key(out = x0, d = x1, scratch = x2)`, the result
in `w0`, and the tables at the address of the static `p224.tsym`.
-/

namespace VG.Proof.EcKey.AArch64.P224

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.AArch64 (p224)
open VG.Proof.Ecdsa.AArch64.P224 (TblHeld p224_combConsts p224_combWords_length satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P224.curve) :=
  publicKey Spec.P224.curve (ofBytes (bytesAt m d 28))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 57⟩
    let d : Region := ⟨s.gpr .x1, 28⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d, ⟨s.syms p224.tsym, 8 * p224.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 57 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 57 = List.replicate 57 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ s₁.syms p224.tsym = s₂.syms p224.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 28⟩, ⟨s.syms p224.tsym, 8 * p224.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x1, 28⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 57⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 28⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 28 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) (ht : TblHeld s [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.EcKey.P224.inst.publicKeyContract (AArch64.abi.withConsts p224.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, AArch64.abi,
    AArch64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x2000, 28⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_spec :
    (Spec.EcKey.P224.inst.publicKeyContract (AArch64.abi.withConsts p224.combConsts)).pre satState := by
  have hl := p224_combWords_length
  have held : ∀ i < p224.combWords.length, satState.mem.readW (satState.syms p224.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p224.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : pkAArch64.Implies
    (Spec.EcKey.P224.inst.publicKeyContract (AArch64.abi.withConsts p224.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, h4, -, h5⟩ := h
    refine ⟨?_, hw, h2, h1, h3, h4, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p224_combConsts, Abi.withConsts, pkAArch64, pk]
    simp only [pkAArch64, pk, Spec.P224.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p224_combConsts, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.AArch64.P224
