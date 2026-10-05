import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Contract

/-!
# P-384 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.P384.inst.publicKeyContract` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p384.combConsts`),
by name: `vg_ec_p384_public_key(out = x0, d = x1, scratch = x2)`, the result
in `w0`, and the tables at the address of the static `p384.tsym`.
-/

namespace VG.Proof.EcKey.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.AArch64 (p384)
open VG.Proof.Ecdsa.AArch64.P384 (TblHeld p384_combConsts p384_combWords_length satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P384.curve) :=
  publicKey Spec.P384.curve (ofBytes (bytesAt m d 48))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 97⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d, ⟨s.syms p384.tsym, 8 * p384.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 97 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 97 = List.replicate 97 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ s₁.syms p384.tsym = s₂.syms p384.tsym

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 48⟩, ⟨s.syms p384.tsym, 8 * p384.combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 97⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 97⟩ ⟨s.gpr .x1, 48⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 97⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 48⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) (ht : TblHeld s [⟨s.gpr .x0, 97⟩, ⟨s.gpr .x2, 8192⟩]) :
    (Spec.EcKey.P384.inst.publicKeyContract (AArch64.abi.withConsts p384.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
    AArch64.argRegs, p384_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem := satMem
  rd := [⟨0x2000, 48⟩, ⟨0x100000, 337920⟩]
  wr := [⟨0x1000, 97⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

theorem sat_spec :
    (Spec.EcKey.P384.inst.publicKeyContract (AArch64.abi.withConsts p384.combConsts)).pre satState := by
  have hl := p384_combWords_length
  have held : ∀ i < p384.combWords.length, satState.mem.readW (satState.syms p384.tsym +
      BitVec.ofNat 64 (8 * i)) 64 = p384.combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : pkAArch64.Implies
    (Spec.EcKey.P384.inst.publicKeyContract (AArch64.abi.withConsts p384.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p384_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, ht, hw, h1, h2, h3, h4, -, h5⟩ := h
    refine ⟨?_, hw, h2, h1, h3, h4, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p384_combConsts, Abi.withConsts, pkAArch64, pk]
    simp only [pkAArch64, pk, Spec.P384.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
      AArch64.argRegs, p384_combConsts, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.AArch64.P384
