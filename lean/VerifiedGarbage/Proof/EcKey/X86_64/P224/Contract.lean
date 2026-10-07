import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Tables

/-!
# P-224 public keys on x86-64: the contract the proof is written against

The facts of `Spec.EcKey.P224.inst.publicKeyContract` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p224.combConsts`),
by name: `vg_ec_p224_public_key(out = rdi, d = rsi, scratch = rdx)`, the
result in `eax`, and the tables at the address of the static
`VG_P224_COMB`.
-/

namespace VG.Proof.EcKey.X86_64.P224

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.X86_64 (p224)
open VG.Proof.Ecdsa.X86_64.P224 (TblHeld p224W p224W_length p224_combConsts satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P224.curve) :=
  publicKey Spec.P224.curve (ofBytes (bytesAt m d 28))

def pkX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 57⟩
    let d : Region := ⟨s.gpr .rsi, 28⟩
    let scratch : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 57 = encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 57 = List.replicate 57 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.syms "VG_P224_COMB" = s₂.syms "VG_P224_COMB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 28⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 28⟩, ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rsi, 28⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 28⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 57⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 28⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 28 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem sat_spec : (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)).pre
    satState := by
  have hl := p224W_length
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    pkX86_64.Implies (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, h1, h2, h3, r1, -, r3, f0, -, f2⟩ := h
    refine ⟨?_, hw, h2, h1, h3, r1, r3, f0, f2, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts, pkX86_64, pk]
    simp only [pkX86_64, pk, Spec.P224.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.X86_64.P224
