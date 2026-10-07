import VerifiedGarbage.Spec.Ecdsa.Verify.P384
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Tables

/-!
# ECDSA verification over P-384 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.P384.inst.verifyContract` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p384.combConsts`),
by name: `vg_ecdsa_p384_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_P384_COMB`. This adapter supplies the correctness precondition and
postcondition. The timing proof uses the shared contract directly, including
its public input buffers.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P384

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p384)
open VG.Proof.Ecdsa.X86_64.P384 (TblHeld p384W p384W_length p384_combConsts satMem satMem_held)

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
    s.rd = [pk, digest, sig, ⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ digest.Disjoint scratch ∧ sig.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [scratch, ret]
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.syms "VG_P384_COMB" = s₂.syms "VG_P384_COMB"

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
  rd := [⟨0x1000, 97⟩, ⟨0x2000, 48⟩, ⟨0x3000, 96⟩, ⟨0x100000, 337920⟩]
  wr := [⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 97⟩, ⟨s.gpr .rsi, 48⟩, ⟨s.gpr .rdx, 96⟩,
      ⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 97⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 48⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 96⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 97⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 48⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 96⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 97 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 48 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 96 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rcx, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr]),
    hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, f0, f1, f2, f3⟩

theorem sat_spec : (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pre
    satState := by
  have hl := p384W_length
  have held : ∀ i < p384W.length, satState.mem.readW (satState.syms "VG_P384_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (by decide) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    verifyX86_64.Implies (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, h1, h2, h3, -, -, -, r4, -, -, -, f4⟩ := h
    refine ⟨?_, hw, h1, h2, h3, r4, f4, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p384_combConsts, Abi.withConsts, verifyX86_64, vf]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
      Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, -, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.Verify.X86_64.P384
