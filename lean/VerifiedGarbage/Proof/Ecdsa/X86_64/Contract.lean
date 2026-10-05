import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables

/-!
# ECDSA over P-256 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.P256.inst.signContract` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p256.combConsts`),
by name: `vg_ecdsa_p256_sign(out = rdi, d = rsi, digest = rdx, k = rcx,
scratch = r8)`, the result in `eax`, and the tables at the address of the
static `VG_P256_COMB`.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p256)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P256.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.P256.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 64⟩
    let d : Region := ⟨s.gpr .rsi, 32⟩
    let digest : Region := ⟨s.gpr .rdx, 32⟩
    let k : Region := ⟨s.gpr .rcx, 32⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k, ⟨s.syms "VG_P256_COMB", 8 * p256W.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.syms "VG_P256_COMB" = s₂.syms "VG_P256_COMB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 32⟩,
      ⟨s.syms "VG_P256_COMB", 8 * p256W.length⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .r8, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 32⟩) (h2 : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 32⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, 32⟩)
    (h4 : Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .r8, 8192⟩)
    (h5 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, 8192⟩)
    (h6 : Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, 8192⟩)
    (h7 : Region.Disjoint ⟨s.gpr .rcx, 32⟩ ⟨s.gpr .r8, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 64⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 32⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 32⟩)
    (r5 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 32 ≤ 2 ^ 64)
    (f4 : (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts p256.combConsts)).pre s := by
  sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, h4, h5, h6, h7, r1, r2, r3, r4, r5, f0, f1, f2, f3, f4⟩

theorem sat_spec : (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts p256.combConsts)).pre
    satState := by
  have hl := p256W_length
  have held : ∀ i < p256W.length, satState.mem.readW (satState.syms "VG_P256_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    signX86_64.Implies (Spec.Ecdsa.P256.inst.signContract (X86_64.abi.withConsts p256.combConsts)) where
  pre s h := by
    sig_pre [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
      Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, h1, h2, h3, h4, h5, h6, h7, r1, -, -, -, r5, h8, -, -, -, h9⟩ := h
    refine ⟨?_, hw, h4, h1, h2, h3, h5, h6, h7, r1, r5, h8, h9, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    sig_implies_post [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, p256_combConsts, Abi.withConsts, signX86_64, sig]
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
      Spec.P256.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p256_combConsts,
      Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3, h4, h5⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.Ecdsa.X86_64
