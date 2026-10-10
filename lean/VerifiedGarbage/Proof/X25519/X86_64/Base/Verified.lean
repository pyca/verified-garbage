import VerifiedGarbage.Proof.X25519.X86_64.Base.CT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig

/-! Fixed-base X25519 satisfies the reviewed contract, with either field backend, with 8 bytes
of stack for its call of `vg_gf25519_r64_invert`: correct and constant time as its code with the
inversion inlined (`Verified.of_inline`). -/
namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
variable {fld : Arith} [EdArith fld]

theorem engine_public (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engine fld).inline (fun _ _ => True) :=
  engineOf_ct combOk combMultiply_inline base k T


theorem x25519Base_ok [DivstepInv] (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa (x25519Base fld).inline s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519Base_correct (fld := fld) hs
  exact ⟨tr, t, he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; fld_lit_decide) he h.1, h.2⟩

/-- The shared contract's precondition, from its facts. -/
theorem base_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩]) :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem base_sat :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)).pre baseSatStateT := by
  refine base_spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem base_implies :
    baseLocal.Implies (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, combWords_length] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, ht, hw, -, h2, h3, r1, -, r3, -, -, f2⟩ := h
    refine ⟨?_, hw, h3, r1, r3, f2, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, baseLocal]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨baseSatStateT, base_sat⟩

/-- The shared contract's precondition with 8 bytes of stack, from its facts. -/
theorem base_spec_pre8 {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (q1 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdi, 32⟩)
    (q2 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (q3 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64) (hsp : 8 ≤ (s.gpr .rsp).toNat)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hq : Region.Disjoint ⟨s.syms combSym, 40448⟩ ⟨s.gpr .rsp - 8#64, 8⟩) :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hq, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, q1, q2, q3, f0, f1, f2⟩

theorem base_sat8 :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8).pre baseSatStateT := by
  refine base_spec_pre8 rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩ (Region.disjoint_of_sep (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem base_implies8 :
    baseLocal.Implies (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  base_implies.stack8 ⟨baseSatStateT, base_sat8⟩

/-- The output is apart from the call's return address. -/
theorem base_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : baseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : baseLocal.post s b) :
    baseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 32) (by rw [hw]; simp) (by decide)
  exact (bytes_patch hb).trans hp

theorem base_verified_of {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, baseLocal.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s')
    (hct : ConstantTime isa baseLocal.pre baseLocal.pub c.inline) :
    Verified X86_64.target c (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  Verified.of_inline hc hcor hct base_implies8 (fun _ h => Sig.clear_of_pre_consts h)
    (fun s b hv u hs hp => base_patch s b hv u (base_implies8.pre s hs) (Sig.clear_of_pre_consts hs) hp)
    (fun s₁ s₂ h₁ h₂ hp => (base_implies8.pub s₁ s₂ h₁ h₂ hp).1)

theorem x25519Base_verified [DivstepInv] : Verified X86_64.target (x25519Base fld)
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  base_verified_of (by fld_lit_decide) x25519Base_ok (x25519Base_ct engine_public)

end VG.Proof.X25519.X86_64.Base
