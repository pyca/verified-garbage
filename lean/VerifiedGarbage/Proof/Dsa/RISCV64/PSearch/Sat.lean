module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Base
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

-- separate module: the witness's memory and checks, apart from the proofs of the search

/-! # DSA parameter search on RISC-V: a state satisfying the precondition

A 1024-bit search with no seeds left to reject and an empty tape: `out` at
`0x1000`, `used` at `0x2000`, the tape at `0x3000`, the state at `0x4000`
(words 0, 128 and `32769 · 128`), `scratch` at `0x40000` (`64 · 128 + 1024`
words), the stack pointer at `0x8000` and the table at `0x20000`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64

/-- The state's words. -/
def satSmall : Mem := fun a =>
  if a = 0x4008 then 0x80 else if a = 0x4010 then 0x80 else if a = 0x4012 then 0x40 else 0

/-- The witness's memory: the state's words, and the table at `0x20000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x4000).toNat < 0x20 then satSmall a else constMem 0x20000 Impl.RsaKeyGen.TrialTable32.packed a

private theorem packed_length' : Impl.RsaKeyGen.TrialTable32.packed.length = 1024 :=
  Proof.RsaKeyGen.TrialTable32.packed_length

theorem satMem_held : ∀ i < Impl.RsaKeyGen.TrialTable32.packed.length,
    satMem.readW (0x20000 + BitVec.ofNat 64 (8 * i)) 64 = Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
  intro i hi
  rw [← constMem_held _ _ (by rw [packed_length']; decide) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hn : ¬ (0x20000 + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x20 := by
    rw [packed_length'] at hi
    simp only [Nat.reduceDiv] at hj
    have h1 : (0x20000 : Addr).toNat = 131072 := rfl
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1, h2]
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

theorem satMem_small (a : Addr) (ha : (a - 0x4000).toNat + 8 ≤ 0x20) :
    satMem.readW a 64 = satSmall.readW a 64 := by
  refine Mem.readW_congr fun j hj => ?_
  have hn : (a + BitVec.ofNat 64 j - 0x4000 : Addr).toNat < 0x20 := by
    simp only [Nat.reduceDiv] at hj
    have h2 : (0x4000 : Addr).toNat = 16384 := rfl
    have := a.isLt
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h2] at ha ⊢
    omega
  unfold satMem
  simp only [hn, ↓reduceIte]

/-- The witness. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 276 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x40000 | .a6 => 9216
    | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x3000, 0⟩, ⟨0x20000, 8192⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x40000, 9216 * 8⟩, ⟨0x4000, 32⟩]
  syms _ := 0x20000

theorem sat_w0 : satMem.readW 0x4000 64 = 0 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w8 : satMem.readW (0x4000 + 8) 64 = 128 := (satMem_small _ (by decide)).trans (by decide)
theorem sat_w16 : satMem.readW (0x4000 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy 128) :=
  (satMem_small _ (by decide)).trans (by decide)

private theorem kT_eq' : kT = [(Impl.RsaKeyGen.TrialTable32.symbol, Impl.RsaKeyGen.TrialTable32.packed)] := rfl

theorem sat_base : (Spec.Dsa.parameterSearchContract abi 512).pre (stripConsts kT satState) := by
  unfold Spec.Dsa.parameterSearchContract
  refine Sig.contract_pre_of_check (by decide +kernel) ?_
  sig_reduce [Spec.Dsa.parameterSearchSig, abi, argRegs, List.append_eq]
  sig_and_intros
  all_goals (try simp only [sat_w0, sat_w8, sat_w16]); decide

theorem sat_consts : ConstsOk kT 512 satState := by
  have hl := packed_length'
  have held := satMem_held
  rw [kT_eq']
  generalize Impl.RsaKeyGen.TrialTable32.packed = W at hl held ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]; rfl
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact held
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by decide, fun r hr => ?_, fun r hr => ?_⟩
    · change r ∈ [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x40000, 9216 * 8⟩, ⟨0x4000, 32⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · change r ∈ stackBelow 0x8000 512 at hr
      simp only [stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Region.disjoint_of_sep (by decide)
  · rw [constRegs, Abi.constRegions_cons, Abi.constRegions_nil, hl]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    decide

theorem sat : (Spec.Dsa.parameterSearchContract (abi.withConsts kT) 512).pre satState := by
  have h₁ := sat_base
  have h₂ := sat_consts
  unfold Spec.Dsa.parameterSearchContract at h₁ ⊢
  rw [kT_eq'] at h₁ h₂ ⊢
  exact pre_consts.mpr ⟨h₁, h₂⟩

end VG.Proof.Dsa.RISCV64.PSearch
