module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context

/-! # A native seed attempt returns either exhaustion, retry, or packed parameters -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Generation.Layout

def SeedOutcome (p : GenerationContext) (res : Option (Option Spec.Dsa.Params × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = 0 ∧ res = none) ∨
  (W 19 = 3 ∧ res = some (none, p.rand.bytes.drop used)) ∨
  (W 19 = 1 ∧ ∃ a, res = some (some a, p.rand.bytes.drop used) ∧
    Spec.Rsa.bytesAt t.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
      Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)

def SeedFinished (p : GenerationContext) (initial : Nat → BitVec 64)
    (res : Option (Option Spec.Dsa.Params × List Byte)) (s t : State) : Prop :=
  ∃ W used, GenerationMemory p W t ∧ used ≤ p.rand.bytes.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (∀ k ∈ searchSlots, W k = initial k) ∧ SeedOutcome p res W used t ∧
    Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem SeedFinished.prepend {p : GenerationContext} {Wi Wm : Nat → BitVec 64}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {s u t : State}
    (h : SeedFinished p Wm res u t) (slots : ∀ k ∈ searchSlots, Wm k = Wi k)
    (hf : Frame p.changed s.mem u.mem) (hr : u.rd = s.rd) (hw : u.wr = s.wr) :
    SeedFinished p Wi res s t := by
  obtain ⟨W, used, mt, hu, h16, hs, outcome, ft, rt, wt⟩ := h
  exact ⟨W, used, mt, hu, h16, fun k hk => (hs k hk).trans (slots k hk), outcome,
    hf.trans ft, rt.trans hr, wt.trans hw⟩

theorem searchSlots_generator {k : Nat} (h : k ∈ searchSlots) : k ∈ generatorSlots := by
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [generatorSlots]

theorem searchSlots_not_status {k : Nat} (h : k ∈ searchSlots) : k ≠ 19 := by
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Dsa.X86_64.Generation
