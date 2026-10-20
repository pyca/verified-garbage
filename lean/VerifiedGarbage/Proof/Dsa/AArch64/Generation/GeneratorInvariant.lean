module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory

/-! # Search invariant and exact successful generator output -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GeneratorInvariant (p : GeneratorSearchPlan) (expected : Option Nat) (initial : State)
    (used : Nat) (s : State) : Prop :=
  ∃ W, GeneratorSearchMemory p W s ∧ W 20 = BitVec.ofNat 64 used ∧
    expected = p.remaining used ∧ Frame p.core.changed initial.mem s.mem ∧
    s.rd = initial.rd ∧ s.wr = initial.wr

def GeneratorFinished (p : GeneratorSearchPlan) (expected : Option Nat) (initial s : State) : Prop :=
  ∃ W, GeneratorSearchMemory p W s ∧
    ((W 19 = 3 ∧ expected = none) ∨
      ∃ value, W 19 = 1 ∧ expected = some value ∧
        Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.core.B g) p.core.len = Spec.Dsa.encodeBE p.core.len value) ∧
    Frame p.core.changed initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem generatorMemory_congr {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s t : State}
    (h : GeneratorSearchMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.x0, .x3, .x4, .x5, .x15] s t) :
    GeneratorSearchMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.core.F p.core.S V W := hm ▸ R
  exact h.frame (lay_of_rep h.layout R Rt rfl hk.sp hk.wr)
    ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr

theorem generatorInvariant_stable (p : GeneratorSearchPlan) (expected : Option Nat)
    (initial : State) (used : Nat) : TapeStable (GeneratorInvariant p expected initial used) := by
  rintro s t ⟨W, h, h20, he, hf, hr, hw⟩ hm hk
  exact ⟨W, generatorMemory_congr h hm hk, h20, he, hm ▸ hf, hk.rd.trans hr, hk.wr.trans hw⟩

theorem generatorFinished_stable (p : GeneratorSearchPlan) (expected : Option Nat)
    (initial : State) : TapeStable (GeneratorFinished p expected initial) := by
  rintro s t ⟨W, h, result, hf, hr, hw⟩ hm hk
  refine ⟨W, generatorMemory_congr h hm hk, ?_, hm ▸ hf, hk.rd.trans hr, hk.wr.trans hw⟩
  rcases result with fail | ⟨value, h19, he, hg⟩
  · exact Or.inl fail
  · exact Or.inr ⟨value, h19, he, hm ▸ hg⟩

theorem generator_frame_write {p : GeneratorSearchPlan} {m m' : Mem}
    (h : Outside p.core.F 152 8 m m') : Frame p.core.changed m m' := by
  intro a ha
  apply h a
  right
  have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
  change ¬ ofs p.core.F a < frameBytes at hn
  unfold frameBytes at hn
  omega

theorem generator_done {p : GeneratorSearchPlan} {expected : Option Nat} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : GeneratorInvariant p expected initial used s) (hex : p.tape.length - used < p.core.len)
    (R : Rep s.mem p.core.F p.core.S V W)
    (Lt : Lay t p.core.F p.core.S) (Rt : Rep t.mem p.core.F p.core.S V (upd W 19 3))
    (ft : Outside p.core.F 152 8 s.mem t.mem) (kt : Keep [.x0, .x15] s t) :
    GeneratorFinished p expected initial t := by
  obtain ⟨Wi, h, _, he, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 34, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  have ff := generator_frame_write ft
  refine ⟨upd W 19 3, h.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr,
    Or.inl ⟨by simp [upd], he.trans (p.remaining_done hex)⟩, fi.trans ff,
    kt.rd.trans ri, kt.wr.trans wi⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [upd] <;> exact words _ (by decide)

end VG.Proof.Dsa.AArch64.Generation
