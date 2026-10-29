module
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.Generation.Chunks

/-! # The outer seed loop retains the exact remaining parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GenerationContext.remaining (p : GenerationContext) (seedUsed randUsed : Nat) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * p.geo.pLen)
    ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) (8 * p.geo.qLen)
    (Spec.Dsa.generationChunks p.geo.qLen (p.seeds.bytes.drop seedUsed)) (p.rand.bytes.drop randUsed)

def ParameterInvariant (p : GenerationContext) (expected : Option Spec.Dsa.Params) (initial : State)
    (seedUsed : Nat) (s : State) : Prop :=
  ∃ W randUsed, GenerationMemory p W s ∧ randUsed ≤ p.rand.bytes.length ∧
    W 10 = BitVec.ofNat 64 seedUsed ∧ W 16 = BitVec.ofNat 64 randUsed ∧
    expected = p.remaining seedUsed randUsed ∧ Frame p.changed initial.mem s.mem ∧
    s.rd = initial.rd ∧ s.wr = initial.wr

def ParameterFinished (p : GenerationContext) (expected : Option Spec.Dsa.Params) (initial s : State) : Prop :=
  ∃ W, GenerationMemory p W s ∧
    (((W 19 = 0 ∨ W 19 = 3) ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)) ∧
    Frame p.changed initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem GenerationMemory.congr2 {p : GenerationContext} {W : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.rax, .rcx] s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl (hk.gpr (by decide)) hk.2.2
  exact h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2

theorem parameterInvariant_stable (p : GenerationContext) (expected : Option Spec.Dsa.Params)
    (initial : State) (used : Nat) : TapeStable (ParameterInvariant p expected initial used) := by
  rintro s t ⟨W, randUsed, h, hu, h10, h16, he, hf, hr, hw⟩ hm hk
  exact ⟨W, randUsed, h.congr2 hm hk, hu, h10, h16, he, hm ▸ hf, hk.2.1.trans hr, hk.2.2.trans hw⟩

theorem parameterFinished_stable (p : GenerationContext) (expected : Option Spec.Dsa.Params)
    (initial : State) : TapeStable (ParameterFinished p expected initial) := by
  rintro s t ⟨W, h, result, hf, hr, hw⟩ hm hk
  refine ⟨W, h.congr2 hm hk, ?_, hm ▸ hf, hk.2.1.trans hr, hk.2.2.trans hw⟩
  rcases result with fail | ⟨h19, a, he, bytes⟩
  · exact Or.inl fail
  · exact Or.inr ⟨h19, a, he, hm ▸ bytes⟩

theorem GenerationContext.status_frame {p : GenerationContext} {m m' : Mem}
    (h : Outside p.geo.F 152 8 m m') : Frame p.changed m m' := by
  apply GenerationContext.frame_single
  intro a ha
  apply h a
  right
  have hn := ha ⟨p.geo.F, frameBytes⟩ (by simp)
  change ¬ ofs p.geo.F a < frameBytes at hn
  unfold frameBytes at hn
  omega

theorem parameter_done {p : GenerationContext} {expected : Option Spec.Dsa.Params} {initial : State}
    {used : Nat} {s t : State} {V : Nat → Byte} {W : Nat → BitVec 64}
    (hi : ParameterInvariant p expected initial used s) (hex : p.seeds.bytes.length - used < p.geo.qLen)
    (R : Rep s.mem p.geo.F p.geo.hash V W) (Lt : Lay t p.geo.F p.geo.hash)
    (Rt : Rep t.mem p.geo.F p.geo.hash V (upd W 19 3))
    (ft : Outside p.geo.F 152 8 s.mem t.mem) (kt : Keep [.rax] s t) :
    ParameterFinished p expected initial t := by
  obtain ⟨Wi, randUsed, h, _, _, _, he, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 37, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  have ff := p.status_frame ft
  have mt := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd] <;> exact words _ (by decide)) ff kt.2.1 kt.2.2
  refine ⟨upd W 19 3, mt, Or.inl ⟨Or.inr (by simp [upd]), ?_⟩, fi.trans ff, kt.2.1.trans ri, kt.2.2.trans wi⟩
  rw [he, GenerationContext.remaining, VG.Proof.Dsa.Generation.generationChunks_done (bytes := p.seeds.bytes.drop used) (by simpa only [List.length_drop] using hex)]
  rfl

end VG.Proof.Dsa.X86_64.Generation
