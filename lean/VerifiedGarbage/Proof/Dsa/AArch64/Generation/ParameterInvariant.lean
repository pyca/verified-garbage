module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeLoop
import VerifiedGarbage.Proof.Framework.Omega

/-! # The outer seed loop retains the exact remaining parameter search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

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
        Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a)) ∧
    Frame p.changed initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem GenerationMemory.congr2 {p : GenerationContext} {W : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.x0, .x3, .x4, .x5, .x15] s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl hk.sp hk.wr
  exact h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr

theorem parameterInvariant_stable (p : GenerationContext) (expected : Option Spec.Dsa.Params)
    (initial : State) (used : Nat) : TapeStable (ParameterInvariant p expected initial used) := by
  rintro s t ⟨W, randUsed, h, hu, h10, h16, he, hf, hr, hw⟩ hm hk
  exact ⟨W, randUsed, h.congr2 hm hk, hu, h10, h16, he, hm ▸ hf, hk.rd.trans hr, hk.wr.trans hw⟩

theorem parameterFinished_stable (p : GenerationContext) (expected : Option Spec.Dsa.Params)
    (initial : State) : TapeStable (ParameterFinished p expected initial) := by
  rintro s t ⟨W, h, result, hf, hr, hw⟩ hm hk
  refine ⟨W, h.congr2 hm hk, ?_, hm ▸ hf, hk.rd.trans hr, hk.wr.trans hw⟩
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
    (ft : Outside p.geo.F 152 8 s.mem t.mem) (kt : Keep [.x0, .x15] s t) :
    ParameterFinished p expected initial t := by
  obtain ⟨Wi, randUsed, h, _, _, _, he, fi, ri, wi⟩ := hi
  obtain ⟨Vi, Ri⟩ := h.rep
  have words : ∀ k < 34, W k = Wi k := fun k hk => (R.fr k hk).symm.trans (Ri.fr k hk)
  have ff := p.status_frame ft
  have mt := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd] <;> exact words _ (by decide)) ff kt.rd kt.wr
  refine ⟨upd W 19 3, mt, Or.inl ⟨Or.inr (by simp [upd]), ?_⟩, fi.trans ff, kt.rd.trans ri, kt.wr.trans wi⟩
  rw [he, GenerationContext.remaining, VG.Proof.Dsa.Generation.generationChunks_done (bytes := p.seeds.bytes.drop used) (by simpa only [List.length_drop] using hex)]
  rfl

end VG.Proof.Dsa.AArch64.Generation
