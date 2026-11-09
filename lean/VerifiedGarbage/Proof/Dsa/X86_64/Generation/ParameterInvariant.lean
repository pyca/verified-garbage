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

theorem GenerationMemory.congr2 {p : GenerationContext} {W : Nat → BitVec 64} {s t : State}
    (h : GenerationMemory p W s) (hm : t.mem = s.mem) (hk : Keep [.rax, .rcx] s t) : GenerationMemory p W t := by
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.geo.F p.geo.hash V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl (hk.gpr (by decide)) hk.2.2
  exact h.frame Lt ⟨V, Rt⟩ (fun _ _ => rfl) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2

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

end VG.Proof.Dsa.X86_64.Generation
