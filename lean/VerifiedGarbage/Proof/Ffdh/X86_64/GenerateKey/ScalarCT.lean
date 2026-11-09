module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.BoundCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.BoundCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: sampling does not branch on the random bytes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

def MS (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s ∧
  word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧ word s.mem p.B (8 * sMsk) = p.msk ∧ p.mv = true

/-- The result is ready for the shared private-key setup and scalar-range check. -/
def Sliced (p : GkP) (s : State) : Prop := ∃ rb, CheckPrivate.Base p.kp (p.xb rb) s ∧
  s.gpr .rdi = p.B ∧ word s.mem p.B (8 * sG) = off p.dp p.k ∧
  word s.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧ p.mv = true ∧ Buffers p rb s

def cutVal (p : GkP) : Reg → BitVec 64
  | .rdi => p.B | .r8 => BitVec.ofNat 64 p.ld | .r10 => p.rp | .r11 => p.xp
  | .rcx => 0 | .r14 => BitVec.ofNat 64 p.k | _ => 0

theorem cut_regs (p : GkP) (s : State) (h : MS p s) :
    WP isa (.block cutSetup) s fun t =>
      ∀ r ∈ [.rdi, .r8, .r10, .r11, .rcx, .r14], t.gpr r = cutVal p r := by
  obtain ⟨rb, hi, hn, hmask, _⟩ := h
  refine WP.mono (cutSetup_ok hi hn hmask) fun t ⟨⟨⟨hrp, hxp, _, hld, hcx, hk⟩, _⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans hi.rdi
  · exact hld
  · exact hrp
  · exact hxp
  · exact hcx
  · exact hk

theorem cut_stage (p : GkP) (s : State) (h : MS p s) :
    WP isa (.seq (.block cutSetup) (.seq (.loop (.block cutBody) .ne) (.block cutFinish))) s (Sliced p) := by
  obtain ⟨rb, hi, hn, hmask, hm⟩ := h
  refine WP.seq (WP.mono (cutSetup_ok hi hn hmask) fun u ⟨⟨hr, hmem⟩, k₁⟩ => ?_)
  have hu : Inputs p rb u := hi.keep (by intro a _; rw [hmem]) k₁ (by decide)
  refine WP.seq (WP.mono (cut_inputs hu hr) fun v ⟨hv, hx, hh, h8, _, k₂⟩ => ?_)
  have hnv : word v.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := hi.base.hZ; change 200 ≤ p.Z; omega), hmem]; exact hn
  refine WP.mono (finish_base hv hx hm hnv h8) fun t ⟨hb, hd, hG, hQ, _, hf, k₃⟩ => ?_
  refine ⟨rb, hb, hd, hG, hQ, hm, hx.congrK hf k₃, ?_, ?_, hi.base.xy, hi.base.cut_length, hi.base.ld_lt⟩
  · exact ⟨fun i hi' => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hi.base.x.wr i hi', hi.base.x.sep⟩
  · exact ⟨fun i hi' => by rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hi.base.y.wr i hi', hi.base.y.sep⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
