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
import Mathlib.Tactic.ToDual

/-! # FFDH on x86-64: sampling does not branch on the random bytes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

def IV (p : GkP) (s : State) : Prop := I p s ∧ p.mv = true

private def BS (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s ∧
  word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧ s.gpr .rax = p.bc.setWidth 64 ∧ p.mv = true

private def MS (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s ∧
  word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n ∧ word s.mem p.B (8 * sMsk) = p.msk ∧ p.mv = true

/-- The result is ready for the shared private-key setup and scalar-range check. -/
def Sliced (p : GkP) (s : State) : Prop := ∃ rb, CheckPrivate.Base p.kp (p.xb rb) s ∧
  s.gpr .rdi = p.B ∧ word s.mem p.B (8 * sG) = off p.dp p.k ∧
  word s.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧ p.mv = true ∧ Buffers p rb s

private theorem bound_bs (p : GkP) (s : State) (h : IV p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) s (BS p) := by
  obtain ⟨⟨rb, hi⟩, hm⟩ := h
  exact WP.mono (scan_inputs hi) fun t ⟨ht, hn, hax, _⟩ => ⟨rb, ht, hn, hax, hm⟩

private theorem bs_ms (p : GkP) (s : State) (h : BS p s) :
    WP isa (.block smear) s (MS p) := by
  obtain ⟨rb, hi, hn, hax, hm⟩ := h
  exact WP.mono (smear_inputs hi hn hax) fun t ⟨ht, hn, hmask, _⟩ => ⟨rb, ht, hn, hmask, hm⟩

private def cutVal (p : GkP) : Reg → BitVec 64
  | .rdi => p.B | .r8 => BitVec.ofNat 64 p.ld | .r10 => p.rp | .r11 => p.xp
  | .rcx => 0 | .r14 => BitVec.ofNat 64 p.k | _ => 0

private theorem cut_regs (p : GkP) (s : State) (h : MS p s) :
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

private theorem cut_stage (p : GkP) (s : State) (h : MS p s) :
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

/-- All loop bounds and conditional moves use only the public domain width. -/
theorem sample_ct : RelCT isa (Two IV) (seqs scalar) (Two Sliced) := by
  unfold scalar
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) (by simp [bound]) (by simp)
    (RelCT.seq (R := Two BS)
      (two_post (two_map id (fun _ _ h => h.1) bound_ct) bound_bs) ?_)
  change RelCT isa (Two BS) (.seq (.block smear)
    (.seq (.block cutSetup) (.seq (.loop (.block cutBody) .ne) (.block cutFinish)))) (Two Sliced)
  refine RelCT.seq (R := Two MS)
    (two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else p.bc.setWidth 64)
      fun p s h r hr => by
        obtain ⟨_, hi, _, hax, _⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hi.rdi
        · exact hax) (by taint_decide) bs_ms) ?_
  exact pin_ct [.rdi] [.rdi, .r8, .r10, .r11, .rcx, .r14] cutVal
    (pins_rdiB GkP.B fun _ _ h => by obtain ⟨_, hi, _⟩ := h; exact hi.rdi)
    (by taint_decide) cut_regs (by taint_decide) cut_stage

end VG.Proof.Ffdh.X86_64.GenerateKey
