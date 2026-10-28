module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTBase
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTBase
meta import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: constant time

`code_ct`: two runs of `verifyC` from entry states with the same public data
leak the same trace. The check of the modulus' first byte, `emBits` and the
arguments are on public values (the taint analysis); the calls of the
precomputed public operation and of `checkEncoding` are related by their
callees' contracts (`call_ct`, `chk_ct`); the leading byte is only ANDed
into the result.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero wp_and wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two two_taint two_post two_ite two_alloc pdCallCT)
open VG.Proof.RsaPss.AArch64 (ChkImpl chkCallCT)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0)

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem eb : ebS s = ebS a := by unfold ebS; rw [h.n0, h.gpr (r := .x1) (by decide)]

theorem el : elS s = elS a := by unfold elS; rw [h.eb]

theorem lo : loS s = loS a := by unfold loS; rw [h.el, h.gpr (r := .x1) (by decide)]

theorem cw : cwV s = cwV a := by unfold cwV; rw [h.gpr (r := .x1) (by decide)]

end E

/-- A buffer of the caller, apart from the stack. -/
theorem bytes_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {len : Nat}
    (hk : (kR K s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm) hl (List.mem_range.mp hi)

/-- Words of the caller, apart from the stack. -/
theorem words_f {K : Nat} {s : State} {m : Mem} (hf : Frame [⟨fb s, frameBytes⟩] s.mem m) {p : Addr} {n : Nat}
    (hk : (kR K s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [List.mem_singleton.mp hr]; exact (hk.sub_left (frame_sub0 K s)).symm

/-! ## The precomputed public operation -/

theorem call_ct (c : PdChecked) {D K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s, E D K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtCall s (ebS s) (elS s) (loS s) t)
      (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, _, c₁⟩, ⟨s₂, h₂, _, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  have g : ∀ i, 0 < i → i < 5 → stackArg s₁ i = stackArg s₂ i := fun i h h' =>
    (h₁.2.args i h h').trans (h₂.2.args i h h').symm
  refine ⟨pdOk_of c h₁.1 hcK c₁, pdOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, h₁.scr, h₂.scr]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, g 3 (by decide) (by decide)]
    · rw [c₁.x3, c₂.x3, g 4 (by decide) (by decide)]
    · rw [c₁.x4, c₂.x4, e .x2 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x3 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x5 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x1 (by decide)]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.scr, h₂.scr]
    · rw [c₁.a1, c₂.a1, g 2 (by decide) (by decide)]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, words_f c₁.mem h₁.1.kP h₁.1.wP, words_f c₂.mem h₂.1.kP h₂.1.wP, h₁.2.w, h₂.2.w]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_f c₁.mem h₁.1.ke (by have := h₁.1.we; omega),
      bytes_f c₂.mem h₂.1.ke (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

/-! ## `checkEncoding` -/

theorem chk_ct {G : Spec.Mgf1.Hash} (e : ChkImpl G) {K : Nat} (heK : e.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtChkC K s t)
      (.call e.name e.code) (Two fun a t => ∃ s, E G.len K a s ∧ AfterChk G s t) := by
  refine two_post (chkCallCT e fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁⟩, ⟨s₂, h₂, z₂, j₂⟩⟩ => ?_)
    fun a t ⟨s, h, z, j⟩ => WP.mono (chk_ok e h.1 heK z j) fun t' h' => ⟨s, h, h'⟩
  refine ⟨chkOk_of h₁.1 heK z₁ j₁, chkOk_of h₂.1 heK z₂ j₂,
    ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [j₁.x0, j₂.x0, h₁.gpr (by decide), h₂.gpr (by decide)]
  · rw [j₁.x1, j₂.x1, h₁.scr, h₂.scr, h₁.lo, h₂.lo]
  · rw [j₁.x2, j₂.x2, h₁.el, h₂.el]
  · rw [j₁.x3, j₂.x3, h₁.eb, h₂.eb]
  · rw [j₁.x4, j₂.x4, h₁.gpr (by decide), h₂.gpr (by decide)]
  · rw [j₁.x5, j₂.x5, h₁.any, h₂.any]
  · rw [j₁.x6, j₂.x6, h₁.scr, h₂.scr, h₁.cw, h₂.cw]
  · rw [j₁.x7, j₂.x7, h₁.2.args 2 (by decide) (by decide), h₂.2.args 2 (by decide) (by decide), h₁.cw, h₂.cw]

section
variable {G : Spec.Mgf1.Hash} (c : PdChecked) (e : ChkImpl G) {K : Nat} (hcK : c.stack ≤ K) (heK : e.stack ≤ K)

include hcK heK in
theorem code_ct : RelCT isa (Two (E G.len K)) (verifyC e.name e.code c.name c.code) fun _ _ => True := by
  unfold verifyC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold verifyCBody seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := At G.len K AtChk)
    (two_taint [.x0] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp],
      fun r hr => by
        rw [List.mem_singleton.mp hr, e₁, e₂]
        simp only [allocated]
        rw [h₁.gpr (by decide), h₂.gpr (by decide)]⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated]))
      fun t ht => ⟨s, h, ht⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ => by rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.n0, h₂.n0])
    (vfail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩⟩) ?_
  unfold seqs seqs seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtCall s (ebS s) (elS s) (loS s) t)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.n0, h₂.n0]
    · exact (j₁.x20.trans h₁.scr).trans (j₂.x20.trans h₂.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.gpr (by decide), h₂.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono (pubArgsC_ok h.1 j h0) fun t ht => ⟨s, h, h0, ht⟩
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AfterCall K s (ebS s) (elS s) (loS s) t)
    (call_ct c hcK) fun a t ⟨s, h, z, j⟩ => WP.mono (call_ok c h.1 hcK j) fun t' h' => ⟨s, h, z, h'⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtChkC K s t)
    (two_taint [.x20, .x23, .x24, .x25, .x26] (fun a u₁ u₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨s, h, z, j⟩ => WP.mono (chkArgs_ok h.1 z j) fun t ht => ⟨s, h, z, ht⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (j₁.x20.trans h₁.scr).trans (j₂.x20.trans h₂.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.gpr (by decide), h₂.gpr (by decide)]
    · rw [j₁.x24, j₂.x24, h₁.eb, h₂.eb]
    · rw [j₁.x25, j₂.x25, h₁.el, h₂.el]
    · rw [j₁.x26, j₂.x26, h₁.lo, h₂.lo]
  refine RelCT.seq (chk_ct e heK) ?_
  exact two_post (two_taint (Φ := fun a t => ∃ s, E G.len K a s ∧ AfterChk G s t) []
    (fun a t₁ t₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨s, h, j⟩ => wp_and fun t' o _ => wp_nil (by rw [o.sp, j.sp, h.fb])

end

end VG.Proof.RsaPss.AArch64.Vfy
