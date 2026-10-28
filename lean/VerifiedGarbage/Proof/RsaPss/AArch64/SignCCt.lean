module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTBase
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.SignEncode
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTBase
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCorrect
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.SignEncode
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: constant time

`code_ct`: two runs of `signC` from entry states with the same public data
leak the same trace. The check of the modulus' first byte and `emBits` are
on public values (the taint analysis); the calls of `encode` and of the
private-key operation are related by their callees' contracts (`encCallCT`,
`call_ct`), and `encode`'s result, branched on, is public: whether the salt
fits (`AfterEnc.x0`). A failure loads `out` from its slot, public by
correctness (`fail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two Pins two_taint two_post two_map two_ite two_alloc privCallCT
  wp_ldrSp ArgsEq)
open VG.Proof.RsaPss.AArch64 (off EncImpl encCallCT ebV two_step pins_nil emBitsB_ok)

namespace E
variable {D K : Nat} {a s : State} (h : E D K a s)
include h

theorem k : (s.gpr .x3).toNat = (a.gpr .x3).toNat := by rw [h.gpr (r := .x3) (by decide)]

theorem nx : nx s = nx a := congrArg BitVec.toNat h.n0

theorem eb : ebS s = ebS a := by unfold ebS; rw [h.n0, h.gpr (r := .x3) (by decide)]

theorem el : elS s = elS a := by unfold elS; rw [h.eb]

theorem lo : loS s = loS a := by unfold loS; rw [h.el, h.gpr (r := .x3) (by decide)]

theorem argv : argv s = argv a := by
  unfold Sgn.argv
  rw [h.gpr (r := .x6) (by decide), h.gpr (r := .x7) (by decide), h.2.args 0 (by decide), h.2.args 1 (by decide),
    h.2.args 2 (by decide), h.2.args 3 (by decide), h.2.args 4 (by decide), h.2.args 5 (by decide),
    h.2.args 6 (by decide), h.2.args 7 (by decide), h.2.args 12 (by decide), h.scr]

end E

/-- `encode`'s result: 1 exactly when the salt fits. -/
theorem AfterEnc.x0 {G : Spec.Mgf1.Hash} {K : Nat} {s : State} {eb el lo : Nat} {t : State}
    (h : AfterEnc G K s eb el lo t) :
    (t.gpr .x0).setWidth 32 =
      if G.len + (stackArg s 10).toNat + 2 ≤ Spec.RsaPss.emLength eb then (1 : BitVec 32) else 0 := by
  have hi := RsaPss.encode_isSome G (mHash := Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
    (salt := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) (eb := eb)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hi
  have hr := h.res
  revert hr hi
  cases Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) eb with
  | none =>
    intro hi hr
    have hc : ¬ G.len + (stackArg s 10).toNat + 2 ≤ Spec.RsaPss.emLength eb := fun hc => by simp [hc] at hi
    rw [hr, ite_eq_right hc]
  | some e =>
    intro hi hr
    have hc : G.len + (stackArg s 10).toNat + 2 ≤ Spec.RsaPss.emLength eb := by simpa using hi.symm
    rw [hr.1, ite_eq_left hc]

/-! ## A failed check -/

/-- Zeros to `out`: its address is loaded from its slot, the caller's. -/
theorem fail_ct {D K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E D K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
    RelCT isa (Two Φ) signFail (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => ?_
  rotate_left
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    exact WP.mono (fail_ok e.1 m h23) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]
  unfold signFail
  refine RelCT.seq_block_append (M := isa) (l₁ := [ld .x14 sOut]) ?_
  refine two_step (Ψ := fun a t => t.sp = fb a ∧ t.gpr .x14 = a.gpr .x0 ∧ t.gpr .x23 = a.gpr .x3)
    (two_taint [] (fun a s₁ s₂ h₁ h₂ => ?_) (by taint_decide)) (fun a u h => ?_)
    (two_taint [.x14, .x23] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.1, h₂.1], fun r hr => ?_⟩) (by taint_decide))
  · obtain ⟨_, e₁, m₁, _⟩ := hΦ a s₁ h₁
    obtain ⟨_, e₂, m₂, _⟩ := hΦ a s₂ h₂
    exact ⟨by rw [m₁.sp, m₂.sp, e₁.fb, e₂.fb], fun _ h => absurd h List.not_mem_nil⟩
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    unfold ld
    refine wp_ldrSp (by decide) (by
      rw [m.sp, m.rd, m.wr]
      exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide)))) fun u' o x =>
      wp_nil ⟨by rw [o.sp, m.sp, e.fb], ?_, by rw [o.get .x23, h23, e.gpr (by decide)]⟩
    rw [x, m.sp]
    exact (m.fr.rs (.x0, sOut) (by simp [regSlots])).trans (e.gpr (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

/-! ## The private-key operation -/

theorem call_ct (c : PrivChecked) {D K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, E D K a s ∧ AtCall K s em t) (.call c.name c.code) fun _ _ => True := by
  refine privCallCT c fun t₁ t₂ ⟨a, ⟨s₁, em₁, h₁, c₁⟩, ⟨s₂, em₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  refine ⟨privOk_of c h₁.1 hcK c₁, privOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.scr, h₂.scr]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rw [c₁.args i hi, c₂.args i hi, h₁.argv, h₂.argv]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_wrS c₁.mem h₁.1.kn h₁.1.ns (by have := h₁.1.wn; omega),
      bytes_wrS c₂.mem h₂.1.kn h₂.1.ns (by have := h₂.1.wn; omega), h₁.2.bn, h₂.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_wrS c₁.mem h₁.1.ke h₁.1.es (by have := h₁.1.we; omega),
      bytes_wrS c₂.mem h₂.1.ke h₂.1.es (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

section
variable {G : Spec.Mgf1.Hash} (e : EncImpl G) (c : PrivChecked) {K : Nat} (heK : e.stack ≤ K) (hcK : c.stack ≤ K)

include heK in
/-- Two calls of `encode` from runs with the same public data. -/
theorem enc_ct :
    RelCT isa (Two fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧ AtEnc K s (ebS s) (elS s) (loS s) t)
      (.call e.name e.code)
      (Two fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧ AfterEnc G K s (ebS s) (elS s) (loS s) t) := by
  refine two_post (encCallCT e fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁⟩, ⟨s₂, h₂, z₂, j₂⟩⟩ => ?_)
    fun a t ⟨s, h, z, j⟩ => ?_
  · obtain ⟨b₁, b₂, l₁, -⟩ := eb_bounds h₁.1 z₁
    obtain ⟨c₁, c₂, l₂, -⟩ := eb_bounds h₂.1 z₂
    refine ⟨encOk_of h₁.1 heK j₁ (by omega) rfl b₁ b₂, encOk_of h₂.1 heK j₂ (by omega) rfl c₁ c₂,
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [j₁.x0, j₂.x0, h₁.scr, h₂.scr, h₁.lo, h₂.lo]
    · rw [j₁.x1, j₂.x1, h₁.el, h₂.el]
    · rw [j₁.x2, j₂.x2, h₁.2.args 8 (by decide), h₂.2.args 8 (by decide)]
    · rw [j₁.x3, j₂.x3, h₁.2.args 9 (by decide), h₂.2.args 9 (by decide)]
    · rw [j₁.x4, j₂.x4, h₁.2.args 10 (by decide), h₂.2.args 10 (by decide)]
    · rw [j₁.x5, j₂.x5, h₁.eb, h₂.eb]
    · rw [j₁.x6, j₂.x6, h₁.scr, h₂.scr]
    · rw [j₁.x7, j₂.x7, h₁.2.args 12 (by decide), h₂.2.args 12 (by decide)]
  · obtain ⟨b₁, b₂, l, -⟩ := eb_bounds h.1 z
    exact WP.mono (encCall_ok e h.1 heK j (by omega) rfl b₁ b₂) fun t' h' => ⟨s, h, z, h'⟩

include heK hcK in
theorem code_ct : RelCT isa (Two (E G.len K)) (signC e.name e.code c.name c.code) fun _ _ => True := by
  unfold signC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signCBody seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := At G.len K AtChk)
    (two_taint [.x2] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp],
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
    (fail_ct fun a u ⟨⟨s, h, j⟩, _⟩ => ⟨s, h, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, E G.len K a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧ AtEnc K s (ebS s) (elS s) (loS s) t)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁⟩, _⟩ ⟨⟨s₂, h₂, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.n0, h₂.n0]
    · exact (j₁.x20.trans h₁.scr).trans (j₂.x20.trans h₂.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.gpr (by decide), h₂.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono (args_ok h.1 h0 j) fun t ht => ⟨s, h, h0, ht⟩
  refine RelCT.seq (enc_ct e heK) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_zero_w, eval_zero_w, j₁.x0, j₂.x0, h₁.eb, h₂.eb, h₁.2.args 10 (by decide), h₂.2.args 10 (by decide)])
    (fail_ct fun a u ⟨⟨s, h, _, j⟩, _⟩ => ⟨s, h, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E G.len K a s ∧ AtCall K s em t)
    (two_taint [] (fun a t₁ t₂ ⟨⟨s₁, h₁, _, j₁⟩, _⟩ ⟨⟨s₂, h₂, _, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨⟨s, h, z, j⟩, hb⟩ => ?_) ?_
  · obtain ⟨_, _, hm⟩ := main_of h.1 z j hb
    exact WP.mono (privArgs_ok h.1 hm) fun t' h' => ⟨s, _, h, h'⟩
  exact two_post (call_ct c hcK) fun a t ⟨s, em, h, hA⟩ =>
    WP.mono (call_ok c h.1 hcK hA) fun t' h' => by rw [h'.sp, h.fb]

end

end VG.Proof.RsaPss.AArch64.Sgn
