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
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
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
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPCall
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignPCall
import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: constant time

`codeP_ct`: `code_ct`'s runs, from entry states that also agree on `pre`'s
address and length and on the modulus' values in it (`PubX`): a failure
restores `x19` and `x20` from their slots (`failP_ct`), and the call of
`vg_rsa_private_checked_precomputed` is related by its contract
(`callP_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked Two Pins two_taint two_post two_map two_ite two_alloc two_mono
  privPCallCT wp_ldrSp ArgsEq)
open VG.Proof.RsaPss.AArch64 (off ebV two_step pins_nil emBitsB_ok byIdx_ct cmpIdx Tabs)

/-- The public data of `pre`: its address and length, and the modulus'
values in it. -/
def PubX (a s : State) : Prop :=
  stackArg s 16 = stackArg a 16 ∧ stackArg s 17 = stackArg a 17 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 16) (Spec.Rsa.precomputedWords (a.gpr .x3).toNat)

/-- An entry state with the anchor's public data, `pre`'s included. -/
def EP (tsH tsG : List FnTable) (K : Nat) (a s : State) : Prop := E tsH tsG K a s ∧ (PreXS K s ∧ PubX a s)

/-- `ES`, with `pre`. -/
abbrev ESP (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  ES f g tsH tsG K i T Hs Gs a s ∧ (PreXS K s ∧ PubX a s)

/-- Zeros to `out`, and `x19` and `x20` restored. -/
theorem failP_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
    RelCT isa (Two Φ) signFailP (Two fun a t => t.sp = fb a) := by
  refine two_post ?_ fun a u h => ?_
  · unfold signFailP
    exact RelCT.seq (fail_ct hΦ) (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
      ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  · obtain ⟨s, e, m, h23⟩ := hΦ a u h
    exact WP.mono (failP_ok e.1 m h23) fun t ⟨m', _⟩ => by rw [m'.sp, e.fb]

/-- The modulus' values in `pre`, at the call. -/
theorem preWords_eq {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hx : PreXS K s)
    {em : List Byte} (ha : AtCallP K s em t) :
    Spec.Rsa.wordsAt t.mem (stackArg t 12) (Spec.Rsa.precomputedWords (t.gpr .x3).toNat) =
      Spec.Rsa.wordsAt s.mem (stackArg s 16) (Spec.Rsa.precomputedWords (s.gpr .x3).toNat) := by
  rw [ha.pre, ha.x3]
  have hle : Spec.Rsa.precomputedWords (s.gpr .x3).toNat ≤ (stackArg s 17).toNat := by
    rw [hx.prl]; simp only [Spec.Rsa.privatePrecomputedWords]; omega_using []
  have hw := prl_le hp hx
  have sub : Region.Sub ⟨stackArg s 16, 8 * Spec.Rsa.precomputedWords (s.gpr .x3).toNat⟩ (prR s) :=
    Region.sub_prefix (by omega_using [hle])
  exact VG.Proof.Rsa.wordsAt_frame ha.mem (by omega_using [hle, hw])
    (wrS_disj (hx.kpr.sub_right sub) (hx.spr.sub_right sub).symm)

theorem callP_ct (c : PrivPChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, EP tsH tsG K a s ∧ AtCallP K s em t) (.call c.name c.code)
      fun _ _ => True := by
  refine privPCallCT c fun t₁ t₂ ⟨a, ⟨s₁, em₁, h₁, c₁⟩, ⟨s₂, em₂, h₂, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.1.gpr hr).trans (h₂.1.gpr hr).symm
  refine ⟨privPOk_ofP c h₁.1.1 h₁.2.1 hcK c₁, privPOk_ofP c h₂.1.1 h₂.2.1 hcK c₂,
    ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.1.fb, h₂.1.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, e .x0 (by decide)]
    · rw [c₁.x1, c₂.x1, e .x3 (by decide)]
    · rw [c₁.x2, c₂.x2, e .x2 (by decide)]
    · rw [c₁.x3, c₂.x3, e .x3 (by decide)]
    · rw [c₁.x4, c₂.x4, e .x4 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x5 (by decide)]
    · rw [c₁.x6, c₂.x6, h₁.1.scr, h₂.1.scr]
    · rw [c₁.x7, c₂.x7, e .x3 (by decide)]
  · rcases (by omega_using [hi] : i < 12 ∨ i = 12 ∨ i = 13) with h | rfl | rfl
    · rw [c₁.args i h, c₂.args i h, h₁.1.argv, h₂.1.argv]
    · rw [c₁.pre, c₂.pre, h₁.2.2.1, h₂.2.2.1]
    · rw [c₁.prl, c₂.prl, h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, bytes_wrS c₁.mem h₁.1.1.kn h₁.1.1.ns (by have := h₁.1.1.wn; omega_using []),
      bytes_wrS c₂.mem h₂.1.1.kn h₂.1.1.ns (by have := h₂.1.1.wn; omega_using []), h₁.1.2.bn, h₂.1.2.bn]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_wrS c₁.mem h₁.1.1.ke h₁.1.1.es (by have := h₁.1.1.we; omega_using []),
      bytes_wrS c₂.mem h₂.1.1.ke h₂.1.1.es (by have := h₂.1.1.we; omega_using []), h₁.1.2.be, h₂.1.2.be]
  · rw [preWords_eq h₁.1.1 h₁.2.1 c₁, preWords_eq h₂.1.1 h₂.2.1 c₂, h₁.2.2.2.2, h₂.2.2.2.2]

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivPChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Enc.encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Enc.encK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Enc.encK T Hs Gs).pre (Enc.encK T Hs Gs).pub (encode f (ofIdx i) g))

include h624 hcK hv hct in
theorem codeP_ct : RelCT isa (Two (ESP f g tsH tsG K i T Hs Gs)) (signCP f g c.name c.code) fun _ _ => True := by
  unfold signCP
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signCBodyP seqs seqs seqs
  rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (signPrologue.tail ++ n0 .x2)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 14 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.1.2.sp, h₂.1.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x2, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.1.fb, h₂.1.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.1.gpr (by decide), h₂.1.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.1.2.args 14 (by decide), h₂.1.1.2.args 14 (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.1.n0, h₂.1.1.n0])
    (failP_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.1.n0, h₂.1.1.n0]
    · exact (j₁.x20.trans h₁.1.1.scr).trans (j₂.x20.trans h₂.1.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.1.gpr (by decide), h₂.1.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (args_ok h.1.1.1 h0 j) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- `encode`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ESP f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
    (fun a t ⟨s, h, z, j, y⟩ => ⟨h.1.2.1.mem, j.x27.trans h.1.2.1.idx, rfl⟩)
    (fun j hj => by unfold idxs at hj; simp at hj; omega_using [hj]) (fun j hj => ?_) (fun j hj => ?_)) ?_
  · unfold idxs at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact two_taint [.x27] (fun a t₁ t₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun r hr => by
        rw [List.mem_singleton.mp hr, j₁.x27, j₂.x27, h₁.1.2.1.idx, h₂.1.2.1.idx]⟩) (by taint_decide)
  · by_cases hij : i = j
    · subst hij
      refine two_post ((enc_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ ⟨⟨s, h, z, j, y⟩, _⟩ =>
        ⟨s, h.1, z, j, y⟩) fun _ _ _ => trivial) fun a t ⟨⟨s, h, z, j, y⟩, _⟩ => ?_
      obtain ⟨b₁, b₂, l, -⟩ := eb_bounds h.1.1.1 z
      exact WP.mono (encCall_ok h.1.1.1 h624 h.1.2.1 j y (by omega_using [l]) rfl b₁ b₂) fun t' h' => ⟨s, h, z, h'⟩
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  -- `encode`'s result.
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_zero_w, eval_zero_w, j₁.x0 (h₁.1.2.1.hl.trans h₁.1.2.1.hD), j₂.x0 (h₂.1.2.1.hl.trans h₂.1.2.1.hD),
        h₁.1.1.eb, h₂.1.1.eb, h₁.1.1.2.args 11 (by decide), h₂.1.1.2.args 11 (by decide)])
    (failP_ct fun a u ⟨⟨s, h, _, j⟩, _⟩ => ⟨s, h.1.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, EP tsH tsG K a s ∧ AtCallP K s em t)
    (two_taint [] (fun a t₁ t₂ ⟨⟨s₁, h₁, _, j₁⟩, _⟩ ⟨⟨s₂, h₂, _, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.1.fb, h₂.1.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨⟨s, h, z, j⟩, hb⟩ => ?_) ?_
  · obtain ⟨_, _, hm⟩ := main_of h.1.1.1 z j hb
    exact WP.mono (privArgsP_ok h.1.1.1 h.2.1 hm) fun t' h' => ⟨s, _, ⟨h.1.1, h.2⟩, h'⟩
  exact two_post (callP_ct c hcK) fun a t ⟨s, em, h, hA⟩ =>
    WP.mono (callP_ok c h.1.1 h.2.1 hcK hA) fun t' h' => by rw [h'.sp, h.1.fb]


end

end VG.Proof.RsaPss.AArch64.Sgn
