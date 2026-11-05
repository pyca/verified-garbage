module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTBase
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.RsaPss.AArch64.ByIdx
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
callees' contracts (`call_ct`, `chk_ct`), the latter chosen by the table's
index, the same in both runs (`byIdx_ct`), whose tables name the same
functions (`CSel`); the leading byte is only ANDed into the result.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero wp_and wp_nil)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two two_taint two_post two_ite two_alloc two_mono pdCallCT wp_ldrSp)
open VG.Proof.RsaPss.AArch64 (byIdx_ct Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (kR fb frame_sub0 stackArgAddr_fb wp_and callEntry_gpr eval_zero_w)

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
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

theorem call_ct (c : PdChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s, E tsH tsG K a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtCall s (ebS s) (elS s) (loS s) t)
      (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, _, c₁⟩, ⟨s₂, h₂, _, c₂⟩⟩ => ?_
  have e : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := fun r hr => (h₁.gpr hr).trans (h₂.gpr hr).symm
  have g : ∀ i < 8, i ≠ 1 → stackArg s₁ i = stackArg s₂ i := fun i h h' =>
    (h₁.2.args i h h').trans (h₂.2.args i h h').symm
  refine ⟨pdOk_of c h₁.1 hcK c₁, pdOk_of c h₂.1 hcK c₂, ⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, h₁.fb, h₂.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.x0, c₂.x0, h₁.scr, h₂.scr]
    · rw [c₁.x1, c₂.x1, e .x1 (by decide)]
    · rw [c₁.x2, c₂.x2, g 4 (by decide) (by decide)]
    · rw [c₁.x3, c₂.x3, g 5 (by decide) (by decide)]
    · rw [c₁.x4, c₂.x4, e .x2 (by decide)]
    · rw [c₁.x5, c₂.x5, e .x3 (by decide)]
    · rw [c₁.x6, c₂.x6, e .x6 (by decide)]
    · rw [c₁.x7, c₂.x7, e .x1 (by decide)]
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [c₁.a0, c₂.a0, h₁.scr, h₂.scr]
    · rw [c₁.a1, c₂.a1, g 3 (by decide) (by decide)]
  · rw [c₁.x2, c₁.x3, c₂.x2, c₂.x3, words_f c₁.mem h₁.1.kP h₁.1.wP, words_f c₂.mem h₂.1.kP h₂.1.wP, h₁.2.w, h₂.2.w]
  · rw [c₁.x4, c₁.x5, c₂.x4, c₂.x5, bytes_f c₁.mem h₁.1.ke (by have := h₁.1.we; omega),
      bytes_f c₂.mem h₂.1.ke (by have := h₂.1.we; omega), h₁.2.be, h₂.2.be]

/-- An entry state with the anchor's public data, whose tables name the
functions `T` (and hash functions `Hs`, `Gs`) at the anchor's addresses,
for the index `i`. -/
abbrev ES (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  E tsH tsG K a s ∧ CSel f g tsH tsG s i T Hs Gs ∧ ∀ n ∈ T.names, s.syms n = a.syms n

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PdChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Chk.chkK T Hs Gs).pre s' → ∃ t s'', Exec isa (checkEncoding f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Chk.chkK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Chk.chkK T Hs Gs).pre (Chk.chkK T Hs Gs).pub (checkEncoding f (ofIdx i) g))

/-! ## `checkEncoding` -/

include h624 hv hct in
/-- Two calls of `checkEncoding` from runs with the same public data. -/
theorem chk_ct :
    RelCT isa (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧ AtChkC K s t ∧
        t.syms = s.syms)
      (.call (chkName i) (checkEncoding f (ofIdx i) g))
      (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t) := by
  refine two_post (RelCT.callEx (k := Chk.chkK T Hs Gs) hv hct
    fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁, y₁⟩, ⟨s₂, h₂, z₂, j₂, y₂⟩⟩ => ?_) fun a t ⟨s, h, z, j, y⟩ => ?_
  · obtain ⟨r₁, w₁⟩ := chkCovers h₁.1.1 h₁.2.1 z₁ j₁
    obtain ⟨r₂, w₂⟩ := chkCovers h₂.1.1 h₂.2.1 z₂ j₂
    refine ⟨_, _, _, _, chkPre_of h₁.1.1 h624 h₁.2.1 z₁ j₁ y₁, chkPre_of h₂.1.1 h624 h₂.2.1 z₂ j₂ y₂,
      ⟨⟨?_, fun r hr => ?_, ?_, fun j hj => ?_⟩, fun n hn => ?_⟩,
      Covers.append_left r₁ (Covers.right w₁), w₁, Covers.append_left r₂ (Covers.right w₂), w₂⟩
    · show t₂.sp = t₁.sp
      rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb]
    · simp only [State.withRegions_gpr]
      have hr' : r ∈ argRegs := by
        simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h | h <;> simp [h]
      rw [callEntry_gpr hr', callEntry_gpr hr']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [j₁.x0, j₂.x0, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
      · rw [j₁.x1, j₂.x1, h₁.1.scr, h₂.1.scr, h₁.1.lo, h₂.1.lo]
      · rw [j₁.x2, j₂.x2, h₁.1.el, h₂.1.el]
      · rw [j₁.x3, j₂.x3, h₁.1.eb, h₂.1.eb]
      · rw [j₁.x4, j₂.x4, h₁.1.2.args 0 (by decide) (by decide), h₂.1.2.args 0 (by decide) (by decide)]
      · rw [j₁.x6, j₂.x6, h₁.1.scr, h₂.1.scr, h₁.1.cw, h₂.1.cw]
      · rw [j₁.x7, j₂.x7, h₁.1.2.args 3 (by decide) (by decide), h₂.1.2.args 3 (by decide) (by decide),
          h₁.1.cw, h₂.1.cw]
    · simp only [State.withRegions_gpr]
      rw [callEntry_gpr (by decide), callEntry_gpr (by decide), j₁.x5, j₂.x5, h₁.1.any, h₂.1.any]
    · show stackArg t₂ j = stackArg t₁ j
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [j₁.a0, j₂.a0, h₁.1.2.args 6 (by decide) (by decide), h₂.1.2.args 6 (by decide) (by decide)]
      · rw [j₁.a1, j₂.a1, h₁.1.2.args 7 (by decide) (by decide), h₂.1.2.args 7 (by decide) (by decide)]
    · show t₂.syms n = t₁.syms n
      rw [y₁, y₂, h₁.2.2 n hn, h₂.2.2 n hn]
  · exact WP.mono (chkCall_ok h.1.1 h624 h.2.1 z j y) fun t' h' => ⟨s, h, h'⟩

/-- The stack's address `x10` holds the table's address. -/
theorem argT_ok {s : State} (hp : PreV tsH tsG K s) :
    WP isa (.block [arg .x10 6]) (allocated frameBytes s) fun u => u.gpr .x10 = stackArg s 6 ∧
      u.syms = s.syms ∧ u.sp = fb s ∧ u.gpr .x0 = s.gpr .x0 := by
  refine WP.of_syms ?_
  unfold arg
  refine wp_ldrSp (by decide) (by
    simp only [allocated]
    rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
    exact arg_in hp (Covers.left (Covers.refl _)) (j := 6) (by decide)) fun u o e => wp_nil fun sy =>
      ⟨?_, sy, by rw [o.sp]; rfl, by rw [o.get .x0]; rfl⟩
  rw [e]
  simp only [allocated]
  rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
  rfl

include h624 hcK hv hct in
theorem code_ct : RelCT isa (Two (ES f g tsH tsG K i T Hs Gs)) (verifyC f g c.name c.code) fun _ _ => True := by
  unfold verifyC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold verifyCBody seqs seqs seqs
  rw [show verifyPrologue ++ n0 .x0 = [arg .x10 6] ++ (verifyPrologue.tail ++ n0 .x0) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (verifyPrologue.tail ++ n0 .x0)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 6 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x0 = s.gpr .x0)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.2.sp, h₂.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1 (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show verifyPrologue ++ n0 .x0 = [arg .x10 6] ++ (verifyPrologue.tail ++ n0 .x0) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x0, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.fb, h₂.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.2.args 6 (by decide) (by decide), h₂.1.2.args 6 (by decide) (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0])
    (vfail_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩⟩) ?_
  unfold seqs seqs seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AtCall s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0]
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (pubArgsC_ok h.1.1 j h0) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- The public operation.
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AfterCall K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    ((call_ct c hcK).mono (fun _ _ => two_mono fun _ _ ⟨s, h, z, j, _⟩ => ⟨s, h.1, z, j⟩) fun _ _ h => h)
    fun a t ⟨s, h, z, j, y⟩ => WP.mono_syms (call_ok c h.1.1 hcK j) fun t' h' sy => ⟨s, h, z, h', sy.trans y⟩) ?_
  -- `checkEncoding`'s arguments.
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x0) ≠ 0 ∧
      AtChkC K s t ∧ t.syms = s.syms)
    (two_taint [.x20, .x23, .x24, .x25, .x26] (fun a u₁ u₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨s, h, z, j, y⟩ => WP.mono_syms (chkArgs_ok h.1.1 z j) fun t ht sy => ⟨s, h, z, ht, sy.trans y⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
    · rw [j₁.x24, j₂.x24, h₁.1.eb, h₂.1.eb]
    · rw [j₁.x25, j₂.x25, h₁.1.el, h₂.1.el]
    · rw [j₁.x26, j₂.x26, h₁.1.lo, h₂.1.lo]
  -- `checkEncoding`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t)
    (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
    (fun a t ⟨s, h, z, j, y⟩ => ⟨h.2.1.mem, j.x27.trans h.2.1.idx, rfl⟩)
    (fun j hj => by unfold idxs at hj; simp at hj; omega) (fun j hj => ?_) (fun j hj => ?_)) ?_
  · unfold idxs at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact two_taint [.x27] (fun a t₁ t₂ ⟨s₁, h₁, _, j₁, _⟩ ⟨s₂, h₂, _, j₂, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => by
        rw [List.mem_singleton.mp hr, j₁.x27, j₂.x27, h₁.2.1.idx, h₂.2.1.idx]⟩) (by taint_decide)
  · by_cases hij : i = j
    · subst hij
      exact (chk_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  exact two_post (two_taint (Φ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AfterChkC Hs Gs K s t) []
    (fun a t₁ t₂ ⟨s₁, h₁, j₁⟩ ⟨s₂, h₂, j₂⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨s, h, j⟩ => wp_and fun t' o _ => wp_nil (by rw [o.sp, j.sp, h.1.fb])

end

end VG.Proof.RsaPss.AArch64.Vfy
