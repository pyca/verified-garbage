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

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: constant time

`code_ct`: two runs of `signC` from entry states with the same public data
leak the same trace. The check of the modulus' first byte and `emBits` are
on public values (the taint analysis); the choice of `encode` by the table's
index is the same in both runs (`byIdx_ct`), whose tables name the same
functions (`ESel`); the calls of `encode` and of the private-key operation
are related by their callees' contracts (`enc_ct`, `call_ct`), and
`encode`'s result, branched on, is public: whether the salt fits
(`AfterEnc.x0`). A failure loads `out` from its slot, public by
correctness (`fail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two Pins two_taint two_post two_map two_ite two_alloc two_mono privCallCT
  wp_ldrSp ArgsEq)
open VG.Proof.RsaPss.AArch64 (off ebV two_step pins_nil emBitsB_ok byIdx_ct cmpIdx Tabs)

namespace E
variable {tsH tsG : List FnTable} {K : Nat} {a s : State} (h : E tsH tsG K a s)
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
    h.2.args 6 (by decide), h.2.args 7 (by decide), h.2.args 13 (by decide), h.scr]

end E

/-- `encode`'s result: 1 exactly when the salt fits. -/
theorem AfterEnc.x0 {Hs Gs : Spec.Mgf1.Hash} {K : Nat} {s : State} {eb el lo : Nat} {t : State}
    (h : AfterEnc Hs Gs K s eb el lo t) (hl : Hs.len = (stackArg s 9).toNat) :
    (t.gpr .x0).setWidth 32 =
      if Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb then (1 : BitVec 32) else 0 := by
  have hi := RsaPss.encode_isSome₂ Hs Gs (mHash := Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
    (salt := Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) (eb := eb)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hl])
  rw [VG.Proof.RsaPkcs1Sig.bytesAt_length] at hi
  have hr := h.res
  revert hr hi
  cases Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) eb with
  | none =>
    intro hi hr
    have hc : ¬ Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb := fun hc => by simp [hc] at hi
    rw [hr, ite_eq_right hc]
  | some e =>
    intro hi hr
    have hc : Hs.len + (stackArg s 11).toNat + 2 ≤ Spec.RsaPss.emLength eb := by simpa using hi.symm
    rw [hr.1, ite_eq_left hc]

/-! ## A failed check -/

/-- Zeros to `out`: its address is loaded from its slot, the caller's. -/
theorem fail_ct {tsH tsG : List FnTable} {K : Nat} {Φ : State → State → Prop}
    (hΦ : ∀ a u, Φ a u → ∃ s, E tsH tsG K a s ∧ Mid s u ∧ u.gpr .x23 = s.gpr .x3) :
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

theorem call_ct (c : PrivChecked) {tsH tsG : List FnTable} {K : Nat} (hcK : c.stack ≤ K) :
    RelCT isa (Two fun a t => ∃ s em, E tsH tsG K a s ∧ AtCall K s em t) (.call c.name c.code)
      fun _ _ => True := by
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

/-- An entry state with the anchor's public data, whose tables name the
functions `T` (and hash functions `Hs`, `Gs`) at the anchor's addresses,
for the index `i`. -/
abbrev ES (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (K i : Nat) (T : Tabs)
    (Hs Gs : Spec.Mgf1.Hash) (a s : State) : Prop :=
  E tsH tsG K a s ∧ ESel f g tsH tsG s i T Hs Gs ∧ ∀ n ∈ T.names, s.syms n = a.syms n

theorem wp_and {c : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c s P) (h₂ : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨t₁, s₁, e₁, p⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q⟩ := h₂
  obtain ⟨rfl, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, p, q⟩

theorem callEntry_gpr {t : State} {r : Reg} (hr : r ∈ argRegs) : t.callEntry.gpr r = t.gpr r := by
  simp only [State.callEntry]
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} (c : PrivChecked) {K : Nat}
  (h624 : 624 ≤ K) (hcK : c.stack ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
  (hv : ∀ s', (Enc.encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Enc.encK T Hs Gs).post s' s'')
  (hct : ConstantTime isa (Enc.encK T Hs Gs).pre (Enc.encK T Hs Gs).pub (encode f (ofIdx i) g))

include h624 hv hct in
/-- Two calls of `encode` from runs with the same public data. -/
theorem enc_ct :
    RelCT isa (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
        AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
      (.call (encName i) (encode f (ofIdx i) g))
      (Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
        AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) := by
  refine two_post (RelCT.callEx (k := Enc.encK T Hs Gs) hv hct
    fun t₁ t₂ ⟨a, ⟨s₁, h₁, z₁, j₁, y₁⟩, ⟨s₂, h₂, z₂, j₂, y₂⟩⟩ => ?_) fun a t ⟨s, h, z, j, y⟩ => ?_
  · obtain ⟨b₁, b₂, l₁, -⟩ := eb_bounds h₁.1.1 z₁
    obtain ⟨c₁, c₂, l₂, -⟩ := eb_bounds h₂.1.1 z₂
    obtain ⟨r₁, w₁⟩ := enc_covers h₁.1.1 h₁.2.1 j₁ (by omega)
    obtain ⟨r₂, w₂⟩ := enc_covers h₂.1.1 h₂.2.1 j₂ (by omega)
    refine ⟨_, _, _, _, encPre_of h₁.1.1 h624 h₁.2.1 j₁ y₁ (by omega) rfl b₁ b₂,
      encPre_of h₂.1.1 h624 h₂.2.1 j₂ y₂ (by omega) rfl c₁ c₂, ⟨⟨?_, fun r hr => ?_, fun j hj => ?_⟩, fun n hn => ?_⟩,
      Covers.append_left r₁ (Covers.right w₁), w₁, Covers.append_left r₂ (Covers.right w₂), w₂⟩
    · show t₂.sp = t₁.sp
      rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb]
    · simp only [State.withRegions_gpr]
      rw [callEntry_gpr hr, callEntry_gpr hr]
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [j₁.x0, j₂.x0, h₁.1.scr, h₂.1.scr, h₁.1.lo, h₂.1.lo]
      · rw [j₁.x1, j₂.x1, h₁.1.el, h₂.1.el]
      · rw [j₁.x2, j₂.x2, h₁.1.2.args 8 (by decide), h₂.1.2.args 8 (by decide)]
      · rw [j₁.x3, j₂.x3, h₁.1.2.args 10 (by decide), h₂.1.2.args 10 (by decide)]
      · rw [j₁.x4, j₂.x4, h₁.1.2.args 11 (by decide), h₂.1.2.args 11 (by decide)]
      · rw [j₁.x5, j₂.x5, h₁.1.eb, h₂.1.eb]
      · rw [j₁.x6, j₂.x6, h₁.1.scr, h₂.1.scr]
      · rw [j₁.x7, j₂.x7, h₁.1.2.args 13 (by decide), h₂.1.2.args 13 (by decide)]
    · show stackArg t₂ j = stackArg t₁ j
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rw [j₁.a0, j₂.a0, h₁.1.2.args 14 (by decide), h₂.1.2.args 14 (by decide)]
      · rw [j₁.a1, j₂.a1, h₁.1.2.args 15 (by decide), h₂.1.2.args 15 (by decide)]
    · show t₂.syms n = t₁.syms n
      rw [y₁, y₂, h₁.2.2 n hn, h₂.2.2 n hn]
  · obtain ⟨b₁, b₂, l, -⟩ := eb_bounds h.1.1 z
    exact WP.mono (encCall_ok h.1.1 h624 h.2.1 j y (by omega) rfl b₁ b₂) fun t' h' => ⟨s, h, z, h'⟩

/-- The stack's address `x10` holds the table's address. -/
theorem argT_ok {s : State} (hp : PreS tsH tsG K s) :
    WP isa (.block [arg .x10 14]) (allocated frameBytes s) fun u => u.gpr .x10 = stackArg s 14 ∧
      u.syms = s.syms ∧ u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2 := by
  refine WP.of_syms ?_
  unfold arg
  refine wp_ldrSp (by decide) (by
    simp only [allocated]
    rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
    exact arg_in hp (Covers.left (Covers.refl _)) (j := 14) (by decide)) fun u o e => wp_nil fun sy =>
      ⟨?_, sy, by rw [o.sp]; rfl, by rw [o.get .x2]; rfl⟩
  rw [e]
  simp only [allocated]
  rw [show s.sp - BitVec.ofNat 64 frameBytes = fb s from rfl, ← stackArgAddr_fb]
  rfl

include h624 hcK hv hct in
theorem code_ct : RelCT isa (Two (ES f g tsH tsG K i T Hs Gs)) (signC f g c.name c.code) fun _ _ => True := by
  unfold signC
  refine two_alloc (R := fun _ _ => True) ?_
  unfold signCBody seqs seqs seqs
  rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl]
  refine RelCT.seq_block_append ?_
  -- The table's address.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧
      WP isa (.block (signPrologue.tail ++ n0 .x2)) u (AtChk s) ∧ u.gpr .x10 = stackArg s 14 ∧ u.syms = s.syms ∧
      u.sp = fb s ∧ u.gpr .x2 = s.gpr .x2)
    (two_taint [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.1.2.sp, h₂.1.2.sp],
      fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hw := prologue_ok (u := allocated frameBytes s) h.1.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])
    rw [show signPrologue ++ n0 .x2 = [arg .x10 14] ++ (signPrologue.tail ++ n0 .x2) from rfl,
      WP.block_append_iff] at hw
    exact WP.mono (wp_and hw (argT_ok h.1.1)) fun u ⟨w, x, y, p, q⟩ => ⟨s, h, w, x, y, p, q⟩
  -- The prologue.
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ AtChk s u ∧ u.syms = s.syms)
    (two_taint [.x2, .x10] (fun _ u₁ u₂ ⟨s₁, h₁, _, x₁, _, p₁, q₁⟩ ⟨s₂, h₂, _, x₂, _, p₂, q₂⟩ =>
      ⟨by rw [p₁, p₂, h₁.1.fb, h₂.1.fb], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [q₁, q₂, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
        · rw [x₁, x₂, h₁.1.2.args 14 (by decide), h₂.1.2.args 14 (by decide)]⟩)
      (by taint_decide))
    fun a u ⟨s, h, w, x, y, _⟩ => WP.mono_syms w fun t ht sy => ⟨s, h, ht, sy.trans y⟩) ?_
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, j₁, _⟩ ⟨s₂, h₂, j₂, _⟩ => by
      rw [eval_zero, eval_zero, j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0])
    (fail_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  unfold seqs seqs
  refine RelCT.seq (two_post
    (Ψ := fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AtEnc K s (ebS s) (elS s) (loS s) t ∧ t.syms = s.syms)
    (two_taint [.x10, .x20, .x23] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun r hr => ?_⟩) (by taint_decide))
    fun a u ⟨⟨s, h, j, y⟩, hb⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [j₁.x10, j₂.x10, h₁.1.n0, h₂.1.n0]
    · exact (j₁.x20.trans h₁.1.scr).trans (j₂.x20.trans h₂.1.scr).symm
    · rw [j₁.x23, j₂.x23, h₁.1.gpr (by decide), h₂.1.gpr (by decide)]
  · have h0 : s.mem (s.gpr .x2) ≠ 0 := fun h0 => by
      rw [eval_zero, j.x10, h0] at hb
      exact absurd hb (by decide)
    exact WP.mono_syms (args_ok h.1.1 h0 j) fun t ht sy => ⟨s, h, h0, ht, sy.trans y⟩
  -- `encode`, for the index of the table.
  refine RelCT.seq (byIdx_ct (Q := Two fun a t => ∃ s, ES f g tsH tsG K i T Hs Gs a s ∧ s.mem (s.gpr .x2) ≠ 0 ∧
      AfterEnc Hs Gs K s (ebS s) (elS s) (loS s) t) (fun _ => i) (fun a t t' ⟨s, h, z, j, y⟩ o sy => ⟨s, h, z, j.only9 o, sy.trans y⟩)
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
      exact (enc_ct h624 hv hct).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hij h₁.2
  -- `encode`'s result.
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_zero_w, eval_zero_w, j₁.x0 (h₁.2.1.hl.trans h₁.2.1.hD), j₂.x0 (h₂.2.1.hl.trans h₂.2.1.hD),
        h₁.1.eb, h₂.1.eb, h₁.1.2.args 11 (by decide), h₂.1.2.args 11 (by decide)])
    (fail_ct fun a u ⟨⟨s, h, _, j⟩, _⟩ => ⟨s, h.1, ⟨j.sp, j.rd, j.wr, j.v, j.fr⟩, j.x23⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E tsH tsG K a s ∧ AtCall K s em t)
    (two_taint [] (fun a t₁ t₂ ⟨⟨s₁, h₁, _, j₁⟩, _⟩ ⟨⟨s₂, h₂, _, j₂⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.1.fb, h₂.1.fb], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
    fun a t ⟨⟨s, h, z, j⟩, hb⟩ => ?_) ?_
  · obtain ⟨_, _, hm⟩ := main_of h.1.1 z j hb
    exact WP.mono (privArgs_ok h.1.1 hm) fun t' h' => ⟨s, _, h.1, h'⟩
  exact two_post (call_ct c hcK) fun a t ⟨s, em, h, hA⟩ =>
    WP.mono (call_ok c h.1 hcK hA) fun t' h' => by rw [h'.sp, h.fb]

end

end VG.Proof.RsaPss.AArch64.Sgn
