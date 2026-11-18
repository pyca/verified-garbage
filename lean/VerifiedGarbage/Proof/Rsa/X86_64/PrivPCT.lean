module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Rsa.Scratch
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
meta import VerifiedGarbage.Proof.Rsa.PrivCheck
meta import VerifiedGarbage.Proof.Rsa.PreWords
meta import VerifiedGarbage.Proof.Rsa.Scratch
meta import Mathlib.Data.Int.ModEq
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! ### `Rsa.X86_64.PrivPCorrect`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: correctness

`PrivChecked.codeP`, from a state `chkContractP` allows, writes what
`vg_rsa_private_checked` writes (`codeP_correct`): its frame and its checks
are `PrivChecked.code`'s, given the key's precomputed values beyond
`chkContract`'s regions (`PreF`'s `X`); it calls the CRT given `pre`
(`CrtImpl.codeP`), and `vg_rsa_public_precomputed_checked` with `pre`
itself as `n`'s values (its first `2 ⌈n_len / 8⌉` words are
`publicPrecompute`'s, `privatePrecompute_public`), and so has `r₃ = 1`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64

variable {X : List Region}

/-! ## The precondition -/

/-- The regions of `chkContractP` beyond `chkContract`'s: stack arguments 14
and 15, and `pre`. -/
abbrev xP (s : State) : List Region :=
  [⟨stackArgAddr s 14, 16⟩, ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩]

/-- `pre`'s region. -/
abbrev preRP (s : State) : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩

/-- What `chkContractP.pre` adds to `chkContract.pre`, by name. -/
structure PFacts (s : State) : Prop where
  sp3 : (s.gpr .rsp).toNat + 136 ≤ 2 ^ 64
  dOa2 : (outR s).Disjoint ⟨stackArgAddr s 14, 16⟩
  dOp : (outR s).Disjoint (preRP s)
  dSa2 : (scrR s).Disjoint ⟨stackArgAddr s 14, 16⟩
  dSp : (scrR s).Disjoint (preRP s)
  dKa2 : (stkR s).Disjoint ⟨stackArgAddr s 14, 16⟩
  dKp : (stkR s).Disjoint (preRP s)
  dAa2 : (⟨stackArgAddr s 0, 112⟩ : Region).Disjoint ⟨stackArgAddr s 14, 16⟩
  wPr : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  hpl : (stackArg s 15).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 3).toNat
    (stackArg s 5).toNat
  hpp : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 14) (stackArg s 15).toNat)

theorem preFP_of {s : State} (h : chkContractP.pre s) : PreF (xP s) s ∧ PFacts s := by
  obtain ⟨h0, hdrop, sp3, dOa2, dOp, dSa2, dSp, dKa2, dKp, dAa2, wPr, hpl, hpp⟩ := h
  obtain hp0 := preF_of h0
  refine ⟨{ hp0 with hrd := ?_ }, ⟨sp3, dOa2, dOp, dSa2, dSp, dKa2, dKp, dAa2, wPr, hpl, hpp⟩⟩
  rw [← List.take_append_drop 9 s.rd, hdrop]
  exact (congrArg (· ++ xP s) hp0.hrd).trans (by rw [List.append_nil]; rfl)

/-! ## The CRT's arguments -/

/-- A stack argument up to 15, past stores to the frame. -/
theorem argP_outside {s : State} (hp : PreF X s) (hf : PFacts s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m)
    {j : Nat} (hj : j < 16) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := hp.sp1
  have := hf.sp3
  obtain hF : (fb s).toNat + frameBytes + 8 + 128 ≤ 2 ^ 64 := by
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytes at *; omega_arith
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

theorem stackArgAddr_15 (s : State) : stackArgAddr s 15 = stackArgAddr s 14 + BitVec.ofNat 64 8 := by
  unfold stackArgAddr; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Stack arguments 14 and 15 are readable. -/
theorem arg2_in {s : State} (hp : PreF (xP s) s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : 14 ≤ j) (hj' : j < 16) : InRegions (rd ++ wr) (stackArgAddr s j) 8 := by
  refine ⟨⟨stackArgAddr s 14, 16⟩, List.mem_append_left _ (by
    rw [hrd, hp.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)), ?_⟩
  rcases (show j = 14 ∨ j = 15 by omega_using [hj, hj']) with rfl | rfl
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · rw [stackArgAddr_15]
    simp only [Region.Contains]
    rw [BitVec.add_comm (stackArgAddr s 14), BitVec.add_sub_cancel]; decide

/-- The frame's push, and the CRT's arguments with `pre`: `crtArgs_ok`, and
`pre` and `pre_len` at `rsp + 96` and `rsp + 104`. -/
theorem crtArgsP_ok {s : State} (hp : PreF (xP s) s) (hf : PFacts s) :
    WP isa (.block crtArgsP) (allocState frameBytes s) fun t => Env s t ∧
      Outside (fb s) 0 frameBytes s.mem t.mem ∧ (∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) ∧
      word t.mem (fb s) 96 = stackArg s 14 ∧ word t.mem (fb s) 104 = stackArg s 15 ∧
      t.gpr .rdi = off (fb s) oM ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx := by
  obtain hF := fb_toNat hp
  unfold crtArgsP
  rw [WP.block_append_iff]
  refine WP.mono (crtArgs_ok hp) fun t₁ ⟨he, ho, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_
  obtain hs := he.scr hp
  obtain h14 := argP_outside hp hf ho (j := 14) (by decide)
  obtain h15 := argP_outside hp hf ho (j := 15) (by decide)
  obtain ho1 : Outside (fb s) 0 frameBytes s.mem (t₁.mem.writeW (off (fb s) 96) (stackArg s 14)) := fun x hx =>
    (writeW_outside _ _ _ (by unfold frameBytes at *; omega_using []) x (by unfold frameBytes at hx; omega_using [hx])).trans (ho x hx)
  obtain h15' := argP_outside hp hf ho1 (j := 15) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem =
      (t₁.mem.writeW (off (fb s) 96) (stackArg s 14)).writeW (off (fb s) 104) (stackArg s 15)) (by
    xrun [arg, ea_sp, he.rsp,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 14) = stackArgAddr s 14 from (stackArgAddr_fb s 14).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 15) = stackArgAddr s 15 from (stackArgAddr_fb s 15).symm,
      arg2_in hp he.rd t₁.wr (j := 14) (by decide) (by decide),
      arg2_in hp he.rd t₁.wr (j := 15) (by decide) (by decide), h14, h15, h15',
      hs.st (d := 96) (by decide), hs.st (d := 104) (by decide)]) rfl) fun t ⟨hm, k⟩ => ?_
  obtain hw : ∀ d, d + 8 ≤ 96 ∨ 112 ≤ d → d + 8 ≤ frameBytes → word t.mem (fb s) d = word t₁.mem (fb s) d :=
    fun d hd hd' => by
      rw [hm, word_wo _ _ _ (by omega_using [hd]) (by decide) (by unfold frameBytes at hd'; omega_using [hd']),
        word_wo _ _ _ (by omega_using [hd]) (by decide) (by unfold frameBytes at hd'; omega_using [hd'])]
  obtain ho' : Outside (fb s) 0 frameBytes s.mem t.mem := by
    rw [hm]
    intro x hx
    rw [writeW_outside _ _ _ (by unfold frameBytes at *; omega_using []) x (by unfold frameBytes at hx; omega_using [hx]),
      writeW_outside _ _ _ (by unfold frameBytes at *; omega_using []) x (by unfold frameBytes at hx; omega_using [hx])]
    exact ho x hx
  refine ⟨⟨(k.gpr (by decide)).trans he.rsp, k.2.1.trans he.rd, k.2.2.trans he.wr, frame_of_outside ho',
      (hw _ (by decide) (by decide)).trans he.sOut, (hw _ (by decide) (by decide)).trans he.sN,
      (hw _ (by decide) (by decide)).trans he.sK, (hw _ (by decide) (by decide)).trans he.sE,
      (hw _ (by decide) (by decide)).trans he.sEl⟩, ho', fun i hi => (hw _ (by omega_using [hi]) (by unfold frameBytes; omega_using [hi])).trans
      (hargs i hi), ?_, ?_, (k.gpr (by decide)).trans hdi, (k.gpr (by decide)).trans hsi,
      (k.gpr (by decide)).trans hdx, (k.gpr (by decide)).trans hcx, (k.gpr (by decide)).trans h8,
      (k.gpr (by decide)).trans h9⟩
  · rw [hm, word_wo _ _ _ (by decide) (by decide) (by decide)]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _

/-- `pre`'s words, in memory changed only where the function may write. -/
theorem words_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len * 8⟩) (ho : (outR s).Disjoint ⟨p, len * 8⟩) (hs : (scrR s).Disjoint ⟨p, len * 8⟩)
    (hl : p.toNat + len * 8 ≤ 2 ^ 64) : Spec.Rsa.wordsAt m p len = Spec.Rsa.wordsAt s.mem p len := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  refine hf.readW (r := ⟨p, len * 8⟩) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-! ## The CRT -/

/-- What the CRT given `pre` reads. -/
def crtRdP (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 0, (s.gpr .rcx).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, preRP s, ⟨fb s, 112⟩]

/-- Memory at the CRT's entry: changed only where the function may write. -/
theorem entry_frame {s t : State} (he : Env s t) : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
  frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)

theorem crtP_pre {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t)
    (hargs : ∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2))
    (h96 : word t.mem (fb s) 96 = stackArg s 14) (h104 : word t.mem (fb s) 104 = stackArg s 15)
    (hdi : t.gpr .rdi = off (fb s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    crtContractP.pre (t.callEntry.withRegions (crtRdP s) (crtWr s)) := by
  obtain hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_arith)).trans (hargs i hi)
  obtain hE12 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg s 14 :=
    (stackArg_entry he.rsp _ _ (by omega_arith)).trans h96
  obtain hE13 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg s 15 :=
    (stackArg_entry he.rsp _ _ (by omega_arith)).trans h104
  obtain hfE := entry_frame he
  have hil := hp.hil
  obtain b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  have hpp := hf.hpp
  rw [← b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_arith),
    ← b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega_arith),
    ← b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega_arith),
    ← words_of_frame hfE hf.dKp hf.dOp hf.dSp hf.wPr] at hpp
  simp only [crtContractP, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), hE 4 (by decide), hE 5 (by decide), hE 6 (by decide), hE 7 (by decide),
    hE 8 (by decide), hE 9 (by decide), hE 10 (by decide), hE 11 (by decide), hE12, hE13, Nat.reduceAdd, fb_sub8]
  have ⟨hK1, hK2, _⟩ := kb_toNat hp
  have e1 : stackBytes = 3256 := rfl
  have e2 : oM = 168 := rfl
  have e3 : frameBytes = 3240 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  obtain sM : Region.Sub ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  obtain sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 112) (by decide); simpa only [off, BitVec.add_zero] using this
  obtain sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := by
    have := ret_sub s; rwa [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl] at this
  obtain dMA : (⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 112⟩ :=
    Offset.disjoint_base _ (by decide) (by omega_arith)
  obtain hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_kb s
  obtain dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  obtain dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  obtain wM : (off (fb s) oM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega_arith)]; unfold oM; omega_arith), hfb, ← off,
      toNat_off (by omega_arith)]; unfold oM; omega_arith
  obtain dKi : (stkR s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ := by rw [← hil]; exact hp.dKi
  obtain dis : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ := by
    rw [← hil]; exact hp.dis
  obtain wI : (stackArg s 0).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hil]; exact hp.wI
  refine ⟨by omega_arith, rfl, rfl, hp.dKn.sub_left sM, dKi.sub_left sM, hp.dKp.sub_left sM, hp.dKq.sub_left sM,
    hp.dKdp.sub_left sM, hp.dKdq.sub_left sM, hp.dKqi.sub_left sM, hf.dKp.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.dns, dis, hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, hf.dSp.symm, (hp.dKs.sub_left sA).symm, dRM,
    hp.dKn.sub_left sR, dKi.sub_left sR,
    hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR, hp.dKqi.sub_left sR,
    hf.dKp.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.wN, wI, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, hf.wPr,
    ⟨hk1, hk2⟩, trivial, trivial,
    hp.pl1, hp.pl2, hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, hp.hsl, hf.hpl, hpp⟩

/-- The CRT's buffers, `pre` among them, are apart from the return address
of its calls. -/
theorem crtP_clear {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t) :
    Clear (hole ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rsp))
      (t.callEntry.withRegions (crtRdP s) (crtWr s)) := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, he.rsp, fb_sub8]
  obtain sH := hole_sub s
  have hil := hp.hil
  have hk2 := hp.k2
  have e2 : oM = 168 := rfl
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, crtRdP, crtWr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hp.dKn.sub_left sH).symm
  · exact ((show (stkR s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ by rw [← hil]; exact hp.dKi).sub_left sH).symm
  · exact (hp.dKp.sub_left sH).symm
  · exact (hp.dKq.sub_left sH).symm
  · exact (hp.dKdp.sub_left sH).symm
  · exact (hp.dKdq.sub_left sH).symm
  · exact (hp.dKqi.sub_left sH).symm
  · exact (hf.dKp.sub_left sH).symm
  · rw [fb_kb]; exact frame_hole hp (d := 0) (by decide)
  · rw [fb_kb, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact frame_hole hp (by unfold frameBytes; omega_arith)
  · exact (hp.dKs.sub_left sH).symm

theorem crtP_covers {s t : State} (hp : PreF (xP s) s) (he : Env s t) :
    Covers (crtRdP s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk2 := hp.k2
  have hil := hp.hil
  have e2 : oM = 168 := rfl
  have e3 : frameBytes = 3240 := rfl
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  obtain hscr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr]; simp
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  obtain cw : Covers (crtWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oM, rfl, by dsimp only; omega_arith⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega_arith⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  · have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
    simp only [crtRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _,
        by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 0, (stackArg s 1).toNat⟩, hrd ⟨stackArg s 0, (stackArg s 1).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 2, (stackArg s 3).toNat⟩, hrd ⟨stackArg s 2, (stackArg s 3).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 4, (stackArg s 5).toNat⟩, hrd ⟨stackArg s 4, (stackArg s 5).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 6, (stackArg s 7).toNat⟩, hrd ⟨stackArg s 6, (stackArg s 7).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 8, (stackArg s 9).toNat⟩, hrd ⟨stackArg s 8, (stackArg s 9).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨⟨stackArg s 10, (stackArg s 11).toNat⟩, hrd ⟨stackArg s 10, (stackArg s 11).toNat⟩ (by rw [hp.hrd]; simp), 0,
        z _, by dsimp only; omega_arith⟩
    · exact ⟨preRP s, hrd (preRP s) (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega_arith⟩

/-- The call of the CRT given `pre`: `M` holds its result, which it returns. -/
theorem crtP_call (v : CrtImpl) {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t)
    (hargs : ∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2))
    (h96 : word t.mem (fb s) 96 = stackArg s 14) (h104 : word t.mem (fb s) 104 = stackArg s 15)
    (hdi : t.gpr .rdi = off (fb s) oM)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = stackArg s 0) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.nameP v.codeP) t fun t' => Env s t' ∧
      Spec.Rsa.written t'.mem (off (fb s) oM) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 5).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 3).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := crtP_covers hp he
  refine WP.call_mx (k := crtContractP.clear) v.okP v.nospP (by rw [v.depthP]; decide)
    ⟨crtP_pre hp hf he hargs h96 h104 hdi hsi hdx hcx h8 h9, crtP_clear hp hf he⟩ hc hw ?_
  intro s' hrd hwr hcs hf' _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depthP, he.rsp] at hf'
  simp only [Nat.reduceAdd, Nat.reduceMul] at hf'
  obtain hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_arith)).trans (hargs i hi)
  obtain hfE := entry_frame he
  have hk2 := hp.k2
  have hil := hp.hil
  obtain b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  simp only [Contract.clear, crtContractP, crtContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
    hE 6 (by decide), hE 8 (by decide), Nat.reduceAdd, hm₂, hg₂ .rax (by decide)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_arith),
    b (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega_arith),
    b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega_arith),
    b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega_arith),
    b (by rw [← hp.hdpl]; exact hp.dKdp) (by rw [← hp.hdpl]; exact hp.dOdp)
      (by rw [← hp.hdpl]; exact hp.ddps.symm) (by have := hp.wDp; have := hp.hdpl; omega_arith),
    b (by rw [← hp.hdql]; exact hp.dKdq) (by rw [← hp.hdql]; exact hp.dOdq)
      (by rw [← hp.hdql]; exact hp.ddqs.symm) (by have := hp.wDq; have := hp.hdql; omega_arith),
    b (by rw [← hp.hqil]; exact hp.dKqi) (by rw [← hp.hqil]; exact hp.dOqi)
      (by rw [← hp.hqil]; exact hp.dqis.symm) (by have := hp.wQi; have := hp.hqil; omega_arith)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf' fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oM frameBytes; omega_arith))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (ret2_sub s)
  · rw [slot_keep hf' (slot_apart hp (by decide))]; exact he.sOut
  · rw [slot_keep hf' (slot_apart hp (by decide))]; exact he.sN
  · rw [slot_keep hf' (slot_apart hp (by decide))]; exact he.sK
  · rw [slot_keep hf' (slot_apart hp (by decide))]; exact he.sE
  · rw [slot_keep hf' (slot_apart hp (by decide))]; exact he.sEl

/-! ## The public operation, given `pre` -/

/-- `pre`'s first `2 ⌈k / 8⌉` words, `n`'s values. -/
def preRp (s : State) : Region := ⟨stackArg s 14, Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8⟩

theorem preRp_sub {s : State} (hf : PFacts s) : Region.Sub (preRp s) (preRP s) :=
  Region.sub_prefix (by
    rw [hf.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using [])

/-- A stack argument up to 15 past a store to the frame. -/
theorem arg_woP {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 16) :
    (m.writeW (off (fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (fb s) v (by unfold frameBytes at *; omega_using [hd]) (by unfold frameBytes at *; omega_using [hd])
    (by unfold frameBytes; omega_using [hj])

/-- Stack argument 14, `pre`, from the frame. -/
theorem Env.arg14 {s t : State} (he : Env s t) (hf : PFacts s) :
    t.mem.readW (stackArgAddr s 14) 64 = stackArg s 14 := by
  refine he.mem.readW (r := ⟨stackArgAddr s 14, 16⟩) ?_ (fun r hr => ?_) (by decide)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hf.dKa2.symm
    · exact hf.dOa2.symm
    · exact hf.dSa2.symm

/-- `r₁` kept, `r₃ := 1`, and the arguments of
`vg_rsa_public_precomputed_checked`, with `pre` as `n`'s values. -/
theorem pdArgsP_ok {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t) :
    WP isa (.block pdArgsP) t fun t' => Env s t' ∧
      t'.mem = ((((((t.mem.writeW (off (fb s) oR1) (t.gpr .rax)).writeW (off (fb s) oR3) (1 : BitVec 64)).writeW (fb s)
        (off (fb s) oM)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW (off (fb s) 16) (stackArg s 12)).writeW
        (off (fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = stackArg s 14 ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 := by
  obtain hs := he.scr hp
  have hk2 := hp.k2
  obtain h0 : InRegions t.wr (fb s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = ((((((t.mem.writeW (off (fb s) oR1) (t.gpr .rax)).writeW (off (fb s) oR3) (1 : BitVec 64)).writeW (fb s)
        (off (fb s) oM)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW (off (fb s) 16) (stackArg s 12)).writeW
        (off (fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = stackArg s 14 ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) (by
    xrun [pdArgsP, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, arg,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fb s 12).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fb s 13).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 14) = stackArgAddr s 14 from (stackArgAddr_fb s 14).symm,
      hs.st (d := oR1) (by decide), hs.st (d := oR3) (by decide), h0, hs.st (d := 8) (by decide),
      hs.st (d := 16) (by decide), hs.st (d := 24) (by decide), hs.ld (d := oK) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      arg_in hp he (show 12 < 14 by decide), arg_in hp he (show 13 < 14 by decide),
      arg2_in hp he.rd t.wr (j := 14) (by decide) (by decide),
      sx_ofNat (show oM < 2 ^ 31 by decide), word_wo, arg_wo, arg_woP, word_wo0, arg_wo0,
      he.sK, he.sOut, he.sE, he.sEl, he.arg hp (show 12 < 14 by decide), he.arg hp (show 13 < 14 by decide),
      he.arg14 hf, preWords_val (show (s.gpr .rcx).toNat ≤ 1024 by omega_arith),
      show BitVec.setWidth 64 (1 : BitVec 32) = (1 : BitVec 64) from rfl]) rfl)
    fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · have h0' : (⟨fb s, frameBytes⟩ : Region).Contains (fb s) 8 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    obtain fr : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨fb s, frameBytes⟩ : Region).Contains (off (fb s) d) 8 :=
      fun hd => Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)
    rw [hm]
    refine frame_call he.mem (rs := [⟨fb s, frameBytes⟩]) ?_ fun r hr => ?_
    · exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fr (d := oR1) (by decide))).writeW
        (List.mem_singleton_self _) _ (fr (d := oR3) (by decide))).writeW
        (List.mem_singleton_self _) _ h0').writeW (List.mem_singleton_self _) _ (fr (d := 8) (by decide))).writeW
        (List.mem_singleton_self _) _ (fr (d := 16) (by decide))).writeW (List.mem_singleton_self _) _
        (fr (d := 24) (by decide)))
    · rw [List.mem_singleton.mp hr]
      have := frame_sub s (d := 0) (n := frameBytes) (by decide)
      exact .inl (by simpa only [off, BitVec.add_zero] using this)
  all_goals rw [hm]; simp (disch := decide) only [Bignum.word, word_wo, word_wo0]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-- What the call reads, given `pre`: `n`'s values in it, `e`, `M` and its
stack arguments. -/
def pdRdP (s : State) : List Region :=
  [preRp s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, mR s, ⟨fb s, 32⟩]

/-- `pre`'s words, kept by a call's return address. -/
theorem entry_wordsP {s t : State} (hsp : t.gpr .rsp = fb s) (hf : PFacts s) :
    Spec.Rsa.wordsAt t.callEntry.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
      Spec.Rsa.wordsAt t.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
  have hl := hf.wPr
  have hpl := hf.hpl
  obtain sP := preRp_sub hf
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  refine (callEntry_frame hsp).readW (r := preRp s) (Offset.contains_base _ (by first | omega_arith | (simp only [preRp]; omega_arith))
    (by unfold Spec.Rsa.privatePrecomputedWords at hpl; omega_arith)) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  exact ((hf.dKp.sub_left (below_sub s)).symm.sub_left sP)

theorem pdP_pre {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = off (fb s) oM) (hw1 : word t.mem (fb s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fb s) 16 = stackArg s 12) (hw3 : word t.mem (fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 14)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (pdRdP s) (pdWr s)) := by
  obtain hpw := preWords_le hp
  obtain hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry he.rsp _ _ (by omega_arith)
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hcxN, stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, _, _⟩ := kb_toNat hp
  have e3 : oM = 168 := rfl
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_kb s
  obtain sP := preRp_sub hf
  obtain sM := mR_sub hp
  obtain sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  obtain rb : below (fb s) 8 = ⟨kb s, 8⟩ := by simp only [below]; rw [← fb_sub8]; rfl
  obtain sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := by rw [← rb]; exact ret_sub s
  obtain dRP : (⟨kb s, 8⟩ : Region).Disjoint (preRp s) := ((hf.dKp.sub_left sR).symm.sub_left sP).symm
  obtain dOP : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (preRp s) := by
    rw [← hsi']; exact (hf.dOp.symm.sub_left sP).symm
  obtain wPp : (stackArg s 14).toNat + Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 := by
    have := hf.wPr; have := hf.hpl; unfold Spec.Rsa.privatePrecomputedWords at *; omega_arith
  obtain dRM : (⟨kb s, 8⟩ : Region).Disjoint (mR s) := by
    rw [← rb]; exact ret_disjoint s (by unfold oM frameBytes; omega_arith)
  obtain dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  obtain dOut : ∀ {r : Region}, Region.Sub r (stkR s) →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r := fun h => by
    rw [← hsi']; exact (hp.dKo.sub_left h).symm
  obtain wFr : ∀ {d n : Nat}, d + n ≤ frameBytes → (off (fb s) d).toNat + n ≤ 2 ^ 64 := fun {d n} h => by
    unfold frameBytes at h hK1
    rw [fb_off, ← off, toNat_off (by omega_arith)]; omega_arith
  refine ⟨by omega_arith, rfl, rfl, dOP, ?_, dOut sM, ?_, dOut sA, hf.dSp.symm.sub_left sP, hp.des,
    hp.dKs.sub_left sM, (hp.dKs.sub_left sA).symm, ?_, dRP, hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA,
    ?_, wPp, hp.wE, wFr (by unfold oM frameBytes; omega_arith), hp.wS,
    ⟨hp.k1, hp.k2⟩, trivial, trivial, hp.L1, hp.L2,
    VG.Proof.Rsa.publicScratch_le ⟨hp.k1, hp.k2⟩ hp.hsl⟩
  · rw [← hsi']; exact hp.dOe
  · rw [← hsi']; exact hp.dOs
  · rw [← hsi']; exact (hp.dKo.sub_left sR)
  · rw [← hsi']; exact hp.wO

/-- The regions `vg_rsa_public_precomputed_checked` is given. -/
theorem pdP_covers {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t) :
    Covers (pdRdP s) (t.rd ++ t.wr) ∧ Covers (pdWr s) t.wr := by
  obtain hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  obtain cw : Covers (pdWr s) t.wr := Covers.of_mem fun r hr => by
    simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [he.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [← hsi']; simp
    · simp [scrR]
  obtain cr : Covers (pdRdP s) (t.rd ++ t.wr) := Covers.of_sub fun r hr => by
    simp only [pdRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨preRP s, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0, z _, by
        simp only [preRp]; have := hf.hpl; unfold Spec.Rsa.privatePrecomputedWords at this; omega_arith⟩
    · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0, z _,
        by dsimp only; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ hfr, oM, rfl, by simp only [mR]; unfold oM frameBytes; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega_arith⟩
  exact ⟨cr, cw⟩

/-- The call of `vg_rsa_public_precomputed_checked`: `M^e mod n` to `out`,
for whatever modulus `n`'s values in the frame are of. `M` and the slots of
`r₁` and `r₃` are kept. -/
theorem pdP_call (P : PublicImpl) (name : String)
    {s t : State} (hp : PreF (xP s) s) (hq : PFacts s) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = off (fb s) oM) (hw1 : word t.mem (fb s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fb s) 16 = stackArg s 12) (hw3 : word t.mem (fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 14)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call name (P.code)) t fun t' => Env s t' ∧
      (∀ nB : List Byte, nB.length = (s.gpr .rcx).toNat →
        Spec.Rsa.publicPrecompute nB =
          some (Spec.Rsa.wordsAt t.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)) →
        Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat))) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat ∧
      word t'.mem (fb s) oR1 = word t.mem (fb s) oR1 ∧ word t'.mem (fb s) oR3 = word t.mem (fb s) oR3 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain ⟨cr, cw⟩ := pdP_covers hp hq he
  have hv := P.ok
  obtain hpre := pdP_pre hp hq he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9
  obtain hdd : 8 * (P.code).depth + 16 < 2 ^ 64 := by rw [P.depth]; decide
  have hpre' : (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (t.callEntry.withRegions (pdRdP s) (pdWr s)) := hpre
  obtain hcov := Covers.append_left cr cw.right
  refine WP.call_mx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := pdRdP s) (wr := pdWr s)
    hv P.nosp hdd
    hpre' hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [P.depth, he.rsp] at hf
  obtain hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  obtain hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hcxN, hm₂, hg₂ .rax (by decide), stackArg_entry he.rsp _ _ (show 0 < 400 by decide),
    Nat.mul_zero, hw0, entry_bytes he.rsp (show oM + (s.gpr .rcx).toNat ≤ frameBytes by unfold oM frameBytes; omega_arith),
    entry_wordsP he.rsp hq,
    bytes_of_frame hfE hp.dKe hp.dOe (hp.des.symm) (by have := hp.wE; omega_arith)] at hpost
  obtain hapart : ∀ {d n : Nat}, d + n ≤ frameBytes → 32 ≤ d → ∀ r ∈ pdWr s ++ [below (fb s) 8],
      (⟨off (fb s) d, n⟩ : Region).Disjoint r := fun {d n} hdn h32 r hr => by
    simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hsi']; exact (hp.dKo.sub_left (frame_sub s hdn))
    · exact hp.dKs.sub_left (frame_sub s hdn)
    · exact (ret_disjoint s hdn).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, ?_, hcs, hmx⟩
  · simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (by rw [← hsi']; exact sub_refl _))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold oM frameBytes; omega_arith) (by decide) r hr) (by dsimp only; omega_arith)
      (List.mem_range.mp hi)
  · exact slot_keep hf (hapart (by decide) (by decide))
  · exact slot_keep hf (hapart (by decide) (by decide))

/-! ## After the CRT -/

theorem checkP_eq (pdName : String) (pd : Prog isa) :
    seqs (checkP pdName pd) = .seq (.block pdArgsP) (.seq (.call pdName pd) (seqs PrivChecked.tail)) := rfl

/-- Everything after the CRT given `pre`, from any state the frame allows:
as `check_ok`, with `r₃ = 1`. -/
theorem check_okP (P : PublicImpl) (pdName : String)
    {s t : State} (hp : PreF (xP s) s) (hf : PFacts s) (he : Env s t) :
    WP isa (seqs (checkP pdName (P.code))) t fun t' =>
      Env s t' ∧
      t'.gpr .rax = checkResult (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat)
          then Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hk2 := hp.k2
  obtain hpw := preWords_le hp
  obtain csk : ∀ {rs : List Reg} {a b : State}, Keep rs a b → (∀ r ∈ calleeSaved, r ∉ rs) →
      ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun k h r hr => k.gpr (h r hr)
  rw [checkP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (pdArgsP_ok hp hf he) rfl)
    fun t₃ ⟨⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩, k₃⟩ hmx₃ => ?_)
  obtain hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
      [off (fb s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
    rw [hm₃]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
      rfl
    · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
    · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
    · simp (disch := decide) only [word_writeW_self]; rfl
  refine WP.seq (WP.mono (pdP_call P pdName hp hf he₃ (hw (d := 0) (by decide))
    (hw (d := 1) (by decide)) (hw (d := 2) (by decide)) (hw (d := 3) (by decide)) hdi₃ hsi₃ hdx₃ hcx₃ h8₃ h9₃)
    fun t₄ ⟨he₄, hpd, hM₄, hR1₄, hR3₄, hcs₄, hmx₄⟩ => ?_)
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx, .r9, .r8] (tail_ok hp he₄) (by decide +kernel))
    fun t' ⟨⟨hax, hout, hM', he'⟩, k₅⟩ hmx₅ => ⟨he', ?_, ?_, hM',
      fun r hr => by rw [csk k₅ (by decide) r hr, hcs₄ r hr, csk k₃ (by decide) r hr],
      by rw [hmx₅, hmx₄, hmx₃]⟩ <;> clear hM'
  all_goals
    -- The values the tail reads.
    obtain hr1 : word t₄.mem (fb s) oR1 = t.gpr .rax := by
      rw [hR1₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
    obtain hr3 : word t₄.mem (fb s) oR3 = 1 := by
      rw [hR3₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
    obtain hmb : Spec.Rsa.bytesAt t₃.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oM, oR3, oR1]; omega_arith)) only [bytes_wo, bytes_wo0]
    obtain sP := preRp_sub hf
    obtain hpre : Spec.Rsa.wordsAt t₃.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
        Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
      have hl := hf.wPr
      have hpl := hf.hpl
      exact words_of_frame he₃.mem (hf.dKp.symm.sub_left sP).symm (hf.dOp.symm.sub_left sP).symm
        (hf.dSp.symm.sub_left sP).symm (by unfold Spec.Rsa.privatePrecomputedWords at hpl; omega_arith)
    obtain hpub := VG.Proof.Rsa.privatePrecompute_public hf.hpp
    rw [bytesAt_length'] at hpub
    rw [hr1, hr3] at hax hout
    rw [hM₄, hmb] at hout
    simp only [hmb] at hpd
    obtain h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some _ => (1 : BitVec 64).setWidth 32 = 1
        | none => (1 : BitVec 64).setWidth 32 = 0 := by
      rw [hpub]; rfl
    obtain hl := check_logic (r₁ := t.gpr .rax) (r₂ := t₄.gpr .rax) (r₃ := 1)
      (eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (mB := Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat)
      (outB := Spec.Rsa.bytesAt t₄.mem (s.gpr .rdi) (s.gpr .rcx).toNat)
      (xB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) h3 (fun hs => by
        have := hpd _ (bytesAt_length' _ _ _) (by rw [hpre]; exact hpub)
        cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
            (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat) <;>
          simp only [hpo, Spec.Rsa.written] at this ⊢
        · exact this.1
        · exact this)
    first | (rw [hax]; exact hl.1) | (rw [hout]; exact if_congr hl.2 rfl rfl)

/-! ## The function -/

theorem bodyP_eq (crtName : String) (crt : Prog isa) (pdName : String) (pd : Prog isa) :
    bodyP crtName crt pdName pd =
      .seq (.block crtArgsP) (.seq (.call crtName crt) (seqs (checkP pdName pd))) := rfl

/-- `vg_rsa_private_checked_precomputed`, calling the CRT given `pre` of the
implementation `v`. -/
theorem codeP_correct (v : CrtImpl) (pdName : String) (s : State) (h : chkContractP.pre s) :
    ∃ t s', Exec isa (codeP v.nameP v.codeP pdName (v.pubOp.code)) s t s' ∧ abiPreserved s s' ∧
      chkContractP.post s s' := by
  obtain ⟨hp, hf⟩ := preFP_of h
  have hk2 := hp.k2
  suffices hw : WP isa (codeP v.nameP v.codeP pdName (v.pubOp.code)) s fun s' =>
      abiPreserved s s' ∧ chkContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine wp_alloc (by have := hp.sp1; unfold stackBytes at this; unfold frameBytes; omega_using [this]) ?_
  rw [bodyP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .r8, .r9] (crtArgsP_ok hp hf) (by decide +kernel))
    fun t₁ ⟨⟨he₁, _, hargs, h96, h104, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (crtP_call v hp hf he₁ hargs h96 h104 hdi hsi hdx hcx h8 h9) fun t₂ ⟨he₂, hcrt, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono (check_okP v.pubOp pdName hp hf he₂)
    fun t₃ ⟨he₃, hrax, hout, _, hcs₃, hmx₃⟩ => ?_
  refine ⟨he₃.rsp, by rw [he₃.wr]; rfl, fun m u fm => ?_⟩
  have hstk : ∀ r ∈ [(⟨fb s, frameBytes⟩ : Region)], ∃ r' ∈ [stkR s, outR s, scrR s], Region.Sub r r' :=
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stkR s, by simp, frame_stk s⟩
  refine ⟨⟨fun r hr => ?_, ret_frame hp (he₃.mem.trans (fm.sub hstk)), ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he₃.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcs₃ r hr, hcs₂ r hr, k₁.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
      simp only [allocState_gpr, hr', ↓reduceIte]
  · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmx₃, hmx₂, hmx₁]; rfl
  · have hsi := hp.hsi
    rw [← Proof.Rsa.rsa_bytes_frame fm (s.gpr .rcx).isLt (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      have := (hp.dKo.sub_left (frame_stk s)).symm
      rwa [hsi] at this)] at hout
    simp only [chkContract]
    exact outcome_eq (bytesAt_length' _ _ _) (by rw [bytesAt_length']) hcrt hrax hout

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: constant time

As `vg_rsa_private_checked` (`PrivCT.lean`), from entry states that agree on
`chkContractP.pub` (`SibP`): its public data, `pre`'s address and length,
and the modulus' values in `pre`, which the CRT given `pre` and
`vg_rsa_public_precomputed_checked` both take as public (`codeP_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting `chkContractP`'s precondition with the anchor's
public data. -/
def SibP (a s : State) : Prop := chkContractP.pre s ∧ chkContractP.pub a s

theorem pubP_refl (s : State) : chkContractP.pub s s := ⟨pub_refl s, rfl, rfl, rfl⟩

theorem SibP.gpr {a s : State} (h : SibP a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem SibP.arg {a s : State} (h : SibP a s) {i : Nat} (hi : i < 14) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.1) i (List.mem_range.mpr hi)).symm

theorem SibP.n {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.1.2.2.1.symm

theorem SibP.e {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.1.2.2.2.symm

theorem SibP.fb {a s : State} (h : SibP a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem SibP.pre {a s : State} (h : SibP a s) :
    Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) := by
  have hl := h.2.2.2.2
  simp only [Spec.Rsa.privatePrecomputedLeak] at hl
  exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl).symm

/-- A point of a run, described by `J` from the run's entry state. -/
def AtP (J : State → State → Prop) (a t : State) : Prop := ∃ s, SibP a s ∧ J s t

theorem pinP {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, SibP a s → f s = f a) {a t₁ t₂ : State} (h₁ : AtP J a t₁) (h₂ : AtP J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinsP_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t) : Pins (AtP J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pinP fb (fun s t h => (hJ s t h).rsp) (fun _ _ h => h.fb) h₁ h₂

/-! ## The points of the code -/

def J1P (s t : State) : Prop :=
  J1 s t ∧ word t.mem (fb s) 96 = stackArg s 14 ∧ word t.mem (fb s) 104 = stackArg s 15

def J5P (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = off (fb s) oM ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 12 ∧ word t.mem (fb s) 24 = stackArg s 13 ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 14 ∧
    t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

/-! ## The calls -/

/-- `pre`'s words at a callee's entry, from the caller's entry state. -/
theorem Env.entryWordsP {s t : State} (he : Env s t) (hf : PFacts s) (rd wr : List Region) :
    Spec.Rsa.wordsAt (t.callEntry.withRegions rd wr).mem (stackArg s 14)
      (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
    Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
  have sP := preRp_sub hf
  have hl := hf.wPr
  have hpl := hf.hpl
  rw [State.withRegions_mem]
  exact words_of_frame (entry_frame he) (hf.dKp.symm.sub_left sP).symm (hf.dOp.symm.sub_left sP).symm
    (hf.dSp.symm.sub_left sP).symm (by unfold Spec.Rsa.privatePrecomputedWords at hpl; omega_arith)

/-- What the CRT given `pre`'s contract makes public, from the entry state. -/
theorem crtP_view {a s t : State} (S : SibP a s) (h : J1P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr =
      [off (fb a) oM, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, stackArg a 0, a.gpr .rcx, fb a - 8] ∧
    (∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg a (i + 2)) ∧
    stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg a 14 ∧
    stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg a 15 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (crtRdP s) (crtWr s)).mem
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rdx)
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions (crtRdP s) (crtWr s)).mem
      (stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12)
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 14) (a.gpr .rcx).toNat := by
  obtain ⟨⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩ := h
  obtain ⟨hp, hf⟩ := preFP_of S.1
  have e12 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg s 14 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans h96
  have e13 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg s 15 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans h104
  have rcx : (t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx = s.gpr .rcx := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hcx]
  refine ⟨?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by omega_using [hi]), hargs i hi, S.arg (by omega_using [hi])]
  · rw [e12]; exact S.2.2.1.symm
  · rw [e13]; exact S.2.2.2.1.symm
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_using []), S.n]
  · simp only [Spec.Rsa.privatePrecomputedLeak, rcx, e12]
    rw [he.entryWordsP hf, S.pre]

theorem crtP_ct (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.nameP v.codeP) fun _ _ => True := by
  refine RelCT.callEx (k := crtContractP.clear) v.okP v.ctP fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, a12₁, a13₁, n₁, l₁⟩ := crtP_view S₁ j₁
  obtain ⟨r₂, g₂, a12₂, a13₂, n₂, l₂⟩ := crtP_view S₂ j₂
  obtain ⟨hp₁, hf₁⟩ := preFP_of S₁.1
  obtain ⟨hp₂, hf₂⟩ := preFP_of S₂.1
  obtain ⟨c₁, w₁⟩ := crtP_covers hp₁ j₁.1.1
  obtain ⟨c₂, w₂⟩ := crtP_covers hp₂ j₂.1.1
  obtain ⟨⟨he₁, hargs₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩, h96₁, h104₁⟩ := j₁
  obtain ⟨⟨he₂, hargs₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩, h96₂, h104₂⟩ := j₂
  have p₁ : crtContractP.clear.pre ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁)) :=
    ⟨crtP_pre hp₁ hf₁ he₁ hargs₁ h96₁ h104₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁, crtP_clear hp₁ hf₁ he₁⟩
  have p₂ : crtContractP.clear.pre ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) :=
    ⟨crtP_pre hp₂ hf₂ he₂ hargs₂ h96₂ h104₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, crtP_clear hp₂ hf₂ he₂⟩
  have ga : ∀ i < 12, stackArg ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁)) i =
      stackArg ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) i := fun i hi => (g₁ i hi).trans (g₂ i hi).symm
  have hpub : crtContractP.pub ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁))
      ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) :=
    ⟨⟨regs_eq (r₁.trans r₂.symm), ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide),
      ga 4 (by decide), ga 5 (by decide), ga 6 (by decide), ga 7 (by decide), ga 8 (by decide), ga 9 (by decide),
      ga 10 (by decide), ga 11 (by decide), n₁.trans n₂.symm⟩, a12₁.trans a12₂.symm, a13₁.trans a13₂.symm,
      l₁.trans l₂.symm⟩
  exact ⟨crtRdP s₁, crtWr s₁, crtRdP s₂, crtWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precomputed_checked`'s contract makes public, given
`pre`. -/
theorem pdP_view {a s t : State} (S : SibP a s) (h : J5P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 14, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat),
        a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 0 = off (fb a) oM ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 2 = stackArg a 12 ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 3 = stackArg a 13 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (pdRdP s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pdRdP s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .r8)
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  obtain ⟨hp, hf⟩ := preFP_of S.1
  have hk2 := hp.k2
  have hpwl := preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hpwl])
  have rcx := S.gpr (r := .rcx) (by decide)
  have a14 : stackArg s 14 = stackArg a 14 := S.2.2.1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide), a14]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.fb]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← rcx]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, hcxN]
    rw [he.entryWordsP hf, S.pre]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [he.entryBytes _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []), S.e]

theorem pdP_ct (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) fun _ _ => True := by
  have hct : ConstantTime isa (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pub (P.code) :=
    P.ct
  refine RelCT.callEx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    P.ok hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, w₁', e₁⟩ := pdP_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, w₂', e₂⟩ := pdP_view S₂ j₂
  obtain ⟨hp₁, hf₁⟩ := preFP_of S₁.1
  obtain ⟨hp₂, hf₂⟩ := preFP_of S₂.1
  obtain ⟨c₁, w₁⟩ := pdP_covers hp₁ hf₁ j₁.1
  obtain ⟨c₂, w₂⟩ := pdP_covers hp₂ hf₂ j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : pdContract.pre (t₁.callEntry.withRegions (pdRdP s₁) (pdWr s₁)) :=
    pdP_pre hp₁ hf₁ he₁ hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : pdContract.pre (t₂.callEntry.withRegions (pdRdP s₂) (pdWr s₂)) :=
    pdP_pre hp₂ hf₂ he₂ hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdContract.pub (t₁.callEntry.withRegions (pdRdP s₁) (pdWr s₁))
      (t₂.callEntry.withRegions (pdRdP s₂) (pdWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, w₁'.trans w₂'.symm, e₁.trans e₂.symm⟩
  exact ⟨pdRdP s₁, pdWr s₁, pdRdP s₂, pdWr s₂, p₁, p₂, hpub, Covers.append_left c₁ w₁.right, w₁,
    Covers.append_left c₂ w₂.right, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem crtArgsP_two : RelCT isa (Two (AtP J0)) (.block crtArgsP) (Two (AtP J1P)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pinP fb (fun s t h => by rw [h]; rfl) (fun _ _ h => h.fb) h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      subst ht
      obtain ⟨hp, hf⟩ := preFP_of S.1
      exact WP.mono (crtArgsP_ok hp hf) fun _ ⟨he, _, hargs, h96, h104, hdi, hsi, hdx, hcx, h8, h9⟩ =>
        ⟨s, S, ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩

theorem crtCallP_two (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.nameP v.codeP) (Two (AtP J2)) :=
  two_post (crtP_ct v) fun _ _ ⟨s, S, ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩ =>
    WP.mono (crtP_call v (preFP_of S.1).1 (preFP_of S.1).2 he hargs h96 h104 hdi hsi hdx hcx h8 h9)
      fun _ h => ⟨s, S, h.1⟩

theorem pdArgsP_two : RelCT isa (Two (AtP J2)) (.block pdArgsP) (Two (AtP J5P)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ t ⟨s, S, he⟩ => by
      obtain ⟨hp, hf⟩ := preFP_of S.1
      refine WP.mono (pdArgsP_ok hp hf he) fun t₃ ⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩ => ?_
      have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
          [off (fb s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
        rw [hm₃]
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega_using [hd]) with rfl | rfl | rfl | rfl
        · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
          rfl
        · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
        · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
        · simp (disch := decide) only [word_writeW_self]; rfl
      exact ⟨s, S, he₃, hw (d := 0) (by decide), hw (d := 1) (by decide),
        hw (d := 2) (by decide), hw (d := 3) (by decide), hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩

theorem pdCallP_two (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) (Two (AtP J2)) :=
  two_post (pdP_ct P name) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pdP_call P name (preFP_of S.1).1 (preFP_of S.1).2 he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun _ h => ⟨s, S, h.1⟩

theorem cmpArgsP_two : RelCT isa (Two (AtP J2)) (.block cmpArgs) (Two (AtP J7)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (cmpArgs_ok (preFP_of S.1).1 he) fun _ ⟨_, _, hdi, hsi, hcx, h10, _, k⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hsi, hcx, h10⟩

theorem restP_ct : RelCT isa (Two (AtP J7))
    (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) fun _ _ => True :=
  two_taint [.rdi, .rsi, .rcx, .r10, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact pinP (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun s => stackArg s 0) (fun _ _ h => h.2.2.1) (fun _ _ S => S.arg (by decide)) h₁ h₂
    · exact pinP (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2.2) (fun _ _ _ => rfl) h₁ h₂
    · exact pinP fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂) (by taint_decide)

theorem bodyP_ct (v : CrtImpl) (pdName : String) :
    RelCT isa (Two (AtP J0)) (bodyP v.nameP v.codeP pdName (v.pubOp.code)) fun _ _ => True := by
  rw [bodyP_eq, checkP_eq, tail_eq]
  exact RelCT.seq crtArgsP_two (RelCT.seq (crtCallP_two v) (RelCT.seq pdArgsP_two
    (RelCT.seq (pdCallP_two v.pubOp pdName) (RelCT.seq cmpArgsP_two restP_ct))))

/-! ## The function -/

theorem codeP_constantTime (v : CrtImpl) (pdName : String) :
    ConstantTime isa chkContractP.pre chkContractP.pub (codeP v.nameP v.codeP pdName (v.pubOp.code)) :=
  RelCT.constantTime (relCT_alloc ((bodyP_ct v pdName).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pubP_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-- It writes `rsp` only in its frame's push and pop. -/
theorem codeP_spSafe (v : CrtImpl) (pdName : String) :
    (codeP v.nameP v.codeP pdName (v.pubOp.code)).all (fun i => !isa.writesSp i) = true := by
  simp only [codeP, bodyP_eq, checkP_eq, tail_eq, Code.all, v.spSafeP, v.pubOp.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.Rsa.X86_64
