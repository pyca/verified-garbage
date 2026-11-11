module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.Rsa.Scratch
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

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
  have hp0 := preF_of h0
  refine ⟨{ hp0 with hrd := ?_ }, ⟨sp3, dOa2, dOp, dSa2, dSp, dKa2, dKp, dAa2, wPr, hpl, hpp⟩⟩
  rw [← List.take_append_drop 9 s.rd, hdrop]
  exact (congrArg (· ++ xP s) hp0.hrd).trans (by rw [List.append_nil]; rfl)

/-! ## The CRT's arguments -/

/-- A stack argument up to 15, past stores to the frame. -/
theorem argP_outside {s : State} (hp : PreF X s) (hf : PFacts s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m)
    {j : Nat} (hj : j < 16) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := hp.sp1
  have := hf.sp3
  have hF : (fb s).toNat + frameBytes + 8 + 128 ≤ 2 ^ 64 := by
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytes at *; omega
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

theorem stackArgAddr_15 (s : State) : stackArgAddr s 15 = stackArgAddr s 14 + BitVec.ofNat 64 8 := by
  unfold stackArgAddr; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Stack arguments 14 and 15 are readable. -/
theorem arg2_in {s : State} (hp : PreF (xP s) s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : 14 ≤ j) (hj' : j < 16) : InRegions (rd ++ wr) (stackArgAddr s j) 8 := by
  refine ⟨⟨stackArgAddr s 14, 16⟩, List.mem_append_left _ (by
    rw [hrd, hp.hrd]; exact List.mem_append_right _ (List.mem_cons_self ..)), ?_⟩
  rcases (show j = 14 ∨ j = 15 by omega) with rfl | rfl
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
  have hF := fb_toNat hp
  unfold crtArgsP
  rw [WP.block_append_iff]
  refine WP.mono (crtArgs_ok hp) fun t₁ ⟨he, ho, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_
  have hs := he.scr hp
  have h14 := argP_outside hp hf ho (j := 14) (by decide)
  have h15 := argP_outside hp hf ho (j := 15) (by decide)
  have ho1 : Outside (fb s) 0 frameBytes s.mem (t₁.mem.writeW (off (fb s) 96) (stackArg s 14)) := fun x hx =>
    (writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega)).trans (ho x hx)
  have h15' := argP_outside hp hf ho1 (j := 15) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem =
      (t₁.mem.writeW (off (fb s) 96) (stackArg s 14)).writeW (off (fb s) 104) (stackArg s 15)) (by
    xrun [arg, ea_sp, he.rsp,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 14) = stackArgAddr s 14 from (stackArgAddr_fb s 14).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 15) = stackArgAddr s 15 from (stackArgAddr_fb s 15).symm,
      arg2_in hp he.rd t₁.wr (j := 14) (by decide) (by decide),
      arg2_in hp he.rd t₁.wr (j := 15) (by decide) (by decide), h14, h15, h15',
      hs.st (d := 96) (by decide), hs.st (d := 104) (by decide)]) rfl) fun t ⟨hm, k⟩ => ?_
  have hw : ∀ d, d + 8 ≤ 96 ∨ 112 ≤ d → d + 8 ≤ frameBytes → word t.mem (fb s) d = word t₁.mem (fb s) d :=
    fun d hd hd' => by
      rw [hm, word_wo _ _ _ (by omega) (by decide) (by unfold frameBytes at hd'; omega),
        word_wo _ _ _ (by omega) (by decide) (by unfold frameBytes at hd'; omega)]
  have ho' : Outside (fb s) 0 frameBytes s.mem t.mem := by
    rw [hm]
    intro x hx
    rw [writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega),
      writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega)]
    exact ho x hx
  refine ⟨⟨(k.gpr (by decide)).trans he.rsp, k.2.1.trans he.rd, k.2.2.trans he.wr, frame_of_outside ho',
      (hw _ (by decide) (by decide)).trans he.sOut, (hw _ (by decide) (by decide)).trans he.sN,
      (hw _ (by decide) (by decide)).trans he.sK, (hw _ (by decide) (by decide)).trans he.sE,
      (hw _ (by decide) (by decide)).trans he.sEl⟩, ho', fun i hi => (hw _ (by omega) (by unfold frameBytes; omega)).trans
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
  have hi := List.mem_range.mp hi
  refine hf.readW (r := ⟨p, len * 8⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
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
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_arith)).trans (hargs i hi)
  have hE12 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg s 14 :=
    (stackArg_entry he.rsp _ _ (by omega_arith)).trans h96
  have hE13 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg s 15 :=
    (stackArg_entry he.rsp _ _ (by omega_arith)).trans h104
  have hfE := entry_frame he
  have hil := hp.hil
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
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
  have sM : Region.Sub ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 112) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := by
    have := ret_sub s; rwa [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl] at this
  have dMA : (⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 112⟩ :=
    Offset.disjoint_base _ (by decide) (by omega_arith)
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_kb s
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  have wM : (off (fb s) oM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega_arith)]; unfold oM; omega_arith), hfb, ← off,
      toNat_off (by omega_arith)]; unfold oM; omega_arith
  have dKi : (stkR s).Disjoint ⟨stackArg s 0, (s.gpr .rcx).toNat⟩ := by rw [← hil]; exact hp.dKi
  have dis : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ := by
    rw [← hil]; exact hp.dis
  have wI : (stackArg s 0).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hil]; exact hp.wI
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
  have sH := hole_sub s
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
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (crtWr s) t.wr := Covers.of_sub fun r hr => by
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
  have hE : ∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_arith)).trans (hargs i hi)
  have hfE := entry_frame he
  have hk2 := hp.k2
  have hil := hp.hil
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
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
    rw [hf.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega)

/-- A stack argument up to 15 past a store to the frame. -/
theorem arg_woP {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 16) :
    (m.writeW (off (fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (fb s) v (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)

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
  have hs := he.scr hp
  have hk2 := hp.k2
  have h0 : InRegions t.wr (fb s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
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
    have fr : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨fb s, frameBytes⟩ : Region).Contains (off (fb s) d) 8 :=
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
  have sP := preRp_sub hf
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
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
  have hpw := preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) i = word t.mem (fb s) (8 * i) :=
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
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_kb s
  have sP := preRp_sub hf
  have sM := mR_sub hp
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have rb : below (fb s) 8 = ⟨kb s, 8⟩ := by simp only [below]; rw [← fb_sub8]; rfl
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := by rw [← rb]; exact ret_sub s
  have dRP : (⟨kb s, 8⟩ : Region).Disjoint (preRp s) := ((hf.dKp.sub_left sR).symm.sub_left sP).symm
  have dOP : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (preRp s) := by
    rw [← hsi']; exact (hf.dOp.symm.sub_left sP).symm
  have wPp : (stackArg s 14).toNat + Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 := by
    have := hf.wPr; have := hf.hpl; unfold Spec.Rsa.privatePrecomputedWords at *; omega_arith
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint (mR s) := by
    rw [← rb]; exact ret_disjoint s (by unfold oM frameBytes; omega_arith)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
  have dOut : ∀ {r : Region}, Region.Sub r (stkR s) →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r := fun h => by
    rw [← hsi']; exact (hp.dKo.sub_left h).symm
  have wFr : ∀ {d n : Nat}, d + n ≤ frameBytes → (off (fb s) d).toNat + n ≤ 2 ^ 64 := fun {d n} h => by
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
  have hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pdWr s) t.wr := Covers.of_mem fun r hr => by
    simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [he.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [← hsi']; simp
    · simp [scrR]
  have cr : Covers (pdRdP s) (t.rd ++ t.wr) := Covers.of_sub fun r hr => by
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
  have hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain ⟨cr, cw⟩ := pdP_covers hp hq he
  have hv := P.ok
  have hpre := pdP_pre hp hq he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9
  have hdd : 8 * (P.code).depth + 16 < 2 ^ 64 := by rw [P.depth]; decide
  have hpre' : (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (t.callEntry.withRegions (pdRdP s) (pdWr s)) := hpre
  have hcov := Covers.append_left cr cw.right
  refine WP.call_mx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := pdRdP s) (wr := pdWr s)
    hv P.nosp hdd
    hpre' hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [P.depth, he.rsp] at hf
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hcxN, hm₂, hg₂ .rax (by decide), stackArg_entry he.rsp _ _ (show 0 < 400 by decide),
    Nat.mul_zero, hw0, entry_bytes he.rsp (show oM + (s.gpr .rcx).toNat ≤ frameBytes by unfold oM frameBytes; omega_arith),
    entry_wordsP he.rsp hq,
    bytes_of_frame hfE hp.dKe hp.dOe (hp.des.symm) (by have := hp.wE; omega_arith)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ frameBytes → 32 ≤ d → ∀ r ∈ pdWr s ++ [below (fb s) 8],
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
  have hpw := preWords_le hp
  have csk : ∀ {rs : List Reg} {a b : State}, Keep rs a b → (∀ r ∈ calleeSaved, r ∉ rs) →
      ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun k h r hr => k.gpr (h r hr)
  rw [checkP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (pdArgsP_ok hp hf he) rfl)
    fun t₃ ⟨⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩, k₃⟩ hmx₃ => ?_)
  have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
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
    have hr1 : word t₄.mem (fb s) oR1 = t.gpr .rax := by
      rw [hR1₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
    have hr3 : word t₄.mem (fb s) oR3 = 1 := by
      rw [hR3₄, hm₃]
      simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
    have hmb : Spec.Rsa.bytesAt t₃.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat := by
      rw [hm₃]
      simp (disch := first | decide | (simp only [oM, oR3, oR1]; omega_arith)) only [bytes_wo, bytes_wo0]
    have sP := preRp_sub hf
    have hpre : Spec.Rsa.wordsAt t₃.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
        Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
      have hl := hf.wPr
      have hpl := hf.hpl
      exact words_of_frame he₃.mem (hf.dKp.symm.sub_left sP).symm (hf.dOp.symm.sub_left sP).symm
        (hf.dSp.symm.sub_left sP).symm (by unfold Spec.Rsa.privatePrecomputedWords at hpl; omega_arith)
    have hpub := VG.Proof.Rsa.privatePrecompute_public hf.hpp
    rw [bytesAt_length'] at hpub
    rw [hr1, hr3] at hax hout
    rw [hM₄, hmb] at hout
    simp only [hmb] at hpd
    have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some _ => (1 : BitVec 64).setWidth 32 = 1
        | none => (1 : BitVec 64).setWidth 32 = 0 := by
      rw [hpub]; rfl
    have hl := check_logic (r₁ := t.gpr .rax) (r₂ := t₄.gpr .rax) (r₃ := 1)
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
  refine wp_alloc (by have := hp.sp1; unfold stackBytes at this; unfold frameBytes; omega) ?_
  rw [bodyP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .r8, .r9] (crtArgsP_ok hp hf) (by decide +kernel))
    fun t₁ ⟨⟨he₁, _, hargs, h96, h104, hdi, hsi, hdx, hcx, h8, h9⟩, k₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono (crtP_call v hp hf he₁ hargs h96 h104 hdi hsi hdx hcx h8 h9) fun t₂ ⟨he₂, hcrt, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono (check_okP v.pubOp pdName hp hf he₂)
    fun t₃ ⟨he₃, hrax, hout, _, hcs₃, hmx₃⟩ => ?_
  refine ⟨he₃.rsp, by rw [he₃.wr]; rfl, ⟨fun r hr => ?_, ret_frame hp he₃.mem, ?_⟩, ?_⟩
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
  · have hfr : (freed frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
    have hfm : (freed frameBytes t₃).mem = t₃.mem := rfl
    simp only [chkContract, hfr, hfm]
    exact outcome_eq (bytesAt_length' _ _ _) (by rw [bytesAt_length']) hcrt hrax hout

end VG.Proof.Rsa.X86_64
