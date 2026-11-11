module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.PreWords
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

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
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

end VG.Proof.Rsa.X86_64
