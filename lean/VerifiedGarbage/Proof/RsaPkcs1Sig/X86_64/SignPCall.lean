module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCtx
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_pkcs1_sign_precomputed` on x86-64: the call with `pre`

`Sign.codeP` is `Sign.code` but for its call, of
`vg_rsa_private_checked_precomputed` (`privCodeP`), which it also gives the
key's precomputed values `pre` and `pre_len` as its stack arguments 14 and 15
(`callArgsP_ok`), over the slots of `out` and `out_len`; nothing reads those
after the call (`EnvC`). From a state that `vg_rsa_pkcs1_sign_precomputed`'s
contract allows (`PreS` and `PreP`, `preSP_of`), the call meets that
function's contract (`privP_pre`), and so `codeP` writes what `code` writes
(`codeP_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP codeP_correct codeP_spSafe)

/-! ## The private operation -/

/-- `vg_rsa_private_checked_precomputed`'s name and code, for `v`. -/
def privNameP (v : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ v.suffix
def privCodeP (v : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.codeP v.nameP v.codeP (pdName v) v.pubOp.code

theorem privCodeP_depth (v : CrtImpl) : (privCodeP v).x86_64Depth = 3256 := by
  simp only [privCodeP, Impl.Rsa.X86_64.PrivChecked.codeP, Impl.Rsa.X86_64.PrivChecked.bodyP,
    Impl.Rsa.X86_64.PrivChecked.checkP, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp v.nospP, v.depthP, x86_64Depth_noSp v.pubOp.nosp,
    v.pubOp.depth, X86_64.Instr.frameBytes, Impl.Rsa.X86_64.PrivChecked.frameBytes,
    Impl.Rsa.X86_64.PrivChecked.cmpLoop, Impl.Rsa.X86_64.PrivChecked.releaseLoop]
  rfl

/-! ## The precondition -/

/-- `pre`, of `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩

/-- The stack arguments, with `pre` and `pre_len`. -/
abbrev argsP (s : State) : Region := ⟨stackArgAddr s 0, 136⟩

/-- What `vg_rsa_pkcs1_sign_precomputed`'s contract adds to `PreS`: `pre`,
the precomputed values of the key, and the stack arguments that give it. -/
structure PreP (s : State) : Prop where
  hargs : argsP s ∈ s.rd
  hpr : preR s ∈ s.rd
  dKa : (stkR s).Disjoint (argsP s)
  dOa : (outR s).Disjoint (argsP s)
  dsa : (scrR s).Disjoint (argsP s)
  dKr : (stkR s).Disjoint (preR s)
  dOr : (outR s).Disjoint (preR s)
  dsr : (scrR s).Disjoint (preR s)
  wR : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  hpl : (stackArg s 16).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 4).toNat (stackArg s 6).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 15) (stackArg s 16).toNat)

theorem preSP_of {s : State} (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s) :
    PreS s ∧ PreP s := by
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, stackArgs_seventeen, List.append_eq, sigStack, List.range,
    List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOd dOp dOq dOdp dOdq dOqi dOs dOr dOa dns des dds dps dqs ddps ddqs dqis dsr
    dsa dRo dRn dRe dRd dRp dRq dRdp dRdq dRqi dRs dRr dRa dKo dKn dKe dKd dKp dKq dKdp dKdq dKqi dKs dKr dKa wO wN
    wE wD wP wQ wDp wDq wQi wS wR hk hsi L1 L2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsl hpl
  obtain ⟨k1, k2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have sA : Region.Sub ⟨stackArgAddr s 0, 120⟩ (argsP s) := Region.sub_prefix (by decide)
  have hrd' : ∀ r ∈ ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
      ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
      ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩] : List Region), r ∈ s.rd :=
    fun r hr => by rw [hrd]; exact List.mem_append_left [preR s, argsP s] hr
  refine ⟨⟨sp1, by omega_using [sp2], hrd',
    ⟨136, by decide, by decide, by rw [hrd]; simp⟩, hwr, dOn, dOe, dOd, dOp, dOq, dOdp, dOdq, dOqi, dOs,
    (dOa.symm.sub_left sA).symm, dns, des, dds, dps, dqs, ddps, ddqs, dqis, (dsa.symm.sub_left sA).symm, dRo, dRs,
    dKo, dKn, dKe, dKd, dKp, dKq, dKdp, dKdq, dKqi, dKs, (dKa.symm.sub_left sA).symm, wO, wN, wE, wD, wP, wQ, wDp,
    wDq, wQi, wS, k1, k2, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩,
    ⟨by rw [hrd]; simp, by rw [hrd]; simp, dKa, dOa, dsa, dKr, dOr, dsr, wR, hpl, h⟩⟩

/-! ## The arguments of the call -/

/-- The call's stack argument `i`: `callArg`'s, then `pre` and `pre_len`. -/
def callArgP (s : State) (i : Nat) : BitVec 64 := if i < 14 then callArg s i else stackArg s (i + 1)

theorem argP_val {s t : State} (he : EnvC s t) (hq : PreP s) {j : Nat} (hj : j < 17) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine he.mem.readW (r := argsP s) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hq.dKa.symm
    · exact hq.dOa.symm
    · exact hq.dsa.symm

theorem argP_in {s t : State} (hq : PreP s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 17) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨argsP s, List.mem_append_left _ (by rw [hrd]; exact hq.hargs),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

/-- Stack argument `j + 3` to the frame's word `j + 2`, for `pre` and
`pre_len` (`j` 12 and 13), over the slots of `out` and `out_len`. -/
theorem copyArgP_ok {s t : State} (hp : PreS s) (hq : PreP s) (he : EnvC s t) {j : Nat} (hj : 12 ≤ j)
    (hj' : j < 14) :
    WP isa (.block (copyArg j)) t fun t' => EnvC s t' ∧
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3)) ∧ Keep [.rax] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax] (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3))) (by
    xrun [copyArg, @arg_ea s, ea_sp, he.rsp, argP_in hq he.rd (show j + 3 < 17 by omega),
      argP_val he hq (show j + 3 < 17 by omega_using [hj']), hs.st (d := 8 * (j + 2)) (by unfold frameBytes; omega_using [hj'])]) rfl)
    fun t' ⟨hm, k⟩ => ⟨EnvC.of he hp (k.gpr (by decide)) k.2.1 k.2.2 (hm ▸ (Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
      ⟨8 * (j + 2), 8, List.mem_singleton.mp hr, .inl (by unfold oN; omega_using [hj']), by unfold frameBytes; omega_using [hj']⟩, hm, k⟩

/-- The arguments of `vg_rsa_private_checked_precomputed`. -/
theorem callArgsP_ok {s t : State} (hp : PreS s) (hq : PreP s) (he : Env s t) :
    WP isa (.block callArgsP) t fun t' => EnvC s t' ∧ (∀ i < 16, word t'.mem (fb s) (8 * i) = callArgP s i) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Frame [⟨fb s, 128⟩] t.mem t'.mem ∧ Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  unfold callArgsP
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (callArgs_ok hp he) fun t₁ ⟨he₁, hw₁, hdi, hsi, hdx, hcx, h8, h9, hf₁, k₁⟩ => ?_
  refine WP.mono (copyArgP_ok hp hq he₁.core (j := 12) (by decide) (by decide)) fun t₂ ⟨he₂, hm₂, k₂⟩ => ?_
  refine WP.mono (copyArgP_ok hp hq he₂ (j := 13) (by decide) (by decide)) fun t₃ ⟨he₃, hm₃, k₃⟩ => ?_
  have k := (k₁.trans k₂).trans k₃
  have kr : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9], t₃.gpr r = t₁.gpr r := fun r hr => by
    rw [k₃.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₂.gpr (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨he₃, fun i hi => ?_, by rw [kr _ (by simp), hdi], by rw [kr _ (by simp), hsi], by rw [kr _ (by simp), hdx],
    by rw [kr _ (by simp), hcx], by rw [kr _ (by simp), h8], by rw [kr _ (by simp), h9], ?_, k.mono (by decide)⟩
  · rw [hm₃, hm₂]
    unfold callArgP
    rcases (show i < 14 ∨ i = 14 ∨ i = 15 by omega_using [hi]) with hi' | rfl | rfl
    · rw [word_wo _ _ _ (.inr (by omega_using [hi'])) (by decide) (by omega_using [hi]), word_wo _ _ _ (.inr (by omega_using [hi'])) (by decide) (by omega_using [hi])]
      simp only [hi', ↓reduceIte]
      exact hw₁ i hi'
    · rw [word_wo _ _ _ (.inr (by decide)) (by decide) (by decide)]
      exact word_writeW_self _ _ _ _
    · exact word_writeW_self _ _ _ _
  · have hF := fb_toNat hp
    refine (hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans ?_
    rw [hm₃, hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base (fb s) (d := 8 * (12 + 2)) (n := 8) (k := 128) (by decide) (by omega_using []))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains_base (fb s) (d := 8 * (13 + 2)) (n := 8) (k := 128) (by decide) (by omega_using []))

/-! ## The call -/

/-- What `vg_rsa_private_checked_precomputed` reads: `privRd`, its stack
arguments 14 and 15, and `pre`. -/
def privRdP (s : State) : List Region := privRd s ++ [⟨off (fb s) 112, 16⟩, preR s]

theorem wordsP_of_frame {s : State} {m : Mem} (hq : PreP s) (hf : Frame [stkR s, outR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 15) (stackArg s 16).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 15) (stackArg s 16).toNat := by
  have hl := hq.wR
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.readW (r := preR s) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hq.dKr.symm
  · exact hq.dOr.symm
  · exact hq.dsr.symm

/-- The call meets `vg_rsa_private_checked_precomputed`'s contract. -/
theorem privP_pre {s t : State} (hp : PreS s) (hq : PreP s) (he : EnvC s t)
    (hw : ∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContractP.pre (t.callEntry.withRegions (privRdP s) (privWr s)) := by
  have hw14 : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i := fun i hi => by
    rw [hw i (by omega_using [hi])]; simp only [callArgP, hi, ↓reduceIte]
  have hE : ∀ i, i < 16 → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) i = callArgP s i :=
    fun i hi => (stackArg_entry he.rsp _ _ (by omega_using [hi])).trans (hw i hi)
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr, below_kb]; exact .inl (Region.sub_prefix (by decide))
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have hF := fb_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hfb : fb s = off (kb s) 3264 := fb_kb s
  have sA2 : Region.Sub ⟨off (fb s) 112, 16⟩ (stkR s) := by rw [hfb, off_off]; exact ksub s (by decide)
  have sK : Region.Sub ⟨off (kb s) 3256 - BitVec.ofNat 64 3256, 3256⟩ (stkR s) := by
    rw [show off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s from BitVec.add_sub_cancel _ _]
    exact Region.sub_prefix (by decide)
  have hkk : off (kb s) 3256 - BitVec.ofNat 64 3256 = kb s := BitVec.add_sub_cancel _ _
  have e14 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = stackArg s 15 := hE 14 (by decide)
  have e15 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 = stackArg s 16 := hE 15 (by decide)
  have e2 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 2 = stackArg s 3 := hE 2 (by decide)
  have e3 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 3 = stackArg s 4 := hE 3 (by decide)
  have e4 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 4 = stackArg s 5 := hE 4 (by decide)
  have e5 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 5 = stackArg s 6 := hE 5 (by decide)
  have a14 : stackArgAddr (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = off (fb s) 112 := by
    rw [stackArgAddr_eq _ 14, stackArgAddr_entry he.rsp, off]
  have hsp : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rsp = fb s - 8 := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, he.rsp]
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  refine ⟨priv_pre hp he.rsp hw14 hdi hsi hdx hcx h8 h9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.withRegions_rd, a14, e14, e15]; rfl
  · rw [hsp, fb_sub8, toNat_off (by unfold sigStack at hK1; omega_using [hK1])]; unfold sigStack at hK1; omega_using [hK1]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hdi, hsi, a14]
    exact (hp.dKo.sub_left sA2).symm
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hdi, hsi, e14, e15]
    exact hq.dOr
  · rw [hE 12 (by decide), hE 13 (by decide), a14]
    exact (hp.dKs.sub_left sA2).symm
  · rw [hE 12 (by decide), hE 13 (by decide), e14, e15]
    exact hq.dsr
  · rw [hsp, fb_sub8, a14, show off (kb s) 3256 - BitVec.ofNat 64 Rsa.X86_64.stackBytes = kb s from
      BitVec.add_sub_cancel _ _, hfb, off_off]
    exact Offset.base_disjoint (kb s) (by decide) (by unfold sigStack at hK1; omega_using [])
  · rw [hsp, fb_sub8, e14, e15, show off (kb s) 3256 - BitVec.ofNat 64 Rsa.X86_64.stackBytes = kb s from
      BitVec.add_sub_cancel _ _]
    exact hq.dKr.sub_left (Region.sub_prefix (by decide))
  · rw [stackArgAddr_entry he.rsp, a14]
    exact Offset.base_disjoint (fb s) (by decide) (by unfold frameBytes at hF; omega_using [])
  · rw [e14, e15]; exact hq.wR
  · rw [e15, e3, e5]
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hcx]
    exact hq.hpl
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, e2, e3, e4, e5, e14, e15]
    rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_using []), b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega_using []),
      b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega_using []), wordsP_of_frame hq hfE]
    exact hq.key

theorem privP_covers {s t : State} (hp : PreS s) (hq : PreP s) (he : EnvC s t) :
    Covers (privRdP s ++ privWr s) (t.rd ++ t.wr) ∧ Covers (privWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hout : outR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [outR]
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (privWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by simp only [outR]; omega_using []⟩
    · exact ⟨_, hscr, 0, z _, by simp only [scrR]; omega_using []⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [privRdP, privRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hrd ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only [emR]; unfold oEM frameBytes; omega_using [hk2]⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hrd ⟨stackArg s 11, (stackArg s 12).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, 112, rfl, by dsimp only; unfold frameBytes; omega_using []⟩
  · exact ⟨_, hrd (preR s) hq.hpr, 0, z _, by dsimp only; omega_using []⟩

/-- The call of `vg_rsa_private_checked_precomputed`: as `priv_call`. -/
theorem privP_call (v : CrtImpl) {s t : State} (hp : PreS s) (hq : PreP s) (he : EnvC s t)
    (hw : ∀ i < 16, word t.mem (fb s) (8 * i) = callArgP s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call (privNameP v) (privCodeP v)) t (PrivPost s t) := by
  obtain ⟨hc, hcw⟩ := privP_covers hp hq he
  have hw14 : ∀ i < 14, word t.mem (fb s) (8 * i) = callArg s i := fun i hi => by
    rw [hw i (by omega_using [hi])]; simp only [callArgP, hi, ↓reduceIte]
  exact privWith_call (codeP_correct v (pdName v)) (fun _ _ h => h) (codeP_spSafe v _) (privCodeP_depth v) hp he
    hw14 hdi hdx hcx h8 h9 (privP_pre hp hq he hw hdi hsi hdx hcx h8 h9) hc hcw

/-- The arguments of `vg_rsa_private_checked_precomputed` and its call, on
`EM`. -/
theorem callStepP_ok (v : CrtImpl) {s t₃ : State} (hp : PreS s) (hq : PreP s) (he₃ : Env s t₃) {em : List Byte}
    (hEM₃ : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em) :
    WP isa (.block callArgsP) t₃ fun u => WP isa (.call (privNameP v) (privCodeP v)) u (CallOut s t₃ em) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  refine WP.mono_mx (by decide) (callArgsP_ok hp hq he₃)
    fun t₄ ⟨he₄, hw₄, hdi, hsi, hdx, hcx, h8, h9, hf₄, k₄⟩ hmx₄ => ?_
  have hEM : Spec.Rsa.bytesAt t₄.mem (off (fb s) oEM) (s.gpr .rcx).toNat = em := by
    rw [← hEM₃]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hf₄.bytes (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by dsimp only; omega_using []) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint (fb s) (e := oEM) (n := (s.gpr .rcx).toNat) (k := 128) (by decide)
      (by unfold oEM frameBytes at *; omega_using [hk2])).symm
  refine WP.mono (privP_call v hp hq he₄ hw₄ hdi hsi hdx hcx h8 h9) fun t₅ ⟨he₅, hout₅, _, hcs₅, hmx₅⟩ =>
    ⟨he₅, by rw [hEM] at hout₅; exact hout₅, fun r hr => ?_, by rw [hmx₅, hmx₄]⟩
  have hr' : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by
    simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [hcs₅ r hr, k₄.gpr hr']

/-! ## The function -/

/-- `vg_rsa_pkcs1_sign_precomputed`, from a state its contract allows:
`code`'s result. -/
theorem codeP_ok (v : CrtImpl) {s : State} (hp : PreS s) (hq : PreP s) :
    WP isa (codeP (privNameP v) (privCodeP v)) s fun s' => abiPreserved s s' ∧ sigContract.post s s' :=
  codeWith_ok hp fun he₁ h8₁ hK₂ _ hlen hout =>
    afterEncWith_ok hp he₁ h8₁ hK₂ hlen hout fun _ _ he hEM => callStepP_ok v hp hq he hEM

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
