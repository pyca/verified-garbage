module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on x86-64: the call with `pre`

`Decrypt.codeP` is `Decrypt.code` but for its call, of
`vg_rsa_private_checked_precomputed` (`privCodeP`), which it also gives the
key's precomputed values `pre` and `pre_len` as its stack arguments 14 and 15,
over the slots of `out` and `msg_len`: those are kept in the slots `oI` and
`oNB` across the call (`stash_ok`, `SetupP`) and put back after it
(`restore_ok`), which leaves what the call in `Decrypt.code` leaves
(`PostPriv`). From a state that `vg_rsa_pkcs1_decrypt_precomputed`'s
contract allows (`DPre` and `DPreP`, `dPreP_of`), the call meets that
function's contract (`privP_pre`), and so `codeP` writes what `code` writes
(`decP_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP codeP_correct codeP_spSafe)
open VG.Proof.Sha256.X86_64 (Compress)

/-! ## The private operation -/

/-- `vg_rsa_private_checked_precomputed` calling `c`: its name and code. -/
def privNameP (c : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ c.suffix
def privCodeP (c : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.codeP c.nameP c.codeP c.pubOp.name c.pubOp.code

theorem privCodeP_depth (c : CrtImpl) : (privCodeP c).x86_64Depth ≤ privStack := by
  simp only [privCodeP, Impl.Rsa.X86_64.PrivChecked.codeP, Impl.Rsa.X86_64.PrivChecked.bodyP,
    Impl.Rsa.X86_64.PrivChecked.checkP, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_noSp c.nospP, c.depthP,
    x86_64Depth_noSp c.pubOp.nosp, c.pubOp.depth]
  decide

/-! ## The precondition -/

/-- `pre`, of `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 17, (stackArg s 18).toNat * 8⟩

/-- The stack arguments, with `pre` and `pre_len`. -/
abbrev argsP (s : State) : Region := ⟨stackArgAddr s 0, 152⟩

/-- What `vg_rsa_pkcs1_decrypt_precomputed`'s contract adds to `DPre`:
`pre`, the precomputed values of the key, and the stack arguments that give
it. -/
structure DPreP (s : State) : Prop where
  sp3 : (s.gpr .rsp).toNat + 160 ≤ 2 ^ 64
  hargs : argsP s ∈ s.rd
  hpr : preR s ∈ s.rd
  dKa : (stkR s).Disjoint (argsP s)
  dOa : (outR s).Disjoint (argsP s)
  dMa : (mlR s).Disjoint (argsP s)
  dsa : (scrR s).Disjoint (argsP s)
  dKr : (stkR s).Disjoint (preR s)
  dOr : (outR s).Disjoint (preR s)
  dMr : (mlR s).Disjoint (preR s)
  dsr : (scrR s).Disjoint (preR s)
  wR : (stackArg s 17).toNat + (stackArg s 18).toNat * 8 ≤ 2 ^ 64
  hpl : (stackArg s 18).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r8).toNat (stackArg s 6).toNat (stackArg s 8).toNat
  key : Spec.Rsa.privatePrecompute (nB s) (pB s) (qB s) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 17) (stackArg s 18).toNat)

theorem dPreP_of {s : State} (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack).pre s) :
    DPre s ∧ DPreP s := by
  rw [show decStack = 3480 from rfl] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_nineteen, List.append_eq, List.range,
    List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOm dOn dOe dOd dOi dOp dOq dOdp dOdq dOqi dOs dOr dOa dMn dMe dMd dMi dMp dMq dMdp
    dMdq dMqi dMs dMr dMa dns des dds dis dps dqs ddps ddqs dqis dsr dsa dRo dRm dRn dRe dRd dRi dRp dRq dRdp
    dRdq dRqi dRs dRr dRa dKo dKm dKn dKe dKd dKi dKp dKq dKdp dKdq dKqi dKs dKr dKa wO wM wN wE wD wI wP wQ wDp
    wDq wQi wS wR hk hsi hil L1 L2 dl1 dl2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsl hpl
  obtain ⟨k1, k2⟩ := hk
  have sA : Region.Sub ⟨stackArgAddr s 0, 136⟩ (argsP s) := Region.sub_prefix (by decide)
  have hrd' : ∀ r ∈ ([⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
      ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
      ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
      ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
      ⟨stackArg s 13, (stackArg s 14).toNat⟩] : List Region), r ∈ s.rd :=
    fun r hr => by rw [hrd]; exact List.mem_append_left [preR s, argsP s] hr
  exact ⟨⟨sp1, by omega_using [sp2], hrd', ⟨152, by decide, by decide, by rw [hrd]; simp⟩, hwr, dOm, dOn, dOe, dOd, dOi,
    dOp, dOq, dOdp, dOdq, dOqi, dOs, (dOa.symm.sub_left sA).symm, dMn, dMe, dMd, dMi, dMp, dMq, dMdp, dMdq, dMqi,
    dMs, (dMa.symm.sub_left sA).symm, dns, des, dds, dis, dps, dqs, ddps, ddqs, dqis,
    (dsa.symm.sub_left sA).symm, dRo, dRm, dRs, dKo, dKm, dKn, dKe, dKd, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs,
    (dKa.symm.sub_left sA).symm, wO, wM, wN, wE, wD, wI, wP, wQ, wDp, wDq, wQi, wS, k1, k2, hsi, hil, L1, L2,
    dl1, dl2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩,
    ⟨sp2, by rw [hrd]; simp, by rw [hrd]; simp, dKa, dOa, dMa, dsa, dKr, dOr, dMr, dsr, wR, hpl, h⟩⟩

/-! ## Before the call -/

/-- The slots across the call: `Slots`, but `out` and `msg_len` in `oI`
and `oNB`. -/
structure SlotsP (s : State) (m : Mem) : Prop where
  sN : word m (fb s) oN = s.gpr .rcx
  sK : word m (fb s) oK = s.gpr .r8
  sE : word m (fb s) oE = s.gpr .r9
  sEl : word m (fb s) oEl = stackArg s 0
  sD : word m (fb s) oD = stackArg s 1
  sDl : word m (fb s) oDl = stackArg s 2
  sIn : word m (fb s) oIn = stackArg s 3
  sScr : word m (fb s) oScr = stackArg s 15
  sI : word m (fb s) oI = s.gpr .rdi
  sNB : word m (fb s) oNB = s.gpr .rdx

/-- What `setup` and `stash` leave. -/
structure SetupP (s t : State) : Prop where
  call : CallAt s t
  slots : SlotsP s t.mem
  a14 : word t.mem (fb s) 112 = stackArg s 17
  a15 : word t.mem (fb s) 120 = stackArg s 18

theorem argP_in {s : State} (hq : DPreP s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : j < 19) : InRegions (rd ++ wr) (stackArgAddr s j) 8 :=
  ⟨argsP s, List.mem_append_left _ (by rw [hrd]; exact hq.hargs),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

theorem argP_outside {s : State} (hp : DPre s) (hq : DPreP s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m)
    {j : Nat} (hj : j < 19) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  have := hq.sp3
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

/-- A stack argument to the frame's word at `d`, for `pre` and `pre_len`
too. -/
theorem mvArg_run' {s t : State} (hp : DPre s) (hq : DPreP s) (hsp : t.gpr .rsp = fb s)
    (hs : Scr t (fb s) frameBytes) (hrd : t.rd = s.rd) (ho : Outside (fb s) 0 frameBytes s.mem t.mem) {j d : Nat}
    (hj : j < 19) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (mvArg j d)) t fun t' => t'.mem = t.mem.writeW (off (fb s) d) (stackArg s j) ∧
      Keep [.rax] t t' := by
  have ha := argP_in hq hrd t.wr hj
  exact WP.keep [.rax] (by xrun [mvArg, ea_arg hsp, ea_sp, hsp, ha, argP_outside hp hq ho hj, hs.st hd]) rfl

/-- A slot to another, through `rax` or `r11`. -/
theorem mvSlot_run {t : State} {b : Addr} (hsp : t.gpr .rsp = b) (hs : Scr t b frameBytes) {r : Reg}
    (hr : r = .rax ∨ r = .r11) {d e : Nat} (hd : d + 8 ≤ frameBytes) (he : e + 8 ≤ frameBytes) :
    WP isa (.block (mvSlot r d e)) t fun t' => t'.mem = t.mem.writeW (off b e) (word t.mem b d) ∧
      Keep [r] t t' := by
  rcases hr with rfl | rfl
  · exact WP.keep [.rax] (by xrun [mvSlot, ea_sp, hsp, hs.ld hd, hs.st he]) rfl
  · exact WP.keep [.r11] (by xrun [mvSlot, ea_sp, hsp, hs.ld hd, hs.st he]) rfl

/-- `setup`, then `stash`. -/
theorem stash_ok {s t : State} (hp : DPre s) (hq : DPreP s) (h : Setup s t) :
    WP isa (.block stash) t fun t' => SetupP s t' ∧ Keep [.rax] t t' := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by unfold frameBytes at *; omega_arith)
  rw [stash, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mvSlot_run h.rsp hs (.inl rfl) (d := oOut) (e := oI) (by decide) (by decide))
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  refine WP.mono (mvSlot_run ((k₁.gpr (by decide)).trans h.rsp) (hs.congr k₁.2.2) (.inl rfl) (d := oML) (e := oNB)
    (by decide) (by decide)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have ho₂ : Outside (fb s) 0 frameBytes s.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact Outside.ww (Outside.ww h.out _ (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)
  refine WP.mono (mvArg_run' hp hq ((k12.gpr (by decide)).trans h.rsp) (hs.congr k12.2.2) (k12.2.1.trans h.rd) ho₂
    (j := 17) (d := 112) (by decide) (by decide)) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have k13 := k12.trans k₃
  have ho₃ : Outside (fb s) 0 frameBytes s.mem t₃.mem := by
    rw [hm₃]; exact Outside.ww ho₂ _ (by decide) (by decide) (by decide)
  refine WP.mono (mvArg_run' hp hq ((k13.gpr (by decide)).trans h.rsp) (hs.congr k13.2.2) (k13.2.1.trans h.rd) ho₃
    (j := 18) (d := 120) (by decide) (by decide)) fun t' ⟨hm', k'⟩ => ?_
  have k := k13.trans k'
  have ho : Outside (fb s) 0 frameBytes s.mem t'.mem := by
    rw [hm']; exact Outside.ww ho₃ _ (by decide) (by decide) (by decide)
  have w : ∀ {d : Nat}, (d + 8 ≤ oI ∨ oNB + 8 ≤ d) → d % 8 = 0 → d + 8 ≤ frameBytes → d + 8 ≤ 112 ∨ 128 ≤ d →
      word t'.mem (fb s) d = word t.mem (fb s) d := fun h₁ h₂ h₃ h₄ => by
    rw [hm', hm₃, hm₂, hm₁, word_ww _ _ _ (by omega_using [h₄]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by omega_using [h₄]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by simp only [oI, oNB] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by simp only [oI, oNB] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide)]
  have regs : ∀ r : Reg, r ≠ .rax → t'.gpr r = t.gpr r := fun r hr => k.gpr (by simpa using hr)
  refine ⟨⟨⟨(regs _ (by decide)).trans h.rsp, k.2.1.trans h.rd, k.2.2.trans h.wr, ho,
      fun i hi => (w (.inl (by unfold oI; omega_using [hi])) (by omega_using []) (by unfold frameBytes; omega_using [hi]) (.inl (by omega_using [hi]))).trans
        (h.args i hi),
      (regs _ (by decide)).trans h.rdi, (regs _ (by decide)).trans h.rsi, (regs _ (by decide)).trans h.rdx,
      (regs _ (by decide)).trans h.rcx, (regs _ (by decide)).trans h.r8, (regs _ (by decide)).trans h.r9⟩,
    ⟨(w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sN,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sK,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sE,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sEl,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sD,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sDl,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sIn,
      (w (by decide) (by decide) (by decide) (by decide)).trans h.slots.sScr, ?_, ?_⟩, ?_, ?_⟩, k.mono (by decide)⟩
  · rw [hm', hm₃, hm₂, word_ww _ _ _ (by decide) (by decide) (by decide),
      word_ww _ _ _ (by decide) (by decide) (by decide), word_ww _ _ _ (by decide) (by decide) (by decide), hm₁,
      word_writeW_self]
    exact h.slots.sOut
  · rw [hm', hm₃, word_ww _ _ _ (by decide) (by decide) (by decide),
      word_ww _ _ _ (by decide) (by decide) (by decide), hm₂, word_writeW_self, hm₁,
      word_ww _ _ _ (by decide) (by decide) (by decide)]
    exact h.slots.sML
  · rw [hm', word_ww _ _ _ (by decide) (by decide) (by decide), hm₃, word_writeW_self]
  · rw [hm', word_writeW_self]

/-! ## The call -/

/-- What `vg_rsa_private_checked_precomputed` reads: `privRd`, its stack
arguments 14 and 15, and `pre`. -/
def privRdP (s : State) : List Region := privRd s ++ [⟨off (fb s) 112, 16⟩, preR s]

/-- The words of `pre` past changes where the function may write. -/
theorem wordsP_of_frame {s : State} {m : Mem} (hq : DPreP s) (hf : Frame (wrs s) s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 17) (stackArg s 18).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 17) (stackArg s 18).toNat := by
  have hl := hq.wR
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.readW (r := preR s) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hq.dKr.symm
  · exact hq.dOr.symm
  · exact hq.dMr.symm
  · exact hq.dsr.symm

/-- The call meets `vg_rsa_private_checked_precomputed`'s contract. -/
theorem privP_pre {s t : State} (hp : DPre s) (hq : DPreP s) (h : SetupP s t) :
    chkContractP.pre (t.callEntry.withRegions (privRdP s) (privWr s)) := by
  have hc := h.call
  have hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside hc.out) (callEntry_frame hc.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩
  have ⟨hK1, _⟩ := kb_toNat hp
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e5 : decStack = 3480 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 216 := rfl
  have hfb : fb s = off (kb s) (8 + privStack) := fb_eq s
  have sA2 : Region.Sub ⟨off (fb s) 112, 16⟩ (stkR s) := frame_sub s (by decide)
  have hE : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args hc _ _ hi
  have e14 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = stackArg s 17 :=
    (stackArg_entry hc.rsp _ _ (by decide)).trans h.a14
  have e15 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 = stackArg s 18 :=
    (stackArg_entry hc.rsp _ _ (by decide)).trans h.a15
  have a14 : stackArgAddr (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = off (fb s) 112 := by
    rw [stackArgAddr_eq _ 14, stackArgAddr_entry hc.rsp, off]
  have hsp : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rsp = off (kb s) privStack := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, fb_sub8]
  have hkk : off (kb s) privStack - BitVec.ofNat 64 Rsa.X86_64.stackBytes = kb s := BitVec.add_sub_cancel _ _
  have hdi : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rdi = s.gpr .rdi := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hc.rdi]
  have hsi' : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rsi = s.gpr .r8 := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hc.rsi]
  have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
  have dOr : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region).Disjoint (preR s) := by
    have := hq.dOr; simp only [outR] at this; rwa [hsi] at this
  refine ⟨priv_pre hp hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.withRegions_rd, a14, e14, e15]; rfl
  · have hoff : (off (kb s) privStack).toNat = (kb s).toNat + privStack := by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
    rw [hsp, hoff]; omega_using [hK1, e5, e6]
  · rw [hdi, hsi', a14]; exact (dKo.sub_left sA2).symm
  · rw [hdi, hsi', e14, e15]; exact dOr
  · rw [hE (show 12 < 14 by decide), hE (show 13 < 14 by decide), a14]
    exact (hp.dKs.sub_left sA2).symm
  · rw [hE (show 12 < 14 by decide), hE (show 13 < 14 by decide), e14, e15]; exact hq.dsr
  · rw [hsp, a14, hkk, hfb, off_off]
    exact Offset.base_disjoint (kb s) (by decide) (by omega_using [hF])
  · rw [hsp, e14, e15, hkk]
    exact hq.dKr.sub_left (Region.sub_prefix (by decide))
  · rw [stackArgAddr_entry hc.rsp, a14]
    exact Offset.base_disjoint (fb s) (by decide) (by omega_using [])
  · rw [e14, e15]; exact hq.wR
  · rw [e15, hE (show 3 < 14 by decide), hE (show 5 < 14 by decide)]
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hc.rcx]
    exact hq.hpl
  · have bo : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
        (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrR s) → len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
      fun hk ho hm hs hl => bytes_of_frame hfE hk ho hm hs.symm hl
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hc.rdx, hc.rcx, hE (show 2 < 14 by decide),
      hE (show 3 < 14 by decide), hE (show 4 < 14 by decide), hE (show 5 < 14 by decide), e14, e15, Nat.reduceAdd]
    rw [bo hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega_using []),
      bo hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega_using []),
      bo hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega_using []), wordsP_of_frame hq hfE]
    exact hq.key

theorem privP_covers {s t : State} (hp : DPre s) (hq : DPreP s) (h : CallAt s t) :
    Covers (privRdP s ++ privWr s) (t.rd ++ t.wr) ∧ Covers (privWr s) t.wr := by
  obtain ⟨c, cw⟩ := priv_covers hp h
  have e3 : frameBytes = 216 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨?_, cw⟩
  rw [privRdP, List.append_assoc]
  refine Covers.append_left (Covers.trans (fun a n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩) c)
    (Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ hfr, 112, rfl, by dsimp only; omega_using [e3]⟩
    · exact ⟨_, List.mem_append_left _ (by rw [h.rd]; exact hq.hpr), 0, z _, by dsimp only; omega_using []⟩

/-- The call of `vg_rsa_private_checked_precomputed`. -/
theorem privP_call (c : CrtImpl) {s t : State} (hp : DPre s) (hq : DPreP s) (h : SetupP s t) :
    WP isa (.call (privNameP c) (privCodeP c)) t fun t' => PostCall s t t' ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 :=
  let ⟨hc, hw⟩ := privP_covers hp hq h.call
  privWith_call (codeP_correct c c.pubOp.name) (fun _ _ h => h) (codeP_spSafe c _) (privCodeP_depth c) hp h.call
    (privP_pre hp hq h) hc hw

/-! ## After the call -/

/-- `out` and `msg_len` back to their slots: what the call in `code` leaves. -/
theorem restore_ok {s t t' : State} (hp : DPre s) (h : SetupP s t) (c : PostCall s t t') :
    WP isa (.block restore) t' fun u => PostPriv s u ∧ Keep [.r11] t' u := by
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hs : Scr t' (fb s) frameBytes := Scr.of_mem (by rw [c.wr]; exact List.mem_cons_self ..)
    (by unfold frameBytes at *; omega_arith)
  rw [restore, WP.block_append_iff]
  refine WP.mono (mvSlot_run c.rsp hs (.inr rfl) (d := oI) (e := oOut) (by decide) (by decide))
    fun u₁ ⟨hm₁, k₁⟩ => ?_
  refine WP.mono (mvSlot_run ((k₁.gpr (by decide)).trans c.rsp) (hs.congr k₁.2.2) (.inr rfl) (d := oNB) (e := oML)
    (by decide) (by decide)) fun u ⟨hm, k⟩ => ?_
  have kk := k₁.trans k
  have f : Frame [⟨off (fb s) oOut, 64 / 8⟩, ⟨off (fb s) oML, 64 / 8⟩] t'.mem u.mem := by
    rw [hm, hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have w : ∀ {d : Nat}, d + 8 ≤ oOut ∨ oML + 8 ≤ d → d + 8 ≤ frameBytes →
      word u.mem (fb s) d = word t.mem (fb s) d := fun h₁ h₂ => by
    rw [hm, hm₁, word_ww _ _ _ (by simp only [oOut, oML] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₂; omega_using [h₂]) (by decide),
      word_ww _ _ _ (by simp only [oOut, oML] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₂; omega_using [h₂]) (by decide)]
    exact c.keep h₂
  have hb : Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) = Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (kOf s) := by
    refine bytes_keep f (fun r hr => ?_) (by unfold kOf; omega_using [])
    have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dKo.sub_left (frame_sub s (by decide))).symm
    · exact (dKo.sub_left (frame_sub s (by decide))).symm
  refine ⟨⟨(kk.gpr (by decide)).trans c.rsp, kk.2.1.trans c.rd, kk.2.2.trans c.wr,
    c.mem.trans (f.sub fun r hr => ?_), ⟨?_, ?_, (w (.inr (by decide)) (by decide)).trans h.slots.sN,
      (w (.inr (by decide)) (by decide)).trans h.slots.sK, (w (.inr (by decide)) (by decide)).trans h.slots.sE,
      (w (.inr (by decide)) (by decide)).trans h.slots.sEl, (w (.inr (by decide)) (by decide)).trans h.slots.sD,
      (w (.inr (by decide)) (by decide)).trans h.slots.sDl, (w (.inr (by decide)) (by decide)).trans h.slots.sIn,
      (w (.inr (by decide)) (by decide)).trans h.slots.sScr⟩, ?_⟩, kk.mono (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stkR s, List.mem_cons_self .., frame_sub s (by decide)⟩
    · exact ⟨stkR s, List.mem_cons_self .., frame_sub s (by decide)⟩
  · rw [hm, word_ww _ _ _ (by decide) (by decide) (by decide), hm₁, word_writeW_self, c.keep (by decide)]
    exact h.slots.sI
  · rw [hm, word_writeW_self, hm₁, word_ww _ _ _ (by decide) (by decide) (by decide), c.keep (by decide)]
    exact h.slots.sNB
  · have hr := c.res
    rw [kk.gpr (r := .rax) (by decide)]
    revert hr
    cases privOut s <;> simp only [Spec.Rsa.writtenOutcome, hb] <;> exact id

/-! ## The function -/

/-- `vg_rsa_pkcs1_decrypt_precomputed`, from a state its contract allows:
`code`'s result. -/
theorem decP_ok (v : Compress) (c : CrtImpl) {s : State} (hp : DPre s) (hq : DPreP s) :
    WP isa (codeP (HH v) (privNameP c) (privCodeP c)) s fun s' => abiPreserved s s' ∧ decK.post s s' := by
  refine decWith_ok v hp (A := setup ++ stash) (B := .seq (.call (privNameP c) (privCodeP c)) (.block restore)) ?_
  have hA : WP isa (.block (setup ++ stash)) (allocState frameBytes s) fun t =>
      SetupP s t ∧ Keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (allocState frameBytes s) t := by
    rw [WP.block_append_iff]
    exact WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (setup_run hp) (by decide +kernel))
      fun t ⟨h, k⟩ => WP.mono (stash_ok hp hq h) fun u ⟨hu, ku⟩ => ⟨hu, (k.trans ku).mono (by decide)⟩
  refine WP.mono_mx (by decide +kernel) hA fun t₁ ⟨h₁, k₁⟩ hmx₁ => ?_
  refine WP.seq (WP.mono (privP_call c hp hq h₁) fun t₂ ⟨pc, hcs₂, hmx₂⟩ => ?_)
  refine WP.mono_mx (by decide) (restore_ok hp h₁ pc) fun u ⟨hpp, ku⟩ hmxu => ⟨hpp, fun r hr hr' => ?_, ?_⟩
  · rw [ku.cs (by decide) r hr, hcs₂ r hr, k₁.cs (by decide) r hr]
    simp only [allocState_gpr, hr', ↓reduceIte]
  · rw [hmxu, hmx₂, hmx₁]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
