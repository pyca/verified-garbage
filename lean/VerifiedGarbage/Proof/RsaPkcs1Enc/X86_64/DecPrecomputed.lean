module

public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
import VerifiedGarbage.Proof.Rsa.PreWords
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCT5
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCT
meta import VerifiedGarbage.Proof.Rsa.PreWords
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.CallSp
meta import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! ### `RsaPkcs1Enc.X86_64.DecPCT`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecPCall`, which only this module used -/

section

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
  obtain sA : Region.Sub ⟨stackArgAddr s 0, 136⟩ (argsP s) := Region.sub_prefix (by decide)
  obtain hrd' : ∀ r ∈ ([⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
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
  obtain ha := argP_in hq hrd t.wr hj
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
  obtain hF := fb_toNat hp
  obtain hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by unfold frameBytes at *; omega_arith)
  rw [stash, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mvSlot_run h.rsp hs (.inl rfl) (d := oOut) (e := oI) (by decide) (by decide))
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  refine WP.mono (mvSlot_run ((k₁.gpr (by decide)).trans h.rsp) (hs.congr k₁.2.2) (.inl rfl) (d := oML) (e := oNB)
    (by decide) (by decide)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain ho₂ : Outside (fb s) 0 frameBytes s.mem t₂.mem := by
    rw [hm₂, hm₁]
    exact Outside.ww (Outside.ww h.out _ (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)
  refine WP.mono (mvArg_run' hp hq ((k12.gpr (by decide)).trans h.rsp) (hs.congr k12.2.2) (k12.2.1.trans h.rd) ho₂
    (j := 17) (d := 112) (by decide) (by decide)) fun t₃ ⟨hm₃, k₃⟩ => ?_
  obtain k13 := k12.trans k₃
  obtain ho₃ : Outside (fb s) 0 frameBytes s.mem t₃.mem := by
    rw [hm₃]; exact Outside.ww ho₂ _ (by decide) (by decide) (by decide)
  refine WP.mono (mvArg_run' hp hq ((k13.gpr (by decide)).trans h.rsp) (hs.congr k13.2.2) (k13.2.1.trans h.rd) ho₃
    (j := 18) (d := 120) (by decide) (by decide)) fun t' ⟨hm', k'⟩ => ?_
  obtain k := k13.trans k'
  obtain ho : Outside (fb s) 0 frameBytes s.mem t'.mem := by
    rw [hm']; exact Outside.ww ho₃ _ (by decide) (by decide) (by decide)
  obtain w : ∀ {d : Nat}, (d + 8 ≤ oI ∨ oNB + 8 ≤ d) → d % 8 = 0 → d + 8 ≤ frameBytes → d + 8 ≤ 112 ∨ 128 ≤ d →
      word t'.mem (fb s) d = word t.mem (fb s) d := fun h₁ h₂ h₃ h₄ => by
    rw [hm', hm₃, hm₂, hm₁, word_ww _ _ _ (by omega_using [h₄]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by omega_using [h₄]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by simp only [oI, oNB] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide),
      word_ww _ _ _ (by simp only [oI, oNB] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₃; omega_using [h₃]) (by decide)]
  obtain regs : ∀ r : Reg, r ≠ .rax → t'.gpr r = t.gpr r := fun r hr => k.gpr (by simpa using hr)
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
  obtain hi := List.mem_range.mp hi
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
  obtain hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside hc.out) (callEntry_frame hc.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩
  have ⟨hK1, _⟩ := kb_toNat hp
  obtain hF := fb_toNat hp
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e5 : decStack = 3480 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 216 := rfl
  obtain hfb : fb s = off (kb s) (8 + privStack) := fb_eq s
  obtain sA2 : Region.Sub ⟨off (fb s) 112, 16⟩ (stkR s) := frame_sub s (by decide)
  obtain hE : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args hc _ _ hi
  obtain e14 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = stackArg s 17 :=
    (stackArg_entry hc.rsp _ _ (by decide)).trans h.a14
  obtain e15 : stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 = stackArg s 18 :=
    (stackArg_entry hc.rsp _ _ (by decide)).trans h.a15
  obtain a14 : stackArgAddr (t.callEntry.withRegions (privRdP s) (privWr s)) 14 = off (fb s) 112 := by
    rw [stackArgAddr_eq _ 14, stackArgAddr_entry hc.rsp, off]
  obtain hsp : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rsp = off (kb s) privStack := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, hc.rsp, fb_sub8]
  obtain hkk : off (kb s) privStack - BitVec.ofNat 64 Rsa.X86_64.stackBytes = kb s := BitVec.add_sub_cancel _ _
  obtain hdi : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rdi = s.gpr .rdi := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hc.rdi]
  obtain hsi' : (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rsi = s.gpr .r8 := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hc.rsi]
  obtain dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
  obtain dOr : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region).Disjoint (preR s) := by
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
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
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
  obtain hF := fb_toNat hp
  have hk2 := hp.k2
  have hsi := hp.hsi
  obtain hs : Scr t' (fb s) frameBytes := Scr.of_mem (by rw [c.wr]; exact List.mem_cons_self ..)
    (by unfold frameBytes at *; omega_arith)
  rw [restore, WP.block_append_iff]
  refine WP.mono (mvSlot_run c.rsp hs (.inr rfl) (d := oI) (e := oOut) (by decide) (by decide))
    fun u₁ ⟨hm₁, k₁⟩ => ?_
  refine WP.mono (mvSlot_run ((k₁.gpr (by decide)).trans c.rsp) (hs.congr k₁.2.2) (.inr rfl) (d := oNB) (e := oML)
    (by decide) (by decide)) fun u ⟨hm, k⟩ => ?_
  obtain kk := k₁.trans k
  obtain f : Frame [⟨off (fb s) oOut, 64 / 8⟩, ⟨off (fb s) oML, 64 / 8⟩] t'.mem u.mem := by
    rw [hm, hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  obtain w : ∀ {d : Nat}, d + 8 ≤ oOut ∨ oML + 8 ≤ d → d + 8 ≤ frameBytes →
      word u.mem (fb s) d = word t.mem (fb s) d := fun h₁ h₂ => by
    rw [hm, hm₁, word_ww _ _ _ (by simp only [oOut, oML] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₂; omega_using [h₂]) (by decide),
      word_ww _ _ _ (by simp only [oOut, oML] at h₁ ⊢; omega_using [h₁]) (by unfold frameBytes at h₂; omega_using [h₂]) (by decide)]
    exact c.keep h₂
  obtain hb : Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) = Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (kOf s) := by
    refine bytes_keep f (fun r hr => ?_) (by unfold kOf; omega_using [])
    obtain dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
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
  obtain hA : WP isa (.block (setup ++ stash)) (allocState frameBytes s) fun t =>
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

end

end

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on x86-64: constant time

`Decrypt.codeP` leaks what `Decrypt.code` leaks, and, in its call of
`vg_rsa_private_checked_precomputed`, `pre`'s address and length and the
modulus' values in it, which its contract (`decKP`) makes public: `stash`
and `restore` address only the frame and the stack arguments, the call is
constant time for its contract (`privP_ct`), and the rest is `code`'s
(`DecCT1.lean` … `DecCT5.lean`), with entry states that also agree on `pre`
(`XPd`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP codeP_correct)
open VG.Proof.Sha256.X86_64 (Compress)

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s contract, with `decK`'s
postcondition and its public data, with `pre`, `pre_len` and the modulus'
values in `pre`. -/
def decKP : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack).pre
  post := decK.post
  pub s₁ s₂ := decK.pub s₁ s₂ ∧ stackArg s₁ 17 = stackArg s₂ 17 ∧ stackArg s₁ 18 = stackArg s₂ 18 ∧
    Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 17) (s₁.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 17) (s₂.gpr .r8).toNat

/-- What entry states agree on with `a` besides `decK.pub`. -/
def XPd (a s : State) : Prop :=
  DPreP s ∧ stackArg s 17 = stackArg a 17 ∧ stackArg s 18 = stackArg a 18 ∧
    Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 17) (a.gpr .r8).toNat

def J0P (s t : State) : Prop := J0 s t ∧ DPreP s
def JSP (s t : State) : Prop := (SetupP s t ∧ CS s t) ∧ DPreP s
def JPC (s t : State) : Prop := ∃ t₀, SetupP s t₀ ∧ PostCall s t₀ t ∧ CS s t

theorem setupP_two : RelCT isa (Two (At XPd J0P)) (.block (setup ++ stash)) (Two (At XPd JSP)) :=
  two_blk [.rsp] (pins (J := J0P) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨h, -⟩; rw [h]; rfl)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨h, hq⟩ => by
      subst h
      rw [WP.block_append_iff]
      exact WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx, .r8, .r9] (setup_run hp) (by decide +kernel))
        fun t₁ ⟨h₁, k₁⟩ => WP.mono (stash_ok hp hq h₁) fun t' ⟨h', k'⟩ => ⟨⟨h', fun r hr hr' => by
          rw [k'.cs (by decide) r hr, k₁.cs (by decide) r hr]; simp only [allocState_gpr, hr', ↓reduceIte]⟩, hq⟩

/-- The modulus' values in `pre`, at the call. -/
theorem leakP_entry {s t : State} (hq : DPreP s) (h : CallAt s t) (rd wr : List Region) :
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions rd wr).mem (stackArg s 17) (s.gpr .r8).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 17) (s.gpr .r8).toNat := by
  have hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by decide)⟩
  have hle : Spec.Rsa.precomputedWords (s.gpr .r8).toNat ≤ (stackArg s 18).toNat := by
    rw [hq.hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, State.withRegions_mem]
  rw [← VG.Proof.Rsa.wordsAt_take _ _ hle, ← VG.Proof.Rsa.wordsAt_take _ _ hle, wordsP_of_frame hq hfE]

theorem privP_ct (c : CrtImpl) :
    RelCT isa (Two (At XPd JSP)) (.call (privNameP c) (privCodeP c)) fun _ _ => True := by
  refine RelCT.callEx (k := chkContractP) (codeP_correct c _) (Rsa.X86_64.codeP_constantTime c _)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, ⟨j₁, _⟩, hq₁⟩, ⟨s₂, S₂, ⟨j₂, _⟩, hq₂⟩⟩ => ?_
  obtain ⟨r₁, a₁, n₁, e₁⟩ := priv_view (rds := privRdP s₁) S₁ j₁.call
  obtain ⟨r₂, a₂, n₂, e₂⟩ := priv_view (rds := privRdP s₂) S₂ j₂.call
  obtain ⟨c₁, w₁⟩ := privP_covers S₁.p hq₁ j₁.call
  obtain ⟨c₂, w₂⟩ := privP_covers S₂.p hq₂ j₂.call
  have a14 : ∀ {s t : State}, SetupP s t → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 14 =
      stackArg s 17 := fun h => (stackArg_entry h.call.rsp _ _ (by decide)).trans h.a14
  have a15 : ∀ {s t : State}, SetupP s t → stackArg (t.callEntry.withRegions (privRdP s) (privWr s)) 15 =
      stackArg s 18 := fun h => (stackArg_entry h.call.rsp _ _ (by decide)).trans h.a15
  have kx : ∀ {s t : State}, SetupP s t →
      (t.callEntry.withRegions (privRdP s) (privWr s)).gpr .rcx = s.gpr .r8 := fun h => by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h.call.rcx]
  exact ⟨privRdP s₁, privWr s₁, privRdP s₂, privWr s₂, privP_pre S₁.p hq₁ j₁, privP_pre S₂.p hq₂ j₂,
    ⟨⟨List.map_inj_left.mp (r₁.trans r₂.symm), a₁.trans a₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩,
      by rw [a14 j₁, a14 j₂, S₁.2.2.1, S₂.2.2.1], by rw [a15 j₁, a15 j₂, S₁.2.2.2.1, S₂.2.2.2.1],
      by rw [a14 j₁, a14 j₂, kx j₁, kx j₂, leakP_entry hq₁ j₁.call, leakP_entry hq₂ j₂.call, S₁.2.2.2.2,
        S₂.2.2.2.2]⟩,
    c₁, w₁, c₂, w₂, by rw [j₁.call.rsp, j₂.call.rsp, S₁.fb, S₂.fb]⟩

theorem privP_two (c : CrtImpl) :
    RelCT isa (Two (At XPd JSP)) (.call (privNameP c) (privCodeP c)) (Two (At XPd JPC)) :=
  two_then (privP_ct c) fun _ t hp ⟨⟨h, hcs⟩, hq⟩ => WP.mono (privP_call c hp hq h) fun _ ⟨pc, hcs', _⟩ =>
    ⟨t, h, pc, fun r hr hr' => (hcs' r hr).trans (hcs r hr hr')⟩

theorem restore_two : RelCT isa (Two (At XPd JPC)) (.block restore) (Two (At XPd JP)) :=
  two_blk [.rsp] (pins (J := JPC) [(.rsp, fb)] (by
      simp only [List.mem_singleton]; rintro p rfl s t ⟨_, _, pc, _⟩; exact pc.rsp)
    (by simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun s t hp ⟨t₀, h, pc, hcs⟩ => WP.mono (restore_ok hp h pc) fun _ ⟨hpp, k⟩ =>
      ⟨hpp, fun r hr hr' => (k.cs (by decide) r hr).trans (hcs r hr hr')⟩

/-! ## The function -/

theorem bodyP_ct (v : Compress) (c : CrtImpl) :
    RelCT isa (Two (At XPd J0P)) (bodyP (HH v) (privNameP c) (privCodeP c)) fun _ _ => True :=
  RelCT.seq setupP_two (RelCT.seq (RelCT.seq (privP_two c) restore_two) (RelCT.seq dBuild_two (RelCT.seq hashD_two
    (RelCT.seq kdkMac_two (RelCT.seq clLoop_two (RelCT.seq amLoop_two (RelCT.seq maskPart_two
    (RelCT.seq alPart_two (RelCT.seq scanPart_two selPart_ct)))))))))

/-- `vg_rsa_pkcs1_decrypt_precomputed` is constant time but for its public
data. -/
theorem decP_constantTime (v : Compress) (c : CrtImpl) :
    ConstantTime isa decKP.pre decKP.pub (codeP (HH v) (privNameP c) (privCodeP c)) :=
  RelCT.constantTime (relCT_alloc ((bodyP_ct v c).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub, h17, h18, hl⟩, e₁, e₂⟩ =>
      ⟨s₁, ⟨s₁, ⟨⟨(dPreP_of h₁).1, pub_refl s₁⟩, (dPreP_of h₁).2, rfl, rfl, rfl⟩, e₁, (dPreP_of h₁).2⟩,
        ⟨s₂, ⟨⟨(dPreP_of h₂).1, hpub⟩, (dPreP_of h₂).2, h17.symm, h18.symm, hl.symm⟩, e₂, (dPreP_of h₂).2⟩⟩)
    fun _ _ h => h))

theorem decP_correct (v : Compress) (c : CrtImpl) (s : State) (h : decKP.pre s) :
    ∃ t s', Exec isa (codeP (HH v) (privNameP c) (privCodeP c)) s t s' ∧ abiPreserved s s' ∧ decKP.post s s' :=
  let ⟨hp, hq⟩ := dPreP_of h
  let ⟨t, s', he, hq'⟩ := decP_ok v c hp hq
  ⟨t, s', he, hq'⟩

/-- It writes `rsp` only in its frame's push and pop, and its callees' own. -/
theorem decP_spSafe (v : Compress) (c : CrtImpl) :
    (codeP (HH v) (privNameP c) (privCodeP c)).all (fun i => !isa.writesSp i) = true := by
  have h := afterPriv_spSafe v
  have h2 := Rsa.X86_64.codeP_spSafe c c.pubOp.name
  simp only at h h2
  simp only [codeP, bodyP, privCodeP, Code.all, h, h2, Bool.and_true]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end

/-! # `vg_rsa_pkcs1_decrypt_precomputed` on x86-64

`Decrypt.codeP`, which calls `vg_rsa_private_checked_precomputed` with the
key's precomputed values `pre`, against `vg_rsa_pkcs1_decrypt_precomputed`'s
contract (`decryptPrecomputed_verified`): `decKP` implies it
(`decP_implies`), with a state that meets it (`satisfiablePre`), which holds
a real key (`Proof/Rsa/PreKey.lean`); and what its registration's scrub needs
of the contract (`decryptPrecomputed_postOut`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec
open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.Bignum.X86_64 (leak_eq)

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [1, 0x4000, 1, 0x4100, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x20000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `0x10008`, and the
key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10008 i && Nat.blt i 0x100a0 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10008) / 8) 0 / 256 ^ ((i - 0x10008) % 8))
  else bif keyIn i then keyMem a else 0

/-- `decSatState` with the key and its precomputed values. -/
def preState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10008, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10008 a.toNat && Nat.blt a.toNat 0x100a0) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 1 ∧ stackArg preState 1 = 0x4000 ∧ stackArg preState 2 = 1 ∧ stackArg preState 3 = 0x4100 ∧ stackArg preState 4 = 64 ∧ stackArg preState 5 = 0x4200 ∧ stackArg preState 6 = 32 ∧ stackArg preState 7 = 0x4300 ∧ stackArg preState 8 = 32 ∧ stackArg preState 9 = 0x4400 ∧ stackArg preState 10 = 32 ∧ stackArg preState 11 = 0x4500 ∧ stackArg preState 12 = 32 ∧ stackArg preState 13 = 0x4600 ∧ stackArg preState 14 = 32 ∧ stackArg preState 15 = 0x20000 ∧ stackArg preState 16 = 0x420 ∧ stackArg preState 17 = 0x4800 ∧ stackArg preState 18 = 24 := by
  decide

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17, stackArg s 18] := rfl

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack).pre s := by
  refine ⟨preState, ?_⟩
  rw [show decStack = 3480 from rfl]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_nineteen, List.append_eq]
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := pre_args
  have ha : stackArgAddr preState 0 = 0x10008 := by decide
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, ha]
  sig_and_intros
  rotate_right
  · rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      show BitVec.toNat (24 : BitVec 64) = 24 from rfl]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## The code -/

theorem decP_implies : decKP.Implies (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack) where
  pre := fun _ h => h
  post := by
    rw [show decStack = 3480 from rfl]
    sig_implies_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decKP, decK, stackArgs_nineteen, List.append_eq, List.range,
      List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    rw [show decStack = 3480 from rfl] at h
    sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_nineteen, List.append_eq, List.range,
      List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16, a17, a18⟩ := h
    obtain ⟨hne, hlk⟩ := List.append_inj hl (by
      simp only [List.length_map, List.length_append, Proof.Rsa.bytesAt_length', h8, a0])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h8]) hne
    refine ⟨⟨?_, by simp only [stackArgs_seventeen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16], hn, he⟩, a17, a18, hlk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := satisfiablePre

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling
`vg_rsa_private_checked_precomputed` for the implementation `c` of the CRT,
meets its contract. -/
theorem decryptPrecomputed_verified (v : Compress) (c : Proof.Rsa.X86_64.CrtImpl) :
    Verified target (codeP (HH v) (privNameP c) (privCodeP c))
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi decStack) :=
  Verified.of_correct (k := decKP) (decP_correct v c) (decP_constantTime v c) decP_implies

/-! ## Without secret residue -/

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem decryptPrecomputed_postOut (stack : Nat) :
    VG.X86_64.Scrub.PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 64) :=
  VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) VG.X86_64.Scrub.ScrubAbi.plain
    fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 24) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨msgLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨e, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨eLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨input, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨inputLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dp, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dpLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dq, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨dqLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qinvLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    have hol : outLen.toNat = nLen.toNat := hpre.2.1
    have hby : Spec.Rsa.bytesAt m₂ out nLen.toNat = Spec.Rsa.bytesAt m₁ out nLen.toNat :=
      VG.Proof.Rsa.X86_64.bytesAt_agree (by simp only [Elem.size]; omega_using [hol])
        (by have := outLen.isLt; simp only [Elem.size]; omega_using []) hb.1
    have hw : Spec.Rsa.wordsAt m₂ msgLen 1 = Spec.Rsa.wordsAt m₁ msgLen 1 := by
      simp only [Spec.Rsa.wordsAt, List.range, List.range.loop, List.map_cons, List.map_nil, Nat.mul_zero,
        BitVec.add_zero]
      rw [VG.Proof.Rsa.X86_64.readW_agree (by decide) (by decide) hb.2.1]
    replace h : Spec.RsaPkcs1Enc.writtenMsg m₁ out msgLen nLen.toNat r _ := h
    show Spec.RsaPkcs1Enc.writtenMsg m₂ out msgLen nLen.toNat r _
    revert h
    generalize Spec.RsaPkcs1Enc.decrypt _ _ _ _ _ _ _ _ _ = o
    cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsg, hby, hw] <;> exact id

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
