module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

-- separate module: it needs only the correctness proofs, so it builds alongside `SignCCt.lean`

/-!
# `vg_rsa_pss_sign_precomputed` on x86-64: the call with `pre`

`signCP` is `signC` but for its call, of `vg_rsa_private_checked_precomputed`,
which it also gives the key's precomputed values `pre` and `pre_len` (our
stack arguments 18 and 19) as its stack arguments 14 and 15, in the frame's
words 14 and 15 (`privArgsP_ok`); nothing reads those after the call. From a
state that `vg_rsa_pss_sign_precomputed`'s contract allows (`SPre` and
`PreP`, `preSP_of`), the call meets that function's contract (`privP_pre`),
and so `signCP` writes what `signC` writes (`signCP_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (chkContract chkContractP)

theorem stackArgs_twenty (s : State) :
    List.map (stackArg s) (List.range 20) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19] := rfl

/-- `vg_rsa_pss_sign_precomputed`'s contract, with the tables `tsH` and
`tsG`. -/
abbrev pspec (tsH tsG : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) signStack

/-! ## The precondition -/

/-- `pre`, of `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 18, (stackArg s 19).toNat * 8⟩

/-- The stack arguments, with `pre` and `pre_len`. -/
abbrev argsP (s : State) : Region := ⟨stackArgAddr s 0, 160⟩

/-- What `vg_rsa_pss_sign_precomputed`'s contract adds to `SPre`: `pre`,
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
  wR : (stackArg s 18).toNat + (stackArg s 19).toNat * 8 ≤ 2 ^ 64
  hpl : (stackArg s 19).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 1).toNat (stackArg s 3).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 18) (stackArg s 19).toNat)

theorem preSP_of {tsH tsG : List FnTable} {s : State} (h : (pspec tsH tsG).pre s) :
    SPre tsH tsG s ∧ PreP s := by
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, tabFns] at h
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, signStack, stackArgs_twenty, List.append_eq, tabFns, Sig.tableRegion] at h
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr dOn dOe dOp dOq dOdp dOdq dOqi dOdg dOsa dOs dOr dOtH dOtG dOa
    dns des dps dqs ddps ddqs dqis ddgs dsas dsr dstH dstG dsa
    dRo dRn dRe dRp dRq dRdp dRdq dRqi dRdg dRsa dRs dRr dRtH dRtG dRa
    dKo dKn dKe dKp dKq dKdp dKdq dKqi dKdg dKsa dKs dKr dKtH dKtG dKa
    wO wN wE wP wQ wDp wDq wQi wDg wSa wS wR wTH wTG lv hsi L1 L2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsw hpl key
  have sA : Region.Sub ⟨stackArgAddr s 0, 144⟩ (argsP s) := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp2], tabH, tabG, hsy, fun r hr => ?_, ⟨160, by decide, by rw [hrd]; simp⟩, hwr,
    dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOtH, dOtG, (dOa.symm.sub_left sA).symm,
    dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dstH, dstG, (dsa.symm.sub_left sA).symm,
    dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRtH, dRtG, (dRa.symm.sub_left sA).symm,
    dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKtH, dKtG, (dKa.symm.sub_left sA).symm,
    wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, wTH, wTG, lv, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil,
    hdql, hsw, h⟩,
    ⟨by rw [hrd]; simp, by rw [hrd]; simp, dKa, dOa, dsa, dKr, dOr, dsr, wR, hpl, key⟩⟩
  rw [hrd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]

variable {tsH tsG : List FnTable}

/-! ## The arguments of the call -/

theorem argAddr_sub (s : State) (j : Nat) : stackArgAddr s j - stackArgAddr s 0 = BitVec.ofNat 64 (8 * j) := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem argP_in {s u : State} (hq : PreP s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 20) :
    InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := by
  refine ⟨argsP s, List.mem_append_left _ (by rw [hrd]; exact hq.hargs), ?_⟩
  show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ 160
  rw [argAddr_sub, BitVec.toNat_ofNat]; omega_using [hj]

theorem argP_val {s : State} (hq : PreP s) {m : Mem} (hM : Frame (wrR s) s.mem m) {j : Nat} (hj : j < 20) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hM.readW (r := argsP s) (by
      show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ 160
      rw [argAddr_sub, BitVec.toNat_ofNat]; omega_using [hj])
    (in_apart hq.dKa hq.dOa hq.dsa.symm) (by decide)

/-- Stack argument `j` to the frame's bytes at `d`. -/
theorem cpyArgP_ok {s : State} (hp : SPre tsH tsG s) (hq : PreP s) {u : State} {S : Addr} (L : Lay u (fb s) S)
    (hrd : u.rd = s.rd) (hM : Frame (wrR s) s.mem u.mem) {j d : Nat} (hj : j < 20) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) := by
  have hF := fb_toNat hp
  have := hp.sp2
  have hin : InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
    rw [argAddr]; exact argP_in hq hrd hj
  refine WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl
    |> WP.mono <| fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  have hv : u.mem.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
    rw [argAddr]; exact argP_val hq hM hj
  xrun [arg, ea_sp, L.rsp, hin, hv, L.st (d := d) hd]

/-- The stack arguments of `vg_rsa_private_checked_precomputed`: those of
`vg_rsa_private_checked`, then `pre` and `pre_len`. -/
def pArgP (s : State) (i : Nat) : BitVec 64 := if i < 14 then pArg s i else stackArg s (i + 4)

/-- The private-key operation's arguments, with `pre`: `privArgs_ok`, then
`pre` and `pre_len` to the frame's words 14 and 15. -/
theorem privArgsP_ok {s : State} (hp : SPre tsH tsG s) (hq : PreP s) {u : State}
    (L : Lay u (fb s) (stackArg s 14)) (hrd : u.rd = s.rd) (hw : u.wr = frR s :: s.wr)
    (hM : Frame (wrR s) s.mem u.mem)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 14) V W)
    (h16 : W 16 = s.gpr .rdi) (h17 : W 17 = s.gpr .rcx) (h18 : W 18 = s.gpr .rdx) (h19 : W 19 = s.gpr .r8)
    (h20 : W 20 = s.gpr .r9) (h22 : W 22 = stackArg s 15) :
    WP isa (.block privArgsP) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 14) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 14) V W' ∧ (∀ i < 16, W' i = pArgP s i) ∧
        (∀ i < nW, 16 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = s.gpr .rdi ∧ u'.gpr .rsi = s.gpr .rcx ∧ u'.gpr .rdx = s.gpr .rdx ∧ u'.gpr .rcx = s.gpr .rcx ∧
      u'.gpr .r8 = s.gpr .r8 ∧ u'.gpr .r9 = s.gpr .r9 := by
  rw [privArgsP, WP.block_append_iff]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (privArgs_ok hp L hrd (argsKept_of hp hM) R h16 h17 h18 h19 h20 h22))
    fun u1 ⟨⟨k1, L1, ⟨W1, R1, ha1, hb1⟩, d1, s1, x1, c1, e1, n1⟩, f1⟩ => ?_
  have hM1 := frame_keep hp hw L.rsp hM f1
  have hrd1 : u1.rd = s.rd := k1.2.1.trans hrd
  rw [show ([.mov .rax (.mem (arg 18)), .store (sp 112) .rax, .mov .rax (.mem (arg 19)), .store (sp 120) .rax] :
      List Instr) = [.mov .rax (.mem (arg 18)), .store (sp 112) .rax] ++
        [.mov .rax (.mem (arg 19)), .store (sp 120) .rax] from rfl, WP.block_append_iff]
  refine WP.mono (cpyArgP_ok hp hq L1 hrd1 hM1 (j := 18) (d := 112) (by decide) (by decide))
    fun u2 ⟨k2, hm2⟩ => ?_
  have R2 := R1.wf L1.geo (k := 14) (by decide) (stackArg s 18)
  simp only [Nat.reduceMul, ← hm2] at R2
  have L2 : Lay u2 (fb s) (stackArg s 14) :=
    L1.of_rep' R1 R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2
  have hM2 : Frame (wrR s) s.mem u2.mem := hm2 ▸ hM1.trans ((frame_w hp (Frame.refl _ _) (d := 112) (by decide) _).sub
    fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩)
  refine WP.mono (cpyArgP_ok hp hq L2 (k2.2.1.trans hrd1) hM2 (j := 19) (d := 120) (by decide) (by decide))
    fun u3 ⟨k3, hm3⟩ => ?_
  have R3 := R2.wf L2.geo (k := 15) (by decide) (stackArg s 19)
  simp only [Nat.reduceMul, ← hm3] at R3
  have g : ∀ r, r ≠ .rax → u3.gpr r = u1.gpr r := fun r hr => by
    rw [k3.gpr (by simpa using hr), k2.gpr (by simpa using hr)]
  refine ⟨(k1.trans (k2.trans k3)).mono (by decide), L2.of_rep' R2 R3 (by simp [upd]) (k3.gpr (by decide)) k3.2.2,
    ⟨_, R3, fun i hi => ?_, fun i hi h16' => ?_⟩, by rw [g _ (by decide), d1], by rw [g _ (by decide), s1],
    by rw [g _ (by decide), x1], by rw [g _ (by decide), c1], by rw [g _ (by decide), e1], by rw [g _ (by decide), n1]⟩
  · simp only [upd, pArgP]
    rcases (show i < 14 ∨ i = 14 ∨ i = 15 by omega_using [hi]) with h | rfl | rfl
    · rw [ifn (by omega_using [h]), ifn (by omega_using [h]), ifp h]; exact ha1 i h
    · simp
    · simp
  · simp only [upd]
    rw [ifn (by omega_using [h16']), ifn (by omega_using [h16'])]; exact hb1 i hi (by omega_using [h16'])

/-! ## The call -/

/-- What `vg_rsa_private_checked_precomputed` reads: `pRd`, its stack
arguments 14 and 15, and `pre`. -/
def pRdP (s : State) : List Region := pRd s ++ [⟨off (fb s) 112, 16⟩, preR s]

theorem wordsP_of_frame {s : State} (hq : PreP s) {m : Mem} (hf : Frame (wrR s) s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 18) (stackArg s 19).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 18) (stackArg s 19).toNat := by
  have hl := hq.wR
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (r := preR s) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi]))
    (in_apart hq.dKr hq.dOr hq.dsr.symm) (by decide)

/-- The call meets `vg_rsa_private_checked_precomputed`'s contract. -/
theorem privP_pre {s t : State} (hp : SPre tsH tsG s) (hq : PreP s) (hsp : t.gpr .rsp = fb s)
    (hM : Frame (wrR s) s.mem t.mem)
    (hargs : ∀ i < 16, word t.mem (fb s) (8 * i) = pArgP s i) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContractP.pre (t.callEntry.withRegions (pRdP s) (pWr s)) := by
  have h14 : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i := fun i hi => by
    rw [hargs i (by omega_using [hi])]; simp only [pArgP, hi, ↓reduceIte]
  have hE : ∀ i < 16, stackArg (t.callEntry.withRegions (pRdP s) (pWr s)) i = pArgP s i :=
    fun i hi => (stackArg_call hp hsp _ _ hi).trans (hargs i hi)
  have e2 := hE 2 (by decide)
  have e3 := hE 3 (by decide)
  have e4 := hE 4 (by decide)
  have e5 := hE 5 (by decide)
  have e12 := hE 12 (by decide)
  have e13 := hE 13 (by decide)
  have e14 := hE 14 (by decide)
  have e15 := hE 15 (by decide)
  simp only [pArgP, pArg, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd] at e2 e3 e4 e5 e12 e13 e14 e15
  have a14 : stackArgAddr (t.callEntry.withRegions (pRdP s) (pWr s)) 14 = off (fb s) 112 :=
    stackArgAddr_callj hsp _ _ 14
  have hX : (t.callEntry.withRegions (pRdP s) (pWr s)).gpr .rsp = fb s - 8 := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, hsp]
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions (pRdP s) (pWr s)).gpr r = t.gpr r :=
    fun hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have hF := fb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have hsb : Rsa.X86_64.stackBytes = 3256 := rfl
  have h392 : frameBytes = 392 := rfl
  have c2 : oRsa = 8192 := rfl
  have hf8 := fb_sub8' hp
  have hsc : (stackArg s 15 - 1024#64).toNat = (stackArg s 15).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_using [hsl]
  have hKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by rw [← hp.hsi]; exact hp.dKo
  have sA2 : Region.Sub ⟨off (fb s) 112, 16⟩ (stkR s) :=
    fun a h => frame_sub s a (Offset.sub_base (fb s) (d := 112) (n := 16) (k := frameBytes) (by decide) a h)
  have sR : Region.Sub ⟨off (stackArg s 14) oRsa, (stackArg s 15 - 1024#64).toNat * 8⟩ (scrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega_using [hsl, c2])
  have sStk : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 Rsa.X86_64.stackBytes, Rsa.X86_64.stackBytes⟩ (stkR s) := by
    simp only [stkR, fb, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (wrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret8_sub s⟩)
  have b : ∀ {R : Region}, (stkR s).Disjoint R → (outR s).Disjoint R → R.Disjoint (scrR s) → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
    fun hK hO hS hl => bytesAt_frame fSE (in_apart hK hO hS) hl
  refine ⟨priv_pre hp hsp h14 hdi hsi hdx hcx h8 h9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.withRegions_rd, a14, e14, e15]; rfl
  · rw [hX, hf8]; omega_using [hF, h392]
  · rw [g (by decide), g (by decide), hdi, hsi, a14]
    exact (hKo.sub_left sA2).symm
  · rw [g (by decide), g (by decide), hdi, hsi, e14, e15, ← hp.hsi]
    exact hq.dOr
  · rw [e12, e13, a14]
    exact ((hp.dKs.sub_left sA2).sub_right sR).symm
  · rw [e12, e13, e14, e15]
    exact hq.dsr.sub_left sR
  · rw [hX, a14]
    refine Region.Disjoint.sub_right (Region.Disjoint.sub_left
      (Offset.base_disjoint_below (fb s) (n := 3264) (k := 128) (by omega_using [])).symm ?_)
      (Offset.sub_base (fb s) (d := 112) (n := 16) (k := 128) (by decide))
    simp only [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Offset.sub_below _ (by decide) (by decide)
  · rw [hX, e14, e15]
    exact hq.dKr.sub_left sStk
  · rw [stackArgAddr_call hsp, a14]
    exact Offset.base_disjoint (fb s) (e := 112) (n := 16) (k := 112) (Nat.le_refl _) (by decide)
  · rw [e14, e15]; exact hq.wR
  · rw [e15, e3, e5, g (by decide), hcx]; exact hq.hpl
  · simp only [State.withRegions_mem, g (show Reg.rdx ≠ .rsp by decide), g (show Reg.rcx ≠ .rsp by decide), hdx, hcx,
      e2, e3, e4, e5, e14, e15]
    rw [b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKn hp.dOn hp.dns (by have := hp.wN; dsimp only; omega_using []),
      b (R := ⟨stackArg s 0, (stackArg s 1).toNat⟩) hp.dKp hp.dOp hp.dps (by have := hp.wP; dsimp only; omega_using []),
      b (R := ⟨stackArg s 2, (stackArg s 3).toNat⟩) hp.dKq hp.dOq hp.dqs (by have := hp.wQ; dsimp only; omega_using []),
      wordsP_of_frame hq fSE]
    exact hq.key

theorem privP_covers {s t : State} (hp : SPre tsH tsG s) (hq : PreP s) (hrd : t.rd = s.rd)
    (hwr : t.wr = frR s :: s.wr) :
    Covers (pRdP s ++ pWr s) (t.rd ++ t.wr) ∧ Covers (pWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hk1 := hp.k1
  have hsi := hp.hsi
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc : (stackArg s 15 - 1024#64).toNat = (stackArg s 15).toNat - 1024 := by
    rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_using [hsl]
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega_using [hsi]⟩
    · exact ⟨_, hscr, oRsa, rfl, by dsimp only; rw [hsc]; omega_using [hsl, c2]⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  simp only [pRdP, pRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hscr, oEm, rfl, by dsimp only; omega_using [hsl, c1]⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, hin _ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_using []⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩
  · exact ⟨_, List.mem_append_right _ hfr, 112, rfl, by dsimp only; decide⟩
  · exact ⟨_, hin _ hq.hpr, 0, z _, by dsimp only; omega_using []⟩

/-- `vg_rsa_private_checked_precomputed`'s arguments and call. -/
theorem privStepP_ok {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContractP.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContractP.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State} (hp : SPre tsH tsG s)
    (hq : PreP s) : PStep privArgsP privN privC s := by
  intro u V W L hrd hw hM R h16 h17 h18 h19 h20 h22
  have hk2 := hp.k2
  refine WP.seq (WP.mono_mx (by decide) (WP.keepIn (by decide) (by exact Nat.zero_le 16)
    (privArgsP_ok hp hq L hrd hw hM R h16 h17 h18 h19 h20 h22))
    fun u2 ⟨⟨k10, L10, ⟨W2, R10, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f10⟩ hx10 => ?_)
  have hw10 : u2.wr = frR s :: s.wr := k10.2.2.trans hw
  have hrd10 : u2.rd = s.rd := k10.2.1.trans hrd
  have hM10 := frame_keep hp hw L.rsp hM f10
  have ha : ∀ i < 16, word u2.mem (fb s) (8 * i) = pArgP s i :=
    fun i hi => (R10.fr i (by unfold nW frameBytes; omega_arith)).trans (hW2a i hi)
  have h14 : ∀ i < 14, word u2.mem (fb s) (8 * i) = pArg s i := fun i hi => by
    rw [ha i (by omega_using [hi])]; simp only [pArgP, hi, ↓reduceIte]
  obtain ⟨hc, hcw⟩ := privP_covers hp hq hrd10 hw10
  refine WP.mono (privWith_call (k := chkContractP) (fun _ _ h => h) hv hspC hdC hp L10.rsp hM10 h14 h2di h2dx h2cx
    h2r8 h2r9 (privP_pre hp hq L10.rsp hM10 ha h2di h2si h2dx h2cx h2r8 h2r9) hc hcw)
    fun u3 ⟨rd3, wr3, cs3, mx3, _, hk3, hout3⟩ => ?_
  have R3' : Rep u3.mem (fb s) (stackArg s 14) V W2 := R10.of_keep L10.geo fun x hx => hk3 x hx
  have hem : Spec.Rsa.bytesAt u2.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt u.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat :=
    Rep.bytes_eq R10 R (by unfold oEm oRsa; omega_arith)
  refine ⟨W2, L10.of_rep' R10 R3' rfl (cs3 .rsp (by decide)) wr3, wr3.trans k10.2.2, fun r hr => ?_,
    by rw [mx3, hx10], R3', fun j h hj => hW2b j hj (by omega_arith), by rw [← hem]; exact hout3⟩
  have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
  have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
  have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
  rw [cs3 r h1, k10.gpr h2]

/-! ## The function -/

/-- `vg_rsa_pss_sign_precomputed`, from a state its contract allows:
`signC`'s result. -/
theorem signCP_ok {f : MdFns} {g : Impl.Mgf1.X86_64.Table.Fns} {privN : String} {privC : Prog isa}
    (hspE : ∀ i ∈ idxs, SpSafe (encode f (ofIdx i) g)) (hdE : ∀ i ∈ idxs, (encode f (ofIdx i) g).x86_64Depth ≤ encStack)
    (hv : ∀ s, chkContractP.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContractP.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State}
    (hp : SPre tsH tsG s) (hq : PreP s) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash} (E : ESel f g s i T Hs Gs) :
    WP isa (signCP f g privN privC) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      (signK tsH tsG).post s s' ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 :=
  signCWith_ok hspE hdE hp (privStepP_ok hv hspC hdC hp hq) E

end VG.Proof.RsaPss.X86_64
