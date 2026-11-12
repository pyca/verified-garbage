module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecTab
import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

-- separate module: it needs only the correctness proofs, so it builds alongside `DecCT.lean`

/-!
# `vg_rsa_oaep_decrypt_precomputed` on x86-64: the call with `pre`

`decBodyP` is `decBody` but for its call, of
`vg_rsa_private_checked_precomputed`, which it also gives the key's
precomputed values `pre` and `pre_len` (our stack arguments 19 and 20) as its
stack arguments 14 and 15, in the frame's words 14 and 15, `sScr` and `sSrc`
(`decHeadP_ok`). Across the call the frame's words are `privWP`, which `Lay`
does not allow (`sScr` is not `scratch`), so the call is `privDW_call`'s;
after it, `scratch` back to `sScr` restores `Lay` (`restoreTab_ok`), and the
rest is `decBody`'s (`decAfterTab_ok`). From a state that
`vg_rsa_oaep_decrypt_precomputed`'s contract allows (`DPreT` and `PreP`,
`preDP_of`), the call meets that function's contract (`privDP_pre`), and so
`decryptP` writes what `decrypt` writes (`decP_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifn ifp)
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract chkContractP)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK privNameP privCodeP privCodeP_ok privCodeP_spSafe privCodeP_depth)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable.X86_64 (tables fnsOf Coh tabOK_of held_tableOf)

theorem stackArgs_twentyone (s : State) :
    List.map (stackArg s) (List.range 21) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19, stackArg s 20] := rfl

/-- `vg_rsa_oaep_decrypt_precomputed`'s contract, with the tables `ts`. -/
abbrev pdspec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) decStack

/-! ## The precondition -/

/-- `pre`, of `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 19, (stackArg s 20).toNat * 8⟩

/-- The stack arguments, with `pre` and `pre_len`. -/
abbrev argsP (s : State) : Region := ⟨stackArgAddr s 0, 168⟩

/-- What `vg_rsa_oaep_decrypt_precomputed`'s contract adds to `DPreT`:
`pre`, the precomputed values of the key, and the stack arguments that give
it. -/
structure PreP (s : State) : Prop where
  hargs : argsP s ∈ s.rd
  hpr : preR s ∈ s.rd
  dKa : (stkD s).Disjoint (argsP s)
  dOa : (outR s).Disjoint (argsP s)
  dMa : (mlR s).Disjoint (argsP s)
  dsa : (scrD s).Disjoint (argsP s)
  dKr : (stkD s).Disjoint (preR s)
  dOr : (outR s).Disjoint (preR s)
  dMr : (mlR s).Disjoint (preR s)
  dsr : (scrD s).Disjoint (preR s)
  wR : (stackArg s 19).toNat + (stackArg s 20).toNat * 8 ≤ 2 ^ 64
  hpl : (stackArg s 20).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r8).toNat (stackArg s 2).toNat (stackArg s 4).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 19) (stackArg s 20).toNat)

theorem preDP_of {ts : List FnTable} {s : State} (h : (pdspec ts).pre s) : DPreT ts s ∧ PreP s := by
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq, tabFns] at h
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, decStack, RsaPkcs1Enc.X86_64.privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq, tabFns, Sig.tableRegion] at h
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabL' tabR' hsy hrd hwr dOM dOn dOe dOp dOq dOdp dOdq dOqi dOlb dOct dOs dOr dOtL dOt dOa
    dMn dMe dMp dMq dMdp dMdq dMqi dMlb dMct dMs dMr dMtL dMt dMa
    dns des dps dqs ddps ddqs dqis dlbs dcts dsr dstL dst dsa
    dRO dRM dRn dRe dRp dRq dRdp dRdq dRqi dRlb dRct dRs dRr dRtL dRt dRa
    dKO dKM dKn dKe dKp dKq dKdp dKdq dKqi dKlb dKct dKs dKr dKtL dKt dKa
    wO wM wN wE wP wQ wDp wDq wQi wL wC wS wR wTL wT lv hsi hcl el1 el2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsw hpl
  have sA : Region.Sub ⟨stackArgAddr s 0, 152⟩ (argsP s) := Region.sub_prefix (by decide)
  refine ⟨⟨⟨sp1, by omega, fun r hr => ?_, ⟨168, by decide, by rw [hrd]; simp⟩, hwr, dOM, dOn, dOe, dOp, dOq,
    dOdp, dOdq, dOqi, dOlb, dOct, dOs, (dOa.symm.sub_left sA).symm, dMn, dMe, dMp, dMq, dMdp, dMdq, dMqi, dMlb,
    dMct, dMs, (dMa.symm.sub_left sA).symm, dns, des, dps, dqs, ddps, ddqs, dqis, dlbs, dcts,
    (dsa.symm.sub_left sA).symm, dRO, dRM, dRs, dKO, dKM, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKlb, dKct, dKs,
    (dKa.symm.sub_left sA).symm, wO, wM, wN, wE, wP, wQ, wDp, wDq, wQi, wL, wC, wS, lv, hsi, hcl, el1, el2, pl1,
    pl2, ql1, ql2, hdpl, hqil, hdql, hsw, dOt, dMt, dst, dKt, wT, dOtL, dMtL, dstL, dKtL, wTL⟩,
    tabL', tabR', hsy.sublist (List.sublist_append_left _ _)⟩,
    ⟨by rw [hrd]; simp, by rw [hrd]; simp, dKa, dOa, dMa, dsa, dKr, dOr, dMr, dsr, wR, hpl, h⟩⟩
  rw [hrd]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> simp [h, tabL, tabR]

/-! ## The arguments of the call -/

theorem argP_in {s u : State} (hq : PreP s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 21) :
    InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 := by
  refine ⟨argsP s, List.mem_append_left _ (by rw [hrd]; exact hq.hargs), ?_⟩
  show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ 168
  rw [stackArgAddr_j s j, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega

theorem argP_val {s : State} (hq : PreP s) {m : Mem} (hf : FrD s m) {j : Nat} (hj : j < 21) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hf.readW' (r := argsP s) (by
      show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ 168
      rw [stackArgAddr_j s j, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega)
    hq.dKa hq.dOa hq.dMa hq.dsa

/-- A stack argument of `DPre`'s, in memory the code may leave. -/
theorem arg_valD {s : State} (hp : DPre s) {m : Mem} (hf : FrD s m) {j : Nat} (hj : j < 19) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hf.readW' (r := ⟨stackArgAddr s 0, 152⟩) (by
      show (stackArgAddr s j - stackArgAddr s 0).toNat + 8 ≤ 152
      rw [stackArgAddr_j s j, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega)
    hp.dKa hp.dOa hp.dMa hp.dsa

/-- A stack argument to the frame's bytes at `d`. -/
theorem argSlotE_ok {s u : State} (hp : DPre s) (he : EnvD s u) {j d : Nat}
    (hin : InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8) (hv : u.mem.readW (stackArgAddr s j) 64 = stackArg s j)
    (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (argSlot j d)) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes :=
    Scr.of_mem (by rw [he.wr]; exact List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  rw [← argAddr] at hin hv
  xrun [argSlot, arg, ea_sp, he.rsp, hin, hv, hsc.st (d := d) hd]

/-- `Lay`, from what `EnvD` and `DPre` say, and `scratch` in `sScr`. -/
theorem Lay.of_envD {s t : State} (hp : DPre s) (he : EnvD s t) (hs : word t.mem (fb s) sScr = stackArg s 15) :
    Lay t (fb s) (stackArg s 15) := by
  have hF := fb_toNatD hp
  have := hp.sp1; have := hp.sp2
  have G' := hp.geo
  have hsl := hp.hsl
  have hk := hp.lv.1
  refine ⟨he.rsp, by rw [he.wr]; exact List.mem_cons_self .., ?_, ?_,
    ⟨⟨stackArg s 15, 0, (stackArg s 16).toNat * 8, by rw [he.wr]; simp [scrD], (BitVec.add_zero _).symm,
      by unfold oRsa; omega, by have := hp.wS; omega⟩, G'.Sw⟩, hs, G'.dFS, G'.dRS⟩
  · unfold decStack privStack at *; unfold frameBytes at *; omega
  · unfold frameBytes at *; omega

/-- The frame's words at the call: `privW`, with `pre` and `pre_len` in
words 14 and 15. -/
def privWP (s : State) : Nat → BitVec 64 := upd (upd (privW s) 14 (stackArg s 19)) 15 (stackArg s 20)

theorem privWP_lt {s : State} {i : Nat} (hi : i < 14) : privWP s i = privW s i := by
  simp only [privWP, upd]; rw [ifn (by omega), ifn (by omega)]

/-- The prologue, the arguments of `vg_rsa_private_checked_precomputed`, and
`pre` and `pre_len` to the frame's words 14 and 15. -/
theorem decHeadP_ok {s : State} (hp : DPre s) (hq : PreP s) :
    WP isa (.block (decPrologue ++ privArgs ++ argSlot 19 sScr ++ argSlot 20 sSrc)) (allocState frameBytes s)
      (DCall s (privWP s)) := by
  have G' := hp.geo
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (decHead_ok hp) fun t0 h0 => ?_
  refine WP.mono (wp_good (block_good _ rfl) (argSlotE_ok hp h0.he (j := 19) (d := sScr)
    (argP_in hq h0.he.rd (by decide)) (argP_val hq h0.he.fr (by decide)) (by decide)))
    fun t1 ⟨⟨k1, hm1⟩, sp1, mx1, f1⟩ => ?_
  have he1 := h0.he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  have R1 : Rep t1.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o))
      (upd (privW s) 14 (stackArg s 19)) := hm1 ▸ h0.R.wf G' (k := 14) (by decide) _
  refine WP.mono (wp_good (block_good _ rfl) (argSlotE_ok hp he1 (j := 20) (d := sSrc)
    (argP_in hq he1.rd (by decide)) (argP_val hq he1.fr (by decide)) (by decide)))
    fun t2 ⟨⟨k2, hm2⟩, sp2, mx2, f2⟩ => ?_
  have he2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  have R2 : Rep t2.mem (fb s) (stackArg s 15) (fun o => s.mem (off (stackArg s 15) o)) (privWP s) :=
    hm2 ▸ R1.wf G' (k := 15) (by decide) _
  have g : ∀ {r : Reg}, r ≠ .rax → t2.gpr r = t0.gpr r := fun hr => by
    rw [k2.gpr (by simpa using hr), k1.gpr (by simpa using hr)]
  exact ⟨he2, R2, fun i hi => privWP_lt hi, by rw [g (by decide), h0.rdi], by rw [g (by decide), h0.rsi],
    by rw [g (by decide), h0.rdx], by rw [g (by decide), h0.rcx], by rw [g (by decide), h0.r8],
    by rw [g (by decide), h0.r9]⟩

/-! ## The call -/

/-- What `vg_rsa_private_checked_precomputed` reads: `privRdD`, its stack
arguments 14 and 15, and `pre`. -/
def privRdDP (s : State) : List Region := privRdD s ++ [⟨off (fb s) 112, 16⟩, preR s]

theorem wordsP_of_frame {s : State} (hq : PreP s) {m : Mem} (hf : FrD s m) :
    Spec.Rsa.wordsAt m (stackArg s 19) (stackArg s 20).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 19) (stackArg s 20).toNat := by
  have hl := hq.wR
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW' (r := preR s) (Offset.contains_base _ (by omega) (by omega)) hq.dKr hq.dOr hq.dMr hq.dsr

/-- The memory at the call's entry. -/
theorem frD_entry {s t : State} (he : EnvD s t) : FrD s t.callEntry.mem := by
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  exact he.fr.trans (hfe.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)

theorem privDP_args {s t : State} (hp : DPre s) (h : DCall s (privWP s) t) (rd wr : List Region) {i : Nat}
    (hi : i < 16) : stackArg (t.callEntry.withRegions rd wr) i = privWP s i := by
  have hF := fb_toNatD hp
  rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold decStack privStack frameBytes at *; omega_arith) _ _
    (by have := hp.sp2; unfold frameBytes at *; omega_arith)]
  exact h.R.rd i rfl (by unfold nW frameBytes; omega_arith)

/-- The call meets `vg_rsa_private_checked_precomputed`'s contract. -/
theorem privDP_pre {s t : State} (hp : DPre s) (hq : PreP s) (h : DCall s (privWP s) t) :
    chkContractP.pre (t.callEntry.withRegions (privRdDP s) (privWrD s)) := by
  have e : ∀ i, i < 16 → stackArg (t.callEntry.withRegions (privRdDP s) (privWrD s)) i = privWP s i :=
    fun i hi => privDP_args hp h _ _ hi
  have e3 := e 3 (by decide)
  have e5 := e 5 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e4 := e 4 (by decide)
  have e12 := e 12 (by decide)
  have e13 := e 13 (by decide)
  have e14 := e 14 (by decide)
  have e15 := e 15 (by decide)
  simp only [privWP, privW, upd, Nat.reduceEqDiff, ↓reduceIte] at e1 e2 e3 e4 e5 e12 e13 e14 e15
  have a14 : stackArgAddr (t.callEntry.withRegions (privRdDP s) (privWrD s)) 14 = off (fb s) 112 := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, h.he.rsp, off]
    rw [show 8 * (14 + 1) = 8 + 112 by rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  have hX : (t.callEntry.withRegions (privRdDP s) (privWrD s)).gpr .rsp = fb s - 8 := by
    simp only [State.withRegions_gpr, State.callEntry_rsp, h.he.rsp]
  have g : ∀ {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions (privRdDP s) (privWrD s)).gpr r = t.gpr r :=
    fun hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have hF := fb_toNatD hp
  have := hp.sp1; have := hp.sp2
  have hk2 := hp.lv.2
  have ⟨hK1, hK2⟩ := kbD_toNat hp
  have hfb : fb s = off (kbD s) (8 + privStack) := fb_eqD s
  have e5' : decStack = 3560 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 296 := rfl
  have sA2 : Region.Sub ⟨off (fb s) 112, 16⟩ (stkD s) :=
    fun a h => frame_subD s a (Offset.sub_base (fb s) (d := 112) (n := 16) (k := frameBytes) (by decide) a h)
  have sK : Region.Sub ⟨fb s - 8 - BitVec.ofNat 64 privStack, privStack⟩ (stkD s) := by
    rw [fb_sub8D, show off (kbD s) privStack - BitVec.ofNat 64 privStack = kbD s from BitVec.add_sub_cancel _ _]
    exact Region.sub_prefix (by omega_arith)
  have fE := frD_entry h.he
  have b : ∀ {p : Addr} {len : Nat}, (stkD s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrD s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hm hs hl => FrD.bytes fE hk ho hm hs.symm hl
  have em := emD_sub hp
  have rs := rsaD_sub hp
  refine ⟨privD_pre hp ⟨h.he, h.R, fun i hi => privWP_lt hi, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.withRegions_rd, a14, e14, e15]; rfl
  · have hoff : (off (kbD s) privStack).toNat = (kbD s).toNat + privStack := by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
    rw [hX, fb_sub8D, hoff]; omega_arith
  · rw [g (by decide), g (by decide), h.rdi, h.rsi, a14]
    exact ((hp.dKs.sub_left sA2).sub_right em).symm
  · rw [g (by decide), g (by decide), h.rdi, h.rsi, e14, e15]
    exact hq.dsr.sub_left em
  · rw [e12, e13, a14]
    exact ((hp.dKs.sub_left sA2).sub_right rs).symm
  · rw [e12, e13, e14, e15]
    exact hq.dsr.sub_left rs
  · rw [hX, a14]
    refine Region.Disjoint.sub_right (Region.Disjoint.sub_left
      (Offset.base_disjoint_below (fb s) (n := 3264) (k := 128) (by omega_arith)).symm ?_)
      (Offset.sub_base (fb s) (d := 112) (n := 16) (k := 128) (by decide))
    rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
    exact Offset.sub_below _ (by decide) (by decide)
  · rw [hX, e14, e15]
    exact hq.dKr.sub_left sK
  · rw [stackArgAddr_entryD h.he.rsp, a14]
    exact Offset.base_disjoint (fb s) (e := 112) (n := 16) (k := 112) (Nat.le_refl _) (by decide)
  · rw [e14, e15]; exact hq.wR
  · rw [e15, e3, e5, g (by decide), h.rcx]; exact hq.hpl
  · simp only [State.withRegions_mem, g (show Reg.rdx ≠ .rsp by decide), g (show Reg.rcx ≠ .rsp by decide), h.rdx,
      h.rcx, e2, e3, e4, e5, e14, e15]
    rw [b hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega),
      b hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega),
      b hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega),
      wordsP_of_frame hq fE]
    exact hq.key

theorem privDP_covers {s t : State} (hp : DPre s) (hq : PreP s) (h : DCall s (privWP s) t) :
    Covers (privRdDP s ++ privWrD s) (t.rd ++ t.wr) ∧ Covers (privWrD s) t.wr := by
  obtain ⟨c, w⟩ := privD_covers hp ⟨h.he, h.R, fun i hi => privWP_lt hi, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9⟩
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨Covers.append_left (Covers.append_left (fun a n ⟨r, hr, hc⟩ => c a n ⟨r, List.mem_append_left _ hr, hc⟩)
    (Covers.of_sub fun r hr => ?_)) w.right, w⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨frR s, List.mem_append_right _ (by rw [h.he.wr]; exact List.mem_cons_self ..), 112, rfl,
      by show 112 + 16 ≤ frameBytes; decide⟩
  · exact ⟨_, List.mem_append_left _ (by rw [h.he.rd]; exact hq.hpr), 0, z _, by dsimp only; omega⟩

/-- The call of `vg_rsa_private_checked_precomputed` for `c`. -/
theorem privDP_call (c : CrtImpl) {s t : State} (hp : DPre s) (hq : PreP s) (h : DCall s (privWP s) t) :
    WP isa (.call (privNameP c) (privCodeP c)) t fun t' => EnvD s t' ∧
      Rep t'.mem (fb s) (stackArg s 15) (fun o => t'.mem (off (stackArg s 15) o)) (privWP s) ∧
      Spec.Rsa.writtenOutcome t'.mem (off (stackArg s 15) oEm) (s.gpr .r8).toNat ((t'.gpr .rax).setWidth 32)
        (privOutD s) :=
  let ⟨hc, hw⟩ := privDP_covers hp hq h
  WP.mono (privDW_call (k := chkContractP) (fun _ _ h => h) (privCodeP_ok c) (privCodeP_spSafe c)
      (privCodeP_depth c) hp h (privDP_pre hp hq h) hc hw)
    fun _ ⟨he, _, R, o⟩ => ⟨he, R, o⟩

/-! ## After the call -/

/-- `scratch` back to `sScr`. -/
theorem scrSlot_ok {s u : State} (hp : DPre s) (he : EnvD s u) :
    WP isa (.block scrSlot) u fun u' => Keep [.r11] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) sScr) (stackArg s 15) := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes :=
    Scr.of_mem (by rw [he.wr]; exact List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  have hin := hp.argIn he.rd (j := 15) (by decide)
  have hv := arg_valD hp he.fr (j := 15) (by decide)
  refine WP.mono (WP.keep [.r11] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) sScr) (stackArg s 15)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm⟩
  rw [← argAddr] at hin hv
  xrun [scrSlot, arg, ea_sp, he.rsp, hin, hv, hsc.st (d := sScr) (by decide)]

/-- `scratch` back to `sScr`, then the table of the label's hash function to
its slot: `decBody`'s state after its table slot. -/
theorem restoreTab_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} {f : Impl.Mgf1.X86_64.Table.Fns} {s t : State}
    (hp : DPre s) (he : EnvD s t) (hsy : t.syms = s.syms) {V : Nat → Byte}
    (R : Rep t.mem (fb s) (stackArg s 15) V (privWP s)) (ok : Table.TabOK G f s.syms)
    (hm : Table.TabMem G s.syms (stackArg s 17) s.mem)
    (hD : s.mem.readW (off (stackArg s 17) 48) 64 = BitVec.ofNat 64 G.D) :
    WP isa (.block (scrSlot ++ tabSlot 17)) t fun t' => EnvD s t' ∧ Lay t' (fb s) (stackArg s 15) ∧
      Rep t'.mem (fb s) (stackArg s 15) V (upd (upd (privWP s) 14 (stackArg s 15)) 35 (stackArg s 17)) ∧
      t'.syms = s.syms ∧ Keep [.r11] t t' := by
  rw [WP.block_append_iff]
  refine X86_64.WP.mono_syms (wp_good (block_good _ rfl) (scrSlot_ok hp he))
    fun t1 ⟨⟨k1, hm1⟩, sp1, mx1, f1⟩ sy1 => ?_
  have he1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  have R1 : Rep t1.mem (fb s) (stackArg s 15) V (upd (privWP s) 14 (stackArg s 15)) :=
    hm1 ▸ R.wf hp.geo (k := 14) (by decide) _
  have L1 : Lay t1 (fb s) (stackArg s 15) :=
    Lay.of_envD hp he1 (by rw [slot_eq sScr 14 rfl, R1.fr 14 (by decide)]; simp [upd])
  refine X86_64.WP.mono_syms (wp_good (block_good _ rfl) (tabSlot_ok L1 R1 (dtabL hp he1 (sy1.trans hsy) ok hm hD)))
    fun t2 ⟨⟨k2, L2, R2, _⟩, sp2, mx2, f2⟩ sy2 => ?_
  exact ⟨he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2, L2, R2, sy2.trans (sy1.trans hsy),
    (k1.trans k2).mono (by decide)⟩

/-- The frame's words after `restoreTab_ok`: they hold the arguments. -/
theorem ArgsD_privWP (s : State) : ArgsD s (upd (privWP s) 14 (stackArg s 15)) :=
  (ArgsD_privW s).of fun k hk => by
    rcases decKs_iff hk with rfl | ⟨h1, -⟩
    · simp [upd, privW, decW]
    · simp only [privWP, upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega)]

variable {vs : List MdHash} (hc : Coh vs)

include hc in
/-- `vg_rsa_oaep_decrypt_precomputed`, calling
`vg_rsa_private_checked_precomputed` for `c`: what `vg_rsa_oaep_decrypt`
writes. -/
theorem decP_correct (c : CrtImpl) (s : State) (h : (pdspec (tables vs)).pre s) :
    ∃ t s', Exec isa (decryptP (fnsOf vs) (privNameP c) (privCodeP c)) s t s' ∧ abiPreserved s s' ∧
      (decK (tables vs)).post s s' := by
  obtain ⟨⟨hp, htab⟩, hq⟩ := preDP_of h
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, -, hd⟩ := htab
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨hmL, -, hDmL⟩ := held_tableOf hheld₁
  have okL := tabOK_of hc hd hw₁
  suffices hw : WP isa (decryptP (fnsOf vs) (privNameP c) (privCodeP c)) s
      fun s' => abiPreserved s s' ∧ (decK (tables vs)).post s s' by
    obtain ⟨t, s', he, hq⟩ := hw; exact ⟨t, s', he, hq⟩
  refine wp_alloc (by have := hp.sp1; unfold decStack privStack at this; unfold frameBytes at *; omega) ?_
  unfold decBodyP Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs Impl.Mgf1.X86_64.seqs
  refine WP.seq (X86_64.WP.mono_syms (decHeadP_ok hp hq) fun t0 h0 sy0 => ?_)
  refine WP.seq (X86_64.WP.mono_syms (privDP_call c hp hq h0) fun t1 ⟨he1, R1, hw1⟩ sy1 => ?_)
  refine WP.seq (WP.mono (restoreTab_ok hp he1 (sy1.trans sy0) R1 okL hmL hDmL)
    fun ta ⟨hea, La, Ra, sya, ka⟩ => ?_)
  exact decAfterTab_ok hc hp (preDP_of h).1.2 hw1 hea sya La (ArgsD_privWP s) Ra (ka.gpr (by decide))
    fun s₂ _ _ hH hG he hw => decFin hp hH hG he hw

end VG.Proof.RsaOaep.X86_64
