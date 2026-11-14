module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT

/-!
# RSAES-OAEP decryption on AArch64, given the key's precomputed values

`vg_rsa_oaep_decrypt_precomputed` (`decryptP`) is `vg_rsa_oaep_decrypt` with
`vg_rsa_private_checked_precomputed` as the private-key operation: our stack
arguments 17 and 18, `pre` and `pre_len`, are its stack arguments 12 and 13,
the frame's words 12 and 13 (`preArgs`), MGF1's slots of `scratch` and of its
source, which nothing reads before the call; after it, `scratch` goes back to
its slot (`fixScr`), and the decoding is `vg_rsa_oaep_decrypt`'s (`after_ok`).

The layout (`layP`) is `vg_rsa_oaep_decrypt`'s, with `pre` among the buffers
read (`DLay.X`), our 19 stack arguments (`DLay.al`), and `pre`'s modulus'
values among what the function may leak (`DLay.lk`). `specP` is what the
contract says of it, and `PreX` what the call needs of `pre`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked stackArgs_fourteen)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq read8 write8 q_add add_add toNat_sub_k
  popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp freed_v freed_gpr preserved_ne)

/-- The contract, with both hash functions each one of the tables `ts` and
`P + 288` bytes of stack. -/
abbrev decSpecP (ts : List FnTable) (P : Nat) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract (AArch64.abi.withTables
    Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) (P + 288)

/-- Unfolds the contract's precondition at `h`. -/
macro "dec_preP" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- What a call from `s` adds to the layout: `pre` (our stack arguments 17
and 18), our 19 stack arguments, and the modulus' values in `pre`, which the
function may leak. -/
def dxP (s : State) : DX where
  X := [⟨stackArg s 17, (stackArg s 18).toNat * 8⟩]
  al := 152
  pre := stackArg s 17
  prl := stackArg s 18
  lk := fun m => Spec.Rsa.privatePrecomputedLeak m (stackArg s 17) (s.gpr .x4).toNat

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
abbrev layP (P : Nat) (s : State) : DLay := lay P s (dxP s)

/-- What the call of `vg_rsa_private_checked_precomputed` needs of `pre`,
from the memory `m₀` on entry. -/
structure PreX (L : DLay) (m₀ : Mem) : Prop where
  x : L.X = [⟨L.pre, L.prl.toNat * 8⟩]
  al : L.al = 152
  a17 : m₀.readW (L.Q + BitVec.ofNat 64 424) 64 = L.pre
  a18 : m₀.readW (L.Q + BitVec.ofNat 64 432) 64 = L.prl
  prlv : L.prl.toNat = Spec.Rsa.privatePrecomputedWords L.k.toNat L.pl.toNat L.ql.toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
      (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) =
    some (Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat)
  lk : L.lk = fun m => Spec.Rsa.privatePrecomputedLeak m L.pre L.k.toNat

/-- What the contract says of a call. -/
structure SpecP (ts : List FnTable) (P : Nat) (s : State) : Prop where
  ok : (layP P s).Ok
  rd : s.rd = [(layP P s).N, (layP P s).E, (layP P s).PP, (layP P s).QQ, (layP P s).DP, (layP P s).DQ,
    (layP P s).QI, (layP P s).LAB, (layP P s).CT] ++ (layP P s).X ++
    [(layP P s).TABL, (layP P s).TAB, (layP P s).ARGS]
  wr : s.wr = [(layP P s).OUT, (layP P s).ML, (layP P s).SCR]
  pre : PreX (layP P s) s.mem
  sp : P + 288 ≤ s.sp.toNat
  tabL : ∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)
  tab : ∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)
  pw : ((ts.map (·.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)

theorem stackArg_q (P : Nat) (s : State) (x : DX) (j : Nat) :
    s.mem.readW ((lay P s x).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q P s x, add_add]

theorem specP {ts : List FnTable} {P : Nat} {s : State} (h : (decSpecP ts P).pre s) : SpecP ts P s := by
  dec_preP at h
  sig_split h
  rename_i hsp hsp2 hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPr oTL oT oA mN mE mP mQ mDP
    mDQ mQI mL mC mS mPr mTL mT mA nS eS pS qS dpS dqS qiS lS cS sPr sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC
    kS kPr kTL kT kA bO bM bN bE bP bQ bDP bDQ bQI bL bC bS bPr bTL bT kv hk1 hk2 el1 elk pl1 plk ql1 qlk hdp hqi
    hdq slk prl
  have key := h
  clear h kA
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oP oQ oDP oDQ oQI oL oC oS oM oT oTL oPr
  simp only [hk2, hdp, hqi, hdq] at mC mDP mDQ mQI cS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kC kDP kDQ kQI bO bC bDP bDQ bQI
  have eA : (layP P s).ARGS = ⟨stackArgAddr s 0, 152⟩ := by
    show (⟨(layP P s).Q + BitVec.ofNat 64 288, 152⟩ : Region) = _
    rw [lay_args P s (dxP s)]
  have eK : (layP P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 288), P + 288⟩ := by
    show (⟨(layP P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region) = _
    rw [lay_stk P s (dxP s)]
  have hQ : (layP P s).Q.toNat = s.sp.toNat - 288 := toNat_sub_k (by omega_arith)
  have one : ∀ {F : Region → Prop}, F ⟨stackArg s 17, (stackArg s 18).toNat * 8⟩ →
      ∀ R ∈ (layP P s).X, F R := fun hF R hR => by
    rw [List.mem_singleton.mp hR]; exact hF
  refine ⟨⟨oM, oS, mS, forall_ro ⟨oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC⟩,
    forall_ro ⟨mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC⟩,
    forall_ro ⟨nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm⟩, eA ▸ oA,
    eA ▸ mA, eA ▸ sA, oT, mT, sT, oTL, mTL, sTL, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kP,
    eK ▸ kQ, eK ▸ kDP, eK ▸ kDQ, eK ▸ kQI, eK ▸ kL, eK ▸ kC⟩, eK ▸ kT, eK ▸ kTL, bO, bM, bS,
    forall_ro ⟨bN, bE, bP, bQ, bDP, bDQ, bQI, bL, bC⟩, bT, bTL,
    by simp only [lay] at hQ ⊢; omega_arith, by simp only [lay] at hQ ⊢; omega_arith, kv, hk1, hk2, el1, elk,
    pl1, plk, ql1, qlk, hdp, hqi, hdq, slk, (by decide : 136 ≤ 152), Nat.le_refl _,
    by show (layP P s).Q.toNat + 288 + 152 ≤ _; simp only [lay] at hQ ⊢; omega_arith, one oPr.symm, one mPr.symm, one sPr.symm, one (eK ▸ kPr), one bPr⟩,
    ?_, ?_, ⟨rfl, rfl, ?_, ?_, prl, key, rfl⟩, hsp, hheld, hheld2, hpw.sublist (List.sublist_append_left _ _)⟩
  · rw [hrd, hk2, hdp, hqi, hdq, ← lay_args P s (dxP s)]; rfl
  · rw [hwr, hk1]; rfl
  · exact stackArg_q P s (dxP s) 17
  · exact stackArg_q P s (dxP s) 18

/-! ## The moves of `pre` and `pre_len` -/

section
variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- A word of our stack arguments 17 and 18, as on entry. -/
theorem PreX.arg (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) {d : Nat}
    (hd : d = 424 ∨ d = 432) :
    t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = m₀.readW (L.Q + BitVec.ofNat 64 d) 64 := by
  have hpQ := hL.pQ
  have hn := hL.nQa
  have hal := hx.al
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ L.ARGS := Offset.sub _ (by omega_using [hd]) (by omega_using [hd, hal])
  refine hc.frame.readW (r := ⟨L.Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact (hL.oA.sub_right hs).symm
  · exact (hL.mA.sub_right hs).symm
  · exact (hL.sA.sub_right hs).symm
  · show Region.Disjoint _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 288⟩
    rw [q_add L.Q L.P d]
    exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hd, hpQ, hn, hal])

/-- Our stack arguments 17 and 18 to the frame's words 12 and 13. -/
theorem preArgs_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) :
    WP isa (.block preArgs) t fun u => Ctx L g vv m₀ u ∧ Ready L u ∧
      Rep u.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl) := by
  have hpQ := hL.pQ
  have hn := hL.nQa
  have hal := hx.al
  have G' := hL.geo hP
  unfold preArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  have h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  have x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  have inA : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ d, d = 424 ∨ d = 432 →
      InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 d) 8 := fun u hu hw d hd =>
    ⟨L.ARGS, by rw [hu, hw, hc.rd]; simp, Offset.contains _ (by omega_using [hd]) (by omega_using [hal, hd]) (by omega_using [hal])⟩
  have inF : ∀ (u : State), u.wr = t.wr → ∀ d, d + 8 ≤ frameBytes →
      InRegions u.wr (L.Q + BitVec.ofNat 64 d) 8 := fun u hw d hd =>
    ⟨L.FR, by rw [hw, hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega_using [hd])⟩
  refine WP.mono (mv_step (j := 17) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp]; exact inA _ (RegUpd.rd_write ..) (RegUpd.wr_write ..) 424 (.inl rfl))
    (by rw [x9]; exact inF _ (RegUpd.wr_write ..) 96 (by decide))) fun t₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  have sp₁ : t₁.sp = L.Q := by rw [s₁, RegUpd.sp_write, hc.sp]
  refine WP.mono (mv_step (j := 18) (d := 104) (by decide) (by decide)
    (by rw [sp₁]; exact inA _ (r₁.trans (RegUpd.rd_write ..)) (w₁.trans (RegUpd.wr_write ..)) 432 (.inr rfl))
    (by rw [g₁ .x9 (by decide), x9]; exact inF _ (w₁.trans (RegUpd.wr_write ..)) 104 (by decide)))
    fun u ⟨r₂, w₂, s₂, v₂, m₂, g₂⟩ => ?_
  -- The values moved.
  have e17 : (t.write .x .x9 L.Q).mem.readW ((t.write .x .x9 L.Q).sp + BitVec.ofNat 64 (arg 17)) 64 = L.pre := by
    rw [RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 17 = 424 from rfl, hx.arg hL hc (.inl rfl), hx.a17]
  have sep : Mem.Sep (L.Q + BitVec.ofNat 64 432) 8 (L.Q + BitVec.ofNat 64 96) 8 :=
    Offset.sep _ (by omega_using []) (by omega_using []) (by omega_using [])
  have e18 : t₁.mem.readW (t₁.sp + BitVec.ofNat 64 (arg 18)) 64 = L.prl := by
    rw [m₁, x9, e17, sp₁, show arg 18 = 432 from rfl, RegUpd.mem_write,
      Mem.readW_writeW_sep sep (by decide), hx.arg hL hc (.inr rfl), hx.a18]
  have mu : u.mem = (t.mem.write (off L.Q (8 * 12)) 8 L.pre).write (off L.Q (8 * 13)) 8 L.prl := by
    rw [m₂, e18, g₁ .x9 (by decide), x9, m₁, x9, e17, RegUpd.mem_write, write8, write8]
  have gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₂ r h10, g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  have S : Step L.Q L.scr [] t u := ⟨r₂.trans (r₁.trans (RegUpd.rd_write ..)),
    w₂.trans (w₁.trans (RegUpd.wr_write ..)), by rw [s₂, sp₁, hc.sp],
    fun r hr _ => gu r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)),
    fun r _ => by rw [v₂, v₁, RegUpd.v_write], by
      rw [mu]
      exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF L.Q (by decide)))
        (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  refine ⟨hc.step hL hP S fun r h => absurd h List.not_mem_nil, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [gu .x0 (by decide) (by decide)]; exact hr.x0
  · rw [gu .x1 (by decide) (by decide)]; exact hr.x1
  · rw [gu .x2 (by decide) (by decide)]; exact hr.x2
  · rw [gu .x3 (by decide) (by decide)]; exact hr.x3
  · rw [gu .x4 (by decide) (by decide)]; exact hr.x4
  · rw [gu .x5 (by decide) (by decide)]; exact hr.x5
  · rw [gu .x6 (by decide) (by decide)]; exact hr.x6
  · rw [gu .x7 (by decide) (by decide)]; exact hr.x7
  · rw [mu]; exact (R.wq G' (k := 12) (by decide) _).wq G' (k := 13) (by decide) _

/-! ## The call -/

/-- The regions the call of `vg_rsa_private_checked_precomputed` reads. -/
abbrev privRdP (L : DLay) : List Region :=
  [L.N, L.E, L.CT, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.pre, L.prl.toNat * 8⟩, ⟨L.Q + BitVec.ofNat 64 0, 112⟩]

theorem upd2 {W : Nat → BitVec 64} {a b : BitVec 64} {i : Nat} (hi : i < 12) :
    upd (upd W 12 a) 13 b i = W i := by
  simp only [upd]; rw [ifn (by omega_using [hi]), ifn (by omega_using [hi])]

theorem pre_mem (hx : PreX L m₀) : (⟨L.pre, L.prl.toNat * 8⟩ : Region) ∈ L.X := by rw [hx.x]; simp

/-- The first `n` words of `pre`, as on entry. -/
theorem PreX.words (hx : PreX L m₀) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {n : Nat}
    (hn : n ≤ L.prl.toNat) : Spec.Rsa.wordsAt t.mem L.pre n = Spec.Rsa.wordsAt m₀ L.pre n := by
  have hPm := pre_mem hx
  have := hL.xw _ hPm
  dsimp only at this
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hc.frame.readW (r := ⟨L.pre, L.prl.toNat * 8⟩) (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hn, this, hi])) ?_
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  exacts [hL.xO _ hPm, hL.xM _ hPm, hL.xS _ hPm, (hL.xK _ hPm).symm]

theorem privP_pre (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl))
    (hA : CallArgs L W) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pre
      (t.callEntry.withRegions (privRdP L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hbS := hL.bS
  rw [hP] at hpQ
  have hPm := pre_mem hx
  have hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  have sa : ∀ i < 14, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = upd (upd W 12 L.pre) 13 L.prl i :=
    fun i hi => by rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega_arith)
  have sw : ∀ i < 12, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = W i :=
    fun i hi => (sa i (by omega_using [hi])).trans (upd2 hi)
  have a0 := (sw 0 (by decide)).trans hA.p
  have a1 := (sw 1 (by decide)).trans (hA.args 0 (by decide))
  have a2 := (sw 2 (by decide)).trans (hA.args 1 (by decide))
  have a3 := (sw 3 (by decide)).trans (hA.args 2 (by decide))
  have a4 := (sw 4 (by decide)).trans (hA.args 3 (by decide))
  have a5 := (sw 5 (by decide)).trans (hA.args 4 (by decide))
  have a6 := (sw 6 (by decide)).trans (hA.args 5 (by decide))
  have a7 := (sw 7 (by decide)).trans (hA.args 6 (by decide))
  have a8 := (sw 8 (by decide)).trans (hA.args 7 (by decide))
  have a9 := (sw 9 (by decide)).trans (hA.args 8 (by decide))
  have a10 := (sw 10 (by decide)).trans hA.s10
  have a11 := (sw 11 (by decide)).trans hA.s11
  have a12 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre :=
    (sa 12 (by decide)).trans (by simp [upd])
  have a13 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl :=
    (sa 13 (by decide)).trans (by simp [upd])
  simp only [ourArg] at a1 a2 a3 a4 a5 a6 a7 a8 a9
  have aa : stackArgAddr (t.callEntry.withRegions (privRdP L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 112⟩ L.STK := DLay.Ok.sub_stk (by omega_arith)
  have lS := DLay.Ok.low_stk (L := L)
  have hsl := sl_sub hL
  have hOut : Region.Sub ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩ L.SCR := Offset.sub_base _ (by omega_arith)
  have hScr : Region.Sub ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ L.SCR :=
    Offset.sub_base _ (by rw [hsl]; omega_arith)
  have dOS : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩
      ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ :=
    Offset.disjoint L.scr (.inl (by omega_arith)) (by omega_arith) (by rw [hsl]; omega_arith)
  have hw := hx.words hL hc (Nat.le_refl _)
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  simp only [hc.sp, hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, aa, hlow, hL.dpl, hL.qil, hL.dql, hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hw]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
    (hL.sR _ (ro_N L)).sub_left hOut, (hL.sR _ (ro_E L)).sub_left hOut, (hL.sR _ (ro_CT L)).sub_left hOut,
    (hL.sR _ (ro_PP L)).sub_left hOut, (hL.sR _ (ro_QQ L)).sub_left hOut, (hL.sR _ (ro_DP L)).sub_left hOut,
    (hL.sR _ (ro_DQ L)).sub_left hOut, (hL.sR _ (ro_QI L)).sub_left hOut, dOS,
    (hL.xS _ hPm).symm.sub_left hOut, ((hL.kS.sub_left arS).symm.sub_left hOut),
    ((hL.sR _ (ro_N L)).sub_left hScr).symm, ((hL.sR _ (ro_E L)).sub_left hScr).symm,
    ((hL.sR _ (ro_CT L)).sub_left hScr).symm, ((hL.sR _ (ro_PP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_QQ L)).sub_left hScr).symm, ((hL.sR _ (ro_DP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_DQ L)).sub_left hScr).symm, ((hL.sR _ (ro_QI L)).sub_left hScr).symm,
    (hL.xS _ hPm).symm.sub_left hScr, ((hL.kS.sub_left arS).symm.sub_left hScr),
    (hL.kS.sub_left lS).sub_right hOut, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_CT L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    (hL.kS.sub_left lS).sub_right hScr, (hL.xK _ hPm).sub_left lS, (hL.fr_low (by omega_arith)).symm,
    by rw [BitVec.add_zero]; omega_arith, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_CT L), hL.bR _ (ro_PP L),
    hL.bR _ (ro_QQ L), hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L),
    by rw [scr8192 hL, hsl]; omega_arith, hL.xw _ hPm,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial,
    by rw [hsl]; have := hL.slk; unfold Spec.RsaPss.scratchWords at this; omega_arith, hx.prlv, hx.key⟩

theorem covers_privP (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) :
    Covers (privRdP L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hsl := sl_sub hL
  have c1 : ∃ off, L.scr + BitVec.ofNat 64 0 = L.SCR.base + BitVec.ofNat 64 off ∧ off + L.k.toNat ≤ L.SCR.len :=
    ⟨0, rfl, by show 0 + L.k.toNat ≤ L.sl.toNat * 8; omega_arith⟩
  have c2 : ∃ off, L.scr + BitVec.ofNat 64 8192 = L.SCR.base + BitVec.ofNat 64 off ∧
      off + (L.sl - BitVec.ofNat 64 1024).toNat * 8 ≤ L.SCR.len :=
    ⟨8192, rfl, by show 8192 + _ ≤ L.sl.toNat * 8; rw [hsl]; omega_arith⟩
  rw [hc.rd, hc.wr, hx.x]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.CT, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨⟨L.pre, L.prl.toNat * 8⟩, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 112 ≤ frameBytes; decide⟩
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩

/-- The call of `vg_rsa_private_checked_precomputed`: as `priv_call`, the
frame's words as they were. -/
theorem privP_call (c : PrivPChecked) (hL : L.Ok) (hP : L.P = c.stack) (hx : PreX L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl)) (hA : CallArgs L W) :
    WP isa (.call c.name c.code) t (Called L g vv m₀ (upd (upd W 12 L.pre) 13 L.prl)) := by
  obtain ⟨S, hS⟩ : ∃ S, c.stack = S + 1 := ⟨c.stack - 1, by have := c.pos; omega_using [this]⟩
  have hP' : L.P = S + 1 := hP.trans hS
  have hnQ := hL.nQ
  have hdp : 16 * c.code.aarch64Depth ≤ S + 1 := hS ▸ c.depth
  have hpQ := hL.pQ
  rw [hP'] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_privP hL hx hc
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hsl := sl_sub hL
  have hv : Verified AArch64.target c.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)) :=
    hS ▸ c.verified
  refine WP.callFV hv.1 (privP_pre hL hP' hx hc hr R hA) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  have hlow : Region.Sub (below t.sp (16 * c.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP']; exact Offset.sub_below _ hdp (by omega_arith)
  have hws : ∀ r ∈ privWr L ++ [below t.sp (16 * c.code.aarch64Depth)],
      Region.Sub r L.SCR ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Offset.sub_base _ (by omega_arith))
    · exact .inl (Offset.sub_base _ (by rw [hsl]; omega_arith))
    · exact .inr hlow
  have hfr : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      ∀ X ∈ privWr L ++ [below t.sp (16 * c.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ X :=
    fun d h₁ h₂ X hX => by
      rcases hws X hX with hs | hs
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inr (.inr hs))
        · exact hL.args_buf h₂ h₁ (.inr (.inr hs))
      · exact (hL.fr_low h₁).sub_right hs
  have hk' : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      s'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (hfr d h₁ h₂) (by decide)
  have hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), (hk' 272 (by decide) (by decide)).trans hc.lr,
      fun j hj => (hk' _ (by omega_arith) (by omega_arith)).trans (hc.args j hj), hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with hs | hs
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (DLay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ⟨fun _ _ => rfl, fun j hj => ?_⟩, ?_⟩
  · have : 8 * j + 8 ≤ 272 := by unfold nW frameBytes at hj; omega_arith
    exact (hk' (8 * j) (by omega_arith) (.inl (by omega_arith))).trans (R.fr j hj)
  have sw : ∀ i < 12, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact (R.fr i (by unfold nW frameBytes; omega_arith)).trans (upd2 hi)
  have a0 := (sw 0 (by decide)).trans hA.p
  have a1 := (sw 1 (by decide)).trans (hA.args 0 (by decide))
  have a2 := (sw 2 (by decide)).trans (hA.args 1 (by decide))
  have a3 := (sw 3 (by decide)).trans (hA.args 2 (by decide))
  have a4 := (sw 4 (by decide)).trans (hA.args 3 (by decide))
  have a6 := (sw 6 (by decide)).trans (hA.args 5 (by decide))
  have a8 := (sw 8 (by decide)).trans (hA.args 7 (by decide))
  simp only [ourArg] at a1 a2 a3 a4 a6 a8
  have hp := hpost
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at hp
  simp only [hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_CT L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

/-! ## `scratch` back to its slot -/

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {n : Nat} {r r' : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n) (hr : r' = r) (h : Spec.Rsa.writtenOutcome m a n r o) :
    Spec.Rsa.writtenOutcome m' a n r' o := by
  cases o <;> exact ⟨hr.trans h.1, hb.trans h.2⟩

theorem fixScr_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {W : Nat → BitVec 64} (hcl : Called L g vv m₀ W t) :
    WP isa (.block fixScr) t (Called L g vv m₀ (upd W 12 L.scr)) := by
  have hc := hcl.ctx
  have G' := hL.geo hP
  have hn := hL.nQa
  have hal := hL.al136
  have hal' := hL.al152
  have hk := hL.k1024
  rw [show fixScr = [.addSp .x9 0] ++ mvArg 13 sScr from rfl, WP.block_append_iff]
  have h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  have x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  refine WP.mono (mv_step (j := 13) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp, RegUpd.rd_write, RegUpd.wr_write]
        exact ⟨L.ARGS, by rw [hc.rd]; simp, Offset.contains _ (by decide) (by unfold arg frameBytes; omega_using [hal])
          (by omega_using [hal'])⟩)
    (by rw [x9, RegUpd.wr_write]
        exact ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ (by decide) (by decide)⟩))
    fun u ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  have mu : u.mem = t.mem.write (off L.Q (8 * 12)) 8 L.scr := by
    rw [m₁, x9, RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 13 = 288 + 8 * 13 from rfl, hc.args 13 (by decide),
      write8]
    rfl
  have gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  have S : Step L.Q L.scr [] t u := ⟨r₁.trans (RegUpd.rd_write ..), w₁.trans (RegUpd.wr_write ..),
    by rw [s₁, RegUpd.sp_write],
    fun r hr _ => gu r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)),
    fun r _ => by rw [v₁, RegUpd.v_write], by
      rw [mu]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  have R' : Rep u.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (upd W 12 L.scr) := by
    rw [mu]; exact hcl.rep.wq G' (k := 12) (by decide) _
  refine ⟨hc.step hL hP S fun r h => absurd h List.not_mem_nil, ⟨fun _ _ => rfl, R'.fr⟩, ?_⟩
  refine writtenOutcome_congr (bytesAt_eq fun i hi => ?_) (by rw [gu .x0 (by decide) (by decide)]) hcl.out
  rw [BitVec.add_zero]
  exact R'.scr i (by unfold oRsa; omega_using [hk, hi])

end

/-- The slots, after `scratch` goes back to its slot over `pre`. -/
theorem slots_fix {L : DLay} {W : Nat → BitVec 64} {a b : BitVec 64} (hS : Slots L W) :
    Slots L (upd (upd (upd W 12 a) 13 b) 12 L.scr) :=
  hS.of fun j _ _ h3 => by
    simp only [upd]
    rcases h3 with rfl | h3
    · rw [ifp rfl]; exact hS.scr.symm
    · rw [ifn (by omega_using [h3]), ifn (by omega_using [h3]), ifn (by omega_using [h3])]

/-! ## The whole function -/

theorem decBodyP_eq (f : Fns) (privN : String) (privC : Prog isa) :
    decBodyP f privN privC = .seq (.block (decPrologue ++ privArgs ++ preArgs)) (.seq (.call privN privC)
      (.seq (.block fixScr) (.seq (.block (tabSlot 15)) (.seq (.block lenLoad)
        (byLen (fun d => decTail (ofLen d) f) lens))))) := rfl

/-- The postcondition, from what the body wrote with `Hs` and `Gs`, the hash
functions the tables name. -/
theorem resultP_ok {Hs Gs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s : State} {t : State}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some Hs)
    (hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some Gs)
    (hw : Spec.RsaOaep.writtenDecrypt t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
      (decOut Hs Gs (Spec.Rsa.bytesAt s.mem (lay P s).lab (lay P s).labl.toNat) (privOut (lay P s) s.mem))) :
    (decSpecP ts P).post s t := by
  sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  intro H' G' hH' hG'
  obtain rfl : Hs = H' := Option.some.inj (hH.symm.trans hH')
  obtain rfl : Gs = G' := Option.some.inj (hG.symm.trans hG')
  rw [decrypt_eq (by simp [Spec.Rsa.bytesAt])]
  exact hw

/-- `vg_rsa_oaep_decrypt_precomputed` meets its contract and the calling
convention, with both hash functions the tables of `vs`, calling `c`. -/
theorem decP_ok {vs : List MdHash} (hc : Coh vs) (c : PrivPChecked) (h16 : 16 ≤ c.stack) {s : State}
    (h : (decSpecP (tables vs) c.stack).pre s) :
    WP isa (decryptP (fnsOf vs) c.name c.code) s fun s' =>
      abiPreserved s s' ∧ (decSpecP (tables vs) c.stack).post s s' := by
  have hx := specP h
  have hL := hx.ok
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hsp := hx.sp
  obtain ⟨T₁, hT₁, hheld₁⟩ := hx.tabL
  obtain ⟨T, hT, hheld⟩ := hx.tab
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hixL, hDL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hix, hD⟩ := held_tableOf hheld
  have okL := tabOK_of hc hx.pw hw₁
  have ok := tabOK_of hc hx.pw hw
  have hHa := hashAt_tableOf hixL
  have hGa := hashAt_tableOf hix
  have hP16 : 16 ≤ (layP c.stack s).P := h16
  refine WP.frame (by omega_arith) (WP.alloc (by decide) ?_ ?_)
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (decBodyP (fnsOf vs) c.name c.code) (entered s) _
    rw [decBodyP_eq]
    refine WP.seq ?_
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (Table.wp_sy (prologueX_ok hL hx.rd hx.wr)) fun t ⟨⟨hct, h9, hpw⟩, sy⟩ => ?_
    have sy' : t.syms = s.syms := sy
    rw [WP.block_append_iff, privArgs_eq, WP.block_append_iff]
    have R₀ : Rep t.mem (layP c.stack s).Q (layP c.stack s).scr (fun o => t.mem (off (layP c.stack s).scr o))
        (fun j => word t.mem (layP c.stack s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    refine WP.mono (Table.wp_sy (privW_ok hL hP16 hct h9 R₀ hpw.slots)) fun u1 ⟨⟨hc1, _, R1⟩, sy1⟩ => ?_
    have hS1 : Slots (layP c.stack s) (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) :=
      hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
    refine WP.mono (Table.wp_sy (privR_ok hL hP16 hc1 R1 hS1)) fun u2 ⟨⟨hc2, hm2, hr2⟩, sy2⟩ => ?_
    have R2 : Rep u2.mem (layP c.stack s).Q (layP c.stack s).scr (fun o => t.mem (off (layP c.stack s).scr o))
        (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) := hm2 ▸ R1
    have hA : CallArgs (layP c.stack s) (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) :=
      ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
        simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
        by simp [privW, upd], by simp [privW, upd]⟩
    refine WP.mono (Table.wp_sy (preArgs_ok hL hP16 hx.pre hc2 hr2 R2)) fun u3 ⟨⟨hc3, hr3, R3⟩, sy3⟩ => ?_
    refine WP.seq (WP.mono (Table.wp_sy (privP_call c hL rfl hx.pre hc3 hr3 R3 hA)) fun u4 ⟨hcl, sy4⟩ => ?_)
    refine WP.seq (WP.mono (Table.wp_sy (fixScr_ok hL hP16 hcl)) fun u5 ⟨hcl5, sy5⟩ => ?_)
    have hS5 := slots_fix (a := (layP c.stack s).pre) (b := (layP c.stack s).prl) hS1
    have sy05 : u5.syms = s.syms := sy5.trans (sy4.trans (sy3.trans (sy2.trans (sy1.trans sy'))))
    refine WP.mono (after_ok w₁.ok.stream w.ok.stream w₁.mgf.hash w₁.mgf.len (mgf_valid w₁.mgf) w₁.mgf.mem
      w.mgf.hash w.mgf.len (mgf_valid w.mgf) hL hP16 hS5 hcl5 (sy05 ▸ okL) (sy05 ▸ hmL) hDL (sy05 ▸ ok)
      (sy05 ▸ hm) hD) fun u' ⟨hc', hw'⟩ => ?_
    have hsp' : (freed frameBytes u').sp = (layP c.stack s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · rw [popped_sp, hsp']
      show (layP c.stack s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s _
    · rw [popped_v, freed_v]
      exact hc'.vs r hr
    · refine resultP_ok hHa hGa ?_
      rw [popped_mem, freed_mem, popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Dec
