module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- The regions `vg_rsa_pkcs1_decrypt` reads: its buffers and stack arguments. -/
def rdD (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨stackArgAddr s 0, 120⟩]

/-- `pre` and `pre_len`, our stack arguments 15 and 16, and `pre`. -/
def XD (s : State) : List Region :=
  [⟨stackArgAddr s 15, 16⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]

/-- What the contract says of `pre`, besides what `decSpec` says. -/
structure PreD (P : Nat) (s : State) : Prop where
  sp2 : s.sp.toNat + 136 ≤ 2 ^ 64
  rd : s.rd = (rdD s).take 9 ++ [⟨stackArg s 15, (stackArg s 16).toNat * 8⟩, ⟨stackArgAddr s 0, 136⟩]
  oa : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  ma : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  sa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  ka : (⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  op : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  mp : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  sp : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  kp : (⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  wp : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  prl : (stackArg s 16).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .x4).toNat (stackArg s 4).toNat (stackArg s 6).toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 15) (stackArg s 16).toNat)

theorem sub120 (s : State) : Region.Sub ⟨stackArgAddr s 0, 120⟩ ⟨stackArgAddr s 0, 136⟩ := by
  simpa using Offset.sub_base (stackArgAddr s 0) (d := 0) (n := 120) (k := 136) (by decide)

theorem decSpec_of {P : Nat} {s : State}
    (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (P + 240)).pre s) :
    (decSpec P).pre (s.withRegions (rdD s) s.wr) ∧ PreD P s := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop] at h
  sig_split h
  rename_i sp1 sp2 rd wr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPr oA mN mE mD mI mP mQ mDP mDQ mQI mS mPr mA
    nS eS dS iS pS qS dpS dqS qiS sPr sA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA bO bM bN bE bD bI bP bQ
    bDP bDQ bQI bS bPr kv olk ilk el1 elk dl1 dlk pl1 plk ql1 qlk dpl qil dql slk prl
  have s1 := sub120 s
  have e : P + 239 + 1 = P + 240 := by omega
  rw [e] at sp1 kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPr kA
  refine ⟨?_, ⟨sp2, by rw [rd]; rfl, oA, mA, sA, kA, oPr, mPr, sPr, kPr, bPr, prl, h⟩⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [Proof.Rsa.AArch64.stackArg_withRegions, Proof.Rsa.AArch64.stackArgAddr_withRegions, e]
  exact ⟨sp1, by omega, rfl, wr, oM, oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oS, oA.sub_right s1, mN, mE, mD, mI,
    mP, mQ, mDP, mDQ, mQI, mS, mA.sub_right s1, nS, eS, dS, iS, pS, qS, dpS, dqS, qiS, sA.sub_right s1, kO, kM,
    kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kS, kA.sub_right s1, bO, bM, bN, bE, bD, bI, bP, bQ, bDP, bDQ, bQI,
    bS, kv, olk, ilk, el1, elk, dl1, dlk, pl1, plk, ql1, qlk, dpl, qil, dql, slk⟩

/-! ## The callee -/

/-- An implementation of `vg_rsa_private_checked_precomputed`, as
`PrivImpl` is of `vg_rsa_private_checked`. -/
structure PrivPImpl where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi stack)
  pos : 16 ≤ stack
  depth : 16 * code.aarch64Depth ≤ stack

namespace PrivPImpl

variable (v : PrivPImpl)

def S : Nat := v.stack - 1

theorem stack_eq : v.stack = v.S + 1 := by have := v.pos; unfold S; omega

theorem verified' :
    Verified AArch64.target v.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (v.S + 1)) :=
  v.stack_eq ▸ v.verified

theorem depth' : 16 * v.code.aarch64Depth ≤ v.S + 1 := v.stack_eq ▸ v.depth

theorem S15 : 15 ≤ v.S := by have := v.pos; unfold S; omega

end PrivPImpl

/-! ## In the frames -/

/-- What the call of `vg_rsa_private_checked_precomputed` needs, besides
`Ctx`: our stack arguments 15 and 16, `pre` and `pre_len`, and `pre`, in the
memory `m₀` on entry. -/
structure PreX (L : Lay) (m₀ : Mem) : Prop where
  x : L.X = [⟨L.Q + BitVec.ofNat 64 360, 16⟩, ⟨L.pre, L.prl.toNat * 8⟩]
  nQ2 : L.Q.toNat + 376 ≤ 2 ^ 64
  a15 : m₀.readW (L.Q + BitVec.ofNat 64 360) 64 = L.pre
  a16 : m₀.readW (L.Q + BitVec.ofNat 64 368) 64 = L.prl
  ao : L.OUT.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  am : L.ML.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  as : L.SCR.Disjoint ⟨L.Q + BitVec.ofNat 64 360, 16⟩
  po : L.OUT.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  pm : L.ML.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  ps : L.SCR.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  pk : L.STK.Disjoint ⟨L.pre, L.prl.toNat * 8⟩
  wp : L.pre.toNat + L.prl.toNat * 8 ≤ 2 ^ 64
  prlv : L.prl.toNat = Spec.Rsa.privatePrecomputedWords L.k.toNat L.pl.toNat L.ql.toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
      (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) =
    some (Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `Ctx` survives writes to the private-key operation's stack arguments 12
and 13, which no step reads but the call. -/
theorem Ctx.args2 (hL : L.Ok) {t t' : State} (hc : Ctx L g vv m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.Q + BitVec.ofNat 64 96, 16⟩] t.mem t'.mem) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => by
      rw [List.mem_singleton.mp hR]
      unfold keptOff at hd
      exact hL.fr_sep (by omega) (by omega) (by omega),
    hc.frame.trans (hf.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega)⟩)⟩

/-- A word of our stack arguments 15 and 16, as on entry. -/
theorem PreX.arg (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) {d : Nat}
    (hd : d = 360 ∨ d = 368) : t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = m₀.readW (L.Q + BitVec.ofNat 64 d) 64 := by
  have hpQ := hL.pQ
  have hn := hx.nQ2
  have hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ ⟨L.Q + BitVec.ofNat 64 360, 16⟩ :=
    Offset.sub _ (by omega) (by omega)
  refine hc.frame.readW (r := ⟨L.Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact (hx.ao.sub_right hs).symm
  · exact (hx.am.sub_right hs).symm
  · exact (hx.as.sub_right hs).symm
  · show Region.Disjoint _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 240⟩
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.q_add L.Q L.P d]
    exact Offset.disjoint_base _ (by omega) (by omega)


theorem extra_ok (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hr : Ready L t) :
    WP isa (.block extraMoves) t fun u => Ctx L g vv m₀ u ∧ Ready L u ∧
      u.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre ∧ u.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl := by
  have hpQ := hL.pQ
  have hn := hx.nQ2
  have hnQ := hL.nQ
  unfold extraMoves
  rw [WP.block_append_iff, WP.block_append_iff]
  have h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  have x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  have inA : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ d, d = 360 ∨ d = 368 →
      InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 d) 8 := fun u hu hw d hd =>
    ⟨⟨L.Q + BitVec.ofNat 64 360, 16⟩, by rw [hu, hw, hc.rd, hx.x]; simp,
      Offset.contains _ (by omega) (by omega) (by omega)⟩
  have inF : ∀ (u : State), u.wr = t.wr → ∀ d, d + 8 ≤ frameBytes →
      InRegions u.wr (L.Q + BitVec.ofNat 64 d) 8 := fun u hw d hd => by rw [hw]; exact hc.inFr hd
  refine WP.mono (mv_step (j := 15) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp]; exact inA _ (RegUpd.rd_write ..) (RegUpd.wr_write ..) 360 (.inl rfl))
    (by rw [x9]; exact inF _ (RegUpd.wr_write ..) 96 (by decide))) fun t₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  have sp₁ : t₁.sp = L.Q := by rw [s₁, RegUpd.sp_write, hc.sp]
  refine WP.mono (mv_step (j := 16) (d := 104) (by decide) (by decide)
    (by rw [sp₁]; exact inA _ (r₁.trans (RegUpd.rd_write ..)) (w₁.trans (RegUpd.wr_write ..)) 368 (.inr rfl))
    (by rw [g₁ .x9 (by decide), x9]; exact inF _ (w₁.trans (RegUpd.wr_write ..)) 104 (by decide)))
    fun u ⟨r₂, w₂, s₂, v₂, m₂, g₂⟩ => ?_
  -- The values moved.
  have e15 : (t.write .x .x9 L.Q).mem.readW ((t.write .x .x9 L.Q).sp + BitVec.ofNat 64 (arg 15)) 64 = L.pre := by
    rw [RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 15 = 360 from rfl, hx.arg hL hc (.inl rfl), hx.a15]
  have sep : Mem.Sep (L.Q + BitVec.ofNat 64 368) 8 (L.Q + BitVec.ofNat 64 96) 8 :=
    Offset.sep _ (by omega) (by omega) (by omega)
  have e16 : t₁.mem.readW (t₁.sp + BitVec.ofNat 64 (arg 16)) 64 = L.prl := by
    rw [m₁, x9, e15, sp₁, show arg 16 = 368 from rfl, RegUpd.mem_write,
      Mem.readW_writeW_sep sep (by decide), hx.arg hL hc (.inr rfl), hx.a16]
  have mu : u.mem = (t.mem.writeW (L.Q + BitVec.ofNat 64 96) L.pre).writeW (L.Q + BitVec.ofNat 64 104) L.prl := by
    rw [m₂, e16, g₁ .x9 (by decide), x9, m₁, x9, e15, RegUpd.mem_write]
  have hr96 : Region.Contains ⟨L.Q + BitVec.ofNat 64 96, 16⟩ (L.Q + BitVec.ofNat 64 96) (64 / 8) :=
    Offset.contains _ (by omega) (by omega) (by omega)
  have hr104 : Region.Contains ⟨L.Q + BitVec.ofNat 64 96, 16⟩ (L.Q + BitVec.ofNat 64 104) (64 / 8) :=
    Offset.contains _ (by omega) (by omega) (by omega)
  have gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₂ r h10, g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  have hfr : Frame [⟨L.Q + BitVec.ofNat 64 96, 16⟩] t.mem u.mem := by
    rw [mu]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hr96).writeW (List.mem_singleton_self _) _ hr104
  refine ⟨hc.args2 hL (r₂.trans (r₁.trans (RegUpd.rd_write ..))) (w₂.trans (w₁.trans (RegUpd.wr_write ..)))
    (by rw [s₂, sp₁, hc.sp]) (by rw [v₂, v₁, RegUpd.v_write])
    (fun r hr _ => gu r (Enc.preserved_ne hr (by decide)) (Enc.preserved_ne hr (by decide)))
    hfr, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [gu .x0 (by decide) (by decide)]; exact hr.x0
  · rw [gu .x1 (by decide) (by decide)]; exact hr.x1
  · rw [gu .x2 (by decide) (by decide)]; exact hr.x2
  · rw [gu .x3 (by decide) (by decide)]; exact hr.x3
  · rw [gu .x4 (by decide) (by decide)]; exact hr.x4
  · rw [gu .x5 (by decide) (by decide)]; exact hr.x5
  · rw [gu .x6 (by decide) (by decide)]; exact hr.x6
  · rw [gu .x7 (by decide) (by decide)]; exact hr.x7
  · rw [mu, Mem.readW_writeW_sep (Offset.sep L.Q (d := 96) (n := 8) (e := 104) (k := 8) (by omega) (by omega)
      (by omega)) (by decide), Mem.readW_writeW_self64]
  · rw [mu, Mem.readW_writeW_self64]


/-- The regions the call of `vg_rsa_private_checked_precomputed` reads. -/
abbrev privRdP (L : Lay) : List Region :=
  [L.N, L.E, L.INP, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.pre, L.prl.toNat * 8⟩, ⟨L.Q + BitVec.ofNat 64 0, 112⟩]

theorem privP_pre (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) (h96 : t.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre)
    (h104 : t.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pre
      (t.callEntry.withRegions (privRdP L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := priv_args hc (privRdP L) (privWr L)
  have hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  have aa : stackArgAddr (t.callEntry.withRegions (privRdP L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  have a12 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hc.sp]; exact h96
  have a13 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl := by
    rw [VG.Proof.RsaPkcs1Enc.AArch64.Enc.stackArg_ce, hc.sp]; exact h104
  have arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 112⟩ L.STK := Lay.Ok.sub_stk (by omega_arith)
  have lS := Lay.Ok.low_stk (L := L)
  have hw : Spec.Rsa.wordsAt t.mem L.pre L.prl.toNat = Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat := by
    have := hx.wp
    simp only [Spec.Rsa.wordsAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    refine hc.frame.readW (r := ⟨L.pre, L.prl.toNat * 8⟩) (Offset.contains_base _ (by omega) (by omega)) ?_
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [hx.po.symm, hx.pm.symm, hx.ps.symm, hx.pk.symm]
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, Proof.Rsa.AArch64.stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  simp only [hc.sp,
    hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, aa, hlow, hL.dpl, hL.qil, hL.dql, hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hw]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
    hL.oR _ (ro_N L), hL.oR _ (ro_E L), hL.oR _ (ro_INP L), hL.oR _ (ro_PP L), hL.oR _ (ro_QQ L),
    hL.oR _ (ro_DP L), hL.oR _ (ro_DQ L), hL.oR _ (ro_QI L), hL.oS, hx.po, (hL.kO.sub_left arS).symm,
    (hL.sR _ (ro_N L)).symm, (hL.sR _ (ro_E L)).symm, (hL.sR _ (ro_INP L)).symm, (hL.sR _ (ro_PP L)).symm,
    (hL.sR _ (ro_QQ L)).symm, (hL.sR _ (ro_DP L)).symm, (hL.sR _ (ro_DQ L)).symm, (hL.sR _ (ro_QI L)).symm,
    hx.ps, (hL.kS.sub_left arS).symm,
    hL.kO.sub_left lS, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_INP L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    hL.kS.sub_left lS, hx.pk.sub_left lS, (hL.fr_low (by omega_arith)).symm,
    hL.bO, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_INP L), hL.bR _ (ro_PP L), hL.bR _ (ro_QQ L),
    hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L), hL.bS, hx.wp,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial, hL.slk,
    hx.prlv, hx.key⟩


theorem covers_privP (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) :
    Covers (privRdP L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  rw [hc.rd, hc.wr, hx.x]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.INP, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨⟨L.pre, L.prl.toNat * 8⟩, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 112 ≤ frameBytes; decide⟩
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, 0, z _, by simp⟩
    · exact ⟨L.SCR, by simp, 0, z _, by simp⟩

theorem privP_call (v : PrivPImpl) (hL : L.Ok) (hP : L.P = v.S + 1) (hx : PreX L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) (hr : Ready L t) (h96 : t.mem.readW (L.Q + BitVec.ofNat 64 96) 64 = L.pre)
    (h104 : t.mem.readW (L.Q + BitVec.ofNat 64 104) 64 = L.prl) :
    WP isa (.call v.name v.code) t (Called L g vv m₀) := by
  have hnQ := hL.nQ
  have hdp := v.depth'
  have hpQ := hL.pQ
  rw [hP] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_privP hx hc
  refine WP.callFV v.verified'.1 (privP_pre hL hP hx hc hr h96 h104) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  have hlow : Region.Sub (below t.sp (16 * v.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP]; exact Offset.sub_below _ hdp (by omega_arith)
  have hws : ∀ r ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      (Region.Sub r L.OUT ∨ Region.Sub r L.SCR) ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (.inl fun _ h => h)
    · exact .inl (.inr fun _ h => h)
    · exact .inr hlow
  have hkept : ∀ d, keptOff d → ∀ R ∈ privWr L ++ [below t.sp (16 * v.code.aarch64Depth)],
      Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ R := fun d hd R hR => by
    rcases hws R hR with (hs | hs) | hs
    · exact hL.kept_buf hd (.inl hs)
    · exact hL.kept_buf hd (.inr (.inr hs))
    · exact (hL.fr_low (by unfold keptOff at hd; omega_arith)).sub_right hs
  have hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), hc.kept.frame hf hkept, hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with (hs | hs) | hs
        · exact ⟨L.OUT, by simp, hs⟩
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (Lay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, -, -, -⟩ := priv_args hc (privRdP L) (privWr L)
  have hp := hpost
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, Proof.Rsa.AArch64.stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at hp
  simp only [hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_INP L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

end

/-! ## The call, narrowed -/

theorem q360 (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 360 = stackArgAddr s 15 := by
  rw [show (360 : Nat) = 240 + 120 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, lay_Q]; rfl

theorem q368 (P : Nat) (s : State) : (lay P s).Q + BitVec.ofNat 64 368 = stackArgAddr s 16 := by
  rw [show (368 : Nat) = 240 + 128 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, lay_Q]; rfl

theorem sub_arg15 (s : State) : Region.Sub ⟨stackArgAddr s 15, 16⟩ ⟨stackArgAddr s 0, 136⟩ :=
  Offset.sub s.sp (d := 120) (n := 16) (e := 0) (k := 136) (by decide) (by decide)

/-- The facts about `pre`, in the layout of the call. -/
theorem preX_of {P : Nat} {s : State} (hD : (decSpec P).pre (s.withRegions (rdD s) s.wr)) (hx : PreD P s) :
    PreX (layW P s (XD s) (stackArg s 15) (stackArg s 16)) s.mem := by
  have hL := lay_ok hD
  have hsp : P + 240 ≤ s.sp.toNat := spec_sp (s := s.withRegions (rdD s) s.wr) hD
  have hQ : (lay P s).Q.toNat = s.sp.toNat - 240 := by
    show (s.sp - BitVec.ofNat 64 240).toNat = _
    rw [BitVec.toNat_sub_of_le (by show 240 ≤ s.sp.toNat; omega)]; rfl
  have hsp2 := hx.sp2
  have hO : (layW P s (XD s) (stackArg s 15) (stackArg s 16)).OUT = ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ := by
    have e : (s.gpr .x1).toNat = (s.gpr .x4).toNat := hL.olk
    show (⟨s.gpr .x0, (s.gpr .x4).toNat⟩ : Region) = _; rw [e]
  have hK : (layW P s (XD s) (stackArg s 15) (stackArg s 16)).STK =
      ⟨s.sp - BitVec.ofNat 64 (P + 240), P + 240⟩ := by
    show (⟨(lay P s).Q - BitVec.ofNat 64 P, P + 240⟩ : Region) = _; rw [lay_stk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show XD s = [⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩, _]; rw [q360]; rfl
  · show (lay P s).Q.toNat + 376 ≤ 2 ^ 64; omega
  · show s.mem.readW ((lay P s).Q + BitVec.ofNat 64 360) 64 = _; rw [q360]; rfl
  · show s.mem.readW ((lay P s).Q + BitVec.ofNat 64 368) 64 = _; rw [q368]; rfl
  · rw [hO]; show Region.Disjoint _ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.oa.sub_right (sub_arg15 s)
  · show Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.ma.sub_right (sub_arg15 s)
  · show Region.Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ ⟨(lay P s).Q + BitVec.ofNat 64 360, 16⟩
    rw [q360]; exact hx.sa.sub_right (sub_arg15 s)
  · rw [hO]; exact hx.op
  · exact hx.mp
  · exact hx.sp
  · rw [hK]; exact hx.kp
  · exact hx.wp
  · exact hx.prl
  · exact hx.key

/-- Running from a state that permits more memory. -/
theorem wp_widen {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rd wr : List Region}
    (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    WP isa c (s.withRegions rd wr) fun u => ∃ t, Q t ∧ u = t.withRegions rd wr := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, _, Exec.widen he hc hw, t, hq, rfl⟩

/-- The call, reading only `vg_rsa_pkcs1_decrypt`'s regions and `XD`. -/
def narrowD (s : State) : State := s.withRegions (rdD s ++ XD s) s.wr

theorem narrowD_widen (s : State) : (narrowD s).withRegions s.rd s.wr = s := by
  simp only [narrowD, State.withRegions_withRegions, State.withRegions_self]

theorem narrowD_covers {P : Nat} {s : State} (hx : PreD P s) :
    Covers ((narrowD s).rd ++ (narrowD s).wr) (s.rd ++ s.wr) := by
  refine Covers.of_sub fun r hr => ?_
  have self : ∀ r ∈ s.rd ++ s.wr, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := fun r hr => ⟨r, hr, 0, (BitVec.add_zero _).symm, by omega⟩
  have m9 : ∀ r ∈ (rdD s).take 9, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len :=
    fun r hr => self r (by rw [hx.rd]; exact List.mem_append_left _ (List.mem_append_left _ hr))
  have ma : (⟨stackArgAddr s 0, 136⟩ : Region) ∈ s.rd ++ s.wr := by rw [hx.rd]; simp
  have mp : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hx.rd]; simp
  simp only [narrowD, State.withRegions_rd, State.withRegions_wr, rdD, XD, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | hw
  iterate 9 exact m9 _ (by simp [rdD])
  · exact ⟨_, ma, 0, (BitVec.add_zero _).symm, by dsimp only; omega⟩
  · exact ⟨_, ma, 120, by simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat], by dsimp only; omega⟩
  · exact ⟨_, mp, 0, (BitVec.add_zero _).symm, by dsimp only; omega⟩
  · exact self _ (List.mem_append_right _ hw)

/-- The setup, the moves of `pre` and `pre_len`, and the call, on the
narrowed call: `entry_ok` on the call narrowed further to
`vg_rsa_pkcs1_decrypt`'s regions, widened. -/
theorem stageP_ok (pv : PrivPImpl) {s : State} (hD : (decSpec (pv.S + 1)).pre (s.withRegions (rdD s) s.wr))
    (hx : PreD (pv.S + 1) s) :
    WP isa (.block (setup ++ extraMoves)) (entered (narrowD s)) fun t =>
      WP isa (.call pv.name pv.code) t
        (Called (layW (pv.S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).gpr
          (narrowD s).v (narrowD s).mem) := by
  have hL := lay_ok hD
  obtain ⟨hrd, hwr⟩ := spec_rdwr hD
  have eN : entered (narrowD s) =
      (entered (s.withRegions (rdD s) s.wr)).withRegions (rdD s ++ XD s) (entered (s.withRegions (rdD s) s.wr)).wr :=
    rfl
  rw [WP.block_append_iff, eN]
  refine WP.mono (wp_widen (entry_ok hD) (rd := rdD s ++ XD s) (wr := (entered (s.withRegions (rdD s) s.wr)).wr)
    (Covers.of_mem fun r hr => by
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h) (Covers.refl _)) fun u ⟨t, ⟨hc, hr⟩, hu⟩ => ?_
  subst hu
  have hL' : (layW (pv.S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)).Ok :=
    hL.withX (XD s) (stackArg s 15) (stackArg s 16)
  have hX : PreX (layW (pv.S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).mem :=
    preX_of (s := s) hD hx
  have hc' : Ctx (layW (pv.S + 1) (narrowD s) (XD s) (stackArg s 15) (stackArg s 16)) (narrowD s).gpr
      (narrowD s).v (narrowD s).mem (t.withRegions (rdD s ++ XD s) (entered (s.withRegions (rdD s) s.wr)).wr) := by
    refine ⟨?_, ?_, hc.sp, hc.cs, hc.vs, { hc.kept with }, hc.frame⟩
    · show rdD s ++ XD s = _
      rw [show rdD s = (s.withRegions (rdD s) s.wr).rd from rfl, hrd]; rfl
    · rw [State.withRegions_wr, entered_wr (pv.S + 1), hwr]; rfl
  exact WP.mono (extra_ok hL' hX hc' { hr with }) fun u ⟨hc'', hr'', h96, h104⟩ =>
    privP_call pv hL' rfl hX hc'' hr'' h96 h104

theorem post_of {P : Nat} {s s' : State} (h : (decSpec P).post (s.withRegions (rdD s) s.wr) s') :
    (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (P + 240)).post s (s'.withRegions s.rd s.wr) := by
  sig_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, AArch64.abi, AArch64.argRegs, stackArgs_seventeen, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  exact h

theorem decP_correct (v : Compress) (pv : PrivPImpl) (s : State)
    (h : (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (pv.S + 1 + 240)).pre s) :
    ∃ t s', Exec isa (codeP (HH v) pv.name pv.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract AArch64.abi (pv.S + 1 + 240)).post s s' := by
  have hS := pv.S15
  obtain ⟨hD, hx⟩ := decSpec_of h
  obtain ⟨t, s', he, ha, hp⟩ := decW_ok v (by omega) (s := narrowD s) (R₀ := rdD s) (X := XD s)
    (pre := stackArg s 15) (prl := stackArg s 16) hD (setup ++ extraMoves) pv.name pv.code (stageP_ok pv hD hx)
  have hw := Exec.widen he (narrowD_covers hx) (Covers.refl _)
  rw [narrowD_widen] at hw
  exact ⟨t, _, hw, ha, post_of hp⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
