import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Layout
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash

/-!
# Ed448 signing with a cached public key on x86-64: the hashes

Between the frame's push and pop (`Ctx`): the first ten bytes of
`dom4(0, context)` written to the frame (`hdr_ok`), the Keccak state at
`scratch` zeroed (`zeroSt_ok`), and the calls of the sponge functions on it
(`kabs_ok`, `kpad_ok`, `ksqz_ok`); then the three hashes, each into the frame:
`SHAKE256(seed, 114)` (`seedHash_ok`), `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)`
(`nonceHash_ok`) and `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` (`chalHash_ok`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk Arg hdr zeroSt kabs kpad ksqz aSt aKs sigEd448 fHdr fH fPk fCtx fCtxLen
  fMsg fLen fScr)
open VG.Proof.Ed448.X86_64.Verify (Within within_off within_base within_self add_add ea_stk ea_base gpr_ce ne_cs
  bytesAt_length x0 dbl_ok hdr_bytes zstores zstores_ok zero_state ofNat_toNat_self ofNat_toNat_eq FrOk
  setArgs_ok argRegs_cs argsIn5 argsIn6 below_call_sub)
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_nosp
  pad_nosp squeeze_nosp absorb_depth pad_depth squeeze_depth callEntry_repr callEntry_bytesAt callEntry_stateAt
  ofNat_toNat')
open VG.Spec.Sha3 (bytesAt stateAt absorb pad squeezeFrom Repr)

theorem H_eq (L : Lay) : L.H = L.B + BitVec.ofNat 64 32 := add_add _ _ _

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## The arguments in the frame -/

theorem Ctx.frOk {t : State} (hc : Ctx L g mx m₀ t) : FrOk t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr (by omega)

theorem Ctx.slot {t : State} (hc : Ctx L g mx m₀ t) (f : Nat) :
    (Arg.slot f).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.sp {t : State} (hc : Ctx L g mx m₀ t) (o : Nat) : (Arg.sp o).val t = L.SP + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.aSt {t : State} (hc : Ctx L g mx m₀ t) : aSt.val t = L.ST := by
  simp only [Impl.Ed448.X86_64.Verify.aSt, hc.slot, hc.pScr]

theorem Ctx.aKs {t : State} (hc : Ctx L g mx m₀ t) : aKs.val t = L.KS := by
  simp only [Impl.Ed448.X86_64.Verify.aKs, Arg.val, hc.rsp, hc.pScr]

/-! ## Regions -/

/-- The 16 bytes below `rsp` that a call from the frame uses. -/
theorem k16 {t : State} (hc : Ctx L g mx m₀ t) {r : Region} (h : Region.Disjoint ⟨L.B, 16⟩ r) :
    (below (t.gpr .rsp) 16).Disjoint r := by
  rw [hc.rsp]; exact h.sub_left (below_call_sub L.B (Nat.le_refl _))

theorem st_ks (L : Lay) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.KS, 640⟩ := by
  have := Offset.disjoint L.scr (d := 0) (n := 200) (e := 256) (k := 640) (by omega) (by omega) (by omega)
  simpa only [x0] using this

theorem st_h (hL : L.Ok) : Region.Disjoint ⟨L.ST, 200⟩ ⟨L.H, 114⟩ := by
  have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 200) (by omega) (by omega)
  rw [H_eq]; simpa only [x0] using this.symm

theorem h_ks (hL : L.Ok) : Region.Disjoint ⟨L.H, 114⟩ ⟨L.KS, 640⟩ := by
  rw [H_eq]; exact hL.stk_x (by omega) (by omega)

/-- The 16 bytes below the frame, apart from `scratch`. -/
theorem k_x (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  have := hL.stk_x (d := 0) (n := 16) (by omega) h₂
  simpa only [x0] using this

theorem k_st (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.ST, 200⟩ := by
  have := k_x hL (e := 0) (k := 200) (by omega); simpa only [x0] using this

theorem k_ks (hL : L.Ok) : Region.Disjoint ⟨L.B, 16⟩ ⟨L.KS, 640⟩ := k_x hL (by omega)

theorem k_h : Region.Disjoint ⟨L.B, 16⟩ ⟨L.H, 114⟩ := by
  rw [H_eq]; exact Offset.base_disjoint _ (by omega) (by omega)

/-- The 16 bytes below the frame, apart from a buffer apart from the stack. -/
theorem k_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) : Region.Disjoint ⟨L.B, 16⟩ r := by
  have := hL.stk_r hr (d := 0) (n := 16) (by omega); simpa only [x0] using this

theorem w_st : WOk L ⟨L.ST, 200⟩ := .inl (within_base _ (by omega))
theorem w_ks : WOk L ⟨L.KS, 640⟩ := .inl (within_off _ (by omega))
theorem w_h : WOk L ⟨L.H, 114⟩ := .inr (.inr (.inl (within_off _ (by omega))))

/-- The first 57 bytes of `out`, where `R` goes. -/
theorem o57_sub : Region.Sub ⟨L.out, 57⟩ L.OUT := (within_base _ (by omega)).sub

/-- Bytes apart from the Keccak state, the working space and the 16 bytes
below the frame are kept by a sponge function's call. -/
theorem keep3 {m m' : Mem} (hf : Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') {p : Addr} {n : Nat}
    (dS : Region.Disjoint ⟨p, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨p, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Verify.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [dS, dK, kD.symm]) hn hi

theorem keep1 {m m' : Mem} (hf : Frame [⟨L.ST, 200⟩] m m') {p : Addr} {n : Nat}
    (dS : Region.Disjoint ⟨p, n⟩ ⟨L.ST, 200⟩) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Verify.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) (by simpa using dS) hn hi

/-! ## The header of `dom4` -/

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem hdr_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block hdr) t fun t' => Ctx L g mx m₀ t' ∧ bytesAt t'.mem L.SP 10 = hdrBytes L := by
  have w0 : InRegions t.wr L.SP 8 := by simpa only [x0] using hc.inFrW (d := 0) (n := 8) (by omega)
  have r216 := hc.inFr (d := 216) (by omega)
  have e : (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).readW (L.SP + BitVec.ofNat 64 216) 64 = L.ctxLen := by
    rw [Mem.readW_writeW_sep (fun x h₁ h₂ =>
      Offset.sep_base L.SP (n := 8) (e := 216) (k := 8) (by omega) (by omega) x h₂ h₁) (by decide)]
    exact hc.pCtxLen
  rw [hdr, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448) ∧
      s1.gpr .rax = L.ctxLen ∧ s1.mxcsr = t.mxcsr)
    (by xrun [ea_stk, fHdr, fCtxLen, hc.rsp, w0, r216, e, RegUpd.mxcsr_setReg]) (by decide))
    fun t1 ⟨⟨hm1, ha1, hx1⟩, k1⟩ => ?_
  refine WP.mono (dbl_ok 8 t1) fun t2 ⟨⟨ha2, hm2, hx2⟩, k2⟩ => ?_
  have hsp2 : t2.gpr .rsp = L.SP := by rw [k2.gpr (by decide), k1.gpr (by decide), hc.rsp]
  have w8 : InRegions t2.wr (L.SP + BitVec.ofNat 64 8) 8 := by
    rw [k2.2.2, k1.2.2]; exact hc.inFrW (by omega)
  refine WP.mono (Q := fun t3 : State => t3.mem = t2.mem.writeW (L.SP + BitVec.ofNat 64 8) (t2.gpr .rax) ∧
      t3.gpr = t2.gpr ∧ t3.rd = t2.rd ∧ t3.wr = t2.wr ∧ t3.mxcsr = t2.mxcsr) ?_
    fun t3 ⟨hm3, hg3, hrd3, hwr3, hx3⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, fHdr, Nat.reduceAdd, hsp2,
      w8, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  have hm : t3.mem = (t.mem.writeW L.SP (BitVec.ofNat 64 sigEd448)).writeW (L.SP + BitVec.ofNat 64 8)
      (L.ctxLen * BitVec.ofNat 64 (2 ^ 8)) := by
    rw [hm3, ha2, ha1, hm2, hm1]
  have hf : Frame ([⟨L.SP, 16⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem := by
    rw [hm]
    have c0 : (⟨L.SP, 16⟩ : Region).Contains L.SP 8 := by
      simpa only [x0] using Offset.contains_base L.SP (d := 0) (n := 8) (k := 16) (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ c0).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨hc.of_frame hL (hrd3.trans (k2.2.1.trans k1.2.1)) (hwr3.trans (k2.2.2.trans k1.2.2))
    (fun r hr => by
      rw [hg3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))])
    (by rw [hx3, hx2, hx1]) hf (fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inr (.inl (within_base _ (by omega))))
  · rw [hm]; exact hdr_bytes _ _ _ hL.ctxLt

/-! ## Zeroing the state -/

theorem zeroSt_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa zeroSt t fun t' => Ctx L g mx m₀ t' ∧ Frame [⟨L.ST, 200⟩] t.mem t'.mem ∧
      stateAt t'.mem L.ST = Spec.Sha3.zero := by
  refine WP.seq ?_
  show WP isa (.block (aSt.mov .rdi ++ [.mov32 .rax (.imm 0)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (Verify.Arg.mov_ok .rdi aSt (by decide) (by decide) t hc.frOk) fun t1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = t1.mem ∧ s1.gpr .rax = 0 ∧ s1.mxcsr = t1.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg]) (by decide)) fun t2 ⟨⟨hm2, hax, hx2⟩, k2⟩ => ?_
  have hdi : t2.gpr .rdi = L.scr := (k2.gpr (by decide)).trans (h1.trans hc.aSt)
  have hw2 : t2.wr = L.FR :: L.wr := k2.2.2.trans (k1.2.2.trans hc.wr)
  refine WP.mono (zstores_ok 25 (Nat.le_refl _) t2 hdi hax fun j hj => ?_)
    fun t3 ⟨g3, rd3, wr3, mx3, hf, hz⟩ => ?_
  · rw [hw2, hL.wr]
    exact ⟨L.SCR, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [hm2, hm1] at hf
    have hcs : ∀ r ∈ calleeSaved, t3.gpr r = t.gpr r := fun r hr => by
      rw [g3, k2.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide)),
        k1.gpr (by simp only [List.mem_singleton]; exact ne_cs hr (by decide))]
    have hf' : Frame ([⟨L.ST, 200⟩] ++ [⟨L.B, 16⟩]) t.mem t3.mem :=
      hf.mono fun r hr => by simp at hr ⊢; exact .inl hr
    exact ⟨hc.of_frame hL (rd3.trans (k2.2.1.trans k1.2.1)) (wr3.trans (k2.2.2.trans k1.2.2)) hcs
      (by rw [mx3, hx2, hx1]) hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact w_st), hf, zero_state hz⟩

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`. -/
abbrev absArgs (src len pos : Arg) : List Arg := [aSt, .imm 136, pos, src, len, aKs]

theorem kabs_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {src len pos : Arg} (hok : (absArgs src len pos).all Arg.ok = true)
    {dp : Addr} {n q : Nat} (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n)
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩) (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩)
    (kD : Region.Disjoint ⟨L.B, 16⟩ ⟨dp, n⟩) :
    WP isa (kabs src len pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        Repr t'.mem L.ST 136 (msg ++ bytesAt t.mem dp n)) ∧ (t'.gpr .rax).toNat = (q + n) % 136 := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hdp] at e4
  rw [hn] at e5
  rw [hq] at e3
  have ha : AbsorbArgs t1 L.ST dp L.KS 136 q n :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, hql, hnl, st_ks L, dS, dK, k16 hc1 (k_st hL), k16 hc1 kD,
      k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Absorb.absorb_correct absorb_nosp (by rw [absorb_depth])
    hc1 (absorb_pre ha) (by simpa using hin) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_st, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩ => ?_
  have hn' := ofNat_toNat' hnl
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, hn', hq'] at hpost hrax
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_, by rw [← hg₂ _ (by decide)]; exact hrax⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rwa [callEntry_bytesAt t1 hnl ha.k_d, hm] at this

/-- The arguments of a call of `vg_keccak_pad`. -/
abbrev padArgs (pos : Arg) : List Arg := [aSt, .imm 136, pos, .imm 0x1f, aKs]

theorem kpad_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {pos : Arg} (hok : (padArgs pos).all Arg.ok = true) {q : Nat}
    (hq : pos.val t = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad pos) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      (∀ msg, Repr t.mem L.ST 136 msg → q = msg.length % 136 →
        stateAt t'.mem L.ST = absorb 136 (pad 136 Spec.Sha3.shakeSuffix msg)) := by
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e5
  rw [hq] at e3
  have ha : PadArgs t1 L.ST L.KS 136 q :=
    ⟨e1, e2, e3, e5, by decide, hql, st_ks L, k16 hc1 (k_st hL), k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Pad.pad_correct pad_nosp (by rw [pad_depth])
    hc1 (pad_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [w_st, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hq' := ofNat_toNat' (show q < 2 ^ 64 by omega)
  simp only [Proof.Sha3.padX86_64, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂, hq'] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, fun msg hmsg hp => ?_⟩
  have := hpost msg ((callEntry_repr t1 ha.k_st).mpr (hm ▸ hmsg)) hp
  rw [this]
  rfl

/-- The arguments of a call of `vg_keccak_squeeze`. -/
abbrev sqzArgs : List Arg := [aSt, .imm 136, .imm 0, .sp fH, .imm 114, aKs]

theorem ksqz_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa ksqz t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem L.H 114 = squeezeFrom 136 (stateAt t.mem L.ST) 0 114 := by
  refine WP.seq (WP.mono (setArgs_ok sqzArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  rw [hc.aSt] at e1
  rw [hc.aKs] at e6
  rw [hc.sp] at e4
  change t1.gpr .rcx = L.H at e4
  have ha : SqueezeArgs t1 L.ST L.H L.KS 136 0 114 :=
    ⟨e1, e2, e3, e4, e5, e6, by decide, by decide, by decide, st_h hL, st_ks L, h_ks hL, k16 hc1 (k_st hL),
      k16 hc1 k_h, k16 hc1 (k_ks hL)⟩
  refine call_ok hL Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct squeeze_nosp
    (by rw [squeeze_depth]) hc1 (squeeze_pre ha) (by simp) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [w_st, w_h, w_ks])
    fun s' hc' hf _ ⟨s₂, hm₂, _, hpost, _⟩ => ?_
  simp only [State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
    gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, e5, hm₂, Arg.val, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hpost
  refine ⟨hc', by rw [← hm]; simpa using hf, ?_⟩
  rw [hpost, callEntry_stateAt t1 ha.k_st, hm]

/-! ## Where the pieces are -/

/-- A piece in the frame, apart from the Keccak state, the working space and
the 16 bytes below the frame. -/
theorem frSide (hL : L.Ok) {d n : Nat} (h : d + n ≤ 448) :
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.SP + BitVec.ofNat 64 d, n⟩ R) ∧
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.ST, 200⟩ ∧
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.KS, 640⟩ ∧
    Region.Disjoint ⟨L.B, 16⟩ ⟨L.SP + BitVec.ofNat 64 d, n⟩ := by
  refine ⟨⟨L.FR, by simp, within_off _ h⟩, ?_, ?_, ?_⟩ <;> rw [Lay.SP, add_add]
  · have := hL.stk_x (d := 16 + d) (n := n) (e := 0) (k := 200) (by omega) (by omega)
    simpa only [x0] using this
  · exact hL.stk_x (d := 16 + d) (n := n) (by omega) (by omega)
  · exact Offset.base_disjoint _ (by omega) (by omega)

/-- A buffer apart from `scratch` and the stack. -/
theorem bufSide (hL : L.Ok) {r : Region} (hin : ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hx : L.SCR.Disjoint r) (hk : L.STK.Disjoint r) :
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R) ∧ Region.Disjoint r ⟨L.ST, 200⟩ ∧
    Region.Disjoint r ⟨L.KS, 640⟩ ∧ Region.Disjoint ⟨L.B, 16⟩ r :=
  ⟨hin, by have := hL.x_r hx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm,
    (hL.x_r hx (e := 256) (k := 640) (by omega)).symm, k_r hL hk⟩

theorem sp0 (L : Lay) : L.SP + BitVec.ofNat 64 0 = L.SP := x0 _

/-! ## The hashes -/

/-- What the hashes write: `scratch`, the hash, and the 16 bytes below the
frame. -/
abbrev HW (L : Lay) : List Region := [L.SCR, ⟨L.H, 114⟩, ⟨L.B, 16⟩]

theorem frameH {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, r = ⟨L.B, 16⟩ ∨ Within r L.SCR ∨ Within r ⟨L.H, 114⟩) : Frame (HW L) m m' :=
  Frame.sub h fun r hr => by
    rcases hs r hr with rfl | hw | hw
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hw.sub⟩
    · exact ⟨_, by simp, hw.sub⟩

theorem fz {m m' : Mem} (h : Frame [⟨L.ST, 200⟩] m m') : Frame (HW L) m m' :=
  frameH h (by simp only [List.mem_singleton]; rintro r rfl; exact .inr (.inl (within_base _ (by omega))))

theorem fa {m m' : Mem} (h : Frame [⟨L.ST, 200⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') : Frame (HW L) m m' :=
  frameH h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [.inr (.inl (within_base _ (by omega))), .inr (.inl (within_off _ (by omega))), .inl rfl])

theorem fs {m m' : Mem} (h : Frame [⟨L.ST, 200⟩, ⟨L.H, 114⟩, ⟨L.KS, 640⟩, ⟨L.B, 16⟩] m m') : Frame (HW L) m m' :=
  frameH h (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exacts [.inr (.inl (within_base _ (by omega))), .inr (.inr (within_self _)),
      .inr (.inl (within_off _ (by omega))), .inl rfl])

theorem seedHash_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa seedHash t fun t' => Ctx L g mx m₀ t' ∧ Frame (HW L) t.mem t'.mem ∧
      bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (bytesAt m₀ L.seed 57) 114 := by
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  obtain ⟨i, s, k, d⟩ := bufSide hL ⟨L.SEED, List.mem_append_left _ hL.inSeed, within_self _⟩ hL.xSeed hL.kSeed
  refine WP.seq (WP.mono (kabs_ok hL hc1 (by decide) (dp := L.seed) (n := 57) (q := 0)
    (by rw [hc1.slot]; exact hc1.pSeed) rfl rfl (by decide) (by decide) i s k d)
    fun t2 ⟨hc2, hf2, hR2, _⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  rw [List.nil_append, hc1.bytesAt_eq hL.xSeed hL.oSeed hL.kSeed (by decide)] at hR2
  refine WP.seq (WP.mono (kpad_ok hL hc2 (pos := .imm 57) (by decide) rfl (by decide))
    fun t3 ⟨hc3, hf3, hS3⟩ => ?_)
  have hS3 := hS3 _ hR2 (by rw [bytesAt_length])
  refine WP.mono (ksqz_ok hL hc3) fun t4 ⟨hc4, hf4, hm4⟩ =>
    ⟨hc4, (fz hf1).trans ((fa hf2).trans ((fa hf3).trans (fs hf4))), ?_⟩
  rw [hm4, hS3, PublicKey.shake256_eq]

/-- The position after absorbing `b` after `a`. -/
theorem len_step {a : List Byte} {q n : Nat} (h : q = a.length % 136) (b : List Byte) (hb : b.length = n) :
    (q + n) % 136 = (a ++ b).length % 136 := by
  rw [List.length_append, hb, h]; omega

theorem nonceHash_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa nonceHash t fun t' => Ctx L g mx m₀ t' ∧ Frame (HW L) t.mem t'.mem ∧
      bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (bytesAt t.mem L.SP 10 ++ bytesAt m₀ L.ctx L.ctxLen.toNat ++
        bytesAt t.mem (L.SP + BitVec.ofNat 64 73) 57 ++ bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  obtain ⟨hi, hs, hk, hd⟩ := frSide hL (d := 0) (n := 10) (by omega)
  obtain ⟨pi, ps, pk, pd⟩ := frSide hL (d := 73) (n := 57) (by omega)
  rw [sp0] at hi hs hk hd
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh := keep1 hf1 hs (by decide)
  have ep1 := keep1 hf1 ps (by decide)
  -- The header.
  refine WP.seq (WP.mono (kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact x0 _) rfl rfl (by decide) (by decide) hi hs hk hd) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  have ep2 := keep3 hf2 ps pk pd (by decide)
  -- The context.
  obtain ⟨ci, cs, ck, cd⟩ := bufSide hL ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩ hL.xCtx hL.kCtx
  refine WP.seq (WP.mono (kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx2) (by omega) (by omega) ci cs ck cd) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.nil_append, bytesAt_length])
  rw [hc2.bytesAt_eq hL.xCtx hL.oCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  have ep3 := keep3 hf3 ps pk pd (by decide)
  -- The prefix.
  refine WP.seq (WP.mono (kabs_ok hL hc3 (by decide) (dp := L.SP + BitVec.ofNat 64 73) (n := 57)
    (by rw [hc3.sp]; rfl) rfl (ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide) pi ps pk pd)
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (len_step (by simp only [List.nil_append, bytesAt_length]) _ (bytesAt_length _ _ _))
  -- The message.
  obtain ⟨mi, ms, mk, md⟩ := bufSide hL ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩ hL.xMsg hL.kMsg
  refine WP.seq (WP.mono (kabs_ok hL hc4 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc4.slot]; exact hc4.pMsg) (by rw [hc4.slot]; exact hc4.pLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) L.len.isLt mi ms mk md)
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (len_step (len_step (by simp only [List.nil_append, bytesAt_length]) _
    (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _))
  rw [hc4.bytesAt_eq hL.xMsg hL.oMsg hL.kMsg (by have := hL.nMsg; omega)] at hR5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (kpad_ok hL hc5 (pos := .ret) (by decide) (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)))
    fun t6 ⟨hc6, hf6, hS6⟩ => ?_)
  have hS6 := hS6 _ hR5 (len_step (len_step (len_step (by simp only [List.nil_append, bytesAt_length]) _
    (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _))
  refine WP.mono (ksqz_ok hL hc6) fun t7 ⟨hc7, hf7, hm7⟩ => ⟨hc7, (fz hf1).trans ((fa hf2).trans ((fa hf3).trans
    ((fa hf4).trans ((fa hf5).trans ((fa hf6).trans (fs hf7)))))), ?_⟩
  rw [hm7, hS6, PublicKey.shake256_eq, List.nil_append, eh, ep3, ep2, ep1]

theorem chalHash_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa chalHash t fun t' => Ctx L g mx m₀ t' ∧ Frame (HW L) t.mem t'.mem ∧
      bytesAt t'.mem L.H 114 = Spec.Sha3.shake256 (bytesAt t.mem L.SP 10 ++ bytesAt m₀ L.ctx L.ctxLen.toNat ++
        bytesAt t.mem L.out 57 ++ bytesAt m₀ L.pk 57 ++ bytesAt m₀ L.msg L.len.toNat) 114 := by
  have hctx := hL.ctxLt
  obtain ⟨hi, hs, hk, hd⟩ := frSide hL (d := 0) (n := 10) (by omega)
  rw [sp0] at hi hs hk hd
  have xR := hL.xOut.sub_right o57_sub
  have kR := hL.kOut.sub_right o57_sub
  obtain ⟨oi, os, ok, od⟩ := bufSide hL ⟨L.OUT, by simp [hL.wr], within_base _ (by omega)⟩ xR kR
  refine WP.seq (WP.mono (zeroSt_ok hL hc) fun t1 ⟨hc1, hf1, hz⟩ => ?_)
  have eh := keep1 hf1 hs (by decide)
  have eo1 := keep1 hf1 os (by decide)
  -- The header.
  refine WP.seq (WP.mono (kabs_ok hL hc1 (by decide) (dp := L.SP) (n := 10) (q := 0)
    (by rw [hc1.sp]; exact x0 _) rfl rfl (by decide) (by decide) hi hs hk hd) fun t2 ⟨hc2, hf2, hR2, hx2⟩ => ?_)
  have hR2 := hR2 [] (PublicKey.repr_nil hz) rfl
  have eo2 := keep3 hf2 os ok od (by decide)
  -- The context.
  obtain ⟨ci, cs, ck, cd⟩ := bufSide hL ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩ hL.xCtx hL.kCtx
  refine WP.seq (WP.mono (kabs_ok hL hc2 (by decide) (dp := L.ctx) (n := L.ctxLen.toNat)
    (by rw [hc2.slot]; exact hc2.pCtx) (by rw [hc2.slot]; exact hc2.pCtxLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx2) (by omega) (by omega) ci cs ck cd) fun t3 ⟨hc3, hf3, hR3, hx3⟩ => ?_)
  have hR3 := hR3 _ hR2 (by simp only [List.nil_append, bytesAt_length])
  rw [hc2.bytesAt_eq hL.xCtx hL.oCtx hL.kCtx (by have := hL.nCtx; omega)] at hR3
  have eo3 := keep3 hf3 os ok od (by decide)
  -- `R`.
  refine WP.seq (WP.mono (kabs_ok hL hc3 (by decide) (dp := L.out) (n := 57)
    (by rw [hc3.slot]; exact hc3.pOut) rfl (ofNat_toNat_eq hx3) (Nat.mod_lt _ (by decide)) (by decide) oi os ok od)
    fun t4 ⟨hc4, hf4, hR4, hx4⟩ => ?_)
  have hR4 := hR4 _ hR3 (len_step (by simp only [List.nil_append, bytesAt_length]) _ (bytesAt_length _ _ _))
  -- `A`.
  obtain ⟨ai, as, ak, ad⟩ := bufSide hL ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩ hL.xPk hL.kPk
  refine WP.seq (WP.mono (kabs_ok hL hc4 (by decide) (dp := L.pk) (n := 57)
    (by rw [hc4.slot]; exact hc4.pPk) rfl (ofNat_toNat_eq hx4) (Nat.mod_lt _ (by decide)) (by decide) ai as ak ad)
    fun t5 ⟨hc5, hf5, hR5, hx5⟩ => ?_)
  have hR5 := hR5 _ hR4 (len_step (len_step (by simp only [List.nil_append, bytesAt_length]) _
    (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _))
  rw [hc4.bytesAt_eq hL.xPk hL.oPk hL.kPk (by decide)] at hR5
  -- The message.
  obtain ⟨mi, ms, mk, md⟩ := bufSide hL ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩ hL.xMsg hL.kMsg
  refine WP.seq (WP.mono (kabs_ok hL hc5 (by decide) (dp := L.msg) (n := L.len.toNat)
    (by rw [hc5.slot]; exact hc5.pMsg) (by rw [hc5.slot]; exact hc5.pLen.trans (ofNat_toNat_self _).symm)
    (ofNat_toNat_eq hx5) (Nat.mod_lt _ (by decide)) L.len.isLt mi ms mk md)
    fun t6 ⟨hc6, hf6, hR6, hx6⟩ => ?_)
  have hR6 := hR6 _ hR5 (len_step (len_step (len_step (by simp only [List.nil_append, bytesAt_length]) _
    (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _))
  rw [hc5.bytesAt_eq hL.xMsg hL.oMsg hL.kMsg (by have := hL.nMsg; omega)] at hR6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (kpad_ok hL hc6 (pos := .ret) (by decide) (ofNat_toNat_eq hx6) (Nat.mod_lt _ (by decide)))
    fun t7 ⟨hc7, hf7, hS7⟩ => ?_)
  have hS7 := hS7 _ hR6 (len_step (len_step (len_step (len_step (by simp only [List.nil_append, bytesAt_length]) _
    (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _)) _ (bytesAt_length _ _ _))
  refine WP.mono (ksqz_ok hL hc7) fun t8 ⟨hc8, hf8, hm8⟩ => ⟨hc8, (fz hf1).trans ((fa hf2).trans ((fa hf3).trans
    ((fa hf4).trans ((fa hf5).trans ((fa hf6).trans ((fa hf7).trans (fs hf8))))))), ?_⟩
  rw [hm8, hS7, PublicKey.shake256_eq, List.nil_append, eh, eo3, eo2, eo1]

end

end VG.Proof.Ed448.X86_64.SignCached
