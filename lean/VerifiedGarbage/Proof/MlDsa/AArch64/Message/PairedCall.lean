import VerifiedGarbage.Proof.MlDsa.AArch64.Message.PairedRoots

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots PairedRoots StaticTable pairedSignRootConsts)

structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified target c (signContract p (abi.withConsts pairedSignRootConsts) 16)
  dle : DLe 1 c

section
variable {p : Params} {s : State}
theorem signK_base_pre (hp : p ∈ params) (h : SPre p s) (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State} (hc : Ctx (slay p s) g vv m₀ t)
    (hA : ∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (signContract p AArch64.abi 16).pre (t1.callEntry.withRegions (signRd p s) (signWr p s)) := by
  have hL := slay_ok hp h h8
  obtain ⟨e0, e1, e2, e3, e4⟩ := signRegs_of hc hA
  have hmu := (mu_within p s).sub
  have hsub := sScr_sub p s
  have hstk : ∀ {rd wr : List Region} {r : Region}, (rStk s).Disjoint r →
      (rStk (t1.callEntry.withRegions rd wr)).Disjoint r := by
    intro rd wr r hr; simpa [rStk, hsp1] using hr
  refine signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [gpr_ce t1 (r := .x0), gpr_ce t1 (r := .x1), gpr_ce t1 (r := .x2), gpr_ce t1 (r := .x3),
      gpr_ce t1 (r := .x4), e0, e1, e2, e3, e4, State.withRegions_rd, State.withRegions_wr]
  · simp only [State.withRegions_sp, State.callEntry_sp, hsp1]; exact h.sp
  · exact h.skSig
  · exact h.skScr.sub_right hsub
  · exact h.sigScr.symm.sub_left hmu
  · exact mu_sScr hp s
  · exact h.rndSig
  · exact h.rndScr.sub_right hsub
  · exact h.sigScr.sub_right hsub
  · exact hstk h.stkSk
  · have km := k_mu hL
    exact hstk km
  · exact hstk h.stkRnd
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · exact h.nSk
  · exact mu_nowrap hL
  · exact h.nRnd
  · exact h.nSig
  · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega

theorem signK_pre (hp : p∈params) (h : SPre p s) (h8 : (s.gpr .x4).toNat<256)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (slay p s) g vv m₀ t)
    (hm : (∀da∈signArgs,t1.gpr da.1=da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (signArgs.map (·.1)) t t1)
    (hsy : t1.syms=t.syms) (hr : StaticRoots 16 t) (rp : PairedRoots 16 t) :
    (signContract p (abi.withConsts pairedSignRootConsts) 16).pre
      (t1.callEntry.withRegions (signRd p s++rootRegions t1) (signWr p s)) := by
  have hL := slay_ok hp h h8
  obtain ⟨hA,o⟩ := hm
  have hc1 : Ctx (slay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  obtain ⟨e0, e1, e2, e3, _⟩ := signRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hbase := signK_base_pre hp h h8 hc hA hsp1
  have hr1 : StaticRoots 16 t1 := by
    have pass {nm ws} (ht : StaticTable 16 nm ws t) : StaticTable 16 nm ws t1 := by
      apply ht.frame (W := []) ?_ (by simp) o.rd o.wr o.sp hsy
      rw [o.mem]; exact Frame.refl _ _
    exact ⟨pass hr.forward,pass hr.inverse⟩
  have rp1 : PairedRoots 16 t1 := by
    apply rp.frame (W:=[]) ?_ (by simp) o.rd o.wr o.sp hsy
    rw [o.mem]; exact Frame.refl _ _
  have hcw : Covers (signWr p s) t1.wr := by
    rw [hc1.wr]
    refine covers_of_within fun r hr=>?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,by simp [slay,h.wr],within_self _⟩
    · exact ⟨⟨s.gpr .x7,mScrLen p⟩,by simp [slay,h.wr],
        within_base _ (by rw [mScr_eq]; simp only [sScr,oE]; omega)⟩
  let rd := signRd p s++rootRegions t1
  have hroot := roots_reborrow hr1 (rd := rd) (List.subset_append_right _ _) hcw
  have hpair := paired_reborrow rp1 (rd:=rd) (List.subset_append_right _ _) hcw
  have hpre : (signContract p (abi.withConsts pairedSignRootConsts) 16).pre
      (t1.callEntry.withRegions rd (signWr p s)) := by
    refine sign_pre_extend ?_ hroot hpair ?_
    · simpa only [State.withRegions_withRegions,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),State.withRegions_gpr,State.withRegions_wr,e0,e1,e2] using hbase
    · simp only [State.withRegions_rd,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),e0,e1,e2]
      rfl
  exact hpre

theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) (h : SPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p s) g vv m₀ t) (hr : StaticRoots 16 t) (rp : PairedRoots 16 t) :
    WP isa (callA n c signArgs) t fun s' => Fin (slay p s) g vv s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .x0) p.skLen) (bytesAt t.mem (slay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) 32)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x6) p.sigLen) := by
  have hL := slay_ok hp h h8
  refine WP.seq (WP.mono_syms (setArgs_ok signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ hsy => ?_)
  have hc1 : Ctx (slay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  obtain ⟨e0, e1, e2, e3, _⟩ := signRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hd := hS.dle.1
  have hbase := signK_base_pre hp h h8 hc hA hsp1
  have hr1 : StaticRoots 16 t1 := by
    have pass {nm ws} (ht : StaticTable 16 nm ws t) : StaticTable 16 nm ws t1 := by
      apply ht.frame (W := []) ?_ (by simp) o.rd o.wr o.sp hsy
      rw [o.mem]; exact Frame.refl _ _
    exact ⟨pass hr.forward,pass hr.inverse⟩
  have rp1 : PairedRoots 16 t1 := by
    apply rp.frame (W:=[]) ?_ (by simp) o.rd o.wr o.sp hsy
    rw [o.mem]; exact Frame.refl _ _
  have hcw : Covers (signWr p s) t1.wr := by
    rw [hc1.wr]
    refine covers_of_within fun r hr=>?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,by simp [slay,h.wr],within_self _⟩
    · exact ⟨⟨s.gpr .x7,mScrLen p⟩,by simp [slay,h.wr],
        within_base _ (by rw [mScr_eq]; simp only [sScr,oE]; omega)⟩
  let rd := signRd p s++rootRegions t1
  have hroot := roots_reborrow hr1 (rd := rd) (List.subset_append_right _ _) hcw
  have hpair := paired_reborrow rp1 (rd:=rd) (List.subset_append_right _ _) hcw
  have hpre : (signContract p (abi.withConsts pairedSignRootConsts) 16).pre
      (t1.callEntry.withRegions rd (signWr p s)) := by
    refine sign_pre_extend ?_ hroot hpair ?_
    · simpa only [State.withRegions_withRegions,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),State.withRegions_gpr,State.withRegions_wr,e0,e1,e2] using hbase
    · simp only [State.withRegions_rd,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),e0,e1,e2]
      rfl
  refine WP.callFV hS.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · change Covers ((signRd p s++rootRegions t1)++signWr p s) (t1.rd++t1.wr)
    rw [List.append_assoc]
    apply Covers.append_left
    · rw [hc1.rd,hc1.wr]
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,by simp [slay,h.rd],within_self _⟩
      · exact ⟨_,by simp [slay,h.wr],mu_within p s⟩
      · exact ⟨_,by simp [slay,h.rd],within_self _⟩
    · apply Covers.append_left
      · exact Covers.append_left hr1.forward.readable (Covers.pair hr1.inverse.readable rp1.readable)
      · exact hcw.right
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [slay, h.wr], within_self _⟩
    · exact ⟨⟨s.gpr .x7, mScrLen p⟩, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [add_add]
        exact (h.sigScr.symm.sub_left ((within_off (slay p s).X (d := 904 + d) (n := 8) (k := 1024)
          (by omega)).trans (slay_X p s)).sub)
      · exact sv_sScr hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [signContract, signSig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.pairedSignRootConsts_eq, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, e3, o.mem] at hpost
  exact hpost

end
end VG.Proof.MlDsa.AArch64.Message.Paired
