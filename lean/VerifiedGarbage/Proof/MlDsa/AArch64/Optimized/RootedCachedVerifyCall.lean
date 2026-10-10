import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallPre

/-! ## From `RootedCachedVerifyRoots.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.AArch64.Message
open Message.Optimized (rootRegions roots_reborrow)

/-- The wrapper's hash workspace and stack cannot change either root table. -/
theorem roots_ctx {p : Params} {s t : State} {g : Reg → BitVec 64} {v : VReg → BitVec 128}
    (h : CachedPre p s) (hc : Ctx (cachedLay p s) g v s.mem t) (hy : t.syms=s.syms) :
    StaticRoots 16 t := by
  have transfer {nm : String} {ws : List (BitVec 64)} (hr : StaticTable 16 nm ws s) : StaticTable 16 nm ws t := by
    refine hr.frame hc.frame ?_ hc.rd hc.wr hc.sp hy
    intro r hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · exact (hr.writable _ (by rw [h.wr]; simp)).sub_right (cachedLay_X p s).sub
    · exact hr.stack
  exact ⟨transfer h.roots.forward,transfer h.roots.inverse⟩

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify

end

/-! ## From `RootedCachedVerifyCallPre.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open Message.Optimized (rootRegions roots_reborrow)
open Message.OptimizedVerify (verify_pre_extend)

section
variable {p : Params} {s : State}

theorem sScrV_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x6, sScr p⟩ ⟨s.gpr .x6, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega)

theorem sv_sScrV {p : Params} (hp : p ∈ params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(cachedLay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x6, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_sScrV {p : Params} (hp : p ∈ params) (s : State) :
    Region.Disjoint ⟨(cachedLay p s).MU, 64⟩ ⟨s.gpr .x6, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x6 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_withinV (p : Params) (s : State) : Within ⟨(cachedLay p s).MU, 64⟩ ⟨s.gpr .x6, mScrLen p⟩ :=
  (within_off (cachedLay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (cachedLay_X p s)

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (s : State) : List Region :=
  [⟨s.gpr .x0, p.pkLen⟩, ⟨(cachedLay p s).MU, 64⟩, ⟨s.gpr .x5, p.sigLen⟩]
abbrev verifyWr (p : Params) (s : State) : List Region := [⟨s.gpr .x6, sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (cachedLay p s) g vv m₀ t) (hm : (∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .x0 = s.gpr .x0 ∧ t1.gpr .x1 = (cachedLay p s).MU ∧ t1.gpr .x2 = s.gpr .x5 ∧ t1.gpr .x3 = s.gpr .x6 := by
  have e0 := hm (.x0, .slot fKey) (by simp)
  have e1 := hm (.x1, .off oMU) (by simp)
  have e2 := hm (.x2, .slot fSig) (by simp)
  have e3 := hm (.x3, .slot fScr) (by simp)
  rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV (f := fSig) (j := 6) rfl (by omega)] at e2
  rw [hc.slotV (f := fScr) (j := 7) rfl (by omega)] at e3
  simp only [Lay.vals, cachedLay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_base_pre (hp : p ∈ params) (h : CachedPre p s) (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64}
    {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State} (hc : Ctx (cachedLay p s) g vv m₀ t)
    (hA : ∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (verifyContract p AArch64.abi 16).pre (t1.callEntry.withRegions (verifyRd p s) (verifyWr p s)) := by
  have hL := cachedLay_ok hp h h8
  obtain ⟨e0, e1, e2, e3⟩ := verifyRegs_of hc hA
  have hsub := sScrV_sub p s
  have hstk : ∀ {rd wr : List Region} {r : Region}, (rStk s).Disjoint r →
      (rStk (t1.callEntry.withRegions rd wr)).Disjoint r := by
    intro rd wr r hr; simpa [rStk, hsp1] using hr
  refine verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [gpr_ce t1 (r := .x0), gpr_ce t1 (r := .x1), gpr_ce t1 (r := .x2), gpr_ce t1 (r := .x3),
      e0, e1, e2, e3, State.withRegions_rd, State.withRegions_wr]
  · simp only [State.withRegions_sp, State.callEntry_sp, hsp1]; exact h.sp
  · exact h.pkScr.sub_right hsub
  · exact mu_sScrV hp s
  · exact h.sigScr.sub_right hsub
  · exact hstk h.stkPk
  · have km := k_mu hL
    exact hstk km
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · exact h.nPk
  · exact mu_nowrap hL
  · exact h.nSig
  · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega

theorem verifyK_pre (hp : p∈params) (h : CachedPre p s) (h8 : (s.gpr .x4).toNat<256)
    {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (cachedLay p s) g vv m₀ t)
    (hm : (∀da∈verifyArgs,t1.gpr da.1=da.2.val t) ∧
      VG.Proof.MlKem.AArch64.Only (verifyArgs.map (·.1)) t t1)
    (hsy : t1.syms=t.syms) (hr : StaticRoots 16 t) :
    (verifyContract p (abi.withConsts signRootConsts) 16).pre
      (t1.callEntry.withRegions (verifyRd p s++rootRegions t1) (verifyWr p s)) := by
  have hL := cachedLay_ok hp h h8
  obtain ⟨hA,o⟩ := hm
  have hc1 : Ctx (cachedLay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hbase := verifyK_base_pre hp h h8 hc hA hsp1
  have hr1 : StaticRoots 16 t1 := by
    have pass {nm ws} (ht : StaticTable 16 nm ws t) : StaticTable 16 nm ws t1 := by
      apply ht.frame (W := []) ?_ (by simp) o.rd o.wr o.sp hsy
      rw [o.mem]; exact Frame.refl _ _
    exact ⟨pass hr.forward,pass hr.inverse⟩
  have hcw : Covers (verifyWr p s) t1.wr := by
    rw [hc1.wr]
    refine covers_of_within fun r hr=>?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    subst hr
    exact ⟨⟨s.gpr .x6,mScrLen p⟩,by simp [cachedLay,h.wr],
      within_base _ (by rw [mScr_eq]; simp only [sScr,oE]; omega)⟩
  let rd := verifyRd p s++rootRegions t1
  have hroot := roots_reborrow hr1 (rd := rd) (List.subset_append_right _ _) hcw
  have hpre : (verifyContract p (abi.withConsts signRootConsts) 16).pre
      (t1.callEntry.withRegions rd (verifyWr p s)) := by
    refine verify_pre_extend ?_ hroot ?_
    · simpa only [State.withRegions_withRegions,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),State.withRegions_gpr,State.withRegions_wr,e0,e1,e2] using hbase
    · simp only [State.withRegions_rd,gpr_ce t1 (r := .x0),
        gpr_ce t1 (r := .x1),gpr_ce t1 (r := .x2),e0,e1,e2]
      rfl
  exact hpre

end
end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify

end

/-! ## From `RootedCachedVerifyCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.AArch64.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open Message.Optimized (rootRegions roots_reborrow)
variable {p : Params} {s : State}
/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : Message.OptimizedVerify.VerifyFn p c) (hp : p ∈ params) (h : CachedPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx (cachedLay p s) g vv m₀ t) (hr : StaticRoots 16 t) :
    WP isa (callA n c verifyArgs) t fun s' => Fin (cachedLay p s) g vv s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (s.gpr .x0) p.pkLen) (bytesAt t.mem (cachedLay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) p.sigLen);
        ((s'.gpr .x0).setWidth 32 = 1 ∧ ∃ b, w b = some true) ∨
          ((s'.gpr .x0).setWidth 32 = 0 ∧ w minBounds ≠ some true)) := by
  have hL := cachedLay_ok hp h h8
  refine WP.seq (WP.mono_syms (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ hsy => ?_)
  have hc1 : Ctx (cachedLay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hd := hV.dle.1
  have hpre := verifyK_pre hp h h8 hc ⟨hA,o⟩ hsy hr
  have hr1 : StaticRoots 16 t1 := by
    have pass {nm ws} (ht : StaticTable 16 nm ws t) : StaticTable 16 nm ws t1 := by
      apply ht.frame (W := []) ?_ (by simp) o.rd o.wr o.sp hsy
      rw [o.mem]; exact Frame.refl _ _
    exact ⟨pass hr.forward,pass hr.inverse⟩
  refine WP.callFV hV.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · change Covers ((verifyRd p s++rootRegions t1)++verifyWr p s) (t1.rd++t1.wr)
    rw [List.append_assoc]
    apply Covers.append_left
    · rw [hc1.rd,hc1.wr]
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,by simp [cachedLay,h.rd],within_self _⟩
      · exact ⟨_,by simp [cachedLay,h.wr],mu_withinV p s⟩
      · exact ⟨_,by simp [cachedLay,h.rd],within_self _⟩
    · apply Covers.append_left
      · exact Covers.pair hr1.forward.readable hr1.inverse.readable
      · rw [hc1.wr]
        refine covers_of_within fun r hr=>?_
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨s.gpr .x6,mScrLen p⟩,by simp [cachedLay,h.wr],
          within_base _ (by rw [mScr_eq]; simp only [sScr,oE]; omega)⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨s.gpr .x6, mScrLen p⟩, by simp [cachedLay, h.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((cachedLay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((cachedLay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sv_sScrV hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, o.mem] at hpost
  exact hpost

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify

end
