import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyRoots

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
