import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Impl.RsaPss.X86_64.Precomputed

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

variable {G : Spec.Mgf1.Hash}

def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩, ⟨fb s, 32⟩]

def validCache (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat)

theorem pre_words {s : State} {m : Mem} (hp : Pre G s) (hf : Frame (vwrR s) s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega)
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega)
  · intro r hr
    simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.preStack
    · exact hp.preScr

theorem call_pre {s t : State} (hp : Pre G s) (hsp : t.gpr .rsp = fb s)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = off (stackArg s 3) oEm)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 5) (hcx : t.gpr .rcx = stackArg s 6)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pdChkContract.pre (t.callEntry.withRegions (callRd s) (vWr s)) := by
  have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (vWr s)) i = vArg s i :=
    fun i hi => (vstackArg_call hp.toVPre hsp _ _ hi).trans (hargs i hi)
  simp only [pdChkContract, pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), vArg]
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 408 := rfl
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have h8' := vfb_sub8 hp.toVPre
  have hsc := vsc_sub hp.toVPre
  have toNat_off : ∀ {p : Addr} {d : Nat}, p.toNat + d < 2 ^ 64 → (off p d).toNat = p.toNat + d := fun h => by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsg : (⟨s.gpr .r9, (s.gpr .rsi).toNat⟩ : Region) = ⟨s.gpr .r9, (stackArg s 0).toNat⟩ := by rw [hp.hsg]
  have dsgs : (⟨s.gpr .r9, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ := by
    rw [hsg]; exact hp.dsgs
  have dKsg : (vstkR s).Disjoint ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩ := by rw [hsg]; exact hp.dKsg
  have wSg : (s.gpr .r9).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by have := hp.wSg; have := hp.hsg; omega
  -- What lies in what.
  have sI : Region.Sub ⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ :=
    Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨off (stackArg s 3) oRsa, (stackArg s 4 - 1024#64).toNat * 8⟩
      ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (vstkR s) := fun a h => vframe_sub s a (Region.sub_prefix (by decide) a h)
  have sRet : Region.Sub ⟨fb s - 8, 8⟩ (vstkR s) := vret_sub s
  have dRA : (⟨fb s - 8, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega)).symm
  have dIR : (⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ : Region).Disjoint
      ⟨off (stackArg s 3) oRsa, (stackArg s 4 - 1024#64).toNat * 8⟩ :=
    Offset.disjoint _ (.inl (by omega)) (by omega) (by rw [hsc]; omega)
  have hsA : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by omega, rfl, rfl, (hp.preScr.sub_right sI).symm, (hp.des.sub_right sI).symm, (dsgs.sub_right sI).symm,
    dIR, hsA.sub_left sI,
    hp.preScr.sub_right sR, hp.des.sub_right sR, dsgs.sub_right sR, hsA.sub_left sR,
    (hp.dKs.sub_left sRet).sub_right sI, hp.preStack.symm.sub_left sRet, hp.dKe.sub_left sRet, dKsg.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    by rw [toNat_off (by omega)]; omega, hp.preWrap, hp.wE, wSg, by rw [toNat_off (by omega), hsc]; omega,
    ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2, by unfold Spec.Rsa.scratchWords; rw [hsc]; omega⟩

/-- The return addresses of the call and of its calls. -/
theorem vret2_sub (s : State) : Region.Sub (below (fb s) 16) (vstkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

theorem vhole_sub (s : State) : Region.Sub (hole (fb s - 8)) (vstkR s) := by
  have h : Region.Sub (hole (fb s - 8)) (below (fb s) 16) := by
    simp only [hole, below, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Region.sub_prefix (by decide)
  exact fun a ha => vret2_sub s a (h a ha)

/-- The call's buffers are apart from the return address of its calls. -/
theorem call_clear {s t : State} (hp : Pre G s) (hsp : t.gpr .rsp = fb s) :
    Clear (hole ((t.callEntry.withRegions (callRd s) (vWr s)).gpr .rsp))
      (t.callEntry.withRegions (callRd s) (vWr s)) := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hsp]
  have sH := vhole_sub s
  have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc := vsc_sub hp.toVPre
  have hF := vfb_toNat hp.toVPre
  have h392 : frameBytes = 392 := rfl
  have sI : Region.Sub ⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ :=
    Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨off (stackArg s 3) oRsa, (stackArg s 4 - 1024#64).toNat * 8⟩
      ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ := Offset.sub_base _ (by rw [hsc]; omega)
  intro r hr
  simp only [State.withRegions_rd, State.withRegions_wr, callRd, vWr, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp.preStack.sub_right sH
  · exact (hp.dKe.sub_left sH).symm
  · exact ((show (vstkR s).Disjoint ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩ by rw [← hp.hsg]; exact hp.dKsg).sub_left
      sH).symm
  · refine Region.Disjoint.sub_right (Offset.base_disjoint_below (fb s) (n := 16) (k := 32) (by omega)) ?_
    simp only [hole, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, sub_sub']
    exact Region.sub_prefix (by decide)
  · exact ((hp.dKs.sub_left sH).symm).sub_left sI
  · exact ((hp.dKs.sub_left sH).symm).sub_left sR

theorem call_covers {s t : State} (hp : Pre G s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) :
    Covers (callRd s ++ vWr s) (t.rd ++ t.wr) ∧ Covers (vWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hk1 := hp.k1
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc := vsc_sub hp.toVPre
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (vWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [vWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, oEm, rfl, by dsimp only; omega⟩
    · exact ⟨_, hscr, oRsa, rfl, by dsimp only; rw [hsc]; omega⟩
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
      ⟨s.gpr .r8, G.len⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
      (t.rd ++ t.wr) := by rw [hrd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hrd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · rw [← hp.hsg]
    exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

theorem call_ok (v : PublicImpl)
    {s t : State} (hp : Pre G s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (vwrR s) s.mem t.mem)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = off (stackArg s 3) oEm)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 5) (hcx : t.gpr .rcx = stackArg s 6)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (vwrR s) s.mem t'.mem ∧
      (∀ x, ((frR s).Contains x 1 ∨ ((⟨stackArg s 3, oRsa⟩ : Region).Contains x 1 ∧
        ¬ (⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ : Region).Contains x 1)) → t'.mem x = t.mem x) ∧
      (validCache s → Spec.Rsa.written t'.mem (off (stackArg s 3) oEm) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat))) := by
  obtain ⟨hc, hw⟩ := call_covers hp hrd hwr
  have hpre := Pc.call_pre hp hst hargs hdi hsi hdx hcx h8 h9
  have hd : v.code.x86_64Depth = 8 := by rw [x86_64Depth_noSp v.nosp, v.depth]
  refine X86_64.WP.callF (s := t) (k := pdChkContract.clear) v.ok (SpSafe.of_all v.spSafe) (by omega)
    ⟨hpre, call_clear hp hst⟩ hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := vfb_toNat hp.toVPre
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 408 := rfl
  have c2 : oRsa = 8192 := rfl
  have c1 : oEm = 2560 := rfl
  have hsc := vsc_sub hp.toVPre
  rw [hst, hd] at hf
  simp only [Nat.reduceAdd] at hf
  have sEm : Region.Sub ⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ (vscrR s) := Offset.sub_base _ (by omega)
  have sScr : Region.Sub ⟨off (stackArg s 3) oRsa, (stackArg s 4 - 1024#64).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have sBel : Region.Sub (below (fb s) 16) (vstkR s) := vret2_sub s
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), fun x hx => hf x fun r hr hc => ?_, ?_⟩
  · simp only [vWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sEm⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sScr⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · simp only [vWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have dFb : (frR s).Disjoint (below (fb s) 16) := Offset.base_disjoint_below (fb s) (by omega)
    rcases hx with hx | ⟨hx, hnx⟩ <;> rcases hr with rfl | rfl | rfl
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sEm x hc)
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sScr x hc)
    · exact dFb x hx hc
    · exact hnx hc
    · exact (Offset.base_disjoint (stackArg s 3) (e := oRsa) (n := (stackArg s 4 - 1024#64).toNat * 8)
        (k := oRsa) (le_refl _) (by rw [hsc]; omega)) x hx hc
    · exact ((hp.dKs.sub_left sBel).symm.sub_left (Region.sub_prefix (by omega))) x hx hc
  · have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (vWr s)) i = vArg s i :=
      fun i hi => (vstackArg_call hp.toVPre hst _ _ hi).trans (hargs i hi)
    have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
    have b : ∀ {R : Region}, (vstkR s).Disjoint R → R.Disjoint (vscrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hS hl => bytesAt_frame fSE (vin_apart hK hS) hl
    simp only [Contract.clear, pdChkContract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hsi, hdx, hcx, h8, h9, hE 0 (by decide), vArg, hm₂, hg₂ .rax (by decide)] at hpost
    rw [pre_words hp fSE,
      b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKe hp.des (by have := hp.wE; dsimp only; omega),
      b (R := ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩) (by rw [← hp.hsg]; exact hp.dKsg) (by rw [← hp.hsg]; exact hp.dsgs)
        (by have := hp.wSg; have := hp.hsg; dsimp only; omega)] at hpost
    exact fun hcache => hpost _ (bytesAt_length ..) hcache


end VG.Proof.RsaPss.X86_64.Pc
