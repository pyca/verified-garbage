import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall

/-!
# RSASSA-PSS verification on x86-64: the call of `vg_rsa_public_checked`

With its stack arguments in the frame's first 4 words (the signature, `k`,
the rest of `scratch`), `vg_rsa_public_checked` runs under its contract
(`pub_pre`) and returns with `EM`'s place (`scratch + oEm`) written as it
says, the frame and the rest of our working space kept (`pub_call`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {G : Spec.Mgf1.Hash}

/-- What the public-key operation reads: `n`, `e`, the signature and its
stack arguments. -/
def vRd (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩, ⟨fb s, 32⟩]

/-- What it writes: `EM`'s place, and the rest of the working space. -/
def vWr (s : State) : List Region :=
  [⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩,
    ⟨off (stackArg s 3) oRsa, (stackArg s 4 - BitVec.ofNat 64 1024).toNat * 8⟩]

/-- Its stack arguments. -/
def vArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => s.gpr .r9
  | 1 => s.gpr .rsi
  | 2 => off (stackArg s 3) oRsa
  | _ => stackArg s 4 - BitVec.ofNat 64 1024

theorem vfb_sub8 {s : State} (hp : VPre G s) : (fb s - 8).toNat = (fb s).toNat - 8 := by
  have hF := vfb_toNat hp; have := hp.sp1
  rw [BitVec.toNat_sub]; unfold verifyStack frameBytes at *
  rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega

theorem vstackArg_call {s t : State} (hp : VPre G s) (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat}
    (hi : i < 4) : stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hF := vfb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hsep := Offset.sep (fb s - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega)
    (by unfold verifyStack frameBytes at *; omega)
  rw [show fb s - 8 + BitVec.ofNat 64 0 = fb s - 8 from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  have ea : fb s - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off (fb s) (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  rw [ea]

theorem vsc_sub {s : State} (hp : VPre G s) :
    (stackArg s 4 - 1024#64).toNat = (stackArg s 4).toNat - 1024 := by
  have := hp.hsl; have := hp.k1
  rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega

theorem pub_pre {s t : State} (hp : VPre G s) (hsp : t.gpr .rsp = fb s)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = off (stackArg s 3) oEm)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi) (hcx : t.gpr .rcx = s.gpr .rsi)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pubChkContract.pre (t.callEntry.withRegions (vRd s) (vWr s)) := by
  have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (vRd s) (vWr s)) i = vArg s i :=
    fun i hi => (vstackArg_call hp hsp _ _ hi).trans (hargs i hi)
  simp only [pubChkContract, pubContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hsp, stackArgAddr_call hsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), vArg]
  have hF := vfb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 400 := rfl
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have h8' := vfb_sub8 hp
  have hsc := vsc_sub hp
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
  refine ⟨by omega, rfl, rfl, (hp.dns.sub_right sI).symm, (hp.des.sub_right sI).symm, (dsgs.sub_right sI).symm,
    dIR, hsA.sub_left sI,
    hp.dns.sub_right sR, hp.des.sub_right sR, dsgs.sub_right sR, hsA.sub_left sR,
    (hp.dKs.sub_left sRet).sub_right sI, hp.dKn.sub_left sRet, hp.dKe.sub_left sRet, dKsg.sub_left sRet,
    (hp.dKs.sub_left sRet).sub_right sR, dRA,
    by rw [toNat_off (by omega)]; omega, hp.wN, hp.wE, wSg, by rw [toNat_off (by omega), hsc]; omega,
    ⟨hk1, hk2⟩, trivial, trivial, hp.L1, hp.L2, by unfold Spec.Rsa.scratchWords; rw [hsc]; omega⟩

theorem pub_covers {s t : State} (hp : VPre G s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr) :
    Covers (vRd s ++ vWr s) (t.rd ++ t.wr) ∧ Covers (vWr s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hk1 := hp.k1
  have c1 : oEm = 2560 := rfl
  have c2 : oRsa = 8192 := rfl
  have hsc := vsc_sub hp
  have hfr : frR s ∈ t.wr := by rw [hwr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (vWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [vWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hscr, oEm, rfl, by dsimp only; omega⟩
    · exact ⟨_, hscr, oRsa, rfl, by dsimp only; rw [hsc]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hin : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [hrd]; exact hx)
  simp only [vRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hin _ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨⟨s.gpr .r9, (stackArg s 0).toNat⟩, hin _ (by rw [hp.hrd]; simp), 0, z _,
      by dsimp only; rw [hp.hsg]; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; decide⟩

theorem pub_call {pubN : String} {pubC : Prog isa}
    (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
    (hsp : SpSafe pubC) (hd : pubC.x86_64Depth = 0)
    {s t : State} (hp : VPre G s) (hst : t.gpr .rsp = fb s) (hrd : t.rd = s.rd) (hwr : t.wr = frR s :: s.wr)
    (hM : Frame (vwrR s) s.mem t.mem)
    (hargs : ∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) (hdi : t.gpr .rdi = off (stackArg s 3) oEm)
    (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi) (hcx : t.gpr .rcx = s.gpr .rsi)
    (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call pubN pubC) t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame (vwrR s) s.mem t'.mem ∧
      (∀ x, ((frR s).Contains x 1 ∨ ((⟨stackArg s 3, oRsa⟩ : Region).Contains x 1 ∧
        ¬ (⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ : Region).Contains x 1)) → t'.mem x = t.mem x) ∧
      Spec.Rsa.written t'.mem (off (stackArg s 3) oEm) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)) := by
  obtain ⟨hc, hw⟩ := pub_covers hp hrd hwr
  have hpre := pub_pre hp hst hargs hdi hsi hdx hcx h8 h9
  refine X86_64.WP.callF (k := pubChkContract) (fun s h => hv s h) hsp (by omega) hpre hc hw ?_
  intro t' hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  have hF := vfb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 400 := rfl
  have c2 : oRsa = 8192 := rfl
  have c1 : oEm = 2560 := rfl
  have hsc := vsc_sub hp
  rw [hst, hd] at hf
  have sEm : Region.Sub ⟨off (stackArg s 3) oEm, (s.gpr .rsi).toNat⟩ (vscrR s) := Offset.sub_base _ (by omega)
  have sScr : Region.Sub ⟨off (stackArg s 3) oRsa, (stackArg s 4 - 1024#64).toNat * 8⟩ (vscrR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have sBel : Region.Sub (below (fb s) (0 + 8)) (vstkR s) := vret_sub s
  refine ⟨hrd', hwr', hcs, hmx, hM.trans (hf.sub fun r hr => ?_), fun x hx => hf x fun r hr hc => ?_, ?_⟩
  · simp only [vWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sEm⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sScr⟩
    · exact ⟨_, List.mem_cons_self .., sBel⟩
  · simp only [vWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have dFb : (frR s).Disjoint (below (fb s) (0 + 8)) := Offset.base_disjoint_below (fb s) (by omega)
    rcases hx with hx | ⟨hx, hnx⟩ <;> rcases hr with rfl | rfl | rfl
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sEm x hc)
    · exact (hp.dKs.sub_left (vframe_sub s)) x hx (sScr x hc)
    · exact dFb x hx hc
    · exact hnx hc
    · exact (Offset.base_disjoint (stackArg s 3) (e := oRsa) (n := (stackArg s 4 - 1024#64).toNat * 8)
        (k := oRsa) (le_refl _) (by rw [hsc]; omega)) x hx hc
    · exact ((hp.dKs.sub_left sBel).symm.sub_left (Region.sub_prefix (by omega))) x hx hc
  · have hE : ∀ i < 4, stackArg (t.callEntry.withRegions (vRd s) (vWr s)) i = vArg s i :=
      fun i hi => (vstackArg_call hp hst _ _ hi).trans (hargs i hi)
    have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
      rw [State.callEntry_mem, hst]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
    have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
    have b : ∀ {R : Region}, (vstkR s).Disjoint R → R.Disjoint (vscrR s) → R.len ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t.callEntry.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
      fun hK hS hl => bytesAt_frame fSE (vin_apart hK hS) hl
    simp only [pubChkContract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
      hdi, hdx, hcx, h8, h9, hE 0 (by decide), vArg, hm₂, hg₂ .rax (by decide)] at hpost
    rw [b (R := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) hp.dKn hp.dns (by have := hp.wN; dsimp only; omega),
      b (R := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) hp.dKe hp.des (by have := hp.wE; dsimp only; omega),
      b (R := ⟨s.gpr .r9, (s.gpr .rsi).toNat⟩) (by rw [← hp.hsg]; exact hp.dKsg) (by rw [← hp.hsg]; exact hp.dsgs)
        (by have := hp.wSg; have := hp.hsg; dsimp only; omega)] at hpost
    exact hpost

/-- The public-key operation's arguments: its stack arguments in the frame's
first words, and its registers. -/
theorem pubArgs_ok {s : State} {u : State} (L : Lay u (fb s) (stackArg s 3))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 3) V W)
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h38 : W 38 = s.gpr .r9) :
    WP isa (.block pubArgs) u fun u' => Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Lay u' (fb s) (stackArg s 3) ∧
      (∃ W', Rep u'.mem (fb s) (stackArg s 3) V W' ∧ (∀ i < 4, W' i = vArg s i) ∧ (∀ i < nW, 4 ≤ i → W' i = W i)) ∧
      u'.gpr .rdi = off (stackArg s 3) oEm ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = s.gpr .rdi ∧
      u'.gpr .rcx = s.gpr .rsi ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx := by
  have G' := L.geo
  have hs : u.mem.readW (off (fb s) sScr) 64 = stackArg s 3 := L.slot
  set S := stackArg s 3
  have Ra := R.wf G' (k := 0) (by decide) (s.gpr .r9)
  have Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rsi)
  have Rc := Rb.wf G' (k := 2) (by decide) (off S oRsa)
  have Rd := Rc.wf G' (k := 3) (by decide) (stackArg s 4 - BitVec.ofNat 64 1024)
  simp only [Nat.reduceMul, off_zero] at Ra Rb Rc Rd
  have hst0 : InRegions u.wr (fb s) 8 := by simpa only [off_zero] using L.st (d := 0) (by decide)
  have f0 : u.mem.readW (off (fb s) sSig) 64 = s.gpr .r9 := by
    rw [R.rd (d := sSig) 38 rfl (by decide), h38]
  have f1 : (u.mem.writeW (fb s) (s.gpr .r9)).readW (off (fb s) sK) 64 = s.gpr .rsi := by
    rw [Ra.rd (d := sK) 17 rfl (by decide)]; simp [upd, h17]
  have f2 : ((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).readW
      (off (fb s) sScr) 64 = S := by
    rw [Rb.rd (d := sScr) 21 rfl (by decide)]; simp only [upd, Nat.reduceEqDiff, ite_false]
    exact (R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs
  have f3 : (((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).readW (off (fb s) sScrLen) 64 = stackArg s 4 := by
    rw [Rc.rd (d := sScrLen) 22 rfl (by decide)]; simp [upd, h22]
  set m4 := ((((u.mem.writeW (fb s) (s.gpr .r9)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off S oRsa)).writeW (off (fb s) 24) (stackArg s 4 - BitVec.ofNat 64 1024)) with hm4
  have g : ∀ k, 4 ≤ k → k < nW → m4.readW (off (fb s) (8 * k)) 64 = W k := fun k hk hk' => by
    refine (Rd.fr k hk').trans ?_; simp only [upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]
  have g21 : m4.readW (off (fb s) sScr) 64 = S :=
    (g 21 (by decide) (by decide)).trans ((R.rd (d := sScr) 21 rfl (by decide)).symm.trans hs)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem = m4 ∧
      u'.gpr .rdi = off S oEm ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = s.gpr .rdi ∧ u'.gpr .rcx = s.gpr .rsi ∧
      u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx) ?_ rfl) fun u2 ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, k2⟩ => ?_
  · xrun [pubArgs, scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sSig) (by decide), f0,
      L.ld (d := sScr) (by decide), VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus, hst0,
      L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
      L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide),
      L.ld (d := sN) (by decide), L.ld (d := sE) (by decide), L.ld (d := sEl) (by decide), f1, f2, f3, g21,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 1024 < 2 ^ 31 by decide),
      show m4.readW (off (fb s) sK) 64 = s.gpr .rsi from (g 17 (by decide) (by decide)).trans h17,
      show m4.readW (off (fb s) sN) 64 = s.gpr .rdi from (g 18 (by decide) (by decide)).trans h18,
      show m4.readW (off (fb s) sE) 64 = s.gpr .rdx from (g 19 (by decide) (by decide)).trans h19,
      show m4.readW (off (fb s) sEl) 64 = s.gpr .rcx from (g 20 (by decide) (by decide)).trans h20,
      show S + BitVec.ofNat 64 oRsa = off S oRsa from rfl, show S + BitVec.ofNat 64 oEm = off S oEm from rfl]
    rw [show BitVec.signExtend 64 (1024 : BitVec 32) = BitVec.ofNat 64 1024 by decide] at *
    rw [← hm4, g21]
    exact ⟨rfl, rfl, (g 17 (by decide) (by decide)).trans h17,
      (g 18 (by decide) (by decide)).trans h18, (g 17 (by decide) (by decide)).trans h17,
      (g 19 (by decide) (by decide)).trans h19, (g 20 (by decide) (by decide)).trans h20⟩
  have R2 : Rep u2.mem (fb s) S V _ := hm ▸ Rd
  refine ⟨k2, L.of_rep' R R2 (by simp [upd]) (k2.gpr (by decide)) k2.2.2,
    ⟨_, R2, fun i hi => ?_, fun i hi h4 => ?_⟩, h1, h2, h3, h4, h5, h6⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with h | h | h | h <;> subst h
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]; rfl
    · simp only [upd, vArg, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [upd]
    rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]

end VG.Proof.RsaPss.X86_64
