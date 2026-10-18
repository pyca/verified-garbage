module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VHead
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

/-!
# RSASSA-PSS verification on x86-64: the public operation

Its arguments (`pubArgsV_ok`): `EM`'s place in our working space, `k`,
`pre`, `e`, the signature and the rest of the working space; its
precondition (`callV_pre`), and what the call leaves (`callV_ok`): `EM`
holds RSAVP1 of the signature, or zeros, if `pre` holds the values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sN sK sE sEl oEm oRsa scr lay arg)
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub argAddr stackArgAddr_j Lay Rep Geo upd ea_sp
  StepW off_plus nW stackArg_entry)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

variable {s : State}

/-- Memory changed only in the frame, from memory changed only where the
function writes. -/
theorem FrV.frame {m m' : Mem} (h : FrV s m) (h' : Frame [frR s] m m') : FrV s m' :=
  h.trans (h'.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s⟩)

/-- The public operation's arguments. -/
theorem pubArgsV_ok (hp : VPre s) {u : State} (L : Lay u (fb s) (stackArg s 4)) (hrd : u.rd = s.rd)
    (hf : FrV s u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) (stackArg s 4) V W)
    (w21 : W 21 = stackArg s 0) (w23 : W 23 = s.gpr .rsi) (w24 : W 24 = s.gpr .rdx) (w25 : W 25 = s.gpr .rcx)
    (w26 : W 26 = stackArg s 5) :
    WP isa (.block pubArgs) u fun u' => Lay u' (fb s) (stackArg s 4) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] u u' ∧
      Rep u'.mem (fb s) (stackArg s 4) V (upd (upd (upd (upd W 0 (stackArg s 0)) 1 (s.gpr .rsi)) 2
        (off (stackArg s 4) oRsa)) 3 (stackArg s 5 - 1024)) ∧
      u'.gpr .rdi = off (stackArg s 4) oEm ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 6 ∧
      u'.gpr .rcx = stackArg s 7 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have Ra := R.wf G' (k := 0) (by decide) (stackArg s 0)
  have z : off (fb s) (8 * 0) = fb s := BitVec.add_zero _
  rw [z] at Ra
  have Rb := Ra.wf G' (k := 1) (by decide) (s.gpr .rsi)
  have Rc := Rb.wf G' (k := 2) (by decide) (off (stackArg s 4) oRsa)
  have R1 := Rc.wf G' (k := 3) (by decide) (stackArg s 5 - 1024)
  rw [show 8 * 1 = 8 from rfl] at Rb Rc R1
  rw [show 8 * 2 = 16 from rfl] at Rc R1
  rw [show 8 * 3 = 24 from rfl] at R1
  have h0 : InRegions u.wr (fb s) 8 := by rw [← z]; exact L.st (d := 0) (by decide)
  have f0 : Frame [frR s] u.mem (u.mem.writeW (fb s) (stackArg s 0)) := by
    have := frame_wV hp (Frame.refl [frR s] u.mem) (d := 0) (by decide) (stackArg s 0)
    rwa [show off (fb s) 0 = fb s from BitVec.add_zero _] at this
  have hfw : FrV s ((((u.mem.writeW (fb s) (stackArg s 0)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
      (off (fb s) 16) (off (stackArg s 4) oRsa)).writeW (off (fb s) 24) (stackArg s 5 - 1024)) := by
    exact hf.frame (frame_wV hp (frame_wV hp (frame_wV hp f0 (by decide) _) (by decide) _) (by decide) _)
  have a6 := arg_keepV hp hfw (j := 6) (by decide)
  have a7 := arg_keepV hp hfw (j := 7) (by decide)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u' => u'.mem =
      (((u.mem.writeW (fb s) (stackArg s 0)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
        (off (fb s) 16) (off (stackArg s 4) oRsa)).writeW (off (fb s) 24) (stackArg s 5 - 1024) ∧
      u'.gpr .rdi = off (stackArg s 4) oEm ∧ u'.gpr .rsi = s.gpr .rsi ∧ u'.gpr .rdx = stackArg s 6 ∧
      u'.gpr .rcx = stackArg s 7 ∧ u'.gpr .r8 = s.gpr .rdx ∧ u'.gpr .r9 = s.gpr .rcx) ?_ rfl)
    fun u' ⟨⟨hm, h1, h2, h3, h4, h5, h6⟩, kk⟩ =>
    ⟨L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2, kk, by rw [hm]; exact R1,
      h1, h2, h3, h4, h5, h6⟩
  xrun [pubArgs, scr, Impl.Mgf1.X86_64.scr, lay, arg, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), L.ld (d := sScrLen) (by decide),
    L.ld (d := sSig) (by decide), L.ld (d := sE) (by decide),
    L.ld (d := sEl) (by decide), hs, R.slot (d := sSig) (k := 21) rfl (by decide) w21,
    R.slot (d := sK) (k := 23) rfl (by decide) w23,
    R.slot (d := sScrLen) (k := 26) rfl (by decide) w26,
    h0, L.st (d := 8) (by decide), L.st (d := 16) (by decide), L.st (d := 24) (by decide),
    R1.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .rsi) (by simp [upd, w23]),
    R1.slot (d := sE) (k := 24) rfl (by decide) (v := s.gpr .rdx) (by simp [upd, w24]),
    R1.slot (d := sEl) (k := 25) rfl (by decide) (v := s.gpr .rcx) (by simp [upd, w25]),
    Ra.slot (d := sK) (k := 23) rfl (by decide) (v := s.gpr .rsi) (by simp [upd, w23]),
    Rb.slot (d := sScr) (k := 14) rfl (by decide) (v := stackArg s 4)
      (by simp only [upd]; exact (R.fr 14 (by decide)).symm.trans hs),
    Rc.slot (d := sScrLen) (k := 26) rfl (by decide) (v := stackArg s 5) (by simp [upd, w26]),
    R1.slot (d := sScr) (k := 14) rfl (by decide) (v := stackArg s 4)
      (by simp only [upd]; exact (R.fr 14 (by decide)).symm.trans hs),
    hp.arg_in hrd (j := 6) (by decide), hp.arg_in hrd (j := 7) (by decide), a6, a7,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oRsa < 2 ^ 31 by decide),
    show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 from by decide]

/-! ## The call -/

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaRV (s : State) : Region := ⟨off (stackArg s 4) oRsa, (stackArg s 5 - 1024).toNat * 8⟩

/-- `EM`'s place. -/
def emRV (s : State) : Region := ⟨off (stackArg s 4) oEm, (s.gpr .rsi).toNat⟩

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, the
signature and its stack arguments. -/
def callRdV (s : State) : List Region := [vpreR s, eR s, ⟨stackArg s 0, (s.gpr .rsi).toNat⟩, ⟨fb s, 32⟩]

/-- What it writes: `EM`'s place and the rest of the working space. -/
def callWrV (s : State) : List Region := [emRV s, rsaRV s]

theorem rsaV_toNat (hp : VPre s) :
    (stackArg s 5 - 1024).toNat = (stackArg s 5).toNat - 1024 ∧
      (off (stackArg s 4) oRsa).toNat = (stackArg s 4).toNat + oRsa := by
  have := hp.hsl'; have := hp.wS; have := hp.k1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa; omega

theorem rsaV_sub (hp : VPre s) : Region.Sub (rsaRV s) (vscrR s) := by
  have ⟨h1, h2⟩ := rsaV_toNat hp
  have := hp.hsl'
  simp only [rsaRV, vscrR]
  rw [h1]
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem emV_sub (hp : VPre s) : Region.Sub (emRV s) (vscrR s) := by
  have := hp.hsl'; have := hp.k2
  exact Offset.sub_base _ (by unfold oEm; omega)

theorem callV_pre (hp : VPre s) {t : State} (hsp : t.gpr .rsp = fb s)
    (hw0 : t.mem.readW (off (fb s) (8 * 0)) 64 = stackArg s 0) (hw1 : t.mem.readW (off (fb s) (8 * 1)) 64 = s.gpr .rsi)
    (hw2 : t.mem.readW (off (fb s) (8 * 2)) 64 = off (stackArg s 4) oRsa)
    (hw3 : t.mem.readW (off (fb s) (8 * 3)) 64 = stackArg s 5 - 1024)
    (hdi : t.gpr .rdi = off (stackArg s 4) oEm) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 6)
    (hcx : t.gpr .rcx = stackArg s 7) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    VG.Proof.Bignum.X86_64.pdContract.pre (t.callEntry.withRegions (callRdV s) (callWrV s)) := by
  have hF := fb_toNatV hp
  have hsp1 := hp.sp1; have hsp2 := hp.sp2
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRdV s) (callWrV s)) i =
      t.mem.readW (off (fb s) (8 * i)) 64 :=
    fun i hi => stackArg_entry hsp (by unfold encStack frameBytes at *; omega) _ _ (by unfold frameBytes at *; omega)
  have hA : stackArgAddr (t.callEntry.withRegions (callRdV s) (callWrV s)) 0 = fb s := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
    rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  simp only [VG.Proof.Bignum.X86_64.pdContract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp, hA,
    hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hw0, hw1, hw2, hw3]
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl'; have wS := hp.wS; have hsg := hp.hsg
  have ⟨r1, r2⟩ := rsaV_toNat hp
  have e8 : fb s - 8 = fb s - BitVec.ofNat 64 8 := rfl
  have sF : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := Offset.sub_below (s.gpr .rsp) (a := frameBytes) (n := 32) (b := encStack) (m := encStack)
      (by decide) (by decide)
    exact this
  have sR : Region.Sub ⟨fb s - 8, 8⟩ (stkR s) := by
    rw [e8]
    exact fun x h => ret_sub s x (Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide)
      (by decide) x h)
  have dRF : Region.Disjoint ⟨fb s - 8, 8⟩ ⟨fb s, 32⟩ := by
    rw [e8]; exact (Offset.base_disjoint_below (fb s) (n := 8) (k := 32) (by omega)).symm
  have dEmR : Region.Disjoint (emRV s) (rsaRV s) := by
    simp only [rsaRV, emRV]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega) (by unfold oRsa; omega)
  have em := emV_sub hp
  have rs := rsaV_sub hp
  have hsig : (⟨stackArg s 0, (s.gpr .rsi).toNat⟩ : Region) = sgR s := by simp [sgR, hsg]
  have dSk : (vscrR s).Disjoint (stkR s) := hp.dKS.symm
  have hf8 : (fb s - 8).toNat = (fb s).toNat - 8 := by
    rw [e8, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega
  refine ⟨by rw [hf8]; unfold frameBytes at *; omega, rfl, rfl,
    (hp.dSp.sub_left em), (hp.deS.symm.sub_left em), by rw [hsig]; exact hp.dgS.symm.sub_left em,
    dEmR, (dSk.sub_right sF).sub_left em,
    hp.dSp.symm.sub_right rs, hp.deS.sub_right rs, by rw [hsig]; exact hp.dgS.sub_right rs,
    (dSk.sub_right sF).sub_left rs,
    (dSk.symm.sub_left sR).sub_right em, hp.dKp.sub_left sR, hp.dKe.sub_left sR,
    by rw [hsig]; exact hp.dKg.sub_left sR, (dSk.symm.sub_left sR).sub_right rs, dRF,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega, hp.wP, hp.wE,
    by rw [← hsg]; exact hp.wG,
    by rw [r1, r2]; unfold oRsa; omega,
    hp.lv, hp.pl, trivial, hp.L1, hp.L2,
    by rw [r1]; unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega⟩

theorem callV_covers (hp : VPre s) {t : State} (hrd : t.rd = s.rd) (hwr : t.wr = [frR s, vscrR s]) :
    Covers (callRdV s ++ callWrV s) (t.rd ++ t.wr) ∧ Covers (callWrV s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl'; have hsg := hp.hsg
  have ⟨r1, r2⟩ := rsaV_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (callWrV s) t.wr := Covers.of_sub fun r hr => by
    simp only [callWrV, rsaRV, emRV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨vscrR s, by simp, oEm, rfl, by dsimp only; unfold oEm; omega⟩
    · exact ⟨vscrR s, by simp, oRsa, rfl, by dsimp only; rw [r1]; unfold oRsa; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [callRdV, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨vpreR s, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp [vrd]), 0, z _, by simp⟩
  · exact ⟨eR s, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp [vrd]), 0, z _, by simp⟩
  · exact ⟨sgR s, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp [vrd]), 0, z _, by simp [hsg]⟩
  · exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; simp), 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- Whether `pre` holds the values for `n`. -/
def VConsistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat)

/-- `pre`, unchanged where the function writes. -/
theorem preV_words (hp : VPre s) {m : Mem} (hf : FrV s m) :
    Spec.Rsa.wordsAt m (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := vpreR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega)
      (by have := hp.wP; have := List.mem_range.mp hi; omega)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKp.symm
    · exact hp.dSp.symm

/-- The call of `vg_rsa_public_precomputed_checked`: `EM` holds RSAVP1 of
the signature, or zeros, if `pre` holds the values for `n`. -/
theorem callV_ok (v : PublicImpl) (hp : VPre s) {t : State} (L : Lay t (fb s) (stackArg s 4)) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 4) V W) (hrd : t.rd = s.rd)
    (hwr : t.wr = [frR s, vscrR s]) (hf : FrV s t.mem)
    (hw0 : W 0 = stackArg s 0) (hw1 : W 1 = s.gpr .rsi) (hw2 : W 2 = off (stackArg s 4) oRsa)
    (hw3 : W 3 = stackArg s 5 - 1024)
    (hdi : t.gpr .rdi = off (stackArg s 4) oEm) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 6)
    (hcx : t.gpr .rcx = stackArg s 7) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' =>
      (VConsistent s → Spec.Rsa.written t'.mem (off (stackArg s 4) oEm) (s.gpr .rsi).toNat
        ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧ StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t' ∧
      Frame (callWrV s ++ [below (fb s) 8]) t.mem t'.mem := by
  have hk2 := hp.k2; have hsl := hp.hsl'
  obtain ⟨hc, hw⟩ := callV_covers hp hrd hwr
  have rd : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = W i := fun i hi => R.rd i rfl (by unfold nW frameBytes; omega)
  have hpre := callV_pre hp L.rsp ((rd 0 (by decide)).trans hw0) ((rd 1 (by decide)).trans hw1)
      ((rd 2 (by decide)).trans hw2) ((rd 3 (by decide)).trans hw3) hdi hsi hdx hcx h8 h9
  refine WP.of_funs (WP.of_syms (WP.call_mx (s := t)
    (k := ⟨VG.Proof.Bignum.X86_64.pdContract.pre, pdChkContract.post, VG.Proof.Bignum.X86_64.pdContract.pub⟩)
    (rd := callRdV s) (wr := callWrV s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_))
  intro s' hrd' hwr' hcs hfr _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy hfu
  rw [v.depth, L.rsp] at hfr
  have hE : stackArg (t.callEntry.withRegions (callRdV s) (callWrV s)) 0 = stackArg s 0 := by
    have hF := fb_toNatV hp
    rw [stackArg_entry L.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega)]
    exact (rd 0 (by decide)).trans hw0
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, L.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrV s t.callEntry.mem :=
    hf.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hE, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [preV_words hp hfE, FrV.bytes hfE hp.dKe hp.deS.symm (by have := hp.wE; omega),
    FrV.bytes hfE (p := stackArg s 0) (len := (s.gpr .rsi).toNat) (by rw [← hp.hsg]; exact hp.dKg)
      (by rw [← hp.hsg]; exact hp.dgS.symm) (by omega)] at hpost
  refine ⟨fun hq => hpost _ (by simp [Spec.Rsa.bytesAt]) hq, hrd', hwr', hcs, hmx, ⟨?_, hfu, hsy⟩, hfr⟩
  rw [L.rsp, hwr]
  refine hfr.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · simp only [callWrV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨vscrR s, List.mem_append_left _ (by simp), emV_sub hp⟩
    · exact ⟨vscrR s, List.mem_append_left _ (by simp), rsaV_sub hp⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨below (fb s) 16, List.mem_append_right _ (List.mem_singleton_self _),
      Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩

end VG.Proof.RsaPss.X86_64
