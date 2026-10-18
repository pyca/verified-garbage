module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SPriv
public import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the private-key operation's call

`vg_rsa_private_checked`'s precondition with its stack arguments in the
frame (`privS_pre`), and what its call leaves (`privS_call`): `out` holds
its outcome for `EM`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr oEm oRsa)
open VG.Proof.RsaOaep.X86_64 (decStack stkD fb frR frame_subD ret_subD below_subD Lay Rep upd nW StepW outR
  stackArg_entry kbD fb_eqD fb_sub8D owned_one slot_eq)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK PrivImpl)

variable {s : State}

/-- After `privArgs`: its stack arguments in the frame, its registers, and
`EM`. -/
structure SSet (s t : State) : Prop where
  he : SEnv s t
  L : Lay t (fb s) (stackArg s 14)
  w : ∀ i < 14, word t.mem (fb s) (8 * i) = pArg s i
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rcx
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = s.gpr .rcx
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaS (s : State) : Region := ⟨off (stackArg s 14) oRsa, (stackArg s 15 - 1024).toNat * 8⟩

/-- `EM`. -/
def emS (s : State) : Region := ⟨off (stackArg s 14) oEm, (s.gpr .rcx).toNat⟩

/-- What `vg_rsa_private_checked` reads: `n`, `e`, `EM`, the private key and
its stack arguments. -/
def privRdS (s : State) : List Region :=
  [snR s, seR s, emS s, spR s, sqR s, sdpR s, sdqR s, sqiR s, ⟨fb s, 112⟩]

/-- What it writes: `out` and the rest of the working space. -/
def privWrS (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, rsaS s]

theorem kbS_toNat (hp : SPre s) : (kbD s).toNat + decStack + 168 ≤ 2 ^ 64 ∧
    (kbD s).toNat + decStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kbD, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega

theorem rsaS_toNat (hp : SPre s) :
    (stackArg s 15 - 1024).toNat = (stackArg s 15).toNat - 1024 ∧
      (off (stackArg s 14) oRsa).toNat = (stackArg s 14).toNat + oRsa := by
  have := hp.hsl; have := hp.wS; have := hp.k1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega

theorem rsaS_sub (hp : SPre s) : Region.Sub (rsaS s) (sscrR s) := by
  have := hp.hsl
  have ⟨r1, _⟩ := rsaS_toNat hp
  simp only [rsaS, sscrR]; rw [r1]
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem emS_sub (hp : SPre s) : Region.Sub (emS s) (sscrR s) := by
  have := hp.hsl; have := hp.k2
  exact Offset.sub_base _ (by unfold oEm; omega)

theorem outS_eq (hp : SPre s) : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) = outR s := by
  simp [outR, hp.hsi]

theorem privS_args (hp : SPre s) {t : State} (h : SSet s t) (rd wr : List Region) {i : Nat} (hi : i < 14) :
    stackArg (t.callEntry.withRegions rd wr) i = pArg s i := by
  have hF := fb_toNatS hp
  rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold decStack privStack frameBytes at *; omega) _ _
    (by have := hp.sp2; unfold frameBytes at *; omega)]
  exact h.w i hi

theorem stackArgAddr_entryS {t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem privS_pre (hp : SPre s) {t : State} (h : SSet s t) :
    privK.pre (t.callEntry.withRegions (privRdS s) (privWrS s)) := by
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdS s) (privWrS s)) i = pArg s i :=
    fun hi => privS_args hp h _ _ hi
  simp only [privK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp,
    stackArgAddr_entryS h.he.rsp, e (show 0 < 14 by decide), e (show 1 < 14 by decide), e (show 2 < 14 by decide),
    e (show 3 < 14 by decide), e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide),
    e (show 7 < 14 by decide), e (show 8 < 14 by decide), e (show 9 < 14 by decide),
    e (show 10 < 14 by decide), e (show 11 < 14 by decide), e (show 12 < 14 by decide),
    e (show 13 < 14 by decide), fb_sub8D, pArg, Nat.reduceSub]
  have ⟨hK1, hK2⟩ := kbS_toNat hp
  have ⟨r1, r2⟩ := rsaS_toNat hp
  have hk1 := hp.k1; have hk2 := hp.k2
  have hsl := hp.hsl; have wS := hp.wS
  have hsi := hp.hsi
  have e5 : decStack = 3672 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 408 := rfl
  have hfb : fb s = off (kbD s) (8 + privStack) := fb_eqD s
  have sK : Region.Sub ⟨kbD s, privStack⟩ (stkD s) := Region.sub_prefix (by omega)
  have sR : Region.Sub ⟨off (kbD s) privStack, 8⟩ (stkD s) := Offset.sub_base _ (by omega)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkD s) := by rw [hfb]; exact Offset.sub_base _ (by omega)
  have dRA : (⟨off (kbD s) privStack, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dKA : (⟨kbD s, privStack⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by omega) (by omega)
  have hoff : (off (kbD s) privStack).toNat = (kbD s).toNat + privStack := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have r1' : (stackArg s 15 - 1024#64).toNat = (stackArg s 15).toNat - 1024 := r1
  have kbsub : kbD s = off (kbD s) privStack - BitVec.ofNat 64 privStack := by
    rw [off, BitVec.add_sub_cancel]
  rw [← kbsub]
  have em := emS_sub hp
  have rs := rsaS_sub hp
  have dEmR : (emS s).Disjoint (rsaS s) := by
    simp only [emS, rsaS]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega) (by unfold oRsa; omega)
  have hO : ∀ {r : Region}, (soR s).Disjoint r → (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r :=
    fun h => by rw [← hsi]; exact h
  have hKO : (stkD s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by rw [← hsi]; exact hp.dKO
  have dSA : (sscrR s).Disjoint ⟨fb s, 112⟩ := (hp.dKs.sub_left sA).symm
  refine ⟨by omega, by omega, rfl, rfl, hO hp.dOn, hO hp.dOe, (hO hp.dOs).sub_right em, hO hp.dOp, hO hp.dOq,
    hO hp.dOdp, hO hp.dOdq, hO hp.dOqi, (hO hp.dOs).sub_right rs, (hKO.sub_left sA).symm,
    hp.dns.sub_right rs, hp.des.sub_right rs, dEmR, hp.dps.sub_right rs, hp.dqs.sub_right rs,
    hp.ddps.sub_right rs, hp.ddqs.sub_right rs, hp.dqis.sub_right rs, dSA.sub_left rs,
    hKO.sub_left sR, hp.dKn.sub_left sR, hp.dKe.sub_left sR, (hp.dKs.sub_left sR).sub_right em,
    hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR, hp.dKqi.sub_left sR,
    (hp.dKs.sub_left sR).sub_right rs, dRA,
    hKO.sub_left sK, hp.dKn.sub_left sK, hp.dKe.sub_left sK, (hp.dKs.sub_left sK).sub_right em,
    hp.dKp.sub_left sK, hp.dKq.sub_left sK, hp.dKdp.sub_left sK, hp.dKdq.sub_left sK, hp.dKqi.sub_left sK,
    (hp.dKs.sub_left sK).sub_right rs, dKA,
    by rw [← hsi]; exact hp.wO, hp.wN, hp.wE,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega, hp.wP, hp.wQ, hp.wDp, hp.wDq,
    hp.wQi, by rw [r1', r2]; unfold oRsa; omega, hp.lv, trivial, trivial, hp.el1, hp.el2, hp.pl1, hp.pl2, hp.ql1,
    hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by rw [r1']; unfold Spec.Rsa.scratchWords; omega⟩

theorem privS_covers (hp : SPre s) {t : State} (h : SSet s t) :
    Covers (privRdS s ++ privWrS s) (t.rd ++ t.wr) ∧ Covers (privWrS s) t.wr := by
  have hk2 := hp.k2; have hsl := hp.hsl; have hsi := hp.hsi
  have ⟨r1, r2⟩ := rsaS_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hwr := h.he.wr
  have cw : Covers (privWrS s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWrS, rsaS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨outR s, by simp, 0, z _, by simp only [outR]; omega⟩
    · exact ⟨sscrR s, by simp, oRsa, rfl, by
        show oRsa + (stackArg s 15 - 1024).toNat * 8 ≤ (stackArg s 15).toNat * 8; rw [r1]; unfold oRsa; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.he.rd]; exact hx)
  simp only [privRdS, emS, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd (snR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd (seR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨sscrR s, List.mem_append_right _ (by rw [hwr]; simp), oEm, rfl, by
      show oEm + (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat * 8; unfold oEm; omega⟩
  · exact ⟨_, hrd (spR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd (sqR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd (sdpR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd (sdqR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd (sqiR s) (by rw [hp.hrd]; simp [srd]), 0, z _, by dsimp only; omega⟩
  · exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..), 0, z _,
      by show 0 + 112 ≤ frameBytes; decide⟩

/-- A word of the frame, apart from what the call writes. -/
theorem frame_apartS (hp : SPre s) {k : Nat} (hk : k < nW) :
    ∀ r ∈ privWrS s ++ [below (fb s) (8 + privStack)], (⟨off (fb s) (8 * k), 8⟩ : Region).Disjoint r := by
  have hF := fb_toNatS hp
  have := hp.sp2
  have sF : Region.Sub ⟨off (fb s) (8 * k), 8⟩ (stkD s) :=
    fun x h => frame_subD s x (Offset.sub_base _ (by unfold nW frameBytes at *; omega) x h)
  intro r hr
  simp only [privWrS, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [outS_eq hp]; exact hp.dKO.sub_left sF
  · exact (hp.dKs.sub_left sF).sub_right (rsaS_sub hp)
  · exact Offset.disjoint_below _ (by unfold nW frameBytes privStack at *; omega)

/-- The private-key operation's outcome for `EM` (`em`). -/
def privOutS (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)

theorem privS_call (v : PrivImpl) (hp : SPre s) {t : State} (h : SSet s t) :
    WP isa (.call v.name v.code) t fun t' => SEnv s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (privOutS s (Spec.Rsa.bytesAt t.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat)) := by
  obtain ⟨hc, hw⟩ := privS_covers hp h
  have hdp := v.depth
  have e2 : privStack = 3256 := rfl
  have hF := fb_toNatS hp
  refine WP.of_funs (WP.of_syms (WP.call_sp_mx (k := privK) v.ok (SpSafe.of_all v.spSafe) (by omega)
    (privS_pre hp h) hc hw ?_))
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx hsy hfu
  rw [h.he.rsp] at hf
  have hf' : Frame (privWrS s ++ [below (fb s) (8 + privStack)]) t.mem s'.mem :=
    Frame.below_mono hf (by omega) (by have := hp.sp2; unfold frameBytes at *; omega)
  have hfe : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hfE : FrS s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdS s) (privWrS s)) i = pArg s i :=
    fun hi => privS_args hp h _ _ hi
  have bo : ∀ {p : Addr} {len : Nat}, (stkD s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (⟨p, len⟩ : Region).Disjoint (sscrR s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hs hl => FrS.bytes hfE hk ho hs.symm hl
  have bEm : Spec.Rsa.bytesAt t.callEntry.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt t.mem (off (stackArg s 14) oEm) (s.gpr .rcx).toNat := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (hfe.sub fun r hr => ⟨r, hr, fun _ h => h⟩) _ fun r hr hc' => ?_
    rw [List.mem_singleton.mp hr] at hc'
    have := hp.k2; have := hp.hsl
    exact ((hp.dKs.sub_left (below_subD s (by decide))).sub_right (emS_sub hp)) _ hc'
      (Offset.contains_base _ (by have := List.mem_range.mp hi; omega) (by have := List.mem_range.mp hi; omega))
  simp only [privK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rdx, h.rcx, h.r8, h.r9, hm₂,
    hg₂ .rax (by decide), e (show 0 < 14 by decide), e (show 2 < 14 by decide), e (show 3 < 14 by decide),
    e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide), e (show 8 < 14 by decide),
    e (show 10 < 14 by decide), pArg, Nat.reduceSub] at hpost
  rw [bo hp.dKn hp.dOn hp.dns (by have := hp.wN; omega), bo hp.dKe hp.dOe hp.des (by have := hp.wE; omega),
    bEm, bo hp.dKp hp.dOp hp.dps (by have := hp.wP; omega), bo hp.dKq hp.dOq hp.dqs (by have := hp.wQ; omega),
    show (stackArg s 1).toNat = (stackArg s 5).toNat from hp.hdpl.symm,
    bo hp.dKdp hp.dOdp hp.ddps (by have := hp.wDp; omega),
    show (stackArg s 3).toNat = (stackArg s 7).toNat from hp.hdql.symm,
    bo hp.dKdq hp.dOdq hp.ddqs (by have := hp.wDq; omega),
    show (stackArg s 5).toNat = (stackArg s 9).toNat by rw [hp.hdpl, hp.hqil],
    bo hp.dKqi hp.dOqi hp.dqis (by have := hp.wQi; omega)] at hpost
  have hsub : ∀ r ∈ privWrS s ++ [below (fb s) (8 + privStack)], ∃ r' ∈ [stkD s, outR s, sscrR s],
      Region.Sub r r' := fun r hr => by
    simp only [privWrS, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, by rw [outS_eq hp]; exact fun _ h => h⟩
    · exact ⟨sscrR s, by simp, rsaS_sub hp⟩
    · exact ⟨stkD s, by simp, below_subD s (le_refl _)⟩
  have hown : Owned decStack s (privWrS s ++ [below (fb s) (8 + privStack)]) :=
    ((stkOS s).cons ((owned_one hp.owned (r := outR s) (by simp)).cons
      (owned_one hp.owned (r := sscrR s) (by simp)))).of_sub hsub
  refine ⟨⟨(hcs .rsp (by decide)).trans h.he.rsp, hrd.trans h.he.rd, hwr.trans h.he.wr,
    fun r hr hne => (hcs r hr).trans (h.he.cs r hr hne), hmx.trans h.he.mx, h.he.fr.trans (hf'.sub hsub),
    h.he.world.step hfu hsy hf' hown, h.he.own, h.he.scr, h.he.sp16⟩, ?_⟩
  rw [show (stackArg s 9).toNat = (stackArg s 1).toNat from hp.hqil,
    show (stackArg s 7).toNat = (stackArg s 3).toNat from hp.hdql] at hpost
  exact hpost

end VG.Proof.RsaPss.X86_64
