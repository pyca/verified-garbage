import VerifiedGarbage.Proof.RsaOaep.X86_64.DecFrame
import VerifiedGarbage.Proof.Framework.X86_64.CallSp

/-!
# RSAES-OAEP decryption on x86-64: the private-key operation

`vg_rsa_private_checked`'s precondition with its stack arguments in the
frame (`privD_pre`), and what its call leaves (`privD_call`): `EM`'s place
in the working space holds its outcome for the ciphertext, and the frame its
words.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK PrivImpl)

/-- The base of the stack the function uses. -/
abbrev kbD (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 decStack

theorem fb_eqD (s : State) : fb s = off (kbD s) (8 + privStack) := Offset.sub_ofNat_eq _ (by decide)

theorem fb_sub8D (s : State) : fb s - 8 = off (kbD s) privStack := by
  rw [fb_eqD, off, off, show 8 + privStack = privStack + 8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem kbD_toNat {s : State} (hp : DPre s) : (kbD s).toNat + decStack + 144 ≤ 2 ^ 64 ∧
    (kbD s).toNat + decStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kbD, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega

/-- What `vg_rsa_private_checked` reads: `n`, `e`, the ciphertext, the
private key and its stack arguments. -/
def privRdD (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 13, (s.gpr .r8).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨fb s, 112⟩]

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaD (s : State) : Region := ⟨off (stackArg s 15) oRsa, (stackArg s 16 - 1024).toNat * 8⟩

/-- What it writes: `EM`'s place and the rest of the working space. -/
def privWrD (s : State) : List Region := [⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩, rsaD s]

theorem rsaD_toNat {s : State} (hp : DPre s) :
    (stackArg s 16 - 1024).toNat = (stackArg s 16).toNat - 1024 ∧
      (off (stackArg s 15) oRsa).toNat = (stackArg s 15).toNat + oRsa := by
  have := hp.hsl; have := hp.wS; have := hp.lv.1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega

theorem rsaD_sub {s : State} (hp : DPre s) : Region.Sub (rsaD s) (scrD s) := by
  have := hp.hsl
  have ⟨r1, _⟩ := rsaD_toNat hp
  simp only [rsaD, scrD]; rw [r1]
  exact Offset.sub_base _ (by unfold oRsa; omega)

theorem emD_sub {s : State} (hp : DPre s) : Region.Sub ⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ (scrD s) := by
  have := hp.hsl; have := hp.lv.2
  exact Offset.sub_base _ (by unfold oEm; omega)

/-- The entry state's stack arguments: the frame's words. -/
theorem privD_args {s t : State} (hp : DPre s) (h : DSet s t) (rd wr : List Region) {i : Nat} (hi : i < 14) :
    stackArg (t.callEntry.withRegions rd wr) i = privW s i := by
  have hF := fb_toNatD hp
  rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold decStack privStack frameBytes at *; omega) _ _
    (by have := hp.sp2; unfold frameBytes at *; omega)]
  exact h.R.rd i rfl (by unfold nW frameBytes; omega)

theorem stackArgAddr_entryD {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem privD_pre {s t : State} (hp : DPre s) (h : DSet s t) :
    privK.pre (t.callEntry.withRegions (privRdD s) (privWrD s)) := by
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdD s) (privWrD s)) i = privW s i :=
    fun hi => privD_args hp h _ _ hi
  simp only [privK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp,
    stackArgAddr_entryD h.he.rsp, e (show 0 < 14 by decide), e (show 1 < 14 by decide), e (show 2 < 14 by decide),
    e (show 3 < 14 by decide), e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide),
    e (show 7 < 14 by decide), e (show 8 < 14 by decide), e (show 9 < 14 by decide),
    e (show 10 < 14 by decide), e (show 11 < 14 by decide), e (show 12 < 14 by decide),
    e (show 13 < 14 by decide), fb_sub8D]
  simp only [privW, upd, Nat.reduceEqDiff, ↓reduceIte]
  have ⟨hK1, hK2⟩ := kbD_toNat hp
  have ⟨r1, r2⟩ := rsaD_toNat hp
  have hk1 := hp.lv.1; have hk2 := hp.lv.2
  have hsl := hp.hsl; have wS := hp.wS
  have e5 : decStack = 3560 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 296 := rfl
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
  have kbsub : kbD s = off (kbD s) privStack - BitVec.ofNat 64 privStack := by
    rw [off, BitVec.add_sub_cancel]
  rw [← kbsub]
  have em := emD_sub hp
  have rs := rsaD_sub hp
  have dEmR : Region.Disjoint ⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ (rsaD s) := by
    simp only [rsaD]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega)) (by unfold oEm; omega) (by unfold oRsa; omega)
  have dSK : (scrD s).Disjoint (stkD s) := hp.dKs.symm
  -- Regions apart from the working space are apart from `EM` and the call's working space.
  have dE : ∀ {r : Region}, (r).Disjoint (scrD s) →
      (⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ : Region).Disjoint r ∧ r.Disjoint (rsaD s) :=
    fun h => ⟨(h.sub_right em).symm, h.sub_right rs⟩
  have dcts : (⟨stackArg s 13, (s.gpr .r8).toNat⟩ : Region).Disjoint (scrD s) := by
    have := hp.dcts; rwa [hp.hcl] at this
  have dKct : (stkD s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dKct; rwa [hp.hcl] at this
  refine ⟨by omega, by omega, rfl, rfl, (dE hp.dns).1, (dE hp.des).1, (dE dcts).1, (dE hp.dps).1,
    (dE hp.dqs).1, (dE hp.ddps).1, (dE hp.ddqs).1, (dE hp.dqis).1, dEmR,
    ((dSK.sub_right sA).sub_left em), (dE hp.dns).2, (dE hp.des).2, (dE dcts).2, (dE hp.dps).2,
    (dE hp.dqs).2, (dE hp.ddps).2, (dE hp.ddqs).2, (dE hp.dqis).2, ((dSK.sub_right sA).sub_left rs),
    ((dSK.symm.sub_left sR).sub_right em), hp.dKn.sub_left sR, hp.dKe.sub_left sR, dKct.sub_left sR,
    hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR, hp.dKqi.sub_left sR,
    ((dSK.symm.sub_left sR).sub_right rs), dRA, ((dSK.symm.sub_left sK).sub_right em), hp.dKn.sub_left sK,
    hp.dKe.sub_left sK, dKct.sub_left sK, hp.dKp.sub_left sK, hp.dKq.sub_left sK, hp.dKdp.sub_left sK,
    hp.dKdq.sub_left sK, hp.dKqi.sub_left sK, ((dSK.symm.sub_left sK).sub_right rs), dKA,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega, hp.wN, hp.wE,
    by have := hp.wC; rw [hp.hcl] at this; exact this, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi,
    by rw [r1, r2]; unfold oRsa; omega, hp.lv, trivial, trivial, hp.el1, hp.el2, hp.pl1, hp.pl2, hp.ql1, hp.ql2,
    hp.hdpl, hp.hqil, hp.hdql, by rw [r1]; unfold Spec.Rsa.scratchWords; omega⟩

theorem privD_covers {s t : State} (hp : DPre s) (h : DSet s t) :
    Covers (privRdD s ++ privWrD s) (t.rd ++ t.wr) ∧ Covers (privWrD s) t.wr := by
  have hk2 := hp.lv.2; have hsl := hp.hsl; have hcl := hp.hcl
  have ⟨r1, r2⟩ := rsaD_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hwr := h.he.wr
  have cw : Covers (privWrD s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWrD, rsaD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨scrD s, by simp, oEm, rfl, by simp only [scrD]; unfold oEm; omega⟩
    · exact ⟨scrD s, by simp, oRsa, rfl, by simp only [scrD]; rw [r1]; unfold oRsa; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.he.rd]; exact hx)
  simp only [privRdD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r9, (stackArg s 0).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 13, (stackArg s 14).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 1, (stackArg s 2).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..), 0, z _,
      by show 0 + 112 ≤ frameBytes; decide⟩

/-! ## The call -/

/-- The private-key operation's outcome for the ciphertext, from the entry
state. -/
def privOutD (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 13) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)

/-- A word of the frame, apart from what the call writes. -/
theorem frame_apartD {s : State} (hp : DPre s) {k : Nat} (hk : k < nW) :
    ∀ r ∈ privWrD s ++ [below (fb s) (8 + privStack)], (⟨off (fb s) (8 * k), 8⟩ : Region).Disjoint r := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have sF : Region.Sub ⟨off (fb s) (8 * k), 8⟩ (stkD s) :=
    fun x h => frame_subD s x (Offset.sub_base _ (by unfold nW frameBytes at *; omega) x h)
  intro r hr
  simp only [privWrD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.dKs.sub_left sF).sub_right (emD_sub hp)
  · exact (hp.dKs.sub_left sF).sub_right (rsaD_sub hp)
  · exact Offset.disjoint_below _ (by unfold nW frameBytes privStack at *; omega)

theorem privD_call (v : PrivImpl) {s t : State} (hp : DPre s) (h : DSet s t) :
    WP isa (.call v.name v.code) t fun t' => EnvD s t' ∧ Lay t' (fb s) (stackArg s 15) ∧
      Rep t'.mem (fb s) (stackArg s 15) (fun o => t'.mem (off (stackArg s 15) o)) (privW s) ∧
      Spec.Rsa.writtenOutcome t'.mem (off (stackArg s 15) oEm) (s.gpr .r8).toNat ((t'.gpr .rax).setWidth 32)
        (privOutD s) := by
  obtain ⟨hc, hw⟩ := privD_covers hp h
  have hdp := v.depth
  have e2 : privStack = 3256 := rfl
  have hF := fb_toNatD hp
  refine WP.call_sp_mx (k := privK) v.ok (SpSafe.of_all v.spSafe) (by omega) (privD_pre hp h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [h.he.rsp] at hf
  have hf' : Frame (privWrD s ++ [below (fb s) (8 + privStack)]) t.mem s'.mem :=
    Frame.below_mono hf (by omega) (by have := hp.sp2; unfold frameBytes at *; omega)
  have hfe : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hfE : FrD s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdD s) (privWrD s)) i = privW s i :=
    fun hi => privD_args hp h _ _ hi
  have bo : ∀ {p : Addr} {len : Nat}, (stkD s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrD s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hm hs hl => FrD.bytes hfE hk ho hm hs.symm hl
  simp only [privK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rdx, h.rcx, h.r8, h.r9, hm₂,
    hg₂ .rax (by decide), e (show 0 < 14 by decide), e (show 2 < 14 by decide), e (show 3 < 14 by decide),
    e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide), e (show 8 < 14 by decide),
    e (show 10 < 14 by decide)] at hpost
  simp only [privW, upd, Nat.reduceEqDiff, ↓reduceIte] at hpost
  have hcl := hp.hcl
  have dcts : (⟨stackArg s 13, (s.gpr .r8).toNat⟩ : Region).Disjoint (scrD s) := by
    have := hp.dcts; rwa [hcl] at this
  have dKct : (stkD s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dKct; rwa [hcl] at this
  have dOct : (outR s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dOct; rwa [hcl] at this
  have dMct : (mlR s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dMct; rwa [hcl] at this
  rw [bo hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega),
    bo hp.dKe hp.dOe hp.dMe hp.des (by have := hp.wE; omega),
    bo dKct dOct dMct dcts (by have := hp.wC; omega),
    bo hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega),
    bo hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega),
    show (stackArg s 2).toNat = (stackArg s 6).toNat from hp.hdpl.symm,
    bo hp.dKdp hp.dOdp hp.dMdp hp.ddps (by have := hp.wDp; omega),
    show (stackArg s 4).toNat = (stackArg s 8).toNat from hp.hdql.symm,
    bo hp.dKdq hp.dOdq hp.dMdq hp.ddqs (by have := hp.wDq; omega),
    show (stackArg s 6).toNat = (stackArg s 10).toNat by rw [hp.hdpl, hp.hqil],
    bo hp.dKqi hp.dOqi hp.dMqi hp.dqis (by have := hp.wQi; omega)] at hpost
  have hkeep : ∀ {k : Nat}, k < nW → word s'.mem (fb s) (8 * k) = word t.mem (fb s) (8 * k) := fun hk =>
    hf'.readW (Region.contains_self _ _) (frame_apartD hp hk) (by decide)
  have hsp' : s'.gpr .rsp = fb s := (hcs .rsp (by decide)).trans h.he.rsp
  refine ⟨⟨hsp', hrd.trans h.he.rd, hwr.trans h.he.wr, fun r hr hne => (hcs r hr).trans (h.he.cs r hr hne),
    hmx.trans h.he.mx, h.he.fr.trans (hf'.sub fun r hr => ?_)⟩,
    h.L.congr ((hcs .rsp (by decide))) hwr (by rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl]; exact hkeep (by decide)),
    ⟨fun _ _ => rfl, fun k hk => (hkeep hk).trans (h.R.fr k hk)⟩, ?_⟩
  · simp only [privWrD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrD s, by simp, emD_sub hp⟩
    · exact ⟨scrD s, by simp, rsaD_sub hp⟩
    · exact ⟨stkD s, by simp, below_subD s (le_refl _)⟩
  · simp only [privOutD]
    rw [show (stackArg s 10).toNat = (stackArg s 2).toNat from hp.hqil,
      show (stackArg s 8).toNat = (stackArg s 4).toNat from hp.hdql] at hpost
    exact hpost

end VG.Proof.RsaOaep.X86_64
