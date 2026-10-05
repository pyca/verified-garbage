import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecFrame

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the private-key operation

Its precondition with its stack arguments in the frame (`priv_pre`), and
what it leaves (`priv_call`): `out` holds its outcome for the ciphertext,
and the frame its slots.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 decStack

theorem fb_sub8 (s : State) : fb s - 8 = off (kb s) privStack := by
  rw [fb_eq, off, off, show 8 + privStack = privStack + 8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : DPre s) : (kb s).toNat + decStack + 144 ≤ 2 ^ 64 ∧
    (kb s).toNat + decStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (off (kb s) privStack) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega)
    (by omega) (by omega)
  rw [show off (kb s) privStack + BitVec.ofNat 64 0 = off (kb s) privStack from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, off_add, show privStack + 8 * (i + 1) = 8 + privStack + 8 * i by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq, off_add, show privStack + 8 * (0 + 1) = 8 + privStack by omega]

/-- What `vg_rsa_private_checked` reads. -/
def privRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
    ⟨stackArg s 13, (stackArg s 14).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out` and the working space. -/
def privWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .r8).toNat⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]

/-- What the callee's entry state's stack arguments are. -/
theorem priv_args {s t : State} (h : Setup s t) (rd wr : List Region) {i : Nat} (hi : i < 14) :
    stackArg (t.callEntry.withRegions rd wr) i = stackArg s (i + 3) :=
  (stackArg_entry h.rsp _ _ (by omega)).trans (h.args i hi)

theorem priv_pre {s t : State} (hp : DPre s) (h : Setup s t) :
    privK.pre (t.callEntry.withRegions (privRd s) (privWr s)) := by
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args h _ _ hi
  simp only [privK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    stackArgAddr_entry h.rsp, e (show 0 < 14 by decide), e (show 1 < 14 by decide), e (show 2 < 14 by decide),
    e (show 3 < 14 by decide), e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide),
    e (show 7 < 14 by decide), e (show 8 < 14 by decide), e (show 9 < 14 by decide),
    e (show 10 < 14 by decide), e (show 11 < 14 by decide), e (show 12 < 14 by decide),
    e (show 13 < 14 by decide), Nat.reduceAdd, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  have e5 : decStack = 3472 := rfl
  have e6 : privStack = 3248 := rfl
  have e7 : frameBytes = 216 := rfl
  have hfb : fb s = off (kb s) (8 + privStack) := fb_eq s
  -- The callee's stack, its return address and its stack arguments, in ours.
  have sK : Region.Sub ⟨kb s, privStack⟩ (stkR s) := Region.sub_prefix (by omega)
  have sR : Region.Sub ⟨off (kb s) privStack, 8⟩ (stkR s) := Offset.sub_base _ (by omega)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by rw [hfb]; exact Offset.sub_base _ (by omega)
  have dRA : (⟨off (kb s) privStack, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dKA : (⟨kb s, privStack⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by omega) (by omega)
  have hoff : (off (kb s) privStack).toNat = (kb s).toNat + privStack := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have kbsub : kb s = off (kb s) privStack - BitVec.ofNat 64 privStack := by
    rw [off, BitVec.add_sub_cancel]
  rw [← kbsub]
  have rw' : ∀ {r : Region}, (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint r →
      (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region).Disjoint r := fun h => by rwa [hsi] at h
  have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
  have dKi : (stkR s).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩ := hp.dKi
  refine ⟨by omega, by omega, rfl, rfl, rw' hp.dOn, rw' hp.dOe, rw' hp.dOi, rw' hp.dOp, rw' hp.dOq, rw' hp.dOdp,
    rw' hp.dOdq, rw' hp.dOqi, rw' hp.dOs, (dKo.sub_left sA).symm, hp.dns, hp.des, hp.dis, hp.dps, hp.dqs, hp.ddps,
    hp.ddqs, hp.dqis, (hp.dKs.sub_left sA).symm, dKo.sub_left sR, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    hp.dKi.sub_left sR, hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR,
    hp.dKqi.sub_left sR, hp.dKs.sub_left sR, dRA, dKo.sub_left sK, hp.dKn.sub_left sK, hp.dKe.sub_left sK,
    hp.dKi.sub_left sK, hp.dKp.sub_left sK, hp.dKq.sub_left sK, hp.dKdp.sub_left sK, hp.dKdq.sub_left sK,
    hp.dKqi.sub_left sK, hp.dKs.sub_left sK, dKA, by have := hp.wO; omega, hp.wN, hp.wE, hp.wI, hp.wP, hp.wQ,
    hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, trivial, hil, hp.L1, hp.L2, hp.pl1, hp.pl2, hp.ql1, hp.ql2,
    hp.hdpl, hp.hqil, hp.hdql, hp.hsl⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
