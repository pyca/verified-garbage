import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecFrame

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the private-key operation

Its precondition with its stack arguments in the frame (`priv_pre`), and
what it leaves (`priv_call`): `out` holds its outcome for the ciphertext,
and the frame its slots.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

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
  have e5 : decStack = 3480 := rfl
  have e6 : privStack = 3256 := rfl
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


theorem priv_covers {s t : State} (hp : DPre s) (h : Setup s t) :
    Covers (privRd s ++ privWr s) (t.rd ++ t.wr) ∧ Covers (privWr s) t.wr := by
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e3 : frameBytes = 216 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (privWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.rd]; exact hx)
  simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r9, (stackArg s 0).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 11, (stackArg s 12).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 13, (stackArg s 14).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega⟩

/-- Memory changed by a call from the frame, within regions the function
may write. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame (wrs s) m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, ∃ R ∈ wrs s, Region.Sub r R) : Frame (wrs s) m₁ m₃ :=
  h₁.trans (h₂.sub hs)

/-- A buffer the function does not write, from memory changed only where it
may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame (wrs s) s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hm : (mlR s).Disjoint ⟨p, len⟩)
    (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hm.symm
  · exact hs.symm

/-! ## The inputs -/

abbrev kOf (s : State) : Nat := (s.gpr .r8).toNat
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (kOf s)
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
abbrev dB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev cB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 3) (kOf s)
abbrev pB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat
abbrev qB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 8).toNat
abbrev dpB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat
abbrev dqB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 8).toNat
abbrev qiB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 13) (stackArg s 6).toNat

/-- The private-key operation's outcome for the ciphertext. -/
abbrev privOut (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (nB s) (eB s) (cB s) (pB s) (qB s) (dpB s) (dqB s) (qiB s)

/-- After the call. -/
structure PostPriv (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t.mem
  slots : Slots s t.mem
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32) (privOut s)

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- The slots are apart from what the call writes. -/
theorem slot_apart {s : State} (hp : DPre s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ privWr s ++ [below (fb s) (8 + privStack)], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : decStack = 3480 := rfl
  have e2 : privStack = 3256 := rfl
  have e3 : frameBytes = 216 := rfl
  have hsi := hp.hsi
  intro r hr
  simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := hp.dKo; rw [hsi] at this; exact this.sub_left (frame_sub s hd)
  · exact hp.dKs.sub_left (frame_sub s hd)
  · rw [show below (fb s) (8 + privStack) = ⟨kb s, 8 + privStack⟩ by
      simp only [below, fb_eq, off, BitVec.add_sub_cancel], fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega) (by omega)

theorem priv_call (v : PrivImpl) {s t : State} (hp : DPre s) (h : Setup s t) :
    WP isa (.call v.name v.code) t fun t' => PostPriv s t' ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := priv_covers hp h
  have hdp := v.depth
  have e2 : privStack = 3256 := rfl
  refine WP.call_sp_mx (k := privK) v.ok (SpSafe.of_all v.spSafe) (by omega) (priv_pre hp h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [h.rsp] at hf
  have hf' : Frame (privWr s ++ [below (fb s) (8 + privStack)]) t.mem s'.mem :=
    Frame.below_mono hf (by omega) (by have := (fb_toNat hp).2.2; omega)
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e7 : frameBytes = 216 := rfl
  have hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by omega)⟩
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args h _ _ hi
  have bo : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨p, len⟩ →
      (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrR s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hm hs hl => bytes_of_frame hfE hk ho hm hs.symm hl
  simp only [privK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rdx, h.rcx, h.r8, h.r9, hm₂,
    hg₂ .rax (by decide), e (show 0 < 14 by decide), e (show 2 < 14 by decide), e (show 3 < 14 by decide),
    e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide), e (show 8 < 14 by decide),
    e (show 10 < 14 by decide), Nat.reduceAdd] at hpost
  have hl := hp.hil
  rw [bo hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega),
    bo hp.dKe hp.dOe hp.dMe hp.des (by have := hp.wE; omega),
    show (s.gpr .r8).toNat = (stackArg s 4).toNat from hl.symm,
    bo hp.dKi hp.dOi hp.dMi hp.dis (by have := hp.wI; omega),
    bo hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega),
    bo hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega),
    show (stackArg s 6).toNat = (stackArg s 10).toNat from hp.hdpl.symm,
    bo hp.dKdp hp.dOdp hp.dMdp hp.ddps (by have := hp.wDp; omega),
    show (stackArg s 8).toNat = (stackArg s 12).toNat from hp.hdql.symm,
    bo hp.dKdq hp.dOdq hp.dMdq hp.ddqs (by have := hp.wDq; omega),
    show (stackArg s 10).toNat = (stackArg s 14).toNat by rw [hp.hdpl, hp.hqil],
    bo hp.dKqi hp.dOqi hp.dMqi hp.dqis (by have := hp.wQi; omega)] at hpost
  have hkeep : ∀ {d : Nat}, d + 8 ≤ frameBytes → word s'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf'.readW (Region.contains_self _ _) (slot_apart hp (by omega)) (by decide)
  refine ⟨⟨(hcs .rsp (by decide)).trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    frame_call (frame_of_outside h.out) hf' fun r hr => ?_,
    ⟨(hkeep (by decide)).trans h.slots.sOut, (hkeep (by decide)).trans h.slots.sML,
      (hkeep (by decide)).trans h.slots.sN, (hkeep (by decide)).trans h.slots.sK,
      (hkeep (by decide)).trans h.slots.sE, (hkeep (by decide)).trans h.slots.sEl,
      (hkeep (by decide)).trans h.slots.sD, (hkeep (by decide)).trans h.slots.sDl,
      (hkeep (by decide)).trans h.slots.sIn, (hkeep (by decide)).trans h.slots.sScr⟩, ?_⟩, hcs, hmx⟩
  · simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, by rw [outR, hsi']; exact fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨stkR s, by simp, below_sub s (Nat.le_refl _)⟩
  · simp only [privOut, nB, eB, cB, pB, qB, dpB, dqB, qiB, kOf]
    rw [hl, hp.hqil, hp.hdql] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
