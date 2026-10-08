import VerifiedGarbage.Proof.AesCbc.X86_64.Loop

/-!
# AES-CBC on x86-64: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`).
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem callArgs_ok (s : State) :
    ∃ s', runBlock isa callArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r13 ∧
      s'.gpr .rcx = 1 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [callArgs, runBlock_cons, runStep_some, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.blk_toNat {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
  have := hp.data_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem UPre.blk_wrap {k : Nat} (hk : k < N s₀) : (blk s₀ k).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.data_wrap
  rw [hp.blk_toNat hk]; omega

/-- The regions the code reads and writes, from the invariant. -/
theorem LInv.regs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

omit hp in
theorem LInv.wrs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hp : UPre s₀) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.callPre {k : Nat} (hk : k < N s₀) {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = blk s₀ k)
    (rcx : s.gpr .rcx = 1) (r8 : s.gpr .r8 = S s₀) (rsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub hk)
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  stkW := by rw [rsp]; exact hp.stk_sch
  stkD := by rw [rsp]; exact hp.stk_data.sub_right (UPre.data_sub hk)
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  wrap := hp.blk_wrap hk
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

theorem UPre.cBlk0 {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (blk s₀ k) 8 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.cBlk8 {k : Nat} (hk : k < N s₀) :
    (dataR s₀).Contains (blk s₀ k + BitVec.ofNat 64 8) 8 := by
  have := hp.data_wrap
  rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)

omit hp in
theorem cIv0 : (ivR s₀).Contains (Iv s₀) 8 := by
  simpa using Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)

omit hp in
theorem cIv8 : (ivR s₀).Contains (Iv s₀ + BitVec.ofNat 64 8) 8 :=
  Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem cSv0 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048) 8 :=
  Offset.contains_base _ (by decide) (by decide)

omit hp in
theorem cSv8 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
  rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) :
    (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

omit hp in
/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

end

theorem calleeSaved_ne_rax {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sv8 (b : Addr) : b + BitVec.ofNat 64 (2048 + 8) = b + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]

/-! ## Encryption -/

/-- What the code before the call leaves. -/
structure EncA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = xorMem s.mem (blk s₀ k) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode true) s₀ k s) :
    WP isa (.block (xorInto .r13 .r12 ++ callArgs)) s (EncA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ k) (Q := Iv s₀) h.r13 h.r12
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)]
  refine ⟨hp.callPre hk (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
    (by rw [rdx₂, g₁ _ (by decide), h.r13]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem encBody_ok (v : BlocksImpl) : BodyOk (cbcMode true) (encBody v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encDepth a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    copy_ok s₂ (dst := .r12) (src := .r13) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
      (by rw [g₂ .r12 (by simp [calleeSaved]), h.r12]; simp)
      (by rw [g₂ .r12 (by simp [calleeSaved]), h.r12])
      (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13]; simp)
      (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hW₂]; exact in_rw (by simp) cIv0) (by rw [hW₂]; exact in_rw (by simp) cIv8)
      (by decide) (by decide)
  obtain ⟨s₄, run₄, r13₄, r14₄, zf₄, keep₄, mem₄, rd₄, wr₄⟩ := advance_regs (s := s₃) hk
    (by rw [g₃ _ (by decide), g₂ .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₃ _ (by decide), g₂ .r14 (by simp [calleeSaved]), h.r14])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h13 h14, g₃ r (calleeSaved_ne_rax hr), g₂ r hr]
  -- Memory.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact xorMem_frame _ _ _
  have f₃ : Frame [ivR s₀] s₂.mem s₃.mem := by rw [mem₃]; exact copyMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  -- The new block, and the chaining value.
  have hblk := h.block hk
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK (cbcMode true) s₀ k))) := by
    rw [mem₄, mem₃, bytesAt_frame (copyMem_frame s₂.mem (Iv s₀) (blk s₀ k)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_iv hk) (by decide),
      c.out, ← UPre.sched_bytes hp big₁,
      ← aesWith_state, a.mem, xorMem_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  have newIv : bytesAt s₄.mem (Iv s₀) 16 = bytesAt s₄.mem (blk s₀ k) 16 := by
    rw [mem₄, mem₃, copyMem_bytes _ ((hp.blk_iv hk).symm),
      bytesAt_frame (copyMem_frame s₂.mem (Iv s₀) (blk s₀ k)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_iv hk) (by decide)]
  have hl : (outK (cbcMode true) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (cbcMode true) s₀ (k + 1) = outK (cbcMode true) s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  refine ⟨⟨?_, ?_, ?_, r13₄, r14₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₄⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, ite_true, outSucc, next_snoc]

/-! ## Decryption -/

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 2048

/-- What the code before the call leaves. -/
structure DecA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = copyMem s.mem (Sv s₀) (blk s₀ k)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block (copy .r15 cOff .r13 0 ++ callArgs)) s (DecA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .r15) (src := .r13) (d := cOff) (e := 0) (P := Sv s₀) (Q := blk s₀ k)
      (by rw [h.r15]; rfl) (by rw [h.r15]; exact sv8 _)
      (by rw [h.r13]; simp) (by rw [h.r13])
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide)
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, cs₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (calleeSaved_ne_rax hr)]
  refine ⟨hp.callPre hk (by rw [rdi₂, g₁ _ (by decide), h.rbx]) (by rw [rsi₂, g₁ _ (by decide), h.rbp])
    (by rw [rdx₂, g₁ _ (by decide), h.r13]) rcx₂ (by rw [r8₂, g₁ _ (by decide), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem decBody_ok (v : BlocksImpl) : BodyOk (cbcMode false) (decBody v.dec) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call v.decOk v.decNosp v.decDepth a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [g₂ .r13 (by simp [calleeSaved]), h.r13])
      (by rw [g₂ .r12 (by simp [calleeSaved]), h.r12])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (calleeSaved_ne_rax hr), g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ :=
    copy_ok s₃ (dst := .r12) (src := .r15) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
      (by rw [g₃' .r12 (by simp [calleeSaved]), h.r12]; simp)
      (by rw [g₃' .r12 (by simp [calleeSaved]), h.r12])
      (by rw [g₃' .r15 (by simp [calleeSaved]), h.r15]; rfl)
      (by rw [g₃' .r15 (by simp [calleeSaved]), h.r15]; exact sv8 _)
      (by rw [hR₃]; exact in_rw (by simp) cSv0) (by rw [hR₃]; exact in_rw (by simp) cSv8)
      (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
      (by decide) (by decide)
  obtain ⟨s₅, run₅, r13₅, r14₅, zf₅, keep₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide), g₃' .r13 (by simp [calleeSaved]), h.r13])
    (by rw [g₄ _ (by decide), g₃' .r14 (by simp [calleeSaved]), h.r14])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h13 h14, g₄ r (calleeSaved_ne_rax hr), g₃' r hr]
  -- Memory.
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact copyMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, by rw [rsp₁]; exact fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · rw [rsp₁]; exact hp.stk_iv.symm
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8],
      (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
    · rw [rsp₁]; exact (hp.stk_scr.sub_right (UPre.scr_sub (by decide))).symm
  have hblk := h.block hk
  -- The chaining value on entry to the block, and the block before the call.
  have ivIn : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [bytesAt_frame c.frame callIv (by decide), a.mem,
      bytesAt_frame (copyMem_frame _ _ _) (one _ _ hp.iv_sv) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, bytesAt_frame (copyMem_frame _ _ _) (one _ _ (hp.blk_sv hk)) (by decide), hblk]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [mem₅, mem₄, bytesAt_frame (copyMem_frame s₃.mem (Iv s₀) (Sv s₀)) (one _ _ (hp.blk_iv hk)) (by decide),
      mem₃, xorMem_bytes _ (hp.blk_iv hk), ivIn, c.out, ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₅, mem₄, copyMem_bytes _ hp.iv_sv, mem₃,
      bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_sv hk).symm) (by decide),
      bytesAt_frame c.frame callSv (by decide), a.mem, copyMem_bytes _ (hp.blk_sv hk).symm, hblk]
  have hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (cbcMode false) s₀ (k + 1) = outK (cbcMode false) s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  refine ⟨⟨?_, ?_, ?_, r13₅, r14₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, zf₅⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.X86_64
