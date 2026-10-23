module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit

/-!
# AES-CBC on PPC64LE: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), as on x86-64
(`Proof/AesCbc/X86_64/Body.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE
open VG.Spec.Aes (bytesAt)

theorem encryptBlocks_noFrames : Impl.Aes.PPC64LE.encryptBlocks.noFrames = true := by decide +kernel

theorem decryptBlocks_noFrames : Impl.Aes.PPC64LE.decryptBlocks.noFrames = true := by decide +kernel

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

theorem LInv.wrs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.callPre {k : Nat} (hk : k < N s₀) {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = blk s₀ k)
    (r6 : s.gpr .r6 = BitVec.ofNat 64 1) (r7 : s.gpr .r7 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub hk)
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
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
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] m m') :
    Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩

end

theorem sv8 (b : Addr) : b + BitVec.ofNat 64 (2048 + 8) = b + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8 := by
  rw [Offset.add_add]

theorem zero8 (b : Addr) : b + BitVec.ofNat 64 (0 + 8) = b + BitVec.ofNat 64 8 := rfl

/-- What the code before a call leaves: the call's arguments, the
nonvolatile registers, and the memory `m`. -/
structure Pre (s₀ : State) (D : Addr) (m : Mem) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r9 ∧ r ≠ .r10 := by
  revert hr; cases r <;> decide

/-- `callArgs` after code that keeps the nonvolatile registers. -/
theorem callArgs_pre {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    {m : Mem} (h : LInv M s₀ k s) (g : ∀ r ∈ preserved, s₁.gpr r = s.gpr r) (hm : s₁.mem = m)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) : WP isa (.block callArgs) s₁ (Pre s₀ (blk s₀ k) m s) :=
  callArgs_wp fun s₂ r3 r4 r5 r6 r7 o mem rd wr => by
    have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
      obtain ⟨h3, h4, h5, h6, h7, -⟩ := preserved_ne hr
      rw [o r (by simp [argRegs5, h3, h4, h5, h6, h7]), g r hr]
    exact ⟨hp.callPre hk (by rw [r3, g _ (by decide), h.r14]) (by rw [r4, g _ (by decide), h.r15])
      (by rw [r5, g _ (by decide), h.r17]) r6 (by rw [r7, g _ (by decide), h.r19])
      (by rw [rd, hrd, h.rd]) (by rw [wr, hwr, h.wr]), keep, by rw [mem, hm], by rw [rd, hrd],
      by rw [wr, hwr]⟩

/-! ## Encryption -/

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode true) s₀ k s) :
    WP isa (.block (xorInto .r17 .r16 ++ callArgs)) s
      (Pre s₀ (blk s₀ k) (xorMem s.mem (blk s₀ k) (Iv s₀)) s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h.r17 h.r16
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
    fun s₁ g₁ mem₁ rd₁ wr₁ => callArgs_pre hp hk h (fun r hr => by
      obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
      exact g₁ r h9 h10) mem₁ rd₁ wr₁

theorem encBody_ok : BodyOk (cbcMode true) encBody := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  refine copy_wp (dst := .r16) (src := .r17) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₂ .r16 (by decide), h.r16, ofNat_zero_add])
    (by rw [g₂ .r16 (by decide), h.r16])
    (by rw [g₂ .r17 (by decide), h.r17, ofNat_zero_add])
    (by rw [g₂ .r17 (by decide), h.r17])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hW₂]; exact in_rw (by simp) cIv0) (by rw [hW₂]; exact in_rw (by simp) cIv8)
    fun s₃ g₃ mem₃ rd₃ wr₃ => advance_regs (s := s₃) hk
      (by rw [g₃ _ (by decide), g₂ .r17 (by decide), h.r17])
      (by rw [g₃ _ (by decide), g₂ .r18 (by decide), h.r18])
      fun s₄ r17₄ r18₄ keep₄ mem₄ rd₄ wr₄ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₄.gpr r = s.gpr r := by
    rw [keep₄ r h17 h18, g₃ r (preserved_ne hr).2.2.2.2.2.1, g₂ r hr]
  -- Memory.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact xorMem_frame _ _ _
  have f₃ : Frame [ivR s₀] s₂.mem s₃.mem := by rw [mem₃]; exact copyMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₄.mem := by
    rw [mem₄]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
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
  refine ⟨?_, ?_, ?_, r17₄, r18₄, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
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

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block (copy .r19 cOff .r17 0 ++ callArgs)) s
      (Pre s₀ (blk s₀ k) (copyMem s.mem (Sv s₀) (blk s₀ k)) s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  refine copy_wp (dst := .r19) (src := .r17) (d := cOff) (e := 0) (P := Sv s₀) (Q := blk s₀ k)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h.r19]; rfl) (by rw [h.r19]; exact sv8 _)
    (by rw [h.r17, ofNat_zero_add]) (by rw [h.r17])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
    fun s₁ g₁ mem₁ rd₁ wr₁ => callArgs_pre hp hk h (fun r hr => g₁ r (preserved_ne hr).2.2.2.2.2.1)
      mem₁ rd₁ wr₁

theorem decBody_ok : BodyOk (cbcMode false) decBody := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.PPC64LE.decryptBlocks_correct decryptBlocks_noFrames a.pre)
    fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  rw [List.append_assoc]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [g₂ .r17 (by decide), h.r17]) (by rw [g₂ .r16 (by decide), h.r16])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
    fun s₃ g₃ mem₃ rd₃ wr₃ => ?_
  have g₃' (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₃ r h9 h10, g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  refine copy_wp (dst := .r16) (src := .r19) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃' .r16 (by decide), h.r16, ofNat_zero_add])
    (by rw [g₃' .r16 (by decide), h.r16])
    (by rw [g₃' .r19 (by decide), h.r19]; rfl)
    (by rw [g₃' .r19 (by decide), h.r19]; exact sv8 _)
    (by rw [hR₃]; exact in_rw (by simp) cSv0) (by rw [hR₃]; exact in_rw (by simp) cSv8)
    (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => advance_regs (s := s₄) hk
      (by rw [g₄ _ (by decide), g₃' .r17 (by decide), h.r17])
      (by rw [g₄ _ (by decide), g₃' .r18 (by decide), h.r18])
      fun s₅ r17₅ r18₅ keep₅ mem₅ rd₅ wr₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h17 h18, g₄ r (preserved_ne hr).2.2.2.2.2.1, g₃' r hr]
  -- Memory.
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [mem₃]; exact xorMem_frame _ _ _
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [mem₄]; exact copyMem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅]
    refine (f₁.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans
      ((f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans ((stepFrame hk (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩)).sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
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
  refine ⟨?_, ?_, ?_, r17₅, r18₅, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.PPC64LE
