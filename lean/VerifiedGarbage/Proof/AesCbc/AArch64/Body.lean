import VerifiedGarbage.Proof.AesCbc.AArch64.Loop

/-!
# AES-CBC on AArch64: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`).
-/

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

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
theorem LInv.regs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.callPre {k : Nat} (hk : k < N s₀) {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = blk s₀ k)
    (x3 : s.gpr .x3 = 1) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
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

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) :
    (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨S s₀ + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

end

section
variable {s₀ : State}

theorem cIv0 : (ivR s₀).Contains (Iv s₀) 8 := by
  simpa using Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)

theorem cIv8 : (ivR s₀).Contains (Iv s₀ + BitVec.ofNat 64 8) 8 :=
  Offset.contains_base _ (by decide) (by decide)

theorem cSv0 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048) 8 :=
  Offset.contains_base _ (by decide) (by decide)

theorem cSv8 : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 8) 8 := by
  rw [Offset.add_add]; exact Offset.contains_base _ (by decide) (by decide)

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

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .x9 ∧ r ≠ .x10 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The invariant's registers after a block, from those before it. -/
theorem LInv.next {enc : Bool} {s₀ : State} {k : Nat} {s s' : State} (h : LInv enc s₀ k s)
    (g : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) :
    s'.gpr .x19 = W s₀ ∧ s'.gpr .x20 = s₀.gpr .x1 ∧ s'.gpr .x21 = Iv s₀ ∧ s'.gpr .x24 = S s₀ ∧
      ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
        r ≠ .x30 → s'.gpr r = s₀.gpr r :=
  ⟨by rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19],
   by rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20],
   by rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21],
   by rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24],
   fun r hr h19 h20 h21 h22 h23 h24 h30 => by rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]⟩

/-! ## Encryption -/

/-- What the code before the call leaves. -/
structure EncA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = xorMem s.mem (blk s₀ k) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv true s₀ k s) :
    WP isa (.block (xorInto ++ callArgs)) s (EncA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    xorInto_ok s (P := blk s₀ k) (Q := Iv s₀) h.x22 h.x21
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 hk))
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1 (preserved_ne hr).2]
  refine ⟨hp.callPre hk (by rw [x0₂, g₁ _ (by decide) (by decide), h.x19])
    (by rw [x1₂, g₁ _ (by decide) (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide) (by decide), h.x22]) x3₂
    (by rw [x4₂, g₁ _ (by decide) (by decide), h.x24]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem encBody_ok (v : BlocksImpl) : BodyOk true (encBody v.enc) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    copy_ok s₂ (dst := .x21) (src := .x22) (d := 0) (e := 0) (P := Iv s₀) (Q := blk s₀ k)
      (by rw [g₂ .x21 (by simp [preserved]) (by decide), h.x21]; simp)
      (by rw [g₂ .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [g₂ .x22 (by simp [preserved]) (by decide), h.x22]; simp)
      (by rw [g₂ .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hW₂]; exact in_rw (by simp) cIv0) (by rw [hW₂]; exact in_rw (by simp) cIv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₄, run₄, x22₄, x23₄, keep₄, sp₄, mem₄, rd₄, wr₄⟩ := advance_regs (s := s₃) hk
    (by rw [g₃ _ (by decide), g₂ .x22 (by simp [preserved]) (by decide), h.x22])
    (by rw [g₃ _ (by decide), g₂ .x23 (by simp [preserved]) (by decide), h.x23])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₄.gpr r = s.gpr r := by
    rw [keep₄ r h22 h23, g₃ r (preserved_ne hr).1, g₂ r hr h30]
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
  have one (r : Region) (P : Addr) (hd : (⟨P, 16⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  -- The new block, and the chaining value.
  have hblk := h.block hk
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK true s₀ k))) := by
    rw [mem₄, mem₃, Proof.Cmac.bytesAt_frame (copyMem_frame s₂.mem (Iv s₀) (blk s₀ k))
        (one _ _ (hp.blk_iv hk)) (by decide),
      c.out, ← UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, xorMem_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  have newIv : bytesAt s₄.mem (Iv s₀) 16 = bytesAt s₄.mem (blk s₀ k) 16 := by
    rw [mem₄, mem₃, copyMem_bytes _ ((hp.blk_iv hk).symm),
      Proof.Cmac.bytesAt_frame (copyMem_frame s₂.mem (Iv s₀) (blk s₀ k)) (one _ _ (hp.blk_iv hk)) (by decide)]
  have hl : (outK true s₀ k).length = k := by
    simp [cbc, length_encrypt, Spec.Cbc.blocksAt]; omega
  have outSucc : outK true s₀ (k + 1) = outK true s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbc, ciph, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₄, x23₄, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₄, sp₃, c.sp, a.sp, h.sp]
  · rw [rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [cts, ite_true, outSucc, next_snoc]

/-! ## Decryption -/

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := S s₀ + BitVec.ofNat 64 2048

/-- What the code before the call leaves. -/
structure DecA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copyMem s.mem (Sv s₀) (blk s₀ k)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv false s₀ k s) :
    WP isa (.block (copy .x24 cOff .x22 0 ++ callArgs)) s (DecA s₀ k s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .x24) (src := .x22) (d := cOff) (e := 0) (P := Sv s₀) (Q := blk s₀ k)
      (by rw [h.x24]; rfl) (by rw [h.x24]; exact sv8 _)
      (by rw [h.x22]; simp) (by rw [h.x22])
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := callArgs_ok s₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1]
  refine ⟨hp.callPre hk (by rw [x0₂, g₁ _ (by decide), h.x19])
    (by rw [x1₂, g₁ _ (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide), h.x22]) x3₂
    (by rw [x4₂, g₁ _ (by decide), h.x24]) (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]),
    keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem decBody_ok (v : BlocksImpl) : BodyOk false (decBody v.dec) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.decOk v.decNoFrames a.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₂.gpr r = s.gpr r := by
    rw [c.saved r hr h30, a.saved r hr]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr, h.regs hp]
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    xorInto_ok s₂ (P := blk s₀ k) (Q := Iv s₀) (by rw [g₂ .x22 (by simp [preserved]) (by decide), h.x22])
      (by rw [g₂ .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hR₂]; exact in_rw (by simp) (hp.cBlk8 hk))
      (by rw [hR₂]; exact in_rw (by simp) cIv0) (by rw [hR₂]; exact in_rw (by simp) cIv8)
      (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk0 hk)) (by rw [hW₂]; exact in_rw (by simp) (hp.cBlk8 hk))
  have g₃' (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (preserved_ne hr).1 (preserved_ne hr).2, g₂ r hr h30]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd₃, wr₃, hR₂]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, hW₂]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    copy_ok s₃ (dst := .x21) (src := .x24) (d := 0) (e := cOff) (P := Iv s₀) (Q := Sv s₀)
      (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21]; simp)
      (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21])
      (by rw [g₃' .x24 (by simp [preserved]) (by decide), h.x24]; rfl)
      (by rw [g₃' .x24 (by simp [preserved]) (by decide), h.x24]; exact sv8 _)
      (by rw [hR₃]; exact in_rw (by simp) cSv0) (by rw [hR₃]; exact in_rw (by simp) cSv8)
      (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₅, run₅, x22₅, x23₅, keep₅, sp₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide), g₃' .x22 (by simp [preserved]) (by decide), h.x22])
    (by rw [g₄ _ (by decide), g₃' .x23 (by simp [preserved]) (by decide), h.x23])
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₅.gpr r = s.gpr r := by
    rw [keep₅ r h22 h23, g₄ r (preserved_ne hr).1, g₃' r hr h30]
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
  have ivIn : bytesAt s₂.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame c.frame callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (one _ _ hp.iv_sv) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _) (one _ _ (hp.blk_sv hk)) (by decide), hblk]
  have newBlk : bytesAt s₅.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [mem₅, mem₄,
      Proof.Cmac.bytesAt_frame (copyMem_frame s₃.mem (Iv s₀) (Sv s₀)) (one _ _ (hp.blk_iv hk)) (by decide),
      mem₃, xorMem_bytes _ (hp.blk_iv hk), ivIn, c.out, ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₅.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₅, mem₄, copyMem_bytes _ hp.iv_sv, mem₃,
      Proof.Cmac.bytesAt_frame (xorMem_frame _ _ _) (one _ _ (hp.blk_sv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame c.frame callSv (by decide), a.mem, copyMem_bytes _ (hp.blk_sv hk).symm, hblk]
  have hl : (outK false s₀ k).length = k := by
    simp [cbc, length_decrypt, Spec.Cbc.blocksAt]; omega
  have outSucc : outK false s₀ (k + 1) = outK false s₀ k ++ [bytesAt s₅.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbc, ciph, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  obtain ⟨x19', x20', x21', x24', other'⟩ := h.next g
  refine ⟨x19', x20', x21', x22₅, x23₅, x24', other', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp₅, sp₄, sp₃, c.sp, a.sp, h.sp]
  · rw [rd₅, rd₄, rd₃, c.rd, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, c.wr, a.wr, h.wr]
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.AArch64
