module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CBC on RISC-V: one block

`decBody_ok`: one run of `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), as on PPC64LE
(`Proof/AesCbc/PPC64LE/Body.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

theorem encryptBlocks_noFrames : Impl.Aes.RISCV64.encryptBlocks.noFrames = true := by lit_decide

theorem decryptBlocks_noFrames : Impl.Aes.RISCV64.decryptBlocks.noFrames = true := by lit_decide

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
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = blk s₀ k)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 1) (a4 : s.gpr .a4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := hp.rounds
  wd := hp.sch_data.sub_right (UPre.data_sub hk)
  ws := hp.sch_scr.sub_right wsR_sub
  ds := (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right wsR_sub
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

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_cR {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (cR s₀) :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right cR_sub

theorem UPre.iv_cR : (ivR s₀).Disjoint (cR s₀) := hp.iv_scr.sub_right cR_sub

/-- Block `k` is in a writable region. -/
theorem LInv.wBlk {M : Mode} {k : Nat} (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.wr, Region.Sub ⟨blk s₀ k, 16⟩ r := ⟨dataR s₀, by rw [h.wrs hp]; simp, UPre.data_sub hk⟩

theorem LInv.rBlk {M : Mode} {k : Nat} (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨blk s₀ k, 16⟩ r :=
  ⟨dataR s₀, by rw [h.regs hp]; simp, UPre.data_sub hk⟩

theorem LInv.wIv {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.wr, Region.Sub (ivR s₀) r := ⟨ivR s₀, by rw [h.wrs hp]; simp, fun _ h => h⟩

theorem LInv.rIv {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub (ivR s₀) r := ⟨ivR s₀, by rw [h.regs hp]; simp, fun _ h => h⟩

theorem LInv.wC {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.wr, Region.Sub (cR s₀) r := ⟨scrR s₀, by rw [h.wrs hp]; simp, cR_sub⟩

theorem LInv.rC {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub (cR s₀) r := ⟨scrR s₀, by rw [h.regs hp]; simp, cR_sub⟩

omit hp in
/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] m m') : Frame (Mut s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨wsR s₀, by simp, fun _ h => h⟩
    · exact ⟨cR s₀, by simp, fun _ h => h⟩

end

/-- A step's frame, from the frames of its pieces. -/
theorem frame_mono {rs rs' : List Region} {m m' : Mem} (hf : Frame rs m m') (h : ∀ r ∈ rs, r ∈ rs') :
    Frame rs' m m' := hf.mono h

/-- What the code before a call leaves: the call's arguments, the callee-saved
registers, and the memory `m`. -/
structure Pre (s₀ : State) (D : Addr) (m : Mem) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) :
    r ∉ argRegs5 ∧ r ≠ .t0 ∧ r ≠ .t3 ∧ r ≠ .t4 := by
  revert hr; cases r <;> decide

/-- `callArgs` after code that keeps the callee-saved registers. -/
theorem callArgs_pre {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    {m : Mem} (h : LInv M s₀ k s) (g : ∀ r ∈ preserved, s₁.gpr r = s.gpr r) (hm : s₁.mem = m)
    (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hsp : s₁.sp = s.sp) :
    WP isa (.block callArgs) s₁ (Pre s₀ (blk s₀ k) m s) :=
  callArgs_wp fun s₂ a0 a1 a2 a3 a4 o mem rd wr sp => by
    have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
      rw [o r (preserved_ne hr).1, g r hr]
    exact ⟨hp.callPre hk (by rw [a0, g _ (by decide), h.s1]) (by rw [a1, g _ (by decide), h.s2])
      (by rw [a2, g _ (by decide), h.s4]) a3 (by rw [a4, g _ (by decide), h.s6])
      (by rw [rd, hrd, h.rd]) (by rw [wr, hwr, h.wr]), keep, by rw [mem, hm], by rw [rd, hrd],
      by rw [wr, hwr], by rw [sp, hsp]⟩

/-- A one-region frame's disjointness, from one fact. -/
theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-- The frame of a call, in the step's regions. -/
theorem callFrame {s₀ : State} {k : Nat} {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩] m m') : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] m m' :=
  hf.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-! ## Decryption -/

theorem decBody_ok : BodyOk (cbcMode false) decBody := by
  intro s₀ hp k hk s h
  have hS6 : s.gpr .s6 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)) =
      sv s₀ := by rw [h.s6]
  unfold decBody
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₀' e => ?_
  subst e
  rw [hS6]
  have w₀ (r : Reg) (hr : r ≠ .t0) : (s.write .t0 (sv s₀)).gpr r = s.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine copy_wp (P := sv s₀) (Q := blk s₀ k) (by decide) (by decide) (RegUpd.gpr_write_self _ _ _)
    (by rw [w₀ _ (by decide), h.s4]) (h.rBlk hp hk) (h.wC hp) (hp.blk_cR hk).symm
    fun s₁ g₁ cp₁ f₁ rd₁ wr₁ sp₁ => WP.mono (callArgs_pre hp hk h (fun r hr => by
      rw [g₁ r (preserved_ne hr).2.2.1, w₀ r (preserved_ne hr).2.1]) rfl rd₁ wr₁ sp₁) fun s₂ a => ?_
  refine WP.seq (WP.mono
    (blk_call Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames a.pre) fun s₃ c => ?_)
  rw [RegUpd.mem_write] at f₁ cp₁
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wrs hp]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [c.rd, c.wr, a.rd, a.wr]; exact h.regs hp
  rw [List.append_assoc, List.append_assoc]
  refine xorInto_wp (P := blk s₀ k) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₃ .s4 (by decide), h.s4]) (by rw [g₃ .s3 (by decide), h.s3])
    ⟨ivR s₀, by rw [hR₃]; simp, fun _ h => h⟩ ⟨dataR s₀, by rw [hW₃]; simp, UPre.data_sub hk⟩
    (hp.blk_iv hk) fun s₄ g₄ x₄ f₄ rd₄ wr₄ sp₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₅ e => ?_
  subst e
  have hS6' : s₄.gpr .s6 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (s₄.gpr .s6 + BitVec.ofNat 64 2048)) =
      sv s₀ := by rw [g₄ _ (by decide) (by decide), g₃ .s6 (by decide), h.s6]
  rw [hS6']
  have w₄ (r : Reg) (hr : r ≠ .t0) : (s₄.write .t0 (sv s₀)).gpr r = s₄.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  have g₄' (r : Reg) (hr : r ∈ preserved) : (s₄.write .t0 (sv s₀)).gpr r = s.gpr r := by
    rw [w₄ r (preserved_ne hr).2.1, g₄ r (preserved_ne hr).2.2.1 (preserved_ne hr).2.2.2, g₃ r hr]
  refine copy_wp (P := Iv s₀) (Q := sv s₀) (by decide) (by decide)
    (by rw [g₄' .s3 (by decide), h.s3]) (RegUpd.gpr_write_self _ _ _)
    ⟨scrR s₀, by show scrR s₀ ∈ s₄.rd ++ s₄.wr; rw [rd₄, wr₄, hR₃]; simp, cR_sub⟩
    ⟨ivR s₀, by show ivR s₀ ∈ s₄.wr; rw [wr₄, hW₃]; simp, fun _ h => h⟩
    hp.iv_cR fun s₆ g₆ cp₆ f₆ rd₆ wr₆ sp₆ => advance_regs (s := s₆) hk
      (by rw [g₆ _ (by decide), g₄' .s4 (by decide), h.s4])
      (by rw [g₆ _ (by decide), g₄' .s5 (by decide), h.s5])
      fun s₇ s4₇ s5₇ keep₇ mem₇ rd₇ wr₇ sp₇ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₇.gpr r = s.gpr r := by
    rw [keep₇ r h4 h5, g₆ r (preserved_ne hr).2.2.1, g₄' r hr]
  -- Memory.
  have m₅ : (s₄.write .t0 (sv s₀)).mem = s₄.mem := rfl
  have fc : Frame [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩] s₁.mem s₃.mem := by
    have := c.frame; rwa [a.mem] at this
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₇.mem := by
    rw [mem₇]
    refine (f₁.mono (by simp)).trans ((callFrame fc).trans ((f₄.mono (by simp)).trans ?_))
    rw [← m₅]; exact f₆.mono (by simp)
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := by
    rw [a.mem]
    exact (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, cR_sub⟩)
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right wsR_sub
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨S s₀, 2048⟩], (cR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.blk_cR hk).symm
    · exact hp.cR_wsR
  have hblk := h.block hk
  -- The chaining value on entry to the block, and the block before the call.
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [bytesAt_frame fc callIv (by decide), bytesAt_frame f₁ (one hp.iv_cR) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₂.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, bytesAt_frame f₁ (one (hp.blk_cR hk)) (by decide), hblk]
  have newBlk : bytesAt s₇.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [mem₇, bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide), m₅, x₄, ivIn, c.out,
      ← UPre.sched_bytes hp big₂, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₇.mem (Iv s₀) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₇, cp₆, m₅, bytesAt_frame f₄ (one (hp.blk_cR hk).symm) (by decide),
      bytesAt_frame fc callSv (by decide), cp₁, hblk]
  have hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (cbcMode false) s₀ (k + 1) = outK (cbcMode false) s₀ k ++ [bytesAt s₇.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk,
      decrypt_snoc]
  refine ⟨?_, ?_, ?_, s4₇, s5₇, ?_, fun r hr hv => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e])), h.keep r hr hv]
  · rw [rd₇, rd₆]; show s₄.rd = _; rw [rd₄, c.rd, a.rd]; exact h.rd
  · rw [wr₇, wr₆]; show s₄.wr = _; rw [wr₄, c.wr, a.wr]; exact h.wr
  · rw [sp₇, sp₆]; show s₄.sp = _; rw [sp₄, c.sp, a.sp]; exact h.sp
  · exact h.frame.trans (stepFrame hk fStep)
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.RISCV64
