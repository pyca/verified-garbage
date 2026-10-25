module

public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Loop
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Steps
import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-!
# AES-CFB8 on RISC-V: one byte

As on PPC64LE (`Proof/AesCfb8/PPC64LE/Body.lean`): `encBody_ok` and
`decBody_ok`, one run of `body` takes the loop invariant (`Loop.lean`) from
`k` bytes to `k + 1` (`BodyOk`). The input block is copied to the block at
`sv` and enciphered there (`call_ok`), the data byte is replaced, and the
input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCbc.RISCV64 VG.Impl.AesCfb8.RISCV64
open VG.Proof.AesCbc (aesWith_state set_prefix)
open VG.Proof.AesCbc.RISCV64 (wK W R Iv Dp N S q sv schR ivR scrR wsR cR iv0 vars in_rw CallPre
  blk_call encryptBlocks_noFrames a1_ofNat bytesAt_frame savePtr_ok copy_wp q_lt sv_eq cR_sub wsR_sub
  ofNat_zero_add)
open VG.Spec.Aes (bytesAt)

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [AesCfb8.writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem one {r : Region} {P : Addr} {n : Nat} (hd : (⟨P, n⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem LInv.regs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_ws {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (wsR s₀) :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right wsR_sub

theorem UPre.byt_cR {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (cR s₀) :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right cR_sub

theorem UPre.iv_cR : (ivR s₀).Disjoint (cR s₀) := hp.iv_scr.sub_right cR_sub

theorem UPre.sv_wrap : (sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  have := q_lt s₀
  rw [sv_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048 + q s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The arguments of a call on the block at `sv`, with the working space at
the start of the scratch buffer. -/
theorem UPre.callPre {s : State}
    (a0 : s.gpr .a0 = W s₀) (a1 : s.gpr .a1 = s₀.gpr .a1) (a2 : s.gpr .a2 = sv s₀)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 1) (a4 : s.gpr .a4 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (sv s₀) (S s₀) (R s₀) where
  a0 := a0
  a1 := by rw [a1, a1_ofNat]
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right cR_sub
  ws := hp.sch_scr.sub_right wsR_sub
  ds := hp.cR_wsR
  wrap := hp.sv_wrap
  reads := by
    have := q_lt s₀
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048 + q s₀, sv_eq s₀, by simp only; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    have := q_lt s₀
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048 + q s₀, sv_eq s₀, by simp only; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (sv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  frame : Frame [cR s₀] s.mem s₁.mem
  blk : bytesAt s₁.mem (sv s₀) 16 = bytesAt s.mem (Iv s₀) 16
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) :
    r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 := by
  revert hr; cases r <;> decide

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  unfold pre
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₁ e₁ => ?_
  subst e₁
  have g₁ (r : Reg) (h0 : r ≠ .t0) : (s.write .t0 (s.gpr .s6 + BitVec.ofNat 64 2048 +
      BitVec.ofNat 64 (pad (s.gpr .s6 + BitVec.ofNat 64 2048)))).gpr r = s.gpr r :=
    RegUpd.gpr_write_of_ne _ _ h0
  refine copy_wp (dst := .t0) (src := .s3) (P := sv s₀) (Q := Iv s₀) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_self, h.s6]) (by rw [g₁ _ (by decide), h.s3])
    ⟨ivR s₀, by rw [RegUpd.rd_write, RegUpd.wr_write, hR]; simp, fun _ h => h⟩
    ⟨scrR s₀, by rw [RegUpd.wr_write, hW]; simp, cR_sub⟩ (hp.iv_cR).symm
    fun s₂ g₂ b₂ f₂ rd₂ wr₂ sp₂ => ?_
  unfold mov
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_li (imm := 1) (by decide)
    fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have g₂' (r : Reg) (h0 : r ≠ .t0) (h3 : r ≠ .t3) : s₂.gpr r = s.gpr r := by rw [g₂ r h3, g₁ r h0]
  have t0₂ : s₂.gpr .t0 = sv s₀ := by rw [g₂ _ (by decide), RegUpd.gpr_write_self, h.s6]
  have keep (r : Reg) (hr : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    obtain ⟨h0, h1, h2, h3, h4, ht0, -, -, ht3⟩ := preserved_ne hr
    rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, u₄.other _ h1, u₃.other _ h0, g₂' r ht0 ht3]
  refine ⟨hp.callPre ?_ ?_ ?_ ?_ ?_ ?_ ?_, keep, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, g₂' _ (by decide) (by decide), h.s1]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂' _ (by decide) (by decide), h.s2]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), t0₂]
  · rw [u₇.other _ (by decide), u₆.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂' _ (by decide) (by decide), h.s6]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, RegUpd.rd_write, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, RegUpd.wr_write, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
    have := f₂; rwa [RegUpd.mem_write] at this
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, b₂, RegUpd.mem_write]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, RegUpd.rd_write]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, RegUpd.wr_write]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, RegUpd.sp_write]

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  sp : s₂.sp = s.sp
  frame : Frame [wsR s₀, cR s₀] s.mem s₂.mem
  out : s₂.mem (sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₃ c => hq s₃ ?_)
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (a.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, cR_sub⟩)
  refine ⟨fun r hr => by rw [c.saved r hr, a.saved r hr], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    by rw [c.sp, a.sp], (a.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨cR s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨cR s₀, by simp, fun _ h => h⟩
    · exact ⟨wsR s₀, by simp, fun _ h => h⟩
  · rw [← headD_bytesAt s₃.mem (sv s₀), c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.blk, h.iv]

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `t1`, the block at `sv` in `t0`), the shift and `advance` take the
invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (t0₃ : s₃.gpr .t0 = sv s₀)
    (g₃ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s₃.gpr r = s₂.gpr r)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v)
    (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr) (sp₃ : s₃.sp = s₂.sp)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : (s₃.gpr .t1).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)) :
    WP isa (.block (shift ++ Impl.AesCfb8.RISCV64.advance)) s₃ (LInv enc s₀ (k + 1)) := by
  have g₃' (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h0, h1, h2, -⟩ := preserved_ne hr
    rw [g₃ r h0 h1 h2, a.g r hr]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wrs hp]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, a.rd, wr₃, a.wr, h.regs hp]
  refine shift_wp (Q := Iv s₀) (T := sv s₀) (by rw [g₃' .s3 (by decide), h.s3]) t0₃
    ⟨ivR s₀, by rw [hR₃]; simp, fun _ h => h⟩ ⟨ivR s₀, by rw [hW₃]; simp, fun _ h => h⟩
    ⟨scrR s₀, by rw [hR₃]; simp, cR_sub⟩ ⟨scrR s₀, by rw [hW₃]; simp, cR_sub⟩ hp.iv_cR
    fun s₄ g₄ b₄ f₄ rd₄ wr₄ sp₄ => ?_
  refine advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide), g₃' .s4 (by decide), h.s4])
    (by rw [g₄ _ (by decide), g₃' .s5 (by decide), h.s5])
    fun s₅ s4₅ s5₅ keep₅ mem₅ rd₅ wr₅ sp₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h4 : r ≠ .s4) (h5 : r ≠ .s5) : s₅.gpr r = s.gpr r := by
    rw [keep₅ r h4 h5, g₄ r (preserved_ne hr).2.2.2.2.2.2.2.2, g₃' r hr]
  -- Memory.
  have f₁ : Frame [⟨byt s₀ k, 1⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₂.mem := a.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wsR s₀, by simp, fun _ h => h⟩
    · exact ⟨cR s₀, by simp, fun _ h => h⟩
  have f₂ : Frame [⟨byt s₀ k, 1⟩, ivR s₀, wsR s₀, cR s₀] s₂.mem s₃.mem := by
    rw [mem₃]
    exact (frame_write8 _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have f₃ : Frame [⟨byt s₀ k, 1⟩, ivR s₀, wsR s₀, cR s₀] s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨cR s₀, by simp, fun _ h => h⟩
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, wsR s₀, cR s₀] s.mem s₅.mem := by
    rw [mem₅]; exact (f₁.trans f₂).trans f₃
  have newByte : s₅.mem (byt s₀ k) = v := by
    rw [mem₅, byte_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.byt_iv hk
      · exact hp.byt_cR hk), mem₃, writeW8_self]
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = inKk s₀ enc k := by
    rw [mem₃, bytesAt_frame (frame_write8 _ _ _) (one (hp.byt_iv hk).symm) (by decide),
      bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right wsR_sub
        · exact hp.iv_cR) (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨?_, ?_, ?_, s4₅, s5₅, ?_, fun r hr hv' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s6 (by decide) (by decide) (by decide), h.s6]
  · rw [g r hr (fun e => hv' (by simp [e])) (fun e => hv' (by simp [e])), h.keep r hr hv']
  · rw [rd₅, rd₄, rd₃, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, a.wr, h.wr]
  · rw [sp₅, sp₄, sp₃, a.sp, h.sp]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨wsR s₀, by simp, fun _ h => h⟩
      · exact ⟨cR s₀, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₅, b₄, ivIn, hc]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

theorem encBody_ok : BodyOk true (body encPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h encPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (sv s₀) 1 := by
    have c₀ := Offset.contains_base (sv s₀) (d := 0) (n := 1) (k := 16) (by decide) (by decide)
    rw [ofNat_zero_add] at c₀
    exact in_rw (r := scrR s₀) (by simp) (cR_sub _ c₀)
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.byt_ws hk
      · exact hp.byt_cR hk), h.byte hk]
  unfold encPost
  simp only [List.append_assoc]
  refine encByte_wp (P := byt s₀ k) (S := S s₀) (by rw [a.g .s4 (by decide), h.s4])
    (by rw [a.g .s6 (by decide), h.s6])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk)) fun s₃ t1₃ t0₃ g₃ mem₃ rd₃ wr₃ sp₃ => ?_
  exact finish_wp hp hk h a t0₃ g₃ mem₃ rd₃ wr₃ sp₃ (by rw [p₂, a.out])
    (by rw [t1₃, xor_ext]; simp only [↓reduceIte, p₂, a.out])

theorem decBody_ok : BodyOk false (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (sv s₀) 1 := by
    have c₀ := Offset.contains_base (sv s₀) (d := 0) (n := 1) (k := 16) (by decide) (by decide)
    rw [ofNat_zero_add] at c₀
    exact in_rw (r := scrR s₀) (by simp) (cR_sub _ c₀)
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.byt_ws hk
      · exact hp.byt_cR hk), h.byte hk]
  unfold decPost
  simp only [List.append_assoc]
  refine decByte_wp (P := byt s₀ k) (S := S s₀) (by rw [a.g .s4 (by decide), h.s4])
    (by rw [a.g .s6 (by decide), h.s6])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk)) fun s₃ t1₃ t0₃ g₃ mem₃ rd₃ wr₃ sp₃ => ?_
  exact finish_wp hp hk h a t0₃ g₃ mem₃ rd₃ wr₃ sp₃ (by rw [p₂, a.out, BitVec.xor_comm])
    (by rw [t1₃, byte_ext]; simp only [Bool.false_eq_true, ↓reduceIte, p₂])

end VG.Proof.AesCfb8.RISCV64
