import VerifiedGarbage.Proof.AesCfb8.AArch64.Steps

/-!
# AES-CFB8 on AArch64: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`). The input block is copied to the
scratch buffer and enciphered there (`call_ok`), the data byte is replaced,
and the input block is shifted (`finish_wp`).
-/

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCfb8.AArch64
open VG.Impl.AesCbc.AArch64 (cOff copy)
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR scrR iv0 wK in_rw Sv cIv0 cIv8 cSv0 cSv8 sv8 copy_ok
  CallPre CallPost blk_call x1_ofNat preserved_ne)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := Proof.Cmac.bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

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

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨S s₀, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega)

theorem UPre.sv_wrap : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The arguments of a call on the copy of the input block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPre {s : State}
    (x0 : s.gpr .x0 = W s₀) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = Sv s₀)
    (x3 : s.gpr .x3 = 1) (x4 : s.gpr .x4 = S s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  x0 := x0
  x1 := by rw [x1, x1_ofNat]
  x2 := x2
  x3 := x3
  x4 := x4
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  wrap := hp.sv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Sv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copyMem s.mem (Sv s₀) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  obtain ⟨s₁, run₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    copy_ok s (dst := .x24) (src := .x21) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
      (by rw [h.x24]; rfl) (by rw [h.x24]; exact sv8 _)
      (by rw [h.x21]; simp) (by rw [h.x21])
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := args_ok s₁
  rw [pre_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have keep (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r := by
    rw [cs₂ r hr, g₁ r (preserved_ne hr).1]
  refine ⟨hp.callPre (by rw [x0₂, g₁ _ (by decide), h.x19]) (by rw [x1₂, g₁ _ (by decide), h.x20])
    (by rw [x2₂, g₁ _ (by decide), h.x24]) x3₂ (by rw [x4₂, g₁ _ (by decide), h.x24])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr]), keep, by rw [sp₂, sp₁], by rw [mem₂, mem₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨S s₀, 2064⟩] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNoFrames a.pre) fun s₂ c => hq s₂ ?_)
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r hr h30 => by rw [c.saved r hr h30, a.saved r hr], by rw [c.sp, a.sp], by rw [c.rd, a.rd],
    by rw [c.wr, a.wr], (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · rw [← headD_bytesAt s₂.mem (Sv s₀), c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copyMem_bytes _ hp.iv_sv.symm, h.iv]

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `x9`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → s₃.gpr r = s₂.gpr r) (sp₃ : s₃.sp = s₂.sp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : s₃.gpr .x9 = (if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)).setWidth 64) :
    WP isa (.block (shift ++ Impl.AesCfb8.AArch64.advance)) s₃ (LInv enc s₀ (k + 1)) := by
  have g₃' (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (preserved_ne hr).1 (preserved_ne hr).2, a.g r hr h30]
  have rl : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, a.rd, a.wr, h.regs hp]
  have wl : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wrs hp]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    shift_ok s₃ (Q := Iv s₀) (by rw [g₃' .x21 (by simp [preserved]) (by decide), h.x21]) hc
      (by rw [rl]; exact in_rw (by simp) cIv0) (by rw [rl]; exact in_rw (by simp) cIv8)
      (by rw [wl]; exact in_rw (by simp) cIv0) (by rw [wl]; exact in_rw (by simp) cIv8)
  obtain ⟨s₅, run₅, x22₅, x23₅, keep₅, sp₅, mem₅, rd₅, wr₅⟩ := advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x22 (by simp [preserved]) (by decide),
      h.x22])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃' .x23 (by simp [preserved]) (by decide),
      h.x23])
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  have g (r : Reg) (hr : r ∈ preserved) (h30 : r ≠ .x30) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
      s₅.gpr r = s.gpr r := by
    have hne : r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [keep₅ r h22 h23, g₄ r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2, g₃' r hr h30]
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMemX_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have newByte : s₅.mem (byt s₀ k) = v := by
    rw [mem₅, mem₄, byte_frame (AesCfb8.shiftMemX_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃, writeW8_self]
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = inKk s₀ enc k := by
    rw [mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (one _ _ _ (hp.iv_scr.sub_right (Region.sub_prefix (by decide))))
        (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨?_, ?_, ?_, x22₅, x23₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .x19 (by simp [preserved]) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by simp [preserved]) (by decide) (by decide) (by decide), h.x20]
  · rw [g .x21 (by simp [preserved]) (by decide) (by decide) (by decide), h.x21]
  · rw [g .x24 (by simp [preserved]) (by decide) (by decide) (by decide), h.x24]
  · intro r hr h19 h20 h21 h22 h23 h24 h30
    rw [g r hr h30 h22 h23, h.other r hr h19 h20 h21 h22 h23 h24 h30]
  · rw [sp₅, sp₄, sp₃, a.sp, h.sp]
  · rw [rd₅, rd₄, rd₃, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₅, mem₄, AesCfb8.shiftMemX_bytes, ivIn]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

/-- The data byte after the call. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.byt_sv hk), h.byte hk]

theorem AfterCall.args {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.gpr .x22 = byt s₀ k ∧ s₂.gpr .x24 + BitVec.ofNat 64 2048 = Sv s₀ ∧
      InRegions (s₂.rd ++ s₂.wr) (byt s₀ k) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (Sv s₀) 1 ∧
      InRegions s₂.wr (byt s₀ k) 1 := by
  have rl : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  refine ⟨by rw [a.g .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [a.g .x24 (by simp [preserved]) (by decide), h.x24], ?_, ?_, ?_⟩
  · rw [rl]; exact in_rw (by simp) (hp.cByt hk)
  · rw [rl]; exact in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  · rw [a.wr, h.wrs hp]; exact in_rw (by simp) (hp.cByt hk)

theorem encBody_ok (v : BlocksImpl) : BodyOk true (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, x9₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := encByte_ok s₂ eP eT rP rT wP
  rw [encPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [x9₃]; rfl

theorem decBody_ok (v : BlocksImpl) : BodyOk false (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, x9₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := decByte_ok s₂ eP eT rP rT wP
  rw [decPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [x9₃, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.AArch64
