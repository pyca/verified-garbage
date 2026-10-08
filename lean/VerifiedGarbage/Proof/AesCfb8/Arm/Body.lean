import VerifiedGarbage.Proof.AesCfb8.Arm.Steps
import VerifiedGarbage.Proof.AesCbc.Arm.Body

/-!
# AES-CFB8 on ARMv7: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`). The input block is
copied to the scratch buffer and enciphered there (`call_ok`), as AES-CBC
calls the block function (`Proof/AesCbc/Arm/Body.lean`), the data byte is
replaced, and the input block is shifted (`finish_wp`).
-/

namespace VG.Proof.AesCfb8.Arm

open VG VG.Arm VG.Impl.AesCfb8.Arm
open VG.Impl.AesCbc.Arm (cOff encFrame zero4)
open VG.Impl.CmacAes.Arm (xor4 mov)
open VG.Proof.CmacAes.Arm (W R Dp N S schR scrR argsR belowR savedMem add0)
open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_call encF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_add wp_subs ofNat_beq_zero sub_ofNat)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes aesWith_state set_prefix bytesAt_of_statesAt)
open VG.Proof.AesCbc.Arm (Iv ivR iv0 wK Sv covIv covSv copy_wp Moved encFrame_eq)
open VG.Spec.Aes (bytesAt)

/-- The copy of the input block, as a 32-bit address. -/
abbrev Sv32 (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

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

theorem UPre.sv : State.addr (Sv32 s₀) = Sv s₀ := hp.scrA (by decide)

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_fit
  exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) :
    (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨State.addr (S s₀), 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.byt_b {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (belowR s₀) :=
  (hp.b_data.sub_right (UPre.data_sub hk)).symm

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨State.addr (S s₀), 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega)

/-- The arguments of a call on the copy of the input block, with the working
space at the start of the scratch buffer. -/
theorem UPre.blkCall {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = Sv32 s₀) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1 := by
  have hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hd := hp.sv
  have hsc := hp.scr_fit
  have qN : (Sv32 s₀).toNat = (S s₀).toNat + 2048 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by rw [qN]; omega, by omega, ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-! ## The code before the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_eq : pre = zero4 .r10 2048 ++ (xor4 .r10 .r6 .r10 2048 0 2048 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm 2048), .mov .r3 (.imm 1),
      .mov .r12 (.reg .r10)] : List Instr)) := rfl

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  have rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [pre_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega)
    (by rw [h.r10]; omega) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r10, w₀]; exact covSv (by simp)) fun s₁ g₁ => ?_
  have m₁ : s₁.mem = copy4Mem s.mem (Sv s₀) (State.addr (Iv s₀)) := by rw [g₁.mem, h.r10, h.r6, add0]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 hlr => by
      rw [u₆.other _ h12, u₅.other _ h3, u₄.other _ h2, u₃.other _ h1, u₂.other _ h0, g₁.gpr _ h12 hlr]
  have sp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, g₁.sp]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, g₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, g₁.wr]
  have g10 : s₁.gpr .r10 = S s₀ := by rw [g₁.gpr _ (by decide) (by decide), h.r10]
  refine ⟨hp.blkCall ?_ ?_ ?_ ?_ ?_ (by rw [sp₆, h.sp]) (by rw [rd₆, h.rd]) (by rw [wr₆, h.wr]), keep, sp₆,
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁], rd₆, wr₆⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      g₁.gpr _ (by decide) (by decide), h.r4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), h.r5]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g10]; rfl
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g10]

/-! ## The call -/

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r
  sp : s₂.sp = s.sp
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  rw [encFrame_eq]
  refine WP.seq (WP.mono (blk_call encF a.pre) fun s₂ c => hq s₂ ?_)
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨State.addr (S s₀), 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r h0 h1 h2 h3 h9 h12 hlr => ?_, by rw [c.sp, a.sp], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · have : r ∈ preserved ∨ r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3 ∨ r = .r9 ∨ r = .r12 ∨ r = .lr := by
      cases r <;> simp [preserved]
    rcases this with hr | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c.saved r hr hlr, a.keep r h0 h1 h2 h3 h12 hlr]
    all_goals contradiction
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hp.sv]; exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, svSub⟩
    · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · rw [hb]; exact ⟨belowR s₀, by simp, fun _ h => h⟩
  · have o := bytesAt_of_statesAt c.out
    rw [hp.sv] at o
    rw [← headD_bytesAt s₂.mem (Sv s₀), o, show encF.f = Spec.Aes.cipher from rfl, UPre.sched_bytes hp big₁,
      ← aesWith_state, a.mem, copy4Mem_bytes _ hp.iv_sv.symm, h.iv]

/-! ## After the call -/

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `r12`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) (sp₃ : s₃.sp = s₂.sp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : s₃.gpr .r12 = (if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)).setWidth 32) :
    WP isa (.block (shift ++ Impl.AesCfb8.Arm.advance)) s₃
      fun s' => LInv enc s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hiv := hp.iv_fit
  have hdf := hp.data_fit
  have hN := (stackArg s₀ 0).isLt
  have g₃' (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h9 : r ≠ .r9) (h12 : r ≠ .r12)
      (hlr : r ≠ .lr) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h12 hlr, a.g r h0 h1 h2 h3 h9 h12 hlr]
  have rl : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  have wl : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wr, hp.wr]
  have r6 : s₃.gpr .r6 = Iv s₀ := by
    rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  obtain ⟨s₄, run₄, g₄, sp₄, mem₄, rd₄, wr₄⟩ :=
    shift_ok s₃ (Q := State.addr (Iv s₀)) (by rw [r6]) (by rw [r6]; omega) hc
      (fun d n hd => by rw [rl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega)⟩)
      (fun d n hd => by rw [wl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have g (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h7 : r ≠ .r7) (h8 : r ≠ .r8)
      (h9 : r ≠ .r9) (h12 : r ≠ .r12) (hlr : r ≠ .lr) : s₆.gpr r = s.gpr r := by
    rw [u₆.other _ h8, u₅.other _ h7, g₄ r h0 h1 h2 h3, g₃' r h0 h1 h2 h3 h9 h12 hlr]
  have r8₅ : s₅.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  have dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have mem₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  -- Memory.
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₆.mem := by
    rw [mem₆, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMem32_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨belowR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have newByte : s₆.mem (byt s₀ k) = v := by
    rw [mem₆, mem₄, byte_frame (AesCfb8.shiftMem32_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃, writeW8_self]
  have ivIn : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = inKk s₀ enc k := by
    rw [mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
        · exact hp.b_iv.symm) (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [u₆.gpr, r8₅, dec], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r4]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r5]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r6]
  · rw [u₆.other _ (by decide), u₅.gpr, g₄ _ (by decide) (by decide) (by decide) (by decide),
      g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add_eq _ (c := k + 1) (by omega)]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r10]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r11]
  · rw [u₆.sp, u₅.sp, sp₄, sp₃, a.sp, h.sp]
  · rw [u₆.rd, u₅.rd, rd₄, rd₃, a.rd, h.rd]
  · rw [u₆.wr, u₅.wr, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, fun _ h => h⟩
      · exact ⟨belowR s₀, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₆, mem₄, AesCfb8.shiftMem32_bytes, ivIn]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]
  · rw [z₆, r8₅, dec]; exact ofNat_beq_zero (by omega)

/-! ## One byte -/

/-- The data byte after the call. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.byt_sv hk
    · exact hp.byt_b hk), h.byte hk]

/-- The registers and regions the byte operation needs. -/
theorem AfterCall.args {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    State.addr (s₂.gpr .r7 + BitVec.ofNat 32 0) = byt s₀ k ∧
      State.addr (s₂.gpr .r10 + BitVec.ofNat 32 2048) = Sv s₀ ∧
      InRegions (s₂.rd ++ s₂.wr) (byt s₀ k) 1 ∧ InRegions (s₂.rd ++ s₂.wr) (Sv s₀) 1 ∧
      InRegions s₂.wr (byt s₀ k) 1 := by
  have rl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]; simp only [BitVec.add_zero]
    exact hp.dataA hk
  · rw [a.g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
    exact hp.sv
  · rw [rl]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩
  · rw [rl]; exact ⟨scrR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [a.wr, h.wr, hp.wr]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩

theorem encBody_ok : BodyOk true (body encPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h encPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, r12₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := encByte_ok s₂ eP eT rP rT wP
  rw [encPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [r12₃]; rfl

theorem decBody_ok : BodyOk false (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.args hp hk h
  obtain ⟨s₃, run₃, r12₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := decByte_ok s₂ eP eT rP rT wP
  rw [decPost_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, finish_wp hp hk h a g₃ sp₃ mem₃ rd₃ wr₃
    (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [r12₃, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.Arm
