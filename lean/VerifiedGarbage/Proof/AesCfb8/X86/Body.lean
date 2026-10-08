import VerifiedGarbage.Proof.AesCfb8.X86.Steps
import VerifiedGarbage.Proof.AesCbc.X86.Body

/-!
# AES-CFB8 on x86: one byte

`encBody_ok` and `decBody_ok`: one run of `body` takes the loop invariant
(`Loop.lean`) from `k` bytes to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`). The input block is copied to the
scratch buffer and enciphered there (`call_ok`), the data byte is replaced,
and the input block is shifted (`finish_wp`).
-/

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.Impl.AesCfb8.X86
open VG.Impl.AesCbc.X86 (cOff blkCall)
open VG.Impl.CmacAes.X86 (argOp at_ xor4 zero4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 add0' arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.X86 (E W R Iv Dp N S schR ivR scrR argsR stkR iv0 wK savedMem BlkPre BlkPost blk_call
  covIv covSv Sv)
open VG.Proof.Aes.X86 (BlocksImpl)
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

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.sv : (Sv32 s₀).setWidth 64 = Sv s₀ := addr_eq (by have := hp.scr_fit; omega)

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_fit
  exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) :
    (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.byt_stk {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (stkR s₀) :=
  (hp.b_data.sub_right (UPre.data_sub hk)).symm

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega)

/-- The stack arguments, in a state whose memory differs only within `Big`. -/
theorem UPre.args_of {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    ∀ i < 6, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun _ hi => hp.arg_keep hf hi

/-- The arguments of a call on the copy of the input block, with the working
space at the start of the scratch buffer. -/
theorem UPre.blkPre {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = Sv32 s₀)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (Sv32 s₀) (S s₀) (R s₀) := by
  have hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hd := hp.sv
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.b_sch, ?_,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_,
    by have := hp.scr_fit; omega, ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hp.scrN (by decide)]; have := hp.scr_fit; omega
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
structure PreA (s₀ : State) (s : State) (s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (Sv32 s₀) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = copy4Mem s.mem (Sv s₀) ((Iv s₀).setWidth 64)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_eq : pre = .mov .ebp (argOp 5) :: .mov .ebx (argOp 2) :: (zero4 .ebp cOff ++
    (xor4 .ebp .ebx .ebp cOff 0 cOff ++ (.mov .eax (argOp 0) :: .mov .ecx (argOp 1) :: .mov .ebx (.reg .ebp) ::
      .alu .add .ebx (.imm 2048) :: .mov .edi (.imm 1) :: []))) := rfl

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have big := UPre.big_of h.frame
  have hargs := hp.args_of big
  have hsc := hp.scr_fit
  have hiv := hp.iv_fit
  rw [pre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 5 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 2 (by decide))
    fun s₂ u₂ => ?_
  have p₂ : s₂.gpr .ebp = S s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have b₂ : s₂.gpr .ebx = Iv s₀ := u₂.gpr
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₂.wr, u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [p₂]; unfold cOff; omega) (by rw [p₂, w₂]; exact covSv (by simp))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), p₂]
  have b₃ : s₃.gpr .ebx = Iv s₀ := by rw [g₃ _ (by decide), b₂]
  have rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₃]; unfold cOff; omega) (by rw [b₃]; omega) (by rw [p₃]; unfold cOff; omega)
    (by rw [p₃, rw₃]; exact covSv (by simp))
    (by rw [b₃, add0, rw₃]; exact covIv (by simp))
    (by rw [p₃, wr₃, w₂]; exact covSv (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = copy4Mem s.mem (Sv s₀) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, p₃, b₃, add0, m₃, p₂, u₂.mem, u₁.mem]; rfl
  have f₄ : Frame [⟨Sv s₀, 16⟩] s.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  have big₄ : Frame (Big s₀) s₀.mem s₄.mem := big.trans (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  have esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄.gpr _ (by decide) (by decide), g₃ _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, rd₃, wr₃, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hp.args_of big₄ 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), esp₄])
    (by rw [u₅.rd, u₅.wr, rw₄]; exact hp.arg_in (by decide)) (by rw [u₅.mem]; exact hp.args_of big₄ 1 (by decide))
    fun s₆ u₆ => ?_
  refine wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_movi fun s₉ u₉ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → s₉.gpr r = s₄.gpr r :=
    fun r ha hc hb hd => by
      rw [u₉.other _ hd, u₈.other _ hb, u₇.other _ hb, u₆.other _ hc, u₅.other _ ha]
  have g₄' : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .ebp → s₄.gpr r = s.gpr r :=
    fun r ha hc hb hp' => by
      rw [g₄.gpr _ ha hc, g₃ _ ha, u₂.other _ hb, u₁.other _ hp']
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, g₄.rd, rd₃, u₂.rd, u₁.rd]
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, wr₃, u₂.wr, u₁.wr]
  have esp₉ : s₉.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₄]
  have ebp₉ : s₉.gpr .ebp = S s₀ := by
    rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄.gpr _ (by decide) (by decide), p₃]
  refine ⟨hp.blkPre ?_ ?_ ?_ u₉.gpr ebp₉ esp₉ (by rw [rd₉, h.rd]) (by rw [wr₉, h.wr]),
    by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄' _ (by decide) (by decide) (by decide)
      (by decide)],
    by rw [esp₉, h.esp],
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄], rd₉, wr₉⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄.gpr _ (by decide) (by decide), p₃]
    rfl

/-! ## The call -/

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  esi : s₂.gpr .esi = Dp s₀ + BitVec.ofNat 32 k
  esp : s₂.gpr .esp = E s₀
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body v.enc post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => hq s₂ ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨(S s₀).setWidth 64, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi],
    by rw [c.saved .esp (by simp [calleeSaved]), esp₁], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hp.sv]; exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · rw [hb]; exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have o := c.out
    rw [hp.sv] at o
    rw [← headD_bytesAt s₂.mem (Sv s₀), o, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copy4Mem_bytes _ hp.iv_sv.symm, h.iv]

/-! ## After the call -/

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `al`), the input block reloaded, the shift and `advance` take the
invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (esi₃ : s₃.gpr .esi = s₂.gpr .esi) (esp₃ : s₃.gpr .esp = s₂.gpr .esp)
    (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v) (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : (s₃.gpr .eax).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)) :
    WP isa (.block (.mov .ebx (argOp 2) :: (shift ++ Impl.AesCfb8.X86.advance))) s₃
      fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  have hiv := hp.iv_fit
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  -- Memory after the byte.
  have fByte : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₃.mem := by
    rw [mem₃]
    refine (a.frame.sub fun r hr => ?_).trans ((frame_write8 _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have stepOf : ∀ {m : Mem}, Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m := fun hf => hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have big₃ : Frame (Big s₀) s₀.mem s₃.mem := (UPre.big_of h.frame).trans ((stepOf fByte).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have esp₃' : s₃.gpr .esp = E s₀ := by rw [esp₃, a.esp]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, a.rd, a.wr, h.rd, h.wr]
  refine wp_arg (s₀ := s₀) esp₃' (by rw [rw₃]; exact hp.arg_in (by decide)) (hp.args_of big₃ 2 (by decide))
    fun s₄ u₄ => ?_
  have rl : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₄.rd, u₄.wr, rw₃, hp.rd, hp.wr]; rfl
  have wl : s₄.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₄.wr, wr₃, a.wr, h.wr, hp.wr]
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ :=
    shift_ok s₄ (Q := (Iv s₀).setWidth 64) (by rw [u₄.gpr]) (by rw [u₄.gpr]; omega)
      (fun d n hd => by rw [rl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega)⟩)
      (fun d n hd => by rw [wl]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hd (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem := by
    rw [mem₅, u₄.mem]
    exact fByte.trans ((AesCfb8.shiftMem32_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have big₅ : Frame (Big s₀) s₀.mem s₅.mem := (UPre.big_of h.frame).trans ((stepOf fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine WP.mono (advance_wp hp hk
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), esi₃, a.esi])
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), esp₃'])
    (hp.args_of big₅) (by rw [rd₅, wr₅, u₄.rd, u₄.wr, rw₃]))
    fun s₆ ⟨esi₆, esp₆, _, mem₆, rd₆, wr₆, zf₆⟩ => ⟨?_, zf₆⟩
  have newByte : s₆.mem (byt s₀ k) = v := by
    rw [mem₆, mem₅, byte_frame (AesCfb8.shiftMem32_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), u₄.mem, mem₃,
      writeW8_self]
  have ivIn : bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 = inKk s₀ enc k := by
    rw [u₄.mem, mem₃, Proof.Cmac.bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame a.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
        · exact hp.b_iv.symm) (by decide), h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  have eax₄ : (s₄.gpr .eax).setWidth 8 = if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [u₄.other _ (by decide), hc]
  refine ⟨esi₆, esp₆, by rw [rd₆, rd₅, u₄.rd, rd₃, a.rd, h.rd], by rw [wr₆, wr₅, u₄.wr, wr₃, a.wr, h.wr],
    by rw [mem₆]; exact h.frame.trans (stepOf fStep), ?_, ?_⟩
  · rw [mem₆, hp.bytes_step hk fStep, h.data, ← mem₆, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk),
      hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₆, mem₅, AesCfb8.shiftMem32_bytes, ivIn, eax₄]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

/-! ## One byte -/

/-- The data byte before the byte operation. -/
theorem AfterCall.byte {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) :
    s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  rw [byte_frame a.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.byt_sv hk
    · exact hp.byt_stk hk), h.byte hk]

/-- The registers and regions the byte operation needs. -/
theorem AfterCall.regs {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) (u : Upd s₂ s₃ .ebp (arg s₀ 5)) :
    addr (s₃.gpr .esi) 0 = byt s₀ k ∧ addr (s₃.gpr .ebp) 2048 = Sv s₀ ∧
      InRegions (s₃.rd ++ s₃.wr) (byt s₀ k) 1 ∧ InRegions (s₃.rd ++ s₃.wr) (Sv s₀) 1 ∧
      InRegions s₃.wr (byt s₀ k) 1 := by
  have rl : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u.rd, u.wr, a.rd, a.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u.other _ (by decide), a.esi]; simp only [addr, add0']; exact hp.dataA hk
  · rw [u.gpr]; exact hp.sv
  · rw [rl]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩
  · rw [rl]; exact ⟨scrR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [u.wr, a.wr, h.wr, hp.wr]; exact ⟨dataR s₀, by simp, hp.cByt hk⟩

theorem encBody_ok (v : BlocksImpl) : BodyOk true (body v.enc encPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h encPost fun s₂ a => ?_
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans (a.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  rw [encPost_eq]
  refine wp_arg (s₀ := s₀) a.esp (by rw [a.rd, a.wr, h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.args_of big₂ 5 (by decide)) fun s₃ u₃ => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.regs hp hk h u₃
  obtain ⟨s₄, run₄, rax₄, g₄, mem₄, rd₄, wr₄⟩ := encByte_ok s₃ eP eT rP rT wP
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, finish_wp hp hk h a (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)])
    (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)]) (by rw [mem₄, u₃.mem])
    (by rw [rd₄, u₃.rd]) (by rw [wr₄, u₃.wr]) (by rw [a.byte hp hk h, a.out]) ?_⟩
  rw [rax₄, u₃.mem, a.byte hp hk h, a.out]; rfl

theorem decBody_ok (v : BlocksImpl) : BodyOk false (body v.enc decPost) := by
  intro s₀ hp k hk s h
  refine call_ok v hp h decPost fun s₂ a => ?_
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans (a.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  rw [decPost_eq]
  refine wp_arg (s₀ := s₀) a.esp (by rw [a.rd, a.wr, h.rd, h.wr]; exact hp.arg_in (by decide))
    (hp.args_of big₂ 5 (by decide)) fun s₃ u₃ => ?_
  obtain ⟨eP, eT, rP, rT, wP⟩ := a.regs hp hk h u₃
  obtain ⟨s₄, run₄, rax₄, g₄, mem₄, rd₄, wr₄⟩ := decByte_ok s₃ eP eT rP rT wP
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, finish_wp hp hk h a (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)])
    (by rw [g₄ _ (by decide) (by decide), u₃.other _ (by decide)]) (by rw [mem₄, u₃.mem])
    (by rw [rd₄, u₃.rd]) (by rw [wr₄, u₃.wr]) (by rw [a.byte hp hk h, a.out, BitVec.xor_comm]) ?_⟩
  rw [rax₄, u₃.mem, a.byte hp hk h]; rfl

end VG.Proof.AesCfb8.X86
