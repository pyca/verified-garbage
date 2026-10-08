import VerifiedGarbage.Proof.AesCtr.X86.Steps
import VerifiedGarbage.Proof.AesCbc.X86.CT

/-!
# AES-CTR on x86: one block, and constant time

`body_ok`: one run of `body` takes the loop invariant AES-CBC's proofs share
(`Proof/AesCbc/X86/Loop.lean`) from `k` blocks to `k + 1`, for `ctrMode`,
for any implementation of the block functions (`BlocksImpl`). The counter
block is copied to the scratch buffer and enciphered there (`pre_wp`), the
output block is XORed into the data block, and the counter block is
incremented (`Steps.lean`). `body_ct`: it is constant time, by the shared
framework, with the call on the copy.
-/

namespace VG.Proof.AesCtr.X86

open VG VG.X86 VG.Impl.AesCtr.X86
open VG.Impl.AesCbc.X86 (cOff blkCall)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4 zero4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.AesCbc (copy4Mem copy4Mem_frame copy4Mem_bytes xorIn4_bytes aesWith_state set_prefix Mode)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- The copy of the counter block, as a 32-bit address. -/
abbrev Sv32 (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrN {d : Nat} (hd : d < 2176) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.sv : (Sv32 s₀).setWidth 64 = Sv s₀ := addr_eq (by have := hp.scr_fit; omega)

/-- The arguments of a call on the copy of the counter block, with the
working space at the start of the scratch buffer. -/
theorem UPre.blkPreSv {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = Sv32 s₀)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (Sv32 s₀) (S s₀) (R s₀) := by
  have hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hd := UPre.sv hp
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.b_sch, ?_,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_,
    by have := hp.scr_fit; omega, ?_, ?_⟩
  · rw [hd]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hd]; exact hp.sv_scr
  · rw [hb, hd]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [UPre.scrN hp (by decide)]; have := hp.scr_fit; omega
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

theorem pre_wp {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
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
  refine ⟨UPre.blkPreSv hp ?_ ?_ ?_ u₉.gpr ebp₉ esp₉ (by rw [rd₉, h.rd]) (by rw [wr₉, h.wr]),
    by rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄' _ (by decide) (by decide) (by decide)
      (by decide)],
    by rw [esp₉, h.esp],
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄], rd₉, wr₉⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      g₄.gpr _ (by decide) (by decide), p₃]
    rfl

/-! ## One block -/

theorem post_eq : post = .mov .ebp (argOp 5) :: (xor4 .esi .ebp .esi 0 cOff 0 ++
    (.mov .ebx (argOp 2) :: (incr ++ advance))) := rfl

theorem body_ok (v : BlocksImpl) : BodyOk AesCtr.ctrMode (body v.enc) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨(S s₀).setWidth 64, 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have f₂ : Frame [⟨Sv s₀, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, UPre.sv hp] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inr (.inr (.inl svSub)))
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  have big₂ := bigOf fs₂
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [post_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 5 (by decide))
    fun s₃ u₃ => ?_
  have p₃ : s₃.gpr .ebp = S s₀ := u₃.gpr
  have i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega) (by rw [p₃]; unfold cOff; omega) (by rw [i₃, qN]; omega)
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [p₃, u₃.rd, u₃.wr, rwl]; exact covSv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (Sv s₀) := by
    rw [g₄.mem, i₃, p₃, add0, hd, u₃.mem]; rfl
  have f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have fs₄ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₄.mem :=
    fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have big₄ : Frame (Big s₀) s₀.mem s₄.mem := bigOf fs₄
  have esp₄ : s₄.gpr .esp = E s₀ := by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hp.args_of big₄ 2 (by decide))
    fun s₅ u₅ => ?_
  have b₅ : s₅.gpr .ebx = Iv s₀ := u₅.gpr
  have rwl₅ : s₅.rd ++ s₅.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₅.rd, u₅.wr, rw₄, hp.rd, hp.wr]; rfl
  have wl₅ : s₅.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₅.wr, g₄.wr, u₃.wr, w₂]
  obtain ⟨s₆, run₆, g₆, mem₆, rd₆, wr₆⟩ := incr_ok s₅ (Q := (Iv s₀).setWidth 64) (by rw [b₅]) (by rw [b₅]; omega)
    (fun d n hdn => by rw [rwl₅]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
    (fun d n hdn => by rw [wl₅]; exact ⟨ivR s₀, by simp, Offset.contains_base _ hdn (by omega)⟩)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have f₆ : Frame [ivR s₀] s₅.mem s₆.mem := by rw [mem₆]; exact incMem_frame _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₆.mem :=
    (fs₄.trans (by rw [u₅.mem]; exact Frame.refl _ _)).trans
      (f₆.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have keep₆ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) (h₄ : r ≠ .edi) (h₅ : r ≠ .ebx)
      (h₆ : r ≠ .ebp) : s₆.gpr r = s₂.gpr r := by
    rw [g₆ r h₁ h₂ h₃ h₄, u₅.other _ h₅, g₄.gpr _ h₁ h₂, u₃.other _ h₆]
  refine WP.mono (advance_wp hp hk
    (by rw [keep₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esi₂])
    (by rw [keep₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₂])
    (hp.args_of (bigOf fStep)) (by rw [rd₆, wr₆, u₅.rd, u₅.wr, rw₄]))
    fun s₈ ⟨esi₈, esp₈, _, mem₈, rd₈, wr₈, zf₈⟩ => ⟨?_, zf₈⟩
  have callIv : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_sv
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have callBlk : ∀ r ∈ [⟨Sv s₀, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀],
      (⟨blk s₀ k, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.blk_sv hk
    · exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_data.sub_right (UPre.data_sub hk)).symm
  have ivIn : bytesAt s₅.mem ((Iv s₀).setWidth 64) 16 = chainK AesCtr.ctrMode s₀ k := by
    rw [u₅.mem, m₄, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_iv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
  have blkIn : bytesAt s₂.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callBlk (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), h.block hk]
  have outBlk : bytesAt s₂.mem (Sv s₀) 16 = Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k) := by
    have o := c.out
    rw [UPre.sv hp] at o
    rw [o, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, copy4Mem_bytes _ hp.iv_sv.symm, h.iv]
  have newBlk : bytesAt s₈.mem (blk s₀ k) 16 =
      Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) (chainK AesCtr.ctrMode s₀ k)) := by
    rw [mem₈, Proof.Cmac.bytesAt_frame f₆ (one (hp.blk_iv hk)) (by decide), u₅.mem, m₄,
      xorIn4_bytes _ (hp.blk_sv hk), blkIn, outBlk]
  have newIv : bytesAt s₈.mem ((Iv s₀).setWidth 64) 16 = Spec.Ctr.inc (chainK AesCtr.ctrMode s₀ k) := by
    rw [mem₈, mem₆, incMem_bytes, ivIn]
  have hl : (outK AesCtr.ctrMode s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have hlt : ((blks s₀).take k).length = k := by simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK AesCtr.ctrMode s₀ (k + 1) = outK AesCtr.ctrMode s₀ k ++ [bytesAt s₈.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, chainK, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, AesCtr.crypt_snoc]
  refine ⟨esi₈, esp₈, by rw [rd₈, rd₆, u₅.rd, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₈, wr₆, u₅.wr, g₄.wr, u₃.wr, c.wr, a.wr, h.wr],
    by rw [mem₈]; exact h.frame.trans (stepFrame hk fStep), ?_, ?_⟩
  · rw [mem₈, hp.blocksAt_step hk fStep, h.data, ← mem₈, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, AesCtr.ctrMode_chain, take_succ_blks s₀ hk, List.length_append, List.length_singleton,
      hlt, AesCtr.next_succ]

/-! ## Constant time -/

/-- What the code before the call leaves, as `Mid`. -/
theorem Mid.ofSv {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₁ : State}
    (h : LInv AesCtr.ctrMode s₀ k s) (a : PreA s₀ s s₁) : Mid s₀ k (Sv32 s₀) s₁ := by
  have big : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (by
    rw [a.mem]
    exact (copy4Mem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  exact ⟨hk, a.pre, ⟨scrR s₀, by simp, by rw [UPre.sv hp]; exact UPre.scr_sub (by decide)⟩, by rw [a.esi, h.esi],
    ⟨by rw [a.esp, h.esp], by rw [a.wr, h.wr], fun _ hi => hp.arg_keep big hi⟩, big⟩

theorem pre_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post_taint : ∃ h, (taint.check (argTaint [.esi] (4 + 4 * 6)) (.block post) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem body_ct (v : BlocksImpl) : BodyCt AesCtr.ctrMode (body v.enc) :=
  fun hp hp' hq k => VG.Proof.AesCbc.X86.body_ct (D := fun s₀ _ => Sv32 s₀)
    (fun hq _ => by rw [Sv32, Sv32, pub_S hq]) v.encOk v.encCt v.encNosp v.encStack pre_taint post_taint
    (@fun _ hp _ hk _ h => WP.mono (pre_wp hp h) fun _ a => Mid.ofSv hp hk h a) hp hp' hq k

end VG.Proof.AesCtr.X86
