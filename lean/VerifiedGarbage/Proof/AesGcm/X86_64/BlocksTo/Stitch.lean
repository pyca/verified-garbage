import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Mid
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo

/-!
# AES-GCM on whole blocks out of place, x86-64: the first `16 ⌊n / 16⌋` blocks in one pass

Untrusted: everything here is checked by Lean. After the entry, if there are
at least 16 blocks, `r9` becomes `16 ⌊n / 16⌋` and `r11` the working space
(`split_ok`), which with the output in `r10` and the other arguments still in
their registers meets what the out-of-place interleaved loops need
(`spreTo_of`); their result is `Mid` with `q = 16 ⌊n / 16⌋`
(`mid_of_postTo`). With fewer, `q = 0` (`stitch_ok`); then `rest`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode SPreTo EPostTo StitchToOkM)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The registers the entry leaves as they were. -/
def argRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

theorem contains_prefix (a : Addr) {k L : Nat} (h : k ≤ L) : (⟨a, L⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

section
variable {M : CtxMode} {s : State} (hp : BT M s)
include hp

omit hp in
/-- `r9 := 16 ⌊r9 / 16⌋` and `r11` at the powers. -/
theorem split_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) (h11 : s₁.gpr .r11 = S s) :
    WP isa (.block [.mov .rax (.reg .r9), .alu .and .rax (imm 15), .alu .sub .r9 (.reg .rax),
      .alu .add .r11 (imm 64)]) s₁ fun s₃ =>
      s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16) ∧ s₃.gpr .r11 = S s + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s₁.gpr r) ∧
      s₃.mem = s₁.mem ∧ s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have e15 := and15 (s.gpr .r9)
  rw [imm_eq (by decide)] at e15
  have esub : s.gpr .r9 - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 (n s - n s % 16) := by
    rw [← ofNat_sub (Nat.mod_le _ _) hn]; simp
  apply WP.of_runBlock
  refine ⟨_, by xrun [h9, h11, e15, esub], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, h11]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- What the out-of-place loops need, from the arguments in their
registers, `r9 = 16 ⌊n / 16⌋`, the output in `r10` and the working space in
`r11`. -/
theorem spreTo_of {s₃ : State} (h16 : 16 ≤ n s) (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16))
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (h10 : s₃.gpr .r10 = Dst s)
    (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 64) (hrd : s₃.rd = s.rd)
    (hwr : s₃.wr = s.wr) (hf₃ : Frame [kR' s] s.mem s₃.mem) : SPreTo M s₃ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hq : (s₃.gpr .r9).toNat = n s - n s % 16 := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have hqn : 16 * (n s - n s % 16) ≤ n s * 16 := by omega
  have pd : Region.Sub ⟨Dst s, 16 * (n s - n s % 16)⟩ (dR s) := Region.sub_prefix hqn
  have pr : Region.Sub ⟨Src s, 16 * (n s - n s % 16)⟩ (srcR s) := Region.sub_prefix hqn
  have ps : Region.Sub ⟨S s + BitVec.ofNat 64 64, 1024⟩ (sR s) := Offset.sub_base _ (by decide)
  have hws := hp.w_s
  have ts : (S s + BitVec.ofNat 64 64).toNat = (S s).toNat + 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Nat.reducePow, Nat.reduceMod]; omega
  have ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  have ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  have ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  have ed : s₃.gpr .r8 = Src s := hg _ (by simp [argRegs])
  have rd : s.rd = [kR M s, srcR s, aR s] := hp.rd
  have wr : s.wr = wR s := hp.wr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
  simp only [Gcm.X86_64.Stitch.nr, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.sR, Gcm.X86_64.Stitch.oR,
    Gcm.X86_64.Stitch.pR, ek, er, ec, ey, ed, h10, h11, hq, hrd, hwr]
  exacts [hp.rounds, by omega, by omega, ⟨kR M s, by rw [rd]; simp, Region.contains_self _ _⟩,
    ⟨cR s, by rw [wr]; simp, Region.contains_self _ _⟩, ⟨yR s, by rw [wr]; simp, Region.contains_self _ _⟩,
    ⟨srcR s, by rw [rd]; simp, contains_prefix _ hqn⟩, ⟨dR s, by rw [wr]; simp, contains_prefix _ hqn⟩,
    ⟨sR s, by rw [wr]; simp, Offset.contains_base _ (by decide) (by decide)⟩,
    hp.k_c, hp.k_y, hp.k_d.sub_right pd, hp.k_s.sub_right ps,
    hp.c_r.symm.sub_left pr, hp.y_r.symm.sub_left pr, (hp.r_d.sub_left pr).sub_right pd,
    (hp.r_s.sub_left pr).sub_right ps, hp.c_d.symm.sub_left pd, hp.y_d.symm.sub_left pd,
    (hp.d_s.sub_left pd).sub_right ps, hp.c_s.symm.sub_left ps, hp.y_s.symm.sub_left ps, hp.c_y,
    by have := hp.w_r; omega, by have := hp.w_d; omega, hp.w_k, by rw [ts]; omega,
    M.frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub) hp.w_k hp.ok]

/-- `Mid` after the out-of-place loops, from what they leave. -/
theorem mid_of_postTo {s₃ s₄ : State} (h9 : s₃.gpr .r9 = BitVec.ofNat 64 (n s - n s % 16))
    (hg : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r) (hcs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r)
    (h10 : s₃.gpr .r10 = Dst s) (h11 : s₃.gpr .r11 = S s + BitVec.ofNat 64 64)
    (hrd : s₃.rd = s.rd) (hwr : s₃.wr = s.wr) (hkp : Kept s 0 s₃.mem) (hf₃ : Frame [kR' s] s.mem s₃.mem)
    (P : EPostTo s₃ s₄) : Mid s (n s - n s % 16) 0 s₄ := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have data := P.data
  have ctr := P.ctr
  have frame := P.frame
  have y := P.y
  generalize hq : n s - n s % 16 = q at *
  have hqn : q ≤ n s := by omega
  have hq9 : (s₃.gpr .r9).toNat = q := by rw [h9, toNat_ofNat_of_lt (by omega)]
  have ek : s₃.gpr .rdi = K s := hg _ (by simp [argRegs])
  have er : s₃.gpr .rsi = s.gpr .rsi := hg _ (by simp [argRegs])
  have ec : s₃.gpr .rdx = C s := hg _ (by simp [argRegs])
  have ey : s₃.gpr .rcx = Y s := hg _ (by simp [argRegs])
  have ed : s₃.gpr .r8 = Src s := hg _ (by simp [argRegs])
  simp only [Gcm.X86_64.Stitch.cR, Gcm.X86_64.Stitch.yR, Gcm.X86_64.Stitch.oR, Gcm.X86_64.Stitch.pR,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.pp,
    Gcm.X86_64.Stitch.nb, ec, ey, h10, h11, hq9] at frame
  simp only [Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.sp, Gcm.X86_64.Stitch.nb, Gcm.X86_64.Stitch.cb,
    Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.ciph, Gcm.X86_64.Stitch.sch, Gcm.X86_64.Stitch.nr,
    Gcm.X86_64.Stitch.kp, ek, er, ec, ed, h10, hq9] at data
  simp only [Gcm.X86_64.Stitch.cp, Gcm.X86_64.Stitch.cb, Gcm.X86_64.Stitch.nb, ec, hq9] at ctr
  simp only [Gcm.X86_64.Stitch.yp, Gcm.X86_64.Stitch.hk, Gcm.X86_64.Stitch.y₀, Gcm.X86_64.Stitch.kp,
    Gcm.X86_64.Stitch.op, Gcm.X86_64.Stitch.nb, ey, ek, h10, hq9] at y
  have kd : ∀ r ∈ [kR' s], (kR M s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right kR'_sub
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  have eK : Spec.Aes.bytesAt s₃.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) :=
    bytesAt_frame hf₃ (fun r hr => (kd r hr).sub_left (Region.sub_prefix (Nat.le_trans hRb M.ge)))
      (by have := hp.w_k; have := M.ge; omega)
  have eH : blockAt s₃.mem (K s + 240) = hk s :=
    block_kR' hf₃ ((hp.k_s.sub_right kR'_sub).sub_left (Offset.sub_base (d := 240) _ (by have := M.ge; omega)))
  have eC : blockAt s₃.mem (C s) = cb s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  have eY : blockAt s₃.mem (Y s) = y₀ s := block_kR' hf₃ (kR'_disj hp _ (by simp)).symm
  have pr : Region.Sub ⟨Src s, 16 * q⟩ (srcR s) := Region.sub_prefix (by omega)
  have eS : blocksAt s₃.mem (Src s) q = blocksAt s.mem (Src s) q := blocksAt_frame hf₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hp.r_s.sub_left pr).sub_right kR'_sub)
    (by have := hp.w_r; omega)
  rw [eK, eC, eS] at data
  rw [eC] at ctr
  rw [eH, eY, data] at y
  have pd : Region.Sub ⟨Dst s, 16 * q⟩ (dR s) := Region.sub_prefix (by omega)
  have sk : Region.Disjoint (kR' s) ⟨S s + BitVec.ofNat 64 64, 1024⟩ :=
    Offset.base_disjoint _ (by decide) (by have := hp.w_s; omega)
  have fk : ∀ r ∈ [cR s, yR s, (⟨Dst s, 16 * q⟩ : Region), (⟨S s + BitVec.ofNat 64 64, 1024⟩ : Region)],
      (kR' s).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kR'_disj hp _ (by simp)
    · exact kR'_disj hp _ (by simp)
    · exact (kR'_disj hp (dR s) (by simp)).sub_right pd
    · exact sk
  have fw : Frame (wR s) s.mem s₄.mem := by
    refine (frame_kR' hf₃).trans (frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨cR s, by simp, fun _ h => h⟩
    · exact ⟨yR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, pd⟩
    · exact ⟨sR s, by simp, Offset.sub_base _ (by decide)⟩
  refine ⟨hqn, ?_, fun r hr => ?_, P.rd.trans hrd, P.wr.trans hwr, hkp.frame frame fk, fw, data, ctr, y⟩
  · rw [P.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hg _ (by simp [argRegs])
  · have hr' : r ≠ .rax ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.gpr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2]; exact hcs r hr

omit hp in
/-- `cmp r9, 16`. -/
theorem cmp16_ok {s₁ : State} (h9 : s₁.gpr .r9 = s.gpr .r9) :
    WP isa (.block [.alu .cmp .r9 (imm 16)]) s₁ fun s₂ => s₂.gpr = s₁.gpr ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.cf = some (decide (n s < 16)) := by
  have e16 : BitVec.signExtend 64 (BitVec.ofNat 32 16) = 16 := by decide
  apply WP.of_runBlock
  simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, e16, h9, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp

/-- The interleaved part, from the state after the entry. -/
theorem stitch_ok {piece : Prog isa} (hpiece : StitchToOkM M piece)
    {s₁ : State} (h11 : s₁.gpr .r11 = S s) (h10 : s₁.gpr .r10 = Dst s)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r10 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    WP isa (stitchPart piece) s₁ (Mid s (n s - n s % 16) 0) := by
  refine WP.seq (WP.mono (cmp16_ok (hg _ (by decide) (by decide))) fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)
  refine WP.ite (decide (n s < 16)) (by simp only [eval, cf₂]) (fun h => ?_) (fun h => ?_)
  · have h0 : n s - n s % 16 = 0 := by simp at h; omega
    rw [h0]
    refine WP.block_nil (mid_entry hp (by rw [g₂]; exact hg _ (by decide) (by decide))
      (fun r hr => by rw [g₂]; exact hg r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr))
      (by rw [m₂]; exact hk) (by rw [m₂]; exact hf) (rd₂.trans hrd) (wr₂.trans hwr))
  · have h16 : 16 ≤ n s := by simp at h; omega
    refine WP.seq (WP.mono (split_ok (s := s) (s₁ := s₂) (by rw [g₂]; exact hg _ (by decide) (by decide))
      (by rw [g₂, h11])) fun s₃ ⟨h9, h11₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
    have h10₃ : s₃.gpr .r10 = Dst s := by rw [g₃ _ (by decide) (by decide) (by decide), g₂, h10]
    have keepR : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r a b c d => by
      rw [g₃ r a b d, g₂, hg r d c]
    have ga : ∀ r ∈ argRegs, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keepR _ (by decide) (by decide) (by decide) (by decide)
    have gc : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact keepR _ (by decide) (by decide) (by decide) (by decide)
    have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans hrd)
    have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans hwr)
    have hk₃ : Kept s 0 s₃.mem := by rw [m₃, m₂]; exact hk
    have hf₃ : Frame [kR' s] s.mem s₃.mem := by rw [m₃, m₂]; exact hf
    exact WP.mono (hpiece s₃ (spreTo_of hp h16 h9 ga h10₃ h11₃ rd₃' wr₃' hf₃)) fun s₄ hP =>
      mid_of_postTo hp h9 ga gc h10₃ h11₃ rd₃' wr₃' hk₃ hf₃ hP

end

end VG.Proof.AesGcm.X86_64.BlocksTo
