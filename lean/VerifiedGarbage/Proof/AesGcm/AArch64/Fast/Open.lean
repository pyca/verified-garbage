module

import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on AArch64: `open`'s path for TLS records

Untrusted: everything here is checked by Lean. Once the tag length is allowed
and the received tag is at `W`, for a 12-byte nonce and at most 16 bytes of
additional data, `openRunWith gh` computes the tag as `seal`'s path does
(`front_ok`; the ciphertext's whole blocks by one call of `gh`, its last bytes
and the lengths block in registers; `tagSeg_ok`, `tagCall_ok`), into `W + uO`
where `openMain` puts it, and compares it as `openMain` does (`cmp_ok`):
`openRunA_ok` leaves what `openMain` leaves at its branch on the tag (`MidO`),
with memory changed only in `fastFrame`, and the rest is `openMain`'s
(`omB_ok`). It writes nothing below `W + 16`, where the received tag is, nor
the saved registers or the slots of the arguments.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-! ## What the path writes -/

/-- The working space the path writes: between the received tag and the saved
registers, and above the slots of the arguments. -/
abbrev fastFrame (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 256, 2304⟩]

theorem fastFrame_work (W : Addr) : ∀ r ∈ fastFrame W, Region.Sub r (workR W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem saved_fastFrame (W : Addr) : ∀ r ∈ fastFrame W, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

theorem slots_fastFrame (W : Addr) : ∀ r ∈ fastFrame W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)

/-- A region at `W + d` below `W + 128` and above the received tag. -/
theorem fast_lo {W : Addr} {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ fastFrame W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega)⟩

/-- A region at `W + 16 + d` below `W + 128`. -/
theorem fast_lo' {W : Addr} {d k : Nat} (h₂ : 16 + d + k ≤ 128) :
    ∃ r' ∈ fastFrame W, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r' := by
  rw [add_ofNat_assoc]; exact fast_lo (by omega) (by omega)

/-- A region at `W + d` above `W + 256`. -/
theorem fast_hi {W : Addr} {d k : Nat} (h₁ : 256 ≤ d) (h₂ : d + k ≤ 2560) :
    ∃ r' ∈ fastFrame W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub W h₁ (by omega)⟩

/-! ## The path up to the branch on the tag -/

variable (c : Callees) (cl : Prog isa)

/-- `openRunWith` up to the branch on the tag. -/
def openRunA : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.front
  (.seq (.block ([mov .x24 .x26, imm .x25 0] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
      [mov .x13 .x24, mov .x12 .x23]))
  (.seq Impl.AesGcm.AArch64.Fast.padMul
  (.seq (.block (Impl.AesGcm.AArch64.Fast.lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
    (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- `openRunWith` is `openRunA` then `omB`. -/
theorem openRunWith_split : PEq (.seq (openRunA c cl) (omB c)) (Impl.AesGcm.AArch64.Fast.openRunWithP c cl) := by
  unfold openRunA omB Impl.AesGcm.AArch64.Fast.openRunWithP
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

section
variable {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `openRunA`, from the state after `tagIn` with the arguments still in
`x4` to `x7`, for a function `gh` that hashes the whole blocks as `vg_ghash`
does when called with `vg_ghash`'s arguments from a state with the regions
of `t`, whose memory differs from `t`'s only in the working space and the
text (`hgh`). -/
theorem openRunAX_ok (v : GcmImpl) (hMK : MulKey) {s₀ t : State} {ex : List Region} {I : Mem → Prop}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR W] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t.rd → s'.wr = t.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) :
    WP isa (openRunA v.callees cl) t fun u =>
      MidO (fastFrame W ++ ex) Ctx W SP D Np A R 12 al n tl t u ∧ I u.mem := by
  have L := o.lay
  have hle := tagLenOk_le hok
  have hnlt := o.dat.ok.lt
  have hRb := o.rounds
  have ddW := o.ddW
  have dcW := o.dcW
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t :=
    ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, rfl⟩
  generalize hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H at hJ
  unfold openRunA
  refine WP.seq (WP.mono (front_ok L hMK hJ o.aad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  have he₂ := h₂.env
  -- The whole blocks of the ciphertext, by `gh`.
  rw [WP.seq_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, x24₃, x25₃, r₃⟩ : ∃ s₃, runBlock isa [mov .x24 .x26, imm .x25 0] s₂ =
      some s₃ ∧ s₃.gpr .x24 = BitVec.ofNat 64 n ∧ s₃.gpr .x25 = BitVec.ofNat 64 0 ∧ Regs [.x24, .x25] s₂ s₃ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h₂.x26], by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := he₂.of_regs r₃
  have hdat₃ : DataOk (W + BitVec.ofNat 64 16) W s₃ D n :=
    o.dat.ok.of_eq (by rw [r₃.rd, h₂.rd]) (by rw [r₃.wr, h₂.wr])
  generalize hx₁ : bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length) = x₁ at h₂
  have hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 H x₁ D n 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun r hr => r₃.others r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide), Nat.zero_le _, by rw [r₃.others _ (by decide), h₂.x23]; simp,
      by rw [x24₃, Nat.sub_zero], x25₃, hdat₃, by rw [r₃.mem]; exact h₂.hH, fun ha => by simpa [bytesAt] using ha,
      .inr (by omega), Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  have FW : Frame [workR W, ⟨D, n⟩] t.mem s₆.mem := by
    have w : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    have F2 := h₂.frame.sub fun r hr => w (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide))
    have F6 : Frame [workR W, ⟨D, n⟩] s₂.mem s₆.mem := by
      rw [← r₃.mem]
      refine h₆.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact w (stW (by decide))
      · exact w (stW (by decide))
      · exact w (Lay.wSub (by decide))
    exact F2.trans F6
  have rd₆' : s₆.rd = t.rd := by rw [rd₆, r₃.rd, h₂.rd]
  have wr₆' : s₆.wr = t.wr := by rw [wr₆, r₃.wr, h₂.wr]
  have exW : ∀ {R : Region}, Region.Sub R (workR W) → ∀ r ∈ ex, R.Disjoint r :=
    fun hR r hr => (hexW r hr).sub_left hR
  have exS : ∀ {r : Region}, (∃ r' ∈ fastFrame W, Region.Sub r r') → ∃ r' ∈ fastFrame W ++ ex, Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_append_left _ h, hs⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2WithX_ok L (.inr rfl)
    (fun r hr => (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))) (exW (stW (by decide))) h₆
    (hgh s₆ h₆.call (stW (by decide)) (Lay.wSub (by decide)) rd₆' wr₆' h₆.env.sp FW
      (Offset.sub_base D (by omega)))))
    fun s₇ ⟨⟨⟨h₇, hlt₇⟩, I₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * (n / 16) = j at h₇ hlt₇
  have hjn : j ≤ n := by omega
  have he₇ := h₇.env
  have hab₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H x₁ := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁0, List.take_length, ← hx₁, ← h₂.y, r₃.mem]
    · rw [hx₁0, Proof.Gcm.whole_of_mod hx₁0, List.drop_length]; rfl
  have hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = ghash H (blocks (x₁ ++ bytesAt s₃.mem D j)) :=
    (h₇.abs hab₃).whole_eq (by rw [List.length_append, length_bytesAt]; omega)
  have key₃ : KeyAt H s₃.mem W := by rw [r₃.mem]; exact h₂.key
  have key₇ : KeyAt H s₇.mem W := by
    refine key₃.frame h₇.frame fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact exW (Lay.wSub (by decide)) r hr
  -- `H'` again, `Y`, and the last bytes.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := H) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact key₇.2)
    key₇.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (loadRev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ s₁₀.gpr .x12 = D + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), h₇.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), h₇.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  have he₁₀ := he₉.of_regs r₁₀
  have hk₁₀ : HKey H s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  have hy₁₀ : s₁₀.v Y = ext8 (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) := by
    rw [v₁₀, l₉, he₈.x20, m₈, rev64b_read]
  have rd₁₀ : s₁₀.rd = s₃.rd := by rw [r₁₀.rd, o₉.rd, rd₈, rd₇, rd₆]
  have wr₁₀ : s₁₀.wr = s₃.wr := by rw [r₁₀.wr, o₉.wr, wr₈, wr₇, wr₆]
  have hdj : DataOk (W + BitVec.ofNat 64 16) W s₁₀ (D + BitVec.ofNat 64 j) (n - j) :=
    (hdat₃.drop hjn).of_eq rd₁₀ wr₁₀
  refine WP.seq (WP.mono (WP.with_rdwr (padMul_ok hMK he₁₀ hk₁₀ hy₁₀ x12₁₀ x13₁₀ (by omega) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))))) fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  have m₁₀ : s₁₀.mem = s₇.mem := by rw [r₁₀.mem, o₉.mem, m₈]
  -- What the path has written so far.
  have Fa : Frame (fastFrame W) t.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact fast_lo (by decide) (by decide)
    · exact fast_lo (by decide) (by decide)
    · exact fast_hi (by decide) (by decide)
    · exact fast_hi (by decide) (by decide)
  have Fb : Frame (fastFrame W ++ ex) s₂.mem s₇.mem := by
    rw [← r₃.mem]
    refine h₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact exS (fast_lo' (by decide))
    · exact exS (fast_lo' (by decide))
    · exact exS (fast_hi (by decide) (by decide))
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  have Fc : Frame (fastFrame W) s₇.mem s₁₁.mem := by
    rw [← m₁₀]
    refine f₁₁.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact fast_lo (by decide) (by decide)
  have mx : ∀ {m m' : Mem}, Frame (fastFrame W) m m' → Frame (fastFrame W ++ ex) m m' :=
    fun h => h.mono fun r hr => List.mem_append_left _ hr
  have F₁₁ : Frame (fastFrame W ++ ex) t.mem s₁₁.mem := ((mx Fa).trans Fb).trans (mx Fc)
  have slot₁₁ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept F₁₁ (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide)))) h₁ h₂'
  -- The lengths block.
  unfold Impl.AesGcm.AArch64.Fast.lensTagAt
  rw [WP.seq_iff]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have w₁ := he₁₁.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he₁₁.perm.wW (show 104 + 8 ≤ 2560 by decide)
  have q₁ := he₁₁.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have x26₁₁ : s₁₁.gpr .x26 = BitVec.ofNat 64 n := by
    rw [og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  obtain ⟨s₁₂, run₁₂, m₁₂, og₁₂, sp₁₂, rd₁₂, wr₁₂, v₁₂⟩ : ∃ s₁₂, runBlock isa
      [.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
        .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] s₁₁ = some s₁₂ ∧
      s₁₂.mem = (s₁₁.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s₁₁ s₁₂ ∧ s₁₂.sp = s₁₁.sp ∧ s₁₂.rd = s₁₁.rd ∧ s₁₂.wr = s₁₁.wr ∧
      s₁₂.v = s₁₁.v := by
    have e₁ : s₁₁.mem.read (W + 224#64) 8 = BitVec.ofNat 64 al := by
      rw [show s₁₁.mem.read (W + 224#64) 8 = s₁₁.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl,
        slot₁₁ 224 (by decide) (by decide), o.sL]
    refine ⟨_, by arun [he₁₁.x19, q₁, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc, gpr_write, ite_true, ite_false,
      reduceCtorEq, e₁, x26₁₁]
  refine WP.of_runBlock ⟨s₁₂, run₁₂, ?_⟩
  have he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => og₁₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₂ rd₁₂ wr₁₂
  have fT₁₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s₁₁.mem s₁₂.mem := by rw [m₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hT₁₂ : blockAt s₁₂.mem (s₁₂.gpr .x19 + BitVec.ofNat 64 tO) = ofBytes (lensBlock al n) := by
    rw [he₁₂.x19, show tO = 96 from rfl, blockAt, m₁₂, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens,
      toNat_ofNat_of_lt (show al < 2 ^ 64 by omega), toNat_ofNat_of_lt hnlt]
    rfl
  have hk₁₂ : HKey H s₁₂ := hk₁₁.of_v (by rw [v₁₂]) (by rw [v₁₂]) (by rw [v₁₂])
  have y₁₂ : s₁₂.v Y = ext8 (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j)))
      (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j))) := by rw [v₁₂]; exact y₁₁
  rw [WP.block_append_iff]
  refine WP.mono (mulT_ok hMK hk₁₂ y₁₂ (by rw [he₁₂.x19]; exact he₁₂.perm.wR (by decide)))
    fun s₁₃ ⟨y₁₃, _, o₁₃⟩ => ?_
  rw [hT₁₂] at y₁₃
  rw [WP.block_append_iff]
  refine WP.mono (storeY_ok y₁₃ (by rw [o₁₃.gpr, o₁₃.wr, he₁₂.x20]; exact he₁₂.perm.stW (by decide)))
    fun s₁₄ ⟨m₁₄, b₁₄, o₁₄⟩ => ?_
  have g₁₄ : s₁₄.gpr = s₁₂.gpr := by rw [o₁₄.gpr]; exact o₁₃.gpr
  rw [show s₁₃.gpr .x20 = W + BitVec.ofNat 64 16 by rw [o₁₃.gpr, he₁₂.x20]] at b₁₄ m₁₄
  have he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ :=
    he₁₂.keep (fun r _ => by rw [g₁₄]) (by rw [o₁₄.sp, o₁₃.sp]) (by rw [o₁₄.rd, o₁₃.rd]) (by rw [o₁₄.wr, o₁₃.wr])
  have fY₁₄ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s₁₂.mem s₁₄.mem := by
    rw [m₁₄, o₁₃.mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have x22₁₄ : s₁₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x22 (by decide), h₂.x22, o.x22]
  -- The tag, to `W + uO`.
  refine WP.mono (WP.with_rdwr (tagSeg_ok L (o := uO) (.inr rfl) he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ hRb))
    fun s₁₆ ⟨h₁₆, rd₁₆, wr₁₆⟩ => ?_
  refine WP.seq (WP.mono (WP.with_rdwr (tagCall_ok L v (.inr rfl) h₁₆)) fun s₁₇ ⟨h₁₇, rd₁₇, wr₁₇⟩ => ?_)
  have Fd : Frame (fastFrame W) s₁₁.mem s₁₄.mem := by
    refine (fT₁₂.sub fun r hr => ?_).trans (fY₁₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fast_lo (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact fast_lo' (by decide)
  have F₁₄ : Frame (fastFrame W ++ ex) t.mem s₁₄.mem := F₁₁.trans (mx Fd)
  have Fg : Frame (fastFrame W) s₁₄.mem s₁₇.mem := by
    refine h₁₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fast_lo (by decide) (by decide)
    · exact fast_lo (by decide) (by decide)
    · exact fast_lo (by decide) (by decide)
    · exact fast_hi (by decide) (by decide)
  have F₁₇ : Frame (fastFrame W ++ ex) t.mem s₁₇.mem := F₁₄.trans (mx Fg)
  -- The comparison, the tag length still in `x28`.
  have x28₁₄ : s₁₄.gpr .x28 = BitVec.ofNat 64 tl := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x28 (by decide), h₂.x28, o.x28]
  have x28₁₈ : s₁₇.gpr .x28 = BitVec.ofNat 64 tl := by rw [h₁₇.kept .x28 (by decide), x28₁₄]
  have he₁₈ := h₁₇.env
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L he₁₈ (fun _ _ => rfl : Kept s₁₇.gpr s₁₇) x28₁₈ hle))
    fun s₁₉ ⟨⟨x10₁₉, he₁₉, hk₁₉, _, f₁₉⟩, rd₁₉, wr₁₉⟩ => ?_)
  refine WP.mono (okBit_ok (b := decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₁₇.mem W tl)) (by rw [x10₁₉]; simp only [decide_eq_true_eq]))
    fun s₂₀ ⟨x27₂₀, r₂₀⟩ => ?_
  have he₂₀ := he₁₉.of_regs r₂₀
  have Fe : Frame (fastFrame W) s₁₇.mem s₁₉.mem := by
    refine f₁₉.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact fast_hi (by decide) (by decide)
  have F₂₀ : Frame (fastFrame W ++ ex) t.mem s₂₀.mem := by rw [r₂₀.mem]; exact F₁₇.trans (mx Fe)
  have I₂₀ : I s₂₀.mem := by
    rw [r₂₀.mem]
    exact hI I₇ ((((Fc.trans Fd).trans Fg).trans Fe).sub fun r hr =>
      ⟨workR W, List.mem_singleton_self _, fastFrame_work W r hr⟩)
  -- What the frames keep.
  have dCf : ∀ r ∈ fastFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (fastFrame_work W) dcW
  have dDf : ∀ r ∈ fastFrame W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (fastFrame_work W) ddW
  have hc₁₄ : ciphOf s₁₄.mem Ctx R = ciphOf t.mem Ctx R := ciph_frame F₁₄ (disj_ex dCf hexC) hRb
  have hD₃ : bytesAt s₃.mem D n = bytesAt t.mem D n := by rw [r₃.mem]; exact bytesAt_frame Fa dDf (by omega)
  have ht₁₀ : bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [m₁₀, bytesAt_frame h₇.frame (disj_absEx (data_absFrame (.inr rfl) (hdat₃.drop hjn))
      fun r hr => (hexD r hr).sub_left (Offset.sub_base D (by omega))) (by omega)]
  have hsplit : bytesAt s₃.mem D n = bytesAt s₃.mem D j ++ bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [← bytesAt_add, Nat.add_sub_cancel' hjn]
  -- `J₀`, still at the state, and the first counter block.
  have dT : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st0_w L ⟨by decide, by decide⟩
  have hJ₁₄ : blockAt s₁₄.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H (bytesAt t.mem Np 12) := by
    have e₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame h₇.frame fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | rfl | hr
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by decide⟩
        · exact exW (Lay.wSub (by decide)) r hr
    rw [blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st0_disj L (by decide) (by decide)),
      blockAt_frame fT₁₂ dT, blockAt_frame f₁₁ dT, m₁₀, e₇, r₃.mem, h₂.j0]
  have hcb : blockAt s₂₀.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 H (bytesAt t.mem Np 12)) := by
    have d₄₈ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩
    rw [r₂₀.mem, blockAt_frame f₁₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by decide⟩),
      blockAt_frame h₁₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩
        · exact st_wpart L (by decide) ⟨by decide, by decide⟩),
      blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_st (a := 48) (n := 16) (d := 16) (k := 16) (.inr (by decide)) (by decide) (by decide)),
      blockAt_frame fT₁₂ d₄₈, blockAt_frame f₁₁ d₄₈, m₁₀,
      blockAt_frame h₇.frame (disj_absEx (fun r hr => (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide)))
        (exW (stW (by decide)))),
      r₃.mem, h₂.cb]
  -- The tag.
  have hT : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.toBytes (ghashFrom H
      (ghash H (blocks (Proof.Gcm.padded (bytesAt t.mem A al) (bytesAt t.mem D n))))
      [ofBytes (lensBlock (bytesAt t.mem A al).length (bytesAt t.mem D n).length)] ^^^
      ciphOf t.mem Ctx R (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) := by
    rw [h₁₇.out, b₁₄, hJ₁₄, hc₁₄, hY₇, ht₁₀, ← hx₁, ← hD₃, hsplit,
      ghash_padded _ _ _ _ (by rw [length_bytesAt]; omega) (by rw [length_bytesAt]; omega), length_bytesAt,
      List.length_append, length_bytesAt, length_bytesAt, Nat.add_sub_cancel' hjn]
    rfl
  have hT' : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H
      (bytesAt t.mem Np 12) (bytesAt t.mem A al) (bytesAt t.mem D n) := by
    rw [hT, Proof.Gcm.fullTag_eq]
  have hW₁₈ : bytesAt s₁₇.mem W tl = bytesAt t.mem W tl := by
    refine bytesAt_frame F₁₇ (fun r hr => ?_) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | hr
    · exact (Offset.disjoint_base W (show tl ≤ 16 by omega) (by decide)).symm
    · exact (Offset.disjoint_base W (show tl ≤ 256 by omega) (by decide)).symm
    · exact exW (Region.sub_prefix (by omega)) r hr
  have hb : (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
        (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT', hW₁₈]
  generalize hBd : decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) = B at x27₂₀
  have hBeq : decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
      (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  have x22₂₀ : s₂₀.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₂₀.others _ (by decide), hk₁₉ .x22 (by decide), h₁₇.kept .x22 (by decide), x22₁₄]
  subst hH
  refine ⟨⟨he₂₀, F₂₀, x22₂₀, by rw [x27₂₀, hBeq],
    o.dat.of_eq (by rw [r₂₀.rd, rd₁₉, rd₁₇, rd₁₆, o₁₄.rd, o₁₃.rd, rd₁₂, rd₁₁, rd₁₀, r₃.rd, h₂.rd])
      (by rw [r₂₀.wr, wr₁₉, wr₁₇, wr₁₆, o₁₄.wr, o₁₃.wr, wr₁₂, wr₁₁, wr₁₀, r₃.wr, h₂.wr]),
    by rw [slot_kept F₂₀ (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide)))) (by decide) (by decide), o.sD],
    by rw [slot_kept F₂₀ (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide)))) (by decide) (by decide), o.sN],
    hcb⟩, I₂₀⟩

theorem openRunA_ok (v : GcmImpl) (hMK : MulKey) {s₀ t : State}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hok : Spec.Gcm.tagLenOk tl = true)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = t.rd → s'.wr = t.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] t.mem s'.mem →
      WP isa cl s' (GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (openRunA v.callees cl) t (MidO (fastFrame W) Ctx W SP D Np A R 12 al n tl t) :=
  WP.mono (openRunAX_ok cl v hMK (ex := []) (I := fun _ => True) o h4 h5 h6 h7 hal hok (by simp) (by simp)
    (by simp) (fun _ _ => trivial) fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
      WP.mono (hgh s' hc sY sS hrd hwr hsp hf) fun _ g => ⟨g, trivial⟩) fun _ q => q.1

end

/-! ## `open` -/

/-- `openRunWith`, once the received tag is at `W`, for a `gh` that hashes as
`vg_ghash` called with memory changed since the entry `s₀` only in the
working space and the text. -/
theorem openRunWith_post (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t) (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      WP isa cl s' (GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t (OpenPost Ctx W SP Np A D Tg R nl al n tl s₀) := by
  subst h12
  have L := o.lay
  have F₀ : Frame [workR W, ⟨D, n⟩] s₀.mem t.mem :=
    o.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  refine (openRunWith_split v.callees cl).symm.wp (WP.seq (WP.mono (openRunA_ok cl v hMK o h4 h5 h6 h7 hal hok
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf => hgh s' hc sY sS (hrd.trans o.rd₀) (hwr.trans o.wr₀) hsp
      (F₀.trans hf))
    fun _ mo => WP.mono (omB_ok v L o.rounds o.ddW o.dcW mo (fastFrame_work W)) fun s₄ hpost => ?_))
  dsimp only at hpost
  obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
  refine ⟨he₄, o.sv.frame F₄ fun r hr => ?_, ?_⟩
  · rcases List.mem_cons.mp hr with h | hr
    · subst h; exact (o.ddW.sub_right (Lay.wSub (by decide))).symm
    rcases List.mem_append.mp hr with hr | hr
    · exact saved_fastFrame W r hr
    · exact saved_crFrame L o.dat r hr
  · obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
    rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
    · rw [ite_eq_left hc]
      simp only [hc, decide_true, ite_true] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩
    · rw [ite_eq_right hc]
      simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩

/-- `openRunWith_post` for a call that may also write `ex` and establish
`I`, which what the rest writes keeps (`hI`). -/
theorem openRunWith_postX (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR W, ⟨D, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t fun u =>
      OpenPost Ctx W SP Np A D Tg R nl al n tl s₀ u ∧ I u.mem := by
  subst h12
  have L := o.lay
  have F₀ : Frame [workR W, ⟨D, n⟩] s₀.mem t.mem :=
    o.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  have dD : ∀ r ∈ fastFrame W ++ ex, (⟨D, n⟩ : Region).Disjoint r :=
    disj_ex (keep_of_sub (fastFrame_work W) o.ddW) hexD
  have dC : ∀ r ∈ fastFrame W ++ ex, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    disj_ex (keep_of_sub (fastFrame_work W) o.dcW) hexC
  refine (openRunWith_split v.callees cl).symm.wp (WP.seq (WP.mono (openRunAX_ok cl v hMK o h4 h5 h6 h7 hal hok
    hexW hexD hexC (fun hi f => hI hi (f.sub fun r hr => ⟨workR W, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩))
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd => hgh s' hc sY sS (hrd.trans o.rd₀) (hwr.trans o.wr₀) hsp
      (F₀.trans hf) hd)
    fun _ ⟨mo, i₇⟩ => WP.mono (omBX_ok v L o.rounds mo dD dC) fun s₄ ⟨hpost, f₈⟩ => ?_))
  have I₄ : I s₄.mem := hI i₇ (f₈.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩)
  obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
  refine ⟨⟨he₄, o.sv.frame F₄ fun r hr => ?_, ?_⟩, I₄⟩
  · rcases List.mem_cons.mp hr with h | hr
    · subst h; exact (o.ddW.sub_right (Lay.wSub (by decide))).symm
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact saved_fastFrame W r hr
      · exact (hexW r hr).sub_left (Lay.wSub (by decide))
    · exact saved_crFrame L o.dat r hr
  · obtain ⟨hc₃, hH₃, hN₃, hA₃, hD₃⟩ := o.vals
    rw [hc₃, hH₃, hN₃, hA₃, hD₃, hT₃] at x0₄ d₄
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl
    · rw [ite_eq_left hc]
      simp only [hc, decide_true, ite_true] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩
    · rw [ite_eq_right hc]
      simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩

/-- `openRunWith_postX` without an invariant. -/
theorem openRunWith_postE (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t (OpenPost Ctx W SP Np A D Tg R nl al n tl s₀) :=
  WP.mono (openRunWith_postX cl v hMK (I := fun _ => True) o h12 h4 h5 h6 h7 hal hT₃ hok hexW hexD hexC
    (fun _ _ => trivial) fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      WP.mono (hgh s' hc sY sS hr hw hsp hf hd) fun _ g => ⟨g, trivial⟩) fun _ q => q.1

/-- `openWithE_wp` for a TLS record with an allowed tag length, whose call
may also write `ex` and establish `I` (`openRunWith_postX`). -/
theorem openWithEX_wp (v : GcmImpl) (hMK : MulKey) {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} {ex : List Region} {I : Mem → Prop} (hs : openPreXW w extra s extraW)
    (hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12) (htl : Spec.Gcm.tagLenOk (stackArg s 1).toNat = true)
    (hexW : ∀ r ∈ ex, (workR (stackArg s w)).Disjoint r)
    (hexD : ∀ r ∈ ex, (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨s.gpr .x0, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWithE v.callees (8 * w) cl) s fun s' =>
      (GprAbi s s' ∧ openAArch64.post s s') ∧ I s'.mem := by
  unfold Impl.AesGcm.AArch64.Fast.openWithE
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have o₂ := o₁.of_regs r₂
  have x12₂ : s₂.gpr .x12 = stackArg s 0 := by rw [r₂.others _ (by decide), x12₁]
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
  unfold Impl.AesGcm.AArch64.Fast.openFastP
  refine openRestWithX_wp o₂ x12₂ htl fun o' hT hx' => ?_
  have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₂ r hr)
  exact openRunWith_postX cl v hMK o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
    (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT htl hexW hexD hexC hI hgh

/-- `vg_aes_gcm_open` with the path for TLS records, `work` the stack
argument `w`, and its whole blocks hashed by `cl`, which hashes as a call of
`vg_ghash` when run with memory changed since the entry only in the working
space and the text. -/
theorem openWithE_wp (v : GcmImpl) (hMK : MulKey) {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWithE v.callees (8 * w) cl) s fun s' =>
      GprAbi s s' ∧ openAArch64.post s s' := by
  unfold Impl.AesGcm.AArch64.Fast.openWithE
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  have o₂ := o₁.of_regs r₂
  have x12₂ : s₂.gpr .x12 = stackArg s 0 := by rw [r₂.others _ (by decide), x12₁]
  have hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesGcm.AArch64.Fast.openFastP
    refine openRestWith_wp o₂ x12₂ fun o' hT hok hx' => ?_
    have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₂ r hr)
    exact openRunWith_post cl v hMK o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
      (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok hgh
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    exact openRestWith_wp o₂ x12₂ fun o' hT hok _ => openMain_post v o' hT hok

/-- `vg_aes_gcm_open` with the path for TLS records, its whole blocks hashed
by `gh`, which hashes as `vg_ghash` when called with memory changed since the
entry only in the working space and the text. -/
theorem openWith_wp (gh : Fn) (v : GcmImpl) (hMK : MulKey) {extra : List Region} {s : State}
    (hs : openPreX extra s)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg s 2)) → Region.Sub ⟨S, 256⟩ (workR (stackArg s 2)) →
      s'.rd = s.rd → s'.wr = s.wr → Frame [workR (stackArg s 2), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa (.call gh.name gh.code) s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWith v.callees gh) s fun s' => GprAbi s s' ∧ openAArch64.post s s' :=
  openWithE_wp (w := 2) (.call gh.name gh.code) v hMK (.inl rfl) (openPreX_W hs)
    fun s' _ _ _ _ c y z r w _ f => hgh s' c y z r w f

end VG.Proof.AesGcm.AArch64.Fast
