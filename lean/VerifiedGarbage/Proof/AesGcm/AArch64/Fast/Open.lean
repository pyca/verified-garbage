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
additional data, `openRunWithP c cl` computes the tag as `seal`'s path does
(`front_ok`; the ciphertext's whole blocks by `cl`, its last bytes
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
abbrev fastFrame (Wn : Nat) (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 256, Wn - 256⟩]

theorem fastFrame_work {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) : ∀ r ∈ fastFrame Wn W, Region.Sub r (workR Wn W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)

theorem saved_fastFrame {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) : ∀ r ∈ fastFrame Wn W, (savedR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)

theorem slots_fastFrame {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) : ∀ r ∈ fastFrame Wn W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by omega)

/-- A region at `W + d` below `W + 128` and above the received tag. -/
theorem fast_lo {Wn : Nat} {W : Addr} {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ fastFrame Wn W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_using [h₂])⟩

/-- A region at `W + 16 + d` below `W + 128`. -/
theorem fast_lo' {Wn : Nat} {W : Addr} {d k : Nat} (h₂ : 16 + d + k ≤ 128) :
    ∃ r' ∈ fastFrame Wn W, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r' := by
  rw [add_ofNat_assoc]; exact fast_lo (by omega_using []) (by omega_using [h₂])

/-- A region at `W + d` above `W + 256`. -/
theorem fast_hi {Wn : Nat} {W : Addr} {d k : Nat} (h₁ : 256 ≤ d) (h₂ : d + k ≤ Wn) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∃ r' ∈ fastFrame Wn W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub W h₁ (by omega)⟩

/-- What the path writes, more precisely: `fastFrame` without the bytes from
`W + 320` to `W + 512`, where `open_to` keeps `dst`. -/
abbrev fastFrameP (Wn : Nat) (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 112⟩, ⟨W + BitVec.ofNat 64 256, 64⟩, ⟨W + BitVec.ofNat 64 512, Wn - 512⟩]

theorem fastFrameP_work {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) : ∀ r ∈ fastFrameP Wn W, Region.Sub r (workR Wn W) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact Lay.wSub (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)

theorem slots_fastFrameP {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∀ r ∈ fastFrameP Wn W, (⟨W + BitVec.ofNat 64 216, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)

/-- Where `open_to` keeps `dst` is outside what the path writes. -/
theorem dst_fastFrameP {Wn : Nat} (W : Addr) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∀ r ∈ fastFrameP Wn W, (⟨W + BitVec.ofNat 64 320, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)
  · exact Offset.disjoint W (.inl (by decide)) (by decide) (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)

theorem fastFrameP_sub {Wn : Nat} {W : Addr} {ex : List Region} (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ∀ r ∈ fastFrameP Wn W ++ ex, ∃ r' ∈ fastFrame Wn W ++ ex, Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub W (by decide) (by omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub W (by decide) (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)⟩
  · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

/-- `fast_lo` in `fastFrameP`. -/
theorem fastP_lo {Wn : Nat} {W : Addr} {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ fastFrameP Wn W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_using [h₂])⟩

/-- `fast_lo'` in `fastFrameP`. -/
theorem fastP_lo' {Wn : Nat} {W : Addr} {d k : Nat} (h₂ : 16 + d + k ≤ 128) :
    ∃ r' ∈ fastFrameP Wn W, Region.Sub ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 d, k⟩ r' := by
  rw [add_ofNat_assoc]; exact fastP_lo (by omega_using []) (by omega_using [h₂])

/-- A region at `W + d` from `W + 256` to `W + 320`, or above `W + 512`. -/
theorem fastP_hi {Wn : Nat} {W : Addr} {d k : Nat} (h : (256 ≤ d ∧ d + k ≤ 320) ∨ (512 ≤ d ∧ d + k ≤ Wn)) :
    ∃ r' ∈ fastFrameP Wn W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W h₁ (by omega_using [h₂])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Offset.sub W h₁ (by omega_using [h₂])⟩

/-! ## The path up to the branch on the tag -/

variable (c : Callees) (cl : Prog isa)

/-- `openRunWithP` up to the branch on the tag. -/
def openRunA : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.front
  (.seq (.block ([mov .x24 .x26, imm .x25 0] ++ absSeg2 16))
  (.seq cl
  (.seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ Impl.Gcm.AArch64.Pmull.loadRev Y .x20 16 ++
      [mov .x13 .x24, mov .x12 .x23]))
  (.seq Impl.AesGcm.AArch64.Fast.padMulT
  (.seq (.block (Impl.AesGcm.AArch64.Fast.lensTagAt uO))
  (.seq (ctrCall c)
  (.seq cmp
    (.block [imm .x27 1, .sub .x .x27 .x27 .x10]))))))))

/-- `openRunWithP` is `openRunA` then `omBWith (Tail.cryptAlT c)`. -/
theorem openRunWith_split :
    PEq (.seq (openRunA c cl) (omBWith (Impl.AesGcm.AArch64.Tail.cryptAlT c)))
      (Impl.AesGcm.AArch64.Fast.openRunWithP c cl) := by
  unfold openRunA omBWith Impl.AesGcm.AArch64.Fast.openRunWithP Impl.AesGcm.AArch64.Fast.oneCryptT
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
theorem openRunAX_ok {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {to : Bool} {O : Addr} {s₀ t : State} {ex : List Region}
    {I : Mem → Prop} (o : OpenInG Wn to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR Wn W] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = t.rd → s'.wr = t.wr → s'.sp = SP → Frame [workR Wn W] t.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (openRunA v.callees cl) t fun u =>
      (MidOG Wn to (fastFrame Wn W ++ ex) Ctx W SP D O Np A R 12 al n tl t u ∧ u.gpr .x26 = BitVec.ofNat 64 n) ∧
        I u.mem := by
  have L := o.lay
  obtain hle := tagLenOk_le hok
  obtain hnlt := (dataOk_of o.dat).lt
  have hRb := o.rounds
  have ddW := o.ddW
  have dcW := o.dcW
  obtain hJ : J0In Wn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t :=
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
  obtain he₃ := he₂.of_regs r₃
  obtain hdat₃ : DataOk Wn (W + BitVec.ofNat 64 16) W s₃ D n :=
    (dataOk_of o.dat).of_eq (by rw [r₃.rd, h₂.rd]) (by rw [r₃.wr, h₂.wr])
  generalize hx₁ : bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length) = x₁ at h₂
  obtain hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain hM : AbsMid Wn Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 H x₁ D n 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun r hr => r₃.others r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide), Nat.zero_le _, by rw [r₃.others _ (by decide), h₂.x23]; simp,
      by rw [x24₃, Nat.sub_zero], x25₃, hdat₃, by rw [r₃.mem]; exact h₂.hH, fun ha => by simpa [bytesAt] using ha,
      .inr (by omega_arith), Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  obtain FW : Frame [workR Wn W] t.mem s₆.mem := by
    obtain w : ∀ {r : Region}, Region.Sub r (workR Wn W) → ∃ r' ∈ [workR Wn W], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    obtain F2 := h₂.frame.sub fun r hr => w (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega))
    obtain F6 : Frame [workR Wn W] s₂.mem s₆.mem := by
      rw [← r₃.mem]
      refine h₆.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact w (stW (by decide))
      · exact w (stW (by decide))
      · exact w (Lay.wSub (by omega))
    exact F2.trans F6
  obtain rd₆' : s₆.rd = t.rd := by rw [rd₆, r₃.rd, h₂.rd]
  obtain wr₆' : s₆.wr = t.wr := by rw [wr₆, r₃.wr, h₂.wr]
  obtain exW : ∀ {R : Region}, Region.Sub R (workR Wn W) → ∀ r ∈ ex, R.Disjoint r :=
    fun hR r hr => (hexW r hr).sub_left hR
  obtain exS : ∀ {r : Region}, (∃ r' ∈ fastFrameP Wn W, Region.Sub r r') → ∃ r' ∈ fastFrameP Wn W ++ ex, Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_append_left _ h, hs⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2WithX_ok L (.inr rfl)
    (fun r hr => (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))) (exW (stW (by decide))) h₆
    (hgh s₆ h₆.call (stW (by decide)) (Lay.wSub (by omega)) rd₆' wr₆' h₆.env.sp FW
      (Offset.sub_base D (by omega_arith)))))
    fun s₇ ⟨⟨⟨h₇, hlt₇⟩, I₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * (n / 16) = j at h₇ hlt₇
  obtain hjn : j ≤ n := by omega_arith
  have he₇ := h₇.env
  obtain hab₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H x₁ := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁0, List.take_length, ← hx₁, ← h₂.y, r₃.mem]
    · rw [hx₁0, Proof.Gcm.whole_of_mod hx₁0, List.drop_length]; rfl
  obtain hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = ghash H (blocks (x₁ ++ bytesAt s₃.mem D j)) :=
    (h₇.abs hab₃).whole_eq (by rw [List.length_append, length_bytesAt]; omega_arith)
  obtain key₃ : KeyAt H s₃.mem W := by rw [r₃.mem]; exact h₂.key
  obtain key₇ : KeyAt H s₇.mem W := by
    refine key₃.frame h₇.frame fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 32) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    · exact exW (Lay.wSub (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)) r hr
  -- `H'` again, `Y`, and the last bytes.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (reload_ok (H := H) (by rw [he₇.x19]; exact he₇.perm.wR (by decide))
    (by rw [he₇.x19]; exact he₇.perm.wR (by decide)) (by rw [he₇.x19]) (by rw [he₇.x19]; exact key₇.2)
    key₇.1) fun s₈ ⟨hk₈, g₈, v₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain he₈ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₇.keep (fun r hr => g₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₈ rd₈ wr₈
  refine WP.mono (loadRev_ok Y .x20 16 s₈ (by decide) (by decide) (by rw [he₈.x20]; exact he₈.perm.stR (by decide)))
    fun s₉ ⟨l₉, o₉⟩ => ?_
  obtain he₉ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r _ => by rw [o₉.gpr]) o₉.sp o₉.rd o₉.wr
  obtain ⟨s₁₀, run₁₀, x13₁₀, x12₁₀, r₁₀, v₁₀⟩ : ∃ s₁₀, runBlock isa [mov .x13 .x24, mov .x12 .x23] s₉ = some s₁₀ ∧
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - j) ∧ s₁₀.gpr .x12 = D + BitVec.ofNat 64 j ∧
      Regs [.x13, .x12] s₉ s₁₀ ∧ s₁₀.v = s₉.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp [gpr_write, o₉.gpr, g₈ .x24 (by decide), h₇.x24]
    · simp [gpr_write, o₉.gpr, g₈ .x23 (by decide), h₇.x23]
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  obtain he₁₀ := he₉.of_regs r₁₀
  obtain hk₁₀ : HKey H s₁₀ :=
    hk₈.of_v (by rw [v₁₀, o₉.v C (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)]) (by rw [v₁₀, o₉.v _ (by decide)])
  obtain hy₁₀ : s₁₀.v Y = ext8 (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) := by
    rw [v₁₀, l₉, he₈.x20, m₈, rev64b_read]
  obtain rd₁₀ : s₁₀.rd = s₃.rd := by rw [r₁₀.rd, o₉.rd, rd₈, rd₇, rd₆]
  obtain wr₁₀ : s₁₀.wr = s₃.wr := by rw [r₁₀.wr, o₉.wr, wr₈, wr₇, wr₆]
  obtain hdj : DataOk Wn (W + BitVec.ofNat 64 16) W s₁₀ (D + BitVec.ofNat 64 j) (n - j) :=
    (hdat₃.drop hjn).of_eq rd₁₀ wr₁₀
  obtain x26₁₀ : s₁₀.gpr .x26 = BitVec.ofNat 64 n := by
    rw [r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  refine WP.seq (WP.mono (WP.with_rdwr (padMulT_ok hMK he₁₀ hk₁₀ hy₁₀ x12₁₀ x13₁₀ (by omega_arith) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by omega))) x26₁₀ hnlt
    (pad_big (hdat₃.of_eq rd₁₀ wr₁₀).rd hnlt (by congr 2; omega_arith) (by omega_arith))))
    fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
  obtain m₁₀ : s₁₀.mem = s₇.mem := by rw [r₁₀.mem, o₉.mem, m₈]
  -- What the path has written so far.
  obtain Fa : Frame (fastFrameP Wn W) t.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · exact fastP_lo (by decide) (by decide)
    · exact fastP_lo (by decide) (by decide)
    · exact fastP_hi (by omega)
    · exact fastP_hi (by have : Impl.AesGcm.AArch64.Fast.hO = 288 := rfl; omega)
  obtain Fb : Frame (fastFrameP Wn W ++ ex) s₂.mem s₇.mem := by
    rw [← r₃.mem]
    refine h₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact exS (fastP_lo' (by decide))
    · exact exS (fastP_lo' (by decide))
    · exact exS (fastP_hi (by omega))
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩
  obtain Fc : Frame (fastFrameP Wn W) s₇.mem s₁₁.mem := by
    rw [← m₁₀]
    refine f₁₁.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact fastP_lo (by decide) (by decide)
  obtain mx : ∀ {m m' : Mem}, Frame (fastFrameP Wn W) m m' → Frame (fastFrameP Wn W ++ ex) m m' :=
    fun h => h.mono fun r hr => List.mem_append_left _ hr
  obtain F₁₁ : Frame (fastFrameP Wn W ++ ex) t.mem s₁₁.mem := ((mx Fa).trans Fb).trans (mx Fc)
  obtain slot₁₁ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept F₁₁ (disj_ex (slots_fastFrameP W) (exW (Lay.wSub (by omega)))) h₁ h₂'
  -- The lengths block.
  unfold Impl.AesGcm.AArch64.Fast.lensTagAt
  rw [WP.seq_iff]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  obtain w₁ := he₁₁.perm.wW (show 96 + 8 ≤ 512 by decide)
  obtain w₂ := he₁₁.perm.wW (show 104 + 8 ≤ 512 by decide)
  obtain q₁ := he₁₁.perm.wR (show 224 + 8 ≤ 512 by decide)
  obtain x26₁₁ : s₁₁.gpr .x26 = BitVec.ofNat 64 n := by
    rw [og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  obtain ⟨s₁₂, run₁₂, m₁₂, og₁₂, sp₁₂, rd₁₂, wr₁₂, v₁₂⟩ : ∃ s₁₂, runBlock isa
      [.ldr .x .x10 .x19 alenO, .lsl .x .x9 .x10 3, .rev .x9 .x9, .str .x .x9 .x19 tO, .lsl .x .x9 .x26 3,
        .rev .x9 .x9, .str .x .x9 .x19 (tO + 8)] s₁₁ = some s₁₂ ∧
      s₁₂.mem = (s₁₁.mem.writeW (W + BitVec.ofNat 64 96) (AArch64.rev64 (BitVec.ofNat 64 al <<< 3))).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (AArch64.rev64 (BitVec.ofNat 64 n <<< 3)) ∧
      Others [.x9, .x10] s₁₁ s₁₂ ∧ s₁₂.sp = s₁₁.sp ∧ s₁₂.rd = s₁₁.rd ∧ s₁₂.wr = s₁₁.wr ∧
      s₁₂.v = s₁₁.v := by
    obtain e₁ : s₁₁.mem.read (W + 224#64) 8 = BitVec.ofNat 64 al := by
      rw [show s₁₁.mem.read (W + 224#64) 8 = s₁₁.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl,
        slot₁₁ 224 (by decide) (by decide), o.sL]
    refine ⟨_, by arun [he₁₁.x19, q₁, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc, gpr_write, ite_true, ite_false,
      reduceCtorEq, e₁, x26₁₁]
  refine WP.of_runBlock ⟨s₁₂, run₁₂, ?_⟩
  obtain he₁₂ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => og₁₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁₂ rd₁₂ wr₁₂
  obtain fT₁₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s₁₁.mem s₁₂.mem := by rw [m₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hT₁₂ : blockAt s₁₂.mem (s₁₂.gpr .x19 + BitVec.ofNat 64 tO) = ofBytes (lensBlock al n) := by
    rw [he₁₂.x19, show tO = 96 from rfl, blockAt, m₁₂, Proof.Cmac.bytesAt_store2, le8_lens, le8_lens,
      toNat_ofNat_of_lt (show al < 2 ^ 64 by omega_arith), toNat_ofNat_of_lt hnlt]
    rfl
  obtain hk₁₂ : HKey H s₁₂ := hk₁₁.of_v (by rw [v₁₂]) (by rw [v₁₂]) (by rw [v₁₂])
  obtain y₁₂ : s₁₂.v Y = ext8 (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
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
  obtain g₁₄ : s₁₄.gpr = s₁₂.gpr := by rw [o₁₄.gpr]; exact o₁₃.gpr
  rw [show s₁₃.gpr .x20 = W + BitVec.ofNat 64 16 by rw [o₁₃.gpr, he₁₂.x20]] at b₁₄ m₁₄
  obtain he₁₄ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ :=
    he₁₂.keep (fun r _ => by rw [g₁₄]) (by rw [o₁₄.sp, o₁₃.sp]) (by rw [o₁₄.rd, o₁₃.rd]) (by rw [o₁₄.wr, o₁₃.wr])
  obtain fY₁₄ : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s₁₂.mem s₁₄.mem := by
    rw [m₁₄, o₁₃.mem]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain x22₁₄ : s₁₄.gpr .x22 = BitVec.ofNat 64 R := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x22 (by decide), h₂.x22, o.x22]
  -- The tag, to `W + uO`.
  refine WP.mono (WP.with_rdwr (tagSeg_ok L (o := uO) (.inr rfl) he₁₄ (fun _ _ => rfl : Kept s₁₄.gpr s₁₄) x22₁₄ hRb))
    fun s₁₆ ⟨h₁₆, rd₁₆, wr₁₆⟩ => ?_
  refine WP.seq (WP.mono (WP.with_rdwr (tagCall_ok L v (.inr rfl) h₁₆)) fun s₁₇ ⟨h₁₇, rd₁₇, wr₁₇⟩ => ?_)
  obtain Fd : Frame (fastFrameP Wn W) s₁₁.mem s₁₄.mem := by
    refine (fT₁₂.sub fun r hr => ?_).trans (fY₁₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact fastP_lo (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact fastP_lo' (by decide)
  obtain F₁₄ : Frame (fastFrameP Wn W ++ ex) t.mem s₁₄.mem := F₁₁.trans (mx Fd)
  obtain Fg : Frame (fastFrameP Wn W) s₁₄.mem s₁₇.mem := by
    refine h₁₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fastP_lo (by decide) (by decide)
    · exact fastP_lo (by decide) (by decide)
    · exact fastP_lo (by decide) (by decide)
    · exact fastP_hi (by omega)
  obtain F₁₇ : Frame (fastFrameP Wn W ++ ex) t.mem s₁₇.mem := F₁₄.trans (mx Fg)
  -- The comparison, the tag length still in `x28`.
  obtain x28₁₄ : s₁₄.gpr .x28 = BitVec.ofNat 64 tl := by
    rw [g₁₄, og₁₂ _ (by decide), og₁₁ _ (by decide), r₁₀.others _ (by decide), o₉.gpr,
      g₈ _ (by decide), h₇.kept .x28 (by decide), h₂.x28, o.x28]
  obtain x28₁₈ : s₁₇.gpr .x28 = BitVec.ofNat 64 tl := by rw [h₁₇.kept .x28 (by decide), x28₁₄]
  have he₁₈ := h₁₇.env
  refine WP.seq (WP.mono (WP.with_rdwr (cmp_ok L he₁₈ (fun _ _ => rfl : Kept s₁₇.gpr s₁₇) x28₁₈ hle))
    fun s₁₉ ⟨⟨x10₁₉, he₁₉, hk₁₉, _, f₁₉⟩, rd₁₉, wr₁₉⟩ => ?_)
  refine WP.mono (okBit_ok (b := decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl =
      bytesAt s₁₇.mem W tl)) (by rw [x10₁₉]; simp only [decide_eq_true_eq]))
    fun s₂₀ ⟨x27₂₀, r₂₀⟩ => ?_
  obtain he₂₀ := he₁₉.of_regs r₂₀
  obtain Fe : Frame (fastFrameP Wn W) s₁₇.mem s₁₉.mem := by
    refine f₁₉.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact fastP_hi (by omega)
  obtain F₂₀ : Frame (fastFrameP Wn W ++ ex) t.mem s₂₀.mem := by rw [r₂₀.mem]; exact F₁₇.trans (mx Fe)
  obtain I₂₀ : I s₂₀.mem := by
    rw [r₂₀.mem]
    exact hI I₇ ((((Fc.trans Fd).trans Fg).trans Fe).sub fun r hr =>
      ⟨workR Wn W, List.mem_singleton_self _, fastFrameP_work W (hWn := hWn) r hr⟩)
  -- What the frames keep.
  obtain dCf : ∀ r ∈ fastFrameP Wn W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (fastFrameP_work W) dcW
  obtain dDf : ∀ r ∈ fastFrameP Wn W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (fastFrameP_work W) ddW
  obtain hc₁₄ : ciphOf s₁₄.mem Ctx R = ciphOf t.mem Ctx R := ciph_frame F₁₄ (disj_ex dCf hexC) hRb
  obtain hD₃ : bytesAt s₃.mem D n = bytesAt t.mem D n := by rw [r₃.mem]; exact bytesAt_frame Fa dDf (by omega_arith)
  obtain ht₁₀ : bytesAt s₁₀.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [m₁₀, bytesAt_frame h₇.frame (disj_absEx (data_absFrame L (.inr rfl) (hdat₃.drop hjn))
      fun r hr => (hexD r hr).sub_left (Offset.sub_base D (by omega_arith))) (by omega_arith)]
  obtain hsplit : bytesAt s₃.mem D n = bytesAt s₃.mem D j ++ bytesAt s₃.mem (D + BitVec.ofNat 64 j) (n - j) := by
    rw [← bytesAt_add, Nat.add_sub_cancel' hjn]
  -- `J₀`, still at the state, and the first counter block.
  obtain dT : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st0_w L ⟨by decide, by have := L.hWn; omega⟩
  obtain hJ₁₄ : blockAt s₁₄.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H (bytesAt t.mem Np 12) := by
    obtain e₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16) = blockAt s₃.mem (W + BitVec.ofNat 64 16) :=
      blockAt_frame h₇.frame fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | rfl | hr
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact st0_w L ⟨by decide, by have := L.hWn; omega⟩
        · exact exW (Lay.wSub (by omega)) r hr
    rw [blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st0_disj L (by decide) (by decide)),
      blockAt_frame fT₁₂ dT, blockAt_frame f₁₁ dT, m₁₀, e₇, r₃.mem, h₂.j0]
  obtain hcb : blockAt s₂₀.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      inc32 (Spec.Gcm.j0 H (bytesAt t.mem Np 12)) := by
    obtain d₄₈ : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)],
        (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by omega⟩
    rw [r₂₀.mem, blockAt_frame f₁₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact st_wpart L (by decide) ⟨by decide, by omega⟩),
      blockAt_frame h₁₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using L.st_st (a := 48) (n := 16) (d := 0) (k := 32) (.inr (by decide)) (by decide) (by decide)
        · exact st_wpart L (by decide) ⟨by decide, by omega⟩
        · exact st_wpart L (by decide) ⟨by decide, by omega⟩
        · exact st_wpart L (by decide) ⟨by decide, by omega⟩),
      blockAt_frame fY₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.st_st (a := 48) (n := 16) (d := 16) (k := 16) (.inr (by decide)) (by decide) (by decide)),
      blockAt_frame fT₁₂ d₄₈, blockAt_frame f₁₁ d₄₈, m₁₀,
      blockAt_frame h₇.frame (disj_absEx (fun r hr => (ctr_absFrame L r hr).sub_left (Region.sub_prefix (by decide)))
        (exW (stW (by decide)))),
      r₃.mem, h₂.cb]
  -- The tag.
  obtain hT : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.toBytes (ghashFrom H
      (ghash H (blocks (Proof.Gcm.padded (bytesAt t.mem A al) (bytesAt t.mem D n))))
      [ofBytes (lensBlock (bytesAt t.mem A al).length (bytesAt t.mem D n).length)] ^^^
      ciphOf t.mem Ctx R (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) := by
    rw [h₁₇.out, b₁₄, hJ₁₄, hc₁₄, hY₇, ht₁₀, ← hx₁, ← hD₃, hsplit,
      ghash_padded _ _ _ _ (by rw [length_bytesAt]; omega_arith) (by rw [length_bytesAt]; omega_arith), length_bytesAt,
      List.length_append, length_bytesAt, length_bytesAt, Nat.add_sub_cancel' hjn]
    rfl
  obtain hT' : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H
      (bytesAt t.mem Np 12) (bytesAt t.mem A al) (bytesAt t.mem D n) := by
    rw [hT, Proof.Gcm.fullTag_eq]
  obtain hW₁₈ : bytesAt s₁₇.mem W tl = bytesAt t.mem W tl := by
    refine bytesAt_frame F₁₇ (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | hr
    · exact (Offset.disjoint_base W (show tl ≤ 16 by omega_arith) (by decide)).symm
    · exact (Offset.disjoint_base W (show tl ≤ 256 by omega_arith) (by decide)).symm
    · exact (Offset.disjoint_base W (show tl ≤ 512 by omega_arith) (by omega)).symm
    · exact exW (Region.sub_prefix (by omega_arith)) r hr
  obtain hb : (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) ↔
      (Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
        (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl := by
    rw [← bytesAt_take _ _ hle, hT', hW₁₈]
  generalize hBd : decide (bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) tl = bytesAt s₁₇.mem W tl) = B at x27₂₀
  obtain hBeq : decide ((Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H (bytesAt t.mem Np 12)
      (bytesAt t.mem A al) (bytesAt t.mem D n)).take tl = bytesAt t.mem W tl) = B := by
    rw [← hBd]; exact decide_eq_decide.mpr hb.symm
  obtain x22₂₀ : s₂₀.gpr .x22 = BitVec.ofNat 64 R := by
    rw [r₂₀.others _ (by decide), hk₁₉ .x22 (by decide), h₁₇.kept .x22 (by decide), x22₁₄]
  obtain x26₂₀ : s₂₀.gpr .x26 = BitVec.ofNat 64 n := by
    rw [r₂₀.others _ (by decide), hk₁₉ .x26 (by decide), h₁₇.kept .x26 (by decide), g₁₄, og₁₂ _ (by decide),
      x26₁₁]
  subst hH
  obtain rd₂₀ : s₂₀.rd = t.rd := by rw [r₂₀.rd, rd₁₉, rd₁₇, rd₁₆, o₁₄.rd, o₁₃.rd, rd₁₂, rd₁₁, rd₁₀, r₃.rd, h₂.rd]
  obtain wr₂₀ : s₂₀.wr = t.wr := by rw [r₂₀.wr, wr₁₉, wr₁₇, wr₁₆, o₁₄.wr, o₁₃.wr, wr₁₂, wr₁₁, wr₁₀, r₃.wr, h₂.wr]
  obtain sO₂₀ : s₂₀.mem.readW (W + BitVec.ofNat 64 320) 64 = t.mem.readW (W + BitVec.ofNat 64 320) 64 :=
    F₂₀.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _)
      (disj_ex (dst_fastFrameP W) (exW (Lay.wSub (by omega)))) (by decide)
  refine ⟨⟨⟨he₂₀, F₂₀.sub fastFrameP_sub, x22₂₀, by rw [x27₂₀, hBeq], data_of_eq o.dat rd₂₀ wr₂₀,
    by rw [slot_kept F₂₀ (disj_ex (slots_fastFrameP W) (exW (Lay.wSub (by omega)))) (by decide) (by decide), o.sD],
    by rw [slot_kept F₂₀ (disj_ex (slots_fastFrameP W) (exW (Lay.wSub (by omega)))) (by decide) (by decide), o.sN],
    hcb, outG_of_eq o.out rd₂₀ wr₂₀ sO₂₀⟩, x26₂₀⟩, I₂₀⟩

/-- A frame of the working space is one of it and the text. -/
theorem frame_wD {Wn : Nat} {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame [workR Wn W] m m') :
    Frame [workR Wn W, ⟨D, n⟩] m m' :=
  h.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..

theorem openRunA_ok {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {s₀ t : State}
    (o : OpenIn Wn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hok : Spec.Gcm.tagLenOk tl = true)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = t.rd → s'.wr = t.wr → s'.sp = SP → Frame [workR Wn W, ⟨D, n⟩] t.mem s'.mem →
      WP isa cl s' (GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb)) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (openRunA v.callees cl) t fun u =>
      MidO Wn (fastFrame Wn W) Ctx W SP D Np A R 12 al n tl t u ∧ u.gpr .x26 = BitVec.ofNat 64 n :=
  WP.mono (openRunAX_ok cl v hMK (ex := []) (I := fun _ => True) o h4 h5 h6 h7 hal hok (by simp) (by simp)
    (by simp) (fun _ _ => trivial) fun s' _ _ _ _ hc sY sS hrd hwr hsp hf _ =>
      WP.mono (hgh s' hc sY sS hrd hwr hsp (frame_wD hf)) fun _ g => ⟨g, trivial⟩) fun _ q => q.1

end

/-- `omBX_ok`, decrypting with `Tail.cryptAlT`, for a text of `x26` bytes. -/
theorem omBXT_ok {Wn : Nat} (v : GcmImpl) {Ctx W SP D Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidO Wn fr Ctx W SP D Np A R nl al n tl s s₇)
    (h26 : s₇.gpr .x26 = BitVec.ofNat 64 n) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (omBWith (Impl.AesGcm.AArch64.Tail.cryptAlT v.callees)) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ Frame (⟨D, n⟩ :: fr ++ crFrame Wn (W + BitVec.ofNat 64 16) W D n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem D n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else bytesAt s.mem D n) ∧ Frame (crFrame Wn (W + BitVec.ofNat 64 16) W D n) s₇.mem s'.mem :=
  omBXWith_ok _ hR mo dD dC fun {_} h e26 hwr icb => cryptAlT_ok L v (icb := icb) h rfl (by rw [e26, h26])
    mo.data.ok.lt (tail_big (by rw [hwr]; exact mo.data.wr) mo.data.ok.lt (by simp) (Nat.zero_add n))

/-! ## In place or out of place -/

/-- The counter mode of the path for TLS records after the branch on the tag:
`Tail.cryptAlT` in place, and out of place `cryptAlG c true` (`oneCryptTG`). -/
def crT (c : Callees) (to : Bool) : Prog isa :=
  bif to then cryptAlG c true else Impl.AesGcm.AArch64.Tail.cryptAlT c

/-- `openRunWithPG to` is `openRunA` then `omBWithG to (crT c to)`. -/
theorem openRunWithG_split (to : Bool) :
    PEq (.seq (openRunA c cl) (omBWithG to (crT c to)))
      (Impl.AesGcm.AArch64.Fast.openRunWithPG c to cl) := by
  obtain e : omBWithG to (crT c to) = .seq (.ite (.zero .x .x27) (wipeG to)
      (Impl.AesGcm.AArch64.Fast.oneCryptTG c to)) (.block [mov .x0 .x27]) := by
    cases to
    · simp only [omBWithG, crT, Impl.AesGcm.AArch64.Fast.oneCryptTG, Impl.AesGcm.AArch64.Fast.oneCryptT,
        Bool.cond_false, List.append_nil]
    · rfl
  rw [e]
  unfold openRunA Impl.AesGcm.AArch64.Fast.openRunWithPG
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

/-- `omBXWithG_ok` with `crT`, for a text of `x26` bytes. -/
theorem omBXTG_ok {Wn : Nat} (v : GcmImpl) (to : Bool) {Ctx W SP D O Np A : Addr} {R nl al n tl : Nat}
    (L : Lay Wn Ctx (W + BitVec.ofNat 64 16) W) {fr : List Region} {s s₇ : State} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (mo : MidOG Wn to fr Ctx W SP D O Np A R nl al n tl s s₇)
    (h26 : s₇.gpr .x26 = BitVec.ofNat 64 n) (dD : ∀ r ∈ fr, (⟨D, n⟩ : Region).Disjoint r)
    (dC : ∀ r ∈ fr, (⟨Ctx, 256⟩ : Region).Disjoint r) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (omBWithG to (crT v.callees to)) s₇ fun s' =>
      let ciph := ciphOf s.mem Ctx R
      let H := blockAt s.mem (Ctx + BitVec.ofNat 64 240)
      let T := Spec.Gcm.fullTag ciph H (bytesAt s.mem Np nl) (bytesAt s.mem A al) (bytesAt s.mem D n)
      let b := decide (T.take tl = bytesAt s.mem W tl)
      (Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s' ∧
        Frame (⟨O, n⟩ :: fr ++ crFrame Wn (W + BitVec.ofNat 64 16) W O n) s.mem s'.mem ∧
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      bytesAt s'.mem O n = if b then gctr ciph (inc32 (Spec.Gcm.j0 H (bytesAt s.mem Np nl))) (bytesAt s.mem D n)
        else cond to (List.replicate n 0) (bytesAt s.mem D n)) ∧
      Frame (crFrame Wn (W + BitVec.ofNat 64 16) W O n) s₇.mem s'.mem := by
  obtain hWn := L.hWn
  refine omBXWithG_ok to _ hR mo dD dC fun {_} h e26 hwr icb => ?_
  cases to
  · have e : O = D := mo.out
    subst e
    exact cryptAlT_ok L v (icb := icb) h rfl (by rw [e26 rfl, h26]) mo.data.ok.lt
      (tail_big (by rw [hwr]; exact mo.data.wr) mo.data.ok.lt (by simp) (Nat.zero_add n))
  · exact cryptAlG_ok L v true (icb := icb) h rfl

/-- `openRunWithPG to`, once the received tag is at `W`, for a `cl` that
hashes as `vg_ghash` called with memory changed since the entry `s₀` only in
the working space, which may also write `ex` and establish `I`, which what
the rest writes keeps (`hI`): out of place, the output zeroed if the tag is
wrong. -/
theorem openRunWithG_postX {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {to : Bool} {Ctx W SP Np A D O Tg : Addr}
    {R nl al n tl : Nat} {s₀ t : State} {ex : List Region} {I : Mem → Prop}
    (o : OpenInG Wn to Ctx W SP Np A D O Tg R nl al n tl s₀ t) (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR Wn W, ⟨O, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR Wn W] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithPG v.callees to cl) t fun u =>
      OpenPostG Wn Ctx W SP Np A O Tg R nl al n tl (bytesAt s₀.mem D n)
        (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀ u ∧ I u.mem := by
  subst h12
  have L := o.lay
  have ow := o.outW
  obtain F₀ : Frame [workR Wn W] s₀.mem t.mem :=
    o.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entryFr_work to W (hWn := hWn) r hr⟩
  obtain dD : ∀ r ∈ fastFrame Wn W ++ ex, (⟨D, n⟩ : Region).Disjoint r :=
    disj_ex (keep_of_sub (fastFrame_work W) o.ddW) hexD
  obtain dC : ∀ r ∈ fastFrame Wn W ++ ex, (⟨Ctx, 256⟩ : Region).Disjoint r :=
    disj_ex (keep_of_sub (fastFrame_work W) o.dcW) hexC
  refine (openRunWithG_split v.callees cl to).symm.wp (WP.seq (WP.mono (openRunAX_ok cl v hMK o h4 h5 h6 h7 hal
    hok hexW hexD hexC (fun hi f => hI hi (f.sub fun r hr => ⟨workR Wn W, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩))
    fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd => hgh s' hc sY sS (hrd.trans o.rd₀) (hwr.trans o.wr₀) hsp
      (F₀.trans hf) hd)
    fun _ ⟨⟨mo, x26⟩, i₇⟩ => WP.mono (omBXTG_ok v to L o.rounds mo x26 dD dC) fun s₄ ⟨hpost, f₈⟩ => ?_))
  obtain I₄ : I s₄.mem := hI i₇ (f₈.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by omega)⟩)
  obtain ⟨he₄, F₄, x0₄, d₄⟩ := hpost
  refine ⟨⟨he₄, o.sv.frame F₄ fun r hr => ?_, ?_⟩, I₄⟩
  · rcases List.mem_cons.mp hr with h | hr
    · subst h; exact (ow.ok.w.sub_right (Lay.wSub (by omega))).symm
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact saved_fastFrame W (hWn := hWn) r hr
      · exact (hexW r hr).sub_left (Lay.wSub (by omega))
    · exact saved_crFrame L ow r hr
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

/-- `openRunWithG_postX` without an invariant. -/
theorem openRunWithG_postE {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {to : Bool} {Ctx W SP Np A D O Tg : Addr}
    {R nl al n tl : Nat} {s₀ t : State} {ex : List Region}
    (o : OpenInG Wn to Ctx W SP Np A D O Tg R nl al n tl s₀ t) (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR Wn W] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithPG v.callees to cl) t
      (OpenPostG Wn Ctx W SP Np A O Tg R nl al n tl (bytesAt s₀.mem D n)
        (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) :=
  WP.mono (openRunWithG_postX cl v hMK (I := fun _ => True) o h12 h4 h5 h6 h7 hal hT₃ hok hexW hexD hexC
    (fun _ _ => trivial) fun s' _ _ _ _ hc sY sS hr hw hsp hf hd =>
      WP.mono (hgh s' hc sY sS hr hw hsp hf hd) fun _ g => ⟨g, trivial⟩) fun _ q => q.1

/-! ## `open` -/

/-- `openRunWith_post` for a call that may also write `ex` and establish
`I`, which what the rest writes keeps (`hI`). -/
theorem openRunWith_postX {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop} (o : OpenIn Wn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR Wn W, ⟨D, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR Wn W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t fun u =>
      OpenPost Wn Ctx W SP Np A D Tg R nl al n tl s₀ u ∧ I u.mem :=
  openRunWithG_postX cl v hMK o h12 h4 h5 h6 h7 hal hT₃ hok hexW hexD hexC hI
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd => hgh s' hc sY sS hr hw hsp (frame_wD hf) hd

/-- `openRunWith_postX` without an invariant. -/
theorem openRunWith_postE {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} (o : OpenIn Wn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR Wn W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR Wn W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t (OpenPost Wn Ctx W SP Np A D Tg R nl al n tl s₀) :=
  openRunWithG_postE cl v hMK o h12 h4 h5 h6 h7 hal hT₃ hok hexW hexD hexC
    fun s' _ _ _ _ hc sY sS hr hw hsp hf hd => hgh s' hc sY sS hr hw hsp (frame_wD hf) hd

/-- `openRunWithP`, once the received tag is at `W`, for a `cl` that hashes as
`vg_ghash` called with memory changed since the entry `s₀` only in the
working space and the text. -/
theorem openRunWith_post {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} (o : OpenIn Wn Ctx W SP Np A D Tg R nl al n tl s₀ t) (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR Wn W, ⟨D, n⟩] s₀.mem s'.mem →
      WP isa cl s' (GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb)) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (Impl.AesGcm.AArch64.Fast.openRunWithP v.callees cl) t (OpenPost Wn Ctx W SP Np A D Tg R nl al n tl s₀) :=
  openRunWith_postE cl v hMK (ex := []) o h12 h4 h5 h6 h7 hal hT₃ hok (by simp) (by simp) (by simp)
    fun s' _ _ _ _ hc sY sS hr hw hsp hf _ => hgh s' hc sY sS hr hw hsp hf

/-- `vg_aes_gcm_open` with the path for TLS records, `work` the stack
argument `w`, and its whole blocks hashed by `cl`, which hashes as a call of
`vg_ghash` when run with memory changed since the entry only in the working
space and the text. -/
theorem openWithE_wp {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW (Wn := Wn) w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR Wn (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR Wn (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWithE v.callees (8 * w) cl) s fun s' =>
      GprAbi s s' ∧ (openAArch64 Wn).post s s' := by
  unfold Impl.AesGcm.AArch64.Fast.openWithE
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  obtain o₂ := o₁.of_regs r₂
  obtain x12₂ : s₂.gpr .x12 = stackArg s 0 := by rw [r₂.others _ (by decide), x12₁]
  obtain hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
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
theorem openWith_wp {Wn : Nat} (gh : Fn) (v : GcmImpl) (hMK : MulKey) {extra : List Region} {s : State}
    (hs : openPreX (Wn := Wn) extra s)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg s 2)) → Region.Sub ⟨S, 256⟩ (workR Wn (stackArg s 2)) →
      s'.rd = s.rd → s'.wr = s.wr → Frame [workR Wn (stackArg s 2), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa (.call gh.name gh.code) s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWith v.callees gh) s fun s' => GprAbi s s' ∧ (openAArch64 Wn).post s s' :=
  openWithE_wp (w := 2) (.call gh.name gh.code) v hMK (.inl rfl) (openPreX_W hs)
    fun s' _ _ _ _ c y z r w _ f => hgh s' c y z r w f

/-! ## `vg_aes_gcm_open_to` -/

/-- `vg_aes_gcm_open_to` with the path for TLS records (`openWithEG c true
w`), `work` the stack argument `w`, and its whole blocks hashed by `cl`,
which hashes as a call of `vg_ghash` when run with memory changed since the
entry only in the working space. -/
theorem openToWithE_wp {Wn : Nat} (v : GcmImpl) (hMK : MulKey) {w : Nat} (hw : w = 4 ∨ w = 5)
    {extra extraW : List Region} {s : State} (hs : openToPreXW (Wn := Wn) w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR Wn (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [workR Wn (stackArg s w)] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb)) (hv : v.ctr.scratch ≤ Wn - 512 := by assumption) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    WP isa (Impl.AesGcm.AArch64.Fast.openWithEG v.callees true w cl) s fun s' =>
      GprAbi s s' ∧ openToPostOf s s' := by
  unfold Impl.AesGcm.AArch64.Fast.openWithEG
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega_using [hw]) hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  obtain o₂ := o₁.of_regs r₂
  obtain x12₂ : s₂.gpr .x12 = stackArg s 2 := by rw [r₂.others _ (by decide), x12₁]
  obtain hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  obtain post : ∀ {s' : State}, (GprAbi s s' ∧
      match openToRes s with
      | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (stackArg s 0) (s.gpr .x7).toNat = pt
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧
          bytesAt s'.mem (stackArg s 0) (s.gpr .x7).toNat = List.replicate (s.gpr .x7).toNat 0) →
      GprAbi s s' ∧ openToPostOf s s' := fun h => h
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    unfold Impl.AesGcm.AArch64.Fast.openFastPG
    refine WP.mono (openRestWithFl_wp (fl := .seq (.block [imm .x0 0]) (wipeG true))
      (C := bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (F := fun m => bytesAt m (stackArg s 0) (s.gpr .x7).toNat = List.replicate (s.gpr .x7).toNat 0)
      o₂ x12₂ (fun o' _ _ hok => failTo_ok o' hok) fun o' hT hok hx' => ?_) fun _ h => post h
    have hx (r : Reg) (hr : r ∈ [Reg.x4, .x5, .x6, .x7]) := (hx' r hr).trans (hx₂ r hr)
    exact openRunWithG_postE cl v hMK (ex := []) o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
      (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok (by simp) (by simp) (by simp)
      fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh s' c sY sS hr hw hsp hf
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    unfold openRestG
    exact WP.mono (openRestWithFl_wp (fl := .seq (.block [imm .x0 0]) (wipeG true))
      (m := openMainG v.callees true) (C := bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (F := fun m => bytesAt m (stackArg s 0) (s.gpr .x7).toNat = List.replicate (s.gpr .x7).toNat 0)
      o₂ x12₂ (fun o' _ _ hok => failTo_ok o' hok) fun o' hT hok _ => openMainG_post v true o' hT hok)
      fun _ h => post h

end VG.Proof.AesGcm.AArch64.Fast
