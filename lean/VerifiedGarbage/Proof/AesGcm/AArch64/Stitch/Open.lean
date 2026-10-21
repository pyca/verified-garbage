module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenB
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.PadT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on AArch64, interleaved: `open` up to the branch on the tag

Untrusted: everything here is checked by Lean. `openRunAS` does what
`openRunA` does (`Fast/Open.lean`), with the first `128 ⌊n / 128⌋` bytes of
the ciphertext decrypted and hashed by the interleaved loop (`stitchD_ok`),
for a `tb` that writes the table of keys (`htb`) and a `ghPart` that is
GHASH (`Gh8Ok`), the first counter block kept at `W + cbO`: it leaves `MidS`.
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
open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok)

section
variable (cl : Prog isa) {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}

/-- `openRunAX_ok` for `openRunAS`. -/
theorem openRunASX_ok (v : GcmImpl) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {s₀ t : State} {ex : List Region}
    {I : Mem → Prop}
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
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = t.rd → u.wr = t.wr →
      Frame [workR W, ⟨D, n⟩] t.mem u.mem → KeyAt (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) u.mem W →
      WP isa (.block tb) u fun t' => TblOk t'.mem W (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) ∧
        Frame [Stitch.tblR W] u.mem t'.mem ∧ (∀ r, r ≠ .x5 → t'.gpr r = u.gpr r) ∧
        t'.sp = u.sp ∧ t'.rd = u.rd ∧ t'.wr = u.wr) :
    WP isa (openRunAS v.callees cl tb) t fun u =>
      MidS (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) Ctx W SP D Np A R 12 al n tl (Stitch.pre n) t u ∧
        I u.mem := by
  have L := o.lay
  have hle := tagLenOk_le hok
  have hnlt := o.dat.ok.lt
  have hRb := o.rounds
  have ddW := o.ddW
  have dcW := o.dcW
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (blockAt t.mem (Ctx + BitVec.ofNat 64 240)) Np 12 t :=
    ⟨o.env, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, rfl⟩
  generalize hH : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H at hJ htb
  unfold openRunAS
  refine WP.seq (WP.mono (front_ok L hMK hJ o.aad hal h4 h5 h6 h7) fun s₂ h₂ => ?_)
  have he₂ := h₂.env
  have y₂ := h₂.y
  have cb₂ := h₂.cb
  have j0₂ := h₂.j0
  generalize hJ0 : Spec.Gcm.j0 H (bytesAt t.mem Np 12) = J0 at cb₂ j0₂
  generalize hx₁ : bytesAt t.mem A al ++ zeros (padLen (bytesAt t.mem A al).length) = x₁ at y₂
  have hx₁0 : x₁.length % 16 = 0 := by
    rw [← hx₁, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hwrap := o.dat.ok.wrap
  have wE : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
    fun h => ⟨_, List.mem_cons_self .., h⟩
  have dD : ∀ {r : Region}, Region.Sub r ⟨D, n⟩ → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), h⟩
  -- The first counter block, kept for a wrong tag.
  rw [WP.seq_iff]
  obtain ⟨s₂c, run₂c, m₂c, g₂c, sp₂c, rd₂c, wr₂c⟩ := saveCb_ok he₂
  refine WP.of_runBlock ⟨s₂c, run₂c, ?_⟩
  have he₂c : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂c := he₂.keep (fun r _ => by rw [g₂c]) sp₂c rd₂c wr₂c
  have fcb : Frame [⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩] s₂.mem s₂c.mem := by
    rw [m₂c]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dcbR : ∀ {R : Region}, (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint R →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region)], R.Disjoint r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.symm
  have hcbs₂ : blockAt s₂c.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) = inc32 J0 := by
    rw [m₂c, blockAt_copy, cb₂]
  have F₂c : Frame [workR W, ⟨D, n⟩] t.mem s₂c.mem := by
    have F2 := h₂.frame.sub fun r hr => wE (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl <;> exact Lay.wSub (by decide))
    exact F2.trans (fcb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact wE (Lay.wSub (by decide)))
  have hdat₂ : DataW Ctx (W + BitVec.ofNat 64 16) W s₂c D n :=
    o.dat.of_eq (by rw [rd₂c, h₂.rd]) (by rw [wr₂c, h₂.wr])
  have cbD : (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint ⟨D, n⟩ :=
    (ddW.sub_right (Lay.wSub (by decide))).symm
  -- The first `P` bytes, by the interleaved loop.
  have hS : Stitch.SIn Ctx (W + BitVec.ofNat 64 16) W SP H x₁ (inc32 J0) R D n s₂c :=
    ⟨he₂c, by rw [g₂c, h₂.x22, o.x22], hRb, by rw [g₂c, h₂.x23], by rw [g₂c, h₂.x26], hdat₂,
      by rw [blockAt_frame fcb (dcbR ((L.cw'.sub_left (Lay.ctxSub (by decide))).sub_right
        (Lay.wSub (by decide))).symm), h₂.hH],
      by rw [blockAt_frame fcb (dcbR (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm), cb₂],
      by rw [blockAt_frame fcb (dcbR (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm), y₂],
      hx₁0⟩
  have key₂c : KeyAt H s₂c.mem W := h₂.key.frame fcb (dcbR (L.w_w (.inr (by decide)) (by decide) (by decide)))
  have hTb : Stitch.TbOk Ctx (W + BitVec.ofNat 64 16) W SP H tb s₂c :=
    fun u heu hm hrd hwr _ => htb u heu (by rw [hrd, rd₂c, h₂.rd]) (by rw [hwr, wr₂c, h₂.wr])
      (by rw [hm]; exact F₂c) (by rw [hm]; exact key₂c)
  refine WP.seq (WP.mono (Stitch.stitchD_ok L gh hTb hS) fun s₂' hm₂ => ?_)
  have y₂' := hm₂.y
  have ctr₂ := hm₂.ctr
  have dat₂ := hm₂.data
  generalize hP : Stitch.pre n = P at y₂' ctr₂ dat₂
  have hPn : P ≤ n := hP ▸ Nat.mul_div_le n 128
  have hP16 : P % 16 = 0 := by rw [← hP]; simp only [Stitch.pre]; omega
  generalize hD' : D + BitVec.ofNat 64 P = D'
  have hsubD : Region.Sub ⟨D', n - P⟩ ⟨D, n⟩ := hD' ▸ Offset.sub_base D (by omega)
  have hsubP' : Region.Sub ⟨D, Stitch.pre n⟩ ⟨D, n⟩ := Region.sub_prefix (Nat.mul_div_le n 128)
  have g₂' : ∀ r, r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x13, .x14] → s₂'.gpr r = s₂.gpr r :=
    fun r hr => by rw [hm₂.gpr r hr, g₂c]
  -- The rest's whole blocks, by `gh`.
  rw [WP.seq_iff, WP.block_append_iff]
  obtain ⟨s₃, run₃, x23₃, x24₃, x25₃, r₃⟩ := Stitch.afterD_ok (u := s₂') (D := D) (n := n)
    (by rw [g₂' _ (by decide), h₂.x23]) (by rw [g₂' _ (by decide), h₂.x26]) hnlt
  rw [hP, hD'] at x23₃
  rw [hP] at x24₃
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ := hm₂.env.of_regs r₃
  have hdat₃ : DataOk (W + BitVec.ofNat 64 16) W s₃ D' (n - P) :=
    hD' ▸ (o.dat.ok.drop hPn).of_eq (by rw [r₃.rd, hm₂.rd, rd₂c, h₂.rd]) (by rw [r₃.wr, hm₂.wr, wr₂c, h₂.wr])
  have dKS : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W D n, (keyR W).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (L.st_w (a := 16) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact (L.st_w (a := 48) (n := 16) (by decide) (.inr ⟨by decide, by decide⟩)).symm
    · exact ((ddW.sub_left hsubP').sub_right (Lay.wSub (by decide))).symm
    · exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
  have cS : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact o.dat.ctx.sub_right hsubP'
    · exact L.cw'.sub_right (Lay.wSub (by decide))
  have hH₃ : blockAt s₃.mem (Ctx + BitVec.ofNat 64 240) = H := by
    rw [r₃.mem, blockAt_frame hm₂.frame fun r hr => (cS r hr).sub_left (Lay.ctxSub (by decide))]
    exact hS.hH
  generalize hC₀ : bytesAt s₂c.mem D P = C₀ at dat₂ y₂'
  have hC₀l : C₀.length = P := by rw [← hC₀, length_bytesAt]
  have hM : AbsMid Ctx (W + BitVec.ofNat 64 16) W SP s₂.gpr 16 H (x₁ ++ C₀) D' (n - P) 0 s₃.mem 0 s₃ :=
    ⟨he₃, fun r hr => by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [r₃.others _ (by decide), g₂' _ (by decide)],
      Nat.zero_le _, by rw [x23₃]; simp,
      by rw [x24₃, Nat.sub_zero], by rw [x25₃], hdat₃, hH₃, fun ha => by simpa [bytesAt] using ha,
      .inr (by rw [List.length_append, hC₀l]; omega), Frame.refl _ _⟩
  refine WP.mono (WP.with_rdwr (absSeg2_ok L (.inr rfl) hM)) fun s₆ ⟨h₆, rd₆, wr₆⟩ => ?_
  have FW : Frame [workR W, ⟨D, n⟩] t.mem s₆.mem := by
    have F3 : Frame [workR W, ⟨D, n⟩] s₂c.mem s₃.mem := by
      rw [r₃.mem]
      refine hm₂.frame.sub fun r hr => ?_
      simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact wE (stW (by decide))
      · exact wE (stW (by decide))
      · exact dD hsubP'
      · exact wE (Lay.wSub (by decide))
    have F6 : Frame [workR W, ⟨D, n⟩] s₃.mem s₆.mem := by
      refine h₆.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact wE (stW (by decide))
      · exact wE (stW (by decide))
      · exact wE (Lay.wSub (by decide))
    exact (F₂c.trans F3).trans F6
  have rd₆' : s₆.rd = t.rd := by rw [rd₆, r₃.rd, hm₂.rd, rd₂c, h₂.rd]
  have wr₆' : s₆.wr = t.wr := by rw [wr₆, r₃.wr, hm₂.wr, wr₂c, h₂.wr]
  have exW : ∀ {R : Region}, Region.Sub R (workR W) → ∀ r ∈ ex, R.Disjoint r :=
    fun hR r hr => (hexW r hr).sub_left hR
  have exS : ∀ {r : Region}, (∃ r' ∈ fastFrame W, Region.Sub r r') → ∃ r' ∈ fastFrame W ++ ex, Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_append_left _ h, hs⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absCall2WithX_ok L (.inr rfl)
    (fun r hr => (hexC r hr).sub_left (Lay.ctxSub (d := 240) (n := 16) (by decide))) (exW (stW (by decide))) h₆
    (hgh s₆ h₆.call (stW (by decide)) (Lay.wSub (by decide)) rd₆' wr₆' h₆.env.sp FW
      (fun x hx => hsubD x (Offset.sub_base D' (by omega) x hx)))))
    fun s₇ ⟨⟨⟨h₇, hlt₇⟩, I₇⟩, rd₇, wr₇⟩ => ?_)
  rw [Nat.zero_add, Nat.sub_zero] at h₇ hlt₇
  generalize hj : 16 * ((n - P) / 16) = j at h₇ hlt₇
  have hjn : j ≤ n - P := by omega
  have hx₁C : (x₁ ++ C₀).length % 16 = 0 := by rw [List.length_append, hC₀l]; omega
  have he₇ := h₇.env
  have hab₃ : Absorbed s₃.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32)
      H (x₁ ++ C₀) := by
    refine ⟨?_, ?_⟩
    · rw [Proof.Gcm.whole_of_mod hx₁C, List.take_length, ← y₂', r₃.mem]
    · rw [hx₁C, Proof.Gcm.whole_of_mod hx₁C, List.drop_length]; rfl
  have hY₇ : blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghash H (blocks ((x₁ ++ C₀) ++ bytesAt s₃.mem D' j)) :=
    (h₇.abs hab₃).whole_eq (by rw [List.length_append, length_bytesAt]; omega)
  have key₃ : KeyAt H s₃.mem W := key₂c.frame (by rw [r₃.mem]; exact hm₂.frame) dKS
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
      s₁₀.gpr .x13 = BitVec.ofNat 64 (n - P - j) ∧ s₁₀.gpr .x12 = D' + BitVec.ofNat 64 j ∧
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
  have hdj : DataOk (W + BitVec.ofNat 64 16) W s₁₀ (D' + BitVec.ofNat 64 j) (n - P - j) :=
    (hdat₃.drop hjn).of_eq rd₁₀ wr₁₀
  have x26₁₀ : s₁₀.gpr .x26 = BitVec.ofNat 64 n := by
    rw [r₁₀.others _ (by decide), o₉.gpr, g₈ _ (by decide), h₇.kept .x26 (by decide), h₂.x26]
  have hfull₁₀ : DataOk (W + BitVec.ofNat 64 16) W s₁₀ D n :=
    o.dat.ok.of_eq (by rw [rd₁₀, r₃.rd, hm₂.rd, rd₂c, h₂.rd]) (by rw [wr₁₀, r₃.wr, hm₂.wr, wr₂c, h₂.wr])
  refine WP.seq (WP.mono (WP.with_rdwr (padMulT_ok hMK he₁₀ hk₁₀ hy₁₀ x12₁₀ x13₁₀ (by omega) hdj.rd
    (hdj.w.sub_right (Lay.wSub (by decide))) x26₁₀ hnlt
    (pad_big hfull₁₀.rd hnlt (by rw [← hD', Offset.add_add]; congr 2; omega) (by omega))))
    fun s₁₁ ⟨⟨y₁₁, hk₁₁, he₁₁, og₁₁, f₁₁, v₁₁⟩, rd₁₁, wr₁₁⟩ => ?_)
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
  have Fb : Frame (fastFrame W ++ ex) s₃.mem s₇.mem := by
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
  have mx : ∀ {m m' : Mem}, Frame (fastFrame W) m m' → Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) m m' :=
    fun h => h.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr)
  have mx' : ∀ {m m' : Mem}, Frame (fastFrame W) m m' → Frame (fastFrame W ++ ex) m m' :=
    fun h => h.mono fun r hr => List.mem_append_left _ hr
  have my : ∀ {m m' : Mem}, Frame (fastFrame W ++ ex) m m' → Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) m m' :=
    fun h => h.mono fun r hr => List.mem_cons_of_mem _ hr
  have fl : ∀ {r : Region}, (∃ r' ∈ fastFrame W, Region.Sub r r') →
      ∃ r' ∈ (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)), Region.Sub r r' :=
    fun ⟨r', h, hs⟩ => ⟨r', List.mem_cons_of_mem _ (List.mem_append_left _ h), hs⟩
  have Fs₂ : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) s₂c.mem s₃.mem := by
    rw [r₃.mem]
    refine hm₂.frame.sub fun r hr => ?_
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fl (fast_lo' (by decide))
    · exact fl (fast_lo' (by decide))
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact fl (fast_hi (by decide) (by decide))
  have Fs : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) s₂.mem s₃.mem :=
    (fcb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fl (fast_hi (by decide) (by decide))).trans Fs₂
  have dfr : ∀ {R : Region}, Region.Sub R (workR W) → (∀ r ∈ fastFrame W ++ ex, R.Disjoint r) →
      ∀ r ∈ (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)), R.Disjoint r := fun hR h r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (ddW.sub_left hsubP').symm.sub_left hR
    · exact h r hr
  have F₁₁ : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) t.mem s₁₁.mem :=
    (((mx Fa).trans Fs).trans (my Fb)).trans (mx Fc)
  have slot₁₁ : ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      s₁₁.mem.readW (W + BitVec.ofNat 64 d) 64 = t.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂' =>
    slot_kept F₁₁ (dfr (Lay.wSub (by decide)) (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide))))) h₁ h₂'
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
      (bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j)))
      (padStep H (blockAt s₇.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16))
      (bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j))) := by rw [v₁₂]; exact y₁₁
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
  have F₁₄ : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) t.mem s₁₄.mem := F₁₁.trans (mx Fd)
  have Fg : Frame (fastFrame W) s₁₄.mem s₁₇.mem := by
    refine h₁₇.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact fast_lo (by decide) (by decide)
    · exact fast_lo (by decide) (by decide)
    · exact fast_lo (by decide) (by decide)
    · exact fast_hi (by decide) (by decide)
  have F₁₇ : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) t.mem s₁₇.mem := F₁₄.trans (mx Fg)
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
  have F₂₀ : Frame (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)) t.mem s₂₀.mem := by rw [r₂₀.mem]; exact F₁₇.trans (mx Fe)
  have I₂₀ : I s₂₀.mem := by
    rw [r₂₀.mem]
    exact hI I₇ ((((Fc.trans Fd).trans Fg).trans Fe).sub fun r hr =>
      ⟨workR W, List.mem_singleton_self _, fastFrame_work W r hr⟩)
  -- What the frames keep.
  have dCf : ∀ r ∈ fastFrame W, (⟨Ctx, 256⟩ : Region).Disjoint r := keep_of_sub (fastFrame_work W) dcW
  have dDf : ∀ r ∈ fastFrame W, (⟨D, n⟩ : Region).Disjoint r := keep_of_sub (fastFrame_work W) ddW
  have dcfr : ∀ r ∈ (⟨D, Stitch.pre n⟩ :: (fastFrame W ++ ex)), (⟨Ctx, 256⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact o.dat.ctx.sub_right hsubP'
    · exact disj_ex dCf hexC r hr
  have hc₁₄ : ciphOf s₁₄.mem Ctx R = ciphOf t.mem Ctx R := ciph_frame F₁₄ dcfr hRb
  have cbR : ∀ {R : Region}, (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint R →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region)], R.Disjoint r := dcbR
  have hC₀t : C₀ = bytesAt t.mem D P := by
    rw [← hC₀, bytesAt_frame fcb (cbR (cbD.sub_right (Region.sub_prefix hPn))) (by omega),
      bytesAt_frame Fa (fun r hr => (dDf r hr).sub_left (Region.sub_prefix hPn)) (by omega)]
  have dD'S : ∀ r ∈ Stitch.sFrame (W + BitVec.ofNat 64 16) W D n, (⟨D', n - P⟩ : Region).Disjoint r := by
    intro r hr
    simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (o.dat.ok.st.sub_left hsubD).sub_right (Lay.stSub (by decide))
    · exact (o.dat.ok.st.sub_left hsubD).sub_right (Lay.stSub (by decide))
    · rw [hP, ← hD']; exact (Offset.base_disjoint D (Nat.le_refl _) (by omega)).symm
    · exact (ddW.sub_left hsubD).sub_right (Lay.wSub (by decide))
  have hrest₃ : bytesAt s₃.mem D' (n - P) = bytesAt t.mem D' (n - P) := by
    rw [r₃.mem, bytesAt_frame hm₂.frame dD'S (by omega), bytesAt_frame fcb (cbR (cbD.sub_right hsubD)) (by omega),
      bytesAt_frame Fa (fun r hr => (dDf r hr).sub_left hsubD) (by omega)]
  have ht₁₀ : bytesAt s₁₀.mem (D' + BitVec.ofNat 64 j) (n - P - j) =
      bytesAt s₃.mem (D' + BitVec.ofNat 64 j) (n - P - j) := by
    rw [m₁₀, bytesAt_frame h₇.frame (disj_absEx (data_absFrame (.inr rfl) (hdat₃.drop hjn))
      fun r hr => (hexD r hr).sub_left (fun x hx => hsubD x (Offset.sub_base D' (by omega) x hx))) (by omega)]
  have hsplit : bytesAt t.mem D n =
      (C₀ ++ bytesAt s₃.mem D' j) ++ bytesAt s₃.mem (D' + BitVec.ofNat 64 j) (n - P - j) := by
    rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hjn, hrest₃, hC₀t, ← hD', ← bytesAt_add,
      Nat.add_sub_cancel' hPn]
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
      blockAt_frame fT₁₂ dT, blockAt_frame f₁₁ dT, m₁₀, e₇, r₃.mem, blockAt_frame hm₂.frame (fun r hr => by
        simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact st0_disj L (by decide) (by decide)
        · exact st0_disj L (by decide) (by decide)
        · exact (o.dat.ok.st.sub_left hsubP').symm.sub_left (Region.sub_prefix (by decide))
        · exact st0_w L ⟨by decide, by decide⟩),
      blockAt_frame fcb (cbR (st0_w L ⟨by decide, by decide⟩).symm), j0₂, ← hJ0]
  have hcb : blockAt s₂₀.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      Nat.repeat inc32 (P / 16) (inc32 J0) := by
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
      r₃.mem, ctr₂.1, show (P + 15) / 16 = P / 16 by omega]
  have Fz : Frame (fastFrame W ++ ex) s₃.mem s₂₀.mem := by
    rw [r₂₀.mem]; exact Fb.trans (mx' (((Fc.trans Fd).trans Fg).trans Fe))
  have hcbs : blockAt s₂₀.mem (W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO) = inc32 J0 := by
    have cW : ∀ {d k : Nat}, (d + k ≤ 320 ∨ 336 ≤ d) → d + k ≤ 2560 →
        (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
      fun h hk => L.w_w (by simp only [Impl.AesGcm.AArch64.Stitch.cbO]; omega) (by decide) hk
    have cS : ∀ {a k : Nat}, a + k ≤ 80 →
        (⟨W + BitVec.ofNat 64 Impl.AesGcm.AArch64.Stitch.cbO, 16⟩ : Region).Disjoint
          ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a, k⟩ :=
      fun h => (L.st_w h (.inr ⟨by decide, by decide⟩)).symm
    rw [r₂₀.mem, blockAt_frame f₁₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)),
      blockAt_frame h₁₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using cS (a := 0) (k := 32) (by decide)
        · exact cW (.inl (by decide)) (by decide)
        · exact cW (.inl (by decide)) (by decide)
        · exact cW (.inr (by decide)) (by decide)),
      blockAt_frame fY₁₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cS (by decide)),
      blockAt_frame fT₁₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)),
      blockAt_frame f₁₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cW (.inl (by decide)) (by decide)), m₁₀,
      blockAt_frame h₇.frame (disj_absEx (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cS (by decide)
        · exact cS (by decide)
        · exact cW (.inr (by decide)) (by decide)) (exW (Lay.wSub (by decide)))),
      r₃.mem, blockAt_frame hm₂.frame (fun r hr => by
        simp only [Stitch.sFrame, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact cS (by decide)
        · exact cS (by decide)
        · exact cbD.sub_right hsubP'
        · exact cW (.inr (by decide)) (by decide)), hcbs₂]
  -- The tag.
  have hT : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.toBytes (ghashFrom H
      (ghash H (blocks (Proof.Gcm.padded (bytesAt t.mem A al) (bytesAt t.mem D n))))
      [ofBytes (lensBlock (bytesAt t.mem A al).length (bytesAt t.mem D n).length)] ^^^
      ciphOf t.mem Ctx R (Spec.Gcm.j0 H (bytesAt t.mem Np 12))) := by
    rw [h₁₇.out, b₁₄, hJ₁₄, hc₁₄, hY₇, List.append_assoc x₁, ht₁₀, ← hx₁, hsplit,
      ghash_padded _ _ _ _ (by rw [List.length_append, hC₀l, length_bytesAt]; omega)
        (by rw [length_bytesAt]; omega)]
    simp only [List.length_append, hC₀l, length_bytesAt, show P + j + (n - P - j) = n by omega]
    rfl
  have hT' : bytesAt s₁₇.mem (W + BitVec.ofNat 64 112) 16 = Spec.Gcm.fullTag (ciphOf t.mem Ctx R) H
      (bytesAt t.mem Np 12) (bytesAt t.mem A al) (bytesAt t.mem D n) := by
    rw [hT, Proof.Gcm.fullTag_eq]
  have hW₁₈ : bytesAt s₁₇.mem W tl = bytesAt t.mem W tl := by
    refine bytesAt_frame F₁₇ (fun r hr => ?_) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | (rfl | rfl) | hr
    · exact (ddW.sub_left hsubP').symm.sub_left (Region.sub_prefix (by omega))
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
  have hc₂c : ciphOf s₂c.mem Ctx R = ciphOf t.mem Ctx R := by
    rw [ciph_frame fcb (cbR ((L.cw'.sub_right (Lay.wSub (by decide))).symm)) hRb, ciph_frame Fa dCf hRb]
  have hDz : ∀ {E : Addr} {k : Nat}, Region.Sub ⟨E, k⟩ ⟨D, n⟩ → ∀ r ∈ fastFrame W ++ ex, (⟨E, k⟩ : Region).Disjoint r :=
    fun hE r hr => (disj_ex dDf hexD r hr).sub_left hE
  have hpre : bytesAt s₂₀.mem D P = xorKs (ciphOf t.mem Ctx R) (inc32 J0) 0 (bytesAt t.mem D P) := by
    rw [bytesAt_frame Fz (hDz (Region.sub_prefix hPn)) (by omega), r₃.mem, dat₂, hc₂c, hC₀t]
  have hrest : bytesAt s₂₀.mem (D + BitVec.ofNat 64 P) (n - P) = bytesAt t.mem (D + BitVec.ofNat 64 P) (n - P) := by
    rw [hD', bytesAt_frame Fz (hDz hsubD) (by omega), hrest₃]
  subst hH
  refine ⟨⟨he₂₀, by rw [← hP]; exact F₂₀, x22₂₀, by rw [x27₂₀, hBeq],
    o.dat.of_eq (by rw [r₂₀.rd, rd₁₉, rd₁₇, rd₁₆, o₁₄.rd, o₁₃.rd, rd₁₂, rd₁₁, rd₁₀, r₃.rd, hm₂.rd, rd₂c, h₂.rd])
      (by rw [r₂₀.wr, wr₁₉, wr₁₇, wr₁₆, o₁₄.wr, o₁₃.wr, wr₁₂, wr₁₁, wr₁₀, r₃.wr, hm₂.wr, wr₂c, h₂.wr]),
    by rw [slot_kept F₂₀ (dfr (Lay.wSub (by decide)) (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide)))))
      (by decide) (by decide), o.sD],
    by rw [slot_kept F₂₀ (dfr (Lay.wSub (by decide)) (disj_ex (slots_fastFrame W) (exW (Lay.wSub (by decide)))))
      (by decide) (by decide), o.sN],
    by rw [← hP], by rw [hJ0]; exact hpre, hrest, by rw [hJ0]; exact hcb,
    by rw [hJ0]; exact hcbs, ciph_frame F₂₀ dcfr hRb⟩, I₂₀⟩

end

end VG.Proof.AesGcm.AArch64.Fast
