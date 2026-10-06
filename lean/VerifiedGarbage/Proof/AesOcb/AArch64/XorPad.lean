import VerifiedGarbage.Proof.AesOcb.AArch64.Whole

/-!
# AES-OCB on AArch64: the rest of the data XORed with `Pad` (`xorPad`)

Untrusted: everything here is checked by Lean. `xorPad` XORs the `r` bytes
at `x23` with the first `r` bytes at `W + tmpO`, with AES-GCM's `xorLoop`
(`xorPad_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (xorLoop_ok in_left in_off covers_off)

/-- The registers `xorPad` writes. -/
abbrev xpRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-- `xorPad`: the `r` bytes at `P` (in `x23`), `0 < r < 16`, XORed with the
first `r` bytes at `W + tmpO`. -/
theorem xorPad_ok {K W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {P : Addr}
    {r : Nat} (hr : 0 < r) (hr' : r < 16) (h23 : s.gpr .x23 = P) (h24 : s.gpr .x24 = BitVec.ofNat 64 r)
    (hP : DBuf K W s P r) :
    WP isa xorPad s fun t => t.mem = writeBytes s.mem P
        (Spec.Ocb.xor (bytesAt s.mem P r) (bytesAt s.mem (W + BitVec.ofNat 64 112) r)) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.ptr .x11 .x19 tmpO, Impl.AesGcm.AArch64.mov .x12 .x23,
        Impl.AesGcm.AArch64.mov .x13 .x24] s = some s₁ ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 112 ∧ s₁.gpr .x12 = P ∧ s₁.gpr .x13 = BitVec.ofNat 64 r ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h19]
    · simp [gpr_write, h23]
    · simp [gpr_write, h24]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  unfold xorPad
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have pre : Proof.AesGcm.AArch64.LoopPre s₁ (W + BitVec.ofNat 64 112) P r :=
    ⟨by omega, by rw [rd₁, wr₁]; exact Proof.AesGcm.AArch64.covers_left (covers_off hw (by omega) (by decide)),
      by rw [wr₁]; exact hP.wr, (hP.w.sub_right (Lay.wSub (W := W) (d := 112) (n := r) (by omega))).symm⟩
  refine WP.mono (xorLoop_ok s₁ x11₁ x12₁ x13₁ hr pre) fun t ⟨mt, gt, spt, rdt, wrt⟩ => ?_
  refine ⟨by rw [mt, m₁]; rfl, fun q hq => ?_, by rw [spt, sp₁], by rw [rdt, rd₁], by rw [wrt, wr₁]⟩
  simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [gt q (by simp [Proof.AesGcm.AArch64.loopRegs, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]),
    g₁ q hq.1 hq.2.1 hq.2.2.1]

end VG.Proof.AesOcb.AArch64
