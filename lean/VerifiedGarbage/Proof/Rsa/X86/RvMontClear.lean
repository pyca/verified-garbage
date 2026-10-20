module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Clearing a Montgomery result's two extra key-array words -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem clrTop_ok {g : Geo} {s : State} (h : Ws s g.B g.Z g.w nArr) {j : Nat}
    (hj : j < nArr) : WP isa (clrTop g.n j) s fun t =>
      Ws t g.B g.Z g.w nArr ∧ Keep g.B g.w [j] [] s.mem t.mem ∧
      num t.mem g.B g.w j = wordsVal s.mem g.B (arr g.w j) g.n ∧
      Keeps [.eax, .ebp, .edx] s t := by
  have fit := h.arr_fit hj
  have fit64 := h.fit64 hj
  change arr g.w j + 4 * (2 * g.n + 2 + 2) ≤ g.Z at fit
  change arr g.w j + 4 * (2 * g.n + 2 + 2) ≤ 2 ^ 64 at fit64
  refine WP.mono (zerosW_ok h.workspace (o := arr g.w j + 8 * g.n) (k := 2)
    (by decide) (by omega)) fun t ⟨frame, zero, r⟩ => ?_
  refine ⟨h.rest r, Keep.of_arr frame (by change 8 * g.n + 4 * 2 ≤ 4 * (2 * g.n + 2 + 2); omega)
    (by simp), ?_, r⟩
  change val32 t.mem g.B (arr g.w j) (2 * g.n + 2) = _
  rw [val32_append, show 4 * (2 * g.n) = 8 * g.n by omega, zero, Nat.mul_zero, Nat.add_zero]
  rw [frame.val32 (.inl (by omega)) (by omega), wordsVal_eq_val32]

end VG.Proof.Rsa.X86.Recover
