module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Rsa.X86.RvBatchGcd
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The batched GCD in prime recovery by Appendix C.2 (i686)

`RvBatchGcd`'s `batchGcd_ok` for the arrays of Appendix C.2: `gcd(m, x)` of
`m` (odd) in narrow array 8 and `x` in narrow array 0 into narrow array 1,
narrow array 10 zero, keeping `n`, the wide `2^k x` and the flag of `d e ≥ 2`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverDetRt (wX3 sOkDE)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.InvBatchRt (rv nw)
open VG.Proof.Rsa.X86.KeyRt (kw)

theorem gcdDet_ok [VG.Proof.Rsa.X86.BatchLaw] {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x : Nat}
    (h : KS g s0 A [aM, 0, aN] AW [wX3] V [sOkDE] s) (hm : A aM = m) (hx : A 0 = x) (odd : m % 2 = 1) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body VG.Impl.Rsa.X86.RecoverRt.wid) s fun t =>
      KS g s0 (upd (upd A 1 (Nat.gcd m x)) aZero 0) [1, aZero, aN] AW [wX3] V [sOkDE] t := by
  have lo := h.lower; have up := h.upper
  have ek : kw (16 * g.n + 24) = 4 * g.n + 6 := by
    simp only [kw, Spec.Rsa.modulusWords]; omega
  have en : nw (16 * g.n + 24) = 2 * g.n + 3 := by simp only [nw, ek]; omega
  have ew : g.w = 2 * g.n + 2 := rfl
  have ra : ∀ j, rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a j) = arr g.w (2 * j) := by
    intro j
    rw [InvBatchRt.rv_a, en]
    simp only [arr, S, hdr, ew]
    rw [show 2 * j * (4 * (2 * g.n + 2 + 2)) = j * (2 * (4 * (2 * g.n + 2 + 2))) by
      rw [Nat.mul_comm 2 j, Nat.mul_assoc], show 2 * (4 * (2 * g.n + 2 + 2)) = 8 * (2 * g.n + 3) + 8 by omega]
  have rr : rv (kw (16 * g.n + 24)) VG.Impl.Rsa.X86.GcdBatchRt.res = arr g.w 1 := by
    rw [GcdBatchRt.rv_res, ra, en]; simp only [arr, S, hdr, ew]; omega
  have n1 : nw (16 * g.n + 24) - 1 = g.w := by rw [en]; rfl
  have vm : val32 s.mem g.B (rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a 4))
      (nw (16 * g.n + 24) - 1) = m := by
    rw [ra, n1]; exact (h.arrs aM (by simp)).trans hm
  have vx : val32 s.mem g.B (rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a 0))
      (nw (16 * g.n + 24) - 1) = x := by
    rw [ra, n1]; exact (h.arrs 0 (by simp)).trans hx
  refine WP.mono (BatchLaw.gcd_ok h.rtW (by decide) (by omega) (by omega) (by omega) vm vx odd)
    fun t ⟨_, G, Zr, r, U⟩ => ?_
  rw [rr, n1] at G
  rw [ra, n1] at Zr
  have k := gcd_keep U
  have hz : ∀ j ∈ ([0, 1, 2, 3, 4, 5, 11, 12] : List Nat), arr g.W j + S g.W ≤ g.Z := fun j hj =>
    h.wsW.arr_fit (by simp at hj; omega)
  have aNkeep : num t.mem g.B g.w aN = num s.mem g.B g.w aN := by
    have fit := h.ws.arr_fit (j := aN) (by decide)
    have nw' := h.ws.workspace.nowrap
    have r0 := InvBatchRt.rv_a (16 * g.n + 24) 0
    have r11 := InvBatchRt.rv_a (16 * g.n + 24) 11
    rw [en] at r0 r11
    exact Outs.val32 U (by
      intro w hw
      simp only [GcdBatchRt.gcdWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [arr, S, hdr, ew, aN] at fit ⊢
      rcases hw with rfl | rfl | rfl <;> simp only [r0, r11, en, VG.Impl.Rsa.X86.InvBatchRt.win] <;> omega) (by omega)
  refine h.core k hz (by decide) (r.mono (by decide)) ?_ (by decide) (h.arrsW_W k (by decide) (by decide))
    (by decide) (h.sl_keep k (by decide)) h.ls_ok
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact G.trans (by simp [upd, aZero])
  · exact Zr.trans (by simp [upd])
  · rw [aNkeep, h.arrs aN (by simp)]; simp [upd, aN, aZero]

end VG.Proof.Rsa.X86.Recover
