module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvGcdSet
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Batched GCD inside the prime-recovery workspace

The GCD runs on the wide arrays (`RecoverRt.wid`), whose array `j` is narrow array `2 j`: it
reads `m` and `x` from narrow arrays 8 and 0, writes `gcd(m, x)` into narrow array 1, and
leaves narrow array 10 (`aZero`) zero.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)
open VG.Proof.Rsa.X86.InvBatchRt (rv nw)
open VG.Proof.Rsa.X86.KeyRt (kw)

/-- The header words the GCD writes, from the window to the batch count. -/
abbrev gcdSlots : List Nat :=
  [16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100]

/-- The GCD's writes are within the wide arrays 0 to 5, 11 and 12 and the header words. -/
theorem gcd_keep {g : Geo} {m m' : Mem}
    (U : VG.Proof.Weierstrass.Unch g.B (GcdBatchRt.gcdWrites (16 * g.n + 24)) m m') :
    Keep g.B g.W [0, 1, 2, 3, 4, 5, 11, 12] gcdSlots m m' := by
  have ek : kw (16 * g.n + 24) = 4 * g.n + 6 := by
    simp only [kw, Spec.Rsa.modulusWords]; omega
  have en : nw (16 * g.n + 24) = 2 * g.n + 3 := by simp only [nw, ek]; omega
  have eW : g.W = 4 * g.n + 6 := by simp only [Geo.W, wide, width]; omega
  intro x hx
  have each : ∀ j ∈ [0, 1, 2, 3, 4, 5, 11, 12], ofs g.B x < arr g.W j ∨ arr g.W j + S g.W ≤ ofs g.B x :=
    fun j hj => hx (arr g.W j, S g.W) (by
      simp only [ranges, List.mem_append, List.mem_map]
      exact .inl ⟨j, hj, rfl⟩)
  have slots : ofs g.B x < 16 ∨ 104 ≤ ofs g.B x := by
    by_contra c
    have mem : ∀ q < 22, 16 + 4 * q ∈ gcdSlots := by decide
    have := hx (16 + 4 * ((ofs g.B x - 16) / 4), 4) (by
      simp only [ranges, List.mem_append, List.mem_map]
      exact .inr ⟨_, mem _ (by omega), rfl⟩)
    simp only at this
    omega
  have h0 := each 0 (by decide); have h1 := each 1 (by decide); have h2 := each 2 (by decide)
  have h3 := each 3 (by decide); have h4 := each 4 (by decide); have h5 := each 5 (by decide)
  have h11 := each 11 (by decide); have h12 := each 12 (by decide)
  apply U x
  intro w hw
  simp only [GcdBatchRt.gcdWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
  have ar : ∀ j, arr g.W j = 160 + j * (16 * g.n + 32) := fun j => by simp only [arr, S, hdr, eW]; congr 2; omega
  have sr : S g.W = 16 * g.n + 32 := by simp only [S, eW]; omega
  have rj : ∀ j, rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a j) = 160 + j * (16 * g.n + 32) := fun j => by
    rw [InvBatchRt.rv_a, en]; congr 2; omega
  rw [ar, sr] at h0 h1 h2 h3 h4 h5 h11 h12
  rcases hw with rfl | rfl | rfl
  · show ofs g.B x < 16 ∨ 16 + 88 ≤ ofs g.B x
    omega
  all_goals
    show ofs g.B x < _ ∨ _ ≤ ofs g.B x
    rw [rj, en]
    generalize hT : 16 * g.n + 32 = T at *
    rw [show 8 * (2 * g.n + 3) + 8 = T by omega]
    omega

theorem batchGcd_ok [VG.Proof.Rsa.X86.BatchLaw] {g : Geo} {s0 s : State} {V : Nat → Nat} {m y : Nat}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s) (odd : m % 2 = 1) :
    WP isa (VG.Impl.Rsa.X86.GcdBatchRt.body VG.Impl.Rsa.X86.RecoverRt.wid) s fun t =>
      KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1, aN, aZero] (fun _ => 0) [] V [sMask] t := by
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
    rw [ra, n1]; exact h.arrs aM (by simp [liveG])
  have vx : val32 s.mem g.B (rv (kw (16 * g.n + 24)) (VG.Impl.Rsa.X86.InvBatchRt.a 0))
      (nw (16 * g.n + 24) - 1) = sub32 g.w y 1 := by
    rw [ra, n1]; exact h.arrs 0 (by simp [liveG])
  refine WP.mono (BatchLaw.gcd_ok h.rtW (by decide) (by omega) (by omega) (by omega) vm vx odd)
    fun t ⟨_, G, Zr, r, U⟩ => ?_
  rw [rr, n1, Nat.gcd_comm m] at G
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
  refine h.core k hz (by decide) (r.mono (by decide)) ?_ (by decide) (by simp [Arrs]) (by simp)
    (h.sl_keep k (by decide)) h.ls_ok
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact G
  · rw [aNkeep, h.arrs aN (by simp [liveG])]; rfl
  · exact Zr

end VG.Proof.Rsa.X86.Recover
