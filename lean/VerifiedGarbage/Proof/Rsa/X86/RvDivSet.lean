module

public import VerifiedGarbage.Proof.Rsa.X86.RvGcd

/-! # Preparing the division of the modulus by the recovered GCD -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def AD (m p : Nat) : Nat → Nat := upd (upd (AP m p) aQ m) aDv p

theorem divSet_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m p : Nat}
    (h : KS g s0 (AP m p) [1, aN, aZero] (fun _ => 0) [] V [sMask] s) :
    WP isa (divSet g.n) s fun t =>
      KS g s0 (AD m p) [aQ, aDv, 1, aZero] (fun _ => 0) [] V [sMask] t ∧
      w32 t.mem g.B (arr g.w aDv + 4 * g.w) = 0 := by
  unfold divSet
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aQ) (a := aN) (by decide) (by simp) (by simp))
    fun s1 ⟨h1, _, _⟩ => ?_)
  have vn : AP m p aN = m := rfl
  rw [vn] at h1
  refine WP.seq (WP.mono (h1.copy_w (o := aDv) (a := 1) (by decide) (by simp) (by simp))
    fun s2 ⟨h2, _, _⟩ => ?_)
  have vp : upd (AP m p) aQ m 1 = p := rfl
  rw [vp] at h2
  refine wp_movS rfl fun s3 U _ => ?_
  have h3 := h2.of_rest U.keeps (by decide) U.mem
  have fit := h3.ws.arr_fit (by decide : aDv < nArr)
  have nw := h3.ws.workspace.nowrap
  simp only [S] at fit
  change WP isa (.block [.store (VG.Impl.Mont.X86.sc (arr g.w aDv + 4 * g.w)) .eax]) s3 _
  refine wp_storeS (h3.ws.workspace.ea (by omega)) (h3.ws.workspace.write (by omega))
    fun t T => WP.block_nil ?_
  have outside := writeW32_outside s3.mem g.B (d := arr g.w aDv + 4 * g.w) (s3.gpr .eax) (by omega)
  have keep : Keep g.B g.w [aDv] [] s3.mem t.mem := by
    rw [T.mem]
    exact Keep.of_arr outside (by unfold S; omega) (by simp)
  have val : num t.mem g.B g.w aDv = p := by
    rw [T.mem]
    change val32 (s3.mem.writeW (off g.B (arr g.w aDv + 4 * g.w)) (s3.gpr .eax)) g.B (arr g.w aDv) g.w = p
    rw [outside.val32 (by omega) (by omega)]
    exact h3.arrs aDv (by simp)
  have hout := h3.write_w keep (by decide) (by simp) ((T.keeps []).mono (by simp)) val (by simp) (by simp)
  rw [upd_noop (show upd (upd (AP m p) aQ m) aDv p aDv = p from rfl)] at hout
  refine ⟨hout.mono ?_ (by simp) (fun d hd => ⟨hd, rfl⟩), ?_⟩
  · intro j hj
    exact ⟨by simp only [List.mem_cons] at *; grind, rfl⟩
  · rw [T.mem, w32_write_self, U.gpr]
    rfl

end VG.Proof.Rsa.X86.Recover
