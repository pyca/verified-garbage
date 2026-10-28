module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Batch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import Mathlib.Algebra.Order.Ring.Abs

/-! # The batches of the inverse at a run-time width

`loop_ok`: `3 (n + 1)` counted batches from the start state.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)
open VG.Proof.Rsa.Divstep (oddInput)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- After `k` batches. -/
def LoopAt (L : Lay) (B : Addr) (Z len N p x iv : Nat) (s₀ : State) (k : Nat) (s : State) : Prop :=
  Bx L s B Z len N ∧ StateAt len B p iv (Divstep.W32.invRun 30 p iv (oddInput p x) k) s ∧
  w32 s.mem B 100 = 3 * (nw len + 1) - k ∧ Keeps wordClob s₀ s ∧ Unch B (countedWrites len) s₀.mem s.mem

/-- The loop body. -/
abbrev batchCode (L : Lay) : Prog isa :=
  .seq (.block (start L)) (.seq (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30) (.seq (update L)
    (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter])))

theorem loop_ok {s : State} (h : Bx L s B Z len N) (he : nw len % 2 = 0) {p x iv : Nat}
    (hst : StateAt len B p iv (Divstep.W32.invRun 30 p iv (oddInput p x) 0) s)
    (counter : w32 s.mem B 100 = 3 * (nw len + 1))
    (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * nw len)) (xc : x < 2 ^ (32 * nw len)) :
    WP isa (.loop (batchCode L) .ne) s (LoopAt L B Z len N p x iv s (3 * (nw len + 1))) := by
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have cap : p + x < 2 ^ (32 * nw len + 1) := by rw [Nat.pow_succ]; omega
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  have start : LoopAt L B Z len N p x iv s 0 s :=
    ⟨h, hst, by simpa only [Nat.sub_zero] using counter, Keeps.refl _ _, Unch.refl _ _ _⟩
  refine WP.loop (M := isa) (fun remaining u => ∃ k, k + remaining = 3 * (nw len + 1) ∧ 0 < remaining ∧
    LoopAt L B Z len N p x iv s k u) ?_ (3 * (nw len + 1)) s ⟨0, by omega, by omega, start⟩
  intro remaining u ⟨k, total, pos, Hu, I, cu, ku, ou⟩
  obtain ⟨bd, fo, fb, gb, a0, a1, b0, b1⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x)
    odd large hinv (by omega) ox k
  have hd : |(Divstep.W32.invRun 30 p iv (oddInput p x) k).d| + 64 < 2 ^ 30 := by
    omega
  refine WP.mono (countedBatch_ok Hu he I (by omega) hinv hd fo fb gb cap
    (by rw [abs_of_nonneg a0]; omega) (by rw [abs_of_nonneg b0]; omega)
    (by omega) (by omega) cu) fun v ⟨Hv, Iv, cv, zf, kv, ov⟩ => ?_
  have Iv' : StateAt len B p iv (Divstep.W32.invRun 30 p iv (oddInput p x) (k + 1)) v := Iv
  have cv' : w32 v.mem B 100 = 3 * (nw len + 1) - (k + 1) := by rw [cv]; omega
  have next : LoopAt L B Z len N p x iv s (k + 1) v :=
    ⟨Hv, Iv', cv', ku.trans kv, fun y hy => (ov y hy).trans (ou y hy)⟩
  by_cases last : k + 1 = 3 * (nw len + 1)
  · left
    refine ⟨?_, by simpa only [last] using next⟩
    change v.zf.map (!·) = some false
    rw [zf]
    have zero : 3 * (nw len + 1) - k - 1 = 0 := by omega
    simp only [zero, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, remaining - 1, by omega, k + 1, by omega, by omega, next⟩
    change v.zf.map (!·) = some true
    rw [zf]
    have nz : 3 * (nw len + 1) - k - 1 ≠ 0 := by omega
    simp only [nz, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Rsa.X86.InvBatchRt
