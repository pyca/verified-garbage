module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontMul
public import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps

/-! # A Montgomery multiplication advances the tracked recovery stage -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem KS.montResult {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o : Nat}
    (h : KS g s0 A live AW liveW V ls s) (ho : o < nArr)
    (k : Keep g.B g.w (montWrites o) [] s.mem t.mem) (r : Keeps opRegs s t)
    (hl : ∀ j ∈ live, j = o ∨ (j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1))
    (hlW : ∀ j ∈ liveW, ∀ i ∈ montWrites o, i / 2 ≠ j) :
    KS g s0 (upd A o (num t.mem g.B g.w o)) (o :: live) AW liveW V ls t := by
  refine h.core k ?_ (by simp) r ?_ ?_
    (h.arrsW_w k hlW (by simp)) h.liveW_lt (h.sl_keep k (by simp)) h.ls_ok
  · intro j hj
    apply h.ws.arr_fit
    simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ho
    all_goals decide
  · intro j hj
    by_cases eq : j = o
    · subst eq; rw [upd_self]
    · have old := (List.mem_cons.mp hj).resolve_left eq
      have exclude := (hl j old).resolve_left eq
      rw [upd_ne _ _ eq, k.num (fun i hi => by
        simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact Ne.symm eq
        · exact Ne.symm exclude.1
        · exact Ne.symm exclude.2.1
        · exact Ne.symm exclude.2.2) (by simp) (h.ws.fit64 (h.live_lt j old)), h.arrs j old]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | old
    · exact ho
    · exact h.live_lt j old

theorem KS.mmul {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (ho : MontIndex o) (ha : MontIndex a) (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hal : a ∈ live) (hbl : b ∈ live) (hA : A a < m) (hB : A b < m)
    (hl : ∀ j ∈ live, j = o ∨ (j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1))
    (hlW : ∀ j ∈ liveW, ∀ i ∈ montWrites o, i / 2 ≠ j) :
    WP isa (mmul g.n o a b) s fun t => ∃ X,
      KS g s0 (upd A o X) (o :: live) AW liveW V ls t ∧ MR g m t ∧
      (Keeps opRegs s t ∧ t.gpr .esi = s.gpr .esi) ∧
      X < m ∧ X * 2 ^ (64 * g.n) % m = A a * A b % m := by
  refine WP.mono (mmul_ok mr ho ha hb ho0
    (by rw [h.arrs a hal]; exact Nat.lt_trans hA mr.bound)
    (by rw [h.arrs b hbl]; exact hB)) fun t ⟨mt, k, r, lt, value⟩ => ?_
  refine ⟨num t.mem g.B g.w o, ?_, mt, r, lt, ?_⟩
  · exact h.montResult ho.2.1 k r.1 hl hlW
  · rw [h.arrs a hal, h.arrs b hbl] at value
    exact value

end VG.Proof.Rsa.X86.Recover
