module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Pointer

import VerifiedGarbage.Proof.Dsa.X86.WidthMatch

/-! # Selecting supported public component widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem checkDispatch_ok (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (hp : (pointerValue base s (.input .pLen)).toNat = pLen)
    (hq : (pointerValue base s (.input .qLen)).toNat = qLen)
    (body : ∀ t, Keeps [.eax] s t → t.mem = s.mem → WP isa (Generate.checkSized pLen qLen) t Q) :
    WP isa (Generate.checkDispatch widths) s Q := by
  induction widths generalizing s with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    have Brest : ∀ w ∈ rest, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32 :=
      fun w hw => bound w (List.mem_cons_of_mem _ hw)
    unfold Generate.checkDispatch
    refine WP.seq (WP.mono (widthMatch_ok hs hz hp hq B.1 B.2) fun t ⟨Z, K, O⟩ => ?_)
    by_cases Both : pLen = wp ∧ qLen = wq
    · refine WP.ite true (by simp only [eval, Z, Both, true_and, decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
      rw [← Both.1, ← Both.2]
      exact body t K O
    · refine WP.ite false (by simp only [eval, Z, Both, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
      apply ih (hs.of_keeps K (by decide))
        (by simpa only [List.mem_cons, Prod.mk.injEq, Both, false_or] using member) Brest
      · simpa only [pointerValue, O] using hp
      · simpa only [pointerValue, O] using hq
      · intro u Ku Ou
        exact body u (K.trans Ku) (Ou.trans O)

end VG.Proof.Dsa.X86
