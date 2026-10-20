module

public import VerifiedGarbage.Proof.Rsa.X86.RvDivide
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvOps

/-! # Ordering the recovered factors, larger first -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

def AF (p q : Nat) : Nat → Nat := upd (upd (fun _ => 0) 5 (max p q)) 6 (min p q)

theorem order_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {p q : Nat}
    (h : KS g s0 (AQ p q) [1, aQ, aZero] (fun _ => 0) [] V [sMask] s) :
    WP isa (order g.n) s fun t => KS g s0 (AF p q) [5, 6, aZero] (fun _ => 0) [] V [sMask] t := by
  unfold order
  simp only [seqs]
  refine WP.seq (WP.mono (h.subWrap (o := aW) (a := 1) (b := aQ)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)) fun s1 ⟨h1, borrow⟩ => ?_)
  have flag : (s1.gpr .ebx).toNat = b2n (decide (p < q)) := borrow
  refine WP.seq (WP.mono (h1.storeSlot (d := sLt) (by decide) .ebx) fun s2 ⟨h2, _, _⟩ => ?_)
  rw [flag] at h2
  refine WP.seq (WP.mono (h2.sel_w (o := 5) (a := 1) (b := aQ) (sl := sLt)
    (by decide) (by simp) (by simp) (by simp)
    (by rw [upd_self]; exact VG.Proof.Rsa.b2n_le _) (by simp)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.mono (h3.sel_w (o := 6) (a := aQ) (b := 1) (sl := sLt)
    (by decide) (by simp) (by simp) (by simp)
    (by rw [upd_self]; exact VG.Proof.Rsa.b2n_le _) (by simp)) fun t ⟨hout, _⟩ => ?_
  refine hout.mono ?_ (by simp) ?_
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;>
      simp [AF, AQ, upd, aQ, aW, aZero, b2n, Nat.max_def, Nat.min_def] <;> split_ifs <;> omega
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact ⟨by simp, upd_ne _ _ (by decide)⟩

end VG.Proof.Rsa.X86.Recover
