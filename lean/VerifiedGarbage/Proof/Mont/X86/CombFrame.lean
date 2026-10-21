module

public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Impl.Mont.X86.CombTable
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Mont.X86.EncodeBase
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! Shared memory geometry for the retained comb and arithmetic scratch. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure Layout (n context size : Nat) : Prop where
  positive : 0 < n
  apart : contextBytes n ≤ context
  bound : context+272*n ≤ size

theorem Layout.slot {n context size : Nat} (L : Layout n context size) {i : Nat} (hi : i < 9) :
    slot n i+8*n ≤ context := by
  have := slot_bound (n := n) hi
  have := L.apart
  unfold stride at *
  omega

theorem entry_apart (n tab : Nat) {j k : Nat} (h : j ≠ k) :
    entry n tab j+8*n ≤ entry n tab k ∨ entry n tab k+8*n ≤ entry n tab j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_left (8*n) (show j+1 ≤ k by omega)
    simp only [Nat.mul_add, Nat.mul_one] at this
    unfold entry; omega
  · right
    have := Nat.mul_le_mul_left (8*n) (show k+1 ≤ j by omega)
    simp only [Nat.mul_add, Nat.mul_one] at this
    unfold entry; omega

theorem Layout.entry {n context size : Nat} (_L : Layout n context size) {j : Nat} (hj : j < 32) :
    context+16*n ≤ entry n (context+16*n) j ∧
    entry n (context+16*n) j+8*n ≤ context+272*n := by
  have := Nat.mul_le_mul_left (8*n) (show j+1 ≤ 32 by omega)
  simp only [Nat.mul_add, Nat.mul_one] at this
  unfold VG.Impl.Mont.X86.Dynamic.entry
  omega

theorem op_high {n size m o d : Nat} {base : Addr} {s t : State}
    (C : Context n m base size s) (ho : o < 9)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t)
    (hd : contextBytes n ≤ d) (hz : d+8*n ≤ size) :
    wordsVal t.mem base d n = wordsVal s.mem base d n := by
  have bo := slot_bound (n := n) ho
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have nw := C.scr.nowrap
  unfold stride at bo b1 b2
  apply OpKeep.val K
  · right; change slot n o+8*n ≤ d; omega
  · right; change slot n 1+8*n ≤ d; omega
  · right; rw [context_accLen]; omega
  · omega

theorem outside_high_context {n context size m d len : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (C : Context n m base size s) {rs : List Reg}
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hsp : .esp ∉ rs)
    (O : Outside base d len s.mem t.mem) (hd : context ≤ d) : Context n m base size t := by
  apply C.outside_keep K hdi hsp O
  · left; have := L.slot (i := 0) (by decide); omega
  · have := slot_header n 9; have := L.apart; change slot n 9 ≤ context at this; omega

/-- A retained-context write preserves every arithmetic slot. -/
theorem high_write_low {n context size i d len : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (hs : Scr s base size) (hi : i < 9)
    (O : Outside base d len s.mem t.mem) (hd : context ≤ d) :
    wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have bound := L.slot hi
  have size := L.bound
  have nw := hs.nowrap
  exact O.wordsVal (.inl (by omega)) (by omega)

theorem encode_high {n context size d : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (hs : Scr s base size)
    (O : Outs base (encodeRanges n) s.mem t.mem) (hd : context ≤ d) (hz : d+8*n ≤ size) :
    wordsVal t.mem base d n = wordsVal s.mem base d n := by
  have a := L.slot (i := 5) (by decide)
  have b := L.slot (i := 6) (by decide)
  have c := L.slot (i := 1) (by decide)
  have d' := slot_bound (n := n) (i := 2) (by decide)
  have apart := L.apart
  unfold stride at d'
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [encodeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> right <;> omega
  · have := hs.nowrap; omega

theorem high_copy_ok {n context size m src dst : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (hb : src+8*n ≤ size) (hd : context ≤ dst) (hz : dst+8*n ≤ size)
    (sep : dst=src ∨ dst+8*n ≤ src ∨ src+8*n ≤ dst) :
    WP isa (copyWords n src dst) s fun t => Context n m base size t ∧
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      Outside base dst (8*n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.mono (copyWords_ok C.scr L.positive hb hz sep) fun t ⟨V, O, K⟩ =>
    ⟨outside_high_context L C K (by decide) (by decide) O hd, V, O, K⟩

/-- Enlarge disjoint write ranges without changing their meaning. -/
theorem widen {base : Addr} {rs qs : List (Nat × Nat)} {s t : Mem}
    (O : Outs base rs s t)
    (h : ∀ r ∈ rs, ∃ q ∈ qs, q.1 ≤ r.1 ∧ r.1+r.2 ≤ q.1+q.2) : Outs base qs s t := by
  intro x hx
  apply O x
  intro r hr
  obtain ⟨q, hq, lo, hi⟩ := h r hr
  have := hx q hq
  omega

end VG.Proof.Mont.X86.Comb
