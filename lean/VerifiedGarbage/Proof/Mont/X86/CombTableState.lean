module

public import VerifiedGarbage.Proof.Mont.X86.CombFrame
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Partial comb tables and their preservation by shared arithmetic. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def tableValue (n m g bits j : Nat) : Nat :=
  Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent bits j) m * 2^(64*n) % m

def TableAt (n context m g bits : Nat) (base : Addr) (known : Nat → Prop) (mem : Mem) : Prop :=
  ∀ j < 32, known j → wordsVal mem base (entry n (context+16*n) j) n = tableValue n m g bits j

theorem TableAt.outside {n context size m g bits d len : Nat} {base : Addr} {known : Nat → Prop} {s t : State}
    (T : TableAt n context m g bits base known s.mem) (L : Layout n context size) (hs : Scr s base size)
    (O : Outside base d len s.mem t.mem) (sep : d+len ≤ context+16*n ∨ context+272*n ≤ d) :
    TableAt n context m g bits base known t.mem := by
  intro j hj hk
  have ent := L.entry hj
  have bound := L.bound
  have nw := hs.nowrap
  rw [O.wordsVal (by omega) (by omega)]
  exact T j hj hk

theorem TableAt.outs {n context size m g bits : Nat} {base : Addr} {known : Nat → Prop} {s t : State}
    (T : TableAt n context m g bits base known s.mem) (L : Layout n context size) (hs : Scr s base size)
    {ranges : List (Nat × Nat)} (O : Outs base ranges s.mem t.mem)
    (sep : ∀ r ∈ ranges, r.1+r.2 ≤ context+16*n ∨ context+272*n ≤ r.1) :
    TableAt n context m g bits base known t.mem := by
  intro j hj hk
  have ent := L.entry hj
  have bound := L.bound
  have nw := hs.nowrap
  rw [wordsVal_eq_val32, O.val32 (by intro r hr; have := sep r hr; omega) (by omega), ← wordsVal_eq_val32]
  exact T j hj hk

theorem TableAt.op {n context size m g bits o : Nat} {base : Addr} {known : Nat → Prop} {s t : State}
    (T : TableAt n context m g bits base known s.mem) (L : Layout n context size)
    (C : Context n m base size s) (ho : o < 9)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) :
    TableAt n context m g bits base known t.mem := by
  intro j hj hk
  have ent := L.entry hj
  have apart := L.apart
  have bound := L.bound
  rw [op_high C ho K (by omega) (by omega)]
  exact T j hj hk

theorem select_table_ok {n context size m g bits o : Nat} {base : Addr} {known : Nat → Prop} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (T : TableAt n context m g bits base known s.mem)
    (ho : o < 9) (ho0 : o ≠ 0) (idx : w32 s.mem base 4 < 32) (hk : known (w32 s.mem base 4)) :
    WP isa (VG.Impl.Mont.X86.Comb.publicSelect n (context+16*n) (slot n o)) s fun t =>
      Context n m base size t ∧ TableAt n context m g bits base known t.mem ∧
      wordsVal t.mem base (slot n o) n = tableValue n m g bits (w32 s.mem base 4) ∧
      Outside base (slot n o) (8*n) s.mem t.mem ∧ Keeps [.eax,.ebx,.ecx,.edx,.ebp] s t := by
  have ent := L.entry idx
  have bound := L.bound
  have out := L.slot ho
  have header := slot_header n o
  have sep := slot_sep (n := n) ho0
  have cbound := C.size_le
  have head := slot_header n 9
  refine WP.mono (publicSelect_ok C.scr L.positive (by change slot n 9 ≤ size at cbound; omega)
    (by omega) (by omega) (.inl (by omega))) fun t ⟨O,V,K⟩ => ?_
  refine ⟨C.outside_keep K (by decide) (by decide) O ?_ (by omega),
    T.outside L C.scr O (.inl (by omega)), V.trans (T _ idx hk), O, K⟩
  unfold stride at sep
  omega

end VG.Proof.Mont.X86.Comb
