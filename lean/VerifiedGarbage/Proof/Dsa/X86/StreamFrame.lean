module

public import VerifiedGarbage.Proof.Dsa.X86.StreamStep
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Input and header preservation during streaming reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

structure StreamInput (s : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  fit : p.toNat + len ≤ 2 ^ 32
  read : ∀ i < len, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1
  far : ∀ i < len, size ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i)

theorem StreamInput.keep {s t : State} {base : Addr} {size len : Nat} {p : BitVec 32}
    (I : StreamInput s base size p len) {rs : List Reg} (K : Keeps rs s t) : StreamInput t base size p len :=
  ⟨I.fit, by rw [K.2.1, K.2.2]; exact I.read, I.far⟩

theorem streamRanges_whole {n size : Nat} {base : Addr} {s t : State}
    (h : contextBytes n ≤ size) (O : Outs base (streamRanges n) s.mem t.mem) : Outside base 0 size s.mem t.mem := by
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  intro x hx
  apply O x
  intro r hr
  simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [stride] at b1 b2 b6 b7
  rcases hr with rfl | rfl | rfl | rfl <;> omega

theorem StreamInput.byte {s t : State} {base : Addr} {size len i : Nat} {p : BitVec 32}
    (I : StreamInput s base size p len) (hi : i < len) (O : Outside base 0 size s.mem t.mem) :
    t.mem (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
  O _ (.inr (by simpa only [Nat.zero_add] using I.far i hi))

theorem StreamInput.bytes {s t : State} {base : Addr} {size len : Nat} {p : BitVec 32}
    (I : StreamInput s base size p len) (O : Outside base 0 size s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (p.setWidth 64) len = Spec.Rsa.bytesAt s.mem (p.setWidth 64) len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact I.byte (List.mem_range.mp hi) O

theorem streamRanges_constants {n j size : Nat} {base : Addr} {s t : State}
    (O : Outs base (streamRanges n) s.mem t.mem) (hj : j = 3 ∨ j = 4) (hz : contextBytes n ≤ size)
    (hn : base.toNat + size ≤ 2 ^ 32) :
    wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
  have h1 := slot_le (n := n) (i := 1) (j := j) (by omega)
  have h2 := slot_le (n := n) (i := 2) (j := j) (by omega)
  have h6 := slot_le (n := n) (i := j) (j := 6) (by omega)
  have h7 := slot_le (n := n) (i := j) (j := 7) (by omega)
  have bd := slot_bound (n := n) (i := j) (by omega)
  simp only [stride] at *
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> omega
  · omega

end VG.Proof.Dsa.X86
