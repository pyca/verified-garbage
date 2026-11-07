module

public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset

/-! # The stack a call uses, apart from the working space

`CallRoom sp base size`: the bytes below `sp` that a call and its callee
use lie apart from the working space at `base`; and `Outs.widen`, changes
within some ranges as changes within ranges covering them. -/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.Proof.Mont

/-- The 96 bytes below `sp`, which a call and its callee use (a frame of 36
bytes of arguments, the return address and the callee's 56), are apart from
the working space. -/
structure CallRoom (sp : BitVec 32) (base : Addr) (size : Nat) : Prop where
  low : 96 ≤ sp.toNat
  apart : Region.Disjoint (below sp 96) ⟨base, size⟩

/-- The 40 bytes of a call's frame and return address, below `sp`, are apart
from the working space. -/
theorem CallRoom.apart40 {sp : BitVec 32} {base : Addr} {size : Nat} (R : CallRoom sp base size) :
    Region.Disjoint (below sp 40) ⟨base, size⟩ :=
  R.apart.sub_left (below_sub (by decide) R.low)

/-- Changes within some ranges, as changes within ranges covering them. -/
theorem Outs.widen {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    Outs base rs' m₁ m₂ :=
  fun x hx => h x (hr _ hx)

end VG.Proof.Mont.X86
