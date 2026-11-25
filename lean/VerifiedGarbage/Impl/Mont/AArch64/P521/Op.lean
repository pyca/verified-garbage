module

public import VerifiedGarbage.Impl.Mont.AArch64

/-!
# Straight-line carry arithmetic, as data (AArch64)

The scalar operations P-521's field arithmetic is made of (`Op`), apart from
its stores: 64-bit, each writing one register, with loads of word `i` of
operand `k` in place of addresses, so that a sequence of them is closed data
whatever slots it works on. `Op.instr` is the instruction, for the operands'
pointers and offsets.
-/

@[expose] public section

namespace VG.Impl.Mont.AArch64.P521

open VG.AArch64

/-- An operation, its destination first. -/
inductive Op
  /-- Word `i` of operand `k`. -/
  | ld (k i : Nat) (d : Reg)
  | mul (d n m : Reg)
  | umulh (d n m : Reg)
  | add (d n m : Reg)
  | adds (d n m : Reg)
  | adcs (d n m : Reg)
  | adc (d n m : Reg)
  | subs (d n m : Reg)
  | sbcs (d n m : Reg)
  | lsl (d n : Reg) (k : Nat)
  | lsr (d n : Reg) (k : Nat)
  | extr (d n m : Reg) (k : Nat)
  /-- A constant below `2¹⁶`. -/
  | movz (d : Reg) (v : Nat)
  /-- The low `k` bits of `n`, by the mask `2^k - 1` in `m`. -/
  | low (d n m : Reg) (k : Nat)
  deriving Repr, Inhabited

/-- The instruction, for operands at `(ptr k).1 + (ptr k).2`. -/
def Op.instr (ptr : Nat → Reg × Nat) : Op → Instr
  | .ld k i d => .ldr .x d (ptr k).1 ((ptr k).2 + 8 * i)
  | .mul d n m => .mul .x d n m
  | .umulh d n m => .umulh d n m
  | .add d n m => .add .x d n m
  | .adds d n m => .adds .x d n m
  | .adcs d n m => .adcs .x d n m
  | .adc d n m => .adc .x d n m
  | .subs d n m => .subs .x d n m
  | .sbcs d n m => .sbcs .x d n m
  | .lsl d n k => .lsl .x d n k
  | .lsr d n k => .lsr .x d n k
  | .extr d n m k => .extr .x d n m k
  | .movz d v => .movz .x d (BitVec.ofNat 16 v) 0
  | .low d n m _ => .logic .and .x d n m

/-- The register written. -/
def Op.dst : Op → Reg
  | .ld _ _ d | .mul d _ _ | .umulh d _ _ | .add d _ _ | .adds d _ _ | .adcs d _ _ | .adc d _ _
  | .subs d _ _ | .sbcs d _ _ | .lsl d _ _ | .lsr d _ _ | .extr d _ _ _ | .movz d _ | .low d _ _ _ => d

end VG.Impl.Mont.AArch64.P521
