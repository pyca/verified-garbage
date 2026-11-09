module

public import VerifiedGarbage.Proof.Mont.X86.Dynamic
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.Omega

/-! # Memory operands past the working space

`ArgFar`: the bytes a memory operand reads lie past the working space, so it
reads the same while code writes only ranges of the working space
(`readSrc_keep`, `ArgFar.keep`); and the reads of pointers into it
through an update of another register (`readSrc_upd`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The 4 bytes a memory operand reads lie past the working space. -/
def ArgFar (s : State) (base : Addr) (size : Nat) (m : MemOp) : Prop :=
  ∀ j < 4, size ≤ ofs base (s.ea m + BitVec.ofNat 64 j)

/-- A memory operand past the working space reads the same after changes
within ranges of the working space, with its base register and the
permissions as they were. -/
theorem readSrc_keep {s t : State} {base : Addr} {size : Nat} {rs : List (Nat × Nat)} {m : MemOp}
    (hf : ArgFar s base size m) (O : Outs base rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ size)
    (hb : t.gpr m.base = s.gpr m.base) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    readSrc t (.mem m) = readSrc s (.mem m) := by
  have he : t.ea m = s.ea m := by simp only [State.ea, hb]
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  simp only [State.load32, he, hrd, hwr]
  congr 1
  refine congrArg some (Mem.readW_congr fun i hi => O _ fun r hr' => .inr ?_)
  have := hf i (by omega)
  have := hr r hr'
  omega

theorem ArgFar.keep {s t : State} {base : Addr} {size : Nat} {m : MemOp} (hf : ArgFar s base size m)
    (hb : t.gpr m.base = s.gpr m.base) : ArgFar t base size m := by
  intro j hj
  have he : t.ea m = s.ea m := by simp only [State.ea, hb]
  rw [he]; exact hf j hj

/-- A memory operand reads the same after a write of another register. -/
theorem readSrc_upd {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v) {m : MemOp} (h : m.base ≠ d) :
    readSrc t (.mem m) = readSrc s (.mem m) := by
  show t.load32 (t.ea m) = s.load32 (s.ea m)
  have he : t.ea m = s.ea m := by simp only [State.ea, u.other _ h]
  rw [he]
  simp only [State.load32, u.mem, u.rd, u.wr]

end VG.Proof.Mont.X86.Dynamic
