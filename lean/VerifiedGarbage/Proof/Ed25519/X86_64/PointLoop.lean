module

public import VerifiedGarbage.Impl.Ed25519.X86_64.PointLoop
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Sixteen exact doublings, preserving the saved accumulator. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (clob Outside Keeps)

variable {fld : Arith} [EdArith fld]

structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rsi → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : DoubleKeep base s t)
    (k : DoubleKeep base t u) : DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : DoubleKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_zero : ∀ n < 16,
    (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

end VG.Proof.Ed25519.X86_64
