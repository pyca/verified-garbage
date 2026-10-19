module
public import VerifiedGarbage.Impl.Bignum.X86.WideProduct
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.X86.WideRow
import VerifiedGarbage.Proof.Bignum.WideBounds
import VerifiedGarbage.Proof.Mont.X86.Dynamic

/-! # Terminating schoolbook multiplication over a public operand width -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic (outs2_val32 outs2_w32)

structure WideLayout (N bytes out a b mult : Nat) : Prop where
  aBound : a + 4 * N ≤ bytes
  bBound : b + 4 * N ≤ bytes
  outBound : out + 4 * (2 * N + 1) ≤ bytes
  multBound : mult + 4 ≤ bytes
  aOut : a + 4 * N ≤ out ∨ out + 4 * (2 * N + 1) ≤ a
  bOut : b + 4 * N ≤ out ∨ out + 4 * (2 * N + 1) ≤ b
  aMult : mult + 4 ≤ a ∨ a + 4 * N ≤ mult
  bMult : mult + 4 ≤ b ∨ b + 4 * N ≤ mult
  multOut : mult + 4 ≤ out ∨ out + 4 * (2 * N + 1) ≤ mult

structure WideInv (base : Addr) (N out a b mult i : Nat) (s t : State) : Prop where
  pointer : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * i)
  value : val32 t.mem base out (2 * N + 1) = val32 s.mem base a i * val32 s.mem base b N
  mem : Outs base [(out, 4 * (2 * N + 1)), (mult, 4)] s.mem t.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t

theorem wideLoop_ok {s t : State} {base : Addr} {bytes N out a b mult : Nat}
    (hs : Scr s base bytes) (hn : 0 < N) (L : WideLayout N bytes out a b mult)
    (init : WideInv base N out a b mult 0 s t) :
    WP isa (.loop (wideProductRow N out a b mult) .ne) t (WideInv base N out a b mult N s) := by
  have nw := hs.nowrap
  refine WP.loop (M := isa)
    (fun k u => ∃ i, k = N - i ∧ i < N ∧ WideInv base N out a b mult i s u)
    ?_ N t ⟨0, rfl, hn, init⟩
  rintro k u ⟨i, rfl, hi, I⟩
  have Hu := hs.of_keeps I.keeps (by decide)
  have B : val32 u.mem base b N = val32 s.mem base b N :=
    outs2_val32 I.mem L.bOut (by have := L.bMult; omega) (by have := L.bBound; omega)
  have A : w32 u.mem base (a + 4 * i) = w32 s.mem base (a + 4 * i) :=
    outs2_w32 I.mem (by have := L.aOut; omega) (by have := L.aMult; omega)
      (by have := L.aBound; omega)
  refine WP.mono (wideRow_ok Hu hi I.pointer L.aBound L.bBound L.outBound L.multBound
    L.bOut L.bMult L.multOut (by rw [A, B]; exact wide_row_bound hi I.value))
    fun v ⟨P, Z, V, O, K⟩ => ?_
  have next : WideInv base N out a b mult (i + 1) s v := by
    refine ⟨P, ?_, I.mem.trans O, I.keeps.trans K⟩
    rw [V, I.value, A, B, val32_succ, Nat.add_mul, Nat.mul_assoc]
  by_cases done : i + 1 = N
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, N - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

end VG.Proof.Bignum.X86
