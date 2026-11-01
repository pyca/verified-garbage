module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Stream

/-!
# ML-DSA on RISC-V: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

As on PPC64LE (`Impl/MlDsa/PPC64LE/Pack/Encode.lean`): each branches on its
public width argument (a `u32`, compared in its low 32 bits by a `subw`) to a loop of
`Stream.lean` for that width `d`, with groups of `c` coefficients and `nb`
bytes: `(d, c, nb)` is `(3, 8, 3)`, `(4, 2, 1)`, `(6, 4, 3)`, `(10, 4, 5)`,
`(13, 8, 13)`, `(18, 4, 9)` or `(20, 2, 5)`. The functions use only
volatile registers, and no stack. Each first moves its polynomial or
coefficient pointer to `a7` and its other pointer to `t1`.

* `simpleBitPack(f = a0, b = a1, out = a2, len = a3)`: the value of a
  coefficient is the coefficient.
* `bitPack(f = a0, a = a1, b = a2, out = a3, len = a4)`: the value of a
  reduced coefficient `x` is `b - (x mod± q)`, which is `b - x` if `x ≤ b`
  and `b - x + q` otherwise: `b - x`, and `q` added if it is negative
  (`bMinus`), with `b` as a constant in `a1` and `q` in `a4`.
* `bitUnpack(v = a0, len = a1, a = a2, b = a3, f = a4)`: the coefficient of a
  field `x` is `b - x` modulo `q`, computed the same way.
* `unpackT1(v = a0, f = a1)`: the coefficient of a 10-bit field `x` is
  `x · 2¹³` (less than `q`), a shift.

Every address and branch depends only on the pointers and the widths.
-/

@[expose] public section

namespace VG.Impl.MlDsa.RISCV64.Pack

open VG.RISCV64

/-- `p` if the low 32 bits of `r` are `v`, else `e` (`a6` a temporary). -/
def sel (r : Reg) (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block (loadB .a6 v ++ ([.sub .a6 r .a6] : List Instr))) (.ite (.zero .a6) p e)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `a7`, into `a6`. -/
def sbpLd (j : Nat) : List Instr := [.load .w .a6 .a7 (4 * j)]

def simpleBitPack : Prog isa :=
  .seq (.block [.addi .a7 .a0 0, .addi .t1 .a2 0])
    (sel .a1 15 (packLoop sbpLd 4 2 1) (sel .a1 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5)))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `a7`, into
`a6`. -/
def bpLd (j : Nat) : List Instr := .load .w .a6 .a7 (4 * j) :: bMinus

/-- `b = B` into `a1`, then the loop. -/
def withB (B : Nat) (p : Prog isa) : Prog isa := .seq (.block (loadB .a1 B)) p

def bitPack : Prog isa :=
  .seq (.block ([.addi .a7 .a0 0, .addi .t1 .a3 0] ++ loadQ))
    (sel .a2 2 (withB 2 (packLoop bpLd 3 8 3))
      (sel .a2 4 (withB 4 (packLoop bpLd 4 2 1))
        (sel .a2 4096 (withB 4096 (packLoop bpLd 13 8 13))
          (sel .a2 131072 (withB 131072 (packLoop bpLd 18 4 9)) (withB 524288 (packLoop bpLd 20 2 5))))))

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `a6`, to coefficient `j` of the
group at `t1`. -/
def buFin (j : Nat) : List Instr := bMinus ++ ([.store .w .a6 .t1 (4 * j)] : List Instr)

def bitUnpack : Prog isa :=
  .seq (.block ([.addi .a7 .a0 0, .addi .t1 .a4 0] ++ loadQ))
    (sel .a3 2 (withB 2 (unpackLoop buFin 3 8 3))
      (sel .a3 4 (withB 4 (unpackLoop buFin 4 2 1))
        (sel .a3 4096 (withB 4096 (unpackLoop buFin 13 8 13))
          (sel .a3 131072 (withB 131072 (unpackLoop buFin 18 4 9)) (withB 524288 (unpackLoop buFin 20 2 5))))))

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `a6`, to coefficient `j` of the
group at `t1`. -/
def t1Fin (j : Nat) : List Instr := [.shift .sll .d .a6 .a6 13, .store .w .a6 .t1 (4 * j)]

def unpackT1 : Prog isa := .seq (.block [.addi .a7 .a0 0, .addi .t1 .a1 0]) (unpackLoop t1Fin 10 4 5)

end VG.Impl.MlDsa.RISCV64.Pack
