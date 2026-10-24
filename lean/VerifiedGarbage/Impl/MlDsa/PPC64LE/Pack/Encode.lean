module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Stream
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-DSA on PPC64LE: `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack`, `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

As on 32-bit ARM (`Impl/MlDsa/Arm/Pack/Encode.lean`): each branches on its
public width argument (a `u32`, compared in its low 32 bits) to a loop of
`Stream.lean` for that width `d`, with groups of `c` coefficients and `nb`
bytes: `(d, c, nb)` is `(3, 8, 3)`, `(4, 2, 1)`, `(6, 4, 3)`, `(10, 4, 5)`,
`(13, 8, 13)`, `(18, 4, 9)` or `(20, 2, 5)`. The functions use only
volatile registers, and no stack. Each first moves its polynomial or
coefficient pointer to `r10` and its other pointer to `r11`.

* `simpleBitPack(f = r3, b = r4, out = r5, len = r6)`: the value of a
  coefficient is the coefficient.
* `bitPack(f = r3, a = r4, b = r5, out = r6, len = r7)`: the value of a
  reduced coefficient `x` is `b - (x mod± q)`, which is `b - x` if `x ≤ b`
  and `b - x + q` otherwise: `b - x`, and `q` added if it is negative
  (`bMinus`), with `b` as a constant in `r4` and `q` in `r7`.
* `bitUnpack(v = r3, len = r4, a = r5, b = r6, f = r7)`: the coefficient of a
  field `x` is `b - x` modulo `q`, computed the same way.
* `unpackT1(v = r3, f = r4)`: the coefficient of a 10-bit field `x` is
  `x · 2¹³` (less than `q`), a shift.

Every address and branch depends only on the pointers and the widths.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Pack

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- `p` if the low 32 bits of `r` are `v`, else `e` (`r9` a temporary). -/
def sel (r : Reg) (v : Nat) (p e : Prog isa) : Prog isa :=
  .seq (.block (loadB .r9 v ++ ([.sub .r9 r .r9] : List Instr))) (.ite (.zero .w .r9) p e)

/-! ## `vg_mldsa_simple_bit_pack` -/

/-- Coefficient `j` of the group at `r10`, into `r9`. -/
def sbpLd (j : Nat) : List Instr := [.load .w .r9 .r10 (4 * j)]

def simpleBitPack : Prog isa :=
  .seq (.block [mov .r10 .r3, mov .r11 .r5])
    (sel .r4 15 (packLoop sbpLd 4 2 1) (sel .r4 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5)))

/-! ## `vg_mldsa_bit_pack` -/

/-- `b - (x mod± q)` of the coefficient `x` `j` of the group at `r10`, into
`r9`. -/
def bpLd (j : Nat) : List Instr := .load .w .r9 .r10 (4 * j) :: bMinus

/-- `b = B` into `r4`, then the loop. -/
def withB (B : Nat) (p : Prog isa) : Prog isa := .seq (.block (loadB .r4 B)) p

def bitPack : Prog isa :=
  .seq (.block ([mov .r10 .r3, mov .r11 .r6] ++ loadQ))
    (sel .r5 2 (withB 2 (packLoop bpLd 3 8 3))
      (sel .r5 4 (withB 4 (packLoop bpLd 4 2 1))
        (sel .r5 4096 (withB 4096 (packLoop bpLd 13 8 13))
          (sel .r5 131072 (withB 131072 (packLoop bpLd 18 4 9)) (withB 524288 (packLoop bpLd 20 2 5))))))

/-! ## `vg_mldsa_bit_unpack` -/

/-- `b - x` modulo `q` of the field `x` in `r9`, to coefficient `j` of the
group at `r11`. -/
def buFin (j : Nat) : List Instr := bMinus ++ ([.store .w .r9 .r11 (4 * j)] : List Instr)

def bitUnpack : Prog isa :=
  .seq (.block ([mov .r10 .r3, mov .r11 .r7] ++ loadQ))
    (sel .r6 2 (withB 2 (unpackLoop buFin 3 8 3))
      (sel .r6 4 (withB 4 (unpackLoop buFin 4 2 1))
        (sel .r6 4096 (withB 4096 (unpackLoop buFin 13 8 13))
          (sel .r6 131072 (withB 131072 (unpackLoop buFin 18 4 9)) (withB 524288 (unpackLoop buFin 20 2 5))))))

/-! ## `vg_mldsa_unpack_t1` -/

/-- `x · 2¹³` of the 10-bit field `x` in `r9`, to coefficient `j` of the
group at `r11`. -/
def t1Fin (j : Nat) : List Instr := [.lsl .r9 .r9 13, .store .w .r9 .r11 (4 * j)]

def unpackT1 : Prog isa := .seq (.block [mov .r10 .r3, mov .r11 .r4]) (unpackLoop t1Fin 10 4 5)

end VG.Impl.MlDsa.PPC64LE.Pack
