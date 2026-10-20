module

public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-! # Checked public RSA from precomputed values, at a width read at run time (i686 cdecl)

`vg_rsa_public_precomputed_checked` as `PublicRt`'s operation, with the
modulus (number 0) and `R² mod M` (number 4) copied from `pre`, `n` words
of 64 bits each, in place of the modulus's import and the doublings. The
checks that the modulus is odd and above one, and `R² mod M` below it,
choose between the operation and the failure; they are on public values.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrecomputedRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicFn VG.Impl.Bignum.X86.PublicRt

/-- The header word holding the first check's mask. -/
def checkOffset : Nat := 148

/-- Number `j` from the words at `pre` (argument 2), `B` bytes into it when `hi`. -/
def copyIn (j : Nat) (hi : Bool) : Prog isa :=
  .seq (.block (slotPtr .ebp j .ecx ++ .mov .esi (.mem (argAt 0 2)) ::
      (if hi then [.alu .add .esi (.reg .ecx)] else [])))
    (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 4)]) .ne)

/-- The modulus (number 0), `R² mod M` (number 4) and one (number 3). -/
def importKey : Prog isa := .seq (copyIn 0 false) (.seq (copyIn 4 true) (setOne 3))

/-- ZF set unless one is below `M`, `R² mod M` below `M` and `M` odd. -/
def checks : Prog isa :=
  .seq (compareAt 3 0) <| .seq (.block [.store (sc checkOffset) .ecx]) <| .seq (compareAt 4 0) <|
  .block [.mov .edx (.mem (sc checkOffset)), .alu .and .ecx (.reg .edx), .mov .eax (.mem (sc numOff)),
    .alu .and .eax (.imm 1), .alu .and .ecx (.reg .eax), .alu .cmp .ecx (.imm 0)]

/-- The input read, its acceptance and `-M⁻¹ mod 2³²`. -/
def applyPrefix : Prog isa :=
  .seq (load 1 6 7) <| .seq compare <|
  .block ([.store (sc acceptanceOffset) .ecx] ++ VG.Impl.Mont.X86.Dynamic.setupInverse numOff invOff)

/-- The exponentiation and the result. -/
def applyInput : Prog isa := .seq applyPrefix (.seq exponentiate (.seq maskOut write))

def sized : Prog isa := .seq importKey (.seq checks (.ite .e failure applyInput))

def valid : Prog isa := .seq (.block saveExponent) sized

def body : Prog isa :=
  .seq scanExponent (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure valid))

def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.Bignum.X86.PrecomputedRt
