import VerifiedGarbage.Impl.Mont.X86_64

/-!
# P-521's field multiplication and squaring as functions, x86-64 with BMI2 and ADX

`vg_p521_mul_mont_adx(out, a, b)` and `vg_p521_sqr_mont_adx(out, a)`
(`Spec/P521/Field.lean`): the rows, reduction and final reduction of
`mulPX` and `sqrPX` (`Impl/Mont/X86_64.lean`), which the curve's operations
inline, as functions they call. The rows read `a` through `rsi` and `b`
through `rbx` (`rcR`), where the multiplication moves it from `rdx`, which
`mulx` reads; the product's low words go to `out` (`[rdi]`), which `out`
being apart from `a` and `b` lets serve as the temporary area, and the
reduction leaves the result there. The registers of the accumulator that
the calling convention preserves are saved on the stack, one frame each.
-/

namespace VG.Impl.P521Field.X86_64

open VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64

/-- P-521's arithmetic with its temporary area at `[rdi]`: what the rows
and the reduction read of it. -/
def fm : Mod := { n := 9, mo := 0, tmp := 0, minv := 1, red := .friendly p521Ws, adx := true }

/-- `body` in a frame for each register of `rs`, the first outermost. -/
def frames (body : Prog isa) : List Reg → Prog isa
  | [] => body
  | r :: rs => .frame (.push [r]) (frames body rs) (.pop r 1)

/-- `[rdi] = [rsi] [rdx] R⁻¹ mod p`: `b` into `rbx`, then `mulPX`'s rows
(`a` through `rsi`, `b` through `rbx`), reduction and final reduction. -/
def mulBody : List Instr :=
  [.mov .rbx (.reg .rdx)] ++ (List.range 9).flatMap (xRowV fm .rsi .rbx 0 0 0) ++ xRed fm 0 ++
    xCanon 0 0

/-- `[rdi] = [rsi]² R⁻¹ mod p`: `sqrPX`'s products of two different words
(`a` through `rsi`), squares, reduction and final reduction. -/
def sqrBody : List Instr :=
  (List.range 8).flatMap (sRowV fm .rsi 0 0) ++ sDiag fm .rsi 0 0 ++ xRed fm 0 ++ xCanon 0 0

/-- `vg_p521_mul_mont_adx`: `mulBody`, saving `rbx`, `rbp` and `r12`–`r15`. -/
def mulCode : Prog isa := frames (.block mulBody) [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `vg_p521_sqr_mont_adx`: `sqrBody`, saving `rbp` and `r12`–`r15`. -/
def sqrCode : Prog isa := frames (.block sqrBody) [.rbp, .r12, .r13, .r14, .r15]

end VG.Impl.P521Field.X86_64
