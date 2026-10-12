module

public import VerifiedGarbage.Impl.Mont.X86_64

/-!
# P-384's `C [a] - D [b] mod p`, for small `C` and `D`, with BMI2 and ADX

`cms M o C a D b` computes `(C [a] - D [b]) mod p` for P-384's `p` and `C`,
`D` below `64` in one operation, rather than a chain of additions and
subtractions each with its own reduction: Jacobian doubling's linear
combinations (`12 X Y² - 9 (X² - Z⁴)²`, `4 X Y² - X₃`, `3 M (…) - 8 Y⁴`).

1. `p - [b]` into the temporary area (`p` from `[mo]`; `[b] < p`, so it never
   borrows);
2. `N = D (p - [b]) + C [a]`, below `2³⁹¹`, in `r8 … r15`: one row by `rowS0`,
   a second by `rowX`;
3. its words `h` above `2³⁸⁴` folded down by `2³⁸⁴ ≡ c (mod p)` for
   `c = 2³⁸⁴ - p` (`cmsFold`): `L + h c`, below `2p`;
4. `csub`.
-/

@[expose] public section

namespace VG.Impl.Mont.X86_64

open VG.X86_64

/-- `r8 … r13 + 2³⁸⁴ r14 = L + h c` for `L` in `r8 … r13`, `h` in `rdx` and
P-384's `c = 2³⁸⁴ - p`: `h` times `c`'s words `C0` and `C1` by `mulx`
(`madd`), times its word `1` added directly, and the carries up through
`r14`. -/
def cmsFold : List Instr :=
  [Impl.X25519.X86_64.clear, .movImm64 .rax sparseC0] ++ Impl.X25519.X86_64.madd .r8 .r9 (.reg .rax) ++
    ([.mov32 .rax (.imm sparseC1)] : List Instr) ++ Impl.X25519.X86_64.madd .r9 .r10 (.reg .rax) ++
    ([.adox .r10 (.reg .rdx), .mov32 .r14 (.imm 0),
      .adcx .r11 (.reg .rbp), .adox .r11 (.reg .rbp), .adcx .r12 (.reg .rbp), .adox .r12 (.reg .rbp),
      .adcx .r13 (.reg .rbp), .adox .r13 (.reg .rbp), .adcx .r14 (.reg .rbp), .adox .r14 (.reg .rbp)] : List Instr)

/-- `[o] = (C [a] - D [b]) mod p` for P-384's `p`, with BMI2 and ADX (`o` may
be `b`, but `a` must be apart from the temporary area). -/
def cms (M : Mod) (o C a D b : Nat) : List Instr :=
  loads (low 6) M.mo ++ chain .sub .sbb (low 6) b ++ stores (low 6) M.tmp ++
    ([.mov32 .rdx (.imm (BitVec.ofNat 32 D))] : List Instr) ++ rowS0 M.tmp ++
    ([.mov32 .rdx (.imm (BitVec.ofNat 32 C))] : List Instr) ++ rowX 6 (acc 6) a ++
    ([.mov .rdx (.reg .r14)] : List Instr) ++ cmsFold ++ csub M (low 6) .r14 ++ stores (low 6) o

end VG.Impl.Mont.X86_64
