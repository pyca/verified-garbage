module

public import VerifiedGarbage.Impl.MlKem.X86_64.Decode12Avx2

/-!
# ML-KEM on x86-64: the key check with AVX2 (`vg_mlkem768_check_ek_avx2`, `vg_mlkem1024_check_ek_avx2`)

`checkEkAvx2K k (ek = rdi) -> rax`, for the rank `k`, is `checkEkK k`
(`CheckEk.lean`) on eight fields at a time: it splits each of the `32k`
groups of 12 bytes of `ek[0 : 384k]` into its eight 12-bit fields in the
doublewords of `ymm0`, as `vg_mlkem_decode12_avx2` does (`Decode12Avx2.lean`,
whose constants it builds), with `rcx` counting down. A load of the last
group reads 4 bytes past it, which are still in `ek` (its last 32 bytes are
`ρ`). `vpsubd` of `q` makes a field's doubleword negative exactly when the
field is less than `q`, and `vpand` keeps in `ymm2`, which starts with every
bit set, the doublewords' sign bits common to every group. After the loop,
`vpsrad` by 31 spreads each sign over its doubleword, and `vpmovmskb` gathers
the bytes' signs into `eax`: all 32 are set, `eax = 2³² - 1`, exactly when
the key passes the modulus check, and `(eax + 1) >> 32` returns 1 then and 0
otherwise, without a branch. Every address and branch depends only on the
pointer. It clears the upper halves of the vector registers before
returning (`vzeroupper`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The eight fields of the 12 bytes at `rdi` less `q`, their signs kept in `ymm2`. -/
def ckBody : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rdi 0), yb .vpshufb .xmm0 .xmm0 .xmm8, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    yb .vpand .xmm0 .xmm0 .xmm10, yb .vpsubd .xmm0 .xmm0 .xmm11, yb .vpand .xmm2 .xmm2 .xmm0,
    .alu .add .rdi (.imm 12), .alu .sub .rcx (.imm 1)]

/-- 1 if every sign in `ymm2` is set, and 0 otherwise. -/
def ckFin : List Instr :=
  [.vop (.vshift .psrad .l256 .xmm2 .xmm2 31), .vpmovmskb .l256 .rax .xmm2, .alu .add .rax (.imm 1),
    .shift .shr .rax 32, .vop .vzeroupper]

/-- The check of the `32k` groups of 12 bytes of `ek[0 : 384k]`, for the rank `k`. -/
def checkEkAvx2K (k : Nat) : Prog isa :=
  .seq (.block (d12Consts ++ yconst .xmm2 0xffffffff ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * k)))]))
    (.seq (.loop (.block ckBody) .ne) (.block ckFin))

/-- `vg_mlkem768_check_ek_avx2`. -/
abbrev checkEkAvx2 : Prog isa := checkEkAvx2K 3

end VG.Impl.MlKem.X86_64
