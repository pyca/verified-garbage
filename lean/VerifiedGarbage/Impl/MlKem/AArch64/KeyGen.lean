module

public import VerifiedGarbage.Impl.MlKem.AArch64.Lay
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Impl.MlKem.AArch64.Sample

/-!
# ML-KEM on AArch64: `vg_mlkem768_keygen` and `vg_mlkem1024_keygen`

`(L.keyGenWith c)(seed = x0, ek = x1, dk = x2, scratch = x3) -> x0`:
`KeyGen_internal(d, z)` (FIPS 203 Algorithms 16 and 13) of the parameter set
`L` (`KemLay`) with `d ‖ z` at `seed`, as calls of the
verified primitives and Keccak functions. We keep `seed`, `ek`, `dk` and
`scratch` in `x25`–`x28` and the AND of `sample_ntt`'s results in `x24`
(callee-saved, so the callees keep them), and save our caller's values of
them and of `x30` in `scratch`.

1. `(ρ, σ) = G(d ‖ k)`, into `ρ ‖ j ‖ i` (the seed of `Â[i, j]`) and
   `σ ‖ N` (the input of `PRF(σ, N)`) in `scratch`.
2. `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `(i, j)`.
3. `ŝ[j] = NTT(SamplePolyCBD₂(PRF₂(σ, j)))`, and `ByteEncode₁₂(ŝ[j])` into
   `dk`; then `ê[i]` likewise from `PRF₂(σ, k + i)`, and
   `t̂[i] = Â[i, 0] ŝ[0] + ⋯ + Â[i, k - 1] ŝ[k - 1] + ê[i]`, and
   `ByteEncode₁₂(t̂[i])` into `ek` and into `dk`'s copy of `ek`.
4. `ρ` into `ek` and `dk`, `H(ek)` into `dk`, and `z` into `dk`.

Returns 1 if every `SampleNTT` finished within 280 iterations, and 0 if not
(when `ek` and `dk` are then unspecified).

`scratch` holds, at these offsets: the Keccak state (0) and working space
(200), `ρ ‖ j ‖ i` (840), `σ ‖ N` (880), the byte `k` (920), `PRF`'s output
(928), `sample_ntt`'s working space (1056), the NTT's (3104), `Â` (4128, row
by row), and after it `ŝ`, `ê[i]`, `t̂[i]`, a product and the saved
registers (`KG`; for ML-KEM-768 at 13344, 16416, 17440, 18464 and 19488).

Only the calls of `sample_ntt` depend on `ρ` (which the contract declares
that the function may leak); every other address and branch depends only on
the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

namespace KG

def ST : Nat := 0
def WK : Nat := 200
def SB : Nat := 840
def SG : Nat := 880
def BK : Nat := 920
def PB : Nat := 928
def SS : Nat := 1056
def NS : Nat := 3104
def AH : Nat := 4128

variable (L : KemLay)

def SH : Nat := AH + 1024 * (L.k * L.k)
def EP : Nat := SH L + 1024 * L.k
def TP : Nat := EP L + 1024
def PP : Nat := TP L + 1024
def SV : Nat := PP L + 1024

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (L.k * i + j)
/-- `ŝ[j]`. -/
def sOff (j : Nat) : Nat := SH L + 1024 * j

end KG

open KG

/-- Copy the 32 bytes at `sb + so` to `db + do`. -/
def copy32 (sb : Reg) (so : Nat) (db : Reg) (dO : Nat) : List Instr :=
  (List.range 4).flatMap fun k => [.ldr .x .x9 sb (so + 8 * k), .str .x .x9 db (dO + 8 * k)]

namespace KemLay

variable (L : KemLay)

/-- Save our caller's registers, keep the pointers, and store the byte `k`. -/
def kgPrologue : List Instr :=
  [.str .x .x24 .x3 (SV L), .str .x .x25 .x3 (SV L + 8), .str .x .x26 .x3 (SV L + 16),
    .str .x .x27 .x3 (SV L + 24), .str .x .x28 .x3 (SV L + 32), .str .x .x30 .x3 (SV L + 40), mov .x25 .x0,
    mov .x26 .x1, mov .x27 .x2, mov .x28 .x3, .movz .x .x24 1 0, .movz .x .x9 (BitVec.ofNat 16 L.k) 0,
    .strb .x9 .x28 BK]

end KemLay

end VG.Impl.MlKem.AArch64
