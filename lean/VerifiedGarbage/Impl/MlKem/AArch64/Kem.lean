module

public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen

/-!
# ML-KEM on AArch64: what `encaps` and `decaps` share

Both keep four pointers in `x25`–`x28` (`scratch` in `x28`), the AND of
`sample_ntt`'s results in `x24`, and save our caller's values of these and
of `x30` in `scratch` (`kemPrologue`, `kemEpilogue`): the Keccak functions
keep these registers, and restore the others they use from memory. Both run K-PKE.Encrypt (FIPS 203
Algorithm 14) after sampling `Â` (from `ρ ‖ j ‖ i` at `SB`):
`ŷ`, `u` and `v`, with `r` at `RB`, and `ek`, `m` and the
ciphertext wherever the caller says, for the parameter set `L` (`KemLay`).

`scratch` holds, at these offsets: the Keccak state (0) and working space
(200), `ρ ‖ j ‖ i` (840), `H(ek)` (880), `m'` (912), `r ‖ N` (944), `K'`
(984), `K̄` (1016), `PRF`'s output (1048), `sample_ntt`'s working space
(1176), the NTT's (3224), `Â` (4248, row by row), and after it `ŷ`, a noise
polynomial, a sum of products, a product, `t̂[j]`, `c'` and the saved
registers (`KEM`; for ML-KEM-768 at 13464, 16536, 17560, 18584, 19608, 20632
and 21720).
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

namespace KEM

def ST : Nat := 0
def WK : Nat := 200
def SB : Nat := 840
def HB : Nat := 880
def MB : Nat := 912
def RB : Nat := 944
def KP : Nat := 984
def JB : Nat := 1016
def PB : Nat := 1048
def SS : Nat := 1176
def NS : Nat := 3224
def AH : Nat := 4248

variable (L : KemLay)

def YH : Nat := AH + 1024 * (L.k * L.k)
def EP : Nat := YH L + 1024 * L.k
def TP : Nat := EP L + 1024
def PP : Nat := TP L + 1024
def TH : Nat := PP L + 1024
def CB : Nat := TH L + 1024
def SV : Nat := CB L + L.ctLen

/-- `Â[i, j]`. -/
def aOff (i j : Nat) : Nat := AH + 1024 * (L.k * i + j)
/-- `ŷ[j]`. -/
def yOff (j : Nat) : Nat := YH L + 1024 * j

end KEM

open KEM

/-! ## Registers -/

/-- The callee-saved register that keeps pointer `k` (`scratch` is `k = 3`). -/
def slotReg (k : Nat) : Reg := [Reg.x25, .x26, .x27, .x28].getD k .x28

/-- The register argument `b` comes in. -/
def argReg (b : Nat) : Reg := [Reg.x0, .x1, .x2, .x3, .x4].getD b .x5

/-- The registers saved in `scratch`, `x28` last. -/
def kemOwn : List Reg := [.x24, .x30, .x25, .x26, .x27, .x28]

/-! ## Building blocks -/

/-- `f ← f - g`. -/
def subAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call "vg_mlkem_sub" sub)

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into `b + o`, by
the function `name` (`code`). -/
def ceWith (name : String) (code : Prog isa) (off d : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ (.movz .x .x1 (BitVec.ofNat 16 d) 0 :: ptrTo .x2 b o) ++
      ([.movz .x .x3 (BitVec.ofNat 16 (32 * d)) 0] : List Instr)))
    (.call name code)

/-- `Decompress_d(ByteDecode_d(b + o))` into the polynomial at `off`, by the
function `name` (`code`). -/
def ddWith (name : String) (code : Prog isa) (b : Reg) (o d off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ([.movz .x .x1 (BitVec.ofNat 16 (32 * d)) 0,
      .movz .x .x2 (BitVec.ofNat 16 d) 0] : List Instr) ++ ptrTo .x3 .x28 off))
    (.call name code)

/-- `ByteEncode_d(Compress_d(f))`, for the widths of ML-KEM-768 (here `d = 1`). -/
abbrev ceAt := ceWith "vg_mlkem_compress_encode" compressEncode

/-- `Decompress_d(ByteDecode_d(b + o))`, for the widths of ML-KEM-768 (here `d = 1`). -/
abbrev ddAt := ddWith "vg_mlkem_decode_decompress" decodeDecompress

/-- `vg_mlkem<n>_encaps_h(ek = x0, h = x1, m = x2, key = x3, ct = x4, scratch = x5)`'s arguments moved to
`encaps`'s (`m`, `key`, `ct` and `scratch` in `x1`–`x4`), `h` unused: `encaps_h` is `encaps` after these
moves. -/
def hArgs : List Instr := [mov .x1 .x2, mov .x2 .x3, mov .x3 .x4, mov .x4 .x5]

namespace KemLay

variable (L : KemLay)

/-- Save our caller's registers in `scratch` (argument `sc`), keep the
arguments `slots` in `x25`–`x28`, and set `x24` to 1. -/
def kemPrologue (sc : Nat) (slots : List Nat) : List Instr :=
  (List.range 6).map (fun k => .str .x (kemOwn.getD k .x0) (argReg sc) (SV L + 8 * k)) ++
    (List.range 4).map (fun k => mov (slotReg k) (argReg (slots.getD k 0))) ++ [.movz .x .x24 1 0]

/-- The result (`x24`) in `x0`, and our caller's registers back (`x28` last). -/
def kemEpilogue : List Instr :=
  mov .x0 .x24 :: (List.range 6).map fun k => .ldr .x (kemOwn.getD k .x0) .x28 (SV L + 8 * k)

/-- `ByteEncode_d(Compress_d(f))` at the widths `d_u` and `d_v`. -/
abbrev ceLAt := ceWith L.ceName L.ce

/-- `Decompress_d(ByteDecode_d(b + o))` at the widths `d_u` and `d_v`. -/
abbrev ddLAt := ddWith L.ddName L.dd

end KemLay

end VG.Impl.MlKem.AArch64
