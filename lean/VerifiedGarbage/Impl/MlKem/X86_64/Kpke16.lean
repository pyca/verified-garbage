module

public import VerifiedGarbage.Impl.MlKem.X86_64.Kem

/-!
# ML-KEM on x86-64: K-PKE in one call, with 16-bit polynomials

`vg_mlkem*_kpke_decrypt(m = rdi, s = rsi, ct = rdx, scratch = rcx)`
(`Spec/MlKem/Kpke16.lean`): `K-PKE.Decrypt(dk_PKE, c)` (FIPS 203
Algorithm 15) of the parameter set `L`, with the arithmetic of `A`, calling
no function: it runs the code of the polynomial primitives inline, one
after the other, on polynomials in `scratch`. It keeps `scratch` in `rbx`,
`s` in `rbp`, `m` in `r12` and `ct` in `r13`, and saves its caller's values
of them at `scratch + 14336`.

The layout of `scratch` (16 KiB): the working space of
`vg_mlkem*_decrypt_mul` at 0 (4096 bytes); `u'[i]` in polynomial `i`
(`qP i`, 1024 bytes each from 4096), `ŝ[i]` in polynomial `k + i`,
`NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` in polynomial `2k` and `v'` in polynomial `2k + 1`;
the saved registers at 14336.

1. `u'[i] = Decompress_{d_u}(ByteDecode_{d_u}(c[32 d_u i : 32 d_u (i + 1)]))`;
2. `ŝ[i] = ByteDecode₁₂(dk_PKE[384i : 384i + 384])`;
3. `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` (the code of `vg_mlkem*_decrypt_mul`, with its own
   MXCSR region);
4. `v' = Decompress_{d_v}(ByteDecode_{d_v}(c[32 d_u k :]))`;
5. `w = v' - NTT⁻¹(ŝ^⊺ ∘ NTT(u'))`, and `m = ByteEncode₁(Compress₁(w))`.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Kpke16

/-- The saved registers. -/
def oKS : Nat := 14336

/-- Polynomial `i` of the working space. -/
def oQ (i : Nat) : Nat := 4096 + 1024 * i

/-- Polynomial `i` of the working space, as a pointer. -/
abbrev qP (i : Nat) : Ptr := (.rbx, oQ i)

/-- The callee-saved registers the function uses. -/
def kRegs : List Reg := [.rbx, .rbp, .r12, .r13]

/-- Save `kRegs` at `scratch + oKS`, and move the arguments to them. -/
def pro : List Instr :=
  (List.range 4).map (fun i => .store (at_ .rcx (oKS + 8 * i)) (kRegs.getD i .rbx)) ++
    [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rdx)]

/-- Restore `kRegs` (`rbx` last). -/
def epi : List Instr :=
  [.mov .r13 (.mem (at_ .rbx (oKS + 24))), .mov .r12 (.mem (at_ .rbx (oKS + 16))),
    .mov .rbp (.mem (at_ .rbx (oKS + 8))), .mov .rbx (.mem (at_ .rbx oKS))]

variable (L : Kem) (A : Arith)

/-- `Decompress_d(ByteDecode_d(b))` to `f`, inline, for `d = d_u` or `d_v`. -/
def ddIn (b : Ptr) (d : Nat) (f : Ptr) : Prog isa :=
  .seq (.block (lea .rdi b ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))), .mov32 .rdx (.imm (BitVec.ofNat 32 d))] ++
      lea .rcx f))
    (L.dd A.codecs)

/-- `u'[i]`. -/
def uHat (i : Nat) : Prog isa := ddIn L A (.r13, 32 * L.du * i) L.du (qP i)

/-- `ŝ[i]`. -/
def sHat (i : Nat) : Prog isa := .seq (.block (lea .rdi (.rbp, 384 * i) ++ lea .rsi (qP (L.k + i)))) A.dec12

/-- `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` to polynomial `2k`. -/
def prod : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k)) ++ lea .rsi (qP L.k) ++ lea .rdx (qP 0) ++ lea .rcx (.rbx, 0)))
    (A.decMul L.k)

/-- `v'` to polynomial `2k + 1`. -/
def vHat : Prog isa := ddIn L A (.r13, 32 * L.du * L.k) L.dv (qP (2 * L.k + 1))

/-- `w = v' - NTT⁻¹(ŝ^⊺ ∘ NTT(u'))`, in polynomial `2k + 1`. -/
def wSub : Prog isa := .seq (.block (lea .rdi (qP (2 * L.k + 1)) ++ lea .rsi (qP (2 * L.k)))) A.sub

/-- `m = ByteEncode₁(Compress₁(w))`. -/
def mOut : Prog isa :=
  .seq (.block (lea .rdi (qP (2 * L.k + 1)) ++ [.mov32 .rsi (.imm 1)] ++ lea .rdx (.r12, 0) ++
      [.mov32 .rcx (.imm 32)]))
    A.codecs.ce

/-- The body, between `pro` and `epi`. -/
def decBody : Prog isa :=
  .seq (seqR (uHat L A) 0 L.k) (.seq (seqR (sHat L A) 0 L.k)
    (.seq (prod L A) (.seq (vHat L A) (.seq (wSub L A) (mOut L A)))))

end Kpke16

open Kpke16 in
/-- `vg_mlkem*_kpke_decrypt` of the parameter set `L`, with the arithmetic of `A`. -/
def kpkeDecrypt (L : Kem) (A : Arith) : Prog isa :=
  .seq (.block pro) (.seq (decBody L A) (.block epi))

end VG.Impl.MlKem.X86_64
