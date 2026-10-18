module

public import VerifiedGarbage.Impl.MlKem.X86_64.EncapsH

/-!
# ML-KEM on x86-64: encapsulation hashing the key (`vg_mlkem768_encaps`, `vg_mlkem1024_encaps`)

`kemEncaps L c (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`:
`ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17) of the parameter
set `L`, computing `H(ek)` itself (`VG.Spec.MlKem.encapsContract`). It keeps
the pointers in the registers `kemEncapsH` (`EncapsH.lean`) keeps them in
(`scratch` in `rbx`, `m` in `rbp`, `key` in `r12`, `ct` in `r13` and `ek`
in `r14`), and is `kemEncapsH` but for `H(ek)`:

* With an implementation `c` of `vg_mlkem_sample_ntt4` that has no fragment
  to inline (`c.batchH = none`, the baseline), `H(ek)` is computed with the
  sponge functions to `H` first (`hashEk`), and the rest is `kemEncapsH`'s.
* With one (`c.batchH = some b`, AVX2 or AVX-512), the matrix is sampled
  first, three entries at a time with `b` (`Sample4.sampleH`), whose fourth
  Keccak state absorbs `pad(ek)`, three blocks of 136 bytes at a time:
  `ρ` to `SB`; the sponge's state, at `HS` in the working
  space of `vg_mlkem_sample_ntt4` (polynomial `pW`), zeroed; for each
  `i < nb` (`nb = |pad(ek)| / 408`), the 408 bytes of `pad(ek)` from `408 i`
  to `HB` (`hblk`: from `ek`, and for the last, its rest, zeros, SHA-3's
  suffix `0x06` and the last bit `0x80` of the padding), the seeds of
  entries `3i` to `3i + 3`, and `b`, which samples the first three to
  `Â`; then `H(ek)`, the first 32 bytes of the sponge's state, to `H`; the
  remaining entries of `Â` as `kemEncapsH` samples them (four at a time with
  `c`); `m` to `M` and `G(m ‖ H(ek))` to `G` (`EncapsH.hashes`); and `kemEncapsH`'s rest of `K-PKE.Encrypt`
  and outputs, if every `SampleNTT` succeeded.

ML-KEM-768's key is 9 blocks (three `b`), and ML-KEM-1024's 12 (four `b`,
then the last four entries of `Â` with `c`).
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace Encaps

/-- Save the callee-saved registers, keep the pointers, and `r15 ← 1`. -/
def pro : List Instr := topPro .r8 [(.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]

variable (L : Kem)

/-- `H(ek)` to `H`, with the sponge functions. -/
def hashEk : Prog isa := hashAt [((.r14, 0), L.ekLen)] 136 6 (sc oH) 32

/-- The state of `H`'s sponge and its blocks, in the working space of
`vg_mlkem_sample_ntt4` (polynomial `pW`). -/
def oHS : Nat := oP L.pW + Sample4.oHS
def oHB : Nat := oP L.pW + Sample4.oHB

/-- The number of fragments: `|pad(ek)| / 408`. -/
def nb : Nat := (L.ekLen / 136 + 1) / 3

/-- The sponge's state zeroed. -/
def hzero : List Instr := .mov32 .rax (.imm 0) :: zeroSt .rbx (oHS L)

/-- The rest of the last 408 bytes of `pad(ek)`, after the `len` bytes of
`ek`: zeros, and the suffix and the last bit of the padding. -/
def padTail (len : Nat) : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range ((408 - len) / 8)).flatMap (fun j => [.store (at_ .rbx (oHB L + len + 8 * j)) .rax]) ++
    setB (sc (oHB L + len)) 6 ++ setB (sc (oHB L + 407)) 0x80

/-- Bytes `408 i` to `408 i + 407` of `pad(ek)` to `HB`. -/
def hblk (i : Nat) : Prog isa :=
  if 408 * i + 408 ≤ L.ekLen then copy (sc (oHB L)) (.r14, 408 * i) 408
  else .seq (copy (sc (oHB L)) (.r14, 408 * i) (L.ekLen - 408 * i)) (.block (padTail L (L.ekLen - 408 * i)))

/-- The fragment `b` on the four seeds at `scratch` and the polynomials from
`a`, with the working space `scr`, and `r15 ← r15 ∧ result`. -/
def sampleHAt (b : Prog isa) (a scr : Ptr) : Prog isa :=
  .seq (.block (lea .rdi (sc 0) ++ lea .rsi a ++ lea .rdx scr)) (.seq b (.block [.alu32 .and .r15 (.reg .rax)]))

/-- Fragment `i`: its blocks of `pad(ek)`, the seeds of entries `3i` to
`3i + 3`, and `b`, which samples entries `3i` to `3i + 2`. -/
def frag (b : Prog isa) (i : Nat) : Prog isa :=
  .seq (hblk L i) (.seq (seedAt 0 ((3 * i) / L.k) ((3 * i) % L.k))
    (.seq (seedAt 1 ((3 * i + 1) / L.k) ((3 * i + 1) % L.k))
      (.seq (seedAt 2 ((3 * i + 2) / L.k) ((3 * i + 2) % L.k))
        (.seq (seedAt 3 ((3 * i + 3) / L.k) ((3 * i + 3) % L.k))
          (sampleHAt b (pS (L.pA + 3 * i)) (pS L.pW))))))

/-- `ρ` to `SB`, `Â` and `H(ek)` to `H`. -/
def matH (c : Callee4) (b : Prog isa) : Prog isa :=
  .seq (copy (sc oSB) (.r14, 384 * L.k) 32) (.seq (.block (hzero L)) (.seq (seqR (frag L b) 0 (nb L))
    (.seq (copy (sc oH) (sc (oHS L)) 32) (L.ents c (3 * nb L) (L.k * L.k - 3 * nb L)))))

end Encaps

open Encaps in
/-- The encapsulation of the parameter set `L`. -/
def kemEncaps (L : Kem) (c : Callee4) : Prog isa :=
  match c.batchH with
  | none => .seq (.block pro) (.seq (hashEk L) (.seq EncapsH.hashes (.seq (encrypt L c (.r14, 0))
      (.seq (EncapsH.out L) (.block topEpi)))))
  | some b => .seq (.block pro) (.seq (matH L c b) (.seq EncapsH.hashes
      (.seq (ifOk (Encrypt.rest L c (.r14, 0))) (.seq (EncapsH.out L) (.block topEpi)))))

end VG.Impl.MlKem.X86_64
