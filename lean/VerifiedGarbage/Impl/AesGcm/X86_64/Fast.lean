module

public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit

/-!
# AES-GCM on x86-64: `seal_split`'s path for TLS records

`vg_aes_gcm_seal_split` with a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) takes a path of its own for the records of
TLS: a 12-byte nonce, at most 16 bytes of additional data and at least 256
bytes of text (`cond`). It is `SealSplit.run` with the additional data
absorbed without a call (`aad`): `J₀` and the first counter block (`j012`,
`initState`), then the additional data padded with zeros in `T` (`aadPad`)
and multiplied by `H'` (`aadMul`), the prepared power `H` at `ctx + 272`,
where `oneAad` would call `vg_ghash`, which computes `H'` from `H` on every
call. `SealSplit.prefix` and `SealSplit.body` then end it as `run` does.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Fast

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr Fn Callees j012 initState copyLoop alenO lenO aadO tO)
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly)

/-- `rax = 1` if the path applies (a 12-byte nonce in `rbp`, at most 16
bytes of additional data and at least 256 bytes, which reach the interleaved
loop), `0` otherwise; then `test rax, rax`. Each branch falls through while
the path may still apply. -/
def cond : Prog isa :=
  .seq (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)])
  (.seq (.ite .ne (.block [])
      (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)])
        (.ite .ae (.block [])
          (.seq (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .cmp .rcx (imm 256)])
            (.ite .b (.block []) (.block [.mov32 .rax (imm 1)]))))))
    (.block [.alu .test .rax (.reg .rax)]))

/-- The additional data, `rcx` bytes (1 to 16), padded with zeros in `T`. -/
def aadPad : Prog isa :=
  .seq (.block (([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] : List Instr) ++
      ptr .rdi .r15 tO ++ ([.mov .rsi (.mem (at_ .r15 aadO))] : List Instr)))
    copyLoop

/-- The accumulator `mul(T, H')` (`vg_ghash_pclmul`'s multiplication), with
`H'` the prepared power at `ctx + 272`. -/
def aadMul : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.movdquLoad .xmm7 (at_ .r15 tO), .xop (.bin .pshufb .xmm7 .xmm0), .movdquLoad .xmm3 (at_ .r13 272)] : List Instr) ++
  Gcm.X86_64.Pclmul.mul .xmm2 .xmm7 .xmm3 ++
  ([.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .r14 16) .xmm2] : List Instr)

/-- `J₀`, the first counter block (with the accumulator zeroed), and the
additional data absorbed, if any. -/
def aad : Prog isa :=
  .seq (.block j012) (.seq (.block initState)
    (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)])
      (.ite .e (.block []) (.seq aadPad (.block aadMul)))))

/-- After the entry: `aad`, then `SealSplit.run`'s `prefix` (with `fTo`, the
whole blocks at `src`) and `body`. -/
def run (c : Callees) (fTo : Fn) (fin : Prog isa) : Prog isa :=
  .seq aad (.seq (SealSplit.prefix fTo) (SealSplit.body c fin))

/-- `cond`, then this path, or `other`. -/
def sel (c : Callees) (fTo : Fn) (fin : Prog isa) (other : Prog isa) : Prog isa :=
  .seq cond (.ite .e other (run c fTo fin))

end VG.Impl.AesGcm.X86_64.Fast
