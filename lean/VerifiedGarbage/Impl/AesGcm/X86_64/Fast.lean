module

public import VerifiedGarbage.Impl.AesGcm.X86_64.SealSplit

/-!
# AES-GCM on x86-64: `seal_split`'s path for TLS records

`vg_aes_gcm_seal_split` with a prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) takes a path of its own for the records of
TLS: a 12-byte nonce, at most 16 bytes of additional data and at least 256
bytes of text, or any text where the path is faster than the others at every
length (`cond`, with `any`). It is `SealSplit.run` with the additional data
absorbed without a call (`aad`): `J₀` and the first counter block (`j012`,
`initState`), then the additional data padded with zeros in `T` (`aadPad`)
and multiplied by `H'` (`aadMul`), the prepared power `H` at `ctx + 272`,
where `oneAad` would call `vg_ghash`, which computes `H'` from `H` on every
call; five bytes (a TLS 1.3 record's header) are put together in a register
instead (`aadReg`), and sixteen loaded as a block (`aadFull`). `SealSplit.prefix` and `SealSplit.body` then end it as `run` does.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Fast

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr Fn Callees j012 initState copyLoop alenO lenO aadO tO)
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly)

/-- After the nonce and the additional data: `rax = 1` if the text is long
enough, with `any` at any length, and otherwise at 256 bytes or more, which
reach the interleaved loop. -/
def condLen (any : Bool) : Prog isa :=
  if any then .block [.mov32 .rax (imm 1)]
  else
    .seq (.block [.mov .rcx (.mem (at_ .r15 lenO)), .alu .cmp .rcx (imm 256)])
      (.ite .b (.block []) (.block [.mov32 .rax (imm 1)]))

/-- `rax = 1` if the path applies (a 12-byte nonce in `rbp`, at most 16
bytes of additional data and the text `condLen any` takes), `0` otherwise;
then `test rax, rax`. Each branch falls through while the path may still
apply. On 512-bit registers the short path is faster for less text, and
`any` is false; on 128- and 256-bit ones, which have no short path, the
path is faster at every length, and `any` is true. -/
def cond (any : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)])
  (.seq (.ite .ne (.block [])
      (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)])
        (.ite .ae (.block []) (condLen any))))
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

/-- Five bytes of additional data (a TLS 1.3 record's header) at `rsi`, in
the low bytes of `xmm7`, the rest zero: the block `aadPad` would leave in `T`,
without the stores that the load of `T` would wait for. -/
def aadReg : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .movzx8 .r10 (at_ .rsi 4), .shift .shl .r10 32,
    .alu .add .rax (.reg .r10), .xop (.movq .xmm7 .rax)]

/-- `aadMul`, with the block in `xmm7` rather than at `T`. -/
def aadMulR : List Instr :=
  Gcm.X86_64.Pclmul.const .xmm0 revMask ++ Gcm.X86_64.Pclmul.const .xmm1 poly ++
  ([.xop (.bin .pshufb .xmm7 .xmm0), .movdquLoad .xmm3 (at_ .r13 272)] : List Instr) ++
  Gcm.X86_64.Pclmul.mul .xmm2 .xmm7 .xmm3 ++
  ([.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .r14 16) .xmm2] : List Instr)

/-- Sixteen bytes of additional data at `rsi`, a whole block, loaded into
`xmm7`: no padding, and no stores for the load to wait for. -/
def aadFull : List Instr :=
  [.movdquLoad .xmm7 (at_ .rsi 0)]

/-- The additional data, `rcx` bytes (1 to 16), multiplied into the
accumulator: five bytes from a register (`aadReg`), sixteen loaded whole
(`aadFull`), any other length padded in `T` (`aadPad`). -/
def aadSome : Prog isa :=
  .seq (.block [.alu .cmp .rcx (imm 5)])
    (.ite .e (.seq (.block [.mov .rsi (.mem (at_ .r15 aadO))]) (.block (aadReg ++ aadMulR)))
      (.seq (.block [.alu .cmp .rcx (imm 16)])
        (.ite .e (.seq (.block [.mov .rsi (.mem (at_ .r15 aadO))]) (.block (aadFull ++ aadMulR)))
          (.seq aadPad (.block aadMul)))))

/-- `J₀`, the first counter block (with the accumulator zeroed), and the
additional data absorbed, if any. -/
def aad : Prog isa :=
  .seq (.block j012) (.seq (.block initState)
    (.seq (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)])
      (.ite .e (.block []) aadSome)))

/-- At most 16 bytes left after `prefix` (a TLS record's last bytes and its
content type): the total length put back, then `seal`'s end without the
whole blocks or calls, with `H'` and `H'²` from the prepared key context
(`Short.finishP`) and the keystream of `ks`. -/
def tail (ks : Prog isa) : Prog isa :=
  .seq (.block SealSplit.fixTlen) (Short.finishP ks)

/-- After the entry: `aad`, then `SealSplit.run`'s `prefix` (with `fTo`, the
whole blocks at `src`), and `tail` if at most 16 bytes are left, `body`
otherwise. -/
def run (c : Callees) (fTo : Fn) (ks fin : Prog isa) : Prog isa :=
  .seq aad (.seq (SealSplit.prefix fTo)
    (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      (.ite .b (tail ks) (SealSplit.body c fin))))

/-- `cond any`, then this path, or `other`. -/
def sel (c : Callees) (fTo : Fn) (ks fin : Prog isa) (other : Prog isa) (any : Bool := false) : Prog isa :=
  .seq (cond any) (.ite .e other (run c fTo ks fin))

end VG.Impl.AesGcm.X86_64.Fast
