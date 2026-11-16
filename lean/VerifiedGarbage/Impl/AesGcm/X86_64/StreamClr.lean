module
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64

/-!
# AES-GCM streaming on x86-64: the text, clearing registers by path

`vg_aes_gcm_stream_encrypt_prepared` and `_decrypt_prepared` of the
variants whose callees never touch the stack (`_aesni_pclmul`,
`_vaes_vpclmul`) leave secrets on the stack only in `T`, the padded
additional data, and in registers. So that they need not clear the stack or
all the registers on every return, this is `streamText` with two changes:

* the additional data is padded in the streaming state's keystream block
  (`r14 + 64`), which holds nothing before the first text (`firstFlushS`),
  rather than in `T` on the stack;
* every call (of `vg_aes_ctr32`, `vg_ghash` and the whole blocks) is
  followed by `clrAfter v`, which zeroes the vector registers (at the
  level `v`) and the caller-saved general-purpose registers but `rax`,
  in the branch that made it, after the last use of what it left there.

The code is written as `streamTextS` over callees whose code ends in
`clrAfter v` (`Callees.wrapC`), which `hoist` then moves out of each call to
just after it: the same instructions run in the same order (the clearing
touches neither memory nor the stack pointer), and the callees keep their
own code and names. `streamText`, which SM4-GCM also uses, is unchanged.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64

open VG.X86_64 VG.Impl.Scrub.X86_64

/-- The vector registers zeroed at the level `v`, and the caller-saved
general-purpose registers but `rax`. -/
def clrAfter (v : VecLevel) : List Instr := clearVec v ++ scratchRegs.map zeroR

/-- `f`, with `k` run before it returns. -/
def Fn.wrapC (k : List Instr) (f : Fn) : Fn := ⟨f.name, .seq f.code (.block k)⟩

/-- The callees, each with `k` run before it returns (but the key expansion, which the streaming functions never call). -/
def Callees.wrapC (k : List Instr) (c : Callees) : Callees :=
  ⟨c.ctr.wrapC k, c.key, c.gh.wrapC k, c.enc.wrapC k, c.dec.wrapC k⟩

/-- A call of `n` with the body `b`: `k` moved out of it, after it, if `b`
ends with it. -/
def hoistCall (k : List Instr) (n : String) : Prog isa → Prog isa
  | .seq b (.block k') => if k' = k then .seq (.call n b) (.block k) else .call n (.seq b (.block k'))
  | b => .call n b

/-- `c`, with `k` moved out of every call whose body ends with it (but not
out of the calls the called functions make). -/
def hoist (k : List Instr) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (hoist k a) (hoist k b)
  | .ite c t e => .ite c (hoist k t) (hoist k e)
  | .loop b c => .loop (hoist k b) c
  | .call n b => hoistCall k n b
  | .frame i b j => .frame i (hoist k b) j
  | .icall i n b nx => .icall i n b nx

variable (c : Callees)

/-- The `rbx` buffered bytes, padded with zeros in the keystream block of
the state (`r14 + 64`), absorbed. -/
def flushS (yo : Nat) : Prog isa :=
  .seq (.block [.alu .test .rbx (.reg .rbx)])
    (.ite .e (.block [])
      (.seq (.block (([.mov32 .rax (imm 0), .store (at_ .r14 64) .rax, .store (at_ .r14 72) .rax] : List Instr) ++
          ptr .rdi .r14 64 ++ ptr .rsi .r14 32 ++ ([.mov .rcx (.reg .rbx)] : List Instr)))
      (.seq copyLoop (ghash1 c yo .r14 64))))

/-- `firstFlush`, padding in the state (`flushS`). -/
def firstFlushS : Prog isa :=
  .seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)]) (flushS c 16)

/-- `streamText`, with the additional data padded in the state (`firstFlushS`). -/
def streamTextS (enc : Bool) : Prog isa :=
  let part : Prog isa := partWith enc (crypt c) (absorb c 16)
  .seq (.block [.alu .test .rbp (.reg .rbp)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (firstFlushS c) (.block []))
      (.seq (.block streamLoad)
      (.seq (.block streamSmall)
      (.seq (.ite .b (.block [])
        (.seq streamHead
        (.seq (headPart c enc)
        (.seq (.block streamNext)
        (.seq (streamBlocks (if enc then c.enc else c.dec))
          (.block streamLoad))))))
        part))))))

/-- `streamEncrypt` with `streamTextS`. -/
def streamEncryptS : Prog isa :=
  .seq (.block cryptEntry) (.seq (streamTextS c true) (.block restore))

/-- `streamDecrypt` with `streamTextS`. -/
def streamDecryptS : Prog isa :=
  .seq (.block cryptEntry) (.seq (streamTextS c false) (.block restore))

/-- `vg_aes_gcm_stream_encrypt` that clears, after each call, the registers
at the level `v` (`clrAfter`), and pads in the state. -/
def streamEncryptClr (v : VecLevel) : Prog isa := hoist (clrAfter v) (streamEncryptS (c.wrapC (clrAfter v)))

/-- `vg_aes_gcm_stream_decrypt` likewise. -/
def streamDecryptClr (v : VecLevel) : Prog isa := hoist (clrAfter v) (streamDecryptS (c.wrapC (clrAfter v)))

end VG.Impl.AesGcm.X86_64
