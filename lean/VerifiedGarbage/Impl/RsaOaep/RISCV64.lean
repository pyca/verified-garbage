module

public import VerifiedGarbage.Impl.Hmac.Stream.RISCV64
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame
public import VerifiedGarbage.Impl.ICall

/-!
# RSAES-OAEP encryption (RFC 8017 §7.1.1) with a precomputed public key on RISC-V

`vg_rsa_oaep_encrypt_precomputed(out = a0, out_len = a1, n = a2,
n_len = a3, e = a4, e_len = a5, label = a6, label_len = a7, msg, msg_len,
seed, seed_len, scratch, scratch_len, pre, pre_len, hash, mgf1)`, the last
ten on the stack, with the label's hash function that of the table `hash`
and MGF1 over that of the table `mgf1`, both of the interface `Hash`
(`Spec/HashTable.lean`), which it calls, with
`vg_rsa_public_precomputed_checked`. The steps are those of PPC64LE
(`Impl/RsaOaep/PPC64LE.lean`): the digest length of `hash` (its word 4)
selects the code for that length (`byLen`, among `lens`), which is all that
code uses of the hash function's shape (`ofLen`), and every call of a hash
function is through its table (`tcall`).

If `k < 2 hLen + 2` or `msg_len > k - 2 hLen - 2` (`k = n_len`, public), it
writes zeros to `out` and returns 0. Otherwise it writes
`EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the
label hashed with `hash`'s hash function), masks `DB` with MGF1 of the seed and then the seed
with MGF1 of `maskedDB`, and returns `vg_rsa_public_precomputed_checked`
of `EM` into `out`, with `pre` and the rest of `scratch`.

The function allocates a frame of `frameBytes` bytes: the call's stack
arguments (at `sp`, `sp + 8`), then our caller's `s0`–`s11` and our return
address (`saved`). Our own stack arguments are at `sp + frameBytes + 8 j`,
from `t6` (`argBase`). The values the code keeps across the calls are in
`s0`–`s11`, which every function it calls saves and restores: `s0` =
`scratch`, `s1` = `k`, `s2` = `out`, `s3` = `e`, `s4` = `e_len`; and MGF1's
`s6` = `src`, `s7` = `srcLen`, `s8` = `dst`, `s9` = `dstLen`, `s10` = the
counter and `s11` = `done`, the bytes of the mask so far, with the label in
`s6` and `s7` before MGF1. `pre`, `pre_len` and `scratch_len` are read from
our stack arguments for the public operation. Before the first call, `t2`,
`t3` and `t4` hold `msg`, `msg_len` and `seed`.

The first `oRsa` = 8192 bytes of `scratch` are ours: `EM` (up to 1024
bytes), then the streaming state, the digest and MGF1's counter. The public
operation gets the rest, `scratch_len - 1024` words.

A comparison `a < b` of values below `2⁶³` is the top bit of `a - b`. Every
branch and address depends only on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.RISCV64

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)

/-! ## The frame -/

/-- The size of the frame. -/
def frameBytes : Nat := 128

/-- Where our caller's `s0`–`s11` and our return address are saved. -/
def saved : List (Reg × Nat) :=
  [(.s0, 16), (.s1, 24), (.s2, 32), (.s3, 40), (.s4, 48), (.s5, 56), (.s6, 64), (.s7, 72), (.s8, 80),
    (.s9, 88), (.s10, 96), (.s11, 104), (.ra, 112)]

/-- `t6 :=` the address of our first stack argument. -/
def argBase : Instr := .addSp .t6 frameBytes

/-! ## Our part of `scratch` -/

/-- `EM`: `k` bytes. -/
def oEm : Nat := 0
/-- The streaming state (at most 192 bytes). -/
def oSt : Nat := 1024
/-- The bytes `finalize` writes (at most 64). -/
def oDig : Nat := 1280
/-- MGF1's counter. -/
def oCtr : Nat := 1344
/-- Where the public operation's working space starts. -/
def oRsa : Nat := 8192

/-! ## The saves and the restores -/

/-- `t0 := sp`; our caller's `s0`–`s11` and our return address into the
frame. -/
def save : List Instr := .addSp .t0 0 :: saved.map fun p => .store .d p.1 .t0 p.2

/-- Our caller's `s0`–`s11` and our return address back from the frame. -/
def restore : List Instr := .addSp .t0 0 :: saved.map fun p => .load .d p.1 .t0 p.2

/-- The arguments into the registers that keep them; `msg`, `msg_len` and
`seed` into `t2`, `t3` and `t4`. -/
def prologue : List Instr :=
  [argBase, .load .d .s0 .t6 32, mov .s1 .a3, mov .s2 .a0, mov .s3 .a4, mov .s4 .a5, mov .s6 .a6,
    mov .s7 .a7, .load .d .t2 .t6 0, .load .d .t3 .t6 8, .load .d .t4 .t6 16]

/-! ## Loops

`copyLoop` (`a5` bytes from `a4` to `a1`) and `fillLoop` (`t5` bytes `t0`
from `a1`) are RSASSA-PKCS1-v1_5's (`Impl/RsaPkcs1Sig/RISCV64/Encode.lean`). -/

/-- `k` zeros to `out`. -/
def zeroOut : Prog isa := .seq (.block [mov .a1 .s2, mov .t5 .s1, .li .t0 0]) fillLoop

/-- Zeros to `out`, and 0. -/
def encFail : Prog isa := .seq zeroOut (.block [.li .a0 0])

variable (H : Hash)

/-! ## The checks -/

/-- In `a0`, 1 if `k < 2 hLen + 2`, 0 if not. -/
def chkK : List Instr := [.li .a0 (2 * H.D + 2), .sub .a0 .s1 .a0, .shift .srl .d .a0 .a0 63]

/-- In `a0`, nonzero exactly when `msg_len > k - 2 hLen - 2`, for
`k ≥ 2 hLen + 2`: the top bit of `msg_len`, or of
`(k - 2 hLen - 2) - msg_len`. -/
def chkMsg : List Instr :=
  [.li .a0 (2 * H.D + 2), .sub .a1 .s1 .a0, .sub .a1 .a1 .t3, .shift .srl .d .a1 .a1 63,
    .shift .srl .d .a0 .t3 63, .logic .or .a0 .a0 .a1]

/-! ## `EM` before masking -/

/-- `EM`'s place, the first 1024 bytes of `scratch`, cleared. -/
def clearEm : Prog isa := .seq (.block [.addi .a1 .s0 oEm, .li .t5 1024, .li .t0 0]) fillLoop

/-- The seed to `EM + 1`. -/
def copySeed : Prog isa := .seq (.block [mov .a4 .t4, .addi .a1 .s0 ((oEm + 1 : Nat) : Int), .li .a5 H.D]) copyLoop

/-- `0x01` at `EM + k - mLen - 1`, and the message after it, if it is not
empty. -/
def putMsg : Prog isa :=
  .seq (.block [.add .a1 .s0 .s1, .sub .a1 .a1 .t3, .addi .a1 .a1 (-1), .li .t1 1, .store .b .t1 .a1 0,
      .addi .a1 .a1 1, mov .a4 .t2, mov .a5 .t3])
    (.ite (.nonzero .a5) copyLoop (.block []))

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`. -/
def copyLh : Prog isa :=
  .seq (.block [.addi .a4 .s0 oDig, .addi .a1 .s0 ((oEm + 1 + H.D : Nat) : Int), .li .a5 H.D]) copyLoop

/-! ## MGF1

`dst ⊕= MGF1(src, dstLen)` (RFC 8017 Appendix B.2.1), for `dstLen > 0`, with
`src`, `srcLen`, `dst` and `dstLen` in `s6`–`s9`, with a hash function given
at compile time (`mgfXor`) or that of the table that is our stack argument
`j` (`mgfXorT`: the table's functions 0, 1 and 2 are `init`, `update` and
`finalize`, which it calls indirectly, `tcall`: their address, the table's
word, into `t1`, then `jalr ra, 0(t1)`, of whichever of the functions `Fns`
lists is at that address; `hLen` is the table's word 4). For each counter `c`
(`s10`) from 0, while `done = c hLen` (`s11`) is below `dstLen`: the state
is set by `init`, `update` absorbs `src` and `I2OSP(c, 4)` (written
big-endian to `scratch + oCtr`), `finalize` writes the digest to
`scratch + oDig`, and its first `min(hLen, dstLen - done)` bytes are XORed
into `dst + done`. -/

/-- `update(state, srcLen, scratch + oCtr, 4)`, with the counter written
there big-endian first. -/
def updCtrArgs : List Instr :=
  [.addi .a2 .s0 oCtr, mov .t1 .s10, .store .b .t1 .a2 3, .shift .srl .d .t1 .t1 8, .store .b .t1 .a2 2,
    .shift .srl .d .t1 .t1 8, .store .b .t1 .a2 1, .shift .srl .d .t1 .t1 8, .store .b .t1 .a2 0,
    .addi .a0 .s0 oSt, mov .a1 .s7, .li .a3 4]

/-- The functions an indirect call of each of a table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

/-- The word `k` of the table that is our stack argument `j`, into `d`. -/
def tword (d : Reg) (j k : Nat) : List Instr :=
  [.addSp d (frameBytes + 8 * j), .load .d d d 0, .load .d d d (8 * k)]

/-- The call of the table's function `k`, among `ts`: its address into
`t1`, then `jalr ra, 0(t1)`. -/
def tcall (j k : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block (tword .t1 j k)) (Code.icalls (.jalr .t1) ts)

section Table
variable (f : Fns) (j : Nat)

/-- The digest in `a4`, `dst + done` in `a5`, and in `a6`
`min(hLen, dstLen - done)`: `hLen` (the table's word 4) `+ ((rem - hLen) ∧
-(rem < hLen))` for `rem = dstLen - done`. -/
def xorHeadT : List Instr :=
  tword .a6 j 4 ++ [.addi .a4 .s0 oDig, .add .a5 .s8 .s11, .sub .t1 .s9 .s11, .sub .t2 .t1 .a6,
    .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3, .logic .and .t2 .t2 .t3, .add .a6 .a6 .t2]

/-- A byte of the digest XORed into `dst`. -/
def xorBody : List Instr :=
  [.load .b .t1 .a4 0, .load .b .t2 .a5 0, .logic .xor .t2 .t2 .t1, .store .b .t2 .a5 0, .addi .a4 .a4 1,
    .addi .a5 .a5 1]

/-- The first `min(hLen, dstLen - done)` bytes of the digest XORed into
`dst + done`. -/
def xorOutT : Prog isa := .seq (.block (xorHeadT j)) (countLoop .a6 xorBody)

/-- The next counter and `done`, and in `t1` 1 while `done < dstLen`, 0
after. -/
def nextCtrT : List Instr :=
  tword .t1 j 4 ++ [.addi .s10 .s10 1, .add .s11 .s11 .t1, .sub .t1 .s11 .s9, .shift .srl .d .t1 .t1 63]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`, with
the hash function of the table that is our stack argument `j`. -/
def roundT : Prog isa :=
  .seq (.block [.addi .a0 .s0 oSt]) (.seq (tcall j 0 f.init)
  (.seq (.block [.addi .a0 .s0 oSt, .li .a1 0, mov .a2 .s6, mov .a3 .s7]) (.seq (tcall j 1 f.upd)
  (.seq (.block updCtrArgs) (.seq (tcall j 1 f.upd)
  (.seq (.block [.addi .a0 .s0 oSt, .addi .a1 .s7 4, .addi .a2 .s0 oDig]) (.seq (tcall j 2 f.fin)
  (.seq (xorOutT j) (.block (nextCtrT j))))))))))

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`, with the hash function of
the table that is our stack argument `j`. -/
def mgfXorT : Prog isa := .seq (.block [.li .s10 0, .li .s11 0]) (.loop (roundT f j) (.nonzero .t1))

/-- The label hashed to `scratch + oDig`, with the hash function of the table
that is our stack argument `j`: `init`, then `update` with the arguments
`ua` sets (the label and its length), then `finalize` with those `fa` sets. -/
def hashLabelT (ua fa : List Instr) : Prog isa :=
  .seq (.block [.addi .a0 .s0 oSt]) (.seq (tcall j 0 f.init)
  (.seq (.block ua) (.seq (tcall j 1 f.upd) (.seq (.block fa) (tcall j 2 f.fin)))))

/-! ## The hash function's digest length -/

/-- The digest length of the table that is our stack argument `j` (its word
4), to `a0`. -/
def lenLoad : List Instr := tword .a0 j 4

end Table

/-- The digest lengths of the hash functions whose tables the functions take
(MD5, SHA-1, SHA-224 and SHA-512/224, SHA-256 and SHA-512/256, SHA-384,
SHA-512). -/
def lens : List Nat := [16, 20, 28, 32, 48, 64]

/-- The shape of a hash function with only the digest length `d`, which is
all the code with the hash function's calls through a table uses of it. -/
def ofLen (d : Nat) : Hash := ⟨0, 0, d, 0, "", .block [], "", .block [], "", .block []⟩

/-- `b d` for the digest length `d` in `a0`, among `ds`: the last if it is
none of the others. -/
def byLen (b : Nat → Prog isa) : List Nat → Prog isa
  | [] => .block []
  | [d] => b d
  | d :: ds => .seq (.block [.addi .a1 .a0 (-(d : Int))]) (.ite (.zero .a1) (b d) (byLen b ds))

/-! MGF1 with a hash function `G` given at compile time, as RSASSA-PSS
(`Impl/RsaPss/RISCV64.lean`) calls it. -/

section Fixed
variable (G : Hash)

/-- The digest in `a4`, `dst + done` in `a5`, and in `a6`
`min(hLen, dstLen - done)`: `hLen + ((rem - hLen) ∧ -(rem < hLen))` for
`rem = dstLen - done`. -/
def xorHead : List Instr :=
  [.addi .a4 .s0 oDig, .add .a5 .s8 .s11, .sub .t1 .s9 .s11, .li .a6 G.D, .sub .t2 .t1 .a6,
    .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3, .logic .and .t2 .t2 .t3, .add .a6 .a6 .t2]

/-- The first `min(hLen, dstLen - done)` bytes of the digest XORed into
`dst + done`. -/
def xorOut : Prog isa := .seq (.block (xorHead G)) (countLoop .a6 xorBody)

/-- The next counter and `done`, and in `t1` 1 while `done < dstLen`, 0
after. -/
def nextCtr : List Instr :=
  [.addi .s10 .s10 1, .addi .s11 .s11 G.D, .sub .t1 .s11 .s9, .shift .srl .d .t1 .t1 63]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  .seq (.block [.addi .a0 .s0 oSt]) (.seq G.callInit
  (.seq (.block [.addi .a0 .s0 oSt, .li .a1 0, mov .a2 .s6, mov .a3 .s7]) (.seq G.callUpd
  (.seq (.block updCtrArgs) (.seq G.callUpd
  (.seq (.block [.addi .a0 .s0 oSt, .addi .a1 .s7 4, .addi .a2 .s0 oDig]) (.seq G.callFin
  (.seq (xorOut G) (.block (nextCtr G))))))))))

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa := .seq (.block [.li .s10 0, .li .s11 0]) (.loop (round G) (.nonzero .t1))

end Fixed

/-- MGF1's registers for masking `DB` (`k - hLen - 1` bytes at
`EM + 1 + hLen`) with the seed (`hLen` bytes at `EM + 1`). -/
def dbArgs : List Instr :=
  [.addi .s6 .s0 ((oEm + 1 : Nat) : Int), .li .s7 H.D, .addi .s8 .s0 ((oEm + 1 + H.D : Nat) : Int),
    .addi .s9 .s1 (-(H.D + 1 : Nat))]

/-- MGF1's registers for masking the seed with `maskedDB`. -/
def seedArgs : List Instr :=
  [.addi .s6 .s0 ((oEm + 1 + H.D : Nat) : Int), .addi .s7 .s1 (-(H.D + 1 : Nat)),
    .addi .s8 .s0 ((oEm + 1 : Nat) : Int), .li .s9 H.D]

/-! ## The public operation -/

/-- The arguments of `vg_rsa_public_precomputed_checked`: `out` (`k`
bytes), `pre` (our stack arguments 6 and 7), `e`, `EM` as the input (`k`
bytes), and the rest of `scratch` on the stack (`scratch_len` is our stack
argument 5). -/
def pubArgs : List Instr :=
  [.addSp .t0 0, argBase, .li .t1 1024, .shift .sll .d .t1 .t1 3, .add .t1 .s0 .t1, .store .d .t1 .t0 0,
    .load .d .t1 .t6 40, .addi .t1 .t1 (-1024), .store .d .t1 .t0 8, mov .a0 .s2, mov .a1 .s1, .load .d .a2 .t6 48,
    .load .d .a3 .t6 56, mov .a4 .s3, mov .a5 .s4, .addi .a6 .s0 oEm, mov .a7 .s1]

/-! ## The function -/

/-- `EM` before masking, but for `lHash`; the code before the first call. -/
def encEm : Prog isa := .seq clearEm (.seq (copySeed H) putMsg)

variable (f : Fns)

/-- `update`'s arguments for the label, in `s6` and `s7`. -/
def labU : List Instr := [.addi .a0 .s0 oSt, .li .a1 0, mov .a2 .s6, mov .a3 .s7]

/-- `finalize`'s arguments for the label. -/
def labF : List Instr := [.addi .a0 .s0 oSt, mov .a1 .s7, .addi .a2 .s0 oDig]

/-- After the checks: the label's hash with the table `hash`, our stack
argument 8, and MGF1 with the table `mgf1`, our stack argument 9. -/
def encMain : Prog isa :=
  .seq (encEm H) (.seq (hashLabelT f 8 labU labF) (.seq (copyLh H)
  (.seq (.block (dbArgs H)) (.seq (mgfXorT f 9)
  (.seq (.block (seedArgs H)) (.seq (mgfXorT f 9)
  (.seq (.block pubArgs) Impl.RsaPkcs1Sig.RISCV64.pubCall)))))))

/-- The checks, then `encMain`. -/
def checks : Prog isa :=
  .seq (.block (chkK H)) (.ite (.nonzero .a0) encFail
    (.seq (.block (chkMsg H)) (.ite (.nonzero .a0) encFail (encMain H f))))

/-- The frame's body: the digest length of the table `hash` (our stack
argument 8) to `a0`, then the checks for that length. -/
def body : Prog isa :=
  .seq (.block (save ++ prologue)) (.seq (.block (lenLoad 8))
    (.seq (byLen (fun d => checks (ofLen d) f) lens) (.block restore)))

/-- `vg_rsa_oaep_encrypt_precomputed`, with the label's hash function the
table that is its stack argument 8 (`hash`) and MGF1's the table that is its
stack argument 9 (`mgf1`). -/
def encrypt : Prog isa := .frame (.alloc frameBytes) (body f) (.free frameBytes)

end VG.Impl.RsaOaep.RISCV64
