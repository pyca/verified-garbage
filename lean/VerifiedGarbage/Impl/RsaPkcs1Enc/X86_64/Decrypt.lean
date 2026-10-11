module

public import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# RSAES-PKCS1-v1_5 decryption with implicit rejection on x86-64

`vg_rsa_pkcs1_decrypt(out, out_len, msg_len, n, n_len, e, e_len, d, d_len,
input, input_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
scratch, scratch_len)`: the first six arguments in registers, the others on
the stack. With `vg_rsa_private_checked` (`priv`, by its name `privN`) and
SHA-256's streaming functions and HMAC's (`H`), it runs
draft-irtf-cfrg-rsa-guidance-10 §7.2:

1. The private-key operation, `EM` (or zeros) to `out` and its result `r`
   (1, or 0 or 2 for its errors) into a slot (`setup`, `callPriv`).
2. `D = I2OSP(d, k)` in `scratch`: zeros, then `d` at its end (`dBuild`);
   `DH = SHA256(D)` (`hashD`); `KDK = HMAC(DH, C)` (`kdkMac`).
3. The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop`) and the
   alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop`), a block of
   32 bytes per HMAC, the block's counter in a slot.
4. The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
   (`maskPart`), and the alternative length `AL`, the last candidate not
   above `k - 11` (`alPart`), selected without branches.
5. The scan of `EM` for its first zero from index 2 (`scanPart`), the
   validity mask `v` and the lengths, and the output (`selPart`): byte `i`
   of `out` is `EM[i]` or `AM[i]` as `v` selects, if `i ≥ k - len` for the
   selected length `len`, and zero otherwise, and everything (`out`, and
   `len` to `*msg_len`) is masked by `r = 1`. The function returns `r`.

Every address and branch depends only on the pointers, the lengths and the
counters: the validity of the padding, `L`, `AL` and the selection are masks
and values in registers. `out`'s and `AM`'s bytes are all read, whichever
is returned.

The frame is `frameBytes` bytes, an odd number of words, so that `rsp` is a
multiple of 16 at each call: at `rsp`, the private-key operation's stack
arguments; from `oOut`, the slots. Only caller-saved registers are used,
so the slots hold everything kept across a call. In `scratch`, from `sSt`:
the streaming state (also HMAC's inner state), HMAC's outer state, the
working space, the message of an IRPRF block, `DH`, `KDK`, `CL`, `AM` and
`D`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86_64.Decrypt

open VG VG.X86_64

/-- The size of the frame. -/
def frameBytes : Nat := 216

/-! The slots. -/
def oOut : Nat := 112
def oML : Nat := 120
def oN : Nat := 128
def oK : Nat := 136
def oE : Nat := 144
def oEl : Nat := 152
def oD : Nat := 160
def oDl : Nat := 168
def oIn : Nat := 176
def oScr : Nat := 184
def oR : Nat := 192
def oI : Nat := 200
def oNB : Nat := 208

/-! Where things are in `scratch`. -/
def sSt : Nat := 0
def sOuter : Nat := 96
def sWork : Nat := 192
def sMsg : Nat := 1024
def sDH : Nat := 1040
def sKDK : Nat := 1104
def sCL : Nat := 1136
def sAM : Nat := 1392
def sD : Nat := 2416

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := (d : Int) }

/-- The stack argument `j` (from 0) of the function, from the frame. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `[b + i + d]`: byte `i` of the buffer at `b + d`. -/
def bx (b i : Reg) (d : Nat := 0) : MemOp := { base := b, index := some i, disp := (d : Int) }

/-- `r := scratch + d`. -/
def scr (r : Reg) (d : Nat) : List Instr := [.mov r (.mem (sp oScr)), .alu .add r (.imm (BitVec.ofNat 32 d))]

/-! ## 1. The private-key operation -/

/-- The registers' arguments to the slots. -/
def slotStores : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oML) .rdx, .store (sp oN) .rcx, .store (sp oK) .r8, .store (sp oE) .r9]

/-- Stack argument `j` to the frame's word at `d`. -/
def mvArg (j d : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp d) .rax]

/-- The stack arguments kept in the frame: `e_len`, `d`, `d_len`, the input
and `scratch` to their slots, and ours from the input on to the frame's
first 14 words, the private-key operation's stack arguments. -/
def argMoves : List (Nat × Nat) :=
  [(0, oEl), (1, oD), (2, oDl), (3, oIn), (15, oScr)] ++ (List.range 14).map fun j => (j + 3, 8 * j)

/-- Its registers: `out`, `n_len`, `n`, `n_len`, `e`, `e_len`. -/
def privRegs : List Instr :=
  [.mov .rsi (.reg .r8), .mov .rdx (.reg .rcx), .mov .rcx (.reg .r8), .mov .r8 (.reg .r9), .mov .r9 (.mem (sp oEl))]

def setup : List Instr := slotStores ++ (argMoves.flatMap (fun p => mvArg p.1 p.2) ++ privRegs)

/-! ## 2. The key derivation key -/

/-- `r` to its slot; the zeros of `D`: its base in `rdi`, `k` in `rcx`, the
index and the zero. -/
def dPtrs₁ : List Instr :=
  [.store (sp oR) .rax, .mov .rdi (.mem (sp oScr)), .mov .rcx (.mem (sp oK)), .mov32 .r10 (.imm 0),
    .mov32 .rax (.imm 0)]

def zeroLoop : Prog isa :=
  .loop (.block [.store8 (bx .rdi .r10 sD) .rax, .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .rcx)]) .ne

/-- `d` at the end of `D`: `d` in `rsi`, its length in `rcx`, the base of its
place (`scratch + k - d_len`) in `rdi`. -/
def dPtrs₂ : List Instr :=
  [.mov .rsi (.mem (sp oD)), .mov .rcx (.mem (sp oDl)), .mov .rdi (.mem (sp oScr)), .alu .add .rdi (.mem (sp oK)),
    .alu .sub .rdi (.reg .rcx), .mov32 .r10 (.imm 0)]

def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rsi .r10), .store8 (bx .rdi .r10 sD) .rax, .alu .add .r10 (.imm 1),
    .alu .cmp .r10 (.reg .rcx)]) .ne

def dBuild : Prog isa := .seq (.block dPtrs₁) (.seq zeroLoop (.seq (.block dPtrs₂) copyLoop))

variable (H : Impl.Pbkdf2.Md.X86_64.Hash)

/-- `init(state)`. -/
def shaInitArgs : List Instr := [.mov .rdi (.mem (sp oScr))]
/-- `update(state, 0, D, k, work)`. -/
def shaUpdArgs : List Instr :=
  [.mov .rdi (.mem (sp oScr)), .mov32 .rsi (.imm 0)] ++ scr .rdx sD ++ [.mov .rcx (.mem (sp oK))] ++ scr .r8 sWork
/-- `finalize(state, k, DH, work)`. -/
def shaFinArgs : List Instr :=
  [.mov .rdi (.mem (sp oScr)), .mov .rsi (.mem (sp oK))] ++ scr .rdx sDH ++ scr .rcx sWork

def hashD : Prog isa :=
  .seq (.block shaInitArgs) (.seq (.call H.initN H.initC) (.seq (.block shaUpdArgs) (.seq (.call H.updN H.updC)
    (.seq (.block shaFinArgs) (.call H.finN H.finC)))))

/-- HMAC's `init(inner, outer, key, 32, work)` for the key at `scratch + key`. -/
def macInitArgs (key : Nat) : List Instr :=
  [.mov .rdi (.mem (sp oScr))] ++ scr .rsi sOuter ++ scr .rdx key ++ [.mov32 .rcx (.imm 32)] ++ scr .r8 sWork

/-- `update(inner, 64, C, k, work)`. -/
def kdkUpdArgs : List Instr :=
  [.mov .rdi (.mem (sp oScr)), .mov32 .rsi (.imm 64), .mov .rdx (.mem (sp oIn)), .mov .rcx (.mem (sp oK))] ++
    scr .r8 sWork

/-- HMAC's `finalize(inner, outer, 64 + k, KDK, work)`. -/
def kdkFinArgs : List Instr :=
  [.mov .rdi (.mem (sp oScr))] ++ scr .rsi sOuter ++ [.mov .rdx (.mem (sp oK)), .alu .add .rdx (.imm 64)] ++
    scr .rcx sKDK ++ scr .r8 sWork

def kdkMac : Prog isa :=
  .seq (.block (macInitArgs sDH)) (.seq (.call H.hmacInitN H.hmacInit) (.seq (.block kdkUpdArgs)
    (.seq (.call H.updN H.updC) (.seq (.block kdkFinArgs) (.call H.hmacFinN H.hmacFin)))))

/-! ## 3. IRPRF -/

/-- Byte `d` of the block's message: the immediate `v`. -/
def putByte (d v : Nat) : List Instr := [.mov32 .rdx (.imm (BitVec.ofNat 32 v)), .store8 (at_ .rdi (sMsg + d)) .rdx]

/-- The message `I2OSP(i, 2) ‖ label ‖ bitLength` at `scratch + sMsg`, with
`scratch` in `rdi` and `i < 256` in `rax`: the label's bytes, and the code
`len` writing the bit length's two bytes after them. -/
def msgBytes (label : List Nat) (len : List Instr) : List Instr :=
  putByte 0 0 ++ [.store8 (at_ .rdi (sMsg + 1)) .rax] ++
    (label.zipIdx.flatMap fun (v, j) => putByte (2 + j) v) ++ len

/-- The bit length 2048 of `CL`, after the 6 bytes of "length". -/
def clLen : List Instr := putByte 8 0x08 ++ putByte 9 0x00

/-- The bit length `8 k` of `AM`, after the 7 bytes of "message", from `k`
in `r9`. -/
def amLen : List Instr :=
  [.mov .rdx (.reg .r9), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
    .store8 (at_ .rdi (sMsg + 10)) .rdx, .shift .shr .rdx 8, .store8 (at_ .rdi (sMsg + 9)) .rdx]

/-- `update(inner, 64, msg, len, work)`. -/
def prfUpdArgs (len : Nat) : List Instr :=
  [.mov .rdi (.mem (sp oScr)), .mov32 .rsi (.imm 64)] ++ scr .rdx sMsg ++
    [.mov32 .rcx (.imm (BitVec.ofNat 32 len))] ++ scr .r8 sWork

/-- HMAC's `finalize(inner, outer, 64 + len, scratch + dst + 32 i, work)`. -/
def prfFinArgs (len dst : Nat) : List Instr :=
  [.mov .rdi (.mem (sp oScr))] ++ scr .rsi sOuter ++ [.mov32 .rdx (.imm (BitVec.ofNat 32 (64 + len))),
    .mov .rcx (.mem (sp oI)), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.mem (sp oScr)),
    .alu .add .rcx (.imm (BitVec.ofNat 32 dst))] ++ scr .r8 sWork

/-- One more block, and ZF set at the last. -/
def incr (count : Src) : List Instr :=
  [.mov .rax (.mem (sp oI)), .alu .add .rax (.imm 1), .store (sp oI) .rax, .alu .cmp .rax count]

/-- Block `i` (in its slot) of IRPRF with the label `label`, the bit length's
code `len`, to `scratch + dst + 32 i`, and the count `count`. -/
def prfBody (label : List Nat) (len : List Instr) (dst : Nat) (count : Src) : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp oScr)), .mov .rax (.mem (sp oI)), .mov .r9 (.mem (sp oK))])
  (.seq (.block (msgBytes label len))
  (.seq (.block (macInitArgs sKDK)) (.seq (.call H.hmacInitN H.hmacInit)
  (.seq (.block (prfUpdArgs (label.length + 4))) (.seq (.call H.updN H.updC)
  (.seq (.block (prfFinArgs (label.length + 4) dst)) (.seq (.call H.hmacFinN H.hmacFin)
    (.block (incr count)))))))))

/-- "length" and "message", in ASCII. -/
def lengthLabel : List Nat := [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
def messageLabel : List Nat := [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]

/-- The counter, and the number of `AM`'s blocks `⌈k / 32⌉` to its slot. -/
def clInit : List Instr :=
  [.mov32 .rax (.imm 0), .store (sp oI) .rax, .mov .rax (.mem (sp oK)), .alu .add .rax (.imm 31), .shift .shr .rax 5,
    .store (sp oNB) .rax]

def clLoop : Prog isa :=
  .seq (.block clInit) (.loop (prfBody H lengthLabel clLen sCL (.imm 8)) .ne)

def amLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp oI) .rax])
    (.loop (prfBody H messageLabel amLen sAM (.mem (sp oNB))) .ne)

/-! ## 4. The alternative length -/

/-- `k - 11` into `r9`, and the mask `r8` from 0. -/
def maskInit : List Instr := [.mov .r9 (.mem (sp oK)), .alu .sub .r9 (.imm 11), .mov32 .r8 (.imm 0)]

/-- `r8 := 2 r8 + 1` while `r8 < r9`. -/
def maskLoop : Prog isa := .loop (.block [.alu .add .r8 (.reg .r8), .alu .add .r8 (.imm 1), .alu .cmp .r8 (.reg .r9)]) .b

def maskPart : Prog isa := .seq (.block maskInit) maskLoop

/-- `CL` in `rsi`, the byte index `rcx` and `AL` (`r11`) zero. -/
def alInit : List Instr := scr .rsi sCL ++ [.mov32 .rcx (.imm 0), .mov32 .r11 (.imm 0)]

/-- One candidate: `c = (256 CL[i] + CL[i + 1]) & r8`, and `r11 := c` if
`c ≤ k - 11` (`r9`), without branches. -/
def alLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rsi .rcx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .movzx8 .rdx (bx .rsi .rcx 1), .alu .add .rax (.reg .rdx),
    .alu .and .rax (.reg .r8), .mov .rdx (.reg .r9), .alu .cmp .rdx (.reg .rax), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .r11 (.reg .rax), .alu .and .r11 (.reg .rdx), .alu .xor .r11 (.reg .rax), .alu .add .rcx (.imm 2),
    .alu .cmp .rcx (.imm 256)]) .ne

def alPart : Prog isa := .seq (.block alInit) alLoop

/-! ## 5. The padding and the output -/

/-- `EM` (`out`) in `rdi`, `k` in `r9`, the index `rcx` from 2, whether a
zero was found (`rdx`) and where (`r10`). -/
def scanInit : List Instr :=
  [.mov .rdi (.mem (sp oOut)), .mov .r9 (.mem (sp oK)), .mov32 .rcx (.imm 2), .mov32 .rdx (.imm 0),
    .mov32 .r10 (.imm 0)]

/-- Byte `rcx`: `z = -(EM[i] = 0)`, `r10 |= i & z & ~rdx`, `rdx |= z`. -/
def scanLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (bx .rdi .rcx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .mov .rsi (.reg .rdx), .alu .xor .rsi (.imm (BitVec.ofInt 32 (-1))), .alu .and .rsi (.reg .rax),
    .alu .and .rsi (.reg .rcx), .alu .or .r10 (.reg .rsi), .alu .or .rdx (.reg .rax), .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .r9)]) .ne

def scanPart : Prog isa := .seq (.block scanInit) scanLoop

/-- The validity mask `v` (`r10`), the selected length `len` (`rdx`), the
mask of `r = 1` (`r11`), and `k - len` (`rsi`):
`v = -(EM[0] = 0) & -(EM[1] = 2) & found & -(sep ≥ 10)`,
`len = AL ^ ((AL ^ L) & v)` for `L = k - sep - 1`. -/
def validBlock : List Instr :=
  [.movzx8 .rax (at_ .rdi 0), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .movzx8 .rsi (at_ .rdi 1), .alu .xor .rsi (.imm 2), .alu .cmp .rsi (.imm 1), .alu .sbb .rsi (.reg .rsi),
    .alu .and .rax (.reg .rsi), .alu .and .rax (.reg .rdx),
    .mov .rsi (.reg .r10), .alu .cmp .rsi (.imm 10), .alu .sbb .rsi (.reg .rsi),
    .alu .xor .rsi (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.reg .rsi),
    .mov .rsi (.reg .r9), .alu .sub .rsi (.reg .r10), .alu .sub .rsi (.imm 1),
    .mov .rdx (.reg .r11), .alu .xor .rdx (.reg .rsi), .alu .and .rdx (.reg .rax), .alu .xor .rdx (.reg .r11),
    .mov .r10 (.reg .rax),
    .mov .r11 (.mem (sp oR)), .mov32 .r11 (.reg .r11), .alu .xor .r11 (.imm 1), .alu .cmp .r11 (.imm 1),
    .alu .sbb .r11 (.reg .r11),
    .mov .rsi (.reg .r9), .alu .sub .rsi (.reg .rdx), .alu .and .rdx (.reg .r11)]

/-- `msg_len` in `r8`, and `AM` in `rcx`. -/
def outPtrs : List Instr := [.mov .r8 (.mem (sp oML))] ++ scr .rcx sAM

/-- `*msg_len := len & ok`; then `AM` to `rsi` (`k - len` to `rdx`) and the
index `rcx` zero. -/
def outInit : List Instr :=
  [.store (at_ .r8 0) .rdx, .mov .rdx (.reg .rsi), .mov .rsi (.reg .rcx), .mov32 .rcx (.imm 0)]

/-- Byte `rcx` of `out`: `(EM[i] & v | AM[i] & ~v) & -(i ≥ k - len) & ok`. -/
def selBody : List Instr :=
  [.movzx8 .rax (bx .rdi .rcx), .movzx8 .r8 (bx .rsi .rcx), .alu .xor .rax (.reg .r8),
    .alu .and .rax (.reg .r10), .alu .xor .rax (.reg .r8), .mov .r8 (.reg .rcx), .alu .cmp .r8 (.reg .rdx),
    .alu .sbb .r8 (.reg .r8), .alu .xor .r8 (.imm (BitVec.ofInt 32 (-1))), .alu .and .r8 (.reg .r11),
    .alu .and .rax (.reg .r8), .store8 (bx .rdi .rcx) .rax, .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .r9)]

def selLoop : Prog isa := .loop (.block selBody) .ne

def selPart : Prog isa :=
  .seq (.block validBlock) (.seq (.block outPtrs) (.seq (.block outInit) (.seq selLoop
    (.block [.mov .rax (.mem (sp oR))]))))

/-! ## The function -/

/-- The body of the frame, with the private-key operation `priv` (by its
name `privN`). -/
def body (privN : String) (priv : Prog isa) : Prog isa :=
  .seq (.block setup) (.seq (.call privN priv) (.seq dBuild (.seq (hashD H) (.seq (kdkMac H) (.seq (clLoop H)
    (.seq (amLoop H) (.seq maskPart (.seq alPart (.seq scanPart selPart)))))))))

/-- `vg_rsa_pkcs1_decrypt`. -/
def code (privN : String) (priv : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes) (body H privN priv) (.free frameBytes)

end VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
