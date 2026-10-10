import VerifiedGarbage.Impl.Cast5.Tables
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Cast5.Lines

/-!
# CAST5 on baseline x86-64

A lookup in an S-box never uses a secret as an address: the four lookups a
round function makes, `S1[Ia]`, `S2[Ib]`, `S3[Ic]` and `S4[Id]`, are made at
once by a *scan* of a table of 256 entries of 16 bytes, entry `i` the four
dwords `S4[i], S3[i], S2[i], S1[i]` (`VG_CAST5_S1234`), in SSE2 registers: the
indices are the four dword lanes of `xmm0`, `pcmpeqd` with the entry's number
in every lane (`xmm2`) gives a mask that is all ones in the lanes whose index
it is, and the entry is ANDed with it and ORed into the result, `xmm1`; every
entry is loaded, in order. Key expansion scans `VG_CAST5_S5678` the same way,
entry `i` the dwords `S8[i], S7[i], S6[i], S5[i]`.

The rotation by the secret amount `Kr` (§2.2) is five rotations by 1, 2, 4, 8
and 16, each kept or not by a mask made from a bit of `Kr` (`rotate`).

Registers of the scan: the table in `r10`, the count of groups of four
entries left in `r11`, `xmm0`–`xmm5`.
-/

namespace VG.Impl.Cast5.X86_64

open VG.X86_64

/-- `[base + offset]`. -/
def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := Int.ofNat offset }

/-- An immediate. -/
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-! ## The scan -/

/-- Entry `e` of the four at `r10`: its mask, from the indices in `xmm0` and the
entry's number in every lane of `xmm2`, ANDed with it and ORed into `xmm1`;
then the next number. -/
def scanEntry (e : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm4 .xmm0), .xop (.bin .pcmpeqd .xmm4 .xmm2),
   .movdquLoad .xmm5 (at_ .r10 (16 * e)), .xop (.bin .pand .xmm5 .xmm4),
   .xop (.bin .por .xmm1 .xmm5), .xop (.bin .paddd .xmm2 .xmm3)]

/-- Four entries, then on to the next four (ZF is set after the last). -/
def scanBody : List Instr :=
  (List.range 4).flatMap scanEntry ++ ([.alu .add .r10 (imm 64), .alu .sub .r11 (imm 1)] : List Instr)

/-- The table `sym` at the indices in the lanes of `xmm0` (each less than
256), into the lanes of `xmm1`. Clobbers `r10`, `r11`, `xmm1`–`xmm5` and the
flags. -/
def scan (sym : String) : Prog isa :=
  .seq (.block [.leaSym .r10 sym, .mov32 .r11 (imm 64), .xop (.bin .pxor .xmm1 .xmm1),
      .xop (.bin .pxor .xmm2 .xmm2), .xop (.bin .pcmpeqd .xmm3 .xmm3), .xop (.shift .psrld .xmm3 31)])
    (.loop (.block scanBody) .ne)

/-- `xmm0` := the dwords `lo₀, hi₀, lo₁, hi₁`, from the quadwords `lo₀ | hi₀ << 32`
in `r9` and `lo₁ | hi₁ << 32` in `r`. -/
def lanes (r : Reg) : List Instr :=
  [.xop (.movq .xmm0 .r9), .xop (.movq .xmm4 r), .xop (.bin .punpcklqdq .xmm0 .xmm4)]

/-! ## Encryption and decryption -/

/-- One of the five steps of the rotation of `eax` left by the low 5 bits of
`r9` (shifted right by `b` so far): rotate by `2 ^ b` if bit 0 of `r9` is set.
`r14` := 0 if it is, all ones if not; the rotation is in `r15`. -/
def rotateStep (b : Nat) : List Instr :=
  ([.mov32 .r14 (.reg .r9), .alu32 .and .r14 (imm 1), .alu32 .sub .r14 (imm 1),
   .mov32 .r15 (.reg .rax), .shift32 .ror .r15 (32 - 2 ^ b),
   .alu32 .xor .rax (.reg .r15), .alu32 .and .rax (.reg .r14), .alu32 .xor .rax (.reg .r15)] : List Instr) ++
  (if b < 4 then [.shift32 .shr .r9 1] else [])

/-- `eax` rotated left by the low 5 bits of `r9`. Clobbers `r9`, `r14`, `r15`. -/
def rotate : List Instr := (List.range 5).flatMap rotateStep

/-- The bytes `Id, Ic, Ib, Ia` of `I` in `eax` into the lanes of `xmm0`.
Clobbers `r9`, `r14` and `xmm4`. -/
def spread : List Instr :=
  [.mov32 .r9 (.reg .rax), .alu32 .and .r9 (imm 255),
   .mov32 .r14 (.reg .rax), .shift32 .shr .r14 8, .alu32 .and .r14 (imm 255),
   .shift .shl .r14 32, .alu .or .r9 (.reg .r14), .xop (.movq .xmm0 .r9),
   .mov32 .r9 (.reg .rax), .shift32 .shr .r9 16, .alu32 .and .r9 (imm 255),
   .mov32 .r14 (.reg .rax), .shift32 .shr .r14 24,
   .shift .shl .r14 32, .alu .or .r9 (.reg .r14), .xop (.movq .xmm4 .r9),
   .xop (.bin .punpcklqdq .xmm0 .xmm4)]

/-- The round function's first step, `I` (before the rotation) in `eax`, for
`Kmᵢ` at `r12` and `D` in `ebp`: `Kmᵢ + D`, `Kmᵢ ^ D` or `Kmᵢ - D` for Type
1, 2 or 3. -/
def mask : Nat → List Instr
  | 1 => [.mov32 .rax (.mem (at_ .r12 0)), .alu32 .add .rax (.reg .rbp)]
  | 2 => [.mov32 .rax (.mem (at_ .r12 0)), .alu32 .xor .rax (.reg .rbp)]
  | _ => [.mov32 .rax (.mem (at_ .r12 0)), .alu32 .sub .rax (.reg .rbp)]

/-- `f` from `S4[Id], S3[Ic], S2[Ib], S1[Ia]` at `r8 + 0, 4, 8, 12`, into `eax`. -/
def combine : Nat → List Instr
  | 1 => [.mov32 .rax (.mem (at_ .r8 12)), .alu32 .xor .rax (.mem (at_ .r8 8)),
          .alu32 .sub .rax (.mem (at_ .r8 4)), .alu32 .add .rax (.mem (at_ .r8 0))]
  | 2 => [.mov32 .rax (.mem (at_ .r8 12)), .alu32 .sub .rax (.mem (at_ .r8 8)),
          .alu32 .add .rax (.mem (at_ .r8 4)), .alu32 .xor .rax (.mem (at_ .r8 0))]
  | _ => [.mov32 .rax (.mem (at_ .r8 12)), .alu32 .add .rax (.mem (at_ .r8 8)),
          .alu32 .xor .rax (.mem (at_ .r8 4)), .alu32 .sub .rax (.mem (at_ .r8 0))]

/-- `(L, R)` in `(ebx, ebp)` := `(R, L ^ f)`, then `r12` to the next round's
subkeys: up for encryption, down for decryption. -/
def feistel (up : Bool) : List Instr :=
  [.alu32 .xor .rax (.reg .rbx), .mov32 .rbx (.reg .rbp), .mov32 .rbp (.reg .rax),
   if up then .alu .add .r12 (imm 4) else .alu .sub .r12 (imm 4)]

/-- A round of Type `t` (1, 2 or 3) with the subkeys `Kmᵢ` at `r12` and `Krᵢ`
at `r12 + 64`. -/
def round (t : Nat) (up : Bool) : Prog isa :=
  .seq (.block (mask t ++ ([.mov32 .r9 (.mem (at_ .r12 64))] : List Instr) ++ rotate ++ spread))
    (.seq (scan s1234Sym)
      (.block (([.movdquStore (at_ .r8 0) .xmm1] : List Instr) ++ combine t ++ feistel up)))

/-- Three rounds, of Types 1, 2 and 3 (encryption) or 3, 2 and 1
(decryption), then the count of groups left (`r13`) down (ZF set at 0). -/
def group (up : Bool) : Prog isa :=
  .seq (round (if up then 1 else 3) up) (.seq (round 2 up)
    (.seq (round (if up then 3 else 1) up) (.block [.alu .sub .r13 (imm 1)])))

/-- `r13` := `rounds / 4 + 1`: 4 groups for 12 rounds, 5 for 16; ZF set if
`rounds` is 16. -/
def groups : List Instr :=
  [.mov .r13 (.reg .rsi), .shift .shr .r13 2, .alu .add .r13 (imm 1), .alu .cmp .rsi (imm 16)]

/-- The block at `rdx` into `(ebx, ebp)` = `(L₀, R₀)`. -/
def load : List Instr :=
  [.mov32 .rbx (.mem (at_ .rdx 0)), .bswap32 .rbx, .mov32 .rbp (.mem (at_ .rdx 4)), .bswap32 .rbp]

/-- `(Rₙ, Lₙ)` to the block at `rdx`, then on to the next block (ZF set when
none are left). -/
def store : List Instr :=
  [.bswap32 .rbp, .store32 (at_ .rdx 0) .rbp, .bswap32 .rbx, .store32 (at_ .rdx 4) .rbx,
   .alu .add .rdx (imm 8), .alu .sub .rcx (imm 1)]

/-- Encrypting a block: rounds 1–15 in groups of three, then round 16 if
there are 16. -/
def encryptBlock : Prog isa :=
  .seq (.block (load ++ ([.mov .r12 (.reg .rdi)] : List Instr) ++ groups))
    (.seq (.loop (group true) .ne)
      (.seq (.block [.alu .cmp .rsi (imm 16)]) (.seq (.ite .e (round 1 true) (.block []))
        (.block store))))

/-- Decrypting a block: round 16 if there are 16, then the rest in groups of
three, down from the last; `r12` starts at `Kmₙ`, `rdi + 4 (rounds - 1)`. -/
def decryptBlock : Prog isa :=
  .seq (.block (load ++ ([.mov .r12 (.reg .rsi), .shift .shl .r12 2, .alu .add .r12 (.reg .rdi),
      .alu .sub .r12 (imm 4)] : List Instr) ++ groups))
    (.seq (.ite .e (round 1 false) (.block []))
      (.seq (.loop (group false) .ne) (.block store)))

/-- The registers saved in the working space, and where. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 16), (.rbp, 24), (.r12, 32), (.r13, 40), (.r14, 48), (.r15, 56)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r8 d) r
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r8 d))

/-- `vg_cast5_ecb_encrypt(schedule = rdi, rounds = rsi, data = rdx, n = rcx,
scratch = r8)`, or decrypt: each block in turn. -/
def ecb (block : Prog isa) : Prog isa :=
  .seq (.block (save ++ ([.alu .test .rcx (.reg .rcx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop block .ne)) (.block restore))

def ecbEncrypt : Prog isa := ecb encryptBlock
def ecbDecrypt : Prog isa := ecb decryptBlock

/-! ## Key expansion

`x0 … xF` and `z0 … zF` are kept in the working space at `rcx + 16` and
`rcx + 32`, a byte each, in order; the subkeys are written to `rdx`, which
moves on 64 bytes after each half. Only caller-saved registers are used. -/

/-- Where the four extra lookups of a group of lines are kept. -/
def extraOff : Nat := 48

/-- The lanes `S8[d], S7[c], S6[b], S5[a]` of a scan of `VG_CAST5_S5678`, for
the bytes `a, b, c, d`. Clobbers `rax`, `r9`, `r10`, `xmm4`. -/
def gather (a b c d : Pos) : List Instr :=
  ([.movzx8 .r9 (at_ .rcx (srcOff d)), .movzx8 .rax (at_ .rcx (srcOff c)),
   .shift .shl .rax 32, .alu .or .r9 (.reg .rax),
   .movzx8 .r10 (at_ .rcx (srcOff b)), .movzx8 .rax (at_ .rcx (srcOff a)),
   .shift .shl .rax 32, .alu .or .rax (.reg .r10)] : List Instr) ++ lanes .rax

/-- A line `S5[a] ^ S6[b] ^ S7[c] ^ S8[d] ^ Sₑ[f] ^ w`, into `eax`: `Sₑ[f]` from
the group's extra lookups (lane `8 - e` of those at `rcx + 48`), `w` the
quadruple of an array, big-endian, if any. -/
def line (l : Line) : Prog isa :=
  .seq (.block (gather l.main.1 l.main.2.1 l.main.2.2.1 l.main.2.2.2)) (.seq (scan s5678Sym)
    (.block (([.movdquStore (at_ .rcx 0) .xmm1, .mov32 .rax (.mem (at_ .rcx 0)),
      .alu32 .xor .rax (.mem (at_ .rcx 4)), .alu32 .xor .rax (.mem (at_ .rcx 8)),
      .alu32 .xor .rax (.mem (at_ .rcx 12)),
      .alu32 .xor .rax (.mem (at_ .rcx (extraOff + 4 * (8 - l.extra.1))))] : List Instr) ++
      (match l.word with
        | some (a, q) => [.mov32 .r9 (.mem (at_ .rcx (off a + 4 * q))), .bswap32 .r9,
            .alu32 .xor .rax (.reg .r9)]
        | none => []))))

/-- The extra lookups of a group: `S5[a], S6[b], S7[c], S8[d]`, to the lanes
3, 2, 1, 0 at `rcx + 48`. -/
def extras (a b c d : Pos) : Prog isa :=
  .seq (.block (gather a b c d)) (.seq (scan s5678Sym)
    (.block [.movdquStore (at_ .rcx extraOff) .xmm1]))

/-- Four lines, after their extra lookups, each followed by its store `st k`. -/
def lines4 (ls : List Line) (st : Nat → List Instr) : Prog isa :=
  .seq (extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8))
    ((List.range 4).foldr (fun k rest =>
      .seq (line (ls.getD k default))
        (.seq (.block (st k)) rest)) (.block []))

/-- Store `eax` as quadruple `q` of the array `a`, big-endian. -/
def storeQuad (a : Arr) (q : Nat) : List Instr := [.bswap32 .rax, .store32 (at_ .rcx (off a + 4 * q)) .rax]

/-- Store `eax` as subkey `k` at `rdx`. -/
def storeKey (k : Nat) : List Instr := [.store32 (at_ .rdx (4 * k)) .rax]

/-- One half of §2.4 (`Spec.Cast5.half`), with sixteen subkeys to `rdx`, then
`rdx` on 64 bytes and the count of halves left (`rsi`) down. -/
def half : Prog isa :=
  .seq (lines4 zLines (storeQuad .z)) (.seq (lines4 aLines storeKey)
    (.seq (lines4 xLines (storeQuad .x))
      (.seq (lines4 bLines fun k => storeKey (4 + k))
        (.seq (lines4 zLines (storeQuad .z)) (.seq (lines4 cLines fun k => storeKey (8 + k))
          (.seq (lines4 xLines (storeQuad .x))
            (.seq (lines4 dLines fun k => storeKey (12 + k))
              (.block [.alu .add .rdx (imm 64), .alu .sub .rsi (imm 1)]))))))))

/-- Copy a key byte to `x`: `rdi` at the next key byte, `rax` at its place in
`x`, `rsi` the count left. -/
def copyStep : List Instr :=
  [.movzx8 .r9 (at_ .rdi 0), .store8 (at_ .rax 0) .r9, .alu .add .rdi (imm 1),
   .alu .add .rax (imm 1), .alu .sub .rsi (imm 1)]

/-- `vg_cast5_expand_key(key = rdi, key_len = rsi, schedule = rdx, scratch =
rcx)`: `x` := the key padded with zeros (§2.5), then both halves. -/
def expandKey : Prog isa :=
  .seq (.block [.mov32 .rax (imm 0), .store (at_ .rcx xOff) .rax, .store (at_ .rcx (xOff + 8)) .rax,
      .mov .rax (.reg .rcx), .alu .add .rax (imm xOff)])
    (.seq (.loop (.block copyStep) .ne)
      (.seq (.block [.mov32 .rsi (imm 2)]) (.loop half .ne)))

end VG.Impl.Cast5.X86_64
