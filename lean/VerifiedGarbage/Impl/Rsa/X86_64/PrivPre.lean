module

public import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# An RSA private key's precomputed values on x86-64

`vg_rsa_private_precompute(pre = rdi, pre_len = rsi, n = rdx, n_len = rcx,
p = r8, p_len = r9, q, q_len, scratch, scratch_len)`, the last four on the
stack: with the modulus `n` (`k = n_len` bytes) of `w = ⌈k / 8⌉` words and
its factors `p` and `q`, writes `n` and `R² mod n` (`w` words each), then
`R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)` words) and `R_q² mod q` to
`pre` and returns 1 if `n` is valid and `p q = n`, and otherwise writes zeros
and returns 0.

1. The arguments are saved in the header (`entry`), and `pre`'s `pre_len`
   words zeroed (`zeroPre`), so that `pre` read as `vg_rsa_private_crt`'s
   input and as its `qInv` is 0.
2. With `pre` as the input and as `qInv` (and `p`, `q` as the exponents,
   which nothing reads), `vg_rsa_private_crt`'s own code (`Crt.lean`) checks
   `n`, branching on it (it is public), and on a valid `n` sets up `n`'s
   workspace (`n`, `R² mod n`, as `vg_rsa_public_precompute` computes it),
   the primes' and the mask of `0 < n`, `p q = n` and `0 < p`, which is that
   of `p q = n`; where it is clear, `p` and `q` are replaced by 3.
3. In each prime's workspace, `R_X² mod X = 2^(128 w_X) mod X` by `128 w_X`
   doublings of 1 (`r2X`), whose count is public.
4. `n`, `R² mod n`, `R_p² mod p` and `R_q² mod q` to `pre`, each word
   and-ed with the mask (`out`), and the mask's low bit returned.

Nothing branches on `p` or `q`: the loops count lengths, and the code
branches only on `n`'s validity.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- Save the callee-saved registers and the arguments in the header at
`scratch` (stack argument 3), with its base in `rdi`: `pre` as `sOut`, as
the input `sIn` and as `qInv`, and `p` and `q` also as the exponents. The
stack arguments are loaded first. -/
def entry : List Instr :=
  ([.mov .r11 (.mem (stk 3)), .mov .r10 (.mem (stk 1)), .mov .rax (.mem (stk 2))] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store (ws .r11 sOut) .rdi, .store (ws .r11 sN) .rdx, .store (ws .r11 sK) .rcx, .store (ws .r11 sIn) .rdi,
    .store (ws .r11 sP) .r8, .store (ws .r11 sPlen) .r9, .store (ws .r11 sDp) .r8, .store (ws .r11 sQinv) .rdi,
    .store (ws .r11 sQ) .r10, .store (ws .r11 sDq) .r10, .store (ws .r11 sQlen) .rax,
    .mov .rdi (.reg .r11)] : List Instr)

/-- `pre`'s `8 pre_len` bytes (`pre_len` in `rsi`) `:= 0`, as `fail` writes
zeros. -/
def zeroPre : Prog isa :=
  .seq (.block [.mov .rcx (.reg .rsi), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rcx), .mov .rsi (.mem (hdr sOut)), .mov32 .rax (.imm 0)])
    (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)

/-- `rcx := 128 w`, the count of the doublings. -/
def count : List Instr := [.mov .rcx (.mem (hdr sW)), .shift .shl .rcx 7]

/-- In a prime's workspace: `[aY] := 2^(128 w_X) mod X`, by `128 w_X`
doublings of 1, counted in slot `sRem`. -/
def r2X : List (Prog isa) :=
  copyArr aY aOne ++ [.block count, doubles aN aAcc aTmp aY sRem]

/-- `R_X² mod X` in the workspace whose base slot `slotWs` holds. -/
def r2At (slotWs : Nat) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr slotWs))]] ++ r2X ++ [.block [leave]]

/-- `R_X² mod X` in both primes' workspaces. -/
def r2Phase : List (Prog isa) := r2At sWsP ++ r2At sWsQ

/-- `w` words (`r12`) from `[rsi]` to `[rbx]`, each and-ed with `r15`. -/
def copyMasked : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .alu .and .rax (.reg .r15), .store (ix .rbx .r14) .rax]

/-- The current workspace's array `j`, masked, to `[rbx]`, and `rbx` past
it. -/
def outArr (j : Nat) : List (Prog isa) :=
  [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr j)))], copyMasked,
    .block (eightW ++ ([.alu .add .rbx (.reg .rax)] : List Instr))]

/-- The array `aY` of the workspace whose base slot `slotWs` holds,
masked, to `[rbx]`, and `rbx` past it. -/
def outAt (slotWs : Nat) : List (Prog isa) :=
  [.block [.mov .rdi (.mem (hdr slotWs))]] ++ outArr aY ++ [.block [leave]]

/-- `n`, `R² mod n`, `R_p² mod p` and `R_q² mod q` to `pre`, masked, and
the mask's low bit returned. -/
def out : List (Prog isa) :=
  [.block [.mov .rbx (.mem (hdr sOut)), .mov .r15 (.mem (hdr sMask))]] ++ outArr aN ++ outArr aR2 ++
  outAt sWsP ++ outAt sWsQ ++
  [.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)]

/-- The computation, once `n` is known valid. -/
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ r2Phase ++ out)

/-- `vg_rsa_private_precompute`, with the multiplication `mul`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block entry) (.seq zeroPre (.seq (.block (([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++
    invalid)) (.ite .ne fail (main mul))))

end VG.Impl.Rsa.X86_64.PrivPre
