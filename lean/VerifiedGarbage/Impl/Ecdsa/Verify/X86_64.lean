import VerifiedGarbage.Impl.Ecdh.X86_64

/-!
# ECDSA signature verification on x86-64

`vg_ecdsa_<curve>_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx) -> eax`, for a curve of `n` 64-bit words, from the code of
ECDSA's signature (`Impl/Ecdsa/X86_64.lean`) and of ECDH
(`Impl/Ecdh/X86_64.lean`), whose layout of the working space it uses:

1. `scratch` to `r8`, `public` to `r9`, `sig` to `rcx` (the signature's
   `k`), `public + 1` to `rdx` (its hash) and `sig + len` to `r10`; then
   the signature's setup and tables of bits: `r` is read into the slot of
   `k`, the hash into that of `d` (and shifted to `e`), the key's `x` into
   that of the hash; then `s` into `PT` (which only the powers use);
2. ECDH's checks of the key (`peer`, `validate`): its first byte, `x < p`,
   `y < p` and the curve's equation, into the flag, and the key's point, or
   `G` if the flag is clear, to the slots of ECDH's ladder;
3. the masks of `r` and `s` in `[1, n-1]` into the flag, and
   `w = s^(n-2)` (by the signature's inversion or power), in Montgomery form
   modulo `n`;
4. `u = e w` and `v = r w` modulo `n`, out of Montgomery's form;
5. `[u]G` by the signature's comb, or its ladder for a curve without one
   (`Cfg.gMul`, from the table of `u`'s bits), saved
   to `U`, and `R` reset to `O`; then `[v]Q` by ECDH's window method (for
   up to nine words, with `b R mod p` set again in ECDH's slot of it), or
   its ladder (from the table of `v`'s bits), and `[u]G + [v]Q` by the
   complete addition, into `R`;
6. for P-256, compare `X` with `r Z` and, when `r + n < p`, `(r + n) Z`;
   other curves invert `Z` and compare the affine x-coordinate modulo `n`.
   Reject `Z = 0` and return the combined validity flag as 0 or 1.

Everything is computed whatever the flag. P-256 directly indexes the fixed-base
table using the public verification scalar. The shared contract declares
the public key, digest and signature public; secret signing scalars continue
to use constant-time table scans.
-/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64

/-! Slots of the signature's layout, as verification uses them, after ECDH's
checks of the key: `K` holds `r`, `D` the hash and `PT` `s` (until the
power modulo `n`). -/

/-- `s R mod n`, the power's base. -/
def SM' : Nat := KM
/-- `e R mod n` and `r R mod n`. -/
def EM' : Nat := EM
def RM' : Nat := DM
/-- `u R` and `v R` modulo `n`, then `u` and `v`. -/
def UM : Nat := TT
def VM : Nat := SM
def U : Nat := XM
def V : Nat := X
/-- `[u]G`. -/
def UX : Nat := TT
def UY : Nat := SM
def UZ : Nat := KM
/-- `x R mod n`, and `x R - r R mod n`. -/
def XN : Nat := RM
def W : Nat := EM

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `scratch` to `r8`, `public` to `r9`, `sig` to `rcx`, `sig + 8 n` to
`r10` and `public + 1` to `rdx`: the signature's arguments, with `k` the
signature's `r`, `d` the hash and the hash the key's `x`. -/
def args : List Instr :=
  [.mov .r8 (.reg .rcx), .mov .r9 (.reg .rdi), .mov .rcx (.reg .rdx), .mov .r10 (.reg .rdx),
    .alu .add .r10 (.imm (BitVec.ofNat 32 c.C.len)), .mov .rdx (.reg .rdi), .alu .add .rdx (.imm 1)]

/-- `s`, into `PT`. -/
def loadS : List Instr := loadBytes c.C.len c.n (c.sl PT) .r10

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  blocks [c.checkRange (c.sl K) ++ c.checkRange (c.sl PT),
    Mont.X86_64.mul c.MN' (c.sl SM') (c.sl PT) (c.sl R2N)]

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  blocks [Mont.X86_64.mul c.MN' (c.sl EM') (c.sl D) (c.sl R2N),
    Mont.X86_64.mul c.MN' (c.sl RM') (c.sl K) (c.sl R2N),
    Mont.X86_64.mul c.MN' (c.sl UM) (c.sl EM') (c.sl ACC),
    Mont.X86_64.mul c.MN' (c.sl VM) (c.sl RM') (c.sl ACC),
    Mont.X86_64.mul c.MN' (c.sl U) (c.sl UM) (c.sl ONE),
    Mont.X86_64.mul c.MN' (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy c.n (c.sl UX) (c.sl RX) ++ copy c.n (c.sl UY) (c.sl RY) ++ copy c.n (c.sl UZ) (c.sl RZ) ++
  setConst c.n (c.sl RX) 0 ++ setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprogB c.MP' (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++ copy c.n (c.sl RY) (c.sl DY) ++
      copy c.n (c.sl RZ) (c.sl DZ)))

/-- The flag's low bit to `rax`, and the callee-saved registers restored. -/
def finish : List Instr :=
  [.mov .rax (.mem (sc (c.sl FLAG))), .alu .and .rax (.imm 1)] ++
  Impl.Ecdsa.X86_64.Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  blocks [Mont.X86_64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.X86_64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.X86_64.mul c.MN' (c.sl XN) (c.sl X) (c.sl R2N),
    Mont.X86_64.sub c.MN' (c.sl W) (c.sl XN) (c.sl RM'),
    c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.X86_64.Cfg.checkZero c (c.sl W) ++ finish c]

/-- Constants for comparison in projective coordinates. `MN` is no longer
needed for arithmetic modulo the group order. -/
def projectivePrepare : List Instr :=
  setConst c.n (c.sl XM) (c.R * c.R % c.C.p) ++
  setConst c.n (c.sl ACC) (c.mont c.C.n) ++ setConst c.n (c.sl MN) (c.C.p - c.C.n)

/-- Homogeneous coordinates use `X = x Z`: compute both possible lifts of
`x mod n = r`, without an inversion. -/
def projectiveOps (sl : Nat → Nat) : List FOp :=
  [.mul (sl X) (sl XM) (sl RZ), .sub (sl W) (sl RX) (sl X),
    .add (sl XM) (sl XM) (sl ACC), .mul (sl X) (sl XM) (sl RZ), .sub (sl XN) (sl RX) (sl X)]

/-- Match `X = r Z`, or `X = (r+n) Z` with `r+n < p`. -/
def projectiveMatch : List Instr :=
  Impl.Ecdh.X86_64.Cfg.zero c (c.sl W) ++ ([.mov .rbp (.reg .rdx)] : List Instr) ++
  c.ltN (c.sl K) ++ ([.mov .r12 (.reg .rax)] : List Instr) ++
  Impl.Ecdh.X86_64.Cfg.zero c (c.sl XN) ++
  [.alu .and .rdx (.reg .r12), .alu .or .rdx (.reg .rbp)]

/-- Reject infinity and combine the match with the preceding input checks. -/
def projectiveChecks : List Instr :=
  projectiveMatch c ++ c.andFlag ++ c.checkNonzero (c.sl RZ) ++ finish c

/-- Verify using the projective x-coordinate. -/
def projectiveFinal : Prog isa :=
  .seq (.seq (.block (projectivePrepare c))
    (.seq (.block (Mont.X86_64.mul c.MP' (c.sl XM) (c.sl K) (c.sl XM)))
      (fprogB c.MP' (projectiveOps c.sl)))) (.block (projectiveChecks c))

/-- P-256 has at most two possible field representatives of `x mod n`. -/
def tail : Prog isa :=
  if c.C.len = 32 ∧ c.C.n < c.C.p ∧ c.C.p ≤ 2 * c.C.n then projectiveFinal c
  else .seq c.pPow (final c)

/-- `[v]Q`, into `R`: for up to nine words, `b R mod p` to ECDH's `BP` (the
hash's `e R mod n` was there) and ECDH's window method from `v`; for more,
the table of `v`'s bits and ECDH's ladder. -/
def mulV : Prog isa :=
  if c.n ≤ 9 then
    .seq (.block (setConst c.n (c.sl Impl.Ecdh.X86_64.BP) (c.mont c.C.b)))
      (.seq (c.winPrep (c.sl V)) (WinCfg.window (c.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY
        Impl.Ecdh.X86_64.BP)))
  else .seq (bits (c.sl V) (bitsAt c.n 0) (8 * c.n)) (ladder (Impl.Ecdh.X86_64.Cfg.ladderQ c))

/-- `[u]G + [v]Q`, into `R`, from `u` and `v`. -/
def points : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (c.gMul (c.C.len == 32)) <| .seq (.block (save c)) <|
  .seq (mulV c) (sum c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (points c) (tail c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <| .seq (Impl.Ecdh.X86_64.Cfg.validate c) (back c)

end Cfg

end VG.Impl.Ecdsa.Verify.X86_64
