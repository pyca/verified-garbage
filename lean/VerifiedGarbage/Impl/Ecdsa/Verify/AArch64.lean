import VerifiedGarbage.Impl.Ecdh.AArch64

/-!
# ECDSA signature verification on AArch64

`vg_ecdsa_<curve>_verify(public = x0, digest = x1, sig = x2,
scratch = x3) -> w0`, for a curve of `n` 64-bit words, from the code of
ECDSA's signature (`Impl/Ecdsa/AArch64.lean`) and of ECDH
(`Impl/Ecdh/AArch64.lean`), whose layout of the working space it uses, as
on x86-64 (`Impl/Ecdsa/Verify/X86_64.lean`):

1. `scratch` to `x4`, `public` to `x6`, `sig` to `x3` (the signature's
   `k`), `sig + len` to `x8` and `public + 1` to `x2` (its hash); then
   the signature's setup and tables of bits: `r` is read into the slot of
   `k`, the hash (`digest = x1`) into that of `d`, shifted right by the bits
   of the digest that are not `e`'s, the key's `x` into that of the hash;
   then `s` into `PT` (which only the powers use);
2. ECDH's checks of the key (`peer`, `validate`): its first byte, `x < p`,
   `y < p` and the curve's equation, into the flag, and the key's point, or
   `G` if the flag is clear, to the slots of ECDH's window method;
3. the masks of `r` and `s` in `[1, n-1]` into the flag, and
   `w = s^(n-2)`, in Montgomery form modulo `n`;
4. `u = e w` and `v = r w` modulo `n`, out of Montgomery's form;
5. `[u]G` by the signature's comb (from the table of `u`'s bits), saved
   to `U`, and `R` reset to `O`; then `[v]Q` by ECDH's window method and
   `[u]G + [v]Q` by the complete addition, into `R`;
6. for P-256, compare `X` with `rZ` and, when `r+n < p`, `(r+n)Z`, without
   inversion; for the other curves, compute `x = X Z^(p-2)` and compare it
   with `r` modulo `n`. Reject `Z = 0` and return the accumulated flag.

All validity checks run regardless of earlier failures. P-256's comb
addresses depend on its public scalar; the remaining memory accesses and
branches depend only on pointers and fixed loop counters.
-/

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

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

variable (c : Impl.Ecdsa.AArch64.Cfg)

/-- `scratch` to `x4`, `public` to `x6`, `sig` to `x3`, `sig + len` to
`x8` and `public + 1` to `x2`: the signature's arguments, with `k` the
signature's `r`, `d` the hash and the hash the key's `x`. -/
def args : List Instr :=
  [.addImm .x .x4 .x3 0, .addImm .x .x6 .x0 0, .addImm .x .x3 .x2 0, .addImm .x .x8 .x2 c.C.len,
    .addImm .x .x2 .x0 1]

/-- `s`, into `PT`. -/
def loadS : List Instr := loadBytes c.C.len c.n (c.sl PT) .x8

/-- The checks of `r` and `s`, and `s R mod n`. -/
def scalars : Prog isa :=
  blocks [c.checkRange (c.sl K) ++ c.checkRange (c.sl PT),
    Mont.AArch64.mul c.MN' (c.sl SM') (c.sl PT) (c.sl R2N)]

/-- `u` and `v`, from `w R mod n` in `ACC`. -/
def uv : Prog isa :=
  blocks [Mont.AArch64.mul c.MN' (c.sl EM') (c.sl D) (c.sl R2N),
    Mont.AArch64.mul c.MN' (c.sl RM') (c.sl K) (c.sl R2N),
    Mont.AArch64.mul c.MN' (c.sl UM) (c.sl EM') (c.sl ACC),
    Mont.AArch64.mul c.MN' (c.sl VM) (c.sl RM') (c.sl ACC),
    Mont.AArch64.mul c.MN' (c.sl U) (c.sl UM) (c.sl ONE),
    Mont.AArch64.mul c.MN' (c.sl V) (c.sl VM) (c.sl ONE)]

/-- `U = R`, then `R = O = (0 : 1 : 0)`. -/
def save : List Instr :=
  copy c.n (c.sl UX) (c.sl RX) ++ copy c.n (c.sl UY) (c.sl RY) ++ copy c.n (c.sl UZ) (c.sl RZ) ++
  setConst c.n (c.sl RX) 0 ++ setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0

/-- `R = U + R`, through `D`. -/
def sum : Prog isa :=
  .seq (fprogB c.MP' (rcb3 c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)))
    (.block (copy c.n (c.sl RX) (c.sl DX) ++ copy c.n (c.sl RY) (c.sl DY) ++
      copy c.n (c.sl RZ) (c.sl DZ)))

/-- `x19`–`x25` restored, and the flag's low bit to `x0`. -/
def finish : List Instr :=
  [ld .x3 (c.sl FLAG)] ++ Impl.Ecdsa.AArch64.Cfg.saved.map (fun (r, d) => ld r d) ++
  [.movz .x .x1 1 0, .logic .and .x .x0 .x3 .x1]

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, `x R mod n`
and `x R - r R mod n`, the checks of `Z` and of `x ≡ r`, and the result. -/
def final : Prog isa :=
  blocks [Mont.AArch64.mul c.MP' (c.sl XM) (c.sl RX) (c.sl ACC),
    Mont.AArch64.mul c.MP' (c.sl X) (c.sl XM) (c.sl ONE),
    Mont.AArch64.mul c.MN' (c.sl XN) (c.sl X) (c.sl R2N),
    Mont.AArch64.sub c.MN' (c.sl W) (c.sl XN) (c.sl RM'),
    c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.AArch64.Cfg.checkZero c (c.sl W) ++ finish c]

/-- `[u]G + [v]Q`, into `R`: `[u]G` by the comb from the table of the bits of
`u`, `[v]Q` by ECDH's window method. P-256 verification selects its public
comb digits directly; the other curves retain the table scan. -/
def points : Prog isa :=
  .seq (bits (c.sl U) (bitsAt c.n 0) (8 * c.n)) <| .seq (TCombCfg.comb c.combCfg (c.C.len == 32)) <|
  .seq (.block (save c)) <|
  .seq (c.winPrep (c.sl V)) <| .seq (WinCfg.window (c.winCfg PX PY)) (sum c)

/-- The conversion factor, the order in field Montgomery form, and the
upper bound on the signature scalar for its second possible lift. -/
def projectivePrepare : List Instr :=
  setConst c.n (c.sl XM) (c.R * c.R % c.C.p) ++
  setConst c.n (c.sl ACC) (c.mont c.C.n) ++
  setConst c.n (c.sl MN) (c.C.p - c.C.n)

/-- The two differences, `X - rZ` and `X - (r+n)Z`, in field Montgomery form. -/
def projectiveOps (sl : Nat → Nat) : List FOp :=
  [.mul (sl X) (sl XM) (sl RZ), .sub (sl W) (sl RX) (sl X),
    .add (sl XM) (sl XM) (sl ACC), .mul (sl X) (sl XM) (sl RZ),
    .sub (sl XN) (sl RX) (sl X)]

/-- Accept the first equality, or the second when `r+n < p`, together with
all earlier validity checks and `Z ≠ 0`. -/
def projectiveMatch : List Instr :=
  VG.Impl.Ecdh.AArch64.Cfg.zero c (c.sl W) ++ [.addImm .x .x4 .x2 0] ++
  c.ltN (c.sl K) ++ [.addImm .x .x6 .x2 0] ++
  VG.Impl.Ecdh.AArch64.Cfg.zero c (c.sl XN) ++
  [.logic .and .x .x2 .x2 .x6, .logic .orr .x .x2 .x2 .x4]

def projectiveChecks : List Instr :=
  projectiveMatch c ++ c.andFlag ++ c.checkNonzero (c.sl RZ) ++ finish c

/-- ECDSA's final check using projective coordinates. The caller establishes
`n < p ≤ 2n`, so `r` and `r+n` exhaust the possible affine coordinates. -/
def projectiveFinal : Prog isa :=
  .seq (.seq (.block (projectivePrepare c))
    (.seq (.block (mul c.MP' (c.sl XM) (c.sl K) (c.sl XM)))
      (fprogB c.MP' (projectiveOps c.sl)))) (.block (projectiveChecks c))

/-- P-256 compares projective coordinates directly; the other curves retain
an affine conversion until the direct path has been benchmarked for them. -/
def tail : Prog isa :=
  if c.C.len = 32 ∧ c.C.n < c.C.p ∧ c.C.p ≤ 2 * c.C.n then projectiveFinal c
  else .seq c.pPow (final c)

/-- Everything after the checks of the key. -/
def back : Prog isa :=
  .seq (scalars c) <| .seq c.nPow <| .seq (uv c) <| .seq (points c) (tail c)

/-- `vg_ecdsa_<curve>_verify`. -/
def verify : Prog isa :=
  .seq (.block (args c)) <| .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <| .seq (.block (loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <| .seq (Impl.Ecdh.AArch64.Cfg.validate c) (back c)

end Cfg

end VG.Impl.Ecdsa.Verify.AArch64
