module

public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round

/-! # A Miller–Rabin round for public candidates

The shared round (`vg_miller_rabin_round`) copies a window's table entry
`T_d` by scanning all 16 entries under masks, since RSA key generation's
candidates are secret. The candidates of DSA's parameter search are public,
and with them the windows' digits: this round copies the one entry. -/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

/-- `[aXm] := T_d` for the public digit `d` in `kG`: the entry's base is
`T_0`'s and `d` strides. -/
def publicSel : List (Prog isa) := [
  .block (ws ++ base aXm .x17 ++ base aT0 .x16 ++
    ([ldh .x9 kG, .mul .x .x9 .x9 .x11, .add .x .x16 .x16 .x9] : List Instr)),
  copyWords]

/-- One window, its table entry read directly. -/
def publicWin (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := mrWinS publicSel mul

/-- `(ws = x0, ws_len = x1)`: one round from the prepared workspace, for a
public candidate. -/
def publicRound (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  VG.Impl.MillerRabin.AArch64.roundW (publicWin mul) mul

end VG.Impl.Dsa.AArch64.Generation
