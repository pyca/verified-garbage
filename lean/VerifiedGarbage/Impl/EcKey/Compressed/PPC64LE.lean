module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE

/-!
# SEC 1 point compression on PPC64LE

`vg_ec_<curve>_compress_public_key(out, public, scratch) -> r3` (ELFv2: the
arguments in `r3`–`r5`), from the code of ECDH (`Impl/Ecdh/PPC64LE.lean`),
as on 32-bit ARM (`Impl/EcKey/Compressed/Arm.lean`):

1. `public` to `r12`, then the signature's setup, reading `k`, `d` and the
   hash all from `public` (`args`; ECDH's peer parsing then replaces the
   hash's slot);
2. ECDH's parsing and validation of the key `r12` points to: its first byte
   `04`, both coordinates below `p` and the curve's equation, as a mask in
   the flag;
3. `02 + (y mod 2)` and `x` (or zeros, by the flag) to `out` (in `r14`), and
   the flag's low bit returned.
-/

@[expose] public section
namespace VG.Impl.EcKey.Compressed.PPC64LE

open VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass
open VG.Impl.Ecdsa.PPC64LE

/-- The setup reads `k`, `d` and the hash from the key (in `r12`), within its
encoding; the peer's parsing replaces the hash's slot. -/
abbrev args : Args := ⟨.r12, .r12, .r12, .r5, none⟩

/-- `public` to `r12` and the signature's setup. -/
def setup (c : Cfg) : List Instr := [mov .r12 .r4] ++ c.setupWith args

/-- The tag, `((y & 1) + 2) & flag`, to `out`'s first byte, through `r4` and
`r5`. -/
def compressTag (c : Cfg) : List Instr :=
  [.load .d .r4 wb (c.sl Ecdh.PPC64LE.QY), .li .r5 1, .logic .and .r4 .r4 .r5, .addi .r4 .r4 2,
    .logic .and .r4 .r4 .r10, .stb .r4 .r14 0]

/-- The flag, the tag, `x` (or zeros) from `out + 1`, the flag's low bit to
`r3`, and the callee-saved registers restored. -/
def compressFinish (c : Cfg) : List Instr :=
  [.load .d .r10 wb (c.sl FLAG)] ++ compressTag c ++
  storeBytes c.C.len c.n .r14 1 (c.sl E) ++
  ([.li .r4 1, .logic .and .r4 .r10 .r4] : List Instr) ++ Cfg.restore ++ [mov .r3 .r4]

/-- `vg_ec_<curve>_compress_public_key`. -/
def compress (c : Cfg) : Prog isa :=
  .seq (.block (setup c)) <|
  .seq (.block (Ecdh.PPC64LE.Cfg.peerAt c .r12)) <|
  .seq (Ecdh.PPC64LE.Cfg.validate c) (.block (compressFinish c))

end VG.Impl.EcKey.Compressed.PPC64LE
