module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common

/-!
# DSA domain checks on PPC64LE

`vg_dsa_check_parameters(params = r3, params_len = r4, p_len = r5,
q_len = r6, scratch = r7, scratch_len = r8)`. After an entry like
verification's, which saves the nonvolatile registers in `scratch`'s header
and keeps the domain p||q||g in `r27` and the lengths in `r2`, `checkParams`
(`Common.lean`) branches on the domain, all of it public, and leaves 1 or 0.
-/

@[expose] public section

namespace VG.Impl.Dsa.PPC64LE.Params

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- The working space, the registers saved there, the domain into `r27`
(`r28` and `r26`, which name the signature and the digest elsewhere, 0), and
the lengths into `r2`. -/
def entry : List Instr :=
  [.addi .r11 .r7 0] ++ save .r11 ++
    [.addi .r27 .r3 0, .li .r28 0, .li .r26 0, .lsl .r0 .r6 16, .add .r2 .r5 .r0]

/-- `vg_dsa_check_parameters`. -/
def checkParameters : Prog isa :=
  .seq (.block entry) (.seq (checkParams (.block [.li .r3 1]) (.block [.li .r3 0])) (.block restore))

end VG.Impl.Dsa.PPC64LE.Params
