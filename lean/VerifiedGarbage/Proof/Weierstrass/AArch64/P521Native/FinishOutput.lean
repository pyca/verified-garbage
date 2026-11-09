module

-- separate module: the literal last-block identity is checked separately from the generic security-check and serialization contracts

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareValidate
public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! The final public checks and masked output retain the existing ECDH code. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock171)
open VG.Impl.Ecdsa.AArch64 (D RZ)

theorem finish_output_source : outerBlock171=
    ([.umov .x .x30 .v29 0] : List Instr)++
    (config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++
      VG.Impl.Ecdh.AArch64.Cfg.finish config) := by lit_decide

/-- Every postcondition of the existing checked output block transfers to the
actual native suffix, including invalid-input masking and ABI restoration. -/
theorem finish_output_wp {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.block [.umov .x .x30 .v29 0])
      (.block (config.checkRange (config.sl D)++config.checkNonzero (config.sl RZ)++
        VG.Impl.Ecdh.AArch64.Cfg.finish config))) s Q) :
    WP isa (.block outerBlock171) s Q := by
  rw [finish_output_source,VG.WP.block_append_iff]
  exact VG.WP.seq_iff.mp h

end VG.Proof.Weierstrass.AArch64.P521Native
