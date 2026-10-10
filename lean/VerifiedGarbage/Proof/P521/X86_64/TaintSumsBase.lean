import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Proof.P521.X86_64.FieldTmpl

/-!
# P-521 on x86-64: what the summaries of the shared loops start from

The comb's data, the window's configuration and the taints the summaries
(`TaintSums`, `TaintSumsWin`, `TaintSumsWinNorm` and their ADX versions, each its own module,
checked in parallel) start from.
-/

namespace VG.Proof.P521.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64

/-- P-521's comb. -/
abbrev p521d : CombData := ⟨7, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", false⟩

/-- What is public at the comb's loop. -/
def τL : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .rbx, .rsi, .rsp]

/-- What is public at the batches' loop. -/
def τI : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .r14, .rsi, .rsp]

/-- ECDH's window method. -/
abbrev winK : WinCfg := p521.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

theorem winK_ok : p521T.Ok winK.M := p521T_ok

/-- ECDH's window method, with BMI2 and ADX. -/
abbrev winKX : WinCfg := p521x.winCfg Impl.Ecdh.X86_64.PX Impl.Ecdh.X86_64.PY Impl.Ecdh.X86_64.BP

theorem winKX_ok : p521XT.Ok winKX.M := p521XT_ok

/-- What is public at the table. -/
def τB : VG.X86_64.Taint.T := Taint.ofRegs [.rdi, .rsi, .rsp]

end VG.Proof.P521.X86_64
