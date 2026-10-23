module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# Streaming TDEA-CMAC on PPC64LE is constant time

Only the pointers, `count`, `len` and `key_len` are public: `r3`–`r6`, and
`r7` for `absorb`. The key expansion and the block function are analysed at
their calls; the block function never writes `r29`–`r31`, which hold what
`absorb` counts across its calls, nor `r3`–`r5`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- The public arguments of `stream_init` and `finish`, and of `absorb`. -/
abbrev pub4 : State → State → Prop := Proof.TripleDes.PPC64LE.PublicRegs [.r3, .r4, .r5, .r6]
abbrev pub5 : State → State → Prop := Proof.TripleDes.PPC64LE.PublicRegs [.r3, .r4, .r5, .r6, .r7]

theorem init_ct (pre : State → Prop) : ConstantTime isa pre pub4 streamInit :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

theorem absorb_ct (pre : State → Prop) : ConstantTime isa pre pub5 absorb :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

theorem finish_ct (pre : State → Prop) : ConstantTime isa pre pub4 finish :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

end VG.Proof.CmacTripleDes.Stream.PPC64LE
