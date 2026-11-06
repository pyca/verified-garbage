module

-- separate module: the taint analysis builds in parallel with the correctness proofs, which it does not import

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Random
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Random
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: the blocks' taint

The saves, the call's arguments, the wipe of `PS` and the restores address
only the frame and the tape (`r30`); each octet of the scan is read at
`r3 + r4` and kept at `r7 + r5`, and the scan goes on by `r28`, `r5`, `r11`
and `r4`; on a short tape, `out` (`r31`, `r29` octets) is zeroed, the `r5`
octets drawn wiped, and the branches are on `r10`, `r5` and `r28`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Random VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.RsaPkcs1Sig.PPC64LE (fillLoop)

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block setup) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem nil_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block []) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem load_taint (h : Pins Φ [.r3, .r4]) : RelCT isa (Two Φ) (.block load) fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem keep_taint (h : Pins Φ [.r5, .r7]) : RelCT isa (Two Φ) (.block keep) fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem more_taint (h : Pins Φ [.r4, .r5, .r11, .r28]) : RelCT isa (Two Φ) more fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem full_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block [.sub .r12 .r28 .r5]) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem prep_taint (h : Pins Φ [.r30]) :
    RelCT isa (Two Φ) (.block (stackArgs ++ Impl.RsaPkcs1Enc.PPC64LE.Random.regArgs)) fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem accTail_taint (h : Pins Φ [.r28]) :
    RelCT isa (Two Φ) (.seq (.block status) (.seq fillLoop (.block [Impl.AesGcm.PPC64LE.mov .r3 .r5])))
      fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem reject_taint (h : Pins Φ [.r4, .r5, .r28, .r29, .r30, .r31]) :
    RelCT isa (Two Φ) reject fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
