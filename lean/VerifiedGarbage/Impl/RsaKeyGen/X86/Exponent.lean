module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift

/-! # Complete fixed-pass exponent preparation, shared by all witnesses -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Impl.Mont.X86

def markerOffset : Nat := 136

def saveMarker : List Instr := [.store (sc markerOffset) .eax, .store (sc (markerOffset + 4)) .edx]

def clearTops (n src out : Nat) : List Instr :=
  [.mov .eax (.imm 0), .store (sc (src + 4 * n)) .eax, .store (sc (out + 4 * n)) .eax,
    .mov .ecx (.imm (BitVec.allOnes 32))]

def firstPass (n src out : Nat) : Prog isa :=
  .seq (.block (clearTops n src out)) (HalfPass.code n src out)

def finish (n out : Nat) : List Instr :=
  [.mov .eax (.mem (sc markerOffset)), .mov .edx (.mem (sc (markerOffset + 4))),
    .store (sc (out + 4 * n)) .eax, .store (sc (out + 4 * n + 4)) .edx]

/-- `minusOne` holds c-1; `src` holds c. The exponent occupies out's first
2w native words and its 64-bit marker follows those words. -/
def code (w minusOne src out : Nat) : Prog isa :=
  .seq (ExponentMarker.code minusOne w)
    (.seq (.block saveMarker) (.seq (firstPass (2 * w) src out)
      (.seq (ExponentShift.passes (2 * w) markerOffset out) (.block (finish (2 * w) out)))))

end VG.Impl.RsaKeyGen.X86.Exponent
