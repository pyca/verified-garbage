module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
public import VerifiedGarbage.Proof.Dsa.X86.Pointer


/-! # Selecting supported public component widths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem deriveDispatch_ok (widths : List (Nat × Nat))
    {s : State} {base : Addr} {size pLen qLen : Nat} {Q : State → Prop}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (member : (pLen, qLen) ∈ widths)
    (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (hp : (pointerValue base s (.input .pLen)).toNat = pLen)
    (hq : (pointerValue base s (.input .qLen)).toNat = qLen)
    (body : ∀ t, Keeps [.eax] s t → t.mem = s.mem → WP isa (Generate.deriveSized pLen qLen) t Q) :
    WP isa (Generate.deriveDispatch widths) s Q :=
  generationDispatch_ok Generate.deriveSized widths hs hz member bound hp hq body

end VG.Proof.Dsa.X86
