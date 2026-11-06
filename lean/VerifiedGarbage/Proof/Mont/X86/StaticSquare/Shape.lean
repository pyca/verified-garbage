module

import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! # Structural stack safety without expanding the fixed schedules -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86

 def noSp (i : Instr) : Bool := !VG.X86.Taint.clobbers i .esp

 theorem seq_noSp {a b : Prog isa} (ha : a.allInstrs noSp=true) (hb : b.allInstrs noSp=true) :
    (Code.seq a b).allInstrs noSp=true := by change a.allInstrs noSp && b.allInstrs noSp=true; rw [ha,hb]; rfl
 theorem ite_noSp {a b : Prog isa} (cond : Cond) (ha : a.allInstrs noSp=true) (hb : b.allInstrs noSp=true) :
    (Code.ite cond a b).allInstrs noSp=true := by change a.allInstrs noSp && b.allInstrs noSp=true; rw [ha,hb]; rfl

end VG.Proof.Mont.X86.StaticSquare
