module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
public import VerifiedGarbage.Proof.Framework.Arm.Call

/-! The candidate receives only its output, private consumption word, scratch and entropy suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

def callRd (p : SearchParams) (used : Nat) (sp : BitVec 32) : List Region :=
  [⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩, ⟨State.addr sp, 20⟩]

def callWr (p : SearchParams) : List Region :=
  [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr (p.control + 112#32), 8⟩,
    ⟨State.addr p.c.base, 8 * p.c.capacity⟩]

abbrev callState (p : SearchParams) (used : Nat) (s : State) : State :=
  s.callEntry.withRegions (callRd p used s.sp) (callWr p)

end VG.Proof.Ffdh.Arm.ParameterSearch
