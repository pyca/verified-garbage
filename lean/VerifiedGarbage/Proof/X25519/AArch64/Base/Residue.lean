module

public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
public meta import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.X25519.AArch64.Lit
meta import VerifiedGarbage.Proof.X25519.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and it imports the proof of the base-point multiplication, which the residue analysis would otherwise be built with

/-!
# X25519 on AArch64: the base-point multiplication returns without secret residue

`x25519BaseCleared` is `x25519Base`, then what it leaves secret cleared: the
registers that held the field elements and the comb's lookups, and the flags,
from `x1`. The residue analysis for two runs that leak the same
(`RTaintCT.noResidue_of_verified`) proves it leaves nothing secret, the
registers the calling convention preserves, which it restores, aside.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64

abbrev x25519BaseCleared : Prog isa :=
  Impl.Residue.AArch64.withClears
    [.x1, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17] [] (some .x1)
    Impl.X25519.AArch64.Base.x25519Base

theorem x25519BaseCleared_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target x25519BaseCleared
      (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)) :=
  Clears.Verified.withClears_of x25519Base_verified
    (fun {s u u'} h hm hx => by
      have hm' : (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts).mem u' =
          (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts).mem u := hm
      have hx' : (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts).ret u' =
          (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts).ret u := hx
      revert h
      simp only [Spec.X25519.x25519BaseContract, Sig.contract]
      split
      · exact id
      · rw [hm', hx']; exact id)
    (by decide)

theorem x25519BaseCleared_written [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State)
    (t : List Leak) (s' : State)
    (hs : (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)).pre s)
    (he : Exec isa x25519BaseCleared s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts) Spec.X25519.x25519BaseSig
      [("scratch", 1024)] s s' := by
  obtain ⟨_, _, he', hm⟩ := Clears.exec_withClears (by decide) he
  exact Clears.writtenWithin_congr (fun _ => rfl) hm (x25519Base_written s _ _ hs he')

theorem x25519BaseCleared_noResidue [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    NoResidue x25519BaseCleared
      (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)) 0 :=
  RTaintCT.noResidue_of_verified x25519BaseCleared_verified ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.X25519.AArch64.Base.x25519BaseCleared_scrubbed [Ed25519.AArch64.Divstep.Sound] :
    VerifiedScrubbed _root_.VG.AArch64.target Proof.X25519.AArch64.Base.x25519BaseCleared
      (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)) 0 :=
  ⟨Proof.X25519.AArch64.Base.x25519BaseCleared_verified,
    Proof.X25519.AArch64.Base.x25519BaseCleared_noResidue⟩

end VG.Proof.X25519.AArch64.Base
