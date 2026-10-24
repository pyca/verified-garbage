module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Main
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Untouched
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X25519 on PPC64LE: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519PPC64LE`, which it implies, and a state satisfying it.
The code writes no nonvolatile register and never writes the link register
or calls a function, so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE

theorem x25519_ok (s : State) (hs : x25519PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.X25519.PPC64LE.x25519 s t s' ∧ abiPreserved s s' ∧ x25519PPC64LE.post s s' := by
  obtain ⟨t, s', he, h⟩ := x25519_correct (XPre.of hs)
  have hd : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.X25519.PPC64LE.x25519, dstOf i ≠ some r :=
    nv_of_avoids (by decide +kernel)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (hd r hr) he (.inl (by decide +kernel)), Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩

theorem x25519_ct' : ConstantTime isa x25519PPC64LE.pre x25519PPC64LE.pub Impl.X25519.PPC64LE.x25519 :=
  x25519_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified PPC64LE.target Impl.X25519.PPC64LE.x25519 (Spec.X25519.x25519Contract PPC64LE.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    contract_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.PPC64LE.x25519PPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.X25519.PPC64LE.x25519Sat] using Proof.X25519.PPC64LE.x25519Sat)

end VG.Proof.X25519.PPC64LE
