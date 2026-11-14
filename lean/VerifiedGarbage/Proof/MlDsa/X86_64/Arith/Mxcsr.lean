module

public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Impl.MlKem.X86_64.Vec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on x86-64: the arithmetic without MXCSR of its own

The arithmetic runs inside its caller's MXCSR region and sets no MXCSR of
its own (see `Impl/MlDsa/X86_64/Arith/Vec.lean`). `noMx_ok` and `noMxH_ok`
state that in the shape of ML-KEM's `withMxcsr_ok` (through `scratch + 768`,
`mxR`) and of a `withMxcsr` through the last 8 bytes `mxH` of a polynomial,
which the arithmetic once ran inside: its proofs are those of the code they
wrapped.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Proof.MlKem.X86_64 (Keep Keep.refl mxR)

/-- The last 8 bytes of the polynomial at `p`. -/
abbrev mxH (p : Addr) : Region := ⟨p + BitVec.ofNat 64 1016, 8⟩

theorem mxH_in {p : Addr} {rs : List Region} (hw : pR p ∈ rs) (d : Nat) (hd : 1016 ≤ d ∧ d ≤ 1020) :
    InRegions rs (p + BitVec.ofNat 64 d) 4 :=
  ⟨_, hw, Offset.contains_base p (by omega_using [hd]) (by omega_using [hd])⟩

theorem mxH_sub (p : Addr) : Region.Sub (mxH p) (pR p) := Offset.sub_base p (by decide)

/-- The arithmetic's code once ran inside ML-KEM's `withMxcsr`, through `mxR` of
`scratch`; now it runs inside its caller's MXCSR region
(`Impl.Mcdt.X86_64.mcdtCall`) and sets none of its own. Its proofs keep the
shape they had: `c` runs from `s` itself, which differs from `s` in no
register and no byte. -/
theorem noMx_ok {c : Prog isa} {sP : Addr} {s : State} {Q : State → Prop}
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR sP] s.mem s1.mem → WP isa c s1 Q) :
    WP isa c s fun s' => ∃ s2, Q s2 ∧ Frame [mxR sP] s2.mem s'.mem ∧ Keep [] s2 s' :=
  WP.mono (hc s (Keep.refl _ _) (Frame.refl _ _)) fun s' h => ⟨s', h, Frame.refl _ _, Keep.refl _ _⟩

/-- `noMx_ok` through `mxH`, as the products once ran inside `withMxcsr` through it. -/
theorem noMxH_ok {c : Prog isa} {p : Addr} {s : State} {Q : State → Prop}
    (hc : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxH p] s.mem s1.mem → s1.xmm = s.xmm → s1.ymmHi = s.ymmHi →
      WP isa c s1 Q) :
    WP isa c s fun s' =>
      ∃ s2, Q s2 ∧ Frame [mxH p] s2.mem s'.mem ∧ Keep [] s2 s' ∧ s'.xmm = s2.xmm ∧ s'.ymmHi = s2.ymmHi :=
  WP.mono (hc s (Keep.refl _ _) (Frame.refl _ _) rfl rfl) fun s' h =>
    ⟨s', h, Frame.refl _ _, Keep.refl _ _, rfl, rfl⟩

end VG.Proof.MlDsa.X86_64.Arith
