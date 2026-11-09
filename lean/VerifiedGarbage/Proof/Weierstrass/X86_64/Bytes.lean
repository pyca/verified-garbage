module
public import VerifiedGarbage.Impl.Weierstrass.X86_64
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Spec.Ecdsa.Generic

import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Short Weierstrass curves on x86-64: numbers to and from big-endian bytes

What the loads and stores of big-endian numbers read and write, a word at
a time: the address `r + e` (`ea_disp`), and the words of a region, which
are accessible (`inRegions_words`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem ea_disp (s : State) (r : Reg) (e : Nat) :
    s.ea { base := r, disp := (e : Int) } = s.gpr r + BitVec.ofNat 64 e := by
  simp only [State.ea, BitVec.ofInt_natCast]

/-- The words of a region are accessible. -/
theorem inRegions_words {rs : List Region} {p : Addr} {len : Nat} (h : (⟨p, len⟩ : Region) ∈ rs)
    (hl : len ≤ 2 ^ 64) : ∀ d, d + 8 ≤ len → InRegions rs (p + BitVec.ofNat 64 d) 8 :=
  fun _ hd => ⟨_, h, Offset.contains_base p hd (by omega_using [hl, hd])⟩

end VG.Proof.Weierstrass.X86_64
