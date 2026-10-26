module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! # Public loop bounds and addresses for DSA range checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem rangeHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
      .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)]) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rbx = off B (slot w aX) ∧
      u.gpr .r10 = off B (slot w aN) ∧ u.gpr .rbp = mask false ∧ u.mem = s.mem ∧
      Keep [.r12, .rbx, .r10, .rbp] s u := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun u =>
    u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rbx = off B (slot w aX) ∧
    u.gpr .r10 = off B (slot w aN) ∧ u.gpr .rbp = mask false ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨hw, hx, hn, hb, hm⟩, hk⟩ => ⟨hw, hx, hn, hb, hm, hk⟩
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide),
    hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aX (by decide), hg.hdr.harr aN (by decide)]

end VG.Proof.Dsa.X86_64
