import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Short Weierstrass curves on x86 (32-bit): big-endian words

What the loads and stores of big-endian numbers (`BytesLen.lean`) share:
`bswap` is `byteRev32`, the address `[r + d]`, and the 32-bit words of a range
whose bytes are kept.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem bswap_eq (w : BitVec 32) : bswap w = byteRev32 w := rfl

/-- `[r + d]`, for `r` whose `k` bytes up do not wrap. -/
theorem ea_ptr (s : State) {r : Reg} {d : Nat} (h : (s.gpr r).toNat + d < 2 ^ 32) :
    s.ea (at_ r d) = (s.gpr r).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq h

/-- A 32-bit word of a range whose bytes are kept. -/
theorem readW32_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 4, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

end VG.Proof.Weierstrass.X86
