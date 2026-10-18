module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorPower
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Framework.Omega

/-! # Generator construction uses the existing verified public exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64

theorem generatorPower_ok (M : Mont) {s : State} {B : Addr}
    {len modulus : Nat} {mi : BitVec 64} {hb eb : List Byte}
    (h : Good s B activeBytes outerWords 0)
    (child : ChildReady s.mem B pWorkspace (len / 8) modulus mi)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hm : 1 < modulus) (hodd : modulus % 2 = 1)
    (has : OperandBytes s B activeBytes ⟨.input .g, .pLen⟩ hb)
    (hes : OperandBytes s B activeBytes ⟨.input .x, .pLen⟩ eb)
    (hhl : hb.length = len) (hel : eb.length = len)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorPower M.mm) s fun t =>
      Good t B activeBytes outerWords 0 ∧ ChildReady t.mem B pWorkspace (len / 8) modulus mi ∧
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) modulus) ∧
      CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len s.mem t.mem ∧
      Keep coreRegs s t := by
  have hlen : 1 ≤ len ∧ len ≤ 1024 ∧ 2 ≤ len / 8 ∧ len / 8 ≤ 48 ∧
      len / 8 = (len + 7) / 8 ∧ pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  exact corePublicPow_ok M h child (by decide) (by decide) hlen.2.2.2.2.2 (by decide)
    hlen.2.2.1 hlen.2.2.2.1 hlen.2.2.2.1 (by decide) hm hodd
    ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩ ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩
    (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 16; decide)
    has hes (by omega) (by rw [hhl, ← hlen.2.2.2.2.1]) (by omega) (by omega)
    (by simpa only [hhl] using has.length) hlen.1 (by omega) hlen.2.2.2.2.1 hout houtside

end VG.Proof.Dsa.AArch64.Generation
