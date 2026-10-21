module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.TCB.X86.Isa

/-! # Whole-word reversal imports the exact big-endian candidate or witness -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Mont

theorem bswap_byte (x : BitVec 32) {k : Nat} (index : k < 4) :
    (bswap x).extractLsb' (8 * k) 8 = x.extractLsb' (8 * (3 - k)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  change ((byteRev32 x).extractLsb' (8 * k) 8).getLsbD i = _
  simp only [BitVec.getLsbD_extractLsb', bound, decide_true, Bool.true_and]
  rw [byteRev32_getLsbD _ (by omega)]
  congr 1
  omega

theorem StateAt.bytes {g : Geometry} {s₀ s : State} (S : StateAt g s₀ g.count s)
    {j : Nat} (index : j < 4 * g.count) :
    s.mem (off (g.dst.setWidth 64) j) =
      s₀.mem (off (g.src.setWidth 64) (4 * g.count - 1 - j)) := by
  let word := g.count - 1 - j / 4
  have wi : word < g.count := by dsimp only [word]; omega
  have k : j % 4 < 4 := Nat.mod_lt _ (by decide)
  have outAddr : off (g.dst.setWidth 64) j = g.destAt word + BitVec.ofNat 64 (j % 4) := by
    unfold Geometry.destAt off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    dsimp only [word]
    omega
  have inAddr : off (g.src.setWidth 64) (4 * g.count - 1 - j) =
      g.sourceAt word + BitVec.ofNat 64 (3 - j % 4) := by
    unfold Geometry.sourceAt off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    dsimp only [word]
    omega
  rw [outAddr, inAddr, Mem.readW_byte s.mem (g.destAt word) k, S.copied word wi, bswap_byte _ k,
    ← Mem.readW_byte s₀.mem (g.sourceAt word) (by omega : 3 - j % 4 < 4)]

theorem StateAt.os2ip {g : Geometry} {s₀ s : State} (S : StateAt g s₀ g.count s) :
    (s.mem.read (g.dst.setWidth 64) (4 * g.count)).toNat =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (g.src.setWidth 64) (4 * g.count)) :=
  VG.Proof.Bignum.reversed_read _ _ _ _ _ (fun _ index => S.bytes index)

end VG.Proof.RsaKeyGen.X86.Import
