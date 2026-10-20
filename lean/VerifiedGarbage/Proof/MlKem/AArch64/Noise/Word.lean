module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)

/-- Duplicate one seed word into the two interleaved sponge states. -/
theorem seedWord_ok {s : State} {p a : Addr} {sb j : Nat} (hj : j < 4)
    (hoff : sb + 8*j < 32768) (halign : (sb + 8*j) % 8 = 0)
    (hp : s.gpr .x19 = p) (ha : s.gpr .x28 + BitVec.ofNat 64 (sb+8*j) = a)
    (hin : InRegions (s.rd++s.wr) a 8)
    (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block ([.ldr .x .x6 .x28 (sb+8*j), .vop (.dup .d2 .v0 .x6),
      .strq .v0 .x19 (16*j)] : List Instr)) s fun t => RegKeep [.x6] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16 (ofVDwords (s.mem.readW a 64) (s.mem.readW a 64)) := by
  refine wp_ldr ⟨halign,hoff⟩ ha hin fun s1 h1 => ?_
  refine wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p j) (by omega)
    (by rw [h2.gpr,h1.other .x19 (by decide),hp]; rfl)
    (by rw [h2.wr,h1.wr]; exact hw) fun t h3 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3) |>.mono (by simp)
  · rw [h3.mem,h2.v,h1.gpr,h2.mem,h1.mem]

end VG.Proof.MlKem.AArch64.Noise
