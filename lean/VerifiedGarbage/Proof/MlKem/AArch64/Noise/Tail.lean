module
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Insert noise nonces and SHAKE256 padding in an interleaved state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_movz wp_vop wp_strq)

def tailWords (n : Nat) : List Instr :=
 [.movz .x .x6 (BitVec.ofNat 16 (n+0x1f00)) 0,
  .movz .x .x7 (BitVec.ofNat 16 (n+1+0x1f00)) 0,
  .vop (.dup .d2 .v0 .x6), .vop (.ins .d2 .v0 1 .x7), .strq .v0 .x19 64]

theorem tailWords_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .x19 = p) (hw : InRegions s.wr (p+64) 16) :
    WP isa (.block (tailWords n)) s fun t => RegKeep [.x6,.x7] s t ∧
      t.mem = s.mem.write (p+64) 16 (ofVDwords
        ((BitVec.ofNat 16 (n+0x1f00)).setWidth 64)
        ((BitVec.ofNat 16 (n+1+0x1f00)).setWidth 64)) := by
  unfold tailWords
  refine wp_movz fun s1 h1 e1 => wp_movz fun s2 h2 e2 => ?_
  refine wp_vop (d := .v0) rfl fun s3 h3 => wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := p+64) (by decide)
    (by rw [h4.gpr,h3.gpr,h2.get .x19,h1.get .x19,hp]; rfl)
    (by rw [h4.wr,h3.wr,h2.wr,h1.wr]; exact hw) fun t h5 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.vupd h3)).trans
      (RegKeep.vupd h4)).trans (RegKeep.vmem h5) |>.mono (by simp)
  · rw [h5.mem,h4.v,h3.v,h3.gpr,e2,h2.get .x6,e1,
      h4.mem,h3.mem,h2.mem,h1.mem,setLane_pair_hi]

/-- Insert the final SHAKE padding bit in either rate's last lane. -/
theorem padWord_ok {s : State} {p : Addr} {j : Nat} (hj : j < 256)
    (hp : s.gpr .x19 = p) (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block ([.movz .x .x6 0x8000 3, .vop (.dup .d2 .v0 .x6),
      .strq .v0 .x19 (16*j)] : List Instr)) s fun t => RegKeep [.x6] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16
        (ofVDwords 0x8000000000000000 0x8000000000000000) := by
  refine VG.Proof.MlKem.AArch64.wp_x (d := .x6) (v := 0x8000000000000000) (by rfl)
    fun s1 h1 e1 => ?_
  refine wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p j) (by omega)
    (by rw [h2.gpr,h1.get .x19,hp]; rfl)
    (by rw [h2.wr,h1.wr]; exact hw) fun t h3 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((RegKeep.only h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3) |>.mono (by simp)
  · rw [h3.mem,h2.v,e1,h2.mem,h1.mem]

end VG.Proof.MlKem.AArch64.Noise
