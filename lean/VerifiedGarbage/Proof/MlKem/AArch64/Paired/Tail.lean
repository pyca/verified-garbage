module
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Insert noise nonces and SHAKE256 padding in an interleaved state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_movz wp_vop wp_strq)

def suffix (v : BitVec 16) : BitVec 64 :=
 v.setWidth 64 &&& ~~~((0xFFFF : BitVec 64) <<< 16) ||| (31 : BitVec 64) <<< 16

def tailWords (a b k : Nat) : List Instr :=
 [.movz .x .x6 (BitVec.ofNat 16 (a%k+256*(a/k))) 0,.movk .x .x6 31 1,
  .movz .x .x7 (BitVec.ofNat 16 (b%k+256*(b/k))) 0,.movk .x .x7 31 1,
  .vop (.dup .d2 .v0 .x6), .vop (.ins .d2 .v0 1 .x7), .strq .v0 .x19 64]

theorem tailWords_ok {s : State} {p : Addr} {a b k : Nat}
    (hp : s.gpr .x19 = p) (hw : InRegions s.wr (p+64) 16) :
    WP isa (.block (tailWords a b k)) s fun t => RegKeep [.x6,.x7] s t ∧
      t.mem = s.mem.write (p+64) 16 (ofVDwords
        (suffix (BitVec.ofNat 16 (a%k+256*(a/k))))
        (suffix (BitVec.ofNat 16 (b%k+256*(b/k))))) := by
  unfold tailWords
  refine wp_movz fun s1 h1 e1 => wp_movk1 fun s2 h2 e2 =>
    wp_movz fun s3 h3 e3 => wp_movk1 fun s4 h4 e4 => ?_
  refine wp_vop (d := .v0) rfl fun s5 h5 => wp_vop (d := .v0) rfl fun s6 h6 => ?_
  refine wp_strq (a := p+64) (by decide)
    (by rw [h6.gpr,h5.gpr,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19,hp]; rfl)
    (by rw [h6.wr,h5.wr,h4.wr,h3.wr,h2.wr,h1.wr]; exact hw) fun t h7 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((((((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.only h3)).trans
      (RegKeep.only h4)).trans (RegKeep.vupd h5)).trans (RegKeep.vupd h6)).trans (RegKeep.vmem h7) |>.mono (by simp)
  · rw [h7.mem,h6.v,h5.v,h5.gpr,e4,e3,h4.get .x6,h3.get .x6,e2,e1,
      h6.mem,h5.mem,h4.mem,h3.mem,h2.mem,h1.mem,setLane_pair_hi]
    rfl

end VG.Proof.MlKem.AArch64.Paired
