module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitMemory
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep

import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
/-! # Exact padded matrix-seed state -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/Tail.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def seedState (m : Mem) (seed : Addr) (a k : Nat) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
 if i.val<4 then m.readW (seed+BitVec.ofNat 64 (8*i.val)) 64
 else if i.val=4 then suffix (BitVec.ofNat 16 (a%k+256*(a/k)))
 else if i.val=20 then 0x8000000000000000 else 0

theorem seedState_get (m : Mem) (p : Addr) (a k : Nat) {i : Nat} (hi : i<25) :
 (seedState m p a k)[i]! = if i<4 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
 else if i=4 then suffix (BitVec.ofNat 16 (a%k+256*(a/k)))
 else if i=20 then 0x8000000000000000 else 0 := by
 rw [getElem!_pos _ i hi]
 unfold seedState
 rw [Vector.getElem_ofFn]

theorem tail_pair {m input : Mem} {p seed : Addr} {a b k : Nat}
    (h : Noise.SeedWords m input p seed) :
    PairAt ((m.write (wordAddr p 4) 16
      (ofVDwords (suffix (BitVec.ofNat 16 (a%k+256*(a/k))))
        (suffix (BitVec.ofNat 16 (b%k+256*(b/k)))))).write
      (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState input seed a k) (seedState input seed b k) := by
  intro i hi
  rw [Noise.read_write_word _ _ _ hi (by decide),Noise.read_write_word _ _ _ hi (by decide),h i hi,
    seedState_get input seed a k hi,seedState_get input seed b k hi]
  by_cases h4 : i<4
  · simp only [ite_eq_left h4,ite_eq_right (by omega : ¬i=20),ite_eq_right (by omega : ¬i=4)]
  · by_cases he4 : i=4
    · subst i; simp
    · by_cases he20 : i=20
      · subst i; simp
      · simp only [ite_eq_right h4,ite_eq_right he4,ite_eq_right he20]; rfl

end VG.Proof.MlKem.AArch64.Paired
