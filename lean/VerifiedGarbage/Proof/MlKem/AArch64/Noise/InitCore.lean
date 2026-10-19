module
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitMemory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact instruction proof of paired noise state initialization -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem imm64 {n : Nat} (hn : n < 65536) :
    (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem initCore_ok {s : State} {p a : Addr} {sb n : Nat}
    (hn : n+1 < 256) (hoff : sb+32 ≤ 32768) (halign : sb%8=0)
    (hp : s.gpr .x19=p) (ha : s.gpr .x28+BitVec.ofNat 64 sb=a)
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hw : ∀ j<25, InRegions s.wr (wordAddr p j) 16)
    (hsep : (Region.mk a 32).Disjoint (pairR p)) :
    WP isa (.block (Impl.MlKem.AArch64.Noise.initCore sb n)) s fun t =>
      RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧
      PairAt t.mem p (seedState s.mem a n) (seedState s.mem a (n+1)) := by
  change WP isa (.block (zeroStates ++
    (((List.range 4).flatMap fun j => [.ldr .x .x6 .x28 (sb+8*j),
      .vop (.dup .d2 .v0 .x6),.strq .v0 .x19 (16*j)]) ++
    (tailWords n ++ [.movz .x .x6 0x8000 3,.vop (.dup .d2 .v0 .x6),.strq .v0 .x19 256])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok hp hw) fun z ⟨hz,hfz,hzero⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedWords_ok hoff halign ((hz.gpr .x19 (by simp)).trans hp)
    (by rw [hz.gpr .x28 (by simp)]; exact ha)
    (fun j hj => by rw [hz.rd,hz.wr]; exact hin j hj)
    (fun j hj => by rw [hz.wr]; exact hw j (by omega))
    (hsep.sub_right (Region.sub_prefix (by decide : 64≤400)))) fun v ⟨hv,hfv,hvals⟩ => ?_
  have hseed : SeedWords v.mem s.mem p a := seedWords_of_zero hzero hfv (fun j hj => by
    rw [hvals j hj]
    have hr : z.mem.readW (a+BitVec.ofNat 64 (8*j)) 64 = s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64 :=
      hfz.read (Offset.contains_base a (d := 8*j) (n := 8) (k := 32) (by omega) (by omega))
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep) (by decide)
    rw [hr])
  rw [WP.block_append_iff]
  refine WP.mono (tailWords_ok (p := p) (by rw [hv.gpr .x19 (by simp),hz.gpr .x19 (by simp),hp])
    (by rw [hv.wr,hz.wr]; exact hw 4 (by decide))) fun w ⟨hwk,hmw⟩ => ?_
  refine WP.mono (padWord_ok (p := p) (j := 16) (by decide)
    (by rw [hwk.gpr .x19 (by simp),hv.gpr .x19 (by simp),hz.gpr .x19 (by simp),hp])
    (by rw [hwk.wr,hv.wr,hz.wr]; exact hw 16 (by decide))) fun t ⟨ht,hmt⟩ => ?_
  have he : t.mem = (v.mem.write (wordAddr p 4) 16
      (ofVDwords (BitVec.ofNat 64 (n+0x1f00)) (BitVec.ofNat 64 (n+1+0x1f00)))).write
      (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) := by
    rw [hmt,hmw,imm64 (by omega),imm64 (by omega)]; rfl
  refine ⟨(((hz.trans hv).trans hwk).trans ht).mono (by simp),?_,?_⟩
  · have hf : Frame [pairR p] s.mem v.mem := hfz.trans (hfv.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨pairR p,by exact List.mem_singleton_self _,Region.sub_prefix (by decide : 64≤400)⟩))
    rw [he]
    exact (hf.write (by simp) _ (pair_contains p (by decide : 4<25))).write
      (by simp) _ (pair_contains p (by decide : 16<25))
  · rw [he]; exact tail_pair hseed

end VG.Proof.MlKem.AArch64.Noise
