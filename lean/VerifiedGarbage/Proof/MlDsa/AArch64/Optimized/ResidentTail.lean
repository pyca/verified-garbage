import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentPadStore

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (seedTail tailPack)

theorem seedTail_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (ha64 : InRegions (s.rd++s.wr) (a+64) 1) (ha65 : InRegions (s.rd++s.wr) (a+65) 1)
    (hb64 : InRegions (s.rd++s.wr) (b+64) 1) (hb65 : InRegions (s.rd++s.wr) (b+65) 1)
    (hw8 : InRegions s.wr (wordAddr p 8) 16) (hw16 : InRegions s.wr (wordAddr p 16) 16) :
    WP isa (.block seedTail) s fun t => RegKeep [.x6,.x7,.x8,.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 8) 16 (ofVDwords (tailWord s.mem a) (tailWord s.mem b))).write
        (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) ∧
      Frame [pairR p] s.mem t.mem := by
  unfold seedTail
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (seedLast_ok (by decide) (by decide) ha ha64 ha65) fun s1 ⟨h1,e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedLast_ok (by decide) (by decide) ((h1.get .x4).trans hb)
    (by rw [h1.rd,h1.wr]; exact hb64) (by rw [h1.rd,h1.wr]; exact hb65)) fun s2 ⟨h2,e2⟩ => ?_
  unfold tailPack
  rw [WP.block_append_iff]
  refine WP.mono (tailAdd_ok s2) fun s3 ⟨h3,e3,e4⟩ => ?_
  refine WP.mono (tailStore_ok ((h3.get .x2).trans ((h2.get .x2).trans ((h1.get .x2).trans hp)))
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw8)
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw16)) fun t ⟨h4,hm⟩ => ?_
  have e6 : s3.gpr .x6 = tailWord s.mem a := by rw [e3,h2.get .x6,e1]; rfl
  have e7 : s3.gpr .x7 = tailWord s.mem b := by rw [e4,e2,h1.mem]; rfl
  rw [e6,e7,h3.mem,h2.mem,h1.mem] at hm
  refine ⟨(((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.only h3)).trans h4 |>.mono (by simp),hm,?_⟩
  rw [hm]
  exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (pair_contains p (by decide))).write
    (List.mem_singleton_self _) _ (pair_contains p (by decide))
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
