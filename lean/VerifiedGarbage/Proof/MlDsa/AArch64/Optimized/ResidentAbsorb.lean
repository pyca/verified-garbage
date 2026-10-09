import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentPadMem

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (absorbBody)

theorem absorbBody_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : ∀ j < 8, InRegions (s.rd++s.wr) (seedAddr a j) 8)
    (hinb : ∀ j < 8, InRegions (s.rd++s.wr) (seedAddr b j) 8)
    (ha64 : InRegions (s.rd++s.wr) (a+64) 1) (ha65 : InRegions (s.rd++s.wr) (a+65) 1)
    (hb64 : InRegions (s.rd++s.wr) (b+64) 1) (hb65 : InRegions (s.rd++s.wr) (b+65) 1)
    (hw : ∀ j < 25, InRegions s.wr (wordAddr p j) 16)
    (hda : (seedR a).Disjoint (pairR p)) (hdb : (seedR b).Disjoint (pairR p))
    (hz : ∀ i < 25, s.mem.read (wordAddr p i) 16 = 0) :
    WP isa (.block absorbBody) s fun t => RegKeep [.x6,.x7,.x8,.x9] s t ∧
      Frame [pairR p] s.mem t.mem ∧ PairAt t.mem p (seedState s.mem a) (seedState s.mem b) := by
  unfold absorbBody
  rw [WP.block_append_iff]
  refine WP.mono (seedWords_ok hp ha hb hina hinb (fun j hj => hw j (by omega)) hda hdb hz)
    fun s1 ⟨h1,hf1,hpart⟩ => ?_
  refine WP.mono (seedTail_ok ((h1.gpr .x2 (by decide)).trans hp) ((h1.gpr .x3 (by decide)).trans ha)
    ((h1.gpr .x4 (by decide)).trans hb)
    (by rw [h1.rd,h1.wr]; exact ha64) (by rw [h1.rd,h1.wr]; exact ha65)
    (by rw [h1.rd,h1.wr]; exact hb64) (by rw [h1.rd,h1.wr]; exact hb65)
    (by rw [h1.wr]; exact hw 8 (by decide)) (by rw [h1.wr]; exact hw 16 (by decide)))
    fun t ⟨h2,hm,hf2⟩ => ?_
  refine ⟨(h1.trans h2).mono (by simp),hf1.trans hf2,?_⟩
  rw [hm,tailWord_frame hf1 hda,tailWord_frame hf1 hdb]
  exact part_pad hpart
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
