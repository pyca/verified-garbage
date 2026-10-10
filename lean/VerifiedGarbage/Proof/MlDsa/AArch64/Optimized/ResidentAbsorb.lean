import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord

/-! ## From `ResidentPad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only only_write wp_add)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (tailAdd)

theorem tailAdd_ok (s : State) :
    WP isa (.block tailAdd) s fun t => Only [.x6,.x7,.x9] s t ∧
      t.gpr .x6 = s.gpr .x6 + 0x1f0000 ∧ t.gpr .x7 = s.gpr .x7 + 0x1f0000 := by
  unfold tailAdd
  refine VG.Proof.Sha3.AArch64.WP.cons (s' := s.write .x .x9 0x1f0000) rfl ?_
  have h1 := only_write s .x .x9 0x1f0000
  refine wp_add fun s2 h2 e2 => wp_add fun s3 h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x6,e2,h1.get .x6,VG.AArch64.RegUpd.gpr_write_self]
    rfl
  · rw [e3,h2.get .x7,h1.get .x7,h2.get .x9,VG.AArch64.RegUpd.gpr_write_self]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentWords.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (seedWord)

def seedR (p : Addr) : Region := ⟨p,66⟩
def seedAddr (p : Addr) (j : Nat) : Addr := p+BitVec.ofNat 64 (8*j)

def PartAt (m : Mem) (p : Addr) (src : Mem) (a b : Addr) (n : Nat) : Prop :=
  ∀ i < 25, m.read (wordAddr p i) 16 =
    if i < n then ofVDwords (src.readW (seedAddr a i) 64) (src.readW (seedAddr b i) 64) else 0

theorem seed_contains (p : Addr) {j : Nat} (hj : j < 8) :
    (seedR p).Contains (seedAddr p j) 8 := Offset.contains_base p (by omega) (by omega)

/-- Absorb the first 64 bytes of both seeds into corresponding packed lanes. -/
theorem seedWords_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : ∀ j < 8, InRegions (s.rd++s.wr) (seedAddr a j) 8)
    (hinb : ∀ j < 8, InRegions (s.rd++s.wr) (seedAddr b j) 8)
    (hw : ∀ j < 8, InRegions s.wr (wordAddr p j) 16)
    (hda : (seedR a).Disjoint (pairR p)) (hdb : (seedR b).Disjoint (pairR p))
    (hz : ∀ i < 25, s.mem.read (wordAddr p i) 16 = 0) :
    WP isa (.block ((List.range 8).flatMap seedWord)) s fun t =>
      RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧ PartAt t.mem p s.mem a b 8 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧ PartAt t.mem p s.mem a b k)
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,Frame.refl _ _,fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hz i hi⟩
  refine WP.mono (seedWord_ok hk
    ((ht.gpr .x2 (by decide)).trans hp) ((ht.gpr .x3 (by decide)).trans ha)
    ((ht.gpr .x4 (by decide)).trans hb)
    (by rw [ht.rd,ht.wr]; exact hina k hk) (by rw [ht.rd,ht.wr]; exact hinb k hk)
    (by rw [ht.wr]; exact hw k hk)) fun u ⟨hu,hm⟩ => ?_
  have hra : t.mem.readW (seedAddr a k) 64 = s.mem.readW (seedAddr a k) 64 :=
    hf.readW (seed_contains a hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hda) (by decide)
  have hrb : t.mem.readW (seedAddr b k) 64 = s.mem.readW (seedAddr b k) 64 :=
    hf.readW (seed_contains b hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdb) (by decide)
  change u.mem = t.mem.write (wordAddr p k) 16 (ofVDwords
    (t.mem.readW (seedAddr a k) 64) (t.mem.readW (seedAddr b k) 64)) at hm
  rw [hra,hrb] at hm
  refine ⟨(ht.trans hu).mono (by simp),?_,?_⟩
  · rw [hm]; exact hf.write (List.mem_singleton_self _) _ (pair_contains p (by omega))
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [read_write16,ite_eq_left (by omega)]
    · have hs : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs (by decide),hvals i hi]
      by_cases hl : i < k
      · rw [ite_eq_left hl,ite_eq_left (by omega)]
      · rw [ite_eq_right hl,ite_eq_right (by omega)]
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentPadStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq only_write)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (tailStore)

theorem tailStore_ok {s : State} {p : Addr} (hp : s.gpr .x2 = p)
    (hw8 : InRegions s.wr (wordAddr p 8) 16) (hw16 : InRegions s.wr (wordAddr p 16) 16) :
    WP isa (.block tailStore) s fun t => RegKeep [.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 8) 16 (ofVDwords (s.gpr .x6) (s.gpr .x7))).write
        (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) := by
  unfold tailStore
  refine wp_vop (d := .v0) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p 8) (by decide)
    (by rw [h2.gpr,h1.gpr,hp]; rfl) (by rw [h2.wr,h1.wr]; exact hw8) fun s3 h3 => ?_
  let s4 := s3.write .x .x9 (0x8000000000000000 : BitVec 64)
  refine VG.Proof.Sha3.AArch64.WP.cons (s' := s4) rfl ?_
  have h4 := only_write s3 .x .x9 (0x8000000000000000 : BitVec 64)
  refine wp_vop (d := .v0) rfl fun s5 h5 => ?_
  refine wp_strq (a := wordAddr p 16) (by decide)
    (by rw [h5.gpr,h4.get .x2,h3.gpr,h2.gpr,h1.gpr,hp]; rfl)
    (by rw [h5.wr,h4.wr,h3.wr,h2.wr,h1.wr]; exact hw16) fun t h6 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((((RegKeep.vupd h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3)).trans
      (RegKeep.only h4)).trans (RegKeep.vupd h5)).trans (RegKeep.vmem h6) |>.mono (by simp)
  · rw [h6.mem,h5.v,VG.AArch64.RegUpd.gpr_write_self,h5.mem,h4.mem,h3.mem,h2.v,h1.v,
      h1.gpr,h2.mem,h1.mem,setLane_pair_hi]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentTail.lean` -/

section

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

end

/-! ## From `ResidentPadMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Padding changes only the two padding words of each packed state. -/
theorem part_pad {m src : Mem} {p a b : Addr} (h : PartAt m p src a b 8) :
    PairAt ((m.write (wordAddr p 8) 16 (ofVDwords (tailWord src a) (tailWord src b))).write
      (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (seedState src a) (seedState src b) := by
  intro i hi
  rw [seedState_get src a hi,seedState_get src b hi]
  by_cases h16 : i = 16
  · subst i
    rw [read_write16]
    simp (disch := omega) only [ite_true,ite_eq_right]
  · have hs16 : Mem.Sep (wordAddr p i) 16 (wordAddr p 16) 16 :=
      Offset.sep p (d := 16*i) (e := 16*16) (n := 16) (k := 16) (by omega) (by omega) (by omega)
    rw [Mem.read_write_sep hs16 (by decide)]
    by_cases h8 : i = 8
    · subst i
      rw [read_write16]
      simp (disch := omega) only [ite_true,ite_eq_right]
    · have hs4 : Mem.Sep (wordAddr p i) 16 (wordAddr p 8) 16 :=
        Offset.sep p (d := 16*i) (e := 16*8) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs4 (by decide),h i hi]
      by_cases hl : i < 8
      · simp only [ite_eq_left hl]
        rfl
      · simp only [ite_eq_right hl,ite_eq_right h8,ite_eq_right h16]
        rfl

theorem seed_byte_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) {j : Nat} (hj : j < 66) :
    m' (a+BitVec.ofNat 64 j) = m (a+BitVec.ofNat 64 j) :=
  hf _ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ (Offset.contains_base a (by omega) (by omega)))

theorem tailWord_frame {m m' : Mem} {p a : Addr} (hf : Frame [pairR p] m m')
    (hd : (seedR a).Disjoint (pairR p)) : tailWord m' a = tailWord m a := by
  unfold tailWord lastWord
  rw [show a+64 = a+BitVec.ofNat 64 64 from rfl,show a+65 = a+BitVec.ofNat 64 65 from rfl,
    seed_byte_frame hf hd (by decide : 64 < 66),seed_byte_frame hf hd (by decide : 65 < 66)]
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentAbsorb.lean` -/

section

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

end
