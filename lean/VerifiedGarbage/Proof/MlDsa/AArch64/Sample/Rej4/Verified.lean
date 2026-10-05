import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.Sha3.Seed34
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedWord)

/-- Load one complete word from each seed and pack the independent streams. -/
theorem seedWord_ok {s : State} {p a b : Addr} {j : Nat} (hj : j < 4)
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hinb : InRegions (s.rd++s.wr) (b+BitVec.ofNat 64 (8*j)) 8)
    (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block (seedWord j)) s fun t => RegKeep [.x6,.x7] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16 (ofVDwords
        (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64) (s.mem.readW (b+BitVec.ofNat 64 (8*j)) 64)) := by
  unfold seedWord
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [ha]) hina fun s1 h1 => ?_
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [h1.other .x4 (by decide),hb])
    (by rw [h1.rd,h1.wr]; exact hinb) fun s2 h2 => ?_
  refine wp_vop (d := .v0) rfl fun s3 h3 => wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := wordAddr p j) (by omega)
    (by rw [h4.gpr,h3.gpr,h2.other .x2 (by decide),h1.other .x2 (by decide),hp]; rfl)
    (by rw [h4.wr,h3.wr,h2.wr,h1.wr]; exact hw) fun t h5 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((((RegKeep.upd h1).trans (RegKeep.upd h2)).trans (RegKeep.vupd h3)).trans
      (RegKeep.vupd h4)).trans (RegKeep.vmem h5) |>.mono (by simp)
  · rw [h5.mem,h4.v,h3.v,h3.gpr,h2.gpr,h2.other .x6 (by decide),h1.gpr,
      h4.mem,h3.mem,h2.mem,h1.mem,setLane_pair_hi]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Last`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrb wp_lsl wp_add)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedLast)

def lastWord (m : Mem) (p : Addr) : BitVec 64 :=
  (m (p+32)).setWidth 64 + ((m (p+33)).setWidth 64 <<< 8)

/-- Read exactly the final two seed bytes into the low 16 bits of a scalar word. -/
theorem seedLast_ok {s : State} {r n : Reg} {a : Addr} (hr8 : r ≠ .x8)
    (hnr : n ≠ r) (ha : s.gpr n = a)
    (hin32 : InRegions (s.rd++s.wr) (a+32) 1)
    (hin33 : InRegions (s.rd++s.wr) (a+33) 1) :
    WP isa (.block (seedLast r n)) s fun t => Only [r,.x8] s t ∧ t.gpr r = VG.Proof.MlDsa.AArch64.Sample.Rej4.lastWord s.mem a := by
  unfold seedLast
  refine wp_ldrb (a := a+32) (by decide) (by rw [ha]; rfl) hin32 fun s1 h1 e1 => ?_
  refine wp_ldrb (a := a+33) (by decide) (by rw [h1.get n (by simpa using hnr),ha]; rfl)
    (by rw [h1.rd,h1.wr]; exact hin33) fun s2 h2 e2 => ?_
  refine wp_lsl (by decide) fun s3 h3 e3 => wp_add fun t h4 e4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((h1.trans h2).trans h3).trans h4).mono (by simp)
  · rw [e4,e3,h3.get r (by simpa using hr8),h2.get r (by simpa using hr8),e1,e2,h1.mem]
    rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Seed`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (toNat_lsl_n toNat_add_n)

def tailWord (m : Mem) (p : Addr) : BitVec 64 := VG.Proof.MlDsa.AArch64.Sample.Rej4.lastWord m p + 0x1f0000

theorem toNat_append_add {n k : Nat} (a : BitVec n) (b : BitVec k) :
    (a++b).toNat = a.toNat * 2^k + b.toNat := by
  rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq]

theorem tailWord_eq (m : Mem) (p : Addr) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m p = (((0#40 ++ 0x1f#8) ++ m (p+33)) ++ m (p+32)) := by
  have h0 := (m (p+32)).isLt
  have h1 := (m (p+33)).isLt
  have hs : (((m (p+33)).setWidth 64) <<< 8).toNat = (m (p+33)).toNat * 256 := by
    rw [toNat_lsl_n (by rw [BitVec.toNat_setWidth]; omega),BitVec.toNat_setWidth]
    omega
  apply BitVec.eq_of_toNat_eq
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord VG.Proof.MlDsa.AArch64.Sample.Rej4.lastWord
  rw [toNat_add_n (by rw [BitVec.toNat_add,BitVec.toNat_setWidth,hs]; change (_ % _ + 2031616 < _); omega),
    toNat_add_n (by rw [BitVec.toNat_setWidth,hs]; omega),BitVec.toNat_setWidth,hs]
  simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.toNat_append_add,BitVec.toNat_ofNat]
  rw [show (0x1f0000 : BitVec 64).toNat = 2031616 from rfl]
  simp only [Nat.reducePow,Nat.zero_mod,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd]
  omega

theorem tailWord_byte (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m p).extractLsb' (8*k) 8 =
      if k = 0 then m (p+32) else if k = 1 then m (p+33) else if k = 2 then 0x1f else 0 := by
  rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord_eq]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h | h
  · subst k
    simp only [Nat.mul_zero,BitVec.extractLsb'_append_eq_right,ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (2:Nat) = 0),ite_eq_right (by decide : ¬ (2:Nat) = 1),ite_true]
    rfl
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega)]
    simp only [ite_eq_right (by omega : ¬ k = 0),ite_eq_right (by omega : ¬ k = 1),
      ite_eq_right (by omega : ¬ k = 2)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp

/-- The initial state obtained by absorbing a 34-byte seed and SHAKE padding. -/
def seedState (m : Mem) (p : Addr) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
  if i.val < 4 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
  else if i.val = 4 then VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m p
  else if i.val = 20 then 0x8000000000000000 else 0

theorem pad_byte : ∀ k < 8, (0x8000000000000000 : BitVec 64).extractLsb' (8*k) 8 =
    if k = 7 then 0x80 else 0 := by decide

theorem seedState_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState m p)[i]! = if i < 4 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i = 4 then VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m p else if i = 20 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState
  rw [Vector.getElem_ofFn]

theorem seedState_eq (m : Mem) (p : Addr) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState m p = Proof.Sha3.Seed34.A0 (Spec.Sha3.bytesAt m p 34) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Proof.Sha3.Seed34.byteOf_A0 (Proof.Sha3.bytesAt_length _ _ _) hj]
  unfold Proof.Sha3.byteOf
  rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState_get m p (by omega)]
  by_cases h32 : j < 32
  · rw [ite_eq_left (by omega : j/8 < 4),ite_eq_left (by omega : j < 34),
      Proof.MlKem.bytesAt_getD m p (by omega)]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8 = j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8 < 4)]
    by_cases h40 : j < 40
    · rw [ite_eq_left (by omega : j/8 = 4),VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord_byte m p (by omega)]
      rcases (show j = 32 ∨ j = 33 ∨ j = 34 ∨ 35 ≤ j by omega) with h | h | h | h
      · subst j
        simp only [Nat.reduceMod,ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp only [Nat.reduceMod,ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8 = 4)]
      by_cases h20 : j/8 = 20
      · rw [ite_eq_left h20,VG.Proof.MlDsa.AArch64.Sample.Rej4.pad_byte (j%8) (by omega)]
        by_cases he : j = 167 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only only_write wp_add)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (tailAdd)

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
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq only_write)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (tailStore)

theorem tailStore_ok {s : State} {p : Addr} (hp : s.gpr .x2 = p)
    (hw4 : InRegions s.wr (wordAddr p 4) 16) (hw20 : InRegions s.wr (wordAddr p 20) 16) :
    WP isa (.block tailStore) s fun t => RegKeep [.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 4) 16 (ofVDwords (s.gpr .x6) (s.gpr .x7))).write
        (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) := by
  unfold tailStore
  refine wp_vop (d := .v0) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p 4) (by decide)
    (by rw [h2.gpr,h1.gpr,hp]; rfl) (by rw [h2.wr,h1.wr]; exact hw4) fun s3 h3 => ?_
  let s4 := s3.write .x .x9 (0x8000000000000000 : BitVec 64)
  refine VG.Proof.Sha3.AArch64.WP.cons (s' := s4) rfl ?_
  have h4 := only_write s3 .x .x9 (0x8000000000000000 : BitVec 64)
  refine wp_vop (d := .v0) rfl fun s5 h5 => ?_
  refine wp_strq (a := wordAddr p 20) (by decide)
    (by rw [h5.gpr,h4.get .x2,h3.gpr,h2.gpr,h1.gpr,hp]; rfl)
    (by rw [h5.wr,h4.wr,h3.wr,h2.wr,h1.wr]; exact hw20) fun t h6 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((((RegKeep.vupd h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3)).trans
      (RegKeep.only h4)).trans (RegKeep.vupd h5)).trans (RegKeep.vmem h6) |>.mono (by simp)
  · rw [h6.mem,h5.v,VG.AArch64.RegUpd.gpr_write_self,h5.mem,h4.mem,h3.mem,h2.v,h1.v,
      h1.gpr,h2.mem,h1.mem,setLane_pair_hi]
    rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedTail tailPack)

theorem seedTail_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (ha32 : InRegions (s.rd++s.wr) (a+32) 1) (ha33 : InRegions (s.rd++s.wr) (a+33) 1)
    (hb32 : InRegions (s.rd++s.wr) (b+32) 1) (hb33 : InRegions (s.rd++s.wr) (b+33) 1)
    (hw4 : InRegions s.wr (wordAddr p 4) 16) (hw20 : InRegions s.wr (wordAddr p 20) 16) :
    WP isa (.block seedTail) s fun t => RegKeep [.x6,.x7,.x8,.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 4) 16 (ofVDwords (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord s.mem a) (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord s.mem b))).write
        (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) ∧
      VG.Frame [pairR p] s.mem t.mem := by
  unfold seedTail
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedLast_ok (by decide) (by decide) ha ha32 ha33) fun s1 ⟨h1,e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedLast_ok (by decide) (by decide) ((h1.get .x4).trans hb)
    (by rw [h1.rd,h1.wr]; exact hb32) (by rw [h1.rd,h1.wr]; exact hb33)) fun s2 ⟨h2,e2⟩ => ?_
  unfold tailPack
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailAdd_ok s2) fun s3 ⟨h3,e3,e4⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailStore_ok ((h3.get .x2).trans ((h2.get .x2).trans ((h1.get .x2).trans hp)))
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw4)
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw20)) fun t ⟨h4,hm⟩ => ?_
  have e6 : s3.gpr .x6 = VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord s.mem a := by rw [e3,h2.get .x6,e1]; rfl
  have e7 : s3.gpr .x7 = VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord s.mem b := by rw [e4,e2,h1.mem]; rfl
  rw [e6,e7,h3.mem,h2.mem,h1.mem] at hm
  refine ⟨(((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.only h3)).trans h4 |>.mono (by simp),hm,?_⟩
  rw [hm]
  exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (pair_contains p (by decide))).write
    (List.mem_singleton_self _) _ (pair_contains p (by decide))
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Words`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedWord)

def seedR (p : Addr) : Region := ⟨p,34⟩
def seedAddr (p : Addr) (j : Nat) : Addr := p+BitVec.ofNat 64 (8*j)

def PartAt (m : Mem) (p : Addr) (src : Mem) (a b : Addr) (n : Nat) : Prop :=
  ∀ i < 25, m.read (wordAddr p i) 16 =
    if i < n then ofVDwords (src.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a i) 64) (src.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b i) 64) else 0

theorem seed_contains (p : Addr) {j : Nat} (hj : j < 4) :
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR p).Contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr p j) 8 := Offset.contains_base p (by omega) (by omega)

/-- Absorb the first 32 bytes of both seeds into corresponding packed lanes. -/
theorem seedWords_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : ∀ j < 4, InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a j) 8)
    (hinb : ∀ j < 4, InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b j) 8)
    (hw : ∀ j < 4, InRegions s.wr (wordAddr p j) 16)
    (hda : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR a).Disjoint (pairR p)) (hdb : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR b).Disjoint (pairR p))
    (hz : ∀ i < 25, s.mem.read (wordAddr p i) 16 = 0) :
    WP isa (.block ((List.range 4).flatMap seedWord)) s fun t =>
      RegKeep [.x6,.x7] s t ∧ VG.Frame [pairR p] s.mem t.mem ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.PartAt t.mem p s.mem a b 4 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x6,.x7] s t ∧ VG.Frame [pairR p] s.mem t.mem ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.PartAt t.mem p s.mem a b k)
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,Frame.refl _ _,fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hz i hi⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedWord_ok hk
    ((ht.gpr .x2 (by decide)).trans hp) ((ht.gpr .x3 (by decide)).trans ha)
    ((ht.gpr .x4 (by decide)).trans hb)
    (by rw [ht.rd,ht.wr]; exact hina k hk) (by rw [ht.rd,ht.wr]; exact hinb k hk)
    (by rw [ht.wr]; exact hw k hk)) fun u ⟨hu,hm⟩ => ?_
  have hra : t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a k) 64 = s.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a k) 64 :=
    hf.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_contains a hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hda) (by decide)
  have hrb : t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b k) 64 = s.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b k) 64 :=
    hf.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_contains b hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdb) (by decide)
  change u.mem = t.mem.write (wordAddr p k) 16 (ofVDwords
    (t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a k) 64) (t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b k) 64)) at hm
  rw [hra,hrb] at hm
  refine ⟨(ht.trans hu).mono (by simp),?_,?_⟩
  · rw [hm]; exact hf.write (List.mem_singleton_self _) _ (pair_contains p (by omega))
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [VG.Proof.Sha3.AArch64.Neon.read_write16,ite_eq_left (by omega)]
    · have hs : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs (by decide),hvals i hi]
      by_cases hl : i < k
      · rw [ite_eq_left hl,ite_eq_left (by omega)]
      · rw [ite_eq_right hl,ite_eq_right (by omega)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Padding changes only the two padding words of each packed state. -/
theorem part_pad {m src : Mem} {p a b : Addr} (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.PartAt m p src a b 4) :
    PairAt ((m.write (wordAddr p 4) 16 (ofVDwords (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord src a) (VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord src b))).write
      (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000)) p
      (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState src a) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState src b) := by
  intro i hi
  rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState_get src a hi,VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState_get src b hi]
  by_cases h20 : i = 20
  · subst i
    rw [VG.Proof.Sha3.AArch64.Neon.read_write16]
    simp (disch := omega) only [ite_true,ite_eq_right]
  · have hs20 : Mem.Sep (wordAddr p i) 16 (wordAddr p 20) 16 :=
      Offset.sep p (d := 16*i) (e := 16*20) (n := 16) (k := 16) (by omega) (by omega) (by omega)
    rw [Mem.read_write_sep hs20 (by decide)]
    by_cases h4 : i = 4
    · subst i
      rw [VG.Proof.Sha3.AArch64.Neon.read_write16]
      simp (disch := omega) only [ite_true,ite_eq_right]
    · have hs4 : Mem.Sep (wordAddr p i) 16 (wordAddr p 4) 16 :=
        Offset.sep p (d := 16*i) (e := 16*4) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hs4 (by decide),h i hi]
      by_cases hl : i < 4
      · simp only [ite_eq_left hl]
        rfl
      · simp only [ite_eq_right hl,ite_eq_right h4,ite_eq_right h20]
        rfl

theorem seed_byte_frame {m m' : Mem} {p a : Addr} (hf : VG.Frame [pairR p] m m')
    (hd : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR a).Disjoint (pairR p)) {j : Nat} (hj : j < 34) :
    m' (a+BitVec.ofNat 64 j) = m (a+BitVec.ofNat 64 j) :=
  hf _ (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd _ (Offset.contains_base a (by omega) (by omega)))

theorem tailWord_frame {m m' : Mem} {p a : Addr} (hf : VG.Frame [pairR p] m m')
    (hd : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR a).Disjoint (pairR p)) : VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m' a = VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord m a := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord VG.Proof.MlDsa.AArch64.Sample.Rej4.lastWord
  rw [show a+32 = a+BitVec.ofNat 64 32 from rfl,show a+33 = a+BitVec.ofNat 64 33 from rfl,
    VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_byte_frame hf hd (by decide : 32 < 34),VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_byte_frame hf hd (by decide : 33 < 34)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbBody)

theorem absorbBody_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : ∀ j < 4, InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr a j) 8)
    (hinb : ∀ j < 4, InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedAddr b j) 8)
    (ha32 : InRegions (s.rd++s.wr) (a+32) 1) (ha33 : InRegions (s.rd++s.wr) (a+33) 1)
    (hb32 : InRegions (s.rd++s.wr) (b+32) 1) (hb33 : InRegions (s.rd++s.wr) (b+33) 1)
    (hw : ∀ j < 25, InRegions s.wr (wordAddr p j) 16)
    (hda : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR a).Disjoint (pairR p)) (hdb : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR b).Disjoint (pairR p))
    (hz : ∀ i < 25, s.mem.read (wordAddr p i) 16 = 0) :
    WP isa (.block absorbBody) s fun t => RegKeep [.x6,.x7,.x8,.x9] s t ∧
      VG.Frame [pairR p] s.mem t.mem ∧ PairAt t.mem p (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState s.mem a) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState s.mem b) := by
  unfold absorbBody
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedWords_ok hp ha hb hina hinb (fun j hj => hw j (by omega)) hda hdb hz)
    fun s1 ⟨h1,hf1,hpart⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedTail_ok ((h1.gpr .x2 (by decide)).trans hp) ((h1.gpr .x3 (by decide)).trans ha)
    ((h1.gpr .x4 (by decide)).trans hb)
    (by rw [h1.rd,h1.wr]; exact ha32) (by rw [h1.rd,h1.wr]; exact ha33)
    (by rw [h1.rd,h1.wr]; exact hb32) (by rw [h1.rd,h1.wr]; exact hb33)
    (by rw [h1.wr]; exact hw 4 (by decide)) (by rw [h1.wr]; exact hw 20 (by decide)))
    fun t ⟨h2,hm,hf2⟩ => ?_
  refine ⟨(h1.trans h2).mono (by simp),hf1.trans hf2,?_⟩
  rw [hm,VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord_frame hf1 hda,VG.Proof.MlDsa.AArch64.Sample.Rej4.tailWord_frame hf1 hdb]
  exact VG.Proof.MlDsa.AArch64.Sample.Rej4.part_pad hpart
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (zeroStates)

def statesR (p : Addr) : Region := ⟨p,800⟩

theorem zeros_ok {s : State} {p : Addr} (hp : s.gpr .x19 = p)
    (hw : ∀ i < 50, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block zeroStates) s fun t => RegKeep [] s t ∧
      VG.Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.statesR p] s.mem t.mem ∧ ∀ i < 50, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zeroStates
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ VG.Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.statesR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 50 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega)
    (by rw [ht.gpr .x19 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [VG.Proof.Sha3.AArch64.Neon.read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Base`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oSave saved)
open VG.Proof.Sha3 (iterF)

def seedP (s : State) : Addr := s.gpr .x0
def aP (s : State) : Addr := s.gpr .x1
def scr (s : State) : Addr := s.gpr .x2
def at' (s : State) (o : Nat) : Addr := VG.Proof.MlDsa.AArch64.Sample.Rej4.scr s + BitVec.ofNat 64 o

def seedsR (s : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s,136⟩
def aR (s : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.aP s,4096⟩
def scrR (s : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scr s,8192⟩
def lowR (s : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scr s,oSave⟩
def saveR (s : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.at' s oSave,144⟩

structure Pre (s : State) : Prop where
  rd : s.rd = [VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s]
  wr : s.wr = [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s]
  seed_a : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s)
  seed_scr : (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s)
  a_scr : (VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s)

abbrev B (s : State) (k : Nat) : List Byte := Spec.MlDsa.seed4 s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) k
abbrev A0 (s : State) (k : Nat) : Spec.Sha3.State := Proof.Sha3.Seed34.A0 (VG.Proof.MlDsa.AArch64.Sample.Rej4.B s k)
def stateP (s : State) (pair : Nat) : Addr := VG.Proof.MlDsa.AArch64.Sample.Rej4.at' s (400*pair)
def bufP (s : State) (k : Nat) : Addr := VG.Proof.MlDsa.AArch64.Sample.Rej4.at' s (oBuf+1008*k)
def bufAt (s : State) (k n : Nat) : Addr := VG.Proof.MlDsa.AArch64.Sample.Rej4.at' s (oBuf+1008*k+168*n)

structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x19 : s.gpr .x19 = VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ
  x20 : s.gpr .x20 = VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ
  x21 : s.gpr .x21 = VG.Proof.MlDsa.AArch64.Sample.Rej4.aP σ
  x30 : s.gpr .x30 = σ.gpr .x30
  savedG : ∀ i < 10, s.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!)
  savedV : ∀ i < 8, s.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*i)) 64 = vdword (σ.v (Impl.Sha3.AArch64.Sha3.Vector.vreg (8+i))) 0
  frame : Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ] σ.mem s.mem

theorem in_scr {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (hw : s.wr = σ.wr) {d n : Nat} (hd : d+n ≤ 8192) :
    InRegions s.wr (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ d) n := by
  rw [hw,hp.wr]
  exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ,by simp,Offset.contains_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) hd (by omega)⟩

theorem in_scr_rd {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (_hr : s.rd = σ.rd) (hw : s.wr = σ.wr)
    {d n : Nat} (hd : d+n ≤ 8192) : InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ d) n := by
  obtain ⟨r,hm,hc⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp hw hd
  exact ⟨r,List.mem_append.mpr (.inr hm),hc⟩

theorem in_seed {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (hr : s.rd = σ.rd)
    {d n : Nat} (hd : d+n ≤ 136) : InRegions (s.rd++s.wr) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 d) n := by
  rw [hr,hp.rd]
  exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR σ,by simp,Offset.contains_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ) hd (by omega)⟩

theorem low_save (σ : State) : (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.lowR σ) :=
  Offset.disjoint_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave) (n := 144) (k := oSave) (by decide) (by decide)

theorem B_length (σ : State) (k : Nat) : (VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k).length = 34 := Proof.Sha3.bytesAt_length _ _ _
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave)

theorem Env.frameStep {σ s t : State} (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ],Region.Sub r R)
    (hsave : ∀ r ∈ rs,(VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ).Disjoint r)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t := by
  refine ⟨hr.trans he.rd,hw.trans he.wr,hsp.trans he.sp,
    (hg .x19 (by simp)).trans he.x19,(hg .x20 (by simp)).trans he.x20,
    (hg .x21 (by simp)).trans he.x21,(hg .x30 (by simp)).trans he.x30,
    fun i hi => ?_,fun i hi => ?_,he.frame.trans (hf.sub hsub)⟩
  · have hc : (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ).Contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i)) 8 :=
      Offset.contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+8*i) (e := oSave) (n := 8) (k := 144)
        (by omega) (by omega) (by decide)
    rw [hf.readW hc hsave (by decide)]
    exact he.savedG i hi
  · have hc : (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ).Contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*i)) 8 :=
      Offset.contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+80+8*i) (e := oSave) (n := 8) (k := 144)
        (by omega) (by omega) (by decide)
    rw [hf.readW hc hsave (by decide)]
    exact he.savedV i hi

theorem Env.lowStep {σ s t : State} (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs,Region.Sub r (VG.Proof.MlDsa.AArch64.Sample.Rej4.lowR σ))
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t :=
  he.frameStep hf (fun r hm => ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ,by simp,fun x hx =>
      (Region.sub_prefix (by decide : oSave ≤ 8192)) x (hsub r hm x hx)⟩)
    (fun r hm => (VG.Proof.MlDsa.AArch64.Sample.Rej4.low_save σ).sub_right (hsub r hm)) hr hw hsp hg
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64 (wp_str Mupd)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveG oSave saved)

theorem saveG_ok {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) :
    WP isa (.block saveG) σ fun t => Mupd σ t t.mem ∧ Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ] σ.mem t.mem ∧
      ∀ i < 10,t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!) := by
  unfold saveG
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd σ t t.mem ∧ Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.saveR σ] σ.mem t.mem ∧
      ∀ i < k,t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!))
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 10 (Nat.le_refl _) σ
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*k)) ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [ht.gpr]; rfl) (VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp ht.wr (by dsimp only [oSave]; omega)) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+8*k) (e := oSave) (n := 8) (k := 144) (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i)) 8 (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*k)) 8 :=
        Offset.sep (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+8*i) (e := oSave+8*k) (n := 8) (k := 8) (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveV`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_str WP.cons)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveV oSave)

def vSaveR (σ : State) : Region := ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80),64⟩

theorem saveV_step {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x2 = p)
    (hw : InRegions s.wr (p+BitVec.ofNat 64 (oSave+80+8*i)) 8) :
    WP isa (.block ([.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x2 (oSave+80+8*i)] : List Instr)) s
      fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
        t.mem = s.mem.writeW (p+BitVec.ofNat 64 (oSave+80+8*i)) (vdword (s.v (vreg (8+i))) 0) := by
  refine WP.cons (s' := s.write .x .x8 (vdword (s.v (vreg (8+i))) 0)) rfl ?_
  have h1 := Upd.write64 s .x8 (vdword (s.v (vreg (8+i))) 0)
  refine wp_str ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [h1.other .x2 (by decide),hp]) (by rw [h1.wr]; exact hw)
    fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (RegKeep.upd h1).trans (RegKeep.mupd h2) |>.mono (by simp)
  · exact h2.vec.trans h1.vec
  · rw [h2.mem,h1.mem,h1.gpr]

theorem saveV_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (hw : s.wr = σ.wr) (hs : s.gpr .x2 = VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) :
    WP isa (.block saveV) s fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
      Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.vSaveR σ] s.mem t.mem ∧ ∀ i < 8,
        t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0 := by
  unfold saveV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.v = s.v ∧ Frame [VG.Proof.MlDsa.AArch64.Sample.Rej4.vSaveR σ] s.mem t.mem ∧ ∀ i < k,
      t.mem.readW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveV_step hk ((ht.gpr .x2 (by decide)).trans hs)
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp (ht.wr.trans hw) (by dsimp only [oSave]; omega))) fun u ⟨hu,hvu,hm⟩ => ?_
  change u.mem = t.mem.writeW (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*k)) (vdword (t.v (vreg (8+k))) 0) at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+80+8*k) (e := oSave+80) (n := 8) (k := 64)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*i)) 8 (VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+80+8*k)) 8 :=
        Offset.sep (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+80+8*i) (e := oSave+80+8*k) (n := 8) (k := 8)
          (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_mov)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (proArgs)

theorem proArgs_ok (s : State) :
    WP isa (.block proArgs) s fun t => Only [.x19,.x20,.x21] s t ∧
      t.gpr .x19 = s.gpr .x2 ∧ t.gpr .x20 = s.gpr .x0 ∧ t.gpr .x21 = s.gpr .x1 := by
  unfold proArgs
  refine wp_mov fun s1 h1 e1 => wp_mov fun s2 h2 e2 => wp_mov fun t h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x19,h2.get .x19,e1]
  · rw [h3.get .x20,e2,h1.get .x0]
  · rw [e3,h2.get .x1,h1.get .x1]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (pro oSave)

theorem pro_ok {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) : WP isa (.block pro) σ (VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ) := by
  unfold pro
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveG_ok hp) fun s1 ⟨h1,hf1,hg1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveV_ok hp h1.wr (by rw [h1.gpr]; rfl)) fun s2 ⟨h2,hv2,hf2,hvsave⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.proArgs_ok s2) fun t ⟨h3,e19,e20,e21⟩ => ?_
  refine ⟨h3.rd.trans (h2.rd.trans h1.rd),h3.wr.trans (h2.wr.trans h1.wr),
    h3.sp.trans (h2.sp.trans h1.sp),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [e19,h2.gpr .x2 (by decide),h1.gpr]; rfl
  · rw [e20,h2.gpr .x0 (by decide),h1.gpr]; rfl
  · rw [e21,h2.gpr .x1 (by decide),h1.gpr]; rfl
  · rw [h3.get .x30,h2.gpr .x30 (by decide),h1.gpr]
  · intro i hi
    rw [h3.mem]
    have hd : (⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oSave+8*i),8⟩ : Region).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.vSaveR σ) :=
      Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+8*i) (n := 8) (e := oSave+80) (k := 64)
        (by omega) (by dsimp only [oSave]; omega) (by decide)
    rw [hf2.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact hg1 i hi
  · intro i hi
    rw [h3.mem,hvsave i hi,h1.vec]
  · rw [h3.mem]
    exact (hf1.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
      ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ,by simp,Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave) (n := 144) (k := 8192) (by decide)⟩)).trans
      (hf2.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
        ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ,by simp,Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oSave+80) (n := 64) (k := 8192) (by decide)⟩))
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_addImm)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbArgs)

theorem absorbArgs_ok {s : State} {p : Nat} (hp : p < 2) :
    WP isa (.block (absorbArgs p)) s fun t => Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2 = s.gpr .x19+BitVec.ofNat 64 (400*p) ∧
      t.gpr .x3 = s.gpr .x20+BitVec.ofNat 64 (68*p) ∧
      t.gpr .x4 = s.gpr .x20+BitVec.ofNat 64 (68*p+34) := by
  unfold absorbArgs
  refine wp_addImm (by omega) fun s1 h1 e1 => wp_addImm (by omega) fun s2 h2 e2 =>
    wp_addImm (by decide) fun t h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x2,h2.get .x2,e1]
  · rw [h3.get .x3,e2,h1.get .x20]
  · rw [e3,e2,h1.get .x20,Offset.add_add]

/-- Initialize both pairs while retaining the saved ABI registers. -/
theorem zeroAll_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t ∧
      ∀ i < 50,t.mem.read (wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) i) 16 = 0 := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.zeros_ok he.x19 (fun i hi => VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp he.wr (by omega))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64

theorem seed_sub {σ : State} {k : Nat} (hk : k < 4) :
    Region.Sub (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 (34*k))) (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR σ) :=
  Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ) (by omega)

theorem seed_eq {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {k : Nat} (hk : k < 4) :
    Spec.Sha3.bytesAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 (34*k)) 34 = VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_a.sub_left (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_sub hk)
  · exact hp.seed_scr.sub_left (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_sub hk)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbPair oSave)

theorem pair_sub {σ : State} {p : Nat} (hp : p < 2) : Region.Sub (pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.lowR σ) :=
  Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by dsimp only [oSave]; omega)

theorem absorbPair_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {p : Nat} (hpn : p < 2)
    (hz : ∀ i < 25,s.mem.read (wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) i) 16 = 0) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Sample.Rej4.absorbPair p)) s fun t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t ∧
      PairAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ (2*p)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ (2*p+1)) ∧
      Frame [pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p)] s.mem t.mem := by
  unfold VG.Impl.MlDsa.AArch64.Sample.Rej4.absorbPair
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 (34*(2*p))
  let b := VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 (34*(2*p+1))
  have e2' : s1.gpr .x2 = VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 68*p = 34*(2*p) by omega]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 68*p+34 = 34*(2*p+1) by omega]
  have seed_in (k : Nat) (hk : k < 4) (d n : Nat) (hd : d+n ≤ 34) :
      InRegions (s1.rd++s1.wr) ((VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ+BitVec.ofNat 64 (34*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_seed hp he1.rd (by omega)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) j) 16 := by
    intro j hj
    unfold wordAddr VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
    rw [Offset.add_add]
    exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp he1.wr (by omega)
  have hps : Region.Sub (pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ) :=
    Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by omega)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega) (8*j) 8 (by omega))
    (fun j hj => seed_in (2*p+1) (by omega) (8*j) 8 (by omega))
    (seed_in (2*p) (by omega) 32 1 (by decide)) (seed_in (2*p) (by omega) 33 1 (by decide))
    (seed_in (2*p+1) (by omega) 32 1 (by decide)) (seed_in (2*p+1) (by omega) 33 1 (by decide))
    hws ((hp.seed_scr.sub_left (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_sub (by omega))).sub_right hps)
    ((hp.seed_scr.sub_left (VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_sub (by omega))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState_eq,VG.Proof.MlDsa.AArch64.Sample.Rej4.seedState_eq,VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_eq hp he1 (by omega : 2*p < 4),VG.Proof.MlDsa.AArch64.Sample.Rej4.seed_eq hp he1 (by omega : 2*p+1 < 4)] at hp2
    exact hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqBlock`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oSave)

def pReg (p : Nat) : Reg := if p = 0 then .x22 else .x23
def bReg (k : Nat) : Reg := [.x24,.x25,.x26,.x27][k]!

theorem pair_regs : ∀ p < 2,
    VG.Proof.MlDsa.AArch64.Sample.Rej4.pReg p ≠ .x16 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p) ≠ .x6 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p) ≠ .x7 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p) ≠ .x16 ∧
      VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1) ≠ .x6 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1) ≠ .x7 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1) ≠ .x16 := by decide

theorem buf_word (σ : State) (k n i : Nat) : outAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ k n) i = VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oBuf+1008*k+168*n+8*i) := by
  unfold outAddr VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
  rw [Offset.add_add]

theorem pair_word (σ : State) (p i : Nat) : wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) i = VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (400*p+16*i) := by
  unfold wordAddr VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
  rw [Offset.add_add]

theorem block_regions_low {σ : State} {p n : Nat} (hp : p < 2) (hn : n < 6) :
    ∀ r ∈ [pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n)], Region.Sub r (VG.Proof.MlDsa.AArch64.Sample.Rej4.lowR σ) := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by dsimp only [oSave]; omega)
  · exact Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by dsimp only [oBuf,oSave]; omega)
  · exact Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by dsimp only [oBuf,oSave]; omega)

/-- One pair's permutation and rate output, inside the four-way sampler. -/
theorem pairBlock_ok (sha3 : Bool) {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {p n : Nat} (hpn : p < 2) (hn : n < 6)
    {A B : Spec.Sha3.State}
    (hx : s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.pReg p) = VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p)
    (ha : s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p)) = VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n)
    (hb : s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1)) = VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n)
    (hpair : PairAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) A B) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 (VG.Proof.MlDsa.AArch64.Sample.Rej4.pReg p) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1))) s
      fun t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t ∧ VG.Proof.Sha3.AArch64.Neon.BlockKeep s t ∧
        PairAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
        RateAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n) (Spec.Sha3.keccakF A) ∧
        RateAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n) (Spec.Sha3.keccakF B) ∧
        Frame [pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n)] s.mem t.mem := by
  obtain ⟨hp16,ha6,ha7,ha16,hb6,hb7,hb16⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.pair_regs p hpn
  refine WP.mono (prog_okWith sha3 hx ha hb ha6 ha7 ha16 hb6 hb7 hb16 hp16 hpair
    (fun i hi => by rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.pair_word]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp he.rd he.wr (by omega))
    (fun i hi => by rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.pair_word]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp he.wr (by omega))
    (fun i hi => by rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_word]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp he.wr (by dsimp only [oBuf]; omega))
    (fun i hi => by rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_word]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr hp he.wr (by dsimp only [oBuf]; omega))
    (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oBuf+1008*(2*p)+168*n) (n := 168)
      (e := oBuf+1008*(2*p+1)+168*n) (k := 168) (by omega)
      (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega))
    (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*p) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)))
    fun t ⟨ht,hpt,hat,hbt,hft⟩ => ?_
  exact ⟨he.lowStep hft (VG.Proof.MlDsa.AArch64.Sample.Rej4.block_regions_low hpn hn) ht.rd ht.wr ht.sp (fun r hr => ht.gpr r
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    ht,hpt,hat,hbt,hft⟩
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF byteOf)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def F (σ : State) (k j : Nat) : Byte := (Spec.MlDsa.G (VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k) 1008).getD j 0

theorem F_block (σ : State) (k : Nat) {n j : Nat} (hn : n < 6) (hj : j < 168) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.F σ k (168*n+j) = byteOf (iterF (n+1) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ k)) j := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.F
  change (Spec.MlKem.xof (VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k) 1008).getD (168*n+j) 0 = _
  rw [Proof.MlKem.xof_getD (VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k) (by omega),Proof.Sha3.Seed34.xofByte_A0 (VG.Proof.MlDsa.AArch64.Sample.Rej4.B_length σ k) hj]

structure Phase (σ : State) (n phase : Nat) (s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s
  x22 : s.gpr .x22 = VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 0
  x23 : s.gpr .x23 = VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1
  ptrs : ∀ k < 4,s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k) = VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ k n
  count : (s.gpr .x28).toNat = 6-n
  states : ∀ p < 2,PairAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p)
    (iterF (n+if p < phase then 1 else 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ (2*p)))
    (iterF (n+if p < phase then 1 else 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ (2*p+1)))
  out : ∀ k < 4,∀ j < 168*(n+if k < 2*phase then 1 else 0),
    s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j) = VG.Proof.MlDsa.AArch64.Sample.Rej4.F σ k j

theorem phase_state_ptr {σ s : State} {n ph : Nat} (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n ph s) {p : Nat} (hp : p < 2) :
    s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.pReg p) = VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
  · exact h.x22
  · exact h.x23

theorem buf_byte_address (σ : State) (k n j : Nat) (hj : 168*n ≤ j) :
    VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j = VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ k n+BitVec.ofNat 64 (j-168*n) := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
  rw [Offset.add_add,Offset.add_add]
  exact congrArg (fun a => VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ+BitVec.ofNat 64 a) (by omega)

/-- A pair's rate writes preserve all preceding bytes and every other stream. -/
theorem old_byte {σ : State} {p n k j : Nat} (hp : p < 2) (hn : n < 6) (hk : k < 4) (hj : j < 1008)
    (ho : j < 168*n ∨ (k ≠ 2*p ∧ k ≠ 2*p+1)) {m m' : Mem}
    (hf : Frame [pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n)] m m') :
    m' (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j) = m (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j) := by
  have haddr : VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j = VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (oBuf+1008*k+j) := by
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [Offset.add_add]
  rw [haddr]
  refine hf _ (fun r hr => ?_)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oBuf+1008*k+j) (n := 1) (e := 400*p) (k := 400)
      (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega) (by omega)) _ (Region.contains_self _ _)
  · exact (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oBuf+1008*k+j) (n := 1) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by rcases ho with h | ⟨h,_⟩ <;> omega) (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
      _ (Region.contains_self _ _)
  · exact (Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := oBuf+1008*k+j) (n := 1) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by rcases ho with h | ⟨_,h⟩ <;> omega) (by dsimp only [oBuf]; omega) (by dsimp only [oBuf]; omega))
      _ (Region.contains_self _ _)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqFrame`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

theorem pair_frame {σ : State} {p n i : Nat} (hp : p < 2) (hn : n < 6) (hi : i < 2) (hip : i ≠ p)
    {m m' : Mem} (hf : Frame [pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p) n),outR (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt σ (2*p+1) n)] m m')
    {A B : Spec.Sha3.State} (hpair : PairAt m (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ i) A B) : PairAt m' (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ i) A B := by
  intro j hj
  rw [hf.read (pair_contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ i) hj) (fun r hr => ?_) (by decide)]
  · exact hpair j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*i) (n := 400) (e := 400*p) (k := 400)
      (by omega) (by omega) (by omega)
  · exact Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*i) (n := 400) (e := oBuf+1008*(2*p)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)
  · exact Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*i) (n := 400) (e := oBuf+1008*(2*p+1)+168*n) (k := 168)
      (by dsimp only [oBuf]; omega) (by omega) (by dsimp only [oBuf]; omega)

theorem b_regs : ∀ k < 4,VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k ≠ .x6 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k ≠ .x7 ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k ≠ .x16 := by decide
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

theorem phasePair_ok (sha3 : Bool) {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {n p : Nat} (hn : n < 6) (hpn : p < 2)
    (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n p s) :
    WP isa (Impl.Sha3.AArch64.Neon.Pair.progWith sha3 (VG.Proof.MlDsa.AArch64.Sample.Rej4.pReg p) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg (2*p+1))) s
      (VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n (p+1)) := by
  have hpair := h.states p hpn
  simp only [Nat.lt_irrefl,ite_false,Nat.add_zero] at hpair
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.pairBlock_ok sha3 hp h.env hpn hn (VG.Proof.MlDsa.AArch64.Sample.Rej4.phase_state_ptr h hpn)
    (h.ptrs (2*p) (by omega)) (h.ptrs (2*p+1) (by omega)) hpair)
    fun t ⟨he,ht,hpt,hat,hbt,hft⟩ => ?_
  rw [← iterF_succ,← iterF_succ] at hpt
  rw [← iterF_succ] at hat hbt
  refine ⟨he,(ht.gpr .x22 (by decide) (by decide) (by decide)).trans h.x22,
    (ht.gpr .x23 (by decide) (by decide) (by decide)).trans h.x23,
    fun k hk => ?_,by rw [ht.gpr .x28 (by decide) (by decide) (by decide)]; exact h.count,
    fun i hi => ?_,fun k hk j hj => ?_⟩
  · obtain ⟨h6,h7,h16⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.b_regs k hk
    exact (ht.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k) h6 h7 h16).trans (h.ptrs k hk)
  · by_cases heq : i = p
    · subst i
      simpa only [Nat.lt_succ_self,ite_true] using hpt
    · apply VG.Proof.MlDsa.AArch64.Sample.Rej4.pair_frame hpn hn hi heq hft
      have hs := h.states i hi
      by_cases hc : i < p <;> simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hs
  · have hjnext : j < 168*(n+1) := by split at hj <;> omega
    have hj1008 : j < 1008 := by omega
    by_cases hjold : j < 168*n
    · rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.old_byte hpn hn hk hj1008 (.inl hjold) hft]
      exact h.out k hk j (by split <;> omega)
    · by_cases heq : k = 2*p
      · subst k
        rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_byte_address σ (2*p) n j (by omega),hat.byte (j := j-168*n) (by omega),
          ← VG.Proof.MlDsa.AArch64.Sample.Rej4.F_block σ (2*p) (n := n) (j := j-168*n) hn (by omega),show 168*n+(j-168*n) = j by omega]
      · by_cases heq' : k = 2*p+1
        · subst k
          rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_byte_address σ (2*p+1) n j (by omega),hbt.byte (j := j-168*n) (by omega),
            ← VG.Proof.MlDsa.AArch64.Sample.Rej4.F_block σ (2*p+1) (n := n) (j := j-168*n) hn (by omega),show 168*n+(j-168*n) = j by omega]
        · rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.old_byte hpn hn hk hj1008 (.inr ⟨heq,heq'⟩) hft]
          apply h.out k hk j
          by_cases hc : k < 2*p <;>
            simpa (disch := omega) only [ite_eq_left,ite_eq_right] using hj
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_addImm wp_subImm)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (advance)

theorem advance_ok (s : State) : WP isa (.block advance) s fun t => Only [.x24,.x25,.x26,.x27,.x28] s t ∧
    (∀ k < 4,t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k) = s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k)+168) ∧ t.gpr .x28 = s.gpr .x28-1 := by
  unfold advance
  refine wp_addImm (by decide) fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_subImm (by decide) fun t h5 e5 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((((h1.trans h2).trans h3).trans h4).trans h5).mono (by simp)
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = s.gpr .x24+168
      rw [h5.get .x24,h4.get .x24,h3.get .x24,h2.get .x24,e1]; rfl
    · change t.gpr .x25 = s.gpr .x25+168
      rw [h5.get .x25,h4.get .x25,h3.get .x25,e2,h1.get .x25]; rfl
    · change t.gpr .x26 = s.gpr .x26+168
      rw [h5.get .x26,h4.get .x26,e3,h2.get .x26,h1.get .x26]; rfl
    · change t.gpr .x27 = s.gpr .x27+168
      rw [h5.get .x27,e4,h3.get .x27,h2.get .x27,h1.get .x27]; rfl
  · rw [e5,h4.get .x28,h3.get .x28,h2.get .x28,h1.get .x28]; rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init)

theorem pairs_disjoint (σ : State) : (pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 0)).Disjoint (pairR (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1)) :=
  Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ p) i = wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (25*p+i) := by
  unfold wordAddr VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem init_ok {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) : WP isa (.block init) σ fun t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t ∧
    PairAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 1) ∧
    PairAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 2) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 3) := by
  unfold init
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.pro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.absorbPair_ok (p := 0) hp he2 (by decide : 0 < 2) (fun i hi => by
    rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega))) fun s3 ⟨he3,hp3,hf3⟩ => ?_
  have hz3 : ∀ i < 25,s3.mem.read (wordAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1) i) 16 = 0 := by
    intro i hi
    rw [hf3.read (pair_contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1) hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (VG.Proof.MlDsa.AArch64.Sample.Rej4.pairs_disjoint σ).symm) (by decide),VG.Proof.MlDsa.AArch64.Sample.Rej4.state_word]
    exact hz2 (25+i) (by omega)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.absorbPair_ok (p := 1) hp he3 (by decide : 1 < 2) hz3) fun t ⟨het,hpt,hft⟩ => ?_
  refine ⟨het,?_,hpt⟩
  intro i hi
  rw [hft.read (pair_contains (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 0) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlDsa.AArch64.Sample.Rej4.pairs_disjoint σ) (by decide)]
  exact hp3 i hi
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_mov wp_addImm wp_movz)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (setup oBuf)

theorem setup_shape (s : State) : WP isa (.block setup) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧ t.gpr .x22 = s.gpr .x19 ∧
      t.gpr .x23 = s.gpr .x19+BitVec.ofNat 64 400 ∧
      (∀ k < 4,t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg k) = s.gpr .x19+BitVec.ofNat 64 (oBuf+1008*k)) ∧ t.gpr .x28 = 6 := by
  unfold setup
  refine wp_mov fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
        wp_movz fun t h7 e7 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_,?_⟩
  · exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).mono (by simp)
  · rw [h7.get .x22,h6.get .x22,h5.get .x22,h4.get .x22,h3.get .x22,h2.get .x22,e1]
  · rw [h7.get .x23,h6.get .x23,h5.get .x23,h4.get .x23,h3.get .x23,e2,h1.get .x19]
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = _
      rw [h7.get .x24,h6.get .x24,h5.get .x24,h4.get .x24,e3,h2.get .x19,h1.get .x19]
    · change t.gpr .x25 = _
      rw [h7.get .x25,h6.get .x25,h5.get .x25,e4,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x26 = _
      rw [h7.get .x26,h6.get .x26,e5,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x27 = _
      rw [h7.get .x27,e6,h5.get .x19,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
  · rw [e7]; rfl

/-- Enter the six-block loop after absorbing all four seeds. -/
theorem setup_ok {σ s : State} (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s)
    (hp0 : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 1))
    (hp1 : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP σ 1) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 2) (VG.Proof.MlDsa.AArch64.Sample.Rej4.A0 σ 3)) :
    WP isa (.block setup) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 0 0) := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.setup_shape s) fun t ⟨ht,e22,e23,hptr,e28⟩ => ?_
  refine ⟨he.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp) ht.rd ht.wr ht.sp
    (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_,?_,?_,?_,?_⟩
  · rw [e22,he.x19]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
    rw [Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [e23,he.x19]; rfl
  · intro k hk
    rw [hptr k hk,he.x19]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
    rw [Nat.mul_zero,Nat.add_zero]
  · rw [e28]; rfl
  · intro p hp
    rw [ht.mem]
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
    · exact hp0
    · exact hp1
  · intro k _ j hj
    exact False.elim (by simp at hj)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (toNat_sub_n)

theorem phaseAdvance_ok {σ s : State} {n : Nat} (hn : n < 6) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n 2 s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.advance) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ (n+1) 0) := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.advance_ok s) fun t ⟨ht,hptr,hct⟩ => ?_
  refine ⟨h.env.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp) ht.rd ht.wr ht.sp
    (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    (ht.get .x22).trans h.x22,(ht.get .x23).trans h.x23,fun k hk => ?_,?_,fun p hp => ?_,fun k hk j hj => ?_⟩
  · rw [hptr k hk,h.ptrs k hk]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
    rw [show (168 : BitVec 64) = BitVec.ofNat 64 168 from rfl,Offset.add_add]
    exact congrArg (fun d => VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ+BitVec.ofNat 64 d) (by omega)
  · rw [hct,toNat_sub_n (by rw [h.count]; change 1 ≤ 6-n; omega),h.count]
    change 6-n-1 = 6-(n+1)
    omega
  · rw [ht.mem]
    have hs := h.states p hp
    simpa only [ite_eq_left hp,ite_eq_right (Nat.not_lt_zero _)] using hs
  · rw [ht.mem]
    apply h.out k hk j
    simpa only [Nat.mul_zero,ite_eq_left hk,ite_eq_right (Nat.not_lt_zero _)] using hj
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (count_loop)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (squeezeStepWith)

theorem squeezeStep_ok (sha3 : Bool) {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {n : Nat} (hn : n < 6) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n 0 s) :
    WP isa (squeezeStepWith sha3) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ (n+1) 0) := by
  unfold squeezeStepWith
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.phasePair_ok sha3 hp hn (by decide : 0 < 2) h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.phasePair_ok sha3 hp hn (by decide : 1 < 2) h1) fun s2 h2 => ?_)
  exact VG.Proof.MlDsa.AArch64.Sample.Rej4.phaseAdvance_ok hn h2

theorem squeeze_ok (sha3 : Bool) {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 0 0 s) :
    WP isa (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 6 0) := by
  refine count_loop (by decide : 0 < 6) (fun n t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ n 0 t) (fun n hn t ht => ?_) h
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.squeezeStep_ok sha3 hp hn ht) fun u hu => ⟨hu,?_⟩
  rw [hu.count]
  omega
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Sponge`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init setup squeezeStepWith)

structure Ready (σ s : State) : Prop where
  env : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s
  out : ∀ k < 4, ∀ j < 1008, s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k+BitVec.ofNat 64 j) = VG.Proof.MlDsa.AArch64.Sample.Rej4.F σ k j

theorem sponge_ok (sha3 : Bool) {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) :
    WP isa (.seq (.block (init++setup))
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28))) σ (VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.setup_ok he h0 h1) fun u hu => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.squeeze_ok sha3 hp hu) fun t ht => ⟨ht.env,?_⟩
  intro k hk j hj
  exact ht.out k hk j (by simpa using hj)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ParseMem`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.Sample (polyR coeffAddr)

def polyP (σ : State) (k : Nat) : Addr := VG.Proof.MlDsa.AArch64.Sample.Rej4.aP σ+BitVec.ofNat 64 (1024*k)

theorem poly_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)) (VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ) :=
  Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.aP σ) (by omega)

theorem buf_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k,1008⟩ : Region) (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ) :=
  Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by dsimp only [VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf]; omega)

theorem buf_poly {σ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {j k : Nat} (hj : j < 4) (hk : k < 4) :
    (⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ j,1008⟩ : Region).Disjoint (polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)) :=
  hp.a_scr.symm.sub_left (VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_sub σ hj) |>.sub_right (VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_sub σ hk)

theorem coeffs_in {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (hw : s.wr = σ.wr) {k : Nat} (hk : k < 4) :
    ∀ i < 256,InRegions s.wr (coeffAddr (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) i) 4 := by
  intro i hi
  rw [hw,hp.wr]
  refine ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,by simp,?_⟩
  unfold coeffAddr VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP
  rw [Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem Env.polyStep {σ s t : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {k : Nat} (hk : k < 4) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s)
    (hf : Frame [polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ t :=
  he.frameStep hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,by simp,VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_sub σ hk⟩)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.a_scr.symm.sub_left (Offset.sub_base (VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ) (by decide)) |>.sub_right (VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_sub σ hk))
    hr hw hsp hg

theorem Ready.polyStep {σ s t : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {k : Nat} (hk : k < 4) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s)
    (hf : Frame [polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ t := by
  refine ⟨h.env.polyStep hp hk hf hr hw hsp hg,fun j hj i hi => ?_⟩
  rw [← h.out j hj i hi]
  exact hf _ (fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_poly hp hj hk _ (Offset.contains_base _ (by omega) (by omega)) hc)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Parse`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_addImm wp_subImm wp_lsr wp_and wp_nil toNat_lsr)
open VG.Proof.MlDsa.AArch64.Sample (zeroPoly_ok)
open VG.Proof.MlDsa.Sample (rnFold G_length Stored polyR)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop retZ)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample oBuf)

abbrev X (σ : State) (k : Nat) := Spec.MlDsa.G (VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k) 1008
abbrev L (σ : State) (k : Nat) := rnFold [] (VG.Proof.MlDsa.AArch64.Sample.Rej4.X σ k)
abbrev result (σ : State) (k : Nat) : BitVec 64 := if (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length = 256 then 1 else 0
abbrev parseRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x13,.x14,.x15,.x25,.x26,.x27]

theorem sampleArgs_ok {σ s : State} (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) {k : Nat} (hk : k < 4) :
    WP isa (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) s
      fun t => Only [.x25,.x26] s t ∧ t.gpr .x25 = VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (1008*k) ∧ t.gpr .x26 = VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k := by
  refine wp_addImm (by omega) fun u h1 e1 => wp_addImm (by omega) fun t h2 e2 => wp_nil ⟨?_,?_,?_⟩
  · exact (h1.trans h2).mono (by simp)
  · rw [h2.get .x25,e1,he.x19]; rfl
  · rw [e2,h1.get .x21,he.x21]; rfl

theorem retZ_ok {σ s : State} {k : Nat} (h4 : (s.gpr .x4).toNat = 256-(VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length) :
    WP isa (.block (retZ++([.logic .and .x .x27 .x27 .x0] : List Instr))) s fun t =>
      Only [.x0,.x27] s t ∧ t.gpr .x27 = s.gpr .x27 &&& VG.Proof.MlDsa.AArch64.Sample.Rej4.result σ k := by
  unfold retZ
  refine wp_subImm (by decide) fun u h1 e1 => wp_lsr (by decide) fun v h2 e2 =>
    wp_and fun t h3 e3 => wp_nil ⟨((h1.trans h2).trans h3).mono (by simp),?_⟩
  have hl := VG.Proof.MlDsa.Sample.rnFold_length_le (a := ([] : List Spec.MlDsa.Zq)) (by simp) (VG.Proof.MlDsa.AArch64.Sample.Rej4.X σ k)
  have er : v.gpr .x0 = VG.Proof.MlDsa.AArch64.Sample.Rej4.result σ k := by
    apply BitVec.eq_of_toNat_eq
    rw [e2,toNat_lsr,e1,BitVec.toNat_sub,h4]
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [one]
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.result
    have hn1 : (1 : BitVec 64).toNat = 1 := rfl
    have hn0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [VG.Spec.MlDsa.n] at hl
    change (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length ≤ 256 at hl
    split
    · rw [hn1]; omega
    · rw [hn0]; omega
  rw [e3,h2.get .x27,h1.get .x27,er]

theorem sample_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s) {k : Nat} (hk : k < 4) :
    WP isa (sample k) s fun t => VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ t ∧ Keep VG.Proof.MlDsa.AArch64.Sample.Rej4.parseRegs s t ∧
      Frame [polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)] s.mem t.mem ∧ Stored t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k) ∧
        t.gpr .x27 = s.gpr .x27 &&& VG.Proof.MlDsa.AArch64.Sample.Rej4.result σ k := by
  unfold sample
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.sampleArgs_ok h.env hk) fun s1 ⟨h1,e25,e26⟩ => ?_)
  have he1 : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s1 := h.polyStep hp hk (by rw [h1.mem]; exact Frame.refl _ _)
    h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  refine WP.seq (WP.mono (zeroPoly_ok (VG.Proof.MlDsa.AArch64.Sample.Rej4.coeffs_in hp he1.env.wr hk) e26) fun s2 ⟨h2,_,f2⟩ => ?_)
  have he2 : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s2 := he1.polyStep hp hk f2 h2.rd h2.wr h2.sp (fun r hr => h2.get r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have hlp : VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre (VG.Proof.MlDsa.AArch64.Sample.Rej4.X σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) s2 :=
    ⟨he2.out k hk,fun j hj => by
      unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
      rw [Offset.add_add]
      exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp he2.env.rd he2.env.wr (by dsimp only [oBuf]; omega),
      VG.Proof.MlDsa.AArch64.Sample.Rej4.coeffs_in hp he2.env.wr hk,VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_poly hp hk hk,by
        rw [h2.get .x25,e25]
        unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.at' VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP
        rw [Offset.add_add]
        exact congrArg (fun d => VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega),
      (h2.get .x26).trans e26⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (VG.Proof.MlDsa.Sample.G_length _ _) hlp)
    fun s3 h3 => ?_)
  have he3 := he2.polyStep hp hk h3.frame h3.keep.rd h3.keep.wr h3.keep.sp
    (fun r hr => h3.keep.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have hx4 := h3.x4
  have hst := h3.st
  rw [VG.Proof.MlDsa.AArch64.Sample.RejNtt.Lt_336 (VG.Proof.MlDsa.Sample.G_length _ _)] at hx4 hst
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.retZ_ok hx4) fun t ⟨h4,e27⟩ => ?_
  refine ⟨he3.polyStep hp hk (by rw [h4.mem]; exact Frame.refl _ _)
    h4.rd h4.wr h4.sp (fun r hr => h4.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),
    (((h1.keep.trans h2).trans h3.keep).trans h4.keep).mono (by simp [VG.Proof.MlDsa.AArch64.Sample.Rej4.parseRegs,VG.Proof.MlDsa.AArch64.Sample.RejNtt.lRegs]),
    ?_,?_,?_⟩
  · rw [h4.mem,← h1.mem]
    exact f2.trans h3.frame
  · rw [h4.mem]; exact hst
  · rw [e27,h3.keep.get .x27,h2.get .x27,h1.get .x27]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreV`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (restoreV oSave)

theorem low_setLane (v : BitVec 128) (a : BitVec 64) : vdword (setLane v 64 0 a) 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,setLane,BitVec.getLsbD_extractLsb',BitVec.getLsbD_or,
    BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi,decide_eq_true]

theorem restoreV_step {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x19 = p)
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (oSave+80+8*i)) 8) :
    WP isa (.block ([.ldr .x .x8 .x19 (oSave+80+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)] : List Instr)) s
      fun t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
        vdword (t.v (vreg (8+i))) 0 = s.mem.readW (p+BitVec.ofNat 64 (oSave+80+8*i)) 64 ∧
        ∀ r, r ≠ vreg (8+i) → t.v r = s.v r := by
  refine wp_ldr ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [hp]) hin fun u h1 => ?_
  refine wp_vop (d := vreg (8+i)) rfl fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).mono (by simp)
  · exact h2.mem.trans h1.mem
  · rw [h2.v,VG.Proof.MlDsa.AArch64.Sample.Rej4.low_setLane,h1.gpr]
  · intro r hr
    rw [h2.other r hr,h1.vec]

theorem restoreV_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) :
    WP isa (.block restoreV) s fun t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < 8,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0 := by
  unfold restoreV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < k,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hm,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.restoreV_step hk ((ht.gpr .x19 (by decide)).trans he.x19)
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp (ht.rd.trans he.rd) (ht.wr.trans he.wr) (by dsimp only [oSave]; omega)))
      fun u ⟨hu,hmu,hvu,hother⟩ => ?_
  refine ⟨(ht.trans hu).mono (by simp),hmu.trans hm,fun i hi => ?_⟩
  by_cases heq : i = k
  · subst i
    rw [hvu,hm]
    exact he.savedV k hk
  · rw [hother (vreg (8+i)) (fun h => heq (by
      have e := (VG.Proof.Sha3.AArch64.Neon.vreg_inj (8+i) (by omega) (8+k) (by omega)).mp h
      omega))]
    exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrx)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (restoreG oSave saved)

theorem saved_inj : ∀ i < 10, ∀ j < 10, saved[i]! = saved[j]! ↔ i = j := by decide

theorem saved_ne19 : ∀ i < 9, saved[i+1]! ≠ Reg.x19 := by decide

/-- Restore x20 through x28 while keeping the scratch base in x19. -/
theorem restoreG_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) :
    WP isa (.block restoreG) s fun t => Only (saved.drop 1) s t ∧
      ∀ i < 9,t.gpr (saved[i+1]!) = σ.gpr (saved[i+1]!) := by
  unfold restoreG
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Only (saved.drop 1) s t ∧ ∀ i < k,t.gpr (saved[i+1]!) = σ.gpr (saved[i+1]!))
    (fun k t hk ⟨ht,hvals⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨Only.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  have hin := VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp (ht.rd.trans he.rd) (ht.wr.trans he.wr)
    (d := oSave+8*(k+1)) (n := 8) (by dsimp only [oSave]; omega)
  refine wp_ldrx ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [ht.get .x19,he.x19]; rfl) hin fun u hu eu => WP.block_nil_iff.mpr ⟨?_,fun i hi => ?_⟩
  · exact (ht.trans hu).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]
        exact (by
          have hm : ∀ j < 9,saved[j+1]! ∈ saved.drop 1 := by decide
          exact hm k hk))
  · by_cases heq : i = k
    · subst i
      rw [eu,ht.mem]
      exact he.savedG (k+1) (by omega)
    · rw [hu.get (saved[i+1]!) (by
        simp only [List.mem_singleton,VG.Proof.MlDsa.AArch64.Sample.Rej4.saved_inj (i+1) (by omega) (k+1) (by omega)]
        omega)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Epi`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_mov wp_ldrx)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (epi oSave saved)

theorem epi_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (he : VG.Proof.MlDsa.AArch64.Sample.Rej4.Env σ s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .x0 = s.gpr .x27 ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  unfold epi
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine wp_mov fun s1 h1 e1 => WP.block_nil_iff.mpr ?_
  have he1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _) (by simp)
    h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.restoreV_ok hp he1) fun s2 ⟨h2,m2,v2⟩ => ?_
  have he2 := he1.lowStep (rs := []) (by rw [m2]; exact Frame.refl _ _) (by simp)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.restoreG_ok hp he2) fun s3 ⟨h3,g3⟩ => ?_
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ oSave) ⟨by decide,by decide⟩ (by rw [h3.get .x19,he2.x19]; rfl)
    (VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp (h3.rd.trans he2.rd) (h3.wr.trans he2.wr) (d := oSave) (n := 8) (by decide))
    fun t h4 e4 => WP.block_nil_iff.mpr ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro r hr
    have hs : ∀ r ∈ preserved,r = .x19 ∨ r = .x30 ∨ ∃ i < 9,r = saved[i+1]! := by decide
    rcases hs r hr with rfl | rfl | ⟨i,hi,rfl⟩
    · rw [e4,h3.mem,m2,h1.mem]
      exact he.savedG 0 (by decide)
    · rw [h4.get .x30,h3.get .x30,h2.gpr .x30 (by decide),he1.x30]
    · rw [h4.get (saved[i+1]!) (by simpa only [List.mem_singleton] using VG.Proof.MlDsa.AArch64.Sample.Rej4.saved_ne19 i hi)]
      exact g3 i hi
  · exact h4.sp.trans (h3.sp.trans (h2.sp.trans he1.sp))
  · intro r hr
    have hs : ∀ r ∈ preservedV,∃ i < 8,r = VG.Impl.Sha3.AArch64.Sha3.Vector.vreg (8+i) := by decide
    obtain ⟨i,hi,rfl⟩ := hs r hr
    rw [h4.vcs _ hr,h3.vcs _ hr]
    exact v2 i hi
  · exact h4.mem.trans (h3.mem.trans (m2.trans h1.mem))
  · rw [h4.get .x0,h3.get .x0,h2.gpr .x0 (by decide),e1]
  · exact h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd))
  · exact h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr))
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Top`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Proof.MlDsa.Sample (Stored stored_frame stored_polyIs rnFold_length_le)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

def mask (σ : State) (n : Nat) : BitVec 64 :=
  if (List.range n).all (fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length == 256) then 1 else 0

theorem mask_step (σ : State) (n : Nat) : VG.Proof.MlDsa.AArch64.Sample.Rej4.mask σ n &&& VG.Proof.MlDsa.AArch64.Sample.Rej4.result σ n = VG.Proof.MlDsa.AArch64.Sample.Rej4.mask σ (n+1) := by
  have er : VG.Proof.MlDsa.AArch64.Sample.Rej4.result σ n = if (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ n).length == 256 then (1 : BitVec 64) else 0 := by
    simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.result,beq_iff_eq]
  rw [er]
  simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.mask,List.range_succ,List.all_append,List.all_cons,List.all_nil,Bool.and_true]
  cases (List.range n).all (fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k).length == 256) <;>
    cases (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ n).length == 256 <;> rfl

structure Parsed (σ : State) (n : Nat) (s : State) : Prop where
  ready : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s
  mask : s.gpr .x27 = VG.Proof.MlDsa.AArch64.Sample.Rej4.mask σ n
  stored : ∀ k < n,Stored s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.L σ k)

theorem parsed_step {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {n : Nat} (hn : n < 4) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ n s) :
    WP isa (sample n) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ (n+1)) := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.sample_ok hp h.ready hn) fun t ⟨hr,_,hf,hs,hm⟩ => ⟨hr,?_,fun k hk => ?_⟩
  · rw [hm,h.mask,VG.Proof.MlDsa.AArch64.Sample.Rej4.mask_step]
  · by_cases he : k = n
    · subst k; exact hs
    · exact stored_frame hf (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.aP σ) (d := 1024*k) (e := 1024*n) (n := 1024) (k := 1024)
          (by omega) (by omega) (by omega)) (h.stored k (by omega)) (rnFold_length_le (by simp) _)

def r4K : Contract isa where
  pre := VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre
  post s t := (t.gpr .x0).setWidth 32 = (VG.Proof.MlDsa.AArch64.Sample.Rej4.mask s 4).setWidth 32 ∧
    ∀ k < 4,(VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length = 256 → Spec.MlDsa.PolyIs t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP s k) (VG.Proof.MlDsa.Sample.toPoly (VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k))
  pub s t := VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s = VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP t ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.aP s = VG.Proof.MlDsa.AArch64.Sample.Rej4.aP t ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.scr s = VG.Proof.MlDsa.AArch64.Sample.Rej4.scr t ∧ s.sp = t.sp ∧
    Spec.Sha3.bytesAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) 136 = Spec.Sha3.bytesAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP t) 136

theorem end_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ 4 s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.epi_ok hp h.ready.env) fun t ⟨hab,hm,h0,_,_⟩ => ⟨hab,?_,fun k hk he => ?_⟩
  · rw [h0,h.mask]
  · rw [hm]; exact stored_polyIs (h.stored k hk) he

theorem body_ok {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s) :
    WP isa (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi)))))) s
      fun t => abiPreserved σ t ∧ r4K.post σ t := by
  refine WP.seq (wp_movz fun t ht et => wp_nil ?_)
  have hr := h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
    ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  have h0 : VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ 0 t := ⟨hr,by rw [et]; rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  exact WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_step hp (by decide) h0) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_step hp (by decide) h1) fun _ h2 =>
      WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_step hp (by decide) h2) fun _ h3 =>
        WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_step hp (by decide) h3) fun _ h4 => VG.Proof.MlDsa.AArch64.Sample.Rej4.end_ok hp h4))))

theorem correct (sha3 : Bool) (σ : State) (hp : r4K.pre σ) :
    ∃ tr t,Exec isa (rejNTT4With sha3) σ tr t ∧ abiPreserved σ t ∧ r4K.post σ t := by
  unfold rejNTT4With
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.setup_ok he h0 h1) fun u hu => ?_
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.squeeze_ok sha3 hp hu) fun t ht => VG.Proof.MlDsa.AArch64.Sample.Rej4.body_ok hp ⟨ht.env,fun k hk j hj =>
    ht.out k hk j (by simpa using hj)⟩)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTBase`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relMem relTaint)
open VG.Proof.MlDsa.Sample (polyR coeffAddr G_length coeff_contains)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample (zeroPoly rnLoop retZ)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

/-- The four seeds are slices of the public 136-byte input. -/
theorem B_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : VG.Proof.MlDsa.AArch64.Sample.Rej4.B σ k = VG.Proof.MlDsa.AArch64.Sample.Rej4.B τ k := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.B Spec.MlDsa.seed4
  rw [← VG.Proof.MlKem.bytesAt_slice σ.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP σ) (show 34*k+34 ≤ 136 by omega),
    ← VG.Proof.MlKem.bytesAt_slice τ.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP τ) (show 34*k+34 ≤ 136 by omega),hq.2.2.2.2]

theorem X_pub {σ τ : State} (hq : r4K.pub σ τ) {k : Nat} (hk : k < 4) : VG.Proof.MlDsa.AArch64.Sample.Rej4.X σ k = VG.Proof.MlDsa.AArch64.Sample.Rej4.X τ k := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.X
  rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.B_pub hq hk]

structure ArgReady (σ : State) (k : Nat) (s : State) : Prop where
  ready : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s
  x25 : s.gpr .x25 = VG.Proof.MlDsa.AArch64.Sample.Rej4.at' σ (1008*k)
  x26 : s.gpr .x26 = VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k

structure ZeroReady (σ : State) (k : Nat) (s : State) : Prop extends VG.Proof.MlDsa.AArch64.Sample.Rej4.ArgReady σ k s where
  zero : ∀ i < 256,Spec.MlDsa.coeffAt s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) i = 0

theorem args_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s) :
    WP isa (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.ArgReady σ k) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.sampleArgs_ok h.env hk) fun _ ⟨ht,e25,e26⟩ =>
    ⟨h.polyStep hp hk (by rw [ht.mem]; exact Frame.refl _ _) ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),e25,e26⟩

theorem zero_ready {σ s : State} {k : Nat} (hk : k < 4) (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.ArgReady σ k s) :
    WP isa zeroPoly s (VG.Proof.MlDsa.AArch64.Sample.Rej4.ZeroReady σ k) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.zeroPoly_ok (VG.Proof.MlDsa.AArch64.Sample.Rej4.coeffs_in hp h.ready.env.wr hk) h.x26)
    fun _ ⟨ht,hz,hf⟩ => ⟨⟨h.ready.polyStep hp hk hf ht.rd ht.wr ht.sp
      (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)),
      (ht.get .x25).trans h.x25,(ht.get .x26).trans h.x26⟩,hz⟩

theorem zero_lpre {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {k : Nat} (hk : k < 4) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.ZeroReady σ k s) :
    VG.Proof.MlDsa.AArch64.Sample.RejNtt.LPre (VG.Proof.MlDsa.AArch64.Sample.Rej4.X σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k) s :=
  ⟨h.ready.out k hk,fun j hj => by
    unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
    rw [Offset.add_add]
    exact VG.Proof.MlDsa.AArch64.Sample.Rej4.in_scr_rd hp h.ready.env.rd h.ready.env.wr (by dsimp only [oBuf]; omega),
    VG.Proof.MlDsa.AArch64.Sample.Rej4.coeffs_in hp h.ready.env.wr hk,VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_poly hp hk hk,by
      rw [h.x25]
      unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.at' VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP
      rw [Offset.add_add]
      exact congrArg (fun d => VG.Proof.MlDsa.AArch64.Sample.Rej4.scr σ+BitVec.ofNat 64 d) (by dsimp only [oBuf]; omega),h.x26⟩

theorem loop_ready {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) {k : Nat} (hk : k < 4) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.ZeroReady σ k s) :
    WP isa rnLoop s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ) :=
  WP.mono (VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (VG.Proof.MlDsa.Sample.G_length _ _) (VG.Proof.MlDsa.AArch64.Sample.Rej4.zero_lpre hp hk h))
    fun _ ht => h.ready.polyStep hp hk ht.frame ht.keep.rd ht.keep.wr ht.keep.sp (fun r hr => ht.keep.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTLoop`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relMem byte_zero)
open VG.Proof.MlDsa.Sample (polyR coeff_contains G_length)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop)
open VG.Proof.MlKem.AArch64 (ptr_zero)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf)

def lrd (σ : State) (k : Nat) : List Region := [⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k,1008⟩]
def lwr (σ : State) (k : Nat) : List Region := [polyR (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k)]

theorem buf_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP σ k = VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP τ k := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
  rw [hq.2.2.1]

theorem poly_pub {σ τ : State} (hq : r4K.pub σ τ) (k : Nat) : VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP σ k = VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP τ k := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP
  rw [hq.2.1]

theorem loop_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.ZeroReady σ k)) rnLoop fun _ _ => True := by
  refine relMem (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.lrd σ k) (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.lwr σ k) [.x25,.x26]
    (fun σ τ _ _ hq => by simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.lrd,VG.Proof.MlDsa.AArch64.Sample.Rej4.lwr,VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_pub hq,VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_pub hq]; exact ⟨trivial,trivial⟩)
    (fun σ s hp h => ?_) (fun σ s hp h => ?_)
    (fun σ τ s t _ _ hq hs ht => ?_) (by taint_decide)
  · rw [h.ready.env.rd,h.ready.env.wr,hp.rd,hp.wr]
    refine ⟨Covers.of_sub (fun r hr => ?_),Covers.of_sub (fun r hr => ?_)⟩
    · simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.lrd,VG.Proof.MlDsa.AArch64.Sample.Rej4.lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR σ,by simp,VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf+1008*k,rfl,
          by dsimp only [oBuf,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR]; omega⟩
      · exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,by simp,1024*k,rfl,by dsimp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR,polyR]; omega⟩
    · rw [List.mem_singleton.mp hr]
      exact ⟨VG.Proof.MlDsa.AArch64.Sample.Rej4.aR σ,by simp,1024*k,rfl,by dsimp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR,polyR]; omega⟩
  · have h := VG.Proof.MlDsa.AArch64.Sample.Rej4.zero_lpre hp hk h
    obtain ⟨tr,u,he,_⟩ := VG.Proof.MlDsa.AArch64.Sample.RejNtt.loop_ok (VG.Proof.MlDsa.Sample.G_length _ _)
      (s₀ := s.withRegions (VG.Proof.MlDsa.AArch64.Sample.Rej4.lrd σ k) (VG.Proof.MlDsa.AArch64.Sample.Rej4.lwr σ k))
      ⟨h.buf,fun j hj => VG.Proof.MlKem.AArch64.in_rd (VG.Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        fun i hi => VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        h.disj,h.x25,h.x26⟩
    exact ⟨tr,u,he⟩
  · refine ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => ?_,fun x hx => ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.x25,ht.x25]
        unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.at'
        rw [hq.2.2.1]
      · rw [hs.x26,ht.x26,VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_pub hq]
    · obtain ⟨r,hr,hc⟩ := hx
      simp only [VG.Proof.MlDsa.AArch64.Sample.Rej4.lrd,VG.Proof.MlDsa.AArch64.Sample.Rej4.lwr,List.mem_append,List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · obtain ⟨j,hj,rfl⟩ := VG.Proof.MlKem.AArch64.Sample.at_off hc
        rw [hs.ready.out k hk j hj,VG.Proof.MlDsa.AArch64.Sample.Rej4.buf_pub hq,ht.ready.out k hk j hj]
        exact congrArg (fun b : List Byte => b.getD j 0) (VG.Proof.MlDsa.AArch64.Sample.Rej4.X_pub hq hk)
      · rw [byte_zero hs.zero hc,byte_zero ht.zero (by rw [← VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_pub hq]; exact hc)]
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4
materialize_code initCode := (.block (init++setup) : Prog isa)
materialize_code squeezeNeon := (.loop (squeezeStepWith false) (.nonzero .x .x28) : Prog isa)
materialize_code squeezeSha3 := (.loop (squeezeStepWith true) (.nonzero .x .x28) : Prog isa)
materialize_code rejNeon := rejNTT4With false
materialize_code rejSha3 := rejNTT4With true
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CT`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep relTaint vectorRelTaintStep)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi init setup squeezeStepWith rejNTT4With)
open VG.Impl.MlDsa.AArch64.Sample (rnLoop retZ zeroPoly)

theorem sample_ctFor {k : Nat} (hk : k < 4) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hcheck : (taint.check (Taint.ofRegs [.x19,.x21])
      (.block ([.addImm .x .x25 .x19 (1008*k),.addImm .x .x26 .x21 (1024*k)] : List Instr)) hint).isSome = true) :
    RelCT isa (Rel2 r4K.pre r4K.pub VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready) (sample k) fun _ _ => True := by
  unfold sample
  refine RelCT.seq (relTaintStep (J' := fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.ArgReady σ k) [.x19,.x21]
    (fun _ _ hp h => VG.Proof.MlDsa.AArch64.Sample.Rej4.args_ready hk hp h) (fun σ τ s t _ _ hq hs ht => ?_) hcheck) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    rcases mem2 hr with rfl | rfl
    · rw [hs.env.x19,ht.env.x19,hq.2.2.1]
    · rw [hs.env.x21,ht.env.x21,hq.2.1]
  refine RelCT.seq (relTaintStep (J' := fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.ZeroReady σ k) [.x26]
    (fun _ _ hp h => VG.Proof.MlDsa.AArch64.Sample.Rej4.zero_ready hk hp h) (fun σ τ s t _ _ hq hs ht =>
      ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
        rw [List.mem_singleton.mp hr,hs.x26,ht.x26,VG.Proof.MlDsa.AArch64.Sample.Rej4.poly_pub hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready) (fun _ _ hp h => VG.Proof.MlDsa.AArch64.Sample.Rej4.loop_ready hp hk h) (VG.Proof.MlDsa.AArch64.Sample.Rej4.loop_ct hk)) ?_
  exact relTaint [] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)

theorem sample_ct {k : Nat} (hk : k < 4) :
    RelCT isa (Rel2 r4K.pre r4K.pub VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready) (sample k) fun _ _ => True := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact VG.Proof.MlDsa.AArch64.Sample.Rej4.sample_ctFor (by decide) (by taint_decide)

theorem init_ct : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ s => s = σ))
    (.block (init++setup)) (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 0 0)) := by
  refine vectorRelTaintStep [.x0,.x1,.x2] (fun σ s hp hs => ?_)
    (fun _ _ _ _ _ _ hq hs ht => ?_) (by taint_decide)
  · subst s
    rw [WP.block_append_iff]
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.init_ok hp) fun _ ⟨he,h0,h1⟩ => VG.Proof.MlDsa.AArch64.Sample.Rej4.setup_ok he h0 h1
  · subst hs ht
    exact ⟨hq.2.2.2.1,fun r hr => by
      rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact hq.1
      · exact hq.2.1
      · exact hq.2.2.1⟩

theorem squeeze_ctFor (sha3 : Bool) {hint : VG.Taint.Hint VectorTaint.T}
    (hcheck : (VectorTaint.taint.check (VectorTaint.ofRegs [.x22,.x23,.x24,.x25,.x26,.x27,.x28])
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) hint).isSome = true) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready) := by
  refine vectorRelTaintStep (hc := hint) [.x22,.x23,.x24,.x25,.x26,.x27,.x28]
    (fun _ _ hp h => WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.squeeze_ok sha3 hp h) fun _ ht =>
      ⟨ht.env,fun k hk j hj => ht.out k hk j (by simpa using hj)⟩)
    (fun σ τ s t _ _ hq hs ht => ?_) ?_
  · refine ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hs.x22,ht.x22]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · rw [hs.x23,ht.x23]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.stateP VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · change s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 0) = t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 0)
      rw [hs.ptrs 0 (by decide),ht.ptrs 0 (by decide)]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · change s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 1) = t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 1)
      rw [hs.ptrs 1 (by decide),ht.ptrs 1 (by decide)]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · change s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 2) = t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 2)
      rw [hs.ptrs 2 (by decide),ht.ptrs 2 (by decide)]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · change s.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 3) = t.gpr (VG.Proof.MlDsa.AArch64.Sample.Rej4.bReg 3)
      rw [hs.ptrs 3 (by decide),ht.ptrs 3 (by decide)]; unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.bufAt VG.Proof.MlDsa.AArch64.Sample.Rej4.at'; rw [hq.2.2.1]
    · exact BitVec.eq_of_toNat_eq (hs.count.trans ht.count.symm)
  · exact hcheck
theorem squeeze_ct (sha3 : Bool) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Phase σ 0 0))
    (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) (Rel2 r4K.pre r4K.pub VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready) := by
  cases sha3 <;> exact VG.Proof.MlDsa.AArch64.Sample.Rej4.squeeze_ctFor _ (by taint_decide)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.CTTop`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample (Rel2 relStep relTaintStep vectorRelTaint)
open VG.Proof.MlKem.AArch64 (wp_movz wp_nil)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (sample epi rejNTT4With)

theorem start_parsed {σ s : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Rej4.Pre σ) (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready σ s) :
    WP isa (.block [.movz .x .x27 1 0]) s (VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ 0) := by
  refine wp_movz fun t ht et => wp_nil ⟨?_,?_,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  · exact h.polyStep hp (k := 0) (by decide) (by rw [ht.mem]; exact Frame.refl _ _)
      ht.rd ht.wr ht.sp (fun r hr => ht.get r (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
  · rw [et]; rfl

theorem parsed_ct {k : Nat} (hk : k < 4) : RelCT isa (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ k))
    (sample k) (Rel2 r4K.pre r4K.pub (fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ (k+1))) :=
  relStep (fun _ _ hp h => VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_step hp hk h)
    (RelCT.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.sample_ct hk) (fun _ _ ⟨σ,τ,hp,hp',hq,h,h'⟩ =>
      ⟨σ,τ,hp,hp',hq,h.ready,h'.ready⟩) (fun _ _ _ => trivial))

theorem body_ct : RelCT isa (Rel2 r4K.pre r4K.pub VG.Proof.MlDsa.AArch64.Sample.Rej4.Ready)
    (.seq (.block [.movz .x .x27 1 0])
      (.seq (sample 0) (.seq (sample 1) (.seq (sample 2) (.seq (sample 3) (.block epi))))))
    fun _ _ => True := by
  refine RelCT.seq (relTaintStep (J' := fun σ => VG.Proof.MlDsa.AArch64.Sample.Rej4.Parsed σ 0) []
    (fun _ _ hp h => VG.Proof.MlDsa.AArch64.Sample.Rej4.start_parsed hp h) (fun _ _ _ _ _ _ hq hs ht =>
      ⟨by rw [hs.env.sp,ht.env.sp,hq.2.2.2.1],by simp⟩) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_ct (by decide : 0 < 4)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_ct (by decide : 1 < 4)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_ct (by decide : 2 < 4)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.Rej4.parsed_ct (by decide : 3 < 4)) ?_
  exact vectorRelTaint [.x19] (fun _ _ _ _ _ _ hq hs ht =>
    ⟨by rw [hs.ready.env.sp,ht.ready.env.sp,hq.2.2.2.1],fun r hr => by
      rw [List.mem_singleton.mp hr,hs.ready.env.x19,ht.ready.env.x19,hq.2.2.1]⟩) (by taint_decide)

theorem ct (sha3 : Bool) : ConstantTime isa r4K.pre r4K.pub (rejNTT4With sha3) := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    (RelCT.mono (Q := fun _ _ => True) (P := Rel2 r4K.pre r4K.pub (fun σ s => s = σ)) ?_
      (fun s t h => ⟨s,t,h.1,h.2.1,h.2.2,rfl,rfl⟩) (fun _ _ _ => trivial))
  exact RelCT.seq VG.Proof.MlDsa.AArch64.Sample.Rej4.init_ct (RelCT.seq (VG.Proof.MlDsa.AArch64.Sample.Rej4.squeeze_ct sha3) VG.Proof.MlDsa.AArch64.Sample.Rej4.body_ct)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Verified`. -/
section

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none rej4Res)
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

def preProps (s : State) : Prop := s.rd = [VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s] ∧ s.wr = [VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s] ∧
  (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s) ∧ (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s) ∧ (VG.Proof.MlDsa.AArch64.Sample.Rej4.aR s).Disjoint (VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR s)

theorem r4_pre : ∀ s, (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s → r4K.pre s := by
  have h : ∀ s,(Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s → VG.Proof.MlDsa.AArch64.Sample.Rej4.preProps s := by
    sig_implies_pre [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,VG.Proof.MlDsa.AArch64.Sample.Rej4.preProps,
      VG.Proof.MlDsa.AArch64.Sample.Rej4.seedsR,VG.Proof.MlDsa.AArch64.Sample.Rej4.aR,VG.Proof.MlDsa.AArch64.Sample.Rej4.scrR,VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP,VG.Proof.MlDsa.AArch64.Sample.Rej4.aP,VG.Proof.MlDsa.AArch64.Sample.Rej4.scr,AArch64.abi,AArch64.argRegs]
  intro s hs
  obtain ⟨hr,hw,hsa,hss,has⟩ := h s hs
  exact ⟨hr,hw,hsa,hss,has⟩

theorem mask_cast (s : State) : (VG.Proof.MlDsa.AArch64.Sample.Rej4.mask s 4).setWidth 32 = rej4Res s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) := by
  unfold VG.Proof.MlDsa.AArch64.Sample.Rej4.mask rej4Res
  change (if (List.range 4).all (fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length == 256) then (1 : BitVec 64) else 0).setWidth 32 = _
  split <;> rfl

theorem r4_post {s t : State} (h : r4K.post s t) :
    let r := (t.gpr .x0).setWidth 32
    (r = 1 → ∀ k < 4,Spec.MlDsa.Reduced t.mem (Spec.MlDsa.poly4 (VG.Proof.MlDsa.AArch64.Sample.Rej4.aP s) k)) ∧
      ((r = 1 ∧ ∀ k < 4,∃ b : Spec.MlDsa.Bounds,Spec.MlDsa.rejNTTPoly b.rejNTT
          (Spec.MlDsa.seed4 s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) k) = some (Spec.MlDsa.polyAt t.mem (Spec.MlDsa.poly4 (VG.Proof.MlDsa.AArch64.Sample.Rej4.aP s) k))) ∨
        (r = 0 ∧ ∃ k < 4,Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Spec.MlDsa.seed4 s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) k) = none)) := by
  obtain ⟨hr,hp⟩ := h
  rw [VG.Proof.MlDsa.AArch64.Sample.Rej4.mask_cast] at hr
  intro r
  by_cases hall : ((List.range 4).all fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length == 256) = true
  · have hs : ∀ k < 4,(VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    change r = (if (List.range 4).all (fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length == 256) then 1 else 0) at hr
    rw [ite_eq_left hall] at hr
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1,.inl ⟨hr,fun k hk =>
      ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 },?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    change Spec.MlDsa.rejNTTPoly 1008 (VG.Proof.MlDsa.AArch64.Sample.Rej4.B s k) = some (Spec.MlDsa.polyAt t.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.polyP s k))
    rw [rejNTT_some (hs k hk),(hp k hk (hs k hk)).2]
  · change r = (if (List.range 4).all (fun k => (VG.Proof.MlDsa.AArch64.Sample.Rej4.L s k).length == 256) then 1 else 0) at hr
    rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),.inr ⟨hr,?_⟩⟩
    simp only [List.all_eq_true,List.mem_range,Classical.not_forall,beq_iff_eq] at hall
    obtain ⟨k,hk,hk'⟩ := hall
    exact ⟨k,hk,rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

def r4Sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000,136⟩]
  wr := [⟨0x2000,4096⟩,⟨0x4000,8192⟩]

theorem verified (sha3 : Bool) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With sha3)
    (Spec.MlDsa.rejNTT4Contract AArch64.abi) :=
  Verified.of_correct (VG.Proof.MlDsa.AArch64.Sample.Rej4.correct sha3) (VG.Proof.MlDsa.AArch64.Sample.Rej4.ct sha3)
    { pre := VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_pre
      post := by
        intro s t _ h
        sig_post [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs]
        exact VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_post h
      pub := by
        intro s t _ _ h
        sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs] at h
        obtain ⟨hsp,hb,h0,h1,h2⟩ := h
        exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by
        sig_implies_sat [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs]
          [r4Sat] using VG.Proof.MlDsa.AArch64.Sample.Rej4.r4Sat }

theorem ret {sha3 : Bool} {s t : State} {tr : List Leak}
    (hp : (Spec.MlDsa.rejNTT4Contract AArch64.abi).pre s)
    (he : Exec isa (Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With sha3) s tr t) :
    (t.gpr .x0).setWidth 32 = rej4Res s.mem (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedP s) := by
  obtain ⟨_,_,he',_,hq⟩ := VG.Proof.MlDsa.AArch64.Sample.Rej4.correct sha3 s (VG.Proof.MlDsa.AArch64.Sample.Rej4.r4_pre s hp)
  obtain ⟨_,rfl⟩ := Exec.det he he'
  exact hq.1.trans (VG.Proof.MlDsa.AArch64.Sample.Rej4.mask_cast s)
end VG.Proof.MlDsa.AArch64.Sample.Rej4

end
