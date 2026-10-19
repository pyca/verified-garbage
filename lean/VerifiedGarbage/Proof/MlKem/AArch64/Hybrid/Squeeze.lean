module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Step
public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall

/-!
# The three main squeezes of a hashing pair

`squeeze3_ok`: the three `step3`s of pair `i` squeeze three SHAKE128 blocks
of each matrix stream, as `Paired.squeeze` does, and absorb blocks `3i`,
`3i + 1` and `3i + 2` of `pad(ek)` into the third state. `start3_ok`: with
the pair's initialization before them (as `Paired.start_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt streamR block_sub)
open VG.Proof.Sha3 (iterF iterF_succ)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

/-- What a hashing pair's squeezes may write. -/
def squeezeWrites (p st sp : Addr) : List Region :=
  [pairR p, streamR (p + 400), streamR (p + 904), callR (p + 1536), stR st, frame sp]

/-- What a hashing pair's start may write. -/
def startWrites (p st sp : Addr) : List Region := [⟨p, 2048⟩, stR st, frame sp]

/-- After `k` of the three main squeezes. -/
structure SInv3 (L : Impl.MlKem.AArch64.KemLay) (initial : State) (p e st : Addr) (E : List Byte)
    (A B : Spec.Sha3.State) (i k : Nat) (s : State) : Prop where
  keep : Keep stepRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19 = p
  pa : s.gpr .x20 = blockAt (p + 400) k
  pb : s.gpr .x21 = blockAt (p + 904) k
  frame : Frame (squeezeWrites p st initial.sp) initial.mem s.mem
  oa : Blocks s.mem (p + 400) k A
  ob : Blocks s.mem (p + 904) k B
  hash : stateAt s.mem st = hstate E (3 * i + k)
  ek : bytesAt s.mem e L.ekLen = E

/-- What the pair's memory is. -/
structure SqLay (L : Impl.MlKem.AArch64.KemLay) (p e st : Addr) (s : State) : Prop where
  scratch : Covers [⟨p, 2048⟩] s.wr
  state : Covers [stR st] s.wr
  ekr : Covers [⟨e, L.ekLen⟩] (s.rd ++ s.wr)
  sp : 128 ≤ s.sp.toNat
  dSP : (stR st).Disjoint ⟨p, 2048⟩
  dSE : (stR st).Disjoint ⟨e, L.ekLen⟩
  dEP : (Region.mk e L.ekLen).Disjoint ⟨p, 2048⟩
  fP : (frame s.sp).Disjoint ⟨p, 2048⟩
  fS : (frame s.sp).Disjoint (stR st)
  fE : (frame s.sp).Disjoint ⟨e, L.ekLen⟩

theorem SqLay.frame {L : Impl.MlKem.AArch64.KemLay} {p e st : Addr} {s t : State} (h : SqLay L p e st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) : SqLay L p e st t := by
  refine ⟨?_, ?_, ?_, ?_, h.dSP, h.dSE, h.dEP, ?_, ?_, ?_⟩ <;> simp only [hr, hw, hsp]
  exacts [h.scratch, h.state, h.ekr, h.sp, h.fP, h.fS, h.fE]

theorem in_scratch {X : List Region} {p : Addr} (h : Covers [⟨p, 2048⟩] X) {o n : Nat} (ho : o + n ≤ 2048) :
    InRegions X (p + BitVec.ofNat 64 o) n := covers_in h ho (by decide)

theorem cov_scratch {X : List Region} {p : Addr} (h : Covers [⟨p, 2048⟩] X) {o n : Nat} (ho : o + n ≤ 2048) :
    Covers [⟨p + BitVec.ofNat 64 o, n⟩] X :=
  (Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, o, rfl, ho⟩).trans h

theorem blockAt_eq (p : Addr) (o k : Nat) :
    blockAt (p + BitVec.ofNat 64 o) k = p + BitVec.ofNat 64 (o + 168 * k) := by
  simp only [blockAt]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem outAddr_eq (p : Addr) (o i : Nat) :
    outAddr (p + BitVec.ofNat 64 o) i = p + BitVec.ofNat 64 (o + 8 * i) := by
  simp only [outAddr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem SqLay.stepLay {L : Impl.MlKem.AArch64.KemLay} {p e st : Addr} {s : State} (h : SqLay L p e st s)
    {k : Nat} (hk : k < 3) :
    StepLay L p (blockAt (p + 400) k) (blockAt (p + 904) k) e st s := by
  have ea : blockAt (p + 400) k = p + BitVec.ofNat 64 (400 + 168 * k) := blockAt_eq p 400 k
  have eb : blockAt (p + 904) k = p + BitVec.ofNat 64 (904 + 168 * k) := blockAt_eq p 904 k
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have subP : Region.Sub (pairR p) ⟨p, 2048⟩ := Region.sub_prefix (by decide : 400 ≤ 2048)
  rw [ea, eb]
  refine ⟨?_, h.ekr, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h.sp,
    Offset.disjoint p (by omega) (by omega) (by omega),
    Offset.base_disjoint p (by omega) (by omega), Offset.base_disjoint p (by omega) (by omega),
    (h.dSP.sub_right subP).symm, Offset.base_disjoint p (e := 1536) (n := 136) (by decide) (by decide),
    h.dSP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.dSP.sub_right (sub (by omega)),
    h.dSP.sub_right (sub (by omega)),
    h.dSE, h.fP.sub_right subP, h.fS, h.fP.sub_right (sub (o := 1536) (n := 136) (by decide))⟩
  · refine Covers.cons ?_ (Covers.cons (covers_mono h.state (by simp)) (Covers.cons ?_ Covers.nil))
    · simpa only [BitVec.add_zero, pairR] using cov_scratch (o := 0) (n := 400) h.scratch (by decide)
    · exact cov_scratch (o := 1536) (n := 136) h.scratch (by decide)
  · exact Covers.right (cov_scratch h.scratch (o := 16 * i) (n := 16) (by omega)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega)
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega)

theorem extend_blocks3 {m m' : Mem} {p a b st sp : Addr} {A : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    (old : Blocks m a k A) (new : Rate21 m' (blockAt a k) (iterF (k + 1) A))
    (hf : Frame (step3Writes p (blockAt a k) (blockAt b k) st sp) m m')
    (hpa : (pairR p).Disjoint (streamR a)) (hab : (streamR a).Disjoint (streamR b))
    (hwa : (callR (p + 1536)).Disjoint (streamR a)) (hsa : (stR st).Disjoint (streamR a))
    (hfa : (frame sp).Disjoint (streamR a)) : Blocks m' a (k + 1) A := by
  intro j hj
  by_cases he : j = k
  · subst j; exact new
  · have hjk : j < k := by omega
    intro i hi
    have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hf.readW hc (by
        intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hpa.sub_right (block_sub a (by omega))).symm
        · exact Offset.disjoint a (Or.inl (by omega)) (by omega) (by omega)
        · exact (hab.sub_left (block_sub a (by omega))).sub_right (block_sub b hk)
        · exact (hwa.sub_right (block_sub a (by omega))).symm
        · exact (hsa.sub_right (block_sub a (by omega))).symm
        · exact (hfa.sub_right (block_sub a (by omega))).symm) (by decide)]
    exact old j hjk i hi

/-- One of the three main squeezes. -/
theorem sstep_ok (L : Impl.MlKem.AArch64.KemLay) {initial s : State} {p e st : Addr} {E : List Byte}
    {A B : Spec.Sha3.State} {i k : Nat} (hk : k < 3)
    (hb : 136 * (3 * i + k) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hl : SqLay L p e st initial) (h28 : initial.gpr .x28 = st) (h25 : initial.gpr .x25 = e)
    (h : SInv3 L initial p e st E A B i k s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.step3 L (3 * i + k)) s (SInv3 L initial p e st E A B i (k + 1)) := by
  have hls : SqLay L p e st s := hl.frame h.keep.rd h.keep.wr h.keep.sp
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  refine WP.mono (step3_ok L h.ptr h.pa h.pb (by rw [h.keep.get .x25]; exact h25)
    (by rw [h.keep.get .x28]; exact h28) hb h8 hlim h.ek h.hash h.pair (hls.stepLay hk))
    fun t ⟨kt, ft, pt, at', bt, st', t20, t21⟩ => ?_
  have fsub : Frame (squeezeWrites p st initial.sp) s.mem t.mem := by
    rw [h.keep.sp] at ft
    refine ft.sub fun r hr => ?_
    simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨pairR p, by simp [squeezeWrites], fun _ h => h⟩
    · exact ⟨streamR (p + 400), by simp [squeezeWrites], block_sub _ hk⟩
    · exact ⟨streamR (p + 904), by simp [squeezeWrites], block_sub _ hk⟩
    · exact ⟨callR (p + 1536), by simp [squeezeWrites], fun _ h => h⟩
    · exact ⟨stR st, by simp [squeezeWrites], fun _ h => h⟩
    · exact ⟨frame initial.sp, by simp [squeezeWrites], fun _ h => h⟩
  have dP : ∀ {o : Nat}, o + 504 ≤ 2048 → (frame initial.sp).Disjoint (streamR (p + BitVec.ofNat 64 o)) :=
    fun h => hl.fP.sub_right (sub h)
  rw [h.keep.sp] at ft
  refine ⟨(h.keep.trans kt).mono (fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h), ?_, (kt.get .x19).trans h.ptr, ?_, ?_,
    h.frame.trans fsub, ?_, ?_, ?_, ?_⟩
  · simpa only [iterF_succ] using pt
  · rw [t20]; show (p + 400 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 400 + BitVec.ofNat 64 (168 * (k + 1))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
  · rw [t21]; show (p + 904 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 904 + BitVec.ofNat 64 (168 * (k + 1))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
  · exact extend_blocks3 hk h.oa (by simpa only [iterF_succ] using at') ft
      (Offset.base_disjoint p (by decide) (by decide)) (Offset.disjoint p (by decide) (by decide) (by decide))
      (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
      (dP (by decide))
  · refine extend_blocks3 hk h.ob (by simpa only [iterF_succ] using bt) (ft.mono ?_)
      (Offset.base_disjoint p (by decide) (by decide))
      (Offset.disjoint p (d := 400) (n := 504) (e := 904) (k := 504) (by decide) (by decide) (by decide)).symm
      (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
      (dP (by decide))
    intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp [h]
  · rw [st']; rfl
  · rw [VG.Proof.MlKem.bytesAt_frame ft (fun r hr => ?_) (by omega)]
    · exact h.ek
    simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    have dEP := hl.dEP
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact dEP.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048))
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 400) k, 168⟩
      rw [blockAt_eq]; exact dEP.sub_right (sub (by omega))
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 904) k, 168⟩
      rw [blockAt_eq]; exact dEP.sub_right (sub (by omega))
    · exact dEP.sub_right (sub (by decide))
    · exact hl.dSE.symm
    · exact hl.fE.symm

/-- **The three main squeezes** of pair `i`. -/
theorem squeeze3_ok (L : Impl.MlKem.AArch64.KemLay) {s : State} {p e st : Addr} {E : List Byte}
    {A B : Spec.Sha3.State} {i : Nat}
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hl : SqLay L p e st s) (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400)
    (h21 : s.gpr .x21 = p + 904) (h25 : s.gpr .x25 = e) (h28 : s.gpr .x28 = st)
    (pair : PairAt s.mem p A B) (hash : stateAt s.mem st = hstate E (3 * i))
    (hE : bytesAt s.mem e L.ekLen = E) :
    WP isa (Impl.MlKem.AArch64.Hybrid.squeeze3 L i) s (SInv3 L s p e st E A B i 3) := by
  have h0 : SInv3 L s p e st E A B i 0 s :=
    ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
      by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _), hash, hE⟩
  unfold Impl.MlKem.AArch64.Hybrid.squeeze3
  refine WP.seq (WP.mono (sstep_ok L (k := 0) (by decide) (by omega) h8 hlim hl h28 h25 h0) fun t ht => ?_)
  refine WP.seq (WP.mono (sstep_ok L (k := 1) (by decide) (by omega) h8 hlim hl h28 h25 ht) fun u hu => ?_)
  exact sstep_ok L (k := 2) (by decide) hb h8 hlim hl h28 h25 hu

def startRegs3 : List Reg := Paired.initRegs ++ stepRegs

/-- **A hashing pair's initialization and main squeezes** (as `Paired.start_ok`). -/
theorem start3_ok (L : Impl.MlKem.AArch64.KemLay) {s : State} {p seed e st : Addr} {E : List Byte}
    {sb ss a b i : Nat}
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (hl : SqLay L p e st s) (h25 : s.gpr .x25 = e) (h28 : s.gpr .x28 = st)
    (hb : 136 * (3 * i + 2) < L.ekLen) (h8 : L.ekLen % 8 = 0) (hlim : L.ekLen ≤ 4096)
    (hash : stateAt s.mem st = hstate E (3 * i)) (hE : bytesAt s.mem e L.ekLen = E) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k)) (Impl.MlKem.AArch64.Hybrid.squeeze3 L i)) s
      fun t =>
      Keep startRegs3 s t ∧ Frame (startWrites p st s.sp) s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19 = p ∧
      PairAt t.mem p (iterF 3 (Paired.seedState s.mem seed a L.k)) (iterF 3 (Paired.seedState s.mem seed b L.k)) ∧
      Blocks t.mem (p + 400) 3 (Paired.seedState s.mem seed a L.k) ∧
      Blocks t.mem (p + 904) 3 (Paired.seedState s.mem seed b L.k) ∧
      stateAt t.mem st = hstate E (3 * i + 3) ∧ bytesAt t.mem e L.ekLen = E := by
  have hc := hl.scratch
  have iw {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hc h (by decide)
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  refine WP.seq (WP.mono (Paired.init_ok hss hsb h8b hp ha hin
    (fun j hj => iw (by omega)) (fun j hj => iw (by omega))
    (hsep.sub_right (Offset.sub_base p (by decide)))
    (hsep.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku, fu, sv, h19, h20, h21, h22, pair⟩ => ?_)
  have fi : Frame [⟨p, 2048⟩] s.mem u.mem := fu.sub (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨p, 2048⟩, by simp, Offset.sub_base p (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩)
  have hsu : stateAt u.mem st = hstate E (3 * i) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fi (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dSP), hash]
  have heu : bytesAt u.mem e L.ekLen = E := by
    rw [VG.Proof.MlKem.bytesAt_frame fi (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hl.dEP) (by omega), hE]
  refine WP.mono (squeeze3_ok L hb h8 hlim (hl.frame ku.rd ku.wr ku.sp) h19 h20 h21
    (by rw [ku.get .x25]; exact h25) (by rw [ku.get .x28]; exact h28) pair hsu heu) fun t ht => ?_
  refine ⟨ku.trans ht.keep, ?_, ?_, ht.ptr, ht.pair, ht.oa, ht.ob, ht.hash, ht.ek⟩
  · have ft := ht.frame
    rw [ku.sp] at ft
    refine (fi.mono (by simp [startWrites])).trans (ft.sub fun r hr => ?_)
    simp only [squeezeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], Region.sub_prefix (by decide : 400 ≤ 2048)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 400) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 904) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWrites], sub (o := 1536) (n := 136) (by decide)⟩
    · exact ⟨stR st, by simp [startWrites], fun _ h => h⟩
    · exact ⟨frame s.sp, by simp [startWrites], fun _ h => h⟩
  · apply sv.frame ht.frame
    intro r hr; simp only [squeezeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact (hl.dSP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · rw [ku.sp]; exact (hl.fP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm

end VG.Proof.MlKem.AArch64.Hybrid
