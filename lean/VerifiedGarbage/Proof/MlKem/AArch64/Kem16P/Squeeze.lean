module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Slot
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall

/-!
# The three main squeezes of a pair computing PRF outputs

As `Hybrid/Squeeze.lean`, with `Kem16P.stepP` for `Hybrid.stepM`: the
first `m` main squeezes compute `PRF₂(r, N₀ + k)` in the third state
(`slotPrf_ok`) into the buffers from `B₀`, 168 bytes apart (`PrfBufs`), `r` at
`R`. `startP_ok`: with the pair's initialization before them.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt streamR block_sub)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Proof.MlKem.AArch64.Hybrid (stepRegs step3Writes frame squeezeWrites startWrites
  blockAt_eq outAddr_eq in_scratch cov_scratch extend_blocks3 startRegs3)
open VG.Proof.Sha3 (iterF iterF_succ)
open VG.Spec.Sha3 (stateAt bytesAt keccakF)

/-- The three buffers of a pair's PRF outputs. -/
def bufR (B₀ : Addr) : Region := ⟨B₀, 504⟩

/-- Buffer `k` from `B₀`. -/
abbrev bufAt (B₀ : Addr) (k : Nat) : Addr := B₀ + BitVec.ofNat 64 (168 * k)

/-- The first `n` PRF outputs from `N₀`, `r` at `R` in `mR`, in their buffers from `B₀`. -/
def PrfBufs (m : Mem) (B₀ : Addr) (mR : Mem) (R : Addr) (N₀ n : Nat) : Prop :=
  ∀ k < n, Rate128 m (bufAt B₀ k) (keccakF (Noise.seedState mR R (N₀ + k)))

theorem PrfBufs.frame {m m' mR : Mem} {B₀ R : Addr} {N₀ n : Nat} (h : PrfBufs m B₀ mR R N₀ n)
    (hn : n ≤ 3) {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (bufR B₀).Disjoint r) :
    PrfBufs m' B₀ mR R N₀ n := fun k hk i hi => by
  have hc : (bufR B₀).Contains (outAddr (bufAt B₀ k) i) 8 := by
    show (bufR B₀).Contains (B₀ + BitVec.ofNat 64 (168 * k) + BitVec.ofNat 64 (8 * i)) 8
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base B₀ (by omega) (by omega)
  rw [hf.readW hc hd (by decide)]
  exact h k hk i hi

/-- What a PRF pair's squeezes may write. -/
def squeezeWritesP (p st sp B₀ : Addr) : List Region := squeezeWrites p st sp ++ [bufR B₀]

/-- What a PRF pair's start may write. -/
def startWritesP (p st sp B₀ : Addr) : List Region := startWrites p st sp ++ [bufR B₀]

/-- What the pair's memory is. -/
structure SqLayP (p st R B₀ : Addr) (s : State) : Prop where
  scratch : Covers [⟨p, 2048⟩] s.wr
  state : Covers [stR st] s.wr
  sp : 128 ≤ s.sp.toNat
  dSP : (stR st).Disjoint ⟨p, 2048⟩
  fP : (frame s.sp).Disjoint ⟨p, 2048⟩
  fS : (frame s.sp).Disjoint (stR st)
  rin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)
  dSR : (stR st).Disjoint ⟨R, 32⟩
  dPR : (Region.mk p 2048).Disjoint ⟨R, 32⟩
  fR : (frame s.sp).Disjoint ⟨R, 32⟩
  bout : Covers [bufR B₀] s.wr
  dSF : (stR st).Disjoint (bufR B₀)
  dPF : (Region.mk p 2048).Disjoint (bufR B₀)
  fF : (frame s.sp).Disjoint (bufR B₀)
  dRF : (Region.mk R 32).Disjoint (bufR B₀)

theorem SqLayP.frame {p st R B₀ : Addr} {s t : State} (h : SqLayP p st R B₀ s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp) : SqLayP p st R B₀ t := by
  refine ⟨?_, ?_, ?_, h.dSP, ?_, ?_, ?_, h.dSR, h.dPR, ?_, ?_, h.dSF, h.dPF, ?_, h.dRF⟩ <;>
    simp only [hr, hw, hsp]
  exacts [h.scratch, h.state, h.sp, h.fP, h.fS, h.rin, h.fR, h.bout, h.fF]

theorem buf_sub (B₀ : Addr) {k : Nat} (hk : k < 3) : Region.Sub (rateR (bufAt B₀ k)) (bufR B₀) :=
  Offset.sub_base B₀ (by omega)

theorem SqLayP.slotLay {p st R B₀ : Addr} {s : State} (h : SqLayP p st R B₀ s) {k : Nat} (hk : k < 3) :
    SlotLay p (blockAt (p + 400) k) (blockAt (p + 904) k) st R (bufAt B₀ k) s := by
  have ea : blockAt (p + 400) k = p + BitVec.ofNat 64 (400 + 168 * k) := blockAt_eq p 400 k
  have eb : blockAt (p + 904) k = p + BitVec.ofNat 64 (904 + 168 * k) := blockAt_eq p 904 k
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have subP : Region.Sub (pairR p) ⟨p, 2048⟩ := Region.sub_prefix (by decide : 400 ≤ 2048)
  have bs := buf_sub B₀ hk
  rw [ea, eb]
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, h.sp,
    Offset.disjoint p (by omega) (by omega) (by omega),
    Offset.base_disjoint p (by omega) (by omega), Offset.base_disjoint p (by omega) (by omega),
    (h.dSP.sub_right subP).symm, Offset.base_disjoint p (e := 1536) (n := 136) (by decide) (by decide),
    h.dSP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.dSP.sub_right (sub (by omega)),
    h.dSP.sub_right (sub (by omega)), h.fP.sub_right subP, h.fS,
    h.fP.sub_right (sub (o := 1536) (n := 136) (by decide)), h.rin, h.dSR,
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, 168 * k, rfl, by simp only [rateR, bufR]; omega⟩).trans h.bout,
    h.dSF.sub_right bs, (h.dPF.sub_left (sub (by omega))).sub_right bs,
    (h.dPF.sub_left (sub (by omega))).sub_right bs, (h.dPF.sub_left subP).sub_right bs⟩
  · refine Covers.cons ?_ (Covers.cons (Hybrid.covers_mono h.state (by simp)) (Covers.cons ?_ Covers.nil))
    · simpa only [BitVec.add_zero, pairR] using cov_scratch (o := 0) (n := 400) h.scratch (by decide)
    · exact cov_scratch (o := 1536) (n := 136) h.scratch (by decide)
  · exact Covers.right (cov_scratch h.scratch (o := 16 * i) (n := 16) (by omega)) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega)
  · rw [outAddr_eq]; exact in_scratch h.scratch (by omega)

theorem rate128_frame {m m' : Mem} {p : Addr} {A : Spec.Sha3.State} {rs : List Region}
    (h : Rate128 m p A) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (rateR p).Disjoint r) : Rate128 m' p A :=
  fun i hi => by
    show m'.readW (p + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [hf.readW (r := rateR p) (Offset.contains_base p (by omega) (by omega)) hd (by decide)]
    exact h i hi

theorem seedState_frame {m m' : Mem} {R : Addr} {N : Nat} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (Region.mk R 32).Disjoint r) : Noise.seedState m' R N = Noise.seedState m R N := by
  apply Vector.ext; intro i hi
  simp only [Noise.seedState, Vector.getElem_ofFn]
  split
  · rw [hf.readW (r := ⟨R, 32⟩) (Offset.contains_base R (by omega) (by omega)) hd (by decide)]
  · rfl

/-- `Hybrid.extend_blocks3`, with the writes `Bs` too. -/
theorem extend_blocksP {m m' : Mem} {p a b st sp : Addr} {A : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    {Bs : List Region} (old : Blocks m a k A) (new : Rate21 m' (blockAt a k) (iterF (k + 1) A))
    (hf : Frame (step3Writes p (blockAt a k) (blockAt b k) st sp ++ Bs) m m')
    (hpa : (pairR p).Disjoint (streamR a)) (hab : (streamR a).Disjoint (streamR b))
    (hwa : (callR (p + 1536)).Disjoint (streamR a)) (hsa : (stR st).Disjoint (streamR a))
    (hfa : (frame sp).Disjoint (streamR a)) (hBa : ∀ r ∈ Bs, (streamR a).Disjoint r) :
    Blocks m' a (k + 1) A := by
  intro j hj
  by_cases he : j = k
  · subst j; exact new
  · have hjk : j < k := by omega
    intro i hi
    have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
      Offset.contains_base _ (by omega) (by omega)
    rw [hf.readW hc (by
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
          · exact (hpa.sub_right (block_sub a (by omega))).symm
          · exact Offset.disjoint a (Or.inl (by omega)) (by omega) (by omega)
          · exact (hab.sub_left (block_sub a (by omega))).sub_right (block_sub b hk)
          · exact (hwa.sub_right (block_sub a (by omega))).symm
          · exact (hsa.sub_right (block_sub a (by omega))).symm
          · exact (hfa.sub_right (block_sub a (by omega))).symm
        · exact (hBa r hr).sub_left (block_sub a (by omega))) (by decide)]
    exact old j hjk i hi

/-- After `k` of the three main squeezes, the first `m` computing PRF outputs from `N₀`. -/
structure SInvP (initial : State) (p st R B₀ : Addr) (A B : Spec.Sha3.State) (N₀ m k : Nat) (s : State) : Prop where
  keep : Keep stepRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19 = p
  pa : s.gpr .x20 = blockAt (p + 400) k
  pb : s.gpr .x21 = blockAt (p + 904) k
  frame : Frame (squeezeWritesP p st initial.sp B₀) initial.mem s.mem
  oa : Blocks s.mem (p + 400) k A
  ob : Blocks s.mem (p + 904) k B
  prf : PrfBufs s.mem B₀ initial.mem R N₀ (min k m)

/-- A main squeeze computing no PRF output. -/
theorem plainP_ok {s : State} {p st R B₀ : Addr} {A B : Spec.Sha3.State} {k : Nat} (hk : k < 3)
    (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = blockAt (p + 400) k) (h21 : s.gpr .x21 = blockAt (p + 904) k)
    (pair : PairAt s.mem p A B) (hl : SqLayP p st R B₀ s) :
    WP isa Impl.MlKem.AArch64.Hybrid.plainStep s fun t =>
      Keep stepRegs s t ∧
      Frame (step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st s.sp) s.mem t.mem ∧
      PairAt t.mem p (keccakF A) (keccakF B) ∧
      Rate21 t.mem (blockAt (p + 400) k) (keccakF A) ∧ Rate21 t.mem (blockAt (p + 904) k) (keccakF B) ∧
      t.gpr .x20 = blockAt (p + 400) k + 168 ∧ t.gpr .x21 = blockAt (p + 904) k + 168 := by
  have sl := hl.slotLay hk
  have hc := Paired.squeezeBlock_ok (rp := .x19) (ra := .x20) (rb := .x21) h19 h20 h21 (by rw [h19]; rfl)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pair sl.hin sl.hwa sl.hwb sl.dAB sl.dPA sl.dPB sl.dPC
    (Hybrid.covers_mono sl.cov (by simp))
  unfold Impl.MlKem.AArch64.Hybrid.plainStep Impl.MlKem.AArch64.Hybrid.squeezeTail
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hc) fun u hu => ?_
  rw [WP.block_append_iff]
  refine WP.mono hu fun v ⟨kv, pv, av, bv, fv, vv⟩ => ?_
  refine wp_addImm (by decide) fun v1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  have hv : Keep Paired.blockRegs s v := ⟨kv.gpr, kv.rd, kv.wr, kv.sp, vv⟩
  have ot : Only [.x20, .x21] v t := (h1.trans h2).mono (by simp)
  have hm : t.mem = v.mem := ot.mem
  refine ⟨(hv.trans ot.keep).mono (by simp [stepRegs, Hybrid.clobbered, Paired.blockRegs]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact fv.mono (by simp [step3Writes])
  · rw [hm]; exact pv
  · rw [hm]; exact av
  · rw [hm]; exact bv
  · rw [h2.get .x20 (by decide), e1, kv.gpr .x20 (by decide), h20]; rfl
  · rw [e2, h1.get .x21 (by decide), kv.gpr .x21 (by decide), h21]; rfl

/-- One of the three main squeezes. -/
theorem pstep_ok (L : Impl.MlKem.AArch64.KemLay) {initial s : State} {p st R B₀ : Addr}
    {A B : Spec.Sha3.State} {N₀ m k : Nat} (hk : k < 3) (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hl : SqLayP p st R B₀ initial) (h28 : initial.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (h : SInvP initial p st R B₀ A B N₀ m k s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m k) s (SInvP initial p st R B₀ A B N₀ m (k + 1)) := by
  have hls : SqLayP p st R B₀ s := hl.frame h.keep.rd h.keep.wr h.keep.sp
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have bs := buf_sub B₀ hk
  have dBW : ∀ r ∈ step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st initial.sp,
      (bufR B₀).Disjoint r := by
    intro r hr; simp only [step3Writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hl.dPF.sub_left (Region.sub_prefix (by decide : 400 ≤ 2048))).symm
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 400) k, 168⟩
      rw [blockAt_eq]; exact (hl.dPF.sub_left (sub (by omega))).symm
    · show Region.Disjoint _ ⟨blockAt (p + BitVec.ofNat 64 904) k, 168⟩
      rw [blockAt_eq]; exact (hl.dPF.sub_left (sub (by omega))).symm
    · exact (hl.dPF.sub_left (sub (o := 1536) (n := 136) (by decide))).symm
    · exact hl.dSF.symm
    · exact hl.fF.symm
  have next : ∀ {t : State} (Bs : List Region), (∀ r ∈ Bs, r = rateR (bufAt B₀ k)) →
      Keep stepRegs s t → Frame (step3Writes p (blockAt (p + 400) k)
      (blockAt (p + 904) k) st s.sp ++ Bs) s.mem t.mem →
      PairAt t.mem p (keccakF (iterF k A)) (keccakF (iterF k B)) →
      Rate21 t.mem (blockAt (p + 400) k) (keccakF (iterF k A)) →
      Rate21 t.mem (blockAt (p + 904) k) (keccakF (iterF k B)) →
      t.gpr .x20 = blockAt (p + 400) k + 168 → t.gpr .x21 = blockAt (p + 904) k + 168 →
      (k < m → Rate128 t.mem (bufAt B₀ k) (keccakF (Noise.seedState initial.mem R (N₀ + k)))) →
      SInvP initial p st R B₀ A B N₀ m (k + 1) t := by
    intro t Bs hBs kt ft pt at' bt t20 t21 rt
    rw [h.keep.sp] at ft
    have ft3 : Frame (step3Writes p (blockAt (p + 400) k) (blockAt (p + 904) k) st initial.sp ++ [bufR B₀])
        s.mem t.mem := ft.sub fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨bufR B₀, by simp, by rw [hBs r hr]; exact bs⟩
    have fsub : Frame (squeezeWritesP p st initial.sp B₀) s.mem t.mem := by
      refine ft3.sub fun r hr => ?_
      simp only [step3Writes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      · exact ⟨pairR p, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨streamR (p + 400), by simp [squeezeWritesP, squeezeWrites], block_sub _ hk⟩
      · exact ⟨streamR (p + 904), by simp [squeezeWritesP, squeezeWrites], block_sub _ hk⟩
      · exact ⟨callR (p + 1536), by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨stR st, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨frame initial.sp, by simp [squeezeWritesP, squeezeWrites], fun _ h => h⟩
      · exact ⟨bufR B₀, by simp [squeezeWritesP], fun _ h => h⟩
    have dP : ∀ {o : Nat}, o + 504 ≤ 2048 → (frame initial.sp).Disjoint (streamR (p + BitVec.ofNat 64 o)) :=
      fun h => hl.fP.sub_right (sub h)
    have hBs' : ∀ {o : Nat}, o + 504 ≤ 2048 → ∀ r ∈ Bs, (streamR (p + BitVec.ofNat 64 o)).Disjoint r :=
      fun ho r hr => by rw [hBs r hr]; exact (hl.dPF.sub_left (sub ho)).sub_right bs
    refine ⟨(h.keep.trans kt).mono (fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h), ?_,
      (kt.get .x19).trans h.ptr, ?_, ?_, h.frame.trans fsub, ?_, ?_, fun j hj => ?_⟩
    · simpa only [iterF_succ] using pt
    · rw [t20]; show (p + 400 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 400 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
    · rw [t21]; show (p + 904 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 904 + BitVec.ofNat 64 (168 * (k + 1))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
    · exact extend_blocksP hk h.oa (by simpa only [iterF_succ] using at') ft
        (Offset.base_disjoint p (by decide) (by decide)) (Offset.disjoint p (by decide) (by decide) (by decide))
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide)) (hBs' (by decide))
    · refine extend_blocksP hk h.ob (by simpa only [iterF_succ] using bt) (ft.mono ?_)
        (Offset.base_disjoint p (by decide) (by decide))
        (Offset.disjoint p (d := 400) (n := 504) (e := 904) (k := 504) (by decide) (by decide) (by decide)).symm
        (Offset.disjoint p (by decide) (by decide) (by decide)) (hl.dSP.sub_right (sub (by decide)))
        (dP (by decide)) (hBs' (by decide))
      intro r hr; simp only [step3Writes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h | h | h | h) | h <;> simp [h]
    · by_cases hjk : j < min k m
      · refine rate128_frame (h.prf j hjk) ft fun r hr => ?_
        have hj3 : j < 3 := by omega
        rcases List.mem_append.mp hr with hr | hr
        · exact (dBW r hr).sub_left (buf_sub B₀ hj3)
        · rw [hBs r hr]
          exact Offset.disjoint B₀ (by omega) (by omega) (by omega)
      · have hjk' : j = k := by omega
        subst hjk'
        exact rt (by omega)
  unfold Impl.MlKem.AArch64.Kem16P.stepP
  split
  · rename_i hkm
    have hbk : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + k) < 65536 := by
      simp only [Impl.MlKem.AArch64.Kem16P.bufOff] at hbo ⊢; omega
    have hBk : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + k)) = bufAt B₀ k := by
      rw [← hB, bufAt, BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [Impl.MlKem.AArch64.Kem16P.bufOff]
      rw [show Impl.MlKem.AArch64.KEM.TP L + 168 * N₀ + 168 * k = Impl.MlKem.AArch64.KEM.TP L + 168 * (N₀ + k) by
        rw [Nat.mul_add, Nat.add_assoc]]
    refine WP.mono (slotPrf_ok L (N := N₀ + k) (by omega) hbk h.ptr h.pa h.pb
      (by rw [h.keep.get .x28, h28]) hR hBk h.pair (hls.slotLay hk))
      fun t ⟨kt, ft, pt, at', bt, t20, t21, rt⟩ =>
        next [rateR (bufAt B₀ k)] (fun r hr => List.mem_singleton.mp hr) kt ft pt at' bt t20 t21 fun _ => ?_
    rw [seedState_frame h.frame (fun r hr => ?_)] at rt
    · exact rt
    simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact (hl.dPR.sub_left (Region.sub_prefix (by decide : 400 ≤ 2048))).symm
    · exact (hl.dPR.sub_left (sub (by decide))).symm
    · exact (hl.dPR.sub_left (sub (by decide))).symm
    · exact (hl.dPR.sub_left (sub (o := 1536) (n := 136) (by decide))).symm
    · exact hl.dSR.symm
    · exact hl.fR.symm
    · exact hl.dRF
  · rename_i hkm
    refine WP.mono (plainP_ok hk h.ptr h.pa h.pb h.pair hls) fun t ⟨kt, ft, pt, at', bt, t20, t21⟩ =>
      next [] (fun r hr => absurd hr (List.not_mem_nil)) kt (by simpa using ft) pt at' bt t20 t21
        fun hkm' => absurd hkm' hkm

/-- **The three main squeezes** of a pair, the first `m` computing PRF outputs from `N₀`. -/
theorem squeezeP_ok (L : Impl.MlKem.AArch64.KemLay) {s : State} {p st R B₀ : Addr}
    {A B : Spec.Sha3.State} {N₀ m : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hl : SqLayP p st R B₀ s) (h19 : s.gpr .x19 = p) (h20 : s.gpr .x20 = p + 400)
    (h21 : s.gpr .x21 = p + 904) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀)
    (pair : PairAt s.mem p A B) :
    WP isa (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 0)
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 2))) s
      (SInvP s p st R B₀ A B N₀ m 3) := by
  have h0 : SInvP s p st R B₀ A B N₀ m 0 s :=
    ⟨Keep.refl _ _, pair, h19, by rw [h20]; exact (BitVec.add_zero _).symm,
      by rw [h21]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (by simp)⟩
  refine WP.seq (WP.mono (pstep_ok L (k := 0) (by decide) hN hbo hl h28 hR hB h0) fun t ht => ?_)
  refine WP.seq (WP.mono (pstep_ok L (k := 1) (by decide) hN hbo hl h28 hR hB ht) fun u hu => ?_)
  exact pstep_ok L (k := 2) (by decide) hN hbo hl h28 hR hB hu

/-- **A PRF pair's initialization and main squeezes** (as `Hybrid.startM_ok`). -/
theorem startP_ok (L : Impl.MlKem.AArch64.KemLay) {s : State}
    {p seed st R B₀ : Addr} {sb ss a b N₀ m : Nat} (hN : N₀ + 2 < 256)
    (hbo : Impl.MlKem.AArch64.Kem16P.bufOff L (N₀ + 2) < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (hl : SqLayP p st R B₀ s) (h28 : s.gpr .x28 = st)
    (hR : st + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : st + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff L N₀) = B₀) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b L.k))
      (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 0)
        (.seq (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 1) (Impl.MlKem.AArch64.Kem16P.stepP L N₀ m 2)))) s
      fun t =>
      Keep startRegs3 s t ∧ Frame (startWritesP p st s.sp B₀) s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19 = p ∧
      PairAt t.mem p (iterF 3 (Paired.seedState s.mem seed a L.k)) (iterF 3 (Paired.seedState s.mem seed b L.k)) ∧
      Blocks t.mem (p + 400) 3 (Paired.seedState s.mem seed a L.k) ∧
      Blocks t.mem (p + 904) 3 (Paired.seedState s.mem seed b L.k) ∧
      PrfBufs t.mem B₀ s.mem R N₀ (min 3 m) := by
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
  refine WP.mono (squeezeP_ok L hN hbo (hl.frame ku.rd ku.wr ku.sp) h19 h20 h21
    (by rw [ku.get .x28]; exact h28) hR hB pair) fun t ht => ?_
  have hsR : ∀ {N : Nat}, Noise.seedState u.mem R N = Noise.seedState s.mem R N := fun {_} =>
    seedState_frame fi (fun r hr => by rw [List.mem_singleton.mp hr]; exact hl.dPR.symm)
  refine ⟨ku.trans ht.keep, ?_, ?_, ht.ptr, ht.pair, ht.oa, ht.ob, fun k hk => ?_⟩
  · have ft := ht.frame
    rw [ku.sp] at ft
    refine (fi.mono (by simp [startWritesP, startWrites])).trans (ft.sub fun r hr => ?_)
    simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], Region.sub_prefix (by decide : 400 ≤ 2048)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 400) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 904) (n := 504) (by decide)⟩
    · exact ⟨⟨p, 2048⟩, by simp [startWritesP, startWrites], sub (o := 1536) (n := 136) (by decide)⟩
    · exact ⟨stR st, by simp [startWritesP, startWrites], fun _ h => h⟩
    · exact ⟨frame s.sp, by simp [startWritesP, startWrites], fun _ h => h⟩
    · exact ⟨bufR B₀, by simp [startWritesP], fun _ h => h⟩
  · apply sv.frame ht.frame
    intro r hr; simp only [squeezeWritesP, squeezeWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact (hl.dSP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · rw [ku.sp]; exact (hl.fP.sub_right (sub (o := 1800) (n := 48) (by decide))).symm
    · exact (hl.dPF.sub_left (sub (o := 1800) (n := 48) (by decide)))
  · have := ht.prf k hk
    rwa [hsR] at this

end VG.Proof.MlKem.AArch64.Kem16P
