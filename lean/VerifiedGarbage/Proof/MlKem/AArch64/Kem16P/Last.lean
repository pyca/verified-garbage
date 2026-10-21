module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Prf
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FastFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore

/-!
# The singleton computing PRF outputs in its second state

`Kem16P.lastP`: `Paired.lastSample`, whose second state computes
`PRF₂(r, N₀ + k)` in each of the three main squeezes (`stepB`), into the
buffers from `B₀`. As `Paired/LastStart.lean` and `Paired/Last.lean`, with the
buffers among the writes (`fullWritesP`) and their outputs in the
postcondition (`PrfBufs`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr outAddr)
open VG.Proof.Sha3.AArch64.Neon.X2 (callR)
open VG.Proof.MlKem.AArch64.Paired (rateR21 Rate21 Blocks blockAt streamR block_sub
  SingleContext fullWrites seedBytes)
open VG.Proof.MlKem.AArch64.Noise (rateR Rate128)
open VG.Proof.MlKem.AArch64.Hybrid (stepRegs blockAt_eq outAddr_eq in_scratch cov_scratch)
open VG.Proof.Sha3 (iterF iterF_succ)
open VG.Spec.Sha3 (keccakF)

/-- The singleton's memory: its scratch, `r` and the buffers. -/
structure LayB (p R B₀ : Addr) (s : State) : Prop where
  scratch : Covers [⟨p, 2048⟩] s.wr
  rin : Covers [⟨R, 32⟩] (s.rd ++ s.wr)
  dPR : (Region.mk p 2048).Disjoint ⟨R, 32⟩
  bout : Covers [bufR B₀] s.wr
  dPF : (Region.mk p 2048).Disjoint (bufR B₀)
  dRF : (Region.mk R 32).Disjoint (bufR B₀)

theorem LayB.frame {p R B₀ : Addr} {s t : State} (h : LayB p R B₀ s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : LayB p R B₀ t :=
  ⟨by rw [hw]; exact h.scratch, by rw [hr, hw]; exact h.rin, h.dPR, by rw [hw]; exact h.bout,
    h.dPF, h.dRF⟩

/-- What the singleton's squeezes write. -/
def lastWrites (p B₀ : Addr) : List Region := [pairR p, streamR (p + 400), callR (p + 1536), bufR B₀]

theorem buf21_sub (B₀ : Addr) {k : Nat} (hk : k < 3) : Region.Sub (rateR21 (bufAt B₀ k)) (bufR B₀) :=
  Offset.sub_base B₀ (by omega)

/-- After `k` of the singleton's three main squeezes. -/
structure BInv (initial : State) (p R B₀ : Addr) (A : Spec.Sha3.State) (N₀ k : Nat) (s : State) : Prop where
  keep : Keep stepRegs initial s
  pair : ∃ B, PairAt s.mem p (iterF k A) B
  ptr : s.gpr .x19 = p
  pa : s.gpr .x20 = blockAt (p + 400) k
  pb : s.gpr .x21 = bufAt B₀ k
  frame : Frame (lastWrites p B₀) initial.mem s.mem
  oa : Blocks s.mem (p + 400) k A
  prf : PrfBufs s.mem B₀ initial.mem R N₀ k

/-- One main squeeze of the singleton. -/
theorem stepB_ok {initial s : State} {p R B₀ : Addr} {A : Spec.Sha3.State} {N₀ k N : Nat}
    (hNk : N = N₀ + k) (hk : k < 3) (hN : N₀ + 2 < 256) (hl : LayB p R B₀ initial)
    (hR : initial.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (h : BInv initial p R B₀ A N₀ k s) :
    WP isa (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB N) s (BInv initial p R B₀ A N₀ (k + 1)) := by
  subst hNk
  have hls := hl.frame h.keep.rd h.keep.wr
  obtain ⟨B, pair⟩ := h.pair
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  have subP : Region.Sub (pairR p) ⟨p, 2048⟩ := Region.sub_prefix (by decide : 400 ≤ 2048)
  have bs := buf21_sub B₀ hk
  have ea : blockAt (p + 400) k = p + BitVec.ofNat 64 (400 + 168 * k) := blockAt_eq p 400 k
  have cP : Covers [pairR p] s.wr := by
    simpa only [BitVec.add_zero, pairR] using cov_scratch (o := 0) (n := 400) hls.scratch (by decide)
  refine WP.seq (WP.mono (reinitB_ok (N := N₀ + k) (by omega) h.ptr
    (by rw [h.keep.get .x28]; exact hR) pair cP (hl.dPR.sub_left subP) hls.rin)
    fun u ⟨ku, fu, pu⟩ => ?_)
  have u19 : u.gpr .x19 = p := (ku.get .x19).trans h.ptr
  have u20 : u.gpr .x20 = blockAt (p + 400) k := (ku.get .x20).trans h.pa
  have u21 : u.gpr .x21 = bufAt B₀ k := (ku.get .x21).trans h.pb
  have uwr : u.wr = s.wr := ku.wr
  have hc := Paired.squeezeBlock_ok (rp := .x19) (ra := .x20) (rb := .x21) u19 u20 u21
    (by rw [u19])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) pu
    (fun i hi => by
      rw [ku.rd, uwr]
      exact Covers.right (cov_scratch hls.scratch (o := 16 * i) (n := 16) (by omega)) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (fun i hi => by rw [uwr, ea, outAddr_eq]; exact in_scratch hls.scratch (by omega))
    (fun i hi => by
      rw [uwr]
      show InRegions s.wr (B₀ + BitVec.ofNat 64 (168 * k) + BitVec.ofNat 64 (8 * i)) 8
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Hybrid.covers_in hls.bout (by omega : 168 * k + 8 * i + 8 ≤ 504) (by decide))
    (by rw [ea]; exact (hl.dPF.sub_left (sub (by omega))).sub_right bs)
    (by rw [ea]; exact Offset.base_disjoint p (by omega) (by omega))
    ((hl.dPF.sub_left subP).sub_right bs)
    (Offset.base_disjoint p (e := 1536) (n := 136) (by decide) (by decide))
    (by
      rw [uwr]
      exact Covers.cons cP (Covers.cons (cov_scratch (o := 1536) (n := 136) hls.scratch (by decide))
        Covers.nil))
  unfold Impl.MlKem.AArch64.Hybrid.plainStep Impl.MlKem.AArch64.Hybrid.squeezeTail
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp hc) fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono hv fun w ⟨kw, pw, aw, bw, fw, vw⟩ => ?_
  refine wp_addImm (by decide) fun w1 h1 e1 => wp_addImm (by decide) fun t h2 e2 => wp_nil ?_
  have hw : Keep Paired.blockRegs u w := ⟨kw.gpr, kw.rd, kw.wr, kw.sp, vw⟩
  have ot : Only [.x20, .x21] w t := (h1.trans h2).mono (by simp)
  have hm : t.mem = w.mem := ot.mem
  -- What the step wrote.
  have fstep : Frame [pairR p, rateR21 (blockAt (p + 400) k), rateR21 (bufAt B₀ k), callR (p + 1536)]
      s.mem t.mem := by rw [hm]; exact (fu.mono (by simp)).trans fw
  have fst : Frame (lastWrites p B₀) s.mem t.mem := fstep.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨pairR p, by simp [lastWrites], fun _ h => h⟩
    · exact ⟨streamR (p + 400), by simp [lastWrites], block_sub _ hk⟩
    · exact ⟨bufR B₀, by simp [lastWrites], bs⟩
    · exact ⟨callR (p + 1536), by simp [lastWrites], fun _ h => h⟩
  have dW : ∀ r ∈ lastWrites p B₀, (Region.mk R 32).Disjoint r := by
    intro r hr; simp only [lastWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hl.dPR.sub_left subP).symm
    · exact (hl.dPR.sub_left (sub (o := 400) (n := 504) (by decide))).symm
    · exact (hl.dPR.sub_left (sub (o := 1536) (n := 136) (by decide))).symm
    · exact hl.dRF
  refine ⟨(h.keep.trans ((ku.trans hw).trans ot.keep)).mono
      (by simp [stepRegs, Hybrid.clobbered, Paired.blockRegs]),
    ⟨keccakF (Noise.seedState s.mem R (N₀ + k)), ?_⟩, ?_, ?_, ?_, h.frame.trans fst, ?_, fun j hj => ?_⟩
  · rw [hm]; simpa only [iterF_succ] using pw
  · rw [ot.get .x19 (by decide), kw.gpr .x19 (by decide), u19]
  · rw [h2.get .x20 (by decide), e1, kw.gpr .x20 (by decide), u20]
    show (p + 400 + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = p + 400 + BitVec.ofNat 64 (168 * (k + 1))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
  · rw [e2, h1.get .x21 (by decide), kw.gpr .x21 (by decide), u21]
    show (B₀ + BitVec.ofNat 64 (168 * k)) + BitVec.ofNat 64 168 = B₀ + BitVec.ofNat 64 (168 * (k + 1))
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 168 * k + 168 = 168 * (k + 1) by omega]
  · intro j hj
    by_cases he : j = k
    · subst j; rw [hm]; simpa only [iterF_succ] using aw
    · have hjk : j < k := by omega
      intro i hi
      have hc : (rateR21 (blockAt (p + 400) j)).Contains (outAddr (blockAt (p + 400) j) i) 8 :=
        Offset.contains_base _ (by omega) (by omega)
      rw [fstep.readW hc (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact (Offset.base_disjoint p (by decide) (by decide) |>.sub_right
              (block_sub (p + 400) (by omega))).symm
          · exact Offset.disjoint (p + 400) (Or.inl (by omega)) (by omega) (by omega)
          · exact ((hl.dPF.sub_left (sub (o := 400) (n := 504) (by decide))).sub_left
              (block_sub (p + 400) (by omega))).sub_right bs
          · exact ((Offset.disjoint p (d := 1536) (n := 136) (e := 400) (k := 504) (by decide) (by decide)
              (by decide)).sub_right (block_sub (p + 400) (by omega))).symm) (by decide)]
      exact h.oa j hjk i hi
  · by_cases he : j = k
    · subst j
      have e := seedState_frame (N := N₀ + k) h.frame dW
      intro i hi
      rw [hm, ← e]
      exact bw i (by omega)
    · have hjk : j < k := by omega
      have bj := buf_sub B₀ (k := j) (by omega)
      refine rate128_frame (h.prf j hjk) fstep fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hl.dPF.symm.sub_left bj).sub_right subP
      · rw [ea]; exact (hl.dPF.symm.sub_left bj).sub_right (sub (by omega))
      · exact Offset.disjoint B₀ (Or.inl (by omega)) (by omega) (by omega)
      · exact (hl.dPF.symm.sub_left bj).sub_right (sub (o := 1536) (n := 136) (by decide))

/-- The registers the singleton's start changes. -/
def startBRegs : List Reg := Paired.initRegs ++ stepRegs

/-- The singleton's initialization and three main squeezes (as `Paired.start_ok`), its second
state computing `PRF₂(r, N₀)`, …, `PRF₂(r, N₀ + 2)` into the buffers from `B₀`. -/
theorem startB_ok (L : Impl.MlKem.AArch64.KemLay) {s : State} {p seed R B₀ : Addr} {sb ss a N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩) (hl : LayB p R B₀ s)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a L.k ++
        Impl.MlKem.AArch64.ptrTo .x21 .x28 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀)))
      (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB N₀) (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 1))
        (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 2))))) s fun t =>
      Keep startBRegs s t ∧ Frame [⟨p, 2048⟩, bufR B₀] s.mem t.mem ∧ Noise.Saved p s t.mem ∧
      t.gpr .x19 = p ∧ Blocks t.mem (p + 400) 3 (Paired.seedState s.mem seed a L.k) ∧
      PrfBufs t.mem B₀ s.mem R N₀ 3 := by
  have iw {o l : Nat} (h : o + l ≤ 2048) := Noise.inScratch hl.scratch h (by decide)
  have sub : ∀ {o n : Nat}, o + n ≤ 2048 → Region.Sub ⟨p + BitVec.ofNat 64 o, n⟩ ⟨p, 2048⟩ :=
    fun h => Offset.sub_base p h
  apply WP.seq
  rw [WP.block_append_iff]
  refine (WP.mono (Paired.init_ok hss hsb h8 hp ha hin
    (fun j hj => iw (by omega)) (fun j hj => iw (by omega))
    (hsep.sub_right (Offset.sub_base p (by decide)))
    (hsep.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
    (Offset.disjoint_base p (by decide) (by decide)))
    fun u ⟨ku, fu, sv, h19, h20, _, _, pair⟩ => wp_ptrTo' (by decide) hbo fun v ov e21 => ?_)
  have kv : Keep startBRegs s v := (ku.trans ov.keep).mono (by simp [startBRegs, Paired.initRegs])
  have mv : v.mem = u.mem := ov.mem
  have v28 : v.gpr .x28 = s.gpr .x28 := kv.get .x28
  have h0 : BInv v p R B₀ (Paired.seedState s.mem seed a L.k) N₀ 0 v :=
    ⟨Keep.refl _ _, ⟨_, by rw [mv]; exact pair⟩, (ov.get .x19 (by decide)).trans h19,
      by rw [ov.get .x20 (by decide), h20]; exact (BitVec.add_zero _).symm,
      by rw [e21, ku.get .x28, hB]; exact (BitVec.add_zero _).symm, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hlv : LayB p R B₀ v := hl.frame kv.rd kv.wr
  have hRv : v.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R := by rw [v28]; exact hR
  refine WP.seq (WP.mono (stepB_ok (k := 0) rfl (by decide) hN hlv hRv h0) fun t ht => ?_)
  refine WP.seq (WP.mono (stepB_ok (k := 1) rfl (by decide) hN hlv hRv ht) fun t' ht' => ?_)
  refine WP.mono (stepB_ok (k := 2) rfl (by decide) hN hlv hRv ht') fun w hw => ?_
  have fi : Frame [Noise.savedR p, pairR p] s.mem v.mem := by rw [mv]; exact fu
  have dS : ∀ r ∈ lastWrites p B₀, (Noise.savedR p).Disjoint r := by
    intro r hr; simp only [lastWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact hl.dPF.sub_left (sub (o := 1800) (n := 48) (by decide))
  refine ⟨kv.trans hw.keep |>.mono (by simp [startBRegs]), ?_, sv.frame (by rw [← mv]; exact hw.frame) dS,
    hw.ptr, hw.oa, fun k hk => ?_⟩
  · refine (fi.sub fun r hr => ?_).trans (hw.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p, 2048⟩, by simp, sub (o := 1800) (n := 48) (by decide)⟩
      · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩
    · simp only [lastWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨p, 2048⟩, by simp, Region.sub_prefix (by decide : 400 ≤ 2048)⟩
      · exact ⟨⟨p, 2048⟩, by simp, sub (o := 400) (n := 504) (by decide)⟩
      · exact ⟨⟨p, 2048⟩, by simp, sub (o := 1536) (n := 136) (by decide)⟩
      · exact ⟨bufR B₀, by simp, fun _ h => h⟩
  · have e := seedState_frame (N := N₀ + k) fi (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hl.dPR.symm.sub_right (sub (o := 1800) (n := 48) (by decide))
      · exact hl.dPR.symm.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048)))
    rw [← e]; exact hw.prf k hk

/-! ## The rejection and the singleton -/

/-- What the singleton writes. -/
def fullWritesP (p out B₀ : Addr) : List Region := fullWrites p out ++ [bufR B₀]

/-- The singleton's buffers, apart from the rest of its memory. -/
structure BufApart (p seed out table R B₀ : Addr) : Prop where
  lay : (Region.mk p 2048).Disjoint (bufR B₀)
  seed : (Region.mk seed 32).Disjoint (bufR B₀)
  out : (bufR B₀).Disjoint (polyRegion out)
  table : (Region.mk table 4096).Disjoint (bufR B₀)

theorem ctx_frameP {s t : State} {p out table B₀ : Addr} (h : SingleContext p out table s)
    (htb : (Region.mk table 4096).Disjoint (bufR B₀))
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame (fullWritesP p out B₀) s.mem t.mem) :
    SingleContext p out table t := by
  refine ⟨by rw [hw]; exact h.scratch, by rw [hw]; exact h.output, h.apart, ?_,
    by rw [hr, hw]; exact h.readable, h.tableScratch, h.tableOut⟩
  exact h.artifact.frame hf (by
    intro r hr
    simp only [fullWritesP, fullWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.tableScratch
    · exact h.tableOut
    · exact htb)

/-- The singleton's start, constants and rejection (`Paired.lastStartCode`). -/
def lastStartP (sb ss a k off bo N₀ : Nat) (w16 : Bool) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k ++ Impl.MlKem.AArch64.ptrTo .x21 .x28 bo))
   (.seq (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB N₀) (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 1))
      (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 2))))
    (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)))

structure LastStartPostP (w16 : Bool) (B : Nat → Byte) (p out table R B₀ : Addr) (N₀ : Nat)
    (s t : State) : Prop where
  keep : Keep Paired.lastStartRegs s t
  frame : Frame (fullWritesP p out B₀) s.mem t.mem
  saved : Noise.Saved p s t.mem
  context : SingleContext p out table t
  coeffs : Rej8.Scalar.CoeffsW w16 t.mem out (sampleAfter [] B 168)
  flag : (t.gpr .x22).toNat = if (sampleAfter [] B 168).length = 256 then 1 else 0
  ptr : t.gpr .x19 = p
  prf : PrfBufs t.mem B₀ s.mem R N₀ 3

theorem lastStartP_ok (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (hseed : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hout : s.gpr .x28 + BitVec.ofNat 64 off = out)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (ctx : SingleContext p out table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE" = table)
    (hl : LayB p R B₀ s) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀) :
    WP isa (lastStartP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16) s
      (LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s) := by
  have combined := WP.mono_syms (startB_ok L (a := a) hN hbo hss hsb h8 hp hseed hin hsep hl hR hB)
    (R := fun u => WP isa (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts)
      (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)) u
      (LastStartPostP w16 (xofByte (seedBytes s.mem seed a L.k)) p out table R B₀ N₀ s))
    (fun u ⟨ku, fu, svu, u19, bu, pu⟩ sy => by
      have fuP : Frame (fullWritesP p out B₀) s.mem u.mem :=
        fu.mono (by simp [fullWritesP, fullWrites])
      have cu := ctx_frameP ctx ap.table ku.rd ku.wr fuP
      refine WP.seq (WP.mono_syms (Rej8.constants_ok u (by
        rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
        fun v ⟨kv, cv, mv, tv⟩ syv => ?_)
      have fv : Frame [⟨p + 1408, 8⟩] u.mem v.mem := by
        rw [mv, u19]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
      have fvBig : Frame (fullWritesP p out B₀) u.mem v.mem := fv.sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨⟨p, 2048⟩, by simp [fullWritesP, fullWrites], Offset.sub_base p (by decide)⟩)
      have ctv := ctx_frameP cu ap.table kv.rd kv.wr fvBig
      have v19 : v.gpr .x19 = p := (kv.get .x19).trans u19
      have v28 : v.gpr .x28 = s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
      have v16 : v.gpr .x16 = table := by rw [tv, syv, sy, ht]
      have stream : ∀ i < 504, v.mem ((p + 400) + BitVec.ofNat 64 i) =
          xofByte (seedBytes s.mem seed a L.k) i := by
        intro i hi
        have hd : ∀ r ∈ [Region.mk (p + 1408) 8], (Region.mk (p + 400) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide)
        exact (fv.bytes hd (by change 504 ≤ 2 ^ 64; decide) hi).trans (bu.xof hk hk256 hi)
      have ready : Rej8.TableReady v out :=
        ⟨by rw [v16]; exact ctv.artifact, by rw [v16]; exact ctv.readable, by rw [v16]; exact ctv.tableOut⟩
      have env := Paired.rejection_envW (w16 := w16) (off := 400) (N := 168) (by decide) (by decide)
        ctv.scratch ctv.output ctv.apart stream (fun _ hm => ready.read hm)
        (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
      have svv := svu.frame fv (by
        simp only [List.mem_singleton, forall_eq]
        exact Offset.disjoint p (by decide) (by decide) (by decide))
      have pv := pu.frame (Nat.le_refl 3) fv (by
        simp only [List.mem_singleton, forall_eq]
        exact (ap.lay.sub_left (Offset.sub_base p (by decide))).symm)
      refine WP.mono (Paired.reject_ok v (by decide) hoff (by decide)
        (by rw [v19, v28, hout]; exact env) cv) fun t h => ?_
      have ft : Frame [polyRegion out] v.mem t.mem := by rw [v28, hout] at h; exact h.frame
      have ftBig := ft.mono (rs' := fullWritesP p out B₀) (by simp [fullWritesP, fullWrites])
      have svt := svv.frame ft (by
        simp only [List.mem_singleton, forall_eq]
        exact ctx.apart.sub_left (Offset.sub_base p (by decide)))
      refine ⟨((ku.trans kv).trans h.keep).mono (by
          simp [Paired.lastStartRegs, startBRegs, Paired.initRegs, stepRegs, Hybrid.clobbered,
            Paired.startRegs, Paired.squeezeRegs, Paired.blockRegs]),
        (fuP.trans fvBig).trans ftBig, svt,
        ctx_frameP ctv ap.table h.keep.rd h.keep.wr ftBig, ?_, h.flagValue, (h.keep.get .x19).trans v19,
        pv.frame (Nat.le_refl 3) ft (by simp only [List.mem_singleton, forall_eq]; exact ap.out)⟩
      simpa only [v28, hout] using h.coeffs)
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu => WP.seq hu)

/-- `Kem16P.lastP`, as `Paired.lastCode`. -/
def lastCodeP (sb ss a k off bo N₀ : Nat) (w16 : Bool) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k ++ Impl.MlKem.AArch64.ptrTo .x21 .x28 bo))
   (.seq (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB N₀) (.seq (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 1))
      (Impl.MlKem.AArch64.Kem16P.stepB Impl.MlKem.AArch64.KEM.RB (N₀ + 2))))
    (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts)
     (.seq (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)
      (.seq (.ite (.zero .x .x22) (Paired.fullSampleCode sb ss off a k w16) (.block []))
       (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r, i) =>
         .ldr .x r .x19 (1800 + 8 * i)))))))

theorem lastP_eq (L : Impl.MlKem.AArch64.KemLay) (N₀ : Nat) :
    Impl.MlKem.AArch64.Kem16P.lastP L N₀ =
      lastCodeP Impl.MlKem.AArch64.KEM.SB Impl.MlKem.AArch64.KEM.SS (L.k * L.k - 1) L.k
        (Impl.MlKem.AArch64.KEM.AH + 1024 * (L.k * L.k - 1)) (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀)
        N₀ true := by
  simp only [Impl.MlKem.AArch64.Kem16P.lastP, Paired.fullSample_eq,
    lastCodeP, Impl.MlKem.AArch64.seqs, Bool.false_eq_true, ↓reduceIte]

structure LastPostP (w16 : Bool) (B : List Byte) (p out R B₀ : Addr) (N₀ : Nat) (s t : State) : Prop where
  keep : Keep Paired.pairRegs s t
  frame : Frame (fullWritesP p out B₀) s.mem t.mem
  coeffs : CoeffsUpToW w16 t.mem out (sampleAfter [] (xofByte B) 280).length
    (Sample.cvW w16 (sampleAfter [] (xofByte B) 280)) (fun _ => 0)
  reduced : ReducedW (cw w16) t.mem out
  result : ((sampleAfter [] (xofByte B) 280).length = 256 ∧ sampleNTT 280 B = some (polyAtW (cw w16) t.mem out)) ∨
    ((sampleAfter [] (xofByte B) 280).length ≠ 256 ∧ sampleNTT 280 B = none)
  status : t.gpr .x24 = s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] (xofByte B) 280).length = 256 then 1 else 0)
  prf : PrfBufs t.mem B₀ s.mem R N₀ 3

structure LastReadyP (w16 : Bool) (B : List Byte) (p out R B₀ : Addr) (N₀ : Nat) (s t : State) : Prop where
  keep : Keep Paired.pairWorkingRegs s t
  frame : Frame (fullWritesP p out B₀) s.mem t.mem
  saved : Noise.Saved p s t.mem
  ptr : t.gpr .x19 = p
  coeffs : CoeffsUpToW w16 t.mem out (sampleAfter [] (xofByte B) 280).length
    (Sample.cvW w16 (sampleAfter [] (xofByte B) 280)) (fun _ => 0)
  reduced : ReducedW (cw w16) t.mem out
  status : t.gpr .x24 = s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] (xofByte B) 280).length = 256 then 1 else 0)
  prf : PrfBufs t.mem B₀ s.mem R N₀ 3

/-- **The singleton computing PRF outputs** (as `Paired.lastCode_ok`). -/
theorem lastCodeP_ok (L : Impl.MlKem.AArch64.KemLay) {w16 : Bool} {s : State}
    {p seed out table R B₀ : Addr} {sb ss a off N₀ : Nat}
    (hN : N₀ + 2 < 256) (hbo : Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀ < 65536)
    (hss : ss < 4096) (hsb : sb + 32 ≤ 32768) (h8 : sb % 8 = 0) (hoff : off < 65536)
    (hk : 0 < L.k) (hk256 : L.k ≤ 256)
    (hp : s.gpr .x28 + BitVec.ofNat 64 ss = p) (hseed : s.gpr .x28 + BitVec.ofNat 64 sb = seed)
    (hout : s.gpr .x28 + BitVec.ofNat 64 off = out)
    (hin : ∀ j < 4, InRegions (s.rd ++ s.wr) (seed + BitVec.ofNat 64 (8 * j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p, 2048⟩)
    (hseedOut : (Region.mk seed 32).Disjoint (polyRegion out))
    (ctx : SingleContext p out table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE" = table)
    (hstatus : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1)
    (hl : LayB p R B₀ s) (ap : BufApart p seed out table R B₀)
    (hR : s.gpr .x28 + BitVec.ofNat 64 Impl.MlKem.AArch64.KEM.RB = R)
    (hB : s.gpr .x28 + BitVec.ofNat 64 (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) = B₀) :
    WP isa (lastCodeP sb ss a L.k off (Impl.MlKem.AArch64.Kem16P.bufOff (Impl.MlKem.AArch64.KEM.TP L) N₀) N₀ w16) s
      (LastPostP w16 (seedBytes s.mem seed a L.k) p out R B₀ N₀ s) := by
  have dF : ∀ r ∈ fullWrites p out, (bufR B₀).Disjoint r := by
    intro r hr; simp only [fullWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ap.lay.symm
    · exact ap.out
  have combined := WP.mono_syms (lastStartP_ok L (w16 := w16) (a := a) hN hbo (by omega) hsb h8 hoff
      hk hk256 hp hseed hout hin hsep ctx ht hl ap hR hB)
    (R := fun u => WP isa (.seq (.ite (.zero .x .x22) (Paired.fullSampleCode sb ss off a L.k w16) (.block []))
      (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r, i) => .ldr .x r .x19 (1800 + 8 * i)))) u
      (LastPostP w16 (seedBytes s.mem seed a L.k) p out R B₀ N₀ s))
    (fun u hu sy => by
      have seedEq : seedBytes u.mem seed a L.k = seedBytes s.mem seed a L.k := by
        unfold seedBytes
        rw [bytesAt_frame hu.frame (by
          intro r hr
          simp only [fullWritesP, fullWrites, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with (rfl | rfl) | rfl
          · exact hsep
          · exact hseedOut
          · exact ap.seed) (by decide : 32 ≤ 2 ^ 64)]
      have branch : WP isa (.ite (.zero .x .x22) (Paired.fullSampleCode sb ss off a L.k w16) (.block [])) u
          (LastReadyP w16 (seedBytes s.mem seed a L.k) p out R B₀ N₀ s) := by
        refine WP.ite (u.gpr .x22 == 0) (eval_zero _ _) (fun _ => ?_) (fun hz => ?_)
        · refine WP.mono (Paired.fullSampleCode_ok hss hsb h8 hoff hk hk256 hu.ptr
            (by rw [hu.keep.get .x28]; exact hp) (by rw [hu.keep.get .x28]; exact hseed)
            (by rw [hu.keep.get .x28]; exact hout)
            (by rw [hu.keep.rd, hu.keep.wr]; exact hin) hu.context.scratch hu.context.output
            hsep ctx.apart hu.saved (by rw [sy, ht]; exact hu.context.artifact)
            (by rw [sy, ht]; exact hu.context.readable) (by rw [sy, ht]; exact ctx.tableScratch)
            (by rw [sy, ht]; exact ctx.tableOut)) fun t h => ?_
          refine ⟨(hu.keep.trans h.keep).mono (by decide),
            hu.frame.trans (h.frame.mono fun r hr => List.mem_append_left _ hr), h.saved, h.ptr, ?_, h.reduced, ?_,
            hu.prf.frame (Nat.le_refl 3) h.frame dF⟩
          · rw [← seedEq]; exact h.coeffs
          · rw [h.status, hu.keep.get .x24, seedEq]
        · have full : (sampleAfter [] (xofByte (seedBytes s.mem seed a L.k)) 168).length = 256 := by
            by_contra hh
            have he : u.gpr .x22 = 0 := BitVec.eq_of_toNat_eq (by rw [hu.flag, ite_eq_right hh]; rfl)
            rw [he] at hz; contradiction
          have eqFull := sampleAfter_full full 280 (by decide : 168 ≤ 280)
          have cc := Paired.full_coeffs hu.coeffs full
          apply wp_nil
          refine ⟨hu.keep.mono (by decide), hu.frame, hu.saved, hu.ptr, ?_, Sample.reduced_of_coeffs cc, ?_,
            hu.prf⟩
          · rw [eqFull]; exact cc
          · rw [eqFull, ite_eq_left full, hu.keep.get .x24]
            rcases hstatus with h | h <;> rw [h] <;> rfl
      refine WP.seq (WP.mono branch fun t h => ?_)
      refine WP.mono (Paired.restore_ok h.keep h.ptr h.saved (by rw [h.keep.wr]; exact ctx.scratch))
        fun v ⟨kv, mv, v24⟩ => ?_
      have coeffs : CoeffsUpToW w16 v.mem out (sampleAfter [] (xofByte (seedBytes s.mem seed a L.k)) 280).length
          (Sample.cvW w16 (sampleAfter [] (xofByte (seedBytes s.mem seed a L.k)) 280)) (fun _ => 0) := by
        rw [mv]; exact h.coeffs
      exact ⟨kv, by rw [mv]; exact h.frame, coeffs, by rw [mv]; exact h.reduced,
        Paired.coeffs_sample_result coeffs, v24.trans h.status, by rw [mv]; exact h.prf⟩)
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu =>
    WP.seq (WP.mono (WP.seq_iff.mp hu) fun v hv =>
      WP.seq (WP.mono (WP.seq_iff.mp hv) fun w hw => WP.seq hw)))

end VG.Proof.MlKem.AArch64.Kem16P
