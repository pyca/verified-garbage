import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Ends
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress

/-!
# Verified Argon2 block compression on x86-64 with AVX-512

`vg_argon2_compress_avx512` meets `compressContract`, as `vg_argon2_compress`
does: the initial XOR (`init_prefix`), the four pairs of rows and four pairs
of columns (`rows_ok`, `cols_ok`) and the final XOR (`finish_prefix`)
compose to `Spec.Argon2.compress`, between Intel's MXCSR prologue and
epilogue (those of the AVX2 code, and their proofs), which keep MXCSR's
control bits (`ctlOk`). Constant time is checked by evaluation, as for the
scalar code.
-/

namespace VG.Proof.Argon2.X86_64.Avx512

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx512
open VG.Impl.Argon2.X86_64.Avx2 (mxcsrOff)
open VG.Proof.Argon2.X86_64 (off Scratch ea_at Inputs blockAt_get xorBlock_get compressLocal
  initial_agree initialTaint compress_implies original_preserved round_frame scratch_unchanged)
open VG.Proof.Argon2.X86_64.Avx2 (VKeep VKeep.refl ifp ifn save_ok set_ok restore_ok blockAt_mx
  ldmxcsr_ok mxR mxR_sub vzeroupper_ok)

/-! ## The output -/

/-- The output chunk of word `i`. -/
def fchunk (i : Nat) : Nat := 4 * (i % 16 / 8) + i / 32

theorem finish_eq : Impl.Argon2.X86_64.Avx512.finish = (List.range 8).flatMap fun i => finishChunk (i / 4) (i % 4) := rfl

/-- Finish the first `m` chunks, preserving scratch. -/
theorem finish_prefix (m : Nat) (hm : m ≤ 8) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range m).flatMap fun i => finishChunk (i / 4) (i % 4))) s fun t =>
      (∀ i (hi : i < 128), fchunk i < m →
        t.mem.readW (off out (8 * i)) 64 = (cv s.mem p)[i] ^^^ s.mem.readW (off p (8 * i)) 64) ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction m with
  | zero => exact WP.block_nil ⟨fun i hi h => by simp only [fchunk] at h; omega, Frame.refl _ _, VKeep.refl s⟩
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (finishChunk_ok (out := out) (n := m / 4) (k := m % 4) (by omega) (by omega) (hs.of_vkeep hk)
      (by rw [hk.gpr]; exact ho) (by rw [hk.wr]; exact hw)).mono ?_
    rintro u ⟨v, w, hv, hw', hmem, hk'⟩
    have cvs : ∀ j (hj : j < 128), (cv t.mem p)[j] = (cv s.mem p)[j] := fun j hj => by
      rw [cv_get _ _ _ hj, cv_get _ _ _ hj,
        scratch_unchanged hf hd (d := 1024 + cvOff j) (by have := cvOff_lt j hj; omega)]
    have rs : ∀ d, d + 8 ≤ 4096 → t.mem.readW (off p d) 64 = s.mem.readW (off p d) 64 :=
      fun d hd' => scratch_unchanged hf hd hd'
    refine ⟨fun i hi hc => ?_, ?_, hk.trans hk'⟩
    · rw [hmem, read_write512 _ out (by omega) (by omega) (by omega) (by omega),
        read_write512 _ out (by omega) (by omega) (by omega) (by omega)]
      by_cases e : fchunk i = m
      · simp only [fchunk] at e
        by_cases h2 : i / 16 % 2 = 1
        · rw [ifp (by omega), show (8 * i - (256 * (m % 4) + 128 + 64 * (m / 4))) / 8 =
            i - (32 * (m % 4) + 16 + 8 * (m / 4)) by omega, hw' _ (by omega)]
          rw [cv_idx _ _ (show 32 * (m % 4) + 16 + 8 * (m / 4) + (i - (32 * (m % 4) + 16 + 8 * (m / 4))) = i by
            omega) _ hi, cvs i hi, show 8 * (32 * (m % 4) + 16 + 8 * (m / 4) +
              (i - (32 * (m % 4) + 16 + 8 * (m / 4)))) = 8 * i by omega, rs _ (by omega)]
        · rw [ifn (by omega), ifp (by omega), show (8 * i - (256 * (m % 4) + 64 * (m / 4))) / 8 =
            i - (32 * (m % 4) + 8 * (m / 4)) by omega, hv _ (by omega)]
          rw [cv_idx _ _ (show 32 * (m % 4) + 8 * (m / 4) + (i - (32 * (m % 4) + 8 * (m / 4))) = i by
            omega) _ hi, cvs i hi, show 8 * (32 * (m % 4) + 8 * (m / 4) +
              (i - (32 * (m % 4) + 8 * (m / 4)))) = 8 * i by omega, rs _ (by omega)]
      · simp only [fchunk] at e hc
        rw [ifn (by omega), ifn (by omega)]
        exact ht i hi (by simp only [fchunk]; omega)
    · rw [hmem]
      exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))

/-! ## The passes -/

/-- P on row `i / 16` of `r`, word `i % 16`. -/
def rowWord (r : Block) (i : Nat) (hi : i < 128) : Word :=
  (permute (gather (rowIndex ⟨i / 16, by omega⟩) r))[i % 16]'(by omega)

theorem rowPass_list (ps : List Nat) (hps : ∀ pp ∈ ps, pp < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (ps.foldr (fun pp rest => .seq (rows pp) rest) (.block [])) s fun t =>
      (∀ i (hi : i < 128), (cv t.mem p)[i] = if i / 32 ∈ ps then rowWord (blockAt s.mem p) i hi
        else (cv s.mem p)[i]) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction ps generalizing s with
  | nil => exact WP.block_nil ⟨fun i hi => by simp, Frame.refl _ _, VKeep.refl s⟩
  | cons pp ps ih =>
    apply WP.seq
    refine (rows_ok (hps pp List.mem_cons_self) hs).mono ?_
    rintro t ⟨hc, hf, hk⟩
    refine (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk'⟩
    refine ⟨fun i hi => ?_, hf.trans hf', hk.trans hk'⟩
    rw [hc' i hi, hc i hi, original_preserved hf]
    by_cases h1 : i / 32 ∈ ps
    · rw [ifp h1, ifp (List.mem_cons_of_mem _ h1)]
    · rw [ifn h1]
      by_cases h2 : i / 32 = pp
      · rw [ifp h2, ifp (by rw [h2]; exact List.mem_cons_self)]
        rfl
      · rw [ifn h2, ifn (fun h => (List.mem_cons.mp h).elim h2 h1)]

/-- P on columns `2c` and `2c + 1`. -/
def pairStep (b : Block) (c : Nat) : Block :=
  permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
    (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b)

theorem colPass_list (cs : List Nat) (hcs : ∀ c ∈ cs, c < 4) {s : State} {p : Addr} (hs : Scratch s p) :
    WP isa (cs.foldr (fun c rest => .seq (cols c) rest) (.block [])) s fun t =>
      cv t.mem p = cs.foldl pairStep (cv s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ VKeep s t := by
  induction cs generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, VKeep.refl s⟩
  | cons c cs ih =>
    apply WP.seq
    refine (cols_ok (hcs c List.mem_cons_self) hs).mono ?_
    rintro t ⟨hc, hf, hk⟩
    refine (ih (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) (hs.of_vkeep hk)).mono ?_
    rintro u ⟨hc', hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    rw [hc', hc, List.foldl_cons]
    rfl

/-! ## G -/

/-- G between the MXCSR prologue and epilogue. -/
theorem body_ok {s : State} {p x y out : Addr} (hs : Scratch s p) (hin : Inputs s x y p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa body s fun t => blockAt t.mem out = Spec.Argon2.compress (blockAt s.mem x) (blockAt s.mem y) ∧
      Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem t.mem ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  unfold body
  apply WP.seq
  refine (init_prefix 16 (by decide) hs hin).mono ?_
  rintro s1 ⟨hi1, hf1, hk1⟩
  have horig := initialized_all hi1
  have hs1 := hs.of_vkeep hk1
  apply WP.seq
  refine (rowPass_list (List.range 4) (fun _ h => List.mem_range.mp h) hs1).mono ?_
  rintro s2 ⟨hrow, hf2, hk2⟩
  apply WP.seq
  refine (colPass_list (List.range 4) (fun _ h => List.mem_range.mp h) (hs1.of_vkeep hk2)).mono ?_
  rintro s3 ⟨hcol, hf3, hk3⟩
  have hk13 := hk1.trans (hk2.trans hk3)
  rw [WP.block_append_iff]
  refine (finish_prefix 8 (by decide) ((hs1.of_vkeep hk2).of_vkeep hk3)
    (by rw [hk13.gpr]; exact ho) (by rw [hk13.wr]; exact hw) hd).mono ?_
  rintro s4 ⟨hfin, hf4, hk4⟩
  refine (vzeroupper_ok s4).mono ?_
  rintro t ⟨hmt, hgt, hrt, hwt, hxt⟩
  have hq : cv s2.mem p = (List.finRange 8).foldl (fun b r => permuteAt (rowIndex r) b)
      (xorBlock (blockAt s.mem x) (blockAt s.mem y)) := by
    apply Vector.ext; intro i hi
    rw [hrow i hi, ifp (List.mem_range.mpr (by omega)), Proof.Argon2.rows_get _ i hi, horig]
    rfl
  have hz : cv s3.mem p = (List.finRange 8).foldl (fun b c => permuteAt (colIndex c) b) (cv s2.mem p) := by
    rw [hcol, Proof.Argon2.foldl_pairs]
    rfl
  have hr3 : blockAt s3.mem p = xorBlock (blockAt s.mem x) (blockAt s.mem y) := by
    rw [original_preserved hf3, original_preserved hf2, horig]
  refine ⟨?_, ?_, fun r _ => ?_, ?_, ?_, ?_⟩
  · apply Vector.ext; intro i hi
    have e := hfin i hi (by simp only [fchunk]; omega)
    show (blockAt t.mem out)[(⟨i, hi⟩ : Fin 128)] =
      (compress (blockAt s.mem x) (blockAt s.mem y))[(⟨i, hi⟩ : Fin 128)]
    have er := blockAt_get s3.mem p ⟨i, hi⟩
    rw [hr3] at er
    rw [blockAt_get, hmt, e, ← er, hz, hq]
    simp only [Spec.Argon2.compress, xorBlock, Vector.getElem_zipWith, Fin.getElem_fin]
  · rw [hmt]
    have f1 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f4 : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] s3.mem s4.mem :=
      hf4.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    exact ((f1.trans (round_frame hf2)).trans (round_frame hf3)).trans f4
  · rw [hgt, hk4.gpr, hk13.gpr]
  · rw [hrt, hk4.rd, hk13.rd]
  · rw [hwt, hk4.wr, hk13.wr]
  · rw [hxt, hk4.mxcsr, hk13.mxcsr]

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.Avx512.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  unfold Impl.Argon2.X86_64.Avx512.compress
  apply WP.seq
  refine (save_ok scr).mono ?_
  rintro s1 ⟨h11, hg1, hr1, hw1, -, hf1⟩
  have scr1 : Scratch s1 (s.gpr .rcx) := ⟨hg1 .rcx (by decide), hw1 ▸ scr.wr⟩
  apply WP.seq
  apply WP.seq
  refine (set_ok scr1).mono ?_
  rintro s2 ⟨-, hg2, hr2, hw2, hf2⟩
  have hg12 : ∀ r, r ≠ .rax → r ≠ .r11 → s2.gpr r = s.gpr r :=
    fun r h0 h11 => (hg2 r h0).trans (hg1 r h11)
  have scr2 : Scratch s2 (s.gpr .rcx) := ⟨hg12 .rcx (by decide) (by decide), hw2 ▸ scr1.wr⟩
  have hf12 := hf1.trans hf2
  have inputs : Inputs s2 (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨hg12 .rdi (by decide) (by decide), hg12 .rsi (by decide) (by decide),
      by rw [hr2, hw2, hr1, hw1]; simp [hrd], by rw [hr2, hw2, hr1, hw1]; simp [hrd], hx, hy⟩
  apply WP.seq
  refine (body_ok scr2 inputs (out := s.gpr .rdx) (hg12 .rdx (by decide) (by decide))
    (by rw [hw2, hw1, hwr]; simp) hout.symm).mono ?_
  rintro s3 ⟨hpost, hf3, hg3, hr3, hw3, -⟩
  refine WP.of_runBlock ⟨s3, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec], ?_⟩
  have scr3 : Scratch s3 (s.gpr .rcx) := ⟨(hg3 .rcx (by decide)).trans scr2.reg, hw3 ▸ scr2.wr⟩
  have h113 : s3.gpr .r11 = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [hg3 .r11 (by decide), hg2 .r11 (by decide), h11]
  refine (restore_ok scr3 (by rw [h113]; exact ldmxcsr_ok _)).mono ?_
  rintro t ⟨-, hgt, -, -, hft⟩
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · change blockAt t.mem (s.gpr .rdx) = Spec.Argon2.compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
    rw [blockAt_mx hft hout, hpost, blockAt_mx hf12 hx, blockAt_mx hf12 hy]
  · have h0 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h1 : r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hgt, hg3 r h0, hg12 r h0 h1]
  · have hmx : ∀ {m m' : Mem}, Frame [mxR (s.gpr .rcx)] m m' →
        Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] m m' := fun h =>
      h.sub fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨_, by simp, mxR_sub _⟩
    rw [hwr]
    exact ((hmx hf12).trans hf3).trans (hmx hft)

theorem compress_ctl : ctlOk Impl.Argon2.X86_64.Avx512.compress = true := by lit_decide

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.Avx512.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_ctl compress_ctl he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.Avx512.compress :=
  VG.Taint.constantTime (A := taint) initialTaint (fun _ _ hs ht hp => initial_agree hs ht hp)
    (by taint_decide)

/-- `vg_argon2_compress_avx512` meets the contract of `vg_argon2_compress`. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.Avx512.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies

end VG.Proof.Argon2.X86_64.Avx512
