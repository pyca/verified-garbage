module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-!
# The RSA public-key operation on PPC64LE: correctness

`publicChecked` saves the nonvolatile registers in the working space's
header, sets up the arrays (`front_ok`), runs `mid_ok` and restores the
registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

/-- The public data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .r3, (s.gpr .r4).toNat, s.gpr .r5, s.gpr .r7, (s.gpr .r8).toNat, s.gpr .r9, stackArg s 0,
    (stackArg s 1).toNat * 8⟩

theorem sep_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) :
    ∀ x, ofs A x < n → Z ≤ ofs S x := fun x hx => by
  by_contra hc
  exact h x (by simp only [Region.Contains]; simp only [ofs] at hx; omega)
    (by simp only [Region.Contains]; simp only [ofs] at hc; omega)

theorem ne_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) (hn : n ≤ 2 ^ 64) :
    ∀ i < n, ∀ x, ofs S x < Z → off A i ≠ x := fun i hi x hx e => by
  subst e
  exact h _ (Offset.contains_base (d := i) _ (by omega) (by omega))
    (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega)

theorem saved_ne11 : ∀ i < 16, PublicChecked.saved i ≠ .r11 := by decide

/-- `save` and `setup`: `Mid`, with the nonvolatile registers saved. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block (PublicChecked.save ++ setup)) s fun s₃ =>
      Mid (dataOf s) s₃ ∧ (∀ i < 16, s₃.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep (([.r11, .r23] : List Reg) ++ ([.r10, .r11, .r27, .r28, .r29] : List Reg)) s s₃ ∧
        Frame [savR (savW (stackArg s 0))] s.mem s₃.mem := by
  obtain ⟨hsp, hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  unfold PublicChecked.save
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩) fun s₁ ⟨⟨a11, m1, sp1⟩, k1⟩ => ?_)
  have hin : ∀ i < 16, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [a11, k1.wr, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.block_append (WP.mono (save_ok s₁ hin) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have e4 : s₂.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat :=
    (k12.gpr .r4 (by decide)).trans (by simp)
  refine WP.mono (setup_ok (k := (s.gpr .r4).toNat) e4 (hS.r23.trans a11) hk') fun s₃ ⟨⟨j27, j28, j11, j29, j10, jm⟩, k₃⟩ => ?_
  have k := k12.trans k₃
  have hrd₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k.rd, k.wr]
  have hw : ((s.gpr .r4).toNat + 7) / 8 = (dataOf s).w := rfl
  have e8 : slot (dataOf s).w 8 = hdrBytes + 8 * (8 * ((dataOf s).w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have hwd : (dataOf s).w = ((s.gpr .r4).toNat + 7) / 8 := rfl
  have hk1 : (s.gpr .r4).toNat < 2 ^ 64 := (s.gpr .r4).isLt
  refine ⟨⟨Scr.of_mem (by rw [k.wr, hwr]; simp [dataOf]) nwS, Scr.of_mem (by rw [k.wr, hwr]; simp [dataOf]) nwO,
    hk, hk', by show slot (((s.gpr .r4).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8; unfold slot; rw [hh]; omega,
    hL1, hLk, by show (s.gpr .r5).toNat + 16 * (((s.gpr .r4).toNat + 7) / 8) ≤ 2 ^ 64; omega,
    fun x hx => sep_of_disjoint dPS x (by
      change ofs (s.gpr .r5) x < 16 * (((s.gpr .r4).toNat + 7) / 8) at hx; omega), sep_of_disjoint dOS,
    ne_of_disjoint dES (Nat.le_of_lt (s.gpr .r8).isLt),
    fun i hi => ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .r10).isLt) i (by change i < (s.gpr .r4).toNat at hi; omega),
    fun i hi => ⟨⟨s.gpr .r5, (s.gpr .r6).toNat * 8⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < 2 * (((s.gpr .r4).toNat + 7) / 8) at hi; omega) (by
      change i < 2 * (((s.gpr .r4).toNat + 7) / 8) at hi; omega)⟩,
    fun i hi => ⟨⟨s.gpr .r7, (s.gpr .r8).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .r8).toNat at hi; omega) (by change i < (s.gpr .r8).toNat at hi; omega)⟩,
    fun i hi => ⟨⟨s.gpr .r9, (s.gpr .r10).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .r4).toNat at hi; omega) (by change i < (s.gpr .r4).toNat at hi; omega)⟩,
    by rw [k.gpr .r5 (by decide)]; simp [dataOf, off], by rw [k.gpr .r7 (by decide)]; simp [dataOf, off],
    by rw [k.gpr .r8 (by decide)]; simp [dataOf], k.gpr .r9 (by decide),
    (k₃.gpr .r23 (by decide)).trans (hS.r23.trans a11),
    by rw [j27, k12.gpr .r3 (by decide)]; simp [dataOf, off], j28, j10, j11, j29⟩, fun i hi => ?_, k, ?_⟩
  · rw [jm, ← a11, hS.saved i hi, k1.gpr _ fun h => saved_ne11 i hi (List.mem_singleton.mp h)]
  · rw [jm, ← m1, ← a11]; exact hS.frame

/-- `e`'s bytes, apart from the saved registers. -/
theorem front_e {s s₃ : State} (h : fnContract.pre s) (fr : Frame [savR (savW (stackArg s 0))] s.mem s₃.mem) :
    Spec.Rsa.bytesAt s₃.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, dES, -, -, -, -, -, -, nwS, -, -, -, -, -, hsl⟩ := h
  simp only [Spec.Rsa.publicScratchWords] at hsl
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega)
  refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .r8).isLt fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact dES.sub_right savR_sub

theorem pres_cases : ∀ r ∈ preserved, (∀ i < 16, r ≠ PublicChecked.saved i) →
    r ∉ midRegs ∧ r ∉ (([.r11, .r23] : List Reg) ++ ([.r10, .r11, .r27, .r28, .r29] : List Reg)) := by
  decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa publicChecked s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa publicChecked s fun t => abiPreserved s t ∧ fnContract.post s t
  have hpre := h
  obtain ⟨hsp, hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hh : hdrBytes = 256 := rfl
  -- The saved words lie in the working space, below the arrays.
  have sav_sub : ∀ i < 16, Region.Sub ⟨off (savW (stackArg s 0)) (8 * i), 8⟩ ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    fun i hi => by
      show Region.Sub ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩ _
      rw [Offset.add_add]; exact Offset.sub_base _ (by omega)
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega)
  unfold publicChecked
  refine WP.seq (WP.mono (front_ok hpre) fun s₃ ⟨hM, hsv, k3, fr3⟩ => ?_)
  refine mid_ok hM fun t ⟨hpost, hfr, kt⟩ => ?_
  have hin : ∀ i < 16, InRegions t.wr (off (savW (stackArg s 0)) (8 * i)) 8 := fun i hi => by
    rw [kt.wr, k3.wr, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩
  have hsav : ∀ i < 16, t.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
    fun i hi => by
      rw [hfr.readW (r := ⟨off (savW (stackArg s 0)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
      · exact hsv i hi
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · show Region.Disjoint ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩
            ⟨stackArg s 0 + BitVec.ofNat 64 (slot (dataOf s).w 0), _⟩
          rw [Offset.add_add]
          exact Offset.disjoint _ (Or.inl (by unfold slot; rw [hh]; omega)) (by omega)
            (by have := hM.hZ; unfold slot at this ⊢; rw [hh] at this ⊢; show _ ≤ 2 ^ 64
                have := hM.scr.nowrap; omega)
        · exact (dOS.symm.sub_left (sav_sub i hi))
  refine WP.mono (restore_ok t (S := stackArg s 0) (v := fun i => s.gpr (PublicChecked.saved i))
    (by rw [kt.gpr .r23 (by decide)]; exact hM.r23) hin hsav)
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 16, r = PublicChecked.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 16, r ≠ PublicChecked.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_cases r hr hn
      rw [uot r hn, kt.gpr r h1, k3.gpr r h2]
  · rw [usp, kt.sp, k3.sp]
  · rw [ulr, kt.lr, k3.lr]
  · intro nB hl hpp
    rw [uot .r3 (by decide), um]
    have hP : Spec.Rsa.wordsAt s₃.mem (s.gpr .r5) (2 * (dataOf s).w) =
        Spec.Rsa.wordsAt s.mem (s.gpr .r5) (s.gpr .r6).toNat := by
      rw [show 2 * (dataOf s).w = (s.gpr .r6).toNat by show 2 * (((s.gpr .r4).toNat + 7) / 8) = _; omega]
      refine VG.Proof.Rsa.wordsAt_frame fr3 (by omega) fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dPS.sub_left (Region.sub_prefix (by omega))).sub_right savR_sub
    have hE := front_e hpre fr3
    have hX : Spec.Rsa.bytesAt s₃.mem (s.gpr .r9) (s.gpr .r4).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r4).toNat := by
      refine VG.Proof.Rsa.rsa_bytes_frame fr3 (s.gpr .r4).isLt fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dXS.sub_left (Region.sub_prefix (by omega))).sub_right savR_sub
    have := hpost nB hl (by rw [hpp]; exact congrArg some hP.symm)
    simp only [dataOf] at this
    rw [hE, hX] at this
    exact this

end VG.Proof.Bignum.PPC64LE.Pub
