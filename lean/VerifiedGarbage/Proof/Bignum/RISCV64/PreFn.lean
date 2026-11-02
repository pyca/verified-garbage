module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: the function

`fn_correct`: `precompute` saves the callee-saved registers it uses in the
working space's header, runs `core` from the state `setup` leaves (`C1`),
and restores them, meeting `fnContract.post` and the calling convention.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pre

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64.Precompute VG.Proof.Mont
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-- The saved words are in the working space. -/
theorem sav_in {S : Addr} {Z : Nat} (hZ : 200 ≤ Z) {i : Nat} (hi : i < 9) :
    (⟨S, Z⟩ : Region).Contains (off (savW S) (8 * i)) 8 := by
  rw [off, Offset.add_add]
  exact Offset.contains_base S (by omega_arith) (by omega_arith)

theorem sav_eq (S : Addr) (i : Nat) : off (savW S) (8 * i) = off S (128 + 8 * i) := by
  rw [off, off, Offset.add_add]

theorem pres_not_core : ∀ r ∈ preserved, (∀ i < 9, r ≠ saved i) →
    r ∉ [Reg.a1, .a2, .a5, .a6, .a7, .s5, .s7, .s8, .t0] ++ coreRegs ∧ r ≠ .s6 := by
  decide

/-- The data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .a0, s.gpr .a2, s.gpr .a4, (s.gpr .a3).toNat, (s.gpr .a5).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `save` and `setup`: `C1`, with the callee-saved registers saved. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block (Precompute.save ++ setup)) s fun s₂ =>
      C1 (dataOf s) s₂ ∧ (∀ i < 9, s₂.mem.readW (off (savW (s.gpr .a4)) (8 * i)) 64 = s.gpr (saved i)) ∧
        Keep (([.s6] : List Reg) ++ ([.a1, .a2, .a5, .a6, .a7, .s5, .s7, .s8, .t0] : List Reg)) s s₂ := by
  obtain ⟨hrd, hwr, dPN, dPS, dNS, nwP, nwN, nwS, ⟨hk, hk'⟩, hpl, hsl, alP, alS⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hs : Scr s (s.gpr .a4) ((s.gpr .a5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .a4)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, sav_in (by omega_arith) hi⟩
  have hal : ∀ i < 9, (off (savW (s.gpr .a4)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [sav_eq]; exact hs.al8 (by omega_arith) (by omega_arith)
  refine WP.block_append (WP.mono (save_ok s hin hal) fun s₁ hS => ?_)
  have hk1 := hS.keep
  have e3 : s.gpr .a3 = BitVec.ofNat 64 (s.gpr .a3).toNat := (ofNat_toNat64 _).symm
  refine WP.mono (setup_ok (P := s.gpr .a0) (N := s.gpr .a2) (k := (s.gpr .a3).toNat) (hs.congr hk1.2.2)
    (hk1.gpr (by decide)) (hk1.gpr (by decide)) ((hk1.gpr (by decide)).trans e3) hS.s6 (by omega_arith)
    hk' (by omega_arith)) fun s₂ ⟨⟨j5, j7, j8, j0, ja7, ja2, ja5, ja6, jm⟩, k₂⟩ => ?_
  have k12 := hk1.trans k₂
  have hlen : 16 * (((s.gpr .a3).toNat + 7) / 8) = (s.gpr .a1).toNat * 8 := by omega_arith
  have hmem : (⟨s.gpr .a0, 16 * (((s.gpr .a3).toNat + 7) / 8)⟩ : Region) ∈ s₂.wr := by
    rw [k12.2.2, hwr, hlen]; simp
  -- Only the working space changed.
  have fr₂ : Frame [scrR s] s.mem s₂.mem := by
    rw [jm]
    refine (hS.frame.sub fun r hr => ⟨scrR s, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by simp; omega_arith) (by decide))
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.sub_base _ (by omega_arith)
  simp only [dataOf]
  refine ⟨⟨⟨hs.congr k12.2.2, Scr.of_mem hmem (by dsimp only [PD.w]; omega_arith) alP, hk, hk',
    by dsimp only [PD.w]; unfold slot hdrBytes; omega_arith,
    fun x hx => ?_, VG.Proof.Bignum.bytesAt_length _ _ _, j5, ja7, ja2, ja5, ja6, j0,
    (k₂.gpr (r := .s6) (by decide)).trans hS.s6, (k12.gpr (r := .s8) (by decide)).trans e3, j7⟩,
    fun i hi => by
      dsimp only at hi ⊢
      exact ⟨nR s, by rw [k12.2.1, hrd]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi x hx e => ?_, fun i hi => ?_⟩, fun i hi => ?_, k12⟩
  · dsimp only [PD.w] at hx ⊢
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith)
  · dsimp only at hi hx
    subst e
    exact dNS _ (Offset.contains_base (d := i) _ (by omega_arith) (by omega_arith))
      (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega_arith)
  · dsimp only at hi ⊢
    simp only [VG.Proof.Bignum.bytesAt_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact fr₂.bytes (R := nR s) (by simpa using dNS) (by show (s.gpr .a3).toNat ≤ 2 ^ 64; omega_arith) hi
  · have ea : off (savW (s.gpr .a4)) (8 * i) = s.gpr .a4 + BitVec.ofNat 64 (128 + 8 * i) := by
      rw [off, Offset.add_add]
    rw [jm, Mem.readW_writeW_sep ?_ (by decide)]
    · exact hS.saved i hi
    · rw [ea, off]; exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa precompute s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa precompute s fun t => abiPreserved s t ∧ fnContract.post s t
  suffices main : WP isa precompute s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ fnContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hpre := h
  obtain ⟨_, hwr, _, dPS, _, nwP, _, nwS, ⟨hk, hk'⟩, hpl, hsl, _, alS⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hs : Scr s (s.gpr .a4) ((s.gpr .a5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .a4)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, sav_in (by omega_arith) hi⟩
  have hal : ∀ i < 9, (off (savW (s.gpr .a4)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [sav_eq]; exact hs.al8 (by omega_arith) (by omega_arith)
  unfold precompute
  refine WP.seq (WP.mono (front_ok hpre) fun s₂ ⟨hC, hsv, k12⟩ => ?_)
  refine WP.seq (WP.mono (core_C1 hC) fun t ⟨⟨hout, hfr⟩, kt⟩ => ?_)
  dsimp only [dataOf, PD.w] at hout hfr
  have hsav : ∀ i < 9, t.mem.readW (off (savW (s.gpr .a4)) (8 * i)) 64 = s.gpr (saved i) := fun i hi => by
    have ea : off (savW (s.gpr .a4)) (8 * i) = s.gpr .a4 + BitVec.ofNat 64 (128 + 8 * i) := by
      rw [off, Offset.add_add]
    rw [hfr.readW (r := ⟨off (savW (s.gpr .a4)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
    · exact hsv i hi
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [ea]; exact Offset.disjoint _ (by unfold hdrBytes; omega_arith) (by omega_arith) (by unfold hdrBytes; omega_arith)
      · refine Region.Disjoint.sub_left (r₁ := scrR s)
          (fun a h1 h2 => dPS a (by simp only [Region.Contains] at h2 ⊢; omega_arith) h1) ?_
        rw [ea]; exact Offset.sub_base _ (by omega_arith)
  refine WP.mono (restore_ok t (S := s.gpr .a4) (v := fun i => s.gpr (saved i))
    (by rw [kt.gpr (r := .s6) (by decide)]; exact hC.base.s6)
    (fun i hi => by rw [kt.2.2, k12.2.2]; exact hin i hi) hal hsav)
    fun u ⟨urs, uot, um, _, _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 9, r = saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 9, r ≠ saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_core r hr hn
      rw [uot r hn, kt.gpr fun h => h1 (List.mem_append_right _ h),
        k12.gpr fun h => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · exact h2 h
          · exact h1 (List.mem_append_left _ (by simpa using h))]
  · rw [uot .ra (by decide), kt.gpr (by decide), k12.gpr (by decide)]
  · show preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (s.gpr .a0) (s.gpr .a1).toNat
      (u.gpr .a0) u.mem
    rw [uot .a0 (by decide), um, hpl]
    exact hout

end VG.Proof.Bignum.RISCV64.Pre
