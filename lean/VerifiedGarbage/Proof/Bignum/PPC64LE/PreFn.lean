module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreSave
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The precomputed values of an RSA modulus on PPC64LE: the function

`vg_rsa_public_precompute(pre = r3, pre_len = r4, n = r5, n_len = r6,
scratch = r7, scratch_len = r8)` (`fnContract`): `precompute` saves the
nonvolatile registers in the working space's header, sets up the arrays
(`setup_ok`), runs `core_ok` and restores the registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

theorem ofNat_add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_shl3 (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_shl1 (a : Nat) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `setup`, `n` at `r5`, `k` in `r6` and the working space at `r21`. -/
theorem setup_ok {s : State} {P N S : Addr} {Z k : Nat} (hs : Scr s S Z) (h3 : s.gpr .r3 = P)
    (h5 : s.gpr .r5 = N)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (h21 : s.gpr .r21 = S) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hZ : 56 ≤ Z) :
    WP isa (.block setup) s fun t =>
      (t.gpr .r19 = P ∧ t.gpr .r12 = N ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r5 = off S (slot ((k + 7) / 8) 1) ∧
        t.gpr .r8 = off S (slot ((k + 7) / 8) 2) ∧ t.gpr .r9 = off S (slot ((k + 7) / 8) 3) ∧
        t.mem = s.mem.writeW (off S 48) (BitVec.ofNat 64 ((k + 7) / 8))) ∧
      Keep [.r4, .r5, .r8, .r9, .r10, .r11, .r12, .r19] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h3, h5, h6, h21, BitVec.add_zero, ofNat_add7_shr3 k (by omega), ofNat_shl3, ofNat_shl1, sW, hdrBytes, Nat.reduceMul, hs.st (d := 48) (n := 8) (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat] <;>
    congr 2 <;> omega

/-- `pre`, `pre_len` words at `r3`. -/
abbrev preR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat * 8⟩

/-- `n`, `n_len` bytes at `r5`. -/
abbrev nR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩

/-- The working space, `scratch_len` words at `r7`. -/
abbrev scrR (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩

/-- `vg_rsa_public_precompute(pre = r3, pre_len = r4, n = r5, n_len = r6,
scratch = r7, scratch_len = r8)`. -/
def fnContract : Contract isa where
  pre s :=
    let k := (s.gpr .r6).toNat
    s.rd = [nR s] ∧ s.wr = [preR s, scrR s] ∧ (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (scrR s) ∧
      (nR s).Disjoint (scrR s) ∧ (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + k ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      64 ≤ k ∧ k ≤ 1024 ∧ (s.gpr .r4).toNat = 2 * ((k + 7) / 8) ∧ 8 * ((k + 7) / 8) + 48 ≤ (s.gpr .r8).toNat
  post s s' :=
    preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (s.gpr .r3) (s.gpr .r4).toNat (s'.gpr .r3)
      s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat

/-- The saved words are in the working space. -/
theorem sav_in {S : Addr} {Z : Nat} (hZ : 200 ≤ Z) {i : Nat} (hi : i < 9) :
    (⟨S, Z⟩ : Region).Contains (off (savW S) (8 * i)) 8 := by
  rw [off, Offset.add_add]
  exact Offset.contains_base S (by omega) (by omega)

theorem pres_not_core : ∀ r ∈ preserved, (∀ i < 9, r ≠ saved i) →
    r ∉ [Reg.r4, .r5, .r8, .r9, .r10, .r11, .r12, .r19] ++ coreRegs ∧ r ≠ .r21 := by
  decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa precompute s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa precompute s fun t => abiPreserved s t ∧ fnContract.post s t
  obtain ⟨hrd, hwr, dPN, dPS, dNS, nwP, nwN, nwS, hk, hk', hpl, hsl⟩ := h
  have hs : Scr s (s.gpr .r7) ((s.gpr .r8).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .r7)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, sav_in (by omega) hi⟩
  unfold precompute
  refine WP.seq (WP.block_append (WP.mono (save_ok s hin) fun s₁ hS => ?_))
  have hk1 := hS.keep
  have e6 : s.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := (ofNat_toNat64 _).symm
  refine WP.mono (setup_ok (P := s.gpr .r3) (N := s.gpr .r5) (k := (s.gpr .r6).toNat) (hs.congr hk1.wr)
    (hk1.gpr _ (by decide)) (hk1.gpr _ (by decide)) ((hk1.gpr _ (by decide)).trans e6) hS.r21 (by omega)
    hk' (by omega)) fun s₂ ⟨⟨j19, j12, j11, j10, j5, j8, j9, jm⟩, k₂⟩ => ?_
  have k12 := hk1.trans k₂
  have hlen : 16 * (((s.gpr .r6).toNat + 7) / 8) = (s.gpr .r4).toNat * 8 := by omega
  have hmem : (⟨s.gpr .r3, 16 * (((s.gpr .r6).toNat + 7) / 8)⟩ : Region) ∈ s₂.wr := by
    rw [k12.wr, hwr, hlen]; simp
  have hp : Scr s₂ (s.gpr .r3) (16 * (((s.gpr .r6).toNat + 7) / 8)) := Scr.of_mem hmem (by omega)
  -- Only the working space changed so far.
  have fr₂ : Frame [scrR s] s.mem s₂.mem := by
    rw [jm]
    refine (hS.frame.sub fun r hr => ⟨scrR s, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by simp; omega) (by decide))
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.sub_base _ (by omega)
  have hbytes : Spec.Rsa.bytesAt s₂.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => fr₂.bytes (R := nR s) (by simpa using dNS) (by show (s.gpr .r6).toNat ≤ 2 ^ 64; omega)
      (List.mem_range.mp hi)
  refine WP.seq (WP.mono (core_ok (hs.congr k12.wr) hp rfl hk hk' (by unfold slot hdrBytes; omega) j19
    ((k12.gpr .r6 (by decide)).trans e6) j12 j10 j5 j8 j9 j11
    (fun i hi => ⟨nR s, by rw [k12.rd, hrd]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi x hx e => by
      subst e
      exact dNS _ (Offset.contains_base (d := i) _ (by omega) (by omega)) (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega))
    (fun x hx => by
      by_contra hc
      exact dPS x (by simp only [Region.Contains]; simp only [ofs] at hc; omega)
        (by simp only [Region.Contains]; simp only [ofs] at hx; omega)))
    fun t ⟨⟨hout, hfr⟩, kt⟩ => ?_)
  have hsav : ∀ i < 9, t.mem.readW (off (savW (s.gpr .r7)) (8 * i)) 64 = s.gpr (saved i) := fun i hi => by
    have ea : off (savW (s.gpr .r7)) (8 * i) = s.gpr .r7 + BitVec.ofNat 64 (128 + 8 * i) := by
      rw [off, Offset.add_add]
    rw [hfr.readW (r := ⟨off (savW (s.gpr .r7)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide), jm,
      Mem.readW_writeW_sep ?_ (by decide)]
    · exact hS.saved i hi
    · rw [ea, off]; exact Offset.sep _ (by omega) (by omega) (by omega)
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [ea]; exact Offset.disjoint _ (by unfold hdrBytes; omega) (by omega) (by unfold hdrBytes; omega)
      · refine Region.Disjoint.sub_left (r₁ := scrR s) (fun a h1 h2 => dPS a (by simp only [Region.Contains] at h2 ⊢; omega) h1) ?_
        rw [ea]; exact Offset.sub_base _ (by omega)
  refine WP.mono (restore_ok t (S := s.gpr .r7) (v := fun i => s.gpr (saved i))
    (by rw [kt.gpr .r21 (by decide), k₂.gpr .r21 (by decide)]; exact hS.r21)
    (fun i hi => by rw [kt.wr, k12.wr]; exact hin i hi) hsav)
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 9, r = saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 9, r ≠ saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_core r hr hn
      rw [uot r hn, kt.gpr r fun h => h1 (List.mem_append_right _ h),
        k₂.gpr r fun h => h1 (List.mem_append_left _ h), hk1.gpr r (by simpa using h2)]
  · rw [usp, kt.sp, k12.sp]
  · rw [ulr, kt.lr, k12.lr]
  · show preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (s.gpr .r3) (s.gpr .r4).toNat
      (u.gpr .r3) u.mem
    rw [uot .r3 (by decide), um, hpl, ← hbytes]
    exact hout

end VG.Proof.Bignum.PPC64LE.Pre
