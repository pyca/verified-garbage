module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSave
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Bignum.PPC64LE.PreSave`, which only this module used -/

section

/-!
# The precomputed values of an RSA modulus on PPC64LE: saving and restoring

`save` stores `r14`–`r22` in the working space's header words 16–24, through
`r7`, and copies its address into `r21`; `restore` loads them back through
`r21`, `r21` last. The words are `MontSave.lean`'s scratch buffer, at
`S + 128`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Proof.Bignum.PPC64LE (savR sav_contains sav_sep saved_inj saved_ne saved_8)

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 128

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (saveOff i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]; simp only [saveOff, sFn]; congr 2; omega_using []

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  frame : Frame [savR (savW (s₀.gpr .r7))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .r7)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 9, InRegions s₀.wr (off (savW (s₀.gpr .r7)) (8 * i)) 8)
    {n : Nat} (hn : n < 9) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .r7 (saveOff n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .r7 = s₀.gpr .r7 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r7 ≠ .r0 by decide) (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by
      simp only [saveOff, sFn]; omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.r21] s₀ s
  r21 : s.gpr .r21 = s₀.gpr .r7
  frame : Frame [savR (savW (s₀.gpr .r7))] s₀.mem s.mem
  saved : ∀ i < 9, s.mem.readW (off (savW (s₀.gpr .r7)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : ∀ i < 9, InRegions s₀.wr (off (savW (s₀.gpr .r7)) (8 * i)) 8) :
    WP isa (.block Precompute.save) s₀ (Saved s₀) := by
  rw [Precompute.save]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hk h) 9 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .r7 = s₀.gpr .r7 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show Reg.r7 ≠ .r0 by decide)
    (show 0 < 2 ^ 15 by decide), BitVec.add_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr, h.sp, h.lr⟩, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  r21 : s.gpr .r21 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 9, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 9, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 9, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 8) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .r21 (saveOff n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 (saveOff n)) 8 := by
    rw [h.rd, h.wr, h.r21, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn21 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show saveOff n < 2 ^ 15 ∧ (saveOff n) % 4 = 0 by
      simp only [saveOff, sFn]; omega_using [hn]) hin, Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn21)]; exact h.r21
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `r21`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .r21 = S)
    (hsin : ∀ i < 9, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hsav : ∀ i < 9, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block Precompute.restore) sB fun s =>
      (∀ i < 9, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 9, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp ∧ s.lr = sB.lr := by
  rw [Precompute.restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hsav hk h) 8 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r21 + BitVec.ofNat 64 (saveOff 8)) 8 := by
    rw [h.rd, h.wr, h.r21, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 8 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hv : s.mem.readW (S + BitVec.ofNat 64 (saveOff 8)) 64 = v 8 := by
    rw [h.mem, saveOff_eq]; exact hsav 8 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r21 ≠ .r0 by decide) (show saveOff 8 < 2 ^ 15 ∧ saveOff 8 % 4 = 0 by decide) hin,
    Option.some.injEq, exists_eq_left', h.r21, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_8, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_8 ▸ hr 8 (by decide))]
    exact h.others r hr

end VG.Proof.Bignum.PPC64LE.Pre

end

end


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
  omega_arith

theorem ofNat_shl3 (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem ofNat_shl1 (a : Nat) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

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
  prun [h3, h5, h6, h21, BitVec.add_zero, ofNat_add7_shr3 k (by omega_arith), ofNat_shl3, ofNat_shl1, sW, hdrBytes, Nat.reduceMul, hs.st (d := 48) (n := 8) (by omega_arith)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat] <;>
    congr 2 <;> omega_arith

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
    s.rd = [nR s] ∧ s.wr = [preR s, scrR s] ∧ (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (scrR s) ∧
      (nR s).Disjoint (scrR s) ∧ (s.gpr .r3).toNat + (s.gpr .r4).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r6).toNat ∧ (s.gpr .r4).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat ∧
      Spec.Rsa.publicScratchWords (s.gpr .r6).toNat ≤ (s.gpr .r8).toNat
  post s s' :=
    preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (s.gpr .r3) (s.gpr .r4).toNat (s'.gpr .r3)
      s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat).map (·.toNat) ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8

/-- The saved words are in the working space. -/
theorem sav_in {S : Addr} {Z : Nat} (hZ : 200 ≤ Z) {i : Nat} (hi : i < 9) :
    (⟨S, Z⟩ : Region).Contains (off (savW S) (8 * i)) 8 := by
  rw [off, Offset.add_add]
  exact Offset.contains_base S (by omega_arith) (by omega_arith)

theorem pres_not_core : ∀ r ∈ preserved, (∀ i < 9, r ≠ saved i) →
    r ∉ [Reg.r4, .r5, .r8, .r9, .r10, .r11, .r12, .r19] ++ coreRegs ∧ r ≠ .r21 := by
  decide

/-- The data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .r3, s.gpr .r5, s.gpr .r7, (s.gpr .r6).toNat, (s.gpr .r8).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat⟩

/-- `save` and `setup`: `C1`, with the nonvolatile registers saved. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block (Precompute.save ++ setup)) s fun s₂ =>
      C1 (dataOf s) s₂ ∧ (∀ i < 9, s₂.mem.readW (off (savW (s.gpr .r7)) (8 * i)) 64 = s.gpr (saved i)) ∧
        Keep (([.r21] : List Reg) ++ ([.r4, .r5, .r8, .r9, .r10, .r11, .r12, .r19] : List Reg)) s s₂ := by
  obtain ⟨hrd, hwr, dPN, dPS, dNS, nwP, nwN, nwS, ⟨hk, hk'⟩, hpl, hsl⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hs : Scr s (s.gpr .r7) ((s.gpr .r8).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .r7)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, sav_in (by omega_arith) hi⟩
  refine WP.block_append (WP.mono (save_ok s hin) fun s₁ hS => ?_)
  have hk1 := hS.keep
  have e6 : s.gpr .r6 = BitVec.ofNat 64 (s.gpr .r6).toNat := (ofNat_toNat64 _).symm
  refine WP.mono (setup_ok (P := s.gpr .r3) (N := s.gpr .r5) (k := (s.gpr .r6).toNat) (hs.congr hk1.wr)
    (hk1.gpr _ (by decide)) (hk1.gpr _ (by decide)) ((hk1.gpr _ (by decide)).trans e6) hS.r21 (by omega_arith)
    hk' (by omega_arith)) fun s₂ ⟨⟨j19, j12, j11, j10, j5, j8, j9, jm⟩, k₂⟩ => ?_
  have k12 := hk1.trans k₂
  have hlen : 16 * (((s.gpr .r6).toNat + 7) / 8) = (s.gpr .r4).toNat * 8 := by omega_arith
  have hmem : (⟨s.gpr .r3, 16 * (((s.gpr .r6).toNat + 7) / 8)⟩ : Region) ∈ s₂.wr := by
    rw [k12.wr, hwr, hlen]; simp
  -- Only the working space changed.
  have fr₂ : Frame [scrR s] s.mem s₂.mem := by
    rw [jm]
    refine (hS.frame.sub fun r hr => ⟨scrR s, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by simp; omega_arith) (by decide))
    simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.sub_base _ (by omega_arith)
  simp only [dataOf]
  refine ⟨⟨⟨hs.congr k12.wr, Scr.of_mem hmem (by dsimp only [PD.w]; omega_arith), hk, hk',
    by dsimp only [PD.w]; unfold slot hdrBytes; omega_arith,
    fun x hx => ?_, bytesAt_length _ _ _, j19, j10, j5, j8, j9, j11,
    (k₂.gpr .r21 (by decide)).trans hS.r21, (k12.gpr .r6 (by decide)).trans e6, j12⟩,
    fun i hi => by
      dsimp only at hi ⊢
      exact ⟨nR s, by rw [k12.rd, hrd]; simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
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
    simp only [bytesAt_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact fr₂.bytes (R := nR s) (by simpa using dNS) (by show (s.gpr .r6).toNat ≤ 2 ^ 64; omega_arith) hi
  · have ea : off (savW (s.gpr .r7)) (8 * i) = s.gpr .r7 + BitVec.ofNat 64 (128 + 8 * i) := by
      rw [off, Offset.add_add]
    rw [jm, Mem.readW_writeW_sep ?_ (by decide)]
    · exact hS.saved i hi
    · rw [ea, off]; exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa precompute s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa precompute s fun t => abiPreserved s t ∧ fnContract.post s t
  have hpre := h
  obtain ⟨_, hwr, _, dPS, _, nwP, _, nwS, ⟨hk, hk'⟩, hpl, hsl⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hin : ∀ i < 9, InRegions s.wr (off (savW (s.gpr .r7)) (8 * i)) 8 := fun i hi =>
    ⟨scrR s, by rw [hwr]; simp, sav_in (by omega_arith) hi⟩
  unfold precompute
  refine WP.seq (WP.mono (front_ok hpre) fun s₂ ⟨hC, hsv, k12⟩ => ?_)
  refine WP.seq (WP.mono (core_C1 hC) fun t ⟨⟨hout, hfr⟩, kt⟩ => ?_)
  dsimp only [dataOf, PD.w] at hout hfr
  have hsav : ∀ i < 9, t.mem.readW (off (savW (s.gpr .r7)) (8 * i)) 64 = s.gpr (saved i) := fun i hi => by
    have ea : off (savW (s.gpr .r7)) (8 * i) = s.gpr .r7 + BitVec.ofNat 64 (128 + 8 * i) := by
      rw [off, Offset.add_add]
    rw [hfr.readW (r := ⟨off (savW (s.gpr .r7)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
    · exact hsv i hi
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [ea]; exact Offset.disjoint _ (by unfold hdrBytes; omega_arith) (by omega_arith) (by unfold hdrBytes; omega_arith)
      · refine Region.Disjoint.sub_left (r₁ := scrR s)
          (fun a h1 h2 => dPS a (by simp only [Region.Contains] at h2 ⊢; omega_arith) h1) ?_
        rw [ea]; exact Offset.sub_base _ (by omega_arith)
  refine WP.mono (restore_ok t (S := s.gpr .r7) (v := fun i => s.gpr (saved i))
    (by rw [kt.gpr .r21 (by decide)]; exact hC.base.r21)
    (fun i hi => by rw [kt.wr, k12.wr]; exact hin i hi) hsav)
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hs' : ∃ i < 9, r = saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 9, r ≠ saved i := fun i hi e => hs' ⟨i, hi, e⟩
      obtain ⟨h1, h2⟩ := pres_not_core r hr hn
      rw [uot r hn, kt.gpr r fun h => h1 (List.mem_append_right _ h),
        k12.gpr r fun h => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h
          · exact h2 h
          · exact h1 (List.mem_append_left _ (by simpa using h))]
  · rw [usp, kt.sp, k12.sp]
  · rw [ulr, kt.lr, k12.lr]
  · show preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (s.gpr .r3) (s.gpr .r4).toNat
      (u.gpr .r3) u.mem
    rw [uot .r3 (by decide), um, hpl]
    exact hout

end VG.Proof.Bignum.PPC64LE.Pre
