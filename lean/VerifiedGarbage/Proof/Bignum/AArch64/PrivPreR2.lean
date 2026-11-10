module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.Rsa.AArch64.PrivPre
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_private_precompute` on AArch64: `R_X² mod X`

`r2X` in a prime's workspace: the number 1, doubled (`addMod`) `128 w_X` times modulo
`X` (`r2Step_ok`, counted by `count_loop`), is `2^(128 w_X) mod X`; and
`maskCopy`, a copy of words and-ed with a mask (`maskCopy_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Rsa.AArch64.Crt (copyArr addMod)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep count_loop)

/-- What `r2X` writes in the workspace: the accumulator, the temporary,
`Y` and the count in `sBit`. -/
def r2Ranges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * Crt.sBit, 8)]

/-- A workspace's header is kept by a change outside it, within an array. -/
theorem Hdr.of_outside {m m' : Mem} {G : Addr} {w : Nat} {minv : BitVec 64} {j n : Nat} (hH : Hdr m G w minv)
    (ho : Outside G (slot w j) n m m') : Hdr m' G w minv := by
  have hh : ∀ i < 32, word m' G (8 * i) = word m G (8 * i) := fun i hi =>
    ho.word (Or.inl (hdr_lt_slot w j hi)) (by omega_arith)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun k hk => (hh _ (by unfold sArr; omega_arith)).trans (hH.harr k hk)⟩

/-- After `j` doublings, from `s₀`: `Y = 2^j mod X`, and `128 w - j` in
`sBit`. -/
structure RInv (s₀ : State) (G : Addr) (Z w : Nat) (minv : BitVec 64) (X : Nat) (j : Nat) (t : State) :
    Prop where
  good : Good t G Z w minv
  n : wv t.mem G (slot w aN) w = X
  y : wv t.mem G (slot w aY) w = 2 ^ j % X
  c : word t.mem G (8 * Crt.sBit) = BitVec.ofNat 64 (128 * w - j)
  frm : Frm G (r2Ranges w) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- One doubling. -/
theorem r2Step_ok {s₀ t : State} {G : Addr} {Z w : Nat} {minv : BitVec 64} {X : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX : 1 < X) {j : Nat} (hj : j < 128 * w)
    (hI : RInv s₀ G Z w minv X j t) :
    WP isa (.seq (addMod aY aY aY) (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit])) t
      fun t' => RInv s₀ G Z w minv X (j + 1) t' ∧ ((t'.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 128 * w) := by
  have hg := hI.good
  have hn := hg.scr.nowrap
  have hn' : G.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hylt : wv t.mem G (slot w aY) w < X := by rw [hI.y]; exact Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (addMod_ok hg.scr hg.x0 hg.hdr hZ hw hw' (o := aY) (a := aY) (b := aY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hI.n]; exact hylt) (by rw [hI.n]; exact hylt)) fun t₁ ⟨hv₁, ha₁, k₁⟩ => ?_)
  rw [hI.n, hI.y] at hv₁
  have hg₁ : Good t₁ G Z w minv := ⟨hg.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0, ha₁.hdr hg.hdr⟩
  have hc₁ : word t₁.mem G (8 * Crt.sBit) = BitVec.ofNat 64 (128 * w - j) := by
    rw [ha₁.hslot (by decide)]; exact hI.c
  have hsub : BitVec.ofNat 64 (128 * w - j) - 1#64 = BitVec.ofNat 64 (128 * w - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp; omega_arith),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [BitVec.toNat_ofNat]
    omega_arith
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t₁.mem.writeW (off G (8 * Crt.sBit))
      (BitVec.ofNat 64 (128 * w - (j + 1))) ∧ t'.gpr .x3 = BitVec.ofNat 64 (128 * w - (j + 1))) (by
    brun [hg₁.x0, hdr_enc (show Crt.sBit < 32 by decide), hg₁.ld hZ (show Crt.sBit < 32 by decide),
      hg₁.scr.st (show 8 * Crt.sBit + 8 ≤ Z by
        have := hdr_lt_slot w 8 (show Crt.sBit < 32 by decide); omega_arith), hc₁, hsub])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', h3'⟩, k'⟩ => ?_
  have o' : Outside G (8 * Crt.sBit) 8 t₁.mem t'.mem := by
    rw [hm']; exact writeW_outside _ _ _ (by unfold Crt.sBit sFn; omega_arith)
  refine ⟨⟨⟨hg₁.scr.congr k'.wr, (k'.gpr .x0 (by decide)).trans hg₁.x0, by
      rw [hm']; exact Hdr.store hg₁.hdr (by decide) (by decide) _⟩,
    by rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn', ha₁.wv_of_not_mem (by decide) (by decide) hn',
      hI.n],
    by rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn', hv₁, Nat.pow_succ, Nat.mul_two, Nat.add_mod,
      Nat.mod_mod, ← Nat.add_mod],
    by rw [hm', word_writeW_self],
    (hI.frm.trans (Frm.of_arrays ha₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges])),
    (hI.keep.trans (k₁.trans k')).mono (by decide)⟩, ?_⟩
  rw [h3', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- `r2X`: `Y := 2^(128 w) mod X`, for `1 < X`. -/
theorem r2X_ok {s : State} {G : Addr} {Z w : Nat} {minv : BitVec 64} {X : Nat} (hg : Good s G Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 24) (hn : wv s.mem G (slot w aN) w = X)
    (h1 : wv s.mem G (slot w aOne) w = 1) (hX : 1 < X) :
    WP isa (seqs r2X) s fun t => Good t G Z w minv ∧ wv t.mem G (slot w aY) w = 2 ^ (128 * w) % X ∧
      Frm G (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hns := hg.scr.nowrap
  have hn' : G.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  unfold r2X
  refine wp_seqs_append (by simp [copyArr]) (by simp) ?_
  refine WP.mono (copyArr_ok hg hZ (by omega) (by omega_arith) (o := aY) (a := aOne) (by decide) (by decide)
    (by decide)) fun t₁ ⟨hv₁, ho₁, k₁⟩ => ?_
  have hg₁ : Good t₁ G Z w minv := ⟨hg.scr.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0,
    Hdr.of_outside hg.hdr ho₁⟩
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = t₁.mem.writeW (off G (8 * Crt.sBit))
      (BitVec.ofNat 64 (128 * w)) ∧ t.gpr .x3 = BitVec.ofNat 64 (128 * w)) (by
    brun [hg₁.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show Crt.sBit < 32 by decide),
      hg₁.ld hZ (show sW < 32 by decide), hg₁.hdr.hw,
      hg₁.scr.st (show 8 * Crt.sBit + 8 ≤ Z by
        have := hdr_lt_slot w 8 (show Crt.sBit < 32 by decide); omega_arith),
      shl_ofNat (show w * 2 ^ 7 < 2 ^ 64 by omega_arith), show w * 2 ^ 7 = 128 * w by omega_arith]) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨hm₂, _⟩, k₂⟩ => ?_)
  have o₂ : Outside G (8 * Crt.sBit) 8 t₁.mem t₂.mem := by
    rw [hm₂]; exact writeW_outside _ _ _ (by unfold Crt.sBit sFn; omega_arith)
  have hI : RInv s G Z w minv X 0 t₂ := by
    have hsY := slot_le (w := w) (show aY < 8 by decide)
    have hsN := slot_le (w := w) (show aN < 8 by decide)
    refine ⟨⟨hg₁.scr.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans hg₁.x0, by
        rw [hm₂]; exact Hdr.store hg₁.hdr (by decide) (by decide) _⟩,
      by rw [hm₂, hdrStore_wv _ _ _ (by decide) (by decide) hn',
        ho₁.wv (Or.inl (by unfold slot hdrBytes aN aY; omega))
          (by omega_arith), hn],
      by rw [hm₂, hdrStore_wv _ _ _ (by decide) (by decide) hn', hv₁, h1, Nat.pow_zero, Nat.mod_eq_of_lt hX],
      by rw [hm₂, word_writeW_self, Nat.sub_zero],
      (Frm.of_outside (ho₁.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
        (by simp [r2Ranges])).trans (Frm.of_outside o₂ (by simp [r2Ranges])),
      (k₁.trans k₂).mono (by decide)⟩
  refine WP.mono (count_loop (cr := .x3) (n := 128 * w) (by omega) (RInv s G Z w minv X)
    (fun j hj t h => r2Step_ok hZ hw (by omega_arith) hX hj h) hI) fun t h => ⟨h.good, h.y, h.frm, h.keep⟩

/-! ## `maskCopy` -/

structure MCInv (s₀ : State) (S D : Addr) (eS eD : Nat) (j : Nat) (t : State) : Prop where
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off S (eS + 8 * j)
  x17 : t.gpr .x17 = off D (eD + 8 * j)
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i) &&& s₀.gpr .x15
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem mcStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat} (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : MCInv s₀ S D eS eD j t) :
    WP isa (.block ([ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x17, next .x16, next .x17] ++
        ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MCInv s₀ S D eS eD (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.wr]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  have h15 : t.gpr .x15 = s₀.gpr .x15 := hI.keep.gpr .x15 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j) &&& s₀.gpr .x15) ∧
      t₁.gpr .x16 = off S (eS + 8 * j + 8) ∧ t₁.gpr .x17 = off D (eD + 8 * j + 8))
    (by brun [hI.x16, hI.x17, hld, hst, h15, hv]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `maskCopy`: the `w` words at `S + eS` (`x16`) and-ed with `x15` to
`D + eD` (`x17`), which they do not overlap, changing only those. -/
theorem maskCopy_ok {s : State} {S D : Addr} {eS eD w : Nat}
    (h16 : s.gpr .x16 = off S eS) (h17 : s.gpr .x17 = off D eD) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa maskCopy s fun t =>
      (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i) &&& s.gpr .x15) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ t.gpr .x16 = off S (eS + 8 * w) ∧
      t.gpr .x17 = off D (eD + 8 * w) ∧ Keep [.x3, .x14, .x16, .x17] s t := by
  unfold maskCopy
  refine WP.seq (WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by brun [h12]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h14, hm₁⟩, k₁⟩ => ?_)
  have h0 : MCInv s₁ S D eS eD 0 s₁ :=
    ⟨Keep.refl _ _, by rw [k₁.gpr .x16 (by decide), h16]; rfl, by rw [k₁.gpr .x17 (by decide), h17]; rfl,
      fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩
  have e15 : s₁.gpr .x15 = s.gpr .x15 := k₁.gpr .x15 (by decide)
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega) (MCInv s₁ S D eS eD)
    (fun j hj t hI _ => mcStep_ok hD (by rw [k₁.rd, k₁.wr]; exact hrd) (by rw [k₁.wr]; exact hwr) hsep hj hI)
    h0 h14) fun t hI => ?_
  refine ⟨fun i hi => by rw [hI.done i hi, hm₁, e15], by rw [← hm₁]; exact hI.frame, hI.x16, hI.x17,
    (k₁.trans hI.keep).mono (by decide)⟩

/-- Words copied and-ed with a mask: the number, or 0. -/
theorem wv_mask {m m' : Mem} {S D : Addr} {eS eD : Nat} {c : Bool} :
    ∀ {n : Nat}, (∀ i < n, word m' D (eD + 8 * i) = word m S (eS + 8 * i) &&& mask c) →
      wv m' D eD n = if c then wv m S eS n else 0
  | 0, _ => by cases c <;> rfl
  | n + 1, h => by
    rw [wv, wv, wv_mask fun i hi => h i (by omega), h n (by omega), and_mask_toNat]
    cases c <;> simp

end VG.Proof.Bignum.AArch64.PrivPre
