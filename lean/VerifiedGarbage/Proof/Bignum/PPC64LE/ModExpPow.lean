module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck

/-!
# Modular exponentiation by a secret exponent on PPC64LE: a step

`ScanInv`: what holds between the steps of a left-to-right scan in the
public-key operation's working space, the accumulator (array 5) congruent to
`x^c R` once `R² mod m` (array 1, before the scan) is right. `step_inv`: a
step takes `c` to `2 c` or `2 c + 1` by the top bit of `r24`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.ModExp

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE VG.Proof.Bignum.PPC64LE.Pub
open VG.Impl.Bignum.PPC64LE.ModExp (byteScan scan powSecret)

/-- Between steps of a scan from `s`, with `c` the bits scanned so far: the
arrays but 0 changed, `x R mod m` (`XM`) in array 6, 1 in array 7, and the
accumulator in array 5 below `m` (`N`), congruent to `x^c R` if `R² mod m`
was right (`RR = R R mod N`). -/
def ScanInv (s : State) (B : Addr) (w N R X XM RR : Nat) (rs : List Reg) (c : Nat) (t : State) : Prop :=
  Keep rs s t ∧ Outs B (powRs w) s.mem t.mem ∧ val32 t.mem B (slot w 6) (2 * w) = XM ∧
    val32 t.mem B (slot w 7) (2 * w) = 1 ∧ val32 t.mem B (slot w 5) (2 * w) < N ∧
    (RR = R * R % N → val32 t.mem B (slot w 5) (2 * w) % N = X ^ c * R % N)

theorem ScanInv.write {s t : State} {B : Addr} {w N R X XM RR c : Nat} {rs : List Reg} {r : Reg}
    (h : ScanInv s B w N R X XM RR rs c t) (hr : r ∈ rs) (v : BitVec 64) :
    ScanInv s B w N R X XM RR rs c (t.write r v) :=
  ⟨(h.1.trans (Keep.write _ _ _)).mono fun x hx => by
    rcases List.mem_append.mp hx with h' | h'
    · exact h'
    · rw [List.mem_singleton.mp h']; exact hr, h.2⟩

theorem step_inv {s t : State} {B : Addr} {Z w N R X XM RR c : Nat} {rs : List Reg} (hs : Scr s B Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hR : 2 ^ (64 * w) = R) (hcop : Nat.Coprime R N)
    (hXM : XM < N) (hXR : RR = R * R % N → XM % N = X * R % N)
    (hrs : ∀ r ∈ stepRegs, r ∈ rs) (hkr : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs)
    (ht : ScanInv s B w N R X XM RR rs c t) :
    WP isa PublicChecked.step t fun t' =>
      ScanInv s B w N R X XM RR rs (2 * c + (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0)) t' ∧
        t'.gpr .r24 = t.gpr .r24 <<< 1 ∧ Keep stepRegs t t' := by
  obtain ⟨kt, ot, t6, t7, tA, hcA⟩ := ht
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have ap : ∀ {j : Nat} {ks : List Nat}, (∀ k ∈ ks, k ≠ j) →
      ∀ r ∈ ks.map (fun k => (slot w k, 8 * (w + 2))), slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j ks h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact sp (Ne.symm (h k hk))
  have v0 : val32 t.mem B (slot w 0) (2 * w) = N := (ot.val32 (fun r hr => by
    have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
    (by have := sl 0 (by decide); omega)).trans hNd
  have w0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0) :=
    Outs.w32 ot (fun r hr => by have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], t.gpr r = s.gpr r := fun r hr => kt.gpr r (hkr r hr)
  refine WP.mono (Pub.step_ok (hs.congr kt.wr) hw2 hw' hZ ((g .r10 (by simp)).trans h10) ((g .r29 (by simp)).trans h29)
    ((g .r11 (by simp)).trans h11) (by rw [g .r12 (by simp)]; exact h12)
    (by rw [w0, g .r12 (by simp)]; exact hinv) (by rw [v0]; exact tA) (by rw [v0, t6]; exact hXM))
    fun t₁ ⟨⟨S, P, hSN, hPN, eS, eP, hv⟩, os, h24', k'⟩ => ?_
  rw [v0] at hSN hPN eS eP
  rw [t6] at eP
  have os' : Outs B ([2, 3, 4, 1, 5].map fun k => (slot w k, 8 * (w + 2))) t.mem t₁.mem := os
  have v6 : val32 t₁.mem B (slot w 6) (2 * w) = val32 t.mem B (slot w 6) (2 * w) :=
    os'.val32 (fun r hr => by have := ap (j := 6) (ks := [2, 3, 4, 1, 5]) (by decide) r hr; omega)
      (by have := sl 6 (by decide); omega)
  have v7 : val32 t₁.mem B (slot w 7) (2 * w) = val32 t.mem B (slot w 7) (2 * w) :=
    os'.val32 (fun r hr => by have := ap (j := 7) (ks := [2, 3, 4, 1, 5]) (by decide) r hr; omega)
      (by have := sl 7 (by decide); omega)
  refine ⟨⟨(kt.trans k').mono fun r hr => ?_, ot.trans (os'.mono fun r hr => ?_), by rw [v6, t6],
    by rw [v7, t7], by rw [hv]; split <;> with_reducible assumption, fun hE => ?_⟩, h24', k'⟩
  · rcases List.mem_append.mp hr with h | h
    · exact h
    · exact hrs r h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨k, by revert hk; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega, rfl⟩
  · have hS := sq_step hcop (hcA hE) (by rw [← hR]; exact eS)
    have hP := mul_step hcop hS (hXR hE) (by rw [← hR]; exact eP)
    rw [hv]
    split
    · exact hP
    · rw [Nat.add_zero]; exact hS

/-- `byteScan`: the eight bits of the byte at `r30` scanned, `c := 256 c + b`. -/
theorem byteScan_ok {s t : State} {B D : Addr} {Z w N R X XM RR c i : Nat} {rs : List Reg} (hs : Scr s B Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hR : 2 ^ (64 * w) = R) (hcop : Nat.Coprime R N)
    (hXM : XM < N) (hXR : RR = R * R % N → XM % N = X * R % N)
    (hrs : ∀ r ∈ stepRegs ++ [Reg.r24, .r25, .r30], r ∈ rs)
    (hkr : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs)
    (ht : ScanInv s B w N R X XM RR rs c t) (h30 : t.gpr .r30 = off D i)
    (hrd : InRegions (t.rd ++ t.wr) (off D i) 1) :
    WP isa byteScan t fun t' =>
      ScanInv s B w N R X XM RR rs (256 * c + (t.mem (off D i)).toNat) t' ∧ t'.gpr .r30 = off D (i + 1) ∧
        t'.gpr .r31 = t.gpr .r31 := by
  have kt := ht.1
  generalize hb : (t.mem (off D i)).toNat = b
  have hb256 : b < 256 := by rw [← hb]; exact (t.mem (off D i)).isLt
  unfold byteScan
  refine WP.seq (WP.mono (WP.keep [.r24, .r30, .r25] (Q := fun t₁ =>
    t₁.gpr .r24 = BitVec.ofNat 64 b <<< 56 ∧ t₁.gpr .r30 = off D (i + 1) ∧ t₁.gpr .r25 = BitVec.ofNat 64 8 ∧
      t₁.mem = t.mem) ?_ (by decide)) fun t₁ ⟨⟨a24, a30, a25, m1⟩, k1⟩ => ?_)
  · prun [h30, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, read_byte64, hb]
  have hin : ScanInv s B w N R X XM RR rs c t₁ := by
    obtain ⟨_, ot, t6, t7, tA, hcA⟩ := ht
    refine ⟨kt.trans' (k1.mono fun r hr => hrs r (by simp at hr ⊢; rcases hr with h | h | h <;> simp [h])),
      ?_, ?_, ?_, ?_, ?_⟩ <;> rw [m1] <;> assumption
  let Inv : Nat → State → Prop := fun j u =>
    (∃ c', c' * 2 ^ 64 + (u.gpr .r24).toNat = (256 * c + b) * 2 ^ 56 * 2 ^ j ∧
      ScanInv s B w N R X XM RR rs c' u) ∧ u.gpr .r30 = off D (i + 1) ∧ u.gpr .r31 = t.gpr .r31
  refine WP.mono (wp_countdown (cnt := .r25) (N := 8) (by decide) (by decide) Inv
    (fun j _ u ⟨⟨c', hc, hu⟩, u30, u31⟩ _ => ?_) ⟨⟨c, ?_, hin⟩, a30, k1.gpr .r31 (by decide)⟩ a25)
    fun u ⟨⟨c', hc, hu⟩, u30, u31⟩ => ⟨?_, u30, u31⟩
  · refine WP.seq (WP.mono (step_inv hs hw2 hw' hZ h10 h29 h11 h12 hinv hNd hR hcop hXM hXR
      (fun r hr => hrs r (List.mem_append_left _ hr)) hkr hu)
      fun u₁ ⟨hu₁, h24', k'⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r25 (by decide)) fun u₂ e => ?_
    subst e
    refine ⟨⟨⟨_, ?_, hu₁.write (hrs _ (by simp)) _⟩, ?_, ?_⟩, ?_⟩
    rotate_left
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r30 (by decide)]; exact u30
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r31 (by decide)]; exact u31
    · simp only [gpr_write, ↓reduceIte]; rw [k'.gpr .r25 (by decide)]
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [h24', r24_step, show (2 : Nat) ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ 2 j, ← Nat.mul_assoc]
    have hlt := (u.gpr .r24).isLt
    generalize (u.gpr .r24).toNat = r at hc hlt ⊢
    generalize (256 * c + b) * 2 ^ 56 * 2 ^ j = Y at hc ⊢
    split
    · rename_i hb; simp only [decide_eq_true_eq] at hb
      omega_using [hc, hlt, hb]
    · omega_using [hc, hlt]
  · rw [a24, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  · have hc' : c' = 256 * c + b := by
      have := (u.gpr .r24).isLt
      rw [show (256 * c + b) * 2 ^ 56 * 2 ^ 8 = (256 * c + b) * 2 ^ 64 by rw [Nat.mul_assoc]] at hc
      omega
    rw [← hc']; exact hu

end VG.Proof.Bignum.PPC64LE.ModExp
