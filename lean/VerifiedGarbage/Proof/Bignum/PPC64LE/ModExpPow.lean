module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Rsa.Octets

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
    (hrs : ∀ r ∈ Pub.stepRegs, r ∈ rs) (hkr : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs)
    (ht : ScanInv s B w N R X XM RR rs c t) :
    WP isa PublicChecked.step t fun t' =>
      ScanInv s B w N R X XM RR rs (2 * c + (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0)) t' ∧
        t'.gpr .r24 = t.gpr .r24 <<< 1 ∧ Keep Pub.stepRegs t t' := by
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
    (hrs : ∀ r ∈ Pub.stepRegs ++ [Reg.r24, .r25, .r30], r ∈ rs)
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
      ?_, ?_, ?_, ?_, ?_⟩ <;> rw [m1] <;> with_reducible assumption
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

/-- `scan`: the `L ≥ 1` bytes of `d` at `D` (`r30`, `r31`) scanned, most
significant first: `c := os2ip d`. The bytes lie apart from the working
space, which is all the scan writes. -/
theorem scan_ok {s t : State} {B D : Addr} {Z w N R X XM RR L : Nat} {rs : List Reg} (hs : Scr s B Z)
    (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hR : 2 ^ (64 * w) = R) (hcop : Nat.Coprime R N)
    (hXM : XM < N) (hXR : RR = R * R % N → XM % N = X * R % N)
    (hrs : ∀ r ∈ Pub.stepRegs ++ [Reg.r24, .r25, .r30, .r31], r ∈ rs)
    (hkr : ∀ r ∈ [Reg.r10, .r11, .r12, .r29], r ∉ rs)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (ht : ScanInv s B w N R X XM RR rs 0 t) (h30 : t.gpr .r30 = off D 0)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 L) :
    WP isa scan t (ScanInv s B w N R X XM RR rs (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L))) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i u =>
    ScanInv s B w N R X XM RR rs (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) u ∧ u.gpr .r30 = off D i
  refine WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega) (by omega) Inv
    (fun i hi u ⟨hu, u30⟩ _ => ?_) ⟨ht, h30⟩ h31) fun u h => h.1
  have hb : u.mem (off D i) = s.mem (off D i) := by
    refine hu.2.1 _ fun r hr => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    have hk8 : k < 8 := by revert hk; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    have := Nat.le_trans (slot_le (w := w) hk8) hZ
    right
    by_contra hc
    exact hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega) rfl
  have hrs' : ∀ r ∈ Pub.stepRegs ++ [Reg.r24, .r25, .r30], r ∈ rs := fun r hr => hrs r (by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h])
  refine WP.seq (WP.mono (byteScan_ok hs hw2 hw' hZ h10 h29 h11 h12 hinv hNd hR hcop hXM hXR hrs' hkr hu u30
    (by rw [hu.1.rd, hu.1.wr]; exact hrd i hi)) fun u₁ ⟨hu₁, a30, a31⟩ => ?_)
  refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
  subst e
  refine ⟨⟨?_, by simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a30⟩,
    by simp only [gpr_write, ↓reduceIte]; rw [a31]⟩
  have hw := hu₁.write (hrs .r31 (by simp)) (u₁.gpr .r31 - BitVec.ofNat 64 1)
  rw [hb] at hw
  rwa [bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]

/-- The registers `powSecret` writes. -/
def powSRegs : List Reg := Pub.stepRegs ++ [.r25, .r30, .r31]

/-- `powSecret`: `x^d mod m` into array 4, for `x` in array 4, `m` (odd, at
least 2) in array 0, something below `m` in array 1 (if `R² mod m`, the result
is right) and the `L ≥ 1` bytes of `d` at `D` (`r30`, `r31`), apart from the
working space. -/
theorem powSecret_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hRRlt : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa powSecret s fun t =>
      ((val32 s.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) →
          val32 t.mem B (slot w 4) (2 * w) =
            val32 s.mem B (slot w 4) (2 * w) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) %
              val32 s.mem B (slot w 0) (2 * w)) ∧
        Outs B (powRs w) s.mem t.mem) ∧ Keep powSRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have ap : ∀ {j : Nat} {ks : List Nat}, (∀ k ∈ ks, k ≠ j) →
      ∀ r ∈ ks.map (fun k => (slot w k, 8 * (w + 2))), slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j ks h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact sp (Ne.symm (h k hk))
  have v0 : ∀ {m : Mem}, Outs B (powRs w) s.mem m →
      val32 m B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) := fun h =>
    h.val32 (fun r hr => by have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  have w0 : ∀ {m : Mem}, Outs B (powRs w) s.mem m → w32 m B (slot w 0) = w32 s.mem B (slot w 0) := fun h =>
    Outs.w32 h (fun r hr => by have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hRRlt v0 ⊢
  generalize hR : 2 ^ (64 * w) = R
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RRv at hRRlt ⊢
  have hcop : Nat.Coprime R N := by rw [← hR]; exact VG.Proof.Bignum.coprime_pow2 hodd _
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  have hN0 : 0 < N := by omega
  have outs_of : ∀ {m m' : Mem} {js : List Nat}, (∀ j ∈ js, j ∈ [1, 2, 3, 4, 5, 6, 7]) →
      Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m' → Outs B (powRs w) m m' := fun hjs h =>
    h.mono fun r hr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact List.mem_map.mpr ⟨k, hjs k hk, rfl⟩
  have vj : ∀ {m m' : Mem} {js : List Nat} {j : Nat}, j < 8 → (∀ k ∈ js, k ≠ j) →
      Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m' →
      val32 m' B (slot w j) (2 * w) = val32 m B (slot w j) (2 * w) := fun hj hjs h =>
    h.val32 (fun r hr => by have := ap hjs r hr; omega) (by have := sl _ hj; omega)
  unfold powSecret
  -- 1 in array 7.
  refine WP.seq (WP.mono (oneP_ok hs (by omega) hw' hZ h10 h29 h11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  have o1 : Outs B ([7].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem :=
    Outs.of_outside (o := slot w 7) (n := 8 * (w + 2)) (out1.mono (Nat.le_refl _) (by omega)) (by simp)
  have N1 : val32 s₁.mem B (slot w 0) (2 * w) = N := (vj (by decide) (by decide) o1).trans hNd
  have R1 : val32 s₁.mem B (slot w 1) (2 * w) = RRv := by rw [vj (by decide) (by decide) o1, hRRd]
  have X1 : val32 s₁.mem B (slot w 4) (2 * w) = X := (vj (by decide) (by decide) o1).trans hXd
  -- `a := R mod n` into array 5.
  refine WP.seq (WP.mono (montOp_ok (o := 5) (a := 1) (b := 7) (hs.congr k1.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [k1.gpr .r12 (by decide)]; exact h12)
    (by rw [w0 (outs_of (by decide) o1), k1.gpr .r12 (by decide)]; exact hinv) (by rw [h7, N1]; omega))
    fun s₂ ⟨⟨hA0, eA0, o2⟩, k2⟩ => ?_)
  rw [N1, R1, h7, hR] at eA0
  rw [N1] at hA0
  have o2' : Outs B ([2, 3, 5].map fun k => (slot w k, 8 * (w + 2))) s₁.mem s₂.mem := o2
  have k12 := k1.trans k2
  have A0 : RRv = R * R % N → val32 s₂.mem B (slot w 5) (2 * w) % N = X ^ 0 * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [eA0, hE, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mod_mod]
  -- `x R mod n` into array 6.
  have O12 : Outs B (powRs w) s.mem s₂.mem := (outs_of (by decide) o1).trans (outs_of (by decide) o2')
  refine WP.seq (WP.mono (montOp_ok (o := 6) (a := 4) (b := 1) (hs.congr k12.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [k12.gpr .r12 (by decide)]; exact h12)
    (by rw [w0 O12, k12.gpr .r12 (by decide)]; exact hinv)
    (by rw [vj (by decide) (by decide) o2', R1, v0 O12]; exact hRRlt)) fun s₃ ⟨⟨hXM, eXM, o3⟩, k3⟩ => ?_)
  rw [v0 O12, vj (by decide) (by decide) o2', vj (by decide) (by decide) o2', X1, R1, hR] at eXM
  rw [v0 O12] at hXM
  have o3' : Outs B ([2, 3, 6].map fun k => (slot w k, 8 * (w + 2))) s₂.mem s₃.mem := o3
  have k13 := k12.trans k3
  have O13 : Outs B (powRs w) s.mem s₃.mem := O12.trans (outs_of (by decide) o3')
  have XM : RRv = R * R % N → val32 s₃.mem B (slot w 6) (2 * w) % N = X * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [eXM, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  generalize hXMd : val32 s₃.mem B (slot w 6) (2 * w) = XMv at hXM XM
  have A3 : val32 s₃.mem B (slot w 5) (2 * w) = val32 s₂.mem B (slot w 5) (2 * w) :=
    vj (by decide) (by decide) o3'
  have S7 : val32 s₃.mem B (slot w 7) (2 * w) = 1 := by
    rw [vj (by decide) (by decide) o3', vj (by decide) (by decide) o2', h7]
  -- The scan.
  have g3 : ∀ r ∈ [Reg.r30, .r31], s₃.gpr r = s.gpr r := fun r hr => k13.gpr r (by revert r; decide)
  refine WP.seq (WP.mono (scan_ok (rs := powSRegs) hs hw2 hw' hZ h10 h29 h11 h12 hinv hNd hR hcop hXM XM
    (by decide) (by decide) hL hL' hrd hsep ⟨k13.mono, O13, hXMd, S7, by rw [A3]; exact hA0, fun hE => by
      rw [A3]; exact A0 hE⟩ ((g3 .r30 (by simp)).trans h30) ((g3 .r31 (by simp)).trans h31))
    fun t ⟨kt, ot, _, t7, tA, hcA⟩ => ?_)
  -- Out of Montgomery form.
  refine WP.mono (montOp_ok (o := 4) (a := 5) (b := 7) (hs.congr kt.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((kt.gpr _ (by decide)).trans h10)
    ((kt.gpr _ (by decide)).trans h29) ((kt.gpr _ (by decide)).trans h11)
    (by rw [kt.gpr .r12 (by decide)]; exact h12) (by rw [w0 ot, kt.gpr .r12 (by decide)]; exact hinv)
    (by rw [t7, v0 ot]; omega)) fun u ⟨⟨hU, eU, o5⟩, k5⟩ =>
    ⟨⟨?_, ot.trans (outs_of (js := [2, 3, 4]) (by decide) o5)⟩, (kt.trans k5).mono⟩
  intro hE
  rw [v0 ot] at hU eU
  rw [t7, hR, Nat.mul_one] at eU
  have : val32 u.mem B (slot w 4) (2 * w) % N = X ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % N :=
    VG.Proof.Bignum.mont_cancel hcop (by rw [eU, hcA hE])
  rw [← Nat.mod_eq_of_lt hU, this]

end VG.Proof.Bignum.PPC64LE.ModExp
