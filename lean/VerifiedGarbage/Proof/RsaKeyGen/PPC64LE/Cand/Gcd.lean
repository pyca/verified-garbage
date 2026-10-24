module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.ModE
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: `gcd(c − 1, e)`

`modE_ok`: `c` (array 0) copied to `aCm1`, its low word less 1 (`c` is odd),
then its words from the top modulo the `e > 1` in `r21` (`modWords_ok`):
`r3 = (c − 1) mod e`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Candidate
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- The registers `modE` writes. -/
def meRegs : List Reg := [.r5, .r14, .r15, .r17, .r0, .r3, .r4, .r6, .r7, .r8, .r9, .r16]

theorem slot_lt' {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k :=
  VG.Proof.MillerRabin.PPC64LE.slot_lt h

/-- A number of `w ≥ 1` words: its low word and the others. -/
theorem wv_low (m : Mem) (B : Addr) (d w : Nat) (hw : 1 ≤ w) :
    wv m B d w = (word m B d).toNat + 2 ^ 64 * wv m B (d + 8) (w - 1) := by
  rw [show w = 1 + (w - 1) by omega, wv_add, Nat.add_sub_cancel_left]
  simp [wv]

/-- Numbers of equal words at different offsets are equal. -/
theorem wv_shift' {m m' : Mem} {B : Addr} {d d' w : Nat}
    (h : ∀ i < w, word m' B (d' + 8 * i) = word m B (d + 8 * i)) : wv m' B d' w = wv m B d w := by
  induction w with
  | zero => rfl
  | succ k ih => rw [wv, wv, ih fun i hi => h i (by omega), h k (by omega)]

theorem modE_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hodd : c % 2 = 1) (he : 1 < (s.gpr .r21).toNat) :
    WP isa modE s fun t =>
      ((t.gpr .r3).toNat = (c - 1) % (s.gpr .r21).toNat ∧ Outside B (slot w aCm1) (8 * w) s.mem t.mem) ∧
        Keep meRegs s t := by
  have hs := h.hs
  have hn := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have s34 : slot w aCm1 + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt' (show aCm1 < nArr by decide)) h35
  have s0 : slot w 0 + 8 * (w + 2) ≤ slot w aCm1 := slot_lt' (show 0 < aCm1 by decide)
  unfold modE
  -- `r14 :=` `aCm1`, `r15 :=` array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) aCm1) fun t₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  have hp : WP isa (.block [.addi .r15 .r10 0]) t₁ fun t =>
      (t.gpr .r15 = off B (slot w 0) ∧ t.mem = t₁.mem) ∧ Keep [.r15] t₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun [(k₁.gpr .r10 (by decide)).trans h.h10]
  refine WP.mono hp fun t₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  have e2 := (h.keep k₁ (by decide)).keep k₂ (by decide)
  -- The copy.
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok (dS := slot w 0) (dD := slot w aCm1) e2.hs a15
    (by rw [k₂.gpr .r14 (by decide), a14]) e2.h11 (by omega) (by omega) (by omega) (by omega) (.inl (by omega)))
    fun t₃ ⟨⟨_, hcp, out₃⟩, k₃⟩ => ?_)
  have e3 := e2.keep k₃ (by decide)
  -- Its low word less 1, and the loop's registers.
  have hm23 : t₂.mem = s.mem := by rw [m₂, m₁]
  have hw0 : word t₃.mem B (slot w aCm1) = word s.mem B (slot w 0) := by
    have := hcp 0 (by omega); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this, hm23]
  have hodd0 : (word s.mem B (slot w 0)).toNat % 2 = 1 := by
    have := wv_low s.mem B (slot w 0) w (by omega); rw [hc] at this; omega
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (e3.base (rd := .r14) (by decide) (by decide) aCm1) fun t₄ ⟨⟨b14, m₄⟩, k₄⟩ => ?_
  have hblk : WP isa (.block [.load .d .r3 .r14 0, .subi .r3 .r3 1, .store .d .r3 .r14 0, .lsl .r5 .r11 2,
      .add .r14 .r14 .r5, .lsr .d .r17 .r11 1, .li .r3 0]) t₄ fun t =>
      (t.mem = t₄.mem.writeW (off B (slot w aCm1)) (word t₄.mem B (slot w aCm1) - BitVec.ofNat 64 1) ∧
        t.gpr .r14 = off B (slot w aCm1 + 8 * w) ∧ t.gpr .r17 = BitVec.ofNat 64 w ∧ t.gpr .r3 = 0) ∧
        Keep [.r3, .r5, .r14, .r17] t₄ t := by
    refine WP.keep _ ?_ (by decide)
    have h11 : t₄.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k₄.gpr .r11 (by decide)).trans e3.h11
    prun [b14, h11, (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).wr).ld (d := slot w aCm1) (n := 8) (by omega),
      (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).wr).st (d := slot w aCm1) (n := 8) (by omega)]
    refine ⟨?_, ?_, rfl⟩
    · have e8 : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        omega
      rw [e8]; exact off_add _ _ _
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
  refine WP.mono hblk fun t₅ ⟨⟨m₅, b14', b17, b3⟩, k₅⟩ => ?_
  have k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  have e5 : (t₅.gpr .r21).toNat = (s.gpr .r21).toNat := by rw [k15.gpr .r21 (by decide)]
  refine WP.mono (modWords_ok (hs.congr k15.wr) b14' b17 (by omega) (by omega) (by omega) b3 (by rw [e5]; exact he))
    fun t ⟨tv, tm, kt⟩ => ⟨⟨?_, ?_⟩, (k15.trans kt).mono (by decide)⟩
  · rw [tv, e5, m₅, m₄]
    -- The number in `aCm1` is `c − 1`.
    have hv : wv (t₃.mem.writeW (off B (slot w aCm1)) (word t₃.mem B (slot w aCm1) - BitVec.ofNat 64 1)) B
        (slot w aCm1) w = c - 1 := by
      have hout := writeW_outside t₃.mem B (d := slot w aCm1) (word t₃.mem B (slot w aCm1) - BitVec.ofNat 64 1)
        (by omega)
      rw [wv_low _ _ _ _ (by omega), word_writeW_self,
        hout.wv (d := slot w aCm1 + 8) (k := w - 1) (Or.inr (Nat.le_refl _)) (by omega)]
      have hrest : wv t₃.mem B (slot w aCm1 + 8) (w - 1) = wv s.mem B (slot w 0 + 8) (w - 1) := by
        rw [← hm23]
        apply wv_shift'; intro i hi
        have := hcp (i + 1) (by omega)
        rw [show slot w aCm1 + 8 + 8 * i = slot w aCm1 + 8 * (i + 1) by omega,
          show slot w 0 + 8 + 8 * i = slot w 0 + 8 * (i + 1) by omega]
        exact this
      rw [hrest, BitVec.toNat_sub, hw0, BitVec.toNat_ofNat]
      have hcw := wv_low s.mem B (slot w 0) w (by omega)
      rw [hc] at hcw
      have := (word s.mem B (slot w 0)).isLt
      omega
    rw [hv]
  · have o4 : Outside B (slot w aCm1) (8 * w) s.mem t₄.mem := by
      rw [m₄, ← hm23]; exact out₃
    rw [tm, m₅]
    exact o4.trans ((writeW_outside t₄.mem B (d := slot w aCm1) _ (by omega)).mono (by omega) (by omega))


theorem gcdStep_lt {u v : Nat} (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) :
    (VG.Proof.RsaKeyGen.gcdStep u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdStep u v).2 < 2 ^ 64 := by
  unfold VG.Proof.RsaKeyGen.gcdStep
  split
  · split <;> exact ⟨by omega, by omega⟩
  · exact ⟨by omega, hv⟩

theorem gcdIter_lt : ∀ n {u v : Nat}, u < 2 ^ 64 → v < 2 ^ 64 → v % 2 = 1 →
    (VG.Proof.RsaKeyGen.gcdIter n u v).1 < 2 ^ 64 ∧ (VG.Proof.RsaKeyGen.gcdIter n u v).2 < 2 ^ 64 ∧
      (VG.Proof.RsaKeyGen.gcdIter n u v).2 % 2 = 1
  | 0, _, _, hu, hv, ho => ⟨hu, hv, ho⟩
  | n + 1, u, v, hu, hv, ho => by
    rw [VG.Proof.RsaKeyGen.gcdIter]
    exact gcdIter_lt n (gcdStep_lt hu hv).1 (gcdStep_lt hu hv).2 (VG.Proof.RsaKeyGen.gcdStep_odd ho)

/-- The registers the gcd's steps write. -/
def gsRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r9, .r15, .r16, .r21]

/-- 128 steps of the binary gcd from `u = r3` and the odd `v = r21`. -/
theorem gcdLoop_ok {s : State} {u v : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 u)
    (h21 : s.gpr .r21 = BitVec.ofNat 64 v) (h9 : s.gpr .r9 = BitVec.ofNat 64 128) (hu : u < 2 ^ 64)
    (hv : v < 2 ^ 64) (ho : v % 2 = 1) :
    WP isa (Impl.Bignum.PPC64LE.Precompute.countLoop .r9 VG.Impl.RsaKeyGen.PPC64LE.Candidate.gcdStep) s fun t =>
      t.gpr .r21 = BitVec.ofNat 64 (Nat.gcd u v) ∧ t.mem = s.mem ∧ Keep gsRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r9) (N := 128) (by decide) (by decide)
    (fun i t => t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).1 ∧
      t.gpr .r21 = BitVec.ofNat 64 (VG.Proof.RsaKeyGen.gcdIter i u v).2 ∧ t.mem = s.mem ∧ Keep gsRegs s t)
    ?_ ⟨h3, h21, rfl, Keep.refl _ _⟩ h9) fun t ⟨_, t21, tm, tk⟩ => ⟨?_, tm, tk⟩
  · intro i _ t ⟨t3, t21, tm, tk⟩ _
    obtain ⟨b1, b2, bo⟩ := gcdIter_lt i hu hv ho
    refine WP.block_append_iff.mpr (WP.mono (gcdStep_ok t3 t21 b1 b2 bo) fun t₁ ⟨⟨a3, a21, m₁⟩, k₁⟩ => ?_)
    have hsub : WP isa (.block [.subi .r9 .r9 1]) t₁ fun t' =>
        (t'.gpr .r9 = t₁.gpr .r9 - BitVec.ofNat 64 1 ∧ t'.mem = t₁.mem) ∧ Keep [.r9] t₁ t' := by
      refine WP.keep _ ?_ (by decide)
      prun
    refine WP.mono hsub fun t' ⟨⟨h9', m'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, tm], ?_⟩, ?_⟩
    · rw [k'.gpr .r3 (by decide), a3, VG.Proof.RsaKeyGen.gcdIter_succ']
    · rw [k'.gpr .r21 (by decide), a21, VG.Proof.RsaKeyGen.gcdIter_succ']
    · exact ((tk.trans k₁).trans k').mono (by decide)
    · rw [h9', k₁.gpr .r9 (by decide)]
  · rw [t21, VG.Proof.RsaKeyGen.gcdIter_eq 128 u v ho (by
      have : u * v < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt hu hv
      rw [← Nat.pow_add] at this; exact this)]


/-- `gcdE`: `r22 := gcd(c − 1, e) − 1` for the odd `e > 1` in `r21`. -/
theorem gcdE_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hodd : c % 2 = 1) (he : 1 < (s.gpr .r21).toNat)
    (heo : (s.gpr .r21).toNat % 2 = 1) :
    WP isa gcdE s fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (Nat.gcd (c - 1) (s.gpr .r21).toNat) - BitVec.ofNat 64 1 ∧
        Outside B (slot w aCm1) (8 * w) s.mem t.mem) ∧ Keep (meRegs ++ gsRegs ++ ([.r22] : List Reg)) s t := by
  unfold gcdE
  refine WP.seq (WP.mono (modE_ok h h35 hc hodd he) fun t₁ ⟨⟨v₁, o₁⟩, k₁⟩ => ?_)
  have e₁ : t₁.gpr .r21 = s.gpr .r21 := k₁.gpr .r21 (by decide)
  have h9 : WP isa (.block [.li .r9 128]) t₁ fun t =>
      (t.gpr .r9 = BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) ∧ Keep [.r9] t₁ t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.seq (WP.mono h9 fun t₂ ⟨⟨a9, m₂⟩, k₂⟩ => ?_)
  have hE := (s.gpr .r21).isLt
  refine WP.seq (WP.mono (gcdLoop_ok (u := (c - 1) % (s.gpr .r21).toNat) (v := (s.gpr .r21).toNat)
    (by rw [k₂.gpr .r3 (by decide), ← v₁]; exact self_ofNat _)
    (by rw [k₂.gpr .r21 (by decide), e₁]; exact self_ofNat _) a9
    (Nat.lt_trans (Nat.mod_lt _ (by omega)) hE) hE heo) fun t₃ ⟨g₃, m₃, k₃⟩ => ?_)
  have hsub : WP isa (.block [.subi .r22 .r21 1]) t₃ fun t =>
      (t.gpr .r22 = t₃.gpr .r21 - BitVec.ofNat 64 1 ∧ t.mem = t₃.mem) ∧ Keep [.r22] t₃ t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hsub fun t ⟨⟨a22, m⟩, k⟩ => ⟨⟨?_, ?_⟩, ((k₁.trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rw [a22, g₃, show Nat.gcd ((c - 1) % (s.gpr .r21).toNat) (s.gpr .r21).toNat = Nat.gcd (c - 1) (s.gpr .r21).toNat
      from by rw [← Nat.gcd_rec, Nat.gcd_comm]]
  · rw [m, m₃, m₂]; exact o₁

end VG.Proof.RsaKeyGen.PPC64LE.Cand
