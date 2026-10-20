module

public import VerifiedGarbage.Proof.Rsa.AArch64.CkSteps
import VerifiedGarbage.Proof.Rsa.AArch64.CvMain
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Shared RSA key-validation phases on AArch64

`KS c` tracks `CkS`, the accumulated mask, and the arrays holding `n`, `e`
and 1. The full and CRT checkers share the comparison and multiplication
phases and the arithmetic helpers here.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev CkIn.N (I : CkIn) : Nat := Spec.Rsa.os2ip I.nb
abbrev CkIn.E (I : CkIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev CkIn.D (I : CkIn) : Nat := Spec.Rsa.os2ip I.db
abbrev CkIn.P (I : CkIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev CkIn.Q (I : CkIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev CkIn.DP (I : CkIn) : Nat := Spec.Rsa.os2ip I.dpb
abbrev CkIn.DQ (I : CkIn) : Nat := Spec.Rsa.os2ip I.dqb
abbrev CkIn.QI (I : CkIn) : Nat := Spec.Rsa.os2ip I.qib

theorem wp_seqs_cons {e : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa e s fun t => WP isa (seqs l) t Q) : WP isa (seqs (e :: l)) s Q := by
  obtain ⟨d, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  exact WP.seq h

/-- A number of `len ≤ k` bytes fits in `w` words. -/
theorem lt_w {bs : List Byte} {k : Nat} (hl : bs.length ≤ k) : Spec.Rsa.os2ip bs < 2 ^ (64 * wk k) :=
  Nat.lt_of_lt_of_le (os2ip_lt bs) ((Nat.pow_le_pow_right (by decide) hl).trans
    ((pow256_le_wk k).trans (Nat.pow_le_pow_right (by decide) (by simp only [wk]; omega))))

/-- Between the phases. -/
def KS (I : CkIn) (m₀ : Mem) (c : Bool) (s : State) : Prop :=
  CkS I m₀ s ∧ mword s.mem I.B = mask c ∧ I.av s.mem 0 = I.N ∧ I.av s.mem aE = I.E ∧ I.av s.mem aOne = 1

/-- `d < n`. -/
theorem phDN_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sD sDlen ++ ltA aX 0)) s (KS I m₀ (decide (I.D < I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [ltA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.d hs.args.dl hs.d L.dbl L.dl1 L.dl2) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckLt_ok h₁ (a := aX) (b := 0) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  rw [v₁, o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [ot 0 (by decide), o₁ 0 (by decide) (by decide), hN],
    by rw [ot aE (by decide), o₁ aE (by decide) (by decide), hE], by rw [ot aOne (by decide), o₁ aOne (by decide) (by decide), hO]⟩

/-- `p q = n`. -/
theorem phPQ_ok {I : CkIn} {m₀ : Mem} {s : State} {c : Bool} (h : KS I m₀ c s) (L : CkLens I) :
    WP isa (seqs (loadA aX sP sPlen ++ (loadA aR sQ sQlen ++ (mulXR ++ (eqA aA 0 ++ ([.block andZero] : List (Prog isa))))))) s
      (KS I m₀ (decide (I.P * I.Q = I.N) && c)) := by
  obtain ⟨hs, hm, hN, hE, hO⟩ := h
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (ckLoad_ok hs (j := aX) (by decide) (by decide)
    (by decide) hs.args.p hs.args.pl hs.p L.pbl L.pl1 (Nat.le_of_lt L.pl2)) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp [mulXR]) (WP.mono (ckLoad_ok h₁ (j := aR) (by decide)
    (by decide) (by decide) h₁.args.q h₁.args.ql h₁.q L.qbl L.ql1 (Nat.le_of_lt L.ql2)) fun s₂ ⟨h₂, m₂, v₂, o₂⟩ => ?_)
  have x₂ : I.av s₂.mem aX = I.P := by rw [o₂ aX (by decide) (by decide), v₁]
  refine wp_seqs_append (by simp [mulXR]) (by simp [eqA]) (WP.mono (ckMulXR_ok h₂ L
    (by rw [x₂]; exact lt_w (by rw [L.pbl]; exact L.pcap))
    (by rw [v₂]; exact lt_w (by rw [L.qbl]; exact L.qcap))) fun s₃ ⟨h₃, m₃, v₃, o₃⟩ => ?_)
  refine WP.mono (ckEq_ok h₃ (a := aA) (b := 0) (by decide) (by decide) (m₃.trans (m₂.trans (m₁.trans hm))))
    fun t ⟨ht, mt, ot⟩ => ?_
  have k0 : ∀ i < 16, i ≠ aX → i ≠ aR → i ≠ aA → I.av t.mem i = I.av s.mem i := fun i hi h1 h2 h3 => by
    rw [ot i hi, o₃ i hi h3, o₂ i hi h2, o₁ i hi h1]
  rw [v₃, x₂, v₂, o₃ 0 (by decide) (by decide), o₂ 0 (by decide) (by decide), o₁ 0 (by decide) (by decide), hN] at mt
  exact ⟨ht, mt, by rw [k0 0 (by decide) (by decide) (by decide) (by decide), hN],
    by rw [k0 aE (by decide) (by decide) (by decide) (by decide), hE],
    by rw [k0 aOne (by decide) (by decide) (by decide) (by decide), hO]⟩

/-- `modOne`: the mask of `[aA] mod [aM] = 1`. -/
theorem ckModOne_ok {I : CkIn} {m₀ : Mem} {s : State} (h : CkS I m₀ s) {c : Bool} (hm : mword s.mem I.B = mask c)
    (hO : I.av s.mem aOne = 1) :
    WP isa (seqs modOne) s fun t => CkS I m₀ t ∧ (∃ r : Nat, (0 < I.av s.mem aM → r = I.av s.mem aA % I.av s.mem aM) ∧
      mword t.mem I.B = mask (decide (r = 1) && c)) ∧
      ∀ i < 16, i ≠ aA → i ≠ aRem → i ≠ aT → I.av t.mem i = I.av s.mem i := by
  unfold modOne
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (ckDivmod_ok h) fun s₁ ⟨h₁, m₁, v₁, o₁⟩ => ?_)
  refine WP.mono (ckEq_ok h₁ (a := aRem) (b := aOne) (by decide) (by decide) (m₁.trans hm)) fun t ⟨ht, mt, ot⟩ => ?_
  refine ⟨ht, ⟨I.av s₁.mem aRem, v₁, ?_⟩, fun i hi h1 h2 h3 => by rw [ot i hi, o₁ i hi h1 h2 h3]⟩
  rw [mt, o₁ aOne (by decide) (by decide) (by decide) (by decide), hO]

/-- The low word of `[aE]` is `e`, below `2^64`. -/
theorem e_word {I : CkIn} {m : Mem} (hE : I.av m aE = I.E) (hE64 : I.E < 2 ^ 64) :
    (word m I.B (slot (wW I.cap) aE)).toNat = I.E := by
  rw [← wv_mod64 m I.B (slot (wW I.cap) aE) (n := wW I.cap) (by simp only [wW]; omega), show wv m I.B (slot (wW I.cap) aE) (wW I.cap) = I.E
    from hE, Nat.mod_eq_of_lt hE64]


end VG.Proof.Rsa.AArch64
