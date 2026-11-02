module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Init
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: the primes and `lcm(p - 1, q - 1)`

`ltS_ok`: the comparison `[a] < [b]` into a slot, with `[a] - [b]` in `aT`.
`primes_ok`: `p` and `q` ordered (`p ≥ q`), `p - 1` and `q - 1`.
`lcmPart_ok`: `[aL] = lcm(p - 1, q - 1)`, through the product `φ`, `8 p_len`
steps of the halving (`KeyMath.halveIter`, `halving_ok`), the gcd of the
halving's `u` and `v` (`gcdUV_ok`) and the division (`divBy_ok`), as PPC64LE's
(`Proof/RsaKeyGen/PPC64LE/Key/{Primes,Lcm}.lean`). Each stage is stated over
Batch 0's `St` (`Init.lean`): the arrays it writes, the others' values kept,
and its values.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Proof.RsaKeyGen (halveStep halveIter halveIter_succ')
open VG.Impl.Rsa.RISCV64.Keys (seqs copy sub3 sel half bitOf stBorrow aZero)
open VG.Impl.RsaKeyGen.RISCV64.Key (nArr aT aOne aTwo aThree aP0 aQ0 aP aQ aPm aQm aU aV aF aU2 aV2 aS
  aG aL aDv aDr aDt X0 X1 X2 ltS primes halfSel halfStep halving gcdUV divBy lcmPart notS andNotS
  mulTo invOf nP cnt8)

/-- A value of the working space of `s0`. -/
abbrev nm (s0 : State) (m : Mem) (j : Nat) : Nat := num m (bOf s0) (wOf s0) j

/-! ## The comparison -/

/-- `ltS d a b`: the slot `d` := `[a] < [b]`, `[aT]` := `[a] - [b]` modulo `2^(64 w)`. -/
theorem ltS_ok {s : State} {B : Addr} {Z w N d a b : Nat} (h : Ws s B Z w N) (ha : a < N) (hb : b < N)
    (hT : aT < N) (hN : N ≤ 2048) (haT : aT ≠ a) (hbT : aT ≠ b) (hd : d + 8 ≤ hdr) (hd8 : d % 8 = 0) :
    WP isa (seqs (ltS d a b)) s fun t => Ws t B Z w N ∧ VG.Proof.Rsa.RISCV64.Keys.Frame B w [aT] [d] s.mem t.mem ∧
      slot t.mem B d = (if num s.mem B w a < num s.mem B w b then 1 else 0) ∧
      num t.mem B w aT = (if num s.mem B w a < num s.mem B w b then
        num s.mem B w a + 2 ^ (64 * w) - num s.mem B w b else num s.mem B w a - num s.mem B w b) ∧
      Keep opRegs s t := by
  have fT := h.fit64 hT
  rw [show seqs (ltS d a b) = .seq (sub3 aT a b) (.block (stBorrow d)) from rfl]
  refine WP.seq (WP.mono (sub3_ok h hT ha hb hN haT hbT) fun t1 ⟨h1, f1, e1, b1, k1⟩ => ?_)
  refine WP.mono (stBorrow_ok h1 hd hd8) fun t ⟨ht, ft, vt, kt⟩ => ?_
  have la := wordsVal_lt s.mem B (arr w a) w
  have lb := wordsVal_lt s.mem B (arr w b) w
  have lt := wordsVal_lt t1.mem B (arr w aT) w
  have eT : num t.mem B w aT = num t1.mem B w aT := ft.num (by simp) (by simpa using hd) fT
  refine ⟨ht, Frame.join f1 ft (js := [aT]) (ds := [d]), ?_, ?_, (k1.trans kt).mono (by simp)⟩
  · rw [vt]
    simp only [num] at e1 ⊢
    generalize 2 ^ (64 * w) = K at *
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e | e <;> rw [e] at e1 ⊢ <;> split <;> omega
  · rw [eT]
    simp only [num] at e1 ⊢
    generalize 2 ^ (64 * w) = K at *
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with e | e <;> rw [e] at e1 <;> split <;> omega

/-- A free array's words are zero. -/
theorem St.word_zero {s0 s : State} {used : List Nat} (c : St s0 used s) {j i : Nat} (hj : j < nArr)
    (hu : j ∉ used) (hi : i < wOf s0 + 2) : word s.mem (bOf s0) (arr (wOf s0) j + 8 * i) = 0 := by
  have := wordsVal_zero_part (a := i) (c := 1) (c.free j hj hu) (by omega)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- `St` with more arrays written. -/
theorem St.sub {s0 s : State} {used used' : List Nat} (c : St s0 used s) (hs : ∀ j ∈ used, j ∈ used') :
    St s0 used' s :=
  ⟨c.cb, c.ws, fun j hj hu => c.free j hj fun e => hu (hs j e)⟩

/-- The registers the stages here write. -/
abbrev stRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a2, .a3, .a5, .a6, .s7, .s8]

/-! ## The primes -/

/-- `a - 1`, or 0 for 0, from the borrow of `a - 1`. -/
theorem pred_sel {K a : Nat} :
    (if (if a < 1 then 1 else 0) = 0 then (if a < 1 then a + K - 1 else a - 1) else 0) = a - 1 := by
  by_cases h : a < 1 <;> simp [h] <;> omega

/-- The arrays `primes` writes. -/
abbrev primesArrs : List Nat := [aT, aP, aQ, aPm, aQm]

theorem primes_eq : primes = seqs (ltS X0 aP0 aQ0 ++ ([sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] ++
    (ltS X0 aP aOne ++ ([sel aPm aT aZero X0] ++ (ltS X0 aQ aOne ++ [sel aQm aT aZero X0]))))) := rfl

theorem primes_ok {s0 s : State} {used : List Nat} (c : St s0 used s)
    (one : nm s0 s.mem aOne = 1) (zero : nm s0 s.mem aZero = 0) :
    WP isa primes s fun t => St s0 (primesArrs ++ used) t ∧
      (∀ j < nArr, j ∉ primesArrs → nm s0 t.mem j = nm s0 s.mem j) ∧
      nm s0 t.mem aP = (if nm s0 s.mem aP0 < nm s0 s.mem aQ0 then nm s0 s.mem aQ0 else nm s0 s.mem aP0) ∧
      nm s0 t.mem aQ = (if nm s0 s.mem aP0 < nm s0 s.mem aQ0 then nm s0 s.mem aP0 else nm s0 s.mem aQ0) ∧
      nm s0 t.mem aPm = nm s0 t.mem aP - 1 ∧ nm s0 t.mem aQm = nm s0 t.mem aQ - 1 := by
  have h := c.ws
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  -- A frame keeps the values outside it.
  have kn : ∀ {m m' : Mem} {js ds : List Nat}, VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) js ds m m' →
      (∀ d ∈ ds, d + 8 ≤ hdr) → ∀ {j}, j < nArr → (∀ k ∈ js, k ≠ j) →
        num m' (bOf s0) (wOf s0) j = num m (bOf s0) (wOf s0) j := by
    intro m m' js ds f hd j hj hk; exact f.num hk hd (fit _ hj)
  have hX0 : X0 + 8 ≤ hdr := by decide
  have dX0 : ∀ d ∈ [X0], d + 8 ≤ hdr := by simp [hX0]
  have dnil : ∀ d ∈ ([] : List Nat), d + 8 ≤ hdr := by simp
  rw [primes_eq, wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltS_ok h (d := X0) (a := aP0) (b := aQ0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX0 (by decide)) fun t1 ⟨h1, f1, s1, _, k1⟩ => ?_
  rw [wp_seqs_append (by simp) (by simp [ltS]),
    show seqs [sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] = .seq (sel aP aP0 aQ0 X0) (sel aQ aQ0 aP0 X0) from rfl]
  have b1 : slot t1.mem (bOf s0) X0 ≤ 1 := by rw [s1]; split <;> omega
  refine WP.seq (WP.mono (sel_ok h1 (o := aP) (a := aP0) (b := aQ0) (sl := X0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX0 (by decide) b1) fun t2 ⟨h2, f2, v2, k2⟩ => ?_)
  have b2 : slot t2.mem (bOf s0) X0 ≤ 1 := by rw [f2.slot hX0 (by simp)]; exact b1
  refine WP.mono (sel_ok h2 (o := aQ) (a := aQ0) (b := aP0) (sl := X0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX0 (by decide) b2) fun t3 ⟨h3, f3, v3, k3⟩ => ?_
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltS_ok h3 (d := X0) (a := aP) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX0 (by decide)) fun t4 ⟨h4, f4, s4, e4, k4⟩ => ?_
  rw [wp_seqs_append (by simp) (by simp [ltS]), show seqs [sel aPm aT aZero X0] = sel aPm aT aZero X0 from rfl]
  have b4 : slot t4.mem (bOf s0) X0 ≤ 1 := by rw [s4]; split <;> omega
  refine WP.mono (sel_ok h4 (o := aPm) (a := aT) (b := aZero) (sl := X0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX0 (by decide) b4) fun t5 ⟨h5, f5, v5, k5⟩ => ?_
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltS_ok h5 (d := X0) (a := aQ) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX0 (by decide)) fun t6 ⟨h6, f6, s6, e6, k6⟩ => ?_
  rw [show seqs [sel aQm aT aZero X0] = sel aQm aT aZero X0 from rfl]
  have b6 : slot t6.mem (bOf s0) X0 ≤ 1 := by rw [s6]; split <;> omega
  refine WP.mono (sel_ok h6 (o := aQm) (a := aT) (b := aZero) (sl := X0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hX0 (by decide) b6) fun t ⟨ht, ft, vt, kt⟩ => ?_
  -- The frame and the registers.
  have F : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) primesArrs [X0] s.mem t.mem :=
    have j := fun {m₁ m₂ m₃ : Mem} {js₁ ds₁ js₂ ds₂ : List Nat}
        (a : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) js₁ ds₁ m₁ m₂)
        (b : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) js₂ ds₂ m₂ m₃)
        (h₁ : ∀ j ∈ js₁, j ∈ primesArrs) (h₂ : ∀ d ∈ ds₁, d ∈ [X0]) (h₃ : ∀ j ∈ js₂, j ∈ primesArrs)
        (h₄ : ∀ d ∈ ds₂, d ∈ [X0]) => Frame.join a b h₁ h₂ h₃ h₄
    j (j (j (j (j (j f1 f2 (by simp) (by simp) (by simp) (by simp)) f3 (by simp) (by simp) (by simp) (by simp))
      f4 (by simp) (by simp) (by simp) (by simp)) f5 (by simp) (by simp) (by simp) (by simp))
      f6 (by simp) (by simp) (by simp) (by simp)) ft (by simp) (by simp) (by simp) (by simp)
  have K : Keep stRegs s t :=
    (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans kt).mono (by simp))
  -- The values.
  simp only [nm] at one zero ⊢
  generalize hp : num s.mem (bOf s0) (wOf s0) aP0 = p0 at s1
  generalize hq : num s.mem (bOf s0) (wOf s0) aQ0 = q0 at s1
  have p1 : num t1.mem (bOf s0) (wOf s0) aP0 = p0 := by rw [kn f1 dX0 (by decide) (by decide), hp]
  have q1 : num t1.mem (bOf s0) (wOf s0) aQ0 = q0 := by rw [kn f1 dX0 (by decide) (by decide), hq]
  have q2 : num t2.mem (bOf s0) (wOf s0) aQ0 = q0 := by rw [kn f2 dnil (by decide) (by decide), q1]
  have p2 : num t2.mem (bOf s0) (wOf s0) aP0 = p0 := by rw [kn f2 dnil (by decide) (by decide), p1]
  have vP3 : num t3.mem (bOf s0) (wOf s0) aP = if p0 < q0 then q0 else p0 := by
    rw [kn f3 dnil (by decide) (by decide), v2, s1, p1, q1]
    by_cases e : p0 < q0 <;> simp [e]
  have vQ3 : num t3.mem (bOf s0) (wOf s0) aQ = if p0 < q0 then p0 else q0 := by
    rw [v3, f2.slot hX0 (by simp), s1, p2, q2]
    by_cases e : p0 < q0 <;> simp [e]
  have o3 : num t3.mem (bOf s0) (wOf s0) aOne = 1 := by
    rw [kn f3 dnil (by decide) (by decide), kn f2 dnil (by decide) (by decide),
      kn f1 dX0 (by decide) (by decide), one]
  have z4 : num t4.mem (bOf s0) (wOf s0) aZero = 0 := by
    rw [kn f4 dX0 (by decide) (by decide), kn f3 dnil (by decide) (by decide),
      kn f2 dnil (by decide) (by decide), kn f1 dX0 (by decide) (by decide), zero]
  have vPm : num t5.mem (bOf s0) (wOf s0) aPm = num t3.mem (bOf s0) (wOf s0) aP - 1 := by
    rw [v5, s4, e4, o3, z4]
    exact pred_sel
  have vP : num t.mem (bOf s0) (wOf s0) aP = num t3.mem (bOf s0) (wOf s0) aP := by
    rw [kn ft dnil (by decide) (by decide), kn f6 dX0 (by decide) (by decide),
      kn f5 dnil (by decide) (by decide), kn f4 dX0 (by decide) (by decide)]
  have q5 : num t5.mem (bOf s0) (wOf s0) aQ = num t3.mem (bOf s0) (wOf s0) aQ := by
    rw [kn f5 dnil (by decide) (by decide), kn f4 dX0 (by decide) (by decide)]
  have vQ : num t.mem (bOf s0) (wOf s0) aQ = num t3.mem (bOf s0) (wOf s0) aQ := by
    rw [kn ft dnil (by decide) (by decide), kn f6 dX0 (by decide) (by decide), q5]
  have o5 : num t5.mem (bOf s0) (wOf s0) aOne = 1 := by
    rw [kn f5 dnil (by decide) (by decide), kn f4 dX0 (by decide) (by decide), o3]
  have z6 : num t6.mem (bOf s0) (wOf s0) aZero = 0 := by
    rw [kn f6 dX0 (by decide) (by decide), kn f5 dnil (by decide) (by decide), z4]
  refine ⟨c.step ht F (by decide) (by simp [X0, hdr_eq]) K, fun j hj hn => kn F dX0 hj (fun k hk e => hn (e ▸ hk)),
    by rw [vP, vP3], by rw [vQ, vQ3], ?_, ?_⟩
  · rw [kn ft dnil (by decide) (by decide), kn f6 dX0 (by decide) (by decide), vPm, vP]
  · rw [vt, s6, e6, o5, z6, q5, vQ]
    exact pred_sel

end VG.Proof.RsaKeyGen.RISCV64.Key
