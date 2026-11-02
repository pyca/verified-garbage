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
open VG.Impl.Rsa.RISCV64.Keys (seqs copy sub3 sel half bitOf stBorrow)
open VG.Impl.RsaKeyGen.RISCV64.Key (aZero)
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
abbrev stRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a2, .a3, .a5, .a6, .a7, .s7, .s8]

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

/-! ## The halving -/

section
variable {s : State} {B : Addr} {Z w : Nat}

theorem li_t4_zero (u : State) :
    WP isa (.block [.li .t4 0]) u fun v => (v.gpr .t4 = 0#64 ∧ v.mem = u.mem) ∧ Keep [.t4] u v := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : exec (.li .t4 0) u = some (u.write .t4 (BitVec.ofNat 64 0)) := exec_li_small (x := 0) (by decide)
  brun [e]

theorem halfSel_eq (j : Nat) : seqs (halfSel j) =
    .seq (copy aT j) (.seq (.block [.li .t4 0]) (.seq (half aT) (sel j j aT X2))) := rfl

/-- `halfSel j`: `[j]` halved under `X2`. -/
theorem halfSel_ok (h : Ws s B Z w nArr) {j : Nat} (hj : j < nArr) (hjT : j ≠ aT)
    (bit : slot s.mem B X2 ≤ 1) :
    WP isa (seqs (halfSel j)) s fun t => Ws t B Z w nArr ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame B w [aT, j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B X2 = 0 then num s.mem B w j else num s.mem B w j / 2) ∧
      Keep opRegs s t := by
  have hX2 : X2 + 8 ≤ hdr := by decide
  rw [halfSel_eq]
  refine WP.seq (WP.mono (copy_ok h (o := aT) (a := j) (by decide) hj (by decide) (Ne.symm hjT))
    fun t1 ⟨h1, f1, v1, k1, _⟩ => ?_)
  refine WP.seq (WP.mono (li_t4_zero t1) fun t2 ⟨⟨z2, m2⟩, k2⟩ => ?_)
  have h2 := h1.of_keep k2
  refine WP.seq (WP.mono (half_ok h2 (j := aT) (by decide) (by decide) (by rw [z2]; decide))
    fun t3 ⟨h3, f3, v3, _, k3⟩ => ?_)
  have sl3 : slot t3.mem B X2 = slot s.mem B X2 := by
    rw [f3.slot hX2 (by simp), m2, f1.slot hX2 (by simp)]
  refine WP.mono (sel_self_ok h3 (o := j) (b := aT) (sl := X2) hj (by decide) (by decide) hjT hX2
    (by decide) (by rw [sl3]; exact bit)) fun t ⟨ht, ft, vt, kt⟩ => ?_
  have fj := h.fit64 hj
  have jS : num t3.mem B w j = num s.mem B w j := by
    rw [f3.num (by simpa using Ne.symm hjT) (by simp) fj, m2, f1.num (by simpa using Ne.symm hjT) (by simp) fj]
  refine ⟨ht, ?_, ?_, ?_⟩
  · have f2 : VG.Proof.Rsa.RISCV64.Keys.Frame B w [aT, j] [] t1.mem t2.mem := by
      rw [m2]; exact VG.Proof.Rsa.RISCV64.Keys.Frame.refl _ _ _ _ _
    exact ((f1.mono.trans f2.mono).trans f3.mono).trans ft.mono
  · rw [vt, sl3, jS, v3, z2, m2, v1]
    simp
  · exact (((k1.trans k2).trans k3).trans kt).mono (by simp)

/-- `halfStep`'s instructions, re-associated. -/
theorem halfStep_eq : halfStep = seqs (.block (VG.Impl.Rsa.RISCV64.Keys.bitOf X0 aU ++
    (VG.Impl.Rsa.RISCV64.Keys.bitOf X1 aV ++ (notS X1 X1 ++ andNotS X2 X0 X1))) ::
    (halfSel aU ++ (halfSel aV ++ (halfSel aF ++ ([.block [.addi .s7 .s7 (-1)]] : List (Prog isa)))))) := rfl

/-- One step of the halving. -/
theorem halfStep_ok (h : Ws s B Z w nArr) :
    WP isa halfStep s fun t => Ws t B Z w nArr ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame B w [aT, aU, aV, aF] [X0, X1, X2] s.mem t.mem ∧
      (num t.mem B w aU, num t.mem B w aV, num t.mem B w aF) =
        halveStep (num s.mem B w aU, num s.mem B w aV, num s.mem B w aF) ∧
      Keep (.s7 :: opRegs) s t ∧ t.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 := by
  have hX0 : X0 + 8 ≤ hdr := by decide
  have hX1 : X1 + 8 ≤ hdr := by decide
  have hX2 : X2 + 8 ≤ hdr := by decide
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  rw [halfStep_eq, wp_seqs_cons (by simp [halfSel]), WP.block_append_iff]
  refine WP.mono (bitOf_ok h (sl := X0) (j := aU) (by decide) (by decide) hX0 (by decide))
    fun t1 ⟨h1, f1, v1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bitOf_ok h1 (sl := X1) (j := aV) (by decide) (by decide) hX1 (by decide))
    fun t2 ⟨h2, f2, v2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (notS_ok h2 (d := X1) (a := X1) hX1 (by decide) hX1 (by decide)
    (by rw [v2]; omega)) fun t3 ⟨h3, f3, v3, k3⟩ => ?_
  have x0 : slot t3.mem B X0 = num s.mem B w aU % 2 := by
    rw [f3.slot hX0 (by simp [X0, X1]), f2.slot hX0 (by simp [X0, X1]), v1]
  refine WP.mono (andNotS_ok h3 (d := X2) (a := X0) (b := X1) hX2 (by decide) hX0 (by decide) hX1 (by decide)
    (by rw [x0]; omega) (by rw [v3]; omega)) fun t4 ⟨h4, f4, v4, k4⟩ => ?_
  have uV : num t1.mem B w aV = num s.mem B w aV := f1.num (by simp) (by simp [X0, hdr_eq]) (fit _ (by decide))
  have x2 : slot t4.mem B X2 = if num s.mem B w aU % 2 = 0 ∧ num s.mem B w aV % 2 = 0 then 1 else 0 := by
    rw [v4, x0, v3, v2, uV]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aV) with b | b <;> simp [a, b]
  have b4 : slot t4.mem B X2 ≤ 1 := by rw [x2]; split <;> omega
  -- The frame of the block, on arrays: none.
  have F4 : VG.Proof.Rsa.RISCV64.Keys.Frame B w [] [X0, X1, X2] s.mem t4.mem :=
    ((f1.mono.trans f2.mono).trans f3.mono).trans f4.mono
  have n4 : ∀ j < nArr, num t4.mem B w j = num s.mem B w j :=
    fun j hj => F4.num (by simp) (by simp [X0, X1, X2, hdr_eq]) (fit j hj)
  rw [wp_seqs_append (by simp [halfSel]) (by simp [halfSel])]
  refine WP.mono (halfSel_ok h4 (j := aU) (by decide) (by decide) b4) fun t5 ⟨h5, f5, v5, k5⟩ => ?_
  have s5 : slot t5.mem B X2 = slot t4.mem B X2 := f5.slot hX2 (by simp)
  rw [wp_seqs_append (by simp [halfSel]) (by simp [halfSel])]
  refine WP.mono (halfSel_ok h5 (j := aV) (by decide) (by decide) (by rw [s5]; exact b4))
    fun t6 ⟨h6, f6, v6, k6⟩ => ?_
  have s6 : slot t6.mem B X2 = slot t4.mem B X2 := by rw [f6.slot hX2 (by simp), s5]
  rw [wp_seqs_append (by simp [halfSel]) (by simp)]
  refine WP.mono (halfSel_ok h6 (j := aF) (by decide) (by decide) (by rw [s6]; exact b4))
    fun t7 ⟨h7, f7, v7, k7⟩ => ?_
  rw [show seqs [Code.block [.addi .s7 .s7 (-1)]] = (.block [.addi .s7 .s7 (-1)] : Prog isa) from rfl]
  have hb : WP isa (.block [.addi .s7 .s7 (-1)]) t7 fun u =>
      (u.gpr .s7 = t7.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t7.mem) ∧ Keep [.s7] t7 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hb fun t ⟨⟨c8, m8⟩, k8⟩ => ?_
  have K7 : Keep opRegs s t7 :=
    (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).mono (by simp))
  have nF : ∀ {m m' : Mem} {js : List Nat}, VG.Proof.Rsa.RISCV64.Keys.Frame B w js [] m m' →
      ∀ {j}, j < nArr → (∀ k ∈ js, k ≠ j) → num m' B w j = num m B w j := by
    intro m m' js f j hj hk; exact f.num hk (by simp) (fit j hj)
  refine ⟨h7.of_keep k8, ?_, ?_, ?_, ?_⟩
  · have f8 : VG.Proof.Rsa.RISCV64.Keys.Frame B w [] [] t7.mem t.mem := by
      rw [m8]; exact VG.Proof.Rsa.RISCV64.Keys.Frame.refl _ _ _ _ _
    exact (((F4.mono.trans f5.mono).trans f6.mono).trans f7.mono).trans f8.mono
  · rw [m8]
    have eU : num t7.mem B w aU = num t5.mem B w aU := by
      rw [nF f7 (by decide) (by decide), nF f6 (by decide) (by decide)]
    have eV : num t7.mem B w aV = num t6.mem B w aV := nF f7 (by decide) (by decide)
    have aV5 : num t5.mem B w aV = num s.mem B w aV := by rw [nF f5 (by decide) (by decide), n4 _ (by decide)]
    have aF6 : num t6.mem B w aF = num s.mem B w aF := by
      rw [nF f6 (by decide) (by decide), nF f5 (by decide) (by decide), n4 _ (by decide)]
    rw [eU, eV, v7, s6, v6, s5, v5, aV5, aF6, n4 _ (by decide), x2, halveStep]
    by_cases e : num s.mem B w aU % 2 = 0 ∧ num s.mem B w aV % 2 = 0 <;> simp [e]
  · exact Keep.mono (K7.trans k8) (by simp)
  · rw [c8, K7.gpr (by decide)]

/-- The halving's invariant after `i` steps from `s0`. -/
def HalveI (s0 : State) (B : Addr) (Z w : Nat) (st : Nat × Nat × Nat) (i : Nat) (t : State) : Prop :=
  Ws t B Z w nArr ∧ VG.Proof.Rsa.RISCV64.Keys.Frame B w [aT, aU, aV, aF] [X0, X1, X2] s0.mem t.mem ∧
    (num t.mem B w aU, num t.mem B w aV, num t.mem B w aF) = halveIter i st ∧ Keep (.s7 :: opRegs) s0 t

/-- The halving's loop. -/
theorem halveLoop_ok {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64) {st : Nat × Nat × Nat}
    (h0 : HalveI s B Z w st 0 s) (hc : s.gpr .s7 = BitVec.ofNat 64 N) :
    WP isa (.loop halfStep (.nonzero .s7)) s (HalveI s B Z w st N) := by
  refine wp_countdown (N := N) hN' hN _ (fun i _ t ⟨ht, ft, vt, kt⟩ _ => ?_) h0 hc
  refine WP.mono (halfStep_ok ht) fun u ⟨hu, fu, vu, ku, cu⟩ =>
    ⟨⟨hu, ft.trans fu, by rw [vu, vt, halveIter_succ'], Keep.trans' kt ku⟩, cu⟩

/-- The arrays the halving writes. -/
abbrev halvingArrs : List Nat := [aT, aU, aV, aF]

theorem halving_eq : halving = .seq (mulTo aF aPm aQm) (.seq (copy aU aPm) (.seq (copy aV aQm)
    (.seq (.block cnt8) (.loop halfStep (.nonzero .s7))))) := rfl

/-- `φ`, and `8 p_len` steps of the halving. -/
theorem halving_ok (h : Ws s B Z w nArr) {L : Nat} (hl : s.gpr .a1 = BitVec.ofNat 64 L) (hL : 0 < L)
    (hL' : 8 * L < 2 ^ 64) (zero : num s.mem B w aZero = 0) :
    WP isa halving s fun t => Ws t B Z w nArr ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame B w halvingArrs [X0, X1, X2] s.mem t.mem ∧
      (num t.mem B w aU, num t.mem B w aV, num t.mem B w aF) = halveIter (8 * L)
        (num s.mem B w aPm, num s.mem B w aQm, num s.mem B w aPm * num s.mem B w aQm % 2 ^ (64 * w)) ∧
      Keep stRegs s t := by
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have nF : ∀ {m m' : Mem} {js : List Nat}, VG.Proof.Rsa.RISCV64.Keys.Frame B w js [] m m' →
      ∀ {j}, j < nArr → (∀ k ∈ js, k ≠ j) → num m' B w j = num m B w j := by
    intro m m' js f j hj hk; exact f.num hk (by simp) (fit j hj)
  rw [halving_eq]
  refine WP.seq (WP.mono (mulTo_ok h (o := aF) (a := aPm) (b := aQm) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) zero) fun t1 ⟨h1, f1, _, v1, k1⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok h1 (o := aU) (a := aPm) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, f2, v2, k2, _⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok h2 (o := aV) (a := aQm) (by decide) (by decide) (by decide) (by decide))
    fun t3 ⟨h3, f3, v3, k3, _⟩ => ?_)
  have K3 : Keep stRegs s t3 := (((k1.trans k2).trans k3).mono (by simp))
  refine WP.seq (WP.mono (cnt8_ok t3 (L := L) (by rw [K3.gpr (by decide), hl])) fun t4 ⟨⟨c4, m4⟩, k4⟩ => ?_)
  have h4 : Ws t4 B Z w nArr := h3.of_keep k4
  have i0 : HalveI t4 B Z w (num t4.mem B w aU, num t4.mem B w aV, num t4.mem B w aF) 0 t4 :=
    ⟨h4, VG.Proof.Rsa.RISCV64.Keys.Frame.refl _ _ _ _ _, rfl, Keep.refl _ _⟩
  refine WP.mono (halveLoop_ok (by omega) hL' i0 c4) fun t ⟨ht, ft, vt, kt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · have f4 : VG.Proof.Rsa.RISCV64.Keys.Frame B w [] [] t3.mem t4.mem := by
      rw [m4]; exact VG.Proof.Rsa.RISCV64.Keys.Frame.refl _ _ _ _ _
    exact (((f1.mono.trans f2.mono).trans f3.mono).trans f4.mono).trans ft.mono
  · rw [vt, m4]
    have u3 : num t3.mem B w aU = num s.mem B w aPm := by
      rw [nF f3 (by decide) (by decide), v2, nF f1 (by decide) (by decide)]
    have v3' : num t3.mem B w aV = num s.mem B w aQm := by
      rw [v3, nF f2 (by decide) (by decide), nF f1 (by decide) (by decide)]
    have f3' : num t3.mem B w aF = num s.mem B w aPm * num s.mem B w aQm % 2 ^ (64 * w) := by
      rw [nF f3 (by decide) (by decide), nF f2 (by decide) (by decide), v1]
    rw [u3, v3', f3']
  · exact ((K3.trans k4).trans kt).mono (by simp)

/-- An array outside a frame keeps its value. -/
theorem frame_num {js ds : List Nat} {m m' : Mem} (f : VG.Proof.Rsa.RISCV64.Keys.Frame B w js ds m m')
    {j : Nat} (fit : arr w j + S w ≤ 2 ^ 64) (hk : ∀ k ∈ js, k ≠ j := by decide)
    (hd : ∀ d ∈ ds, d + 8 ≤ hdr := by decide) : num m' B w j = num m B w j :=
  f.num hk hd fit

/-! ## The gcd -/

/-- The arrays `gcdUV` writes. -/
abbrev gcdArrs : List Nat := [aT, aU2, aV2, aS, aG] ++ invOfArrs

theorem gcdUV_eq : gcdUV = seqs ((([.block (VG.Impl.Rsa.RISCV64.Keys.bitOf X0 aV ++ notS X0 X0),
    sel aU2 aU aV X0, sel aV2 aV aU X0] : List (Prog isa)) ++ ltS X1 aV2 aTwo) ++
    [sel aS aV2 aThree X1, invOf aU2 aS nP, sel aG 1 aOne X1]) := rfl

/-- `gcdUV`: with `[aV]` even, `u, v := [aV], [aU]`, else `[aU], [aV]`; `[aG] := gcd u v`, or 1
for `v ≤ 1`. -/
theorem gcdUV_ok [VG.Proof.Rsa.RISCV64.InvLaw] (h : Ws s B Z w nArr) {L : Nat}
    (hl : s.gpr .a1 = BitVec.ofNat 64 L) (hw : 4 ≤ w) (hLw : 4 * w = L) (hL' : 8 * L < 2 ^ 64)
    (one : num s.mem B w aOne = 1) (two : num s.mem B w aTwo = 2) (three : num s.mem B w aThree = 3)
    (hu : num s.mem B w aU < 2 ^ (8 * L)) (hv : num s.mem B w aV < 2 ^ (8 * L))
    (odd : 2 ≤ (if num s.mem B w aV % 2 = 0 then num s.mem B w aU else num s.mem B w aV) →
      (if num s.mem B w aV % 2 = 0 then num s.mem B w aU else num s.mem B w aV) % 2 = 1) :
    WP isa gcdUV s fun t => Ws t B Z w nArr ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame B w gcdArrs [X0, X1] s.mem t.mem ∧
      num t.mem B w aG = (if (if num s.mem B w aV % 2 = 0 then num s.mem B w aU else num s.mem B w aV) ≤ 1
        then 1 else Nat.gcd (if num s.mem B w aV % 2 = 0 then num s.mem B w aV else num s.mem B w aU)
          (if num s.mem B w aV % 2 = 0 then num s.mem B w aU else num s.mem B w aV)) ∧
      Keep stRegs s t := by
  have fit : ∀ j < nArr, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hX0 : X0 + 8 ≤ hdr := by decide
  have hX1 : X1 + 8 ≤ hdr := by decide
  rw [gcdUV_eq, wp_seqs_append (by simp) (by simp), wp_seqs_append (by simp) (by simp [ltS]),
    wp_seqs_cons (by simp), WP.block_append_iff]
  refine WP.mono (bitOf_ok h (sl := X0) (j := aV) (by decide) (by decide) hX0 (by decide))
    fun t0 ⟨h0, f0, v0, k0⟩ => ?_
  refine WP.mono (notS_ok h0 (d := X0) (a := X0) hX0 (by decide) hX0 (by decide)
    (by rw [v0]; omega)) fun t1 ⟨h1, f1, v1, k1⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  have b1 : slot t1.mem B X0 ≤ 1 := by rw [v1]; omega
  refine WP.mono (sel_ok h1 (o := aU2) (a := aU) (b := aV) (sl := X0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hX0 (by decide) b1) fun t2 ⟨h2, f2, v2, k2⟩ => ?_
  rw [show seqs [sel aV2 aV aU X0] = sel aV2 aV aU X0 from rfl]
  have s2 : slot t2.mem B X0 = slot t1.mem B X0 := f2.slot hX0 (by decide)
  refine WP.mono (sel_ok h2 (o := aV2) (a := aV) (b := aU) (sl := X0) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hX0 (by decide) (by rw [s2]; exact b1)) fun t3 ⟨h3, f3, v3, k3⟩ => ?_
  refine WP.mono (ltS_ok h3 (d := X1) (a := aV2) (b := aTwo) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hX1 (by decide)) fun t4 ⟨h4, f4, x4, _, k4⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  have b4 : slot t4.mem B X1 ≤ 1 := by rw [x4]; split <;> omega
  refine WP.mono (sel_ok h4 (o := aS) (a := aV2) (b := aThree) (sl := X1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hX1 (by decide) b4) fun t5 ⟨h5, f5, v5, k5⟩ => ?_
  rw [wp_seqs_cons (by simp)]
  have K5 : Keep stRegs s t5 := (((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).mono (by simp)
  have hL4 : L / 4 = w := by omega
  have hL : 0 < L := by omega
  have p8 : 4 ≤ 2 ^ (8 * L) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (8 * L) := Nat.pow_le_pow_right (by decide) (by omega)
  have e32 : 32 * w = 8 * L := by omega
  generalize hU : num s.mem B w aU = U at hu odd ⊢
  generalize hV : num s.mem B w aV = V at hv odd ⊢
  have u1 : num t1.mem B w aU = U := by rw [frame_num f1 (fit _ (by decide)), frame_num f0 (fit _ (by decide)), hU]
  have w1 : num t1.mem B w aV = V := by rw [frame_num f1 (fit _ (by decide)), frame_num f0 (fit _ (by decide)), hV]
  have x1 : slot t1.mem B X0 = 1 - V % 2 := by rw [v1, v0, hV]
  have U2 : num t3.mem B w aU2 = if V % 2 = 0 then V else U := by
    rw [frame_num f3 (fit _ (by decide)), v2, x1, u1, w1]
    rcases Nat.mod_two_eq_zero_or_one V with e | e <;> simp [e]
  have V2 : num t3.mem B w aV2 = if V % 2 = 0 then U else V := by
    rw [v3, s2, x1, frame_num f2 (fit _ (by decide)), frame_num f2 (fit _ (by decide)), u1, w1]
    rcases Nat.mod_two_eq_zero_or_one V with e | e <;> simp [e]
  have n3 : ∀ j, j < nArr → j ∉ gcdArrs → num t3.mem B w j = num s.mem B w j := fun j hj hn => by
    have F : VG.Proof.Rsa.RISCV64.Keys.Frame B w gcdArrs [X0, X1] s.mem t3.mem :=
      (((f0.mono.trans f1.mono).trans f2.mono).trans f3.mono)
    exact F.num (j := j) (fun k hk e => hn (e ▸ hk)) (by decide) (fit j hj)
  have t3T : num t3.mem B w aTwo = 2 := by rw [n3 aTwo (by decide) (by decide), two]
  rw [t3T, V2] at x4
  generalize hu' : (if V % 2 = 0 then V else U) = u at U2 ⊢
  generalize hv' : (if V % 2 = 0 then U else V) = v at V2 odd x4 ⊢
  have uB : u < 2 ^ (8 * L) := by rw [← hu']; split <;> omega
  have vB : v < 2 ^ (8 * L) := by rw [← hv']; split <;> omega
  have u5 : num t5.mem B w aU2 = u := by
    rw [frame_num f5 (fit _ (by decide)), frame_num f4 (fit _ (by decide)), U2]
  have m5 : num t5.mem B w aS = if v < 2 then 3 else v := by
    rw [v5, x4, frame_num f4 (fit _ (by decide)), V2, frame_num f4 (fit _ (by decide)),
      n3 aThree (by decide) (by decide), three]
    by_cases e : v < 2 <;> simp [e]
  have mB : num t5.mem B w aS < 2 ^ (8 * L) := by rw [m5]; split <;> omega
  have modd : num t5.mem B w aS % 2 = 1 := by
    rw [m5]; split
    · rfl
    · exact odd (by omega)
  refine WP.mono (invOf_ok h5 (a := aU2) (m := aS) (n := w) (by decide) (by decide) hw
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    (fun u hu => by
      have := nP_ok u (L := L) (by rw [hu .a1 (by decide), K5.gpr (by decide), hl]) (by omega)
      rwa [hL4] at this)
    (by rw [e32, u5]; exact uB) (by rw [e32]; exact mB) modd)
    fun t6 ⟨h6, f6, k6, v6⟩ => ?_
  rw [show seqs [sel aG 1 aOne X1] = sel aG 1 aOne X1 from rfl]
  have s6 : slot t6.mem B X1 = slot t4.mem B X1 := by rw [f6.slot hX1 (by decide), f5.slot hX1 (by decide)]
  refine WP.mono (sel_ok h6 (o := aG) (a := 1) (b := aOne) (sl := X1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hX1 (by decide) (by rw [s6]; exact b4)) fun t ⟨ht, ft, vt, kt⟩ => ?_
  refine ⟨ht, ?_, ?_, ((K5.trans k6).trans kt).mono (by simp)⟩
  · exact (((((((f0.mono.trans f1.mono).trans f2.mono).trans f3.mono).trans f4.mono).trans f5.mono).trans
      f6.mono).trans ft.mono)
  -- The values.
  have m1 : 1 < num t5.mem B w aS := by rw [m5]; split <;> omega
  have o6 : num t6.mem B w aOne = 1 := by
    rw [frame_num f6 (fit _ (by decide)), frame_num f5 (fit _ (by decide)), frame_num f4 (fit _ (by decide)),
      n3 aOne (by decide) (by decide), one]
  have ⟨g6, _, _⟩ := v6 m1
  rw [vt, s6, x4]
  by_cases e : v < 2
  · simp [e, show v ≤ 1 from by omega, o6]
  · simp only [e, show ¬ v ≤ 1 by omega, ↓reduceIte]
    rw [g6, u5, m5]
    simp only [e, ↓reduceIte]

/-! ## The division -/

/-- `divBy q d`: `[q] := [q] / [d]`, for `0 < [d]`, keeping `aDv`'s extra word 0. -/
theorem divBy_ok (h : Ws s B Z w nArr) {q d : Nat} (hq : q < nArr) (hd : d < nArr) (hq1 : q ≠ aDv)
    (hq2 : q ≠ aDr) (hq3 : q ≠ aDt) (hd1 : d ≠ aDv) (hdv : word s.mem B (arr w aDv + 8 * w) = 0)
    (hD : 0 < num s.mem B w d) :
    WP isa (divBy q d) s fun t => Ws t B Z w nArr ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame B w [aDv, q, aDr, aDt] [] s.mem t.mem ∧
      num t.mem B w q = num s.mem B w q / num s.mem B w d ∧
      word t.mem B (arr w aDv + 8 * w) = 0 ∧ Keep stRegs s t := by
  have fv := h.fit64 (j := aDv) (by decide)
  have hS : S w = 8 * (w + 2) := rfl
  rw [show divBy q d = .seq (copy aDv d) (VG.Impl.Rsa.RISCV64.Div.div q aDr aDv aDt) from rfl]
  refine WP.seq (WP.mono (copy_ok h (o := aDv) (a := d) (by decide) hd (by decide) (Ne.symm hd1))
    fun t1 ⟨h1, f1, v1, k1, o1⟩ => ?_)
  have z1 : word t1.mem B (arr w aDv + 8 * w) = 0 := by
    rw [o1.word (Or.inr (Nat.le_refl _)) (by omega), hdv]
  refine WP.mono (div_ok h1 (q := q) (r := aDr) (d := aDv) (t := aDt) hq (by decide) (by decide) (by decide)
    (by decide) hq2 hq1 hq3 (by decide) (by decide) (by decide) z1) fun t ⟨ht, ft, kt, _, vt⟩ => ?_
  have q1 : num t1.mem B w q = num s.mem B w q := f1.num (by simpa using hq1.symm) (by simp) (h.fit64 hq)
  have ⟨eq, _⟩ := vt (by rw [v1]; exact hD)
  refine ⟨ht, f1.mono.trans ft.mono, by rw [eq, q1, v1], ?_, (k1.trans kt).mono (by simp)⟩
  rw [ft.word (j := aDv) (i := w) (by omega) (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    exacts [hq1, by decide, by decide]) (by simp) fv, z1]

end

/-! ## `lcm(p - 1, q - 1)` -/

/-- The arrays `lcmPart` writes. -/
abbrev lcmArrs : List Nat := [aT, aU, aV, aF, aU2, aV2, aS, aG, aL, aDv, aDr, aDt] ++ invOfArrs

theorem lcmPart_eq : lcmPart = .seq halving (.seq gcdUV (.seq (copy aL aF) (divBy aL aG))) := rfl

/-- `[aL] := lcm(p - 1, q - 1)`, from `p - 1` and `q - 1` below `2^(8 p_len)`. `aDv`'s
extra word (`w`) is 0 before and after (only copies write `aDv`), as the later
divisions need. -/
theorem lcmPart_ok [VG.Proof.Rsa.RISCV64.InvLaw] {s0 s : State} {used : List Nat} (h : PreC s0) (c : St s0 used s)
    (one : nm s0 s.mem aOne = 1) (two : nm s0 s.mem aTwo = 2) (three : nm s0 s.mem aThree = 3)
    (zero : nm s0 s.mem aZero = 0)
    (hpm : nm s0 s.mem aPm < 2 ^ (8 * pLen s0)) (hqm : nm s0 s.mem aQm < 2 ^ (8 * pLen s0))
    (hdv : word s.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0) :
    WP isa lcmPart s fun t => St s0 (lcmArrs ++ used) t ∧
      (∀ j < nArr, j ∉ lcmArrs → nm s0 t.mem j = nm s0 s.mem j) ∧
      nm s0 t.mem aL = Nat.lcm (nm s0 s.mem aPm) (nm s0 s.mem aQm) ∧
      word t.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0 := by
  have hw := h.wOf_eq
  have ⟨_, w8, w128⟩ := h.fits
  have fit : ∀ j < nArr, arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 := fun j hj => c.fit hj
  have hl := pLen_ofNat c.cb
  simp only [nm] at one two three zero hpm hqm ⊢
  generalize hL : pLen s0 = L at hl hpm hqm hw
  have hL0 : 0 < L := by omega
  have hL' : 8 * L < 2 ^ 64 := by omega
  rw [lcmPart_eq]
  refine WP.seq (WP.mono (halving_ok c.ws hl hL0 hL' zero) fun t1 ⟨h1, f1, v1, k1⟩ => ?_)
  have kp : Keep stRegs s t1 := k1
  have n1 : ∀ j, j < nArr → j ∉ halvingArrs → num t1.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j := fun j hj hn =>
    f1.num (j := j) (fun k hk e => hn (e ▸ hk)) (by decide) (fit j hj)
  -- The halving's values.
  generalize hP : num s.mem (bOf s0) (wOf s0) aPm = P at hpm hqm v1 ⊢
  generalize hQ : num s.mem (bOf s0) (wOf s0) aQm = Q at hpm hqm v1 ⊢
  have hPQ : P * Q % 2 ^ (64 * (wOf s0)) = P * Q := by
    apply Nat.mod_eq_of_lt
    have e : 64 * (wOf s0) = 8 * L + 8 * L := by omega
    rw [e, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hpm hqm
  rw [hPQ] at v1
  have hle := lcm_eq hpm hqm
  have hb := halveIter_bounds (8 * L) (st := (P, Q, P * Q)) (a := 2 ^ (8 * L)) (b := 2 ^ (8 * L))
    (f := P * Q + 1) ⟨hpm, hqm, Nat.lt_succ_self _⟩
  generalize hst : halveIter (8 * L) (P, Q, P * Q) = st at v1 hle hb
  obtain ⟨U, V, F⟩ := st
  simp only [Prod.mk.injEq] at v1
  obtain ⟨vU, vV, vF⟩ := v1
  dsimp only at hle hb
  refine WP.seq (WP.mono (gcdUV_ok h1 (L := L) (by rw [k1.gpr (by decide), hl]) (by omega) hw hL'
    (by rw [n1 _ (by decide) (by decide), one])
    (by rw [n1 _ (by decide) (by decide), two]) (by rw [n1 _ (by decide) (by decide), three])
    (by rw [vU]; exact hb.1) (by rw [vV]; exact hb.2.1) (by rw [vU, vV]; exact hle.1))
    fun t2 ⟨h2, f2, v2, k2⟩ => ?_)
  rw [vU, vV] at v2
  refine WP.seq (WP.mono (copy_ok h2 (o := aL) (a := aF) (by decide) (by decide) (by decide) (by decide))
    fun t3 ⟨h3, f3, v3, k3, _⟩ => ?_)
  have g3 : num t3.mem (bOf s0) (wOf s0) aG = num t2.mem (bOf s0) (wOf s0) aG := f3.num (by decide) (by decide) (fit _ (by decide))
  have d3 : word t3.mem (bOf s0) (arr (wOf s0) aDv + 8 * (wOf s0)) = 0 := by
    rw [f3.word (by omega) (by decide) (by decide) (fit _ (by decide)),
      f2.word (by omega) (by decide) (by decide) (fit _ (by decide)),
      f1.word (by omega) (by decide) (by decide) (fit _ (by decide)), hdv]
  have gpos : 0 < num t3.mem (bOf s0) (wOf s0) aG := by
    rw [g3, v2]
    by_cases e : (if V % 2 = 0 then U else V) ≤ 1
    · simp only [e, ↓reduceIte]; decide
    · simp only [e, ↓reduceIte]; exact Nat.gcd_pos_of_pos_right _ (by omega)
  refine WP.mono (divBy_ok h3 (q := aL) (d := aG) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) d3 gpos) fun t ⟨ht, ft, vt, dt, kt⟩ => ?_
  have F : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) lcmArrs [X0, X1, X2] s.mem t.mem :=
    ((f1.mono.trans f2.mono).trans f3.mono).trans ft.mono
  have K : Keep stRegs s t := (((kp.trans k2).trans k3).trans kt).mono (by simp)
  refine ⟨c.step ht F (by decide) (by decide) K, fun j hj hn => F.num (j := j) (fun k hk e => hn (e ▸ hk))
    (by decide) (fit j hj), ?_, dt⟩
  rw [vt, g3, v2, v3, frame_num f2 (fit _ (by decide)), vF, hle.2]

end VG.Proof.RsaKeyGen.RISCV64.Key
