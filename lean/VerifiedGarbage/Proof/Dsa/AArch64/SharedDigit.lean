module
public import VerifiedGarbage.Impl.Dsa.AArch64.SharedPower
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
public import VerifiedGarbage.Proof.Dsa.SharedPower
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorBody
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One digit of both exponents

After `k` digits, bucket `d` of `x` holds `g^(bexp x k d)`, bucket `d` of
`q` holds `g^(bexp q k d)`, and `[aXc]` holds `g^(8^k)`, all in Montgomery
form. A digit multiplies `[aXc]` into the bucket of each exponent's digit
(`q`'s only when it is not zero), and cubes `[aXc]` by three squarings. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- The buckets and the base's power after `k` digits of `ex` and `eq`. -/
structure DigitInv (P : Addr) (wx : Nat) (minv : BitVec 64) (N g ex eq k : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv N (wv t.mem P (slot wx Crt.aXc) wx)
  tab : word t.mem P (8 * Crt.sTab) = off P (slot wx 8)
  lt : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx < N
  xs : ∀ d < 8, wv t.mem P (slot wx (8 + d)) wx % N = g ^ bexp ex k d * 2 ^ (64 * wx) % N
  qs : ∀ d < 8, d ≠ 0 → wv t.mem P (slot wx (8 + (8 + d))) wx % N = g ^ bexp eq k d * 2 ^ (64 * wx) % N
  alt : wv t.mem P (slot wx Crt.aXc) wx < N
  a : wv t.mem P (slot wx Crt.aXc) wx % N = g ^ 8 ^ k * 2 ^ (64 * wx) % N

/-- `[aXc] := [aXc]² R⁻¹`. -/
theorem baseSq_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hA : Xc < N) :
    WP isa (M.mm Crt.aXc Crt.aXc Crt.aXc) s fun t =>
      CExpCtx t P wx minv N (wv t.mem P (slot wx Crt.aXc) wx) ∧ wv t.mem P (slot wx Crt.aXc) wx < N ∧
      wv t.mem P (slot wx Crt.aXc) wx * 2 ^ (64 * wx) % N = Xc * Xc % N ∧
      Arrays P wx [aAcc, aTmp, Crt.aXc] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  refine WP.mono (M.mm_ok (o := Crt.aXc) (a := Crt.aXc) (b := Crt.aXc) hc.good (Nat.le_refl _) hw
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc.inv (by rw [hc.n, hc.x]; exact hA)) fun t ⟨hg, hlt, hm, ha, k⟩ => ?_
  rw [hc.n] at hlt hm
  rw [hc.x] at hm
  refine ⟨⟨hg, hc.scrT.congr k.wr, (ha.wv_of_not_mem (show aN < 8 by decide) (by decide) hnZ).trans hc.n, ?_,
    rfl⟩, hlt, hm, ha, k⟩
  rw [ha.word0_of_not_mem (show aN < 8 by decide) (by decide) hnZ (by omega_arith)]
  exact hc.inv

/-- The digits' values and count move on. -/
theorem digitEnd_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc V Q b : Nat}
    (hc : CExpCtx s P wx minv N Xc) (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (.block digitEnd) s fun t =>
      (t.mem = ((s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).writeW
        (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 (Q / 8))).writeW (off P (8 * Crt.sBit))
          (BitVec.ofNat 64 (b - 1)) ∧ t.gpr .x3 = BitVec.ofNat 64 (b - 1)) ∧ Keep [.x3] s t := by
  obtain hQ₁ : (s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).readW (off P (8 * Crt.sMaskX)) 64 =
      BitVec.ofNat 64 Q := by
    rw [← hQ]; exact hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) (by decide) (by decide)
  obtain hb₂ : (((s.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V / 8))).writeW
      (off P (8 * Crt.sMaskX)) (BitVec.ofNat 64 (Q / 8))).readW (off P (8 * Crt.sBit)) 64) =
      BitVec.ofNat 64 b := by
    rw [← hb]
    exact (hdrStore_hdr (i := Crt.sMaskX) _ _ _ (by decide) (by decide) (by decide)).trans
      (hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) (by decide) (by decide))
  refine WP.keep [.x3] ?_ rfl rfl rfl
  brun [digitEnd, hc.good.x0, hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sMaskX < 32 by decide),
    hdr_enc (show Crt.sBit < 32 by decide), hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sV) (by decide),
    hc.ld (i := Crt.sMaskX) (by decide), hc.st (i := Crt.sMaskX) (by decide),
    hc.ld (i := Crt.sBit) (by decide), hc.st (i := Crt.sBit) (by decide), hV, hQ₁, hb₂,
    WindowVector.shr3_width hV', WindowVector.shr3_width hQ', VG.Offset.ofNat_sub_ofNat hb1]

theorem digit_eq (mul : Nat → Nat → Nat → Prog isa) : digit mul =
    seqs (([.block secretDigit, Crt.select, mul Crt.aT Crt.aT Crt.aXc, store] : List (Prog isa)) ++
      (([.block publicDigit, .ite (.zero .x .x3) (.block []) (publicBucket mul)] : List (Prog isa)) ++
        ([mul Crt.aXc Crt.aXc Crt.aXc, mul Crt.aXc Crt.aXc Crt.aXc, mul Crt.aXc Crt.aXc Crt.aXc,
          .block digitEnd] : List (Prog isa)))) := rfl

/-- One digit of each exponent, the low three bits of the values `V` and
`Q` in `sV` and `sMaskX`: the buckets and the base's power move from `k`
digits to `k + 1`, the values move down three bits, and the digits' count
`b` drops, into `x3`. -/
theorem digit_ok (M : Mont) {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N g ex eq k V Q b : Nat}
    (hw : 8 ≤ wx) (hw' : wx < 2 ^ 30) (hd : wx % 8 = 0) (hR : Nat.Coprime (2 ^ (64 * wx)) N)
    (hI : DigitInv P wx minv N g ex eq k s)
    (hV : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) (hVd : V % 8 = ex / 8 ^ k % 8)
    (hQ : word s.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 Q) (hQ' : Q < 2 ^ 64) (hQd : Q % 8 = eq / 8 ^ k % 8)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) :
    WP isa (digit M.mm) s fun t => DigitInv P wx minv N g ex eq (k + 1) t ∧
      word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (V / 8) ∧
      word t.mem P (8 * Crt.sMaskX) = BitVec.ofNat 64 (Q / 8) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧ t.gpr .x3 = BitVec.ofNat 64 (b - 1) ∧
      (∀ j < 8, j ≠ aAcc → j ≠ aTmp → j ≠ aY → j ≠ Crt.aT → j ≠ Crt.aXc →
        wv t.mem P (slot wx j) wx = wv s.mem P (slot wx j) wx) ∧
      (∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sEnt → i ≠ Crt.sJ → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
        word t.mem P (8 * i) = word s.mem P (8 * i)) ∧
      Frm P (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hI.ctx.scrT.nowrap
  obtain hnZ : P.toNat + slot wx 8 ≤ 2 ^ 64 := by omega_arith
  obtain hw2 : 2 ≤ wx := by omega_arith
  obtain hdx : ex / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain hdq : eq / 8 ^ k % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [digit_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (secretBucket_ok M hI.ctx hw hw' hd hI.tab hV hV' hI.alt)
    fun a ⟨hca, ltA, valA, othA, arrA, hdrA, frmA, kA⟩ => ?_)
  rw [hVd] at ltA valA othA
  refine wp_seqs_append (by simp) (by simp) (WP.mono (publicHalf_ok M hca hw2 hw'
    ((hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hI.tab)
    ((hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hQ) hQ' hI.alt)
    fun b' ⟨hcb, valB, othB, arrB, hdrB, frmB, kB⟩ => ?_)
  rw [hQd] at valB othB
  simp only [seqs]
  refine WP.seq (WP.mono (baseSq_ok M hcb hw2 hw' hI.alt) fun c₁ ⟨hc₁, lt₁, v₁, a₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (baseSq_ok M hc₁ hw2 hw' lt₁) fun c₂ ⟨hc₂, lt₂, v₂, a₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (baseSq_ok M hc₂ hw2 hw' lt₂) fun c₃ ⟨hc₃, lt₃, v₃, a₃, k₃⟩ => ?_)
  obtain a13 : Arrays P wx [aAcc, aTmp, Crt.aXc] b'.mem c₃.mem := (a₁.trans a₂).trans a₃
  obtain hdrC : ∀ i < 32, i ≠ Crt.sNib → i ≠ Crt.sEnt → i ≠ Crt.sJ →
      word c₃.mem P (8 * i) = word s.mem P (8 * i) := fun i hi h1 h2 h3 => by
    rw [a13.hslot hi, hdrB i hi h1 h2 h3, hdrA i hi h1 h2 h3]
  refine WP.mono (digitEnd_ok hc₃ (V := V) (Q := Q) (b := b)
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hV) hV'
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hQ) hQ'
    ((hdrC _ (by decide) (by decide) (by decide) (by decide)).trans hb) hb1) fun t ⟨⟨hm, h3⟩, kD⟩ => ?_
  obtain oD : Outside P 136 120 c₃.mem t.mem := by
    rw [hm]
    exact ((fn_outside _ P _ (by decide) (by decide)).trans (fn_outside _ P _ (by decide) (by decide))).trans
      (fn_outside _ P _ (by decide) (by decide))
  -- The entries, in terms of the state after the buckets' updates.
  obtain ent : ∀ j < 16, wv t.mem P (slot wx (8 + j)) wx = wv b'.mem P (slot wx (8 + j)) wx := fun j hj => by
    rw [fn_ent oD hn hj, arr_ent a13 (by decide) hn hj]
  obtain entX : ∀ d < 8, wv b'.mem P (slot wx (8 + d)) wx = wv a.mem P (slot wx (8 + d)) wx := fun d hd' =>
    othB d (by omega_arith) (Or.inl (by omega_arith))
  obtain aX : wv t.mem P (slot wx Crt.aXc) wx = wv c₃.mem P (slot wx Crt.aXc) wx := fn_arr oD hn (by decide)
  obtain aval : wv c₃.mem P (slot wx Crt.aXc) wx % N = g ^ 8 ^ (k + 1) * 2 ^ (64 * wx) % N := by
    obtain e₁ := VG.Proof.Bignum.mont_sq hR hI.a v₁
    obtain e₂ := VG.Proof.Bignum.mont_sq hR e₁ v₂
    obtain e₃ := VG.Proof.Bignum.mont_sq hR e₂ v₃
    rw [e₃, show 2 * (2 * (2 * 8 ^ k)) = 8 ^ (k + 1) by rw [Nat.pow_succ]; omega_arith]
  obtain xval : ∀ d < 8, wv a.mem P (slot wx (8 + d)) wx % N = g ^ bexp ex (k + 1) d * 2 ^ (64 * wx) % N := by
    intro d hd'
    by_cases he : ex / 8 ^ k % 8 = d
    · subst he
      rw [bexp_digit]
      exact mont_mulT hR (hI.xs _ hd') hI.a valA
    · rw [othA d (by omega_arith) (Ne.symm he), bexp_other he]
      exact hI.xs d hd'
  obtain qval : ∀ d < 8, d ≠ 0 →
      wv b'.mem P (slot wx (8 + (8 + d))) wx % N = g ^ bexp eq (k + 1) d * 2 ^ (64 * wx) % N := by
    intro d hd' hd0
    by_cases he : eq / 8 ^ k % 8 = d
    · subst he
      obtain hv := (valB hd0).2
      rw [othA _ (by omega_arith) (by omega_arith)] at hv
      rw [bexp_digit]
      exact mont_mulT hR (hI.qs _ hd' hd0) hI.a hv
    · rw [othB (8 + d) (by omega_arith) (Or.inl (by omega_arith)), othA _ (by omega_arith) (by omega_arith),
        bexp_other he]
      exact hI.qs d hd' hd0
  obtain ltB : ∀ j < 16, wv b'.mem P (slot wx (8 + j)) wx < N := by
    intro j hj
    by_cases hq : j = 8 + eq / 8 ^ k % 8 ∧ eq / 8 ^ k % 8 ≠ 0
    · rw [hq.1]; exact (valB hq.2).1
    · rw [othB j hj (by omega_arith)]
      by_cases hx : j = ex / 8 ^ k % 8
      · rw [hx]; exact ltA
      · rw [othA j hj hx]; exact hI.lt j hj
  refine ⟨⟨by rw [aX]; exact ctx_of_fn hc₃ oD kD.wr (kD.gpr .x0 (by decide)), ?_, fun j hj => ?_, fun d hd' => ?_,
    fun d hd' hd0 => ?_, by rw [aX]; exact lt₃, by rw [aX]; exact aval⟩, ?_, ?_, ?_, h3, fun j hj h1 h2 h3 h4 h5 => ?_,
    fun i hi h1 h2 h3 h4 h5 h6 => ?_, ?_, ((((kA.trans kB).trans k₁).trans k₂).trans k₃).trans kD |>.mono (by decide)⟩
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrC _ (by decide) (by decide) (by decide) (by decide)]
    exact hI.tab
  · rw [ent j hj]; exact ltB j hj
  · rw [ent d (by omega_arith), entX d hd']; exact xval d hd'
  · rw [ent (8 + d) (by omega_arith)]; exact qval d hd' hd0
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [fn_arr oD hn hj, a13.wv_of_not_mem hj (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h5⟩) hnZ,
      arrB j hj h1 h2 h3 h4, arrA j hj h1 h2 h3 h4]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h6), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h5),
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h4), hdrC i hi h1 h2 h3]
  · exact ((frmA.trans frmB).trans (arrays_work a13 (by decide))).trans (fn_work oD)

end VG.Proof.Dsa.AArch64.SharedPower
