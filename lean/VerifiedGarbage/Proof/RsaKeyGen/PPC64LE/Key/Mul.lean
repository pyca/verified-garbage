module

import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env

/-!
# `vg_rsa_keygen_key` on PPC64LE: the products

`mulToE`: `mulTo o a b k`, `k` setting `r11` to `K`, writes
`([a] ([b] mod 2^K)) mod 2^(32 w)` to `[o]`. Each step of `mulLoop` adds
`[aMa]` (`A 2^i`) to `[aMo]` under the low bit of `[aMb]` (`⌊B / 2^i⌋`),
doubles `[aMa]` and halves `[aMb]` (`mulStep_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel half bitOf aZero sOdd sB sC)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aMo aMa aMb aMm aMn mulStep mulLoop mulTo addTo)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The arrays `mulTo` writes but its result. -/
abbrev mulArrs : List Nat := [aMo, aMa, aMb, aMm, aMn]

theorem mod_pow_succ_bit (B i : Nat) : B % 2 ^ (i + 1) = B % 2 ^ i + 2 ^ i * (B / 2 ^ i % 2) := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm]

/-- The sum of a step. -/
theorem step_sum {A B i M : Nat} :
    (A * (B % 2 ^ i) % M + (if B / 2 ^ i % 2 = 0 then 0 else A * 2 ^ i % M)) % M =
      A * (B % 2 ^ (i + 1)) % M := by
  rw [mod_pow_succ_bit, Nat.mul_add]
  rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ i) with e | e
  · simp [e]
  · simp only [e, show (1 : Nat) ≠ 0 by decide, ↓reduceIte, Nat.mul_one]
    exact (Nat.add_mod _ _ _).symm

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem mulStep_eq : mulStep aMo aMa aMb aMm aMn aZero sOdd =
    .seq (.block (bitOf sOdd aMb)) (.seq (sel aMm aZero aMa sOdd) (.seq (addTo aMo aMm aMn aZero)
      (.seq (addTo aMa aMa aMn aZero) (.seq (.block [.li .r9 0])
        (.seq (half aMb) (.block [.subi .r11 .r11 1])))))) := rfl

/-- One step. -/
theorem mulStep_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {A Bm i : Nat}
    (hO : V aMo = A * (Bm % 2 ^ i) % 2 ^ (32 * w)) (hA : V aMa = A * 2 ^ i % 2 ^ (32 * w))
    (hB : V aMb = Bm / 2 ^ i) (hZ : V aZero = 0) :
    WP isa (mulStep aMo aMa aMb aMm aMn aZero sOdd) s fun t => Ws t B Z w nArr ∧
      (∃ V', KS t.mem B w V' F ∧ (∀ j < nArr, j ∉ mulArrs → V' j = V j) ∧
        V' aMo = A * (Bm % 2 ^ (i + 1)) % 2 ^ (32 * w) ∧ V' aMa = A * 2 ^ (i + 1) % 2 ^ (32 * w) ∧
        V' aMb = Bm / 2 ^ (i + 1)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t ∧ t.gpr .r11 = s.gpr .r11 - BitVec.ofNat 64 1 := by
  rw [mulStep_eq]
  -- The bit of `[aMb]` into `sOdd`.
  rw [WP.seq_iff, ← List.append_nil (bitOf sOdd aMb)]
  refine bitOf_ok h (by decide) nArr_le (by decide) fun t1 h1 k1 v1 r1 => WP.block_nil ?_
  have ks1 : KS t1.mem B w V F := ks.shared (k1.mono (by simp) (by simp)) (fit_of h)
  have bit1 : slot t1.mem B sOdd = Bm / 2 ^ i % 2 := by rw [v1, ks.arrs aMb (by decide), hB]
  -- `[aMm] := bit ? [aMa] : 0`.
  rw [WP.seq_iff]
  refine WP.mono (sel_ok h1 (o := aMm) (a := aZero) (b := aMa) (sl := sOdd) (by decide) (by decide) (by decide)
    nArr_le (by decide) (by decide) (by decide) (by rw [bit1]; omega_arith)) fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  have ks2 : KS t2.mem B w (upd V aMm (if Bm / 2 ^ i % 2 = 0 then 0 else A * 2 ^ i % 2 ^ (32 * w))) F := by
    refine ks1.step k2 (fit_of h1) (fun j hj hn => ?_) (fun j hj => ?_) (fun _ _ _ => rfl)
      (fun d hd => by simp at hd) (fun hd => absurd hd (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; rw [upd_ne hn]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rw [hj, upd_self, v2, bit1, ks1.arrs aZero (by decide), ks1.arrs aMa (by decide), hZ, hA]
  -- `[aMo] += [aMm]`.
  rw [WP.seq_iff]
  refine WP.mono (addToE h2 ks2 (o := aMo) (a := aMm) (n := aMn) (z := aZero) (z0 := by rw [upd_ne (by decide), hZ]))
    fun t3 ⟨h3, ks3, f3, r3⟩ => ?_
  -- `[aMa] += [aMa]`.
  rw [WP.seq_iff]
  refine WP.mono (addToE h3 ks3 (o := aMa) (a := aMa) (n := aMn) (z := aZero)
    (z0 := by simp only [upd, show aZero ≠ aMo by decide, show aZero ≠ aMn by decide,
      show aZero ≠ aMm by decide, ↓reduceIte, hZ])) fun t4 ⟨h4, ks4, f4, r4⟩ => ?_
  -- `r9 := 0` and the halving.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r9] (s := t4) (Q := fun u => u.gpr .r9 = 0 ∧ u.mem = t4.mem) (by prun; rfl) (by decide))
    fun t5 ⟨⟨z5, m5⟩, r5⟩ => ?_
  have h5 : Ws t5 B Z w nArr := h4.of_keep r5
  have ks5 : KS t5.mem B w _ F := m5 ▸ ks4
  rw [WP.seq_iff]
  refine WP.mono (halfE h5 ks5 (j := aMb) (c := 0) (h9 := by rw [z5]; rfl) (hc := by decide))
    fun t6 ⟨h6, ks6, f6, r6⟩ => ?_
  refine WP.mono (WP.keep [.r11] (s := t6) (Q := fun u => u.gpr .r11 = t6.gpr .r11 - BitVec.ofNat 64 1 ∧
    u.mem = t6.mem) (by prun) (by decide)) fun t ⟨⟨c7, m7⟩, r7⟩ => ?_
  have K6 : Keep opsRegs s t6 := ((((r1.mono.trans' r2.mono).trans' r3).trans' r4).trans' r5.mono).trans' r6
  have K : Keep bodyRegs s t := K6.mono.trans' r7.mono
  refine ⟨h6.of_keep r7, ⟨_, m7 ▸ ks6, fun j hj hn => ?_, ?_, ?_, ?_⟩,
    ((((KK.of (k1.mono (by simp) (by simp) : KeyWorkspace.Keep B w [] [sOdd] s.mem t1.mem) (by simp)
      (by decide)).trans (KK.of k2 (by decide) (by simp))).trans f3).trans f4).trans
      (by rw [← m5]; exact f6) |>.trans (by rw [m7]; exact KK.refl _ _ _), K, ?_⟩
  · simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5⟩ := hn
    simp only [upd, n1, n2, n3, n4, n5, ↓reduceIte]
  · simp only [upd, show aMo ≠ aMb by decide, show aMo ≠ aMa by decide, show aMo ≠ aMn by decide,
      ↓reduceIte, show aMo ≠ aMm by decide, hO]
    exact step_sum
  · simp only [upd, show aMa ≠ aMb by decide, show aMa ≠ aMn by decide, show aMa ≠ aMo by decide,
      show aMa ≠ aMm by decide, ↓reduceIte, hA, Nat.pow_succ]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.mul_two, Nat.mul_assoc]
  · simp only [upd, ↓reduceIte, show aMb ≠ aMa by decide, show aMb ≠ aMn by decide,
      show aMb ≠ aMo by decide, show aMb ≠ aMm by decide, hB, Nat.mul_zero, Nat.add_zero, Nat.pow_succ,
      Nat.div_div_eq_div_mul]
  · rw [c7, K6.gpr _ (by decide)]

/-- The loop's invariant after `i` steps, from `s0` with the values `V`. -/
def MulI (s0 : State) (B : Addr) (Z w : Nat) (V F : Nat → Nat) (A Bm i : Nat) (t : State) : Prop :=
  Ws t B Z w nArr ∧ (∃ V', KS t.mem B w V' F ∧ (∀ j < nArr, j ∉ mulArrs → V' j = V j) ∧
    V' aMo = A * (Bm % 2 ^ i) % 2 ^ (32 * w) ∧ V' aMa = A * 2 ^ i % 2 ^ (32 * w) ∧ V' aMb = Bm / 2 ^ i) ∧
  KK B w s0.mem t.mem ∧ Keep bodyRegs s0 t

/-- `K` steps. -/
theorem mulLoop_ok {K : Nat} (hK : 0 < K) (hK' : K < 2 ^ 64) {A Bm : Nat} (hZ : V aZero = 0)
    (h0 : MulI s B Z w V F A Bm 0 s) (hc : s.gpr .r11 = BitVec.ofNat 64 K) :
    WP isa (mulLoop aMo aMa aMb aMm aMn aZero sOdd) s (MulI s B Z w V F A Bm K) := by
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (N := K) hK' hK _ (fun i _ t ⟨ht, ⟨V', kt, fr, vo, va, vb⟩,
    kk, kr⟩ _ => ?_) h0 hc
  refine WP.mono (mulStep_ok ht kt vo va vb (by rw [fr aZero (by decide) (by decide), hZ]))
    fun u ⟨hu, ⟨V'', ku, fr', vo', va', vb'⟩, kk', kr', c⟩ => ⟨⟨hu, ⟨V'', ku, fun j hj hn => ?_, vo', va', vb'⟩,
      kk.trans kk', kr.trans' kr'⟩, c⟩
  rw [fr' j hj hn, fr j hj hn]

theorem mulTo_eq (o a b : Nat) (k : List Instr) : mulTo o a b k =
    .seq (copy aMa a) (.seq (copy aMb b) (.seq (copy aMo aZero) (.seq (.block k)
      (.seq (mulLoop aMo aMa aMb aMm aMn aZero sOdd) (copy o aMo))))) := rfl

/-- `mulTo o a b k`, `k` setting `r11` to `K`. -/
theorem mulToE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {o a b K : Nat} {k : List Instr}
    (ho : o < nArr := by decide) (ha : a < nArr := by decide) (hb : b < nArr := by decide)
    (hom : o ∉ mulArrs := by decide) (ham : a ≠ aMa := by decide)
    (hbm : b ≠ aMb := by decide) (hba : b ≠ aMa := by decide) (hK : 0 < K) (hK' : K < 2 ^ 64)
    (hk : ∀ u : State, u.gpr .r22 = s.gpr .r22 →
      WP isa (.block k) u fun u' => (u'.gpr .r11 = BitVec.ofNat 64 K ∧ u'.mem = u.mem) ∧ Keep [.r11] u u')
    (hZ : V aZero = 0) :
    WP isa (mulTo o a b k) s fun t => Ws t B Z w nArr ∧
      (∃ V', KS t.mem B w V' F ∧ (∀ j < nArr, j ≠ o → j ∉ mulArrs → V' j = V j) ∧
        V' o = V a * (V b % 2 ^ K) % 2 ^ (32 * w)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [mulTo_eq]
  refine WP.seq (WP.mono (copyE h ks (o := aMa) (a := a) (by decide) ha (Ne.symm ham))
    fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (copyE h1 k1 (o := aMb) (a := b) (by decide) hb (Ne.symm hbm))
    fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (copyE h2 k2 (o := aMo) (a := aZero)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  have e22 : t3.gpr .r22 = s.gpr .r22 := ((r1.trans' r2).trans' r3).gpr _ (by decide)
  refine WP.seq (WP.mono (hk t3 e22) fun t4 ⟨⟨c4, m4⟩, r4⟩ => ?_)
  have h4 : Ws t4 B Z w nArr := h3.of_keep r4
  let V3 := upd (upd (upd V aMa (V a)) aMb (upd V aMa (V a) b)) aMo (upd (upd V aMa (V a)) aMb
    (upd V aMa (V a) b) aZero)
  have k4 : KS t4.mem B w V3 F := m4 ▸ k3
  have vA : V3 aMa = V a := by simp [V3, upd, aMa, aMb, aMo]
  have hZ' : V 10 = 0 := hZ
  have vB : V3 aMb = V b := by simp [V3, upd, aMb, aMo, hba]
  have vO : V3 aMo = 0 := by simp [V3, upd, aMo, aMa, aMb, aZero, hZ']
  have hZ3 : V3 aZero = 0 := by simp [V3, upd, aMo, aMa, aMb, aZero, hZ']
  have fr3 : ∀ j < nArr, j ∉ mulArrs → V3 j = V j := by
    intro j _ hn
    simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, -, -⟩ := hn
    simp [V3, upd, n1, n2, n3]
  have i0 : MulI t4 B Z w V3 F (V a) (V b) 0 t4 := ⟨h4, ⟨V3, k4, fun _ _ _ => rfl, (by rw [vO, Nat.pow_zero, Nat.mod_one, Nat.mul_zero, Nat.zero_mod]),
    (by rw [vA, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (ks.lt ha)]),
    (by rw [vB, Nat.pow_zero, Nat.div_one])⟩, KK.refl _ _ _, Keep.refl _ _⟩
  refine WP.seq (WP.mono (mulLoop_ok hK hK' hZ3 i0 c4) fun t5 ⟨h5, ⟨V5, k5, fr5, vo5, _, _⟩, f5, r5⟩ => ?_)
  refine WP.mono (copyE h5 k5 (o := o) (a := aMo) ho (by decide) (fun e => hom (by rw [e]; decide)))
    fun t ⟨ht, kt, ft, rt⟩ => ⟨ht, ⟨_, kt, fun j hj hjo hn => ?_, (by rw [upd_self, vo5])⟩, ?_, ?_⟩
  · rw [upd_ne hjo, fr5 j hj hn, fr3 j hj hn]
  · exact (((f1.trans f2).trans f3).trans (by rw [← m4]; exact KK.refl _ _ _)).trans (f5.trans ft)
  · exact (((r1.mono.trans' r2.mono).trans' r3.mono).trans' r4.mono).trans' (r5.trans' rt.mono)

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
