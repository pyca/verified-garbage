module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Mul
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.HalveBounds
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3

/-!
# `vg_rsa_keygen_key` on PPC64LE: `lcm(p - 1, q - 1)`

`halving_ok`: the product `φ` and `8 p_len` steps of the halving
(`KeyMath.halveIter`); `gcdUV_ok`: the gcd of the halving's `u` and `v`;
`lcmPart_ok`: `[aL] = lcm(p - 1, q - 1)` (`KeyMath.lcm_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Proof.RsaKeyGen (halveStep halveIter halveIter_succ')
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 sel half aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aT aS aOne aTwo aThree aPm aQm aU aV aF aU2 aV2 aG aL aDr aDt
  X0 X1 X2 ltS notS andNotS halfSel halfStep halving gcdUV lcmPart divBy invOf mulTo cnt8)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.PPC64LE (InvLaw)

theorem shl3_ofNat {L : Nat} (_h : 8 * L < 2 ^ 64) : BitVec.ofNat 64 L <<< 3 = BitVec.ofNat 64 (8 * L) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

/-- `cnt8`: `r11 := 8 p_len`. -/
theorem cnt8_ok {L : Nat} (hL : 8 * L < 2 ^ 64) (u : State) (h22 : u.gpr .r22 = BitVec.ofNat 64 L) :
    WP isa (.block cnt8) u fun u' => (u'.gpr .r11 = BitVec.ofNat 64 (8 * L) ∧ u'.mem = u.mem) ∧
      Keep [.r11] u u' := by
  refine WP.keep _ ?_ (by decide)
  prun [cnt8, h22, shl3_ofNat hL]

/-- `halfSel j`: `[j]` halved under `X2`. -/
theorem halfSelE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {j : Nat} (hj : j < nArr := by decide)
    (hjT : j ≠ aT := by decide) (hjdv : j ≠ aDv := by decide) (bit : F X2 ≤ 1) :
    WP isa (seqs (halfSel j)) s fun t => Ws t B Z w nArr ∧
      (∃ V', KS t.mem B w V' F ∧ (∀ i, i ≠ aT → i ≠ j → V' i = V i) ∧
        V' j = (if F X2 = 0 then V j else V j / 2)) ∧ KK B w s.mem t.mem ∧ Keep opsRegs s t := by
  change WP isa (.seq (copy aT j) (.seq (.block [.li .r9 0]) (.seq (half aT) (sel j j aT X2)))) s _
  refine WP.seq (WP.mono (copyE h ks (o := aT) (a := j) (by decide) hj (Ne.symm hjT)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  refine WP.seq (WP.mono (WP.keep [.r9] (s := t1) (Q := fun u => u.gpr .r9 = 0 ∧ u.mem = t1.mem)
    (by prun; rfl) (by decide)) fun t2 ⟨⟨z2, m2⟩, r2⟩ => ?_)
  have h2 : Ws t2 B Z w nArr := h1.of_keep r2
  have k2 : KS t2.mem B w V1 F := m2 ▸ k1
  refine WP.seq (WP.mono (halfE h2 k2 (j := aT) (c := 0) (h9 := by rw [z2]; rfl) (hc := by decide))
    fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  refine WP.mono (selSelfE h3 k3 (o := j) (b := aT) hj (by decide) hjT hjdv (by decide) bit)
    fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V4, kt, e4, o4⟩ := kt.vx
  refine ⟨ht, ⟨V4, kt, fun i hi hij => ?_, ?_⟩, (f1.trans (by rw [← m2]; exact KK.refl _ _ _)).trans (f3.trans ft),
    ((r1.trans' r2.mono).trans' r3).trans' rt⟩
  · rw [o4 i hij, o3 i hi, o1 i hi]
  · rw [e4, o3 j hjT, o1 j hjT, e3, e1]
    simp

theorem halfStep_eq : halfStep = seqs (([.block (VG.Impl.Rsa.PPC64LE.Keys.bitOf X0 aU ++
    (VG.Impl.Rsa.PPC64LE.Keys.bitOf X1 aV ++ (notS X1 X1 ++ andNotS X2 X0 X1)))] : List (Prog isa)) ++
    (halfSel aU ++ (halfSel aV ++ (halfSel aF ++ ([.block [.subi .r11 .r11 1]] : List (Prog isa)))))) := by
  simp only [halfStep, List.append_assoc]

/-- The arrays and flags the halving writes. -/
abbrev halveArrs : List Nat := [aT, aU, aV, aF]

/-- One step of the halving. -/
theorem halfStep_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) :
    WP isa halfStep s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ∉ halveArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧
        (V' aU, V' aV, V' aF) = halveStep (V aU, V aV, V aF)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t ∧ t.gpr .r11 = s.gpr .r11 - BitVec.ofNat 64 1 := by
  rw [halfStep_eq, wp_seqs_append (by simp) (by simp [halfSel])]
  change WP isa (.block _) s _
  refine bitOfE h ks (d := X0) (j := aU) (k := fun t1 h1 k1 f1 r1 => ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  refine bitOfE h1 k1 (d := X1) (j := aV) (k := fun t2 h2 k2 f2 r2 => ?_)
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  refine notSE h2 k2 (d := X1) (a := X1) (ba := by rw [g2]; omega_arith) (k := fun t3 h3 k3 f3 r3 => ?_)
  obtain ⟨F3, k3, g3, p3⟩ := k3.fx
  rw [← List.append_nil (andNotS X2 X0 X1)]
  refine andNotSE h3 k3 (d := X2) (a := X0) (b := X1) (ba := by rw [p3 X0 (by decide), p2 X0 (by decide), g1]; omega_arith)
    (bb := by rw [g3]; omega_arith) (k := fun t4 h4 k4 f4 r4 => WP.block_nil ?_)
  obtain ⟨F4, k4, g4, p4⟩ := k4.fx
  have b4 : F4 X2 ≤ 1 := by rw [g4]; exact flag01 _
  -- `X2`: both even.
  have hX2 : F4 X2 = if V aU % 2 = 0 ∧ V aV % 2 = 0 then 1 else 0 := by
    rw [g4, p3 X0 (by decide), p2 X0 (by decide), g1, g3, g2]
    have := Nat.mod_two_eq_zero_or_one (V aU)
    have := Nat.mod_two_eq_zero_or_one (V aV)
    by_cases a : V aU % 2 = 0 <;> by_cases b : V aV % 2 = 0 <;> simp [a, b] <;> omega_arith
  rw [wp_seqs_append (by simp [halfSel]) (by simp [halfSel])]
  refine WP.mono (halfSelE h4 k4 (j := aU) (bit := b4)) fun t5 ⟨h5, ⟨V5, k5, o5, e5⟩, f5, r5⟩ => ?_
  rw [wp_seqs_append (by simp [halfSel]) (by simp [halfSel])]
  refine WP.mono (halfSelE h5 k5 (j := aV) (bit := b4)) fun t6 ⟨h6, ⟨V6, k6, o6, e6⟩, f6, r6⟩ => ?_
  rw [wp_seqs_append (by simp [halfSel]) (by simp)]
  refine WP.mono (halfSelE h6 k6 (j := aF) (bit := b4)) fun t7 ⟨h7, ⟨V7, k7, o7, e7⟩, f7, r7⟩ => ?_
  change WP isa (.block [.subi .r11 .r11 1]) t7 _
  refine WP.mono (WP.keep [.r11] (s := t7) (Q := fun u => u.gpr .r11 = t7.gpr .r11 - BitVec.ofNat 64 1 ∧
    u.mem = t7.mem) (by prun) (by decide)) fun t ⟨⟨c8, m8⟩, r8⟩ => ?_
  have K7 : Keep opsRegs s t7 := ((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).trans' r7)
  refine ⟨h7.of_keep r8, ⟨V7, F4, m8 ▸ k7, fun j hj => ?_, fun d d0 d1 d2 => ?_, ?_⟩,
    ((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7)).trans
      (by rw [m8]; exact KK.refl _ _ _)), K7.mono.trans' r8.mono, by rw [c8, K7.gpr _ (by decide)]⟩
  · simp only [halveArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨n1, n2, n3, n4⟩ := hj
    rw [o7 j n1 n4, o6 j n1 n3, o5 j n1 n2]
  · rw [p4 d d2, p3 d d1, p2 d d1, p1 d d0]
  · vsimp [e7, e6, e5, o7, o6, o5]
    rw [hX2, halveStep]
    by_cases c : V aU % 2 = 0 ∧ V aV % 2 = 0
    · simp only [c, and_self, ↓reduceIte, Nat.one_ne_zero]
    · simp only [c, ↓reduceIte]

/-- The halving's invariant after `i` steps, from `s0` with the values `V`, `F`. -/
def HalveI (s0 : State) (B : Addr) (Z w : Nat) (V F : Nat → Nat) (st : Nat × Nat × Nat) (i : Nat)
    (t : State) : Prop :=
  Ws t B Z w nArr ∧ (∃ V' F', KS t.mem B w V' F' ∧ (∀ j, j ∉ halveArrs → V' j = V j) ∧
    (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧ (V' aU, V' aV, V' aF) = halveIter i st) ∧
  KK B w s0.mem t.mem ∧ Keep bodyRegs s0 t

/-- The halving's loop. -/
theorem halveLoop_ok {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64) {st : Nat × Nat × Nat}
    (h0 : HalveI s B Z w V F st 0 s) (hc : s.gpr .r11 = BitVec.ofNat 64 N) :
    WP isa (.loop halfStep (.nonzero .d .r11)) s (HalveI s B Z w V F st N) := by
  refine VG.Proof.Bignum.PPC64LE.wp_countdown (N := N) hN' hN _ (fun i _ t ⟨ht, ⟨V', F', kt, fr, ff, v⟩,
    kk, kr⟩ _ => ?_) h0 hc
  refine WP.mono (halfStep_ok ht kt) fun u ⟨hu, ⟨V'', F'', ku, fr', ff', v'⟩, kk', kr', c⟩ =>
    ⟨⟨hu, ⟨V'', F'', ku, fun j hj => by rw [fr' j hj, fr j hj], fun d a b c => by rw [ff' d a b c, ff d a b c],
      by rw [v', v, halveIter_succ']⟩, kk.trans kk', kr.trans' kr'⟩, c⟩

/-- The arrays the halving writes. -/
abbrev halvingArrs : List Nat := [aT, aU, aV, aF, VG.Impl.RsaKeyGen.PPC64LE.Key.aMo,
  VG.Impl.RsaKeyGen.PPC64LE.Key.aMa, VG.Impl.RsaKeyGen.PPC64LE.Key.aMb, VG.Impl.RsaKeyGen.PPC64LE.Key.aMm,
  VG.Impl.RsaKeyGen.PPC64LE.Key.aMn]

theorem halving_eq : halving = .seq (mulTo aF aPm aQm cnt8) (.seq (copy aU aPm) (.seq (copy aV aQm)
    (.seq (.block cnt8) (.loop halfStep (.nonzero .d .r11))))) := rfl

/-- `φ`, and `8 p_len` steps of the halving. -/
theorem halving_ok (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {L : Nat}
    (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL : 0 < L) (hL' : 8 * L < 2 ^ 64) (zero : V aZero = 0) :
    WP isa halving s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ halvingArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧
        (V' aU, V' aV, V' aF) = halveIter (8 * L)
          (V aPm, V aQm, V aPm * (V aQm % 2 ^ (8 * L)) % 2 ^ (32 * w))) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [halving_eq]
  refine WP.seq (WP.mono (mulToE h ks (o := aF) (a := aPm) (b := aQm) (K := 8 * L) (hK := by omega_arith) (hK' := hL')
    (hk := fun u hu => cnt8_ok hL' u (hu.trans h22)) (hZ := zero)) fun t1 ⟨h1, ⟨V1, k1, o1, e1⟩, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (copyE h1 k1 (o := aU) (a := aPm)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  refine WP.seq (WP.mono (copyE h2 k2 (o := aV) (a := aQm)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  have e22 : t3.gpr .r22 = BitVec.ofNat 64 L := by
    rw [(r1.trans' (r2.mono.trans' r3.mono)).gpr _ (by decide), h22]
  refine WP.seq (WP.mono (cnt8_ok hL' t3 e22) fun t4 ⟨⟨c4, m4⟩, r4⟩ => ?_)
  have h4 : Ws t4 B Z w nArr := h3.of_keep r4
  have k4 : KS t4.mem B w V3 F := m4 ▸ k3
  have i0 : HalveI t4 B Z w V3 F (V3 aU, V3 aV, V3 aF) 0 t4 :=
    ⟨h4, ⟨V3, F, k4, fun _ _ => rfl, fun _ _ _ _ => rfl, rfl⟩, KK.refl _ _ _, Keep.refl _ _⟩
  refine WP.mono (halveLoop_ok (by omega_arith) hL' i0 c4) fun t ⟨ht, ⟨V', F', kt, fr, ff, v⟩, kk, kr⟩ => ⟨ht,
    ⟨V', F', kt, fun j hjn hj => ?_, ff, ?_⟩, ((f1.trans f2).trans f3).trans ((show KK B w t3.mem t4.mem by rw [m4]; exact KK.refl _ _ _).trans kk),
    (((r1.trans' r2.mono).trans' r3.mono).trans' r4.mono).trans' kr⟩
  · simp only [halvingArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := hj
    have a1 : j ∉ halveArrs := by
      simp only [halveArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n1, n2, n3, n4⟩
    have a2 : j ∉ mulArrs := by
      simp only [mulArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨n5, n6, n7, n8, n9⟩
    rw [fr j a1, o3 j n3, o2 j n2, o1 j hjn n4 a2]
  · rw [v]
    vsimp [e3, o3, e2, o2, e1, o1]

/-- The arrays `gcdUV` writes. -/
abbrev gcdArrs : List Nat := [aU2, aV2, aT, aS, aG] ++ invOfArrs

theorem gcdUV_eq : gcdUV = seqs (([.block (VG.Impl.Rsa.PPC64LE.Keys.bitOf X0 aV ++ notS X0 X0),
    sel aU2 aU aV X0, sel aV2 aV aU X0] : List (Prog isa)) ++ (ltS X1 aV2 aTwo ++ ([sel aS aV2 aThree X1, invOf aU2 aS VG.Impl.RsaKeyGen.PPC64LE.Key.nP,
      sel aG 1 aOne X1] : List (Prog isa)))) := rfl

/-- `gcdUV`: `v` odd by a swap (if it is even), and `[aG] := gcd(u, v)`, 1 for `v < 2`. -/
theorem gcdUV_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (one : V aOne = 1) (two : V aTwo = 2)
    (three : V aThree = 3) (hw10 : 10 ≤ w) {L : Nat} (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL' : 8 * L < 2 ^ 64)
    (hL4 : L % 4 = 0) (hL1 : 4 ≤ L) (hLw : L ≤ 4 * w) (hu : V aU < 2 ^ (8 * L)) (hv : V aV < 2 ^ (8 * L))
    (hodd : 2 ≤ (if V aV % 2 = 0 then V aU else V aV) → (if V aV % 2 = 0 then V aU else V aV) % 2 = 1) :
    WP isa gcdUV s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ gcdArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → F' d = F d) ∧
        V' aG = (if (if V aV % 2 = 0 then V aU else V aV) < 2 then 1 else
          Nat.gcd (if V aV % 2 = 0 then V aV else V aU) (if V aV % 2 = 0 then V aU else V aV))) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [gcdUV_eq, wp_seqs_append (by simp) (by simp [ltS])]
  change WP isa (.seq (.block _) (.seq (sel aU2 aU aV X0) (sel aV2 aV aU X0))) s _
  rw [WP.seq_iff]
  refine bitOfE h ks (d := X0) (j := aV) (k := fun t1 h1 k1 f1 r1 => ?_)
  obtain ⟨F1, k1, g1, p1⟩ := k1.fx
  rw [← List.append_nil (notS X0 X0)]
  refine notSE h1 k1 (d := X0) (a := X0) (ba := by rw [g1]; omega_arith) (k := fun t2 h2 k2 f2 r2 => WP.block_nil ?_)
  obtain ⟨F2, k2, g2, p2⟩ := k2.fx
  have b2 : F2 X0 ≤ 1 := by rw [g2]; omega_arith
  refine WP.seq (WP.mono (selE h2 k2 (o := aU2) (a := aU) (b := aV) (sl := X0) (bit := b2))
    fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  refine WP.mono (selE h3 k3 (o := aV2) (a := aV) (b := aU) (sl := X0) (bit := b2)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  rw [wp_seqs_append (by simp [ltS]) (by simp)]
  refine WP.mono (ltSE h4 k4 (d := X1) (a := aV2) (b := aTwo)) fun t5 ⟨h5, k5, f5, r5⟩ => ?_
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  obtain ⟨F5, k5, g5, p5⟩ := k5.fx
  have b5 : F5 X1 ≤ 1 := by rw [g5]; exact flag01 _
  change WP isa (.seq (sel aS aV2 aThree X1) (.seq (invOf aU2 aS VG.Impl.RsaKeyGen.PPC64LE.Key.nP) (sel aG 1 aOne X1))) t5 _
  refine WP.seq (WP.mono (selE h5 k5 (o := aS) (a := aV2) (b := aThree) (sl := X1) (bit := b5))
    fun t6 ⟨h6, k6, f6, r6⟩ => ?_)
  obtain ⟨V6, k6, e6, o6⟩ := k6.vx
  -- The values.
  have hv : V aV % 2 = 0 ∨ V aV % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  have vU2 : V6 aU2 = if V aV % 2 = 0 then V aV else V aU := by
    vsimp [o6, o5, o4, e3, g2, g1]
    rcases hv with e | e <;> simp [e]
  have vV2 : V5 aV2 = if V aV % 2 = 0 then V aU else V aV := by
    vsimp [o5, e4, o3, g2, g1]
    rcases hv with e | e <;> simp [e]
  have vS : V6 aS = if (if V aV % 2 = 0 then V aU else V aV) < 2 then 3 else
      (if V aV % 2 = 0 then V aU else V aV) := by
    vsimp [e6, g5, o5, e4, o4, o3, e3, g2, g1, two, three, sel_flag]
    rcases hv with e | e <;> simp [e]
  have sO : V6 aS % 2 = 1 ∧ 1 < V6 aS := by
    by_cases hl : (if V aV % 2 = 0 then V aU else V aV) < 2
    · rw [vS]; simp only [hl, ↓reduceIte]; decide
    · rw [vS]; simp only [hl, ↓reduceIte]; exact ⟨hodd (by omega_arith), by omega_arith⟩
  have e32 : 32 * (L / 4) = 8 * L := by omega_arith
  have K6 : Keep opsRegs s t6 := ((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6
  have hw6 := nP_width (s := t6) (by rw [K6.gpr .r22 (by decide)]; exact h22) (by omega_arith)
  have bU2 : V6 aU2 < 2 ^ (32 * (L / 4)) := by
    rw [vU2, e32]; split <;> with_reducible assumption
  have bS : V6 aS < 2 ^ (32 * (L / 4)) := by
    rw [vS, e32]
    by_cases hl : (if V aV % 2 = 0 then V aU else V aV) < 2
    · simp only [hl, ↓reduceIte]
      exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega_arith : 2 ≤ 8 * L))
    · simp only [hl, ↓reduceIte]; split <;> with_reducible assumption
  refine WP.seq (WP.mono (invOfE h6 k6 hw10 (a := aU2) (m := aS) (hk := hw6) (hn1 := by omega_arith)
    (hnw := by omega_arith) (han := bU2) (hmn := bS) (odd := sO.1) (gt := sO.2)) fun t7 ⟨h7, ⟨V7, k7, fr7, g7, _, _⟩, f7, r7⟩ => ?_)
  refine WP.mono (selE h7 k7 (o := aG) (a := 1) (b := aOne) (sl := X1) (bit := b5)) fun t ⟨ht, kt, ft, rt⟩ => ?_
  obtain ⟨V8, kt, e8, o8⟩ := kt.vx
  refine ⟨ht, ⟨V8, F5, kt, fun j hj hn => ?_, fun d d0 d1 => ?_, ?_⟩,
    (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans (f7.trans ft),
    (((((((r1.trans' r2).trans' r3).trans' r4).trans' r5).trans' r6).mono.trans' (r7.trans' rt.mono)))⟩
  · simp only [gcdArrs, invOfArrs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19⟩ := hn
    have hi : j ∉ invOfArrs := by
      simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19⟩
    rw [o8 j n5, fr7 j hj hi, o6 j n4, o5 j n3, o4 j n2, o3 j n1]
  · rw [p5 d d1, p2 d d0, p1 d d0]
  · have v1 : V7 aOne = 1 := by
      rw [fr7 aOne (by decide) (by decide)]; vsimp [o6, o5, o4, o3, one]
    have vv : V4 aV2 = if V aV % 2 = 0 then V aU else V aV := by rw [← o5 aV2 (by decide)]; exact vV2
    have vt : V4 aTwo = 2 := by vsimp [o4, o3, two]
    rw [e8, g5, sel_flag, v1, g7, vU2, vS, vv, vt]
    by_cases hl : (if V aV % 2 = 0 then V aU else V aV) < 2 <;> simp only [hl, ↓reduceIte]

/-- The arrays `lcmPart` writes. -/
abbrev lcmArrs : List Nat := halvingArrs ++ gcdArrs ++ [aL, aDv, aDr, aDt]

theorem lcmPart_eq : lcmPart = .seq halving (.seq gcdUV (.seq (copy aL aF) (.seq (copy aDv aG)
    (VG.Impl.Rsa.PPC64LE.Div.div aL aDr aDv aDt)))) := rfl

/-- `[aL] := lcm(p - 1, q - 1)`. -/
theorem lcmPart_ok [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {L : Nat}
    (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL : 0 < L) (hL' : 8 * L < 2 ^ 64) (hw : 32 * w = 16 * L)
    (hw10 : 10 ≤ w) (hL4 : L % 4 = 0)
    (hpm : V aPm < 2 ^ (8 * L)) (hqm : V aQm < 2 ^ (8 * L))
    (one : V aOne = 1) (two : V aTwo = 2) (three : V aThree = 3) (zero : V aZero = 0) :
    WP isa lcmPart s fun t => Ws t B Z w nArr ∧
      (∃ V' F', KS t.mem B w V' F' ∧ (∀ j < nArr, j ∉ lcmArrs → V' j = V j) ∧
        (∀ d, d ≠ X0 → d ≠ X1 → d ≠ X2 → F' d = F d) ∧ V' aL = Nat.lcm (V aPm) (V aQm)) ∧
      KK B w s.mem t.mem ∧ Keep bodyRegs s t := by
  rw [lcmPart_eq]
  have hst : V aPm * (V aQm % 2 ^ (8 * L)) % 2 ^ (32 * w) = V aPm * V aQm := by
    rw [Nat.mod_eq_of_lt hqm, Nat.mod_eq_of_lt]
    rw [hw, show 16 * L = 8 * L + 8 * L by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul'' hpm hqm
  have LE := VG.Proof.RsaKeyGen.lcm_eq hpm hqm
  refine WP.seq (WP.mono (halving_ok h ks h22 hL hL' zero) fun t1 ⟨h1, ⟨V1, F1, k1, o1, p1, e1⟩, f1, r1⟩ => ?_)
  rw [hst] at e1
  generalize hS : halveIter (8 * L) (V aPm, V aQm, V aPm * V aQm) = st at e1 LE
  obtain ⟨u, v, f⟩ := st
  simp only [Prod.mk.injEq] at e1
  obtain ⟨eu, ev, ef⟩ := e1
  dsimp only at LE
  have c1 : V1 aOne = 1 := by rw [o1 aOne (by decide) (by decide), one]
  have c2 : V1 aTwo = 2 := by rw [o1 aTwo (by decide) (by decide), two]
  have c3 : V1 aThree = 3 := by rw [o1 aThree (by decide) (by decide), three]
  have c0 : V1 aZero = 0 := by rw [o1 aZero (by decide) (by decide), zero]
  have hb := VG.Proof.RsaKeyGen.halveIter_bounds (8 * L) (st := (V aPm, V aQm, V aPm * V aQm))
    (a := 2 ^ (8 * L)) (b := 2 ^ (8 * L)) (f := V aPm * V aQm + 1) ⟨hpm, hqm, Nat.lt_succ_self _⟩
  rw [hS] at hb
  refine WP.seq (WP.mono (gcdUV_ok h1 k1 c1 c2 c3 hw10 (by rw [r1.gpr .r22 (by decide)]; exact h22) hL' hL4
    (by omega_arith) (by omega_arith) (by rw [eu]; exact hb.1) (by rw [ev]; exact hb.2.1) (by rw [eu, ev]; exact LE.1))
    fun t2 ⟨h2, ⟨V2, F2, k2, o2, p2, e2⟩, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (copyE h2 k2 (o := aL) (a := aF)) fun t3 ⟨h3, k3, f3, r3⟩ => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  refine WP.seq (WP.mono (copyE h3 k3 (o := aDv) (a := aG)) fun t4 ⟨h4, k4, f4, r4⟩ => ?_)
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  refine WP.mono (divE h4 k4 (q := aL) (r := aDr) (t := aDt)) fun t ⟨ht, ⟨V5, k5, o5, e5⟩, f5, r5⟩ => ?_
  have vG : V4 aDv = if (if v % 2 = 0 then u else v) < 2 then 1 else
      Nat.gcd (if v % 2 = 0 then v else u) (if v % 2 = 0 then u else v) := by
    rw [e4, o3 aG (by decide), e2, eu, ev]
  have hG : 0 < V4 aDv := by
    rw [vG]
    by_cases hv : (if v % 2 = 0 then u else v) < 2
    · simp only [hv, ↓reduceIte]; omega_arith
    · simp only [hv, ↓reduceIte]; exact Nat.gcd_pos_of_pos_right _ (by omega_arith)
  refine ⟨ht, ⟨V5, F2, k5, fun j hj hn => ?_, fun d a b c => by rw [p2 d a b, p1 d a b c], ?_⟩,
    (((f1.trans f2).trans f3).trans f4).trans f5, (((r1.trans' r2).trans' r3.mono).trans' r4.mono).trans' r5.mono⟩
  · simp only [lcmArrs, halvingArrs, gcdArrs, invOfArrs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, -, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21,
      n22, n23, n24, n25, n26, n27, n28, n29, n30, n31⟩ := hn
    rw [o5 j hj n28 n30 n31, o4 j n29, o3 j n28]
    have a2 : j ∉ gcdArrs := by
      simp only [gcdArrs, invOfArrs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      exact ⟨n10, n11, n1, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27⟩
    rw [o2 j hj a2]
    have a1 : j ∉ halvingArrs := by
      simp only [halvingArrs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩
    exact o1 j hj a1
  · rw [(e5 hG).1, o4 aL (by decide), e3, o2 aF (by decide) (by decide), ef, vG, LE.2]
    congr 1
    by_cases hv : (if v % 2 = 0 then u else v) < 2
    · simp only [hv, ↓reduceIte, show (if v % 2 = 0 then u else v) ≤ 1 by omega_arith]
    · simp only [hv, ↓reduceIte, show ¬ (if v % 2 = 0 then u else v) ≤ 1 by omega_arith]

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
