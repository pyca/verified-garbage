module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre

/-!
# RSASSA-PSS signing on PPC64LE: `M'` and `EM`

Untrusted: everything here is checked by Lean. The writes to our part of
`scratch`, each keeping `Base`: `M' = 0⁸ ‖ mHash ‖ salt` at `oY`
(`mPrime_ok`); `EM`'s `k` bytes cleared, `0x01` and the salt (`putSalt_ok`),
`H` and `0xbc` (`putH_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa copyLoop zeroLoop arg)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs fb sc_in sc_w rd_in ne_of_dis zero_ok copy_ok
  bytes_entry Base.wb)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_stb wp_addSp wp_nil
  eval_nonzero ne_zero_iff)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The digest and the salt, from the entry state. -/
abbrev digB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 8) D
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (Ss s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega) (by unfold oRsa at h; omega)

/-- Our stack argument `j` into `r`, through `r12`. -/
theorem ldArg_ok {t : State} (h : Base Ss vS s t) {r : Reg} {j : Nat} (hj : j < 13) {is : List Instr}
    {Q : State → Prop} (k : ∀ t', Only [.r12, r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : arg j < 2 ^ 15 ∧ arg j % 4 = 0 := by decide) :
    WP isa (.block (ldArg r j ++ is)) t Q := by
  show WP isa (.block (.addSp .r12 0 :: .load .d r .r12 (arg j) :: is)) t Q
  refine wp_addSp fun t₁ o₁ e₁ => ?_
  refine wp_arg P (r := r) hj (by rw [e₁, Base.sp h, BitVec.add_zero]) (by rw [o₁.rd, h.rd])
    (by rw [o₁.mem]; exact h.mem)
    (fun t' o e => k t' (o₁.trans o) e) ho

/-- The salt's pointer to `r4` and its length to `r6`. -/
theorem saltArgs_ok {t : State} (h : Base Ss vS s t) :
    WP isa (.block (ldArg .r4 9 ++ [mov .r6 .r19])) t fun t' =>
      Only [.r12, .r4, .r6] t t' ∧ t'.gpr .r4 = stackArg s 9 ∧ t'.gpr .r6 = stackArg s 10 :=
  ldArg_ok P h (r := .r4) (j := 9) (by decide) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ =>
    wp_nil ⟨(o₁.trans o₂).mono, by rw [o₂.get .r4, e₁], by rw [e₂, o₁.get .r19, Base.r19 h]⟩

/-- The salt to `S + d`, from its pointer and length. -/
theorem saltCopy_ok {t : State} (h : Base Ss vS s t) {d : Nat} (h4 : t.gpr .r4 = stackArg s 9)
    (h5 : t.gpr .r5 = off (Ss s) d) (h6 : t.gpr .r6 = stackArg s 10) (hd : d + (stackArg s 10).toNat ≤ oRsa) :
    WP isa (.ite (.nonzero .d .r6) copyLoop (.block [])) t fun t' => Base Ss vS s t' ∧
      (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧ t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by
  generalize hL : (stackArg s 10).toNat = sl at hd
  have F := fits P
  have g6 : t.gpr .r6 = BitVec.ofNat 64 sl := by
    rw [h6, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hb : Spec.Rsa.bytesAt t.mem (stackArg s 9) sl = saltB s := by
    rw [← hL]; exact bytes_entry h.mem (P.ksl.sub_left kR_sub) ((P.sls.symm).sub_left (sc_sub P))
      (by have := P.wsl; omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hs0 : sl ≠ 0 := by intro h0; rw [g6, ne_zero_iff, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 9) (p := off (Ss s) d) (n := sl) (by omega)
      (by omega) h4 h5 g6
      (rd_in (s := s) (t := t) h.rd (R := sR s) (by rw [P.hrd]; simp) P.wsl (by show sl ≤ (stackArg s 10).toNat; omega))
      (sc_w F h.wr (d := d) hd)
      (fun j hj i hi => ne_of_dis P.sls (Offset.contains_base _ (by omega) (by have := P.wsl; omega))
        (by have := scR_contains P (o := d + i) (n := 1) (by omega); rwa [← off_off] at this)))
      fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by rw [hm, hb]
    exact ⟨h.wb F hk' (d := d) (xs := saltB s) (by rw [bytesAt_length, hL]; omega) (by rw [hm, hb]),
      fun r hr => hk'.gpr r (by revert r; decide), hm'⟩
  · have hs0 : sl = 0 := by rw [g6, ne_zero_iff] at hc; simp at hc; unfold oRsa at hd; omega
    refine wp_nil ⟨h, fun r hr => rfl, ?_⟩
    rw [show saltB s = [] by simp [saltB, Spec.Rsa.bytesAt, hL, hs0], writeBytes_nil]

/-- `copySalt`: the salt to `S + d`, after `r5` is set to it. -/
theorem copySalt_ok {t : State} (h : Base Ss vS s t) {d : Nat} (h5 : t.gpr .r5 = off (Ss s) d)
    (hd : d + (stackArg s 10).toNat ≤ oRsa) :
    WP isa copySalt t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by
  refine WP.seq (WP.mono (saltArgs_ok P h) fun t₂ ⟨k₂, e4, e6⟩ => ?_)
  refine WP.mono (saltCopy_ok P (h.only (fits P) k₂) e4 (by rw [k₂.get .r5, h5]) e6 hd) fun t' ⟨b', g', m'⟩ =>
    ⟨b', fun r hr => by rw [g' r hr, k₂.gpr r (by revert r; decide)], by rw [m', k₂.mem]⟩

/-- `0⁸` at `S + oY`. -/
theorem zeros_ok {t : State} (h : Base Ss vS s t) :
    WP isa (.seq (.block [.addi .r4 .r14 oY, .li .r5 8, .li .r6 0]) zeroLoop) t fun t' => Base Ss vS s t' ∧
      (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0) := by
  have F := fits P
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide)
    fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (Ss s) oY) (n := 8) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (sc_w F (by rw [k₃.wr, h.wr]) (d := oY) (by decide))) fun t₄ ⟨k₄, m₄⟩ => ?_
  have K₄ : Keep [.r4, .r5, .r6] t t₄ := (k₃.keep.trans k₄).mono
  have m₄' : t₄.mem = writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0) := by rw [m₄, k₃.mem]
  exact ⟨h.wb F K₄ (by rw [List.length_replicate]; decide) m₄', fun r hr => K₄.gpr r (by revert r; decide), m₄'⟩

/-- The digest's pointer to `r4`, `S + oY + 8` to `r5` and `hLen` to `r6`. -/
theorem digArgs_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) :
    WP isa (.block (ldArg .r4 8 ++ ([.addi .r5 .r14 (oY + 8), .li .r6 H.D] : List Instr))) t fun t' =>
      Only [.r12, .r4, .r5, .r6] t t' ∧ t'.gpr .r4 = stackArg s 8 ∧ t'.gpr .r5 = off (Ss s) (oY + 8) ∧
      t'.gpr .r6 = BitVec.ofNat 64 D :=
  ldArg_ok P h (r := .r4) (j := 8) (by decide) fun t₅ o₅ e₅ => wp_addi fun t₆ o₆ e₆ =>
    wp_li (by omega) fun t₇ o₇ e₇ => wp_nil ⟨(o₅.trans (o₆.trans o₇)).mono, by rw [o₇.get .r4, o₆.get .r4, e₅],
      by rw [o₇.get .r5, e₆, o₅.get .r14, h.r14], by rw [e₇, hD]⟩

/-- The digest to `S + oY + 8`. -/
theorem digCopy_ok (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State} (h : Base Ss vS s t) (h4 : t.gpr .r4 = stackArg s 8)
    (h5 : t.gpr .r5 = off (Ss s) (oY + 8)) (h6 : t.gpr .r6 = BitVec.ofNat 64 D) :
    WP isa copyLoop t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (Ss s) (oY + 8)) (digB D s) := by
  have F := fits P
  have hY : oY = 2560 := rfl
  have hb : Spec.Rsa.bytesAt t.mem (stackArg s 8) D = digB D s :=
    bytes_entry h.mem (P.kdg.sub_left kR_sub) ((P.dgs.symm).sub_left (sc_sub P)) (by have := P.wdg; omega)
  refine WP.mono (copy_ok (q := stackArg s 8) (p := off (Ss s) (oY + 8)) (n := D) hD0 (by omega) h4 h5 h6
    (rd_in (s := s) (t := t) h.rd (R := dgR D s) (by rw [P.hrd]; simp) P.wdg (Nat.le_refl _))
    (sc_w F h.wr (d := oY + 8) (by unfold oRsa; omega))
    (fun j hj i hi => ne_of_dis P.dgs (Offset.contains_base _ (by omega) (by have := P.wdg; omega))
      (by have := scR_contains P (o := oY + 8 + i) (n := 1) (by unfold oRsa; omega); rwa [← off_off] at this)))
    fun t' ⟨k', m'⟩ => ⟨h.wb F k' (d := oY + 8) (xs := digB D s) (by rw [bytesAt_length]; unfold oRsa; omega)
      (by rw [m', hb]), fun r hr => k'.gpr r (by revert r; decide), by rw [m', hb]⟩

/-- `M' = 0⁸ ‖ mHash ‖ salt` at `S + oY`. -/
theorem mPrime_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hsl : (stackArg s 10).toNat + 8 + D ≤ 2048) :
    WP isa (mPrime H) t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes (writeBytes (writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0))
        (off (Ss s) (oY + 8)) (digB D s)) (off (Ss s) (oY + 8 + D)) (saltB s) := by
  have F := fits P
  have hY : oY = 2560 := rfl
  refine WP.seq (WP.mono (zeros_ok P h) fun t₄ ⟨b₄, g₄, m₄⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (digArgs_ok P hD hD64 b₄) fun t₇ ⟨k₇, e4, e5, e6⟩ =>
    WP.mono (digCopy_ok P hD0 hD64 (b₄.only F k₇) e4 e5 e6) fun t₈ ⟨b₈, g₈, m₈⟩ => ?_))
  refine WP.seq (wp_addi (h := by unfold oY; omega) fun t₉ o₉ e₉ => wp_nil ?_)
  refine WP.mono (copySalt_ok P (b₈.only F o₉) (d := oY + 8 + D) (by rw [e₉, b₈.r14, hD])
    (by unfold oRsa; omega)) fun t' ⟨b', g', m'⟩ => ⟨b', fun r hr => ?_, ?_⟩
  · rw [g' r hr, o₉.gpr r (by revert r; decide), g₈ r hr, k₇.gpr r (by revert r; decide), g₄ r hr]
  · rw [m', o₉.mem, m₈, k₇.mem, m₄]
/-- `clearEm`: `k` zeros at `S + oEm`. -/
theorem clearEm_ok {t : State} (h : Base Ss vS s t) :
    WP isa clearEm t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (Ss s) oEm) (List.replicate (kk s) 0) := by
  have F := fits P
  have hk1 : 64 ≤ kk s := P.k1; have hk2 : kk s ≤ 1024 := P.k2
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (Ss s) oEm) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂, o₁.get .r15, Base.r15 h]; simp)
    (by rw [e₃]; rfl) (sc_w F (by rw [k₃.wr, h.wr]) (d := oEm) (by unfold oEm oRsa; omega)))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (Ss s) oEm) (List.replicate (kk s) 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb F hK (by rw [List.length_replicate]; unfold oEm oRsa; omega) hm',
    fun r hr => hK.gpr r (by revert r; decide), hm'⟩

/-- `0x01` at `S + oEm + k - sLen - hLen - 2`, and `r5` after it. -/
theorem saltHead_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : (stackArg s 10).toNat + D + 2 ≤ kk s) :
    WP isa (.block [.addi .r4 .r14 oEm, .add .r4 .r4 .r15, .sub .r4 .r4 .r19, .subi .r4 .r4 (H.D + 2), .li .r5 1,
      .stb .r5 .r4 0, .addi .r5 .r4 1]) t fun t' => Base Ss vS s t' ∧
      (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem.writeW (off (Ss s) (oEm + (kk s - (stackArg s 10).toNat - D - 2))) (1 : Byte) ∧
      t'.gpr .r5 = off (Ss s) (oEm + (kk s - (stackArg s 10).toNat - D - 1)) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  generalize hK : kk s = k at hfit k2
  generalize hL : (stackArg s 10).toNat = sl at hfit
  have hE : oEm = 0 := rfl
  refine wp_addi fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_sub fun t₃ o₃ e₃ =>
    wp_subi (h := by omega) fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ => ?_
  have k₅ : Only [.r4, .r5] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have a₄ : t₄.gpr .r4 = off (Ss s) (oEm + (k - sl - D - 2)) := by
    rw [e₄, e₃, e₂, e₁, o₁.get .r15, o₂.get .r19, o₁.get .r19, h.r14, Base.r15 h, Base.r19 h, hD]
    apply BitVec.eq_of_toNat_eq
    have := VG.Proof.RsaOaep.PPC64LE.S_fits F
    have ek : (s.gpr .r6).toNat = k := hK
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek, hL] at this ⊢
    unfold oRsa at this; unfold oEm; omega
  have hA : InRegions t₅.wr (t₅.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [o₅.get .r4, a₄, BitVec.add_zero, k₅.wr, h.wr]; exact VG.Proof.RsaOaep.PPC64LE.sc_inW F (by unfold oEm oRsa; omega)
  refine wp_stb rfl hA fun t₆ m₆ => wp_addi fun t₇ o₇ e₇ => wp_nil ?_
  have hv : (t₅.gpr .r5).setWidth 8 = (1 : Byte) := by rw [e₅]; rfl
  have m₇ : t₇.mem = t.mem.writeW (off (Ss s) (oEm + (k - sl - D - 2))) (1 : Byte) := by
    rw [o₇.mem, m₆.mem, o₅.get .r4, a₄, BitVec.add_zero, hv, k₅.mem]
  have b₇ : Base Ss vS s t₇ := (h.only F k₅).keep F (m₆.keep.trans o₇.keep) (R := [⟨off (Ss s) (oEm + (k - sl - D - 2)), 1⟩])
    (by rw [m₇, ← k₅.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oEm oRsa; omega)))
  have a₇ : t₇.gpr .r5 = off (Ss s) (oEm + (k - sl - D - 1)) := by
    rw [e₇, m₆.gpr, o₅.get .r4, a₄]
    show off (off (Ss s) (oEm + (k - sl - D - 2))) 1 = _
    rw [off_off, show oEm + (k - sl - D - 2) + 1 = oEm + (k - sl - D - 1) by omega]
  exact ⟨b₇, fun r hr => by rw [o₇.gpr r (by revert r; decide), m₆.gpr, k₅.gpr r (by revert r; decide)], m₇, a₇⟩

/-- `putSalt`: `0x01` at `S + oEm + k - sLen - hLen - 2`, and the salt after
it. -/
theorem putSalt_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : (stackArg s 10).toNat + D + 2 ≤ kk s) :
    WP isa (putSalt H) t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes (t.mem.writeW (off (Ss s) (oEm + (kk s - (stackArg s 10).toNat - D - 2))) (1 : Byte))
        (off (Ss s) (oEm + (kk s - (stackArg s 10).toNat - D - 1))) (saltB s) := by
  have k2 : kk s ≤ 1024 := P.k2
  refine WP.seq (WP.mono (saltHead_ok P hD hD64 h hfit) fun t₇ ⟨b₇, g₇, m₇, a₇⟩ => ?_)
  refine WP.mono (copySalt_ok P b₇ a₇ (by unfold oEm oRsa; omega)) fun t' ⟨b', g', m'⟩ =>
    ⟨b', fun r hr => by rw [g' r hr, g₇ r hr], by rw [m', m₇]⟩

/-- `putH`: the `hLen` bytes at `S + oDig` to `S + oEm + k - hLen - 1`, and
`0xbc` at `S + oEm + k - 1`. -/
theorem putH_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : D + 2 ≤ kk s) :
    WP isa (putH H) t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = (writeBytes t.mem (off (Ss s) (oEm + (kk s - D - 1)))
        (Spec.Rsa.bytesAt t.mem (off (Ss s) oDig) D)).writeW (off (Ss s) (oEm + (kk s - 1))) (0xbc : Byte) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  generalize hK : kk s = k at hfit k2
  have hE : oEm = 0 := rfl
  have hS := VG.Proof.RsaOaep.PPC64LE.S_fits F
  have ek : (s.gpr .r6).toNat = k := hK
  refine WP.seq (WP.seq (wp_addi fun t₁ o₁ e₁ => wp_addi fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_subi (h := by omega) fun t₄ o₄ e₄ => wp_li (by omega) fun t₅ o₅ e₅ => wp_nil ?_))
  have k₅ : Only [.r4, .r5, .r6] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have a₅ : t₅.gpr .r5 = off (Ss s) (oEm + (k - D - 1)) := by
    rw [o₅.get .r5, e₄, e₃, e₂, o₂.get .r15, o₁.get .r15, o₁.get .r14, h.r14, Base.r15 h, hD]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega
  refine WP.mono (copy_ok (q := off (Ss s) oDig) (p := off (Ss s) (oEm + (k - D - 1))) (n := D) hD0 (by omega)
    (by rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14]) a₅ (by rw [e₅, hD])
    (fun j hj => by
      have := VG.Proof.RsaOaep.PPC64LE.sc_inR F (o := oDig + j) (n := 1) (by unfold oDig oRsa; omega) t₅.rd
      rw [k₅.wr, h.wr]; rwa [← off_off] at this)
    (sc_w F (by rw [k₅.wr, h.wr]) (d := oEm + (k - D - 1)) (by unfold oEm oRsa; omega))
    (fun j hj i hi => by
      show off (off (Ss s) oDig) j ≠ off (off (Ss s) (oEm + (k - D - 1))) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by unfold oDig; omega) (by unfold oEm; omega)
        (by unfold oDig oEm; omega))) fun t₆ ⟨k₆, m₆⟩ => ?_
  have m₆' : t₆.mem = writeBytes t.mem (off (Ss s) (oEm + (k - D - 1))) (Spec.Rsa.bytesAt t.mem (off (Ss s) oDig) D) := by
    rw [m₆, k₅.mem]
  have b₆ := h.wb F (k₅.keep.trans k₆) (d := oEm + (k - D - 1)) (by rw [bytesAt_length]; unfold oEm oRsa; omega) m₆'
  refine wp_addi fun t₇ o₇ e₇ => wp_add fun t₈ o₈ e₈ => wp_subi fun t₉ o₉ e₉ => wp_li (by decide)
    fun t₁₀ o₁₀ e₁₀ => ?_
  have k₁₀ : Only [.r4, .r5] t₆ t₁₀ := (o₇.trans (o₈.trans (o₉.trans o₁₀))).mono
  have a₉ : t₉.gpr .r4 = off (Ss s) (oEm + (k - 1)) := by
    rw [e₉, e₈, e₇, o₇.get .r15, b₆.r14, Base.r15 b₆]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega
  have hA : InRegions t₁₀.wr (t₁₀.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [o₁₀.get .r4, a₉, BitVec.add_zero, k₁₀.wr, b₆.wr]
    exact VG.Proof.RsaOaep.PPC64LE.sc_inW F (by unfold oEm oRsa; omega)
  refine wp_stb rfl hA fun t' m' => wp_nil ?_
  have hv : (t₁₀.gpr .r5).setWidth 8 = (0xbc : Byte) := by rw [e₁₀]; rfl
  have mm : t'.mem = t₆.mem.writeW (off (Ss s) (oEm + (k - 1))) (0xbc : Byte) := by
    rw [m'.mem, o₁₀.get .r4, a₉, BitVec.add_zero, hv, k₁₀.mem]
  refine ⟨(b₆.only F k₁₀).keep F m'.keep (R := [⟨off (Ss s) (oEm + (k - 1)), 1⟩])
    (by rw [mm, ← k₁₀.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oEm oRsa; omega))),
    fun r hr => ?_, by rw [mm, m₆']⟩
  rw [m'.gpr, k₁₀.gpr r (by revert r; decide), k₆.gpr r (by revert r; decide), k₅.gpr r (by revert r; decide)]

end

end VG.Proof.RsaPss.PPC64LE.Sg
