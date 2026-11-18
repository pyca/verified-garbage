module

public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPss.CtPad
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPss.EncBytes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Tab
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaPss.SignCases
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Params
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre

/-! ### `RsaPss.PPC64LE.Sg.Spec`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.Sg.Em`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: `M'` and `EM`

Untrusted: everything here is checked by Lean. The writes to our part of
`scratch`, each keeping `Base`: `M' = 0⁸ ‖ mHash ‖ salt` at `oY`
(`mPrime_ok`); `EM`'s `k` bytes cleared, `0x01` and the salt (`putSalt_ok`),
`H` and `0xbc` (`putH_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

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
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (Ss s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega_using [h, this]) (by unfold oRsa at h; omega_using [h])

/-- Our stack argument `j` into `r`, through `r12`. -/
theorem ldArg_ok {t : State} (h : Base Ss vS s t) {r : Reg} {j : Nat} (hj : j < 16) {is : List Instr}
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
    WP isa (.block (ldArg .r4 10 ++ [mov .r6 .r19])) t fun t' =>
      Only [.r12, .r4, .r6] t t' ∧ t'.gpr .r4 = stackArg s 10 ∧ t'.gpr .r6 = stackArg s 11 :=
  ldArg_ok P h (r := .r4) (j := 10) (by decide) fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ =>
    wp_nil ⟨(o₁.trans o₂).mono, by rw [o₂.get .r4, e₁], by rw [e₂, o₁.get .r19, Base.r19 h]⟩

/-- The salt to `S + d`, from its pointer and length. -/
theorem saltCopy_ok {t : State} (h : Base Ss vS s t) {d : Nat} (h4 : t.gpr .r4 = stackArg s 10)
    (h5 : t.gpr .r5 = off (Ss s) d) (h6 : t.gpr .r6 = stackArg s 11) (hd : d + (stackArg s 11).toNat ≤ oRsa) :
    WP isa (.ite (.nonzero .d .r6) copyLoop (.block [])) t fun t' => Base Ss vS s t' ∧
      (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧ t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by
  generalize hL : (stackArg s 11).toNat = sl at hd
  have F := fits P
  have g6 : t.gpr .r6 = BitVec.ofNat 64 sl := by
    rw [h6, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hb : Spec.Rsa.bytesAt t.mem (stackArg s 10) sl = saltB s := by
    rw [← hL]; exact bytes_entry h.mem (P.ksl.sub_left kR_sub) ((P.sls.symm).sub_left (sc_sub P))
      (by have := P.wsl; omega_using [])
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hs0 : sl ≠ 0 := by intro h0; rw [g6, ne_zero_iff, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 10) (p := off (Ss s) d) (n := sl) (by omega_using [hs0])
      (by omega_using [hL]) h4 h5 g6
      (rd_in (s := s) (t := t) h.rd (R := sR s) (by rw [P.hrd]; simp) P.wsl (by show sl ≤ (stackArg s 11).toNat; omega_using [hL]))
      (sc_w F h.wr (d := d) hd)
      (fun j hj i hi => ne_of_dis P.sls (Offset.contains_base _ (by omega_using [hL, hj]) (by have := P.wsl; omega_using [hL, hj]))
        (by have := scR_contains P (o := d + i) (n := 1) (by omega_using [hd, hi]); rwa [← off_off] at this)))
      fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by rw [hm, hb]
    exact ⟨h.wb F hk' (d := d) (xs := saltB s) (by rw [bytesAt_length, hL]; omega_using [hd]) (by rw [hm, hb]),
      fun r hr => hk'.gpr r (by revert r; decide), hm'⟩
  · have hs0 : sl = 0 := by rw [g6, ne_zero_iff] at hc; simp at hc; unfold oRsa at hd; omega_using [hL, hc]
    refine wp_nil ⟨h, fun r hr => rfl, ?_⟩
    rw [show saltB s = [] by simp [saltB, Spec.Rsa.bytesAt, hL, hs0], writeBytes_nil]

/-- `copySalt`: the salt to `S + d`, after `r5` is set to it. -/
theorem copySalt_ok {t : State} (h : Base Ss vS s t) {d : Nat} (h5 : t.gpr .r5 = off (Ss s) d)
    (hd : d + (stackArg s 11).toNat ≤ oRsa) :
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
    wp_li (by omega_using [hD, hD64]) fun t₇ o₇ e₇ => wp_nil ⟨(o₅.trans (o₆.trans o₇)).mono, by rw [o₇.get .r4, o₆.get .r4, e₅],
      by rw [o₇.get .r5, e₆, o₅.get .r14, h.r14], by rw [e₇, hD]⟩

/-- The digest to `S + oY + 8`. -/
theorem digCopy_ok (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State} (h : Base Ss vS s t) (h4 : t.gpr .r4 = stackArg s 8)
    (h5 : t.gpr .r5 = off (Ss s) (oY + 8)) (h6 : t.gpr .r6 = BitVec.ofNat 64 D) :
    WP isa copyLoop t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes t.mem (off (Ss s) (oY + 8)) (digB D s) := by
  have F := fits P
  have hY : oY = 2560 := rfl
  have hb : Spec.Rsa.bytesAt t.mem (stackArg s 8) D = digB D s :=
    bytes_entry h.mem (P.kdg.sub_left kR_sub) ((P.dgs.symm).sub_left (sc_sub P)) (by have := P.wdg; omega_using [hD64])
  refine WP.mono (copy_ok (q := stackArg s 8) (p := off (Ss s) (oY + 8)) (n := D) hD0 (by omega_using [hD64]) h4 h5 h6
    (rd_in (s := s) (t := t) h.rd (R := dgR D s) (by rw [P.hrd]; simp) P.wdg (Nat.le_refl _))
    (sc_w F h.wr (d := oY + 8) (by unfold oRsa; omega_using [hD64, hY]))
    (fun j hj i hi => ne_of_dis P.dgs (Offset.contains_base _ (by omega_using [hj]) (by have := P.wdg; omega_using [hD64, hj]))
      (by have := scR_contains P (o := oY + 8 + i) (n := 1) (by unfold oRsa; omega_using [hD64, hY, hi]); rwa [← off_off] at this)))
    fun t' ⟨k', m'⟩ => ⟨h.wb F k' (d := oY + 8) (xs := digB D s) (by rw [bytesAt_length]; unfold oRsa; omega_using [hD64, hY])
      (by rw [m', hb]), fun r hr => k'.gpr r (by revert r; decide), by rw [m', hb]⟩

/-- `M' = 0⁸ ‖ mHash ‖ salt` at `S + oY`. -/
theorem mPrime_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hsl : (stackArg s 11).toNat + 8 + D ≤ 2048) :
    WP isa (mPrime H) t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes (writeBytes (writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0))
        (off (Ss s) (oY + 8)) (digB D s)) (off (Ss s) (oY + 8 + D)) (saltB s) := by
  have F := fits P
  have hY : oY = 2560 := rfl
  refine WP.seq (WP.mono (zeros_ok P h) fun t₄ ⟨b₄, g₄, m₄⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (digArgs_ok P hD hD64 b₄) fun t₇ ⟨k₇, e4, e5, e6⟩ =>
    WP.mono (digCopy_ok P hD0 hD64 (b₄.only F k₇) e4 e5 e6) fun t₈ ⟨b₈, g₈, m₈⟩ => ?_))
  refine WP.seq (wp_addi (h := by unfold oY; omega_using [hD, hD64]) fun t₉ o₉ e₉ => wp_nil ?_)
  refine WP.mono (copySalt_ok P (b₈.only F o₉) (d := oY + 8 + D) (by rw [e₉, b₈.r14, hD])
    (by unfold oRsa; omega_using [hsl, hY])) fun t' ⟨b', g', m'⟩ => ⟨b', fun r hr => ?_, ?_⟩
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
  refine WP.mono (zero_ok (p := off (Ss s) oEm) (n := kk s) (b := 0) (by omega_using [hk1]) (by omega_using [hk2])
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂, o₁.get .r15, Base.r15 h]; simp)
    (by rw [e₃]; rfl) (sc_w F (by rw [k₃.wr, h.wr]) (d := oEm) (by unfold oEm oRsa; omega_using [hk2])))
    fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (Ss s) oEm) (List.replicate (kk s) 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb F hK (by rw [List.length_replicate]; unfold oEm oRsa; omega_using [hk2]) hm',
    fun r hr => hK.gpr r (by revert r; decide), hm'⟩

/-- `0x01` at `S + oEm + k - sLen - hLen - 2`, and `r5` after it. -/
theorem saltHead_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : (stackArg s 11).toNat + D + 2 ≤ kk s) :
    WP isa (.block [.addi .r4 .r14 oEm, .add .r4 .r4 .r15, .sub .r4 .r4 .r19, .subi .r4 .r4 (H.D + 2), .li .r5 1,
      .stb .r5 .r4 0, .addi .r5 .r4 1]) t fun t' => Base Ss vS s t' ∧
      (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem.writeW (off (Ss s) (oEm + (kk s - (stackArg s 11).toNat - D - 2))) (1 : Byte) ∧
      t'.gpr .r5 = off (Ss s) (oEm + (kk s - (stackArg s 11).toNat - D - 1)) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  generalize hK : kk s = k at hfit k2
  generalize hL : (stackArg s 11).toNat = sl at hfit
  have hE : oEm = 0 := rfl
  refine wp_addi fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_sub fun t₃ o₃ e₃ =>
    wp_subi (h := by omega_using [hD, hD64]) fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ => ?_
  have k₅ : Only [.r4, .r5] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have a₄ : t₄.gpr .r4 = off (Ss s) (oEm + (k - sl - D - 2)) := by
    rw [e₄, e₃, e₂, e₁, o₁.get .r15, o₂.get .r19, o₁.get .r19, h.r14, Base.r15 h, Base.r19 h, hD]
    apply BitVec.eq_of_toNat_eq
    have := VG.Proof.RsaOaep.PPC64LE.S_fits F
    have ek : (s.gpr .r6).toNat = k := hK
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek, hL] at this ⊢
    unfold oRsa at this; unfold oEm; omega_using [k2, hfit]
  have hA : InRegions t₅.wr (t₅.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [o₅.get .r4, a₄, BitVec.add_zero, k₅.wr, h.wr]; exact VG.Proof.RsaOaep.PPC64LE.sc_inW F (by unfold oEm oRsa; omega_using [k2])
  refine wp_stb rfl hA fun t₆ m₆ => wp_addi fun t₇ o₇ e₇ => wp_nil ?_
  have hv : (t₅.gpr .r5).setWidth 8 = (1 : Byte) := by rw [e₅]; rfl
  have m₇ : t₇.mem = t.mem.writeW (off (Ss s) (oEm + (k - sl - D - 2))) (1 : Byte) := by
    rw [o₇.mem, m₆.mem, o₅.get .r4, a₄, BitVec.add_zero, hv, k₅.mem]
  have b₇ : Base Ss vS s t₇ := (h.only F k₅).keep F (m₆.keep.trans o₇.keep) (R := [⟨off (Ss s) (oEm + (k - sl - D - 2)), 1⟩])
    (by rw [m₇, ← k₅.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oEm oRsa; omega_using [k2])))
  have a₇ : t₇.gpr .r5 = off (Ss s) (oEm + (k - sl - D - 1)) := by
    rw [e₇, m₆.gpr, o₅.get .r4, a₄]
    show off (off (Ss s) (oEm + (k - sl - D - 2))) 1 = _
    rw [off_off, show oEm + (k - sl - D - 2) + 1 = oEm + (k - sl - D - 1) by omega_using [hfit]]
  exact ⟨b₇, fun r hr => by rw [o₇.gpr r (by revert r; decide), m₆.gpr, k₅.gpr r (by revert r; decide)], m₇, a₇⟩

/-- `putSalt`: `0x01` at `S + oEm + k - sLen - hLen - 2`, and the salt after
it. -/
theorem putSalt_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : (stackArg s 11).toNat + D + 2 ≤ kk s) :
    WP isa (putSalt H) t fun t' => Base Ss vS s t' ∧ (∀ r ∈ .r14 :: fx ++ hiRegs, t'.gpr r = t.gpr r) ∧
      t'.mem = writeBytes (t.mem.writeW (off (Ss s) (oEm + (kk s - (stackArg s 11).toNat - D - 2))) (1 : Byte))
        (off (Ss s) (oEm + (kk s - (stackArg s 11).toNat - D - 1))) (saltB s) := by
  have k2 : kk s ≤ 1024 := P.k2
  refine WP.seq (WP.mono (saltHead_ok P hD hD64 h hfit) fun t₇ ⟨b₇, g₇, m₇, a₇⟩ => ?_)
  refine WP.mono (copySalt_ok P b₇ a₇ (by unfold oEm oRsa; omega_using [hfit, k2])) fun t' ⟨b', g', m'⟩ =>
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
    wp_subi (h := by omega_using [hD, hD64]) fun t₄ o₄ e₄ => wp_li (by omega_using [hD, hD64]) fun t₅ o₅ e₅ => wp_nil ?_))
  have k₅ : Only [.r4, .r5, .r6] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have a₅ : t₅.gpr .r5 = off (Ss s) (oEm + (k - D - 1)) := by
    rw [o₅.get .r5, e₄, e₃, e₂, o₂.get .r15, o₁.get .r15, o₁.get .r14, h.r14, Base.r15 h, hD]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega_using [hfit]
  refine WP.mono (copy_ok (q := off (Ss s) oDig) (p := off (Ss s) (oEm + (k - D - 1))) (n := D) hD0 (by omega_using [hD64])
    (by rw [o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14]) a₅ (by rw [e₅, hD])
    (fun j hj => by
      have := VG.Proof.RsaOaep.PPC64LE.sc_inR F (o := oDig + j) (n := 1) (by unfold oDig oRsa; omega_using [hD64, hj]) t₅.rd
      rw [k₅.wr, h.wr]; rwa [← off_off] at this)
    (sc_w F (by rw [k₅.wr, h.wr]) (d := oEm + (k - D - 1)) (by unfold oEm oRsa; omega_using [hD64, k2]))
    (fun j hj i hi => by
      show off (off (Ss s) oDig) j ≠ off (off (Ss s) (oEm + (k - D - 1))) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by unfold oDig; omega_using [hD64, hj]) (by unfold oEm; omega_using [hD64, k2, hi])
        (by unfold oDig oEm; omega_using [hD64, k2, hi]))) fun t₆ ⟨k₆, m₆⟩ => ?_
  have m₆' : t₆.mem = writeBytes t.mem (off (Ss s) (oEm + (k - D - 1))) (Spec.Rsa.bytesAt t.mem (off (Ss s) oDig) D) := by
    rw [m₆, k₅.mem]
  have b₆ := h.wb F (k₅.keep.trans k₆) (d := oEm + (k - D - 1)) (by rw [bytesAt_length]; unfold oEm oRsa; omega_using [hD64, k2]) m₆'
  refine wp_addi fun t₇ o₇ e₇ => wp_add fun t₈ o₈ e₈ => wp_subi fun t₉ o₉ e₉ => wp_li (by decide)
    fun t₁₀ o₁₀ e₁₀ => ?_
  have k₁₀ : Only [.r4, .r5] t₆ t₁₀ := (o₇.trans (o₈.trans (o₉.trans o₁₀))).mono
  have a₉ : t₉.gpr .r4 = off (Ss s) (oEm + (k - 1)) := by
    rw [e₉, e₈, e₇, o₇.get .r15, b₆.r14, Base.r15 b₆]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega_using [hfit]
  have hA : InRegions t₁₀.wr (t₁₀.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [o₁₀.get .r4, a₉, BitVec.add_zero, k₁₀.wr, b₆.wr]
    exact VG.Proof.RsaOaep.PPC64LE.sc_inW F (by unfold oEm oRsa; omega_using [k2])
  refine wp_stb rfl hA fun t' m' => wp_nil ?_
  have hv : (t₁₀.gpr .r5).setWidth 8 = (0xbc : Byte) := by rw [e₁₀]; rfl
  have mm : t'.mem = t₆.mem.writeW (off (Ss s) (oEm + (k - 1))) (0xbc : Byte) := by
    rw [m'.mem, o₁₀.get .r4, a₉, BitVec.add_zero, hv, k₁₀.mem]
  refine ⟨(b₆.only F k₁₀).keep F m'.keep (R := [⟨off (Ss s) (oEm + (k - 1)), 1⟩])
    (by rw [mm, ← k₁₀.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oEm oRsa; omega_using [k2]))),
    fun r hr => ?_, by rw [mm, m₆']⟩
  rw [m'.gpr, k₁₀.gpr r (by revert r; decide), k₆.gpr r (by revert r; decide), k₅.gpr r (by revert r; decide)]

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end

/-!
# RSASSA-PSS signing on PPC64LE: the outcome, by cases

Untrusted: everything here is checked by Lean. `signOut G s`: what the
contract asks of a call from `s`. It is `invalid` if the modulus' first byte
is zero (`signOut_zero`) or the salt does not fit (`signOut_long`), and
otherwise the private operation (`privOut`) on the encoding `encEm`, with
`lo` and the mask `c` the code computes (`signOut_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE
open VG.Proof.RsaPss.PPC64LE (cmB byte_ok)

variable (Gs Gm : Spec.Mgf1.Hash)

/-- The private operation on `em`, with the entry's key. -/
def privOut (s : State) (em : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) em
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r10).toNat)

/-- The outcome `signMdTableContract.post` asks for. -/
def signOut (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign Gs Gm (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .r10).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .r10).toNat)
    (digB Gs.len s) (saltB s)

/-- `H = Hash(0⁸ ‖ mHash ‖ salt)`. -/
abbrev hS (s : State) : List Byte := Gs.hash (Spec.RsaPss.zeros 8 ++ digB Gs.len s ++ saltB s)

/-- `dbLen`. -/
abbrev dbS (s : State) : Nat := kk s - loN s - Gs.len - 1

/-- The mask of `maskedDB`'s first byte, as a byte. -/
abbrev cS (s : State) : Byte := (cmB (s.mem (s.gpr .r5))).setWidth 8

/-- The encoding, as `k` bytes. -/
def encEm (s : State) : List Byte :=
  (List.range (kk s)).map (RsaPss.emT (loN s) (dbS Gs s) (stackArg s 11).toNat (saltB s) (hS Gs s)
    (Spec.Mgf1.mgf1 Gm (hS Gs s) (dbS Gs s)) (cS s))

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hk]⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

theorem signOut_zero {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .r5) = 0) : signOut Gs Gm s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero₂ Gm Gs ..

theorem emLen_eq {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .r5) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (kk s))) - 1) = kk s - loN s := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loN
  split <;> omega_arith

theorem signOut_long {s : State} (hk : 1 ≤ kk s) (h0 : s.mem (s.gpr .r5) ≠ 0)
    (h : kk s - loN s < Gs.len + (stackArg s 11).toNat + 2) : signOut Gs Gm s = .invalid := by
  unfold signOut
  refine RsaPss.sign_long₂ Gm Gs _ _ _ _ _ _ _ _ ?_
  rw [emLen_eq hk h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  exact h

theorem cS_eq {s : State} (h0 : s.mem (s.gpr .r5) ≠ 0) :
    cS s = if (s.mem (s.gpr .r5)).toNat = 1 then 0xFF
      else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .r5)).toNat - 1) := by
  have hn : (s.mem (s.gpr .r5)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (byte_ok _ (s.mem (s.gpr .r5)).isLt hn).2
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  unfold cS
  rw [this]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)

theorem signOut_eq (hHv : Proof.Mgf1.Valid Gs) (hGv : Proof.Mgf1.Valid Gm) {s : State} (hk : 1 ≤ kk s)
    (h0 : s.mem (s.gpr .r5) ≠ 0)
    (hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s) :
    signOut Gs Gm s = privOut s (encEm Gs Gm s) := by
  have hel := emLen_eq hk h0
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .r5 + 1) (kk s - 1)) h0
  unfold signOut privOut encEm
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat = nB at hel ⊢
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  rw [RsaPss.sign_eq₂ Gm Gs hHv hGv h0 (lo := loN s) (db := dbS Gs s)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl hel
    (by rw [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]; unfold loN; split <;> omega_arith) rfl
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact hfit)]
  rw [hel] at hc
  rw [hc, ← cS_eq h0]
  simp only [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [Nat.sub_add_cancel hk]

end VG.Proof.RsaPss.PPC64LE.Sg

end

end

/-! ### `RsaPss.PPC64LE.Sg.Blocks`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: MGF1's registers and `clearTop`

Untrusted: everything here is checked by Lean. `dbArgs_ok`: MGF1's registers
for masking `DB` (`dbLen` bytes at `lo`) with `H` (at `k - hLen - 1`);
`clearTop_ok`: `DB`'s first byte ANDed with the mask `c` of the modulus'
first byte, read again.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 fx hiRegs kR sc_in sc_inW S_fits)
open VG.Proof.RsaPss.PPC64LE (smB loB cmB)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_lbz wp_lsr
  wp_or wp_and wp_stb wp_nil)

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

omit P in
theorem lo_reg {t : State} (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) :
    t.gpr .r23 = BitVec.ofNat 64 (loN s) := by rw [Base.r23 h, lo_eq h0]

/-- MGF1's registers. -/
theorem dbArgs_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) (hfit : D + 2 ≤ kk s - loN s) :
    WP isa (.block (dbArgs H)) t fun t' => Base Ss vS s t' ∧ t'.mem = t.mem ∧
      t'.gpr .r24 = off (Ss s) (oEm + (kk s - D - 1)) ∧ t'.gpr .r25 = BitVec.ofNat 64 D ∧
      t'.gpr .r26 = off (Ss s) (oEm + loN s) ∧ t'.gpr .r27 = BitVec.ofNat 64 (kk s - loN s - D - 1) := by
  have F := fits P
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  have hS := S_fits F
  have ek : (s.gpr .r6).toNat = kk s := rfl
  have hE : oEm = 0 := rfl
  refine wp_addi fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_subi (h := by omega_using [hD, hD64]) fun t₃ o₃ e₃ =>
    wp_li (by omega_using [hD, hD64]) fun t₄ o₄ e₄ => wp_addi fun t₅ o₅ e₅ => wp_add fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_subi (h := by omega_using [hD, hD64]) fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.r24, .r25, .r26, .r27] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  have r15 : ∀ u : State, Only [.r24, .r25, .r26, .r27] t u → u.gpr .r15 = s.gpr .r6 := fun u o => by
    rw [o.get .r15, Base.r15 h]
  refine ⟨h.only F k₈, k₈.mem, ?_, ?_, ?_, ?_⟩
  · rw [o₈.get .r24, o₇.get .r24, o₆.get .r24, o₅.get .r24, o₄.get .r24, e₃, e₂, e₁,
      r15 t₁ (o₁.mono), h.r14, hD]
    apply BitVec.eq_of_toNat_eq
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at hS ⊢
    unfold oRsa at hS; unfold oEm; omega_using [hfit]
  · rw [o₈.get .r25, o₇.get .r25, o₆.get .r25, o₅.get .r25, e₄, hD]
  · rw [o₈.get .r26, o₇.get .r26, e₆, e₅, o₅.get .r23, o₄.get .r23, o₃.get .r23, o₂.get .r23, o₁.get .r23,
      lo_reg h h0, o₄.get .r14, o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14]
    show _ = off (Ss s) (oEm + loN s)
    rw [← off_off]
  · rw [e₈, e₇, r15 t₆ ((o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono),
      o₆.get .r23, o₅.get .r23, o₄.get .r23, o₃.get .r23, o₂.get .r23, o₁.get .r23, lo_reg h h0, hD,
      ← ofNat_toNat (s.gpr .r6), ek, Offset.ofNat_sub_ofNat (by omega_using [hfit]), Offset.ofNat_sub_ofNat (by omega_using [hfit])]
    congr 1

omit P in
/-- The mask `c` of the byte `b`, as a byte. -/
theorem and_mask (b : Byte) (x : BitVec 64) : ((b.setWidth 64 &&& x).setWidth 8 : Byte) = b &&& x.setWidth 8 := by
  rw [BitVec.setWidth_and]
  congr 1
  exact BitVec.setWidth_setWidth_of_le _ (by decide)

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Ss vS s t) (h0 : s.mem (s.gpr .r5) ≠ 0) :
    WP isa (.block clearTop) t fun t' => Base Ss vS s t' ∧
      t'.mem = t.mem.writeW (off (Ss s) (oEm + loN s)) (view t.mem (Ss s) (oEm + loN s) &&& cS s) := by
  have F := fits P
  have hl1 := loN_le s
  have hn := n_contains P
  have hE : oEm = 0 := rfl
  have hR : oRsa = 8192 := rfl
  simp only [clearTop, List.cons_append, List.nil_append]
  refine wp_lbz (a := s.gpr .r5) (by rw [Base.r20 h, BitVec.add_zero])
    (by rw [h.rd, P.hrd]; exact ⟨nR s, List.mem_append_left _ (by simp), hn⟩) fun t₁ o₁ e₁ => ?_
  have hb : t.mem (s.gpr .r5) = s.mem (s.gpr .r5) := h.mem _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.kn.sub_left kR_sub) _ hc hn
    · exact (P.ns.sub_right (sc_sub P)).symm _ hc hn
  refine wp_lsr fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_or fun t₄ o₄ e₄ => wp_lsr fun t₅ o₅ e₅ =>
    wp_or fun t₆ o₆ e₆ => wp_lsr fun t₇ o₇ e₇ => wp_or fun t₈ o₈ e₈ => wp_subi fun t₉ o₉ e₉ =>
    wp_lsr fun t₁₀ o₁₀ e₁₀ => wp_li (by decide) fun t₁₁ o₁₁ e₁₁ => wp_sub fun t₁₂ o₁₂ e₁₂ =>
    wp_li (by decide) fun t₁₃ o₁₃ e₁₃ => wp_and fun t₁₄ o₁₄ e₁₄ => wp_or fun t₁₅ o₁₅ e₁₅ =>
    wp_addi fun t₁₆ o₁₆ e₁₆ => wp_add fun t₁₇ o₁₇ e₁₇ => ?_
  have x8 : t₈.gpr .r10 = smB (s.mem (s.gpr .r5)) := by
    rw [e₈, o₇.get .r10, e₇, e₆, o₅.get .r10, e₅, e₄, o₃.get .r10, e₃, e₂, e₁, hb]; rfl
  have x10 : t₁₀.gpr .r11 = loB (s.mem (s.gpr .r5)) := by rw [e₁₀, e₉, x8]; rfl
  have x15 : t₁₅.gpr .r10 = cmB (s.mem (s.gpr .r5)) := by
    rw [e₁₅, o₁₄.get .r10, o₁₃.get .r10, o₁₂.get .r10, o₁₁.get .r10, o₁₀.get .r10, o₉.get .r10, x8, e₁₄,
      o₁₃.get .r8, e₁₂, e₁₁, o₁₁.get .r11, x10, e₁₃]; rfl
  have K : Only [.r9, .r10, .r11, .r8, .r7] t t₁₅ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans
      (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅)))))))))))))).mono
  have K₁₇ : Only [.r9, .r10, .r11, .r8, .r7, .r4] t t₁₇ := (K.trans (o₁₆.trans o₁₇)).mono
  have x17 : t₁₇.gpr .r4 = off (Ss s) (oEm + loN s) := by
    rw [e₁₇, e₁₆, o₁₆.get .r23, K.get .r23, K.get .r14, lo_reg h h0, h.r14, ← off_off]
  have hin : InRegions (t₁₇.rd ++ t₁₇.wr) (off (Ss s) (oEm + loN s)) 1 := by
    rw [K₁₇.wr, h.wr]
    have := VG.Proof.RsaOaep.PPC64LE.sc_inR F (o := oEm + loN s) (n := 1) (by omega_using [hl1, hE, hR]) t₁₇.rd
    exact this
  refine wp_lbz (a := off (Ss s) (oEm + loN s)) (by rw [x17, BitVec.add_zero]) hin fun t₁₈ o₁₈ e₁₈ =>
    wp_and fun t₁₉ o₁₉ e₁₉ => ?_
  have K₁₉ : Only [.r9, .r10, .r11, .r8, .r7, .r4, .r5] t t₁₉ := (K₁₇.trans (o₁₈.trans o₁₉)).mono
  refine wp_stb (a := off (Ss s) (oEm + loN s)) (by rw [o₁₉.get .r4, o₁₈.get .r4, x17, BitVec.add_zero])
    (by rw [K₁₉.wr, h.wr]; exact sc_inW F (by omega_using [hl1, hE, hR])) fun t' m' => wp_nil ?_
  have hv : (t₁₉.gpr .r5).setWidth 8 = view t.mem (Ss s) (oEm + loN s) &&& cS s := by
    rw [e₁₉, e₁₈, o₁₈.get .r10, o₁₇.get .r10, o₁₆.get .r10, x15, K₁₇.mem, and_mask]; rfl
  have hm : t'.mem = t.mem.writeW (off (Ss s) (oEm + loN s)) (view t.mem (Ss s) (oEm + loN s) &&& cS s) := by
    rw [m'.mem, hv, K₁₉.mem]
  refine ⟨(h.only F K₁₉).keep F m'.keep (R := [⟨off (Ss s) (oEm + loN s), 1⟩])
    (by rw [hm, ← K₁₉.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega_using [hl1, hE, hR]))), hm⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end

/-! ### `RsaPss.PPC64LE.Sg.PrivCall`, which this module and modules that import it used -/

section

/-! ### `RsaPss.PPC64LE.Sg.PrivArgs`, which only this module used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: the private operation's arguments

Untrusted: everything here is checked by Lean. In the frame of `privBytes`
bytes below ours (`pb`), `privArgs` writes `vg_rsa_private_checked`'s twelve
stack arguments to its Parameter Save Area (`psa`: `p`, `p_len`, our stack
arguments 0 to 7, the rest of `scratch` and its length in words) and sets its
registers: `out`, `n`, `e` and `EM` (`AtPriv`), as RSAES-OAEP decryption does.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr stackArgAddr_fb saved_offs
  allocated_sp allocated_rd allocated_wr allocated_gpr allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_std wp_mov wp_li wp_add wp_addi wp_subi wp_addSp wp_nil)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem privBytes_rng (pc : Bool) : 192 ≤ privBytes pc ∧ privBytes pc ≤ 208 := by
  cases pc <;> decide

theorem privBytes_mod (pc : Bool) : privBytes pc % 16 = 0 := by cases pc <;> decide

theorem pbd {pc : Bool} {d : Nat} (h : d ≤ 192) : d ≤ privBytes pc := Nat.le_trans h (privBytes_rng pc).1

/-- The base of the private operation's frame. -/
abbrev pb (pc : Bool) (s : State) : Addr := fb s - BitVec.ofNat 64 (privBytes pc)

/-- Its stack argument `i`, as `privArgs` writes it. -/
def psa (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r9
  | 1 => s.gpr .r10
  | 10 => Ss s + BitVec.ofNat 64 oRsa
  | 11 => BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)
  | 12 => stackArg s 16
  | 13 => stackArg s 17
  | i + 2 => stackArg s i

/-- The call's stack arguments: 12, or with `pc` 14. -/
abbrev nP (pc : Bool) : Nat := if pc then 14 else 12

theorem pb_eq (s : State) : pb pc s = s.sp - BitVec.ofNat 64 (frameBytes + privBytes pc) := by
  rw [pb, fb, BitVec.sub_sub, BitVec.ofNat_add]

theorem pb_base (s : State) :
    pb pc s = (s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes := by
  rw [pb, fb, ← Offset.sub_add_eq, ← BitVec.ofNat_add, ← Offset.sub_sub_eq,
    Offset.ofNat_sub_ofNat (by have := stackBytes_ge pc; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [this])]
  rw [show stackBytes pc - Impl.Rsa.PPC64LE.Priv.frameBytes = frameBytes + privBytes pc by unfold stackBytes; omega_using []]

/-- The region of `pb pc s + d` within the stack the function uses. -/
theorem pb_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes + privBytes pc) :
    Region.Sub ⟨pb pc s + BitVec.ofNat 64 d, n⟩ (kS pc s) := by
  rw [pb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes; omega_using [h])

/-- In the private operation's frame, at the call, with `em` at `scratch`. -/
structure AtPriv (pc : Bool) (s : State) (em : List Byte) (t : State) : Prop where
  sp : t.sp = pb pc s
  rd : t.rd = s.rd
  wr : t.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr
  mem : Frame [kS pc s, SC Ss s] s.mem t.mem
  em : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  r3 : t.gpr .r3 = s.gpr .r3
  r4 : t.gpr .r4 = s.gpr .r6
  r5 : t.gpr .r5 = s.gpr .r5
  r6 : t.gpr .r6 = s.gpr .r6
  r7 : t.gpr .r7 = s.gpr .r7
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = off (Ss s) oEm
  r10 : t.gpr .r10 = s.gpr .r6
  psa : ∀ i < nP pc, t.mem.readW (pb pc s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i

/-- The state of the copies of our stack arguments: `n` of them done. -/
structure Cp (pc : Bool) (s t₀ : State) (n : Nat) (t : State) : Prop where
  k : Keep [.r0] t₀ t
  mem : Frame [⟨pb pc s + BitVec.ofNat 64 112, 64⟩] t₀.mem t.mem
  got : ∀ j < n, t.mem.readW (pb pc s + BitVec.ofNat 64 (112 + 8 * j)) 64 = stackArg s j

theorem privArgs_eq : privArgs pc = (([.addSp .r12 0, .store .d .r17 .r12 96, .store .d .r18 .r12 104] : List Instr) ++
    ((List.range 8).flatMap fun j => [.load .d .r0 .r12 (argP pc j), .store .d .r0 .r12 (112 + 8 * j)])) ++
    (([.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP pc 13),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184] : List Instr) ++ (preArgs pc ++
    ([Impl.AesGcm.PPC64LE.mov .r3 .r16,
      Impl.AesGcm.PPC64LE.mov .r4 .r15, Impl.AesGcm.PPC64LE.mov .r5 .r20, Impl.AesGcm.PPC64LE.mov .r6 .r15,
      Impl.AesGcm.PPC64LE.mov .r7 .r21, Impl.AesGcm.PPC64LE.mov .r8 .r22, .addi .r9 .r14 oEm,
      Impl.AesGcm.PPC64LE.mov .r10 .r15] : List Instr))) := by
  simp only [privArgs, List.append_assoc, List.cons_append, List.nil_append]

theorem sub_ofNat {x : BitVec 64} {a : Nat} (h : a ≤ x.toNat) : x - BitVec.ofNat 64 a = BitVec.ofNat 64 (x.toNat - a) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) (by omega_using [h]), Nat.mod_eq_of_lt (a := x.toNat - a) (by omega_using [])]; omega_using [h]

/-- The private operation's frame. -/
abbrev PB (pc : Bool) (s : State) : Region := ⟨pb pc s, privBytes pc⟩

theorem pb_in (s : State) {d : Nat} (h : d + 8 ≤ privBytes pc) : (PB pc s).Contains (pb pc s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by have := privBytes_rng pc; omega_using [h, this])

theorem psa_in {s : State} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ privBytes pc) :
    InRegions (⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr) (pb pc s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by have := privBytes_rng pc; omega_using [h₂])
    (by have := privBytes_rng pc; omega_using [this])⟩

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

omit P in
theorem PB_sub : Region.Sub (PB pc s) (kS pc s) := by
  have := pb_sub (pc := pc) s (d := 0) (n := privBytes pc) (by omega_using []); rwa [BitVec.add_zero] at this

/-- A load of our stack argument `j` through `b`, which holds `fb s - o`. -/
theorem wp_argS {t : State} {r b : Reg} {j o : Nat} {is : List Instr} {Q : State → Prop}
    (ha : (aR pc s).Contains (stackArgAddr s j) 8)
    (hb : t.gpr b = fb s - BitVec.ofNat 64 o) (hrd : t.rd = s.rd) (hm : Frame [kS pc s, SC Ss s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : o + arg j < 2 ^ 15 ∧ (o + arg j) % 4 = 0 := by decide) (hb0 : b ≠ .r0 := by decide) :
    WP isa (.block (.load .d r b (o + arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by
    rw [hb, stackArgAddr_fb, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]) ?_
    (fun t' o' e => k t' o' ?_) hb0 ho
  · rw [hrd, P.hrd]; exact ⟨aR pc s, by simp, ha⟩
  · rw [e, stackArg, hm.readW ha (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.ka.symm
      · exact (P.sa.sub_left (sc_sub P)).symm) (by decide)]

/-- The copies of our stack arguments 0 to `n - 1`. -/
theorem copies_ok {t₀ : State} (h12 : t₀.gpr .r12 = pb pc s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr) (hm : Frame [kS pc s, SC Ss s] s.mem t₀.mem) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j =>
      [.load .d .r0 .r12 (argP pc j), .store .d .r0 .r12 (112 + 8 * j)])) t₀ (Cp pc s t₀ n)
  | 0, _ => wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (copies_ok h12 hrd hwr hm n (by omega_using [hn])) fun t ⟨k, fm, got⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain hmt : Frame [kS pc s, SC Ss s] s.mem t.mem := hm.trans (fm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kS pc s, List.mem_cons_self .., pb_sub s (by have := privBytes_rng pc; unfold frameBytes; omega_using [])⟩)
    obtain hb : t.gpr .r12 = fb s - BitVec.ofNat 64 (privBytes pc) := by rw [k.get .r12, h12]
    refine wp_argS P (j := n) (o := privBytes pc) (in_aR (by omega_using [hn])) hb (k.rd.trans hrd) hmt (fun t₁ o₁ e₁ => ?_)
      ⟨by have := privBytes_rng pc; unfold arg frameBytes; omega_using [hn, this],
        by have := privBytes_mod pc; unfold arg frameBytes; omega_using [this]⟩
    obtain hw : InRegions t₁.wr (pb pc s + BitVec.ofNat 64 (112 + 8 * n)) 8 := by
      rw [o₁.wr, k.wr, hwr]; exact psa_in (by omega_using []) (by have := privBytes_rng pc; omega_using [hn, this])
    refine wp_std (a := pb pc s + BitVec.ofNat 64 (112 + 8 * n)) (by rw [o₁.get .r12, hb]) hw (fun t₂ m₂ => wp_nil ?_)
      (by decide) ⟨by omega_using [hn], by omega_using []⟩
    obtain k₂ : Keep [.r0] t₀ t₂ := (k.trans (o₁.keep.trans m₂.keep)).mono
    refine ⟨k₂, ?_, fun j hj => ?_⟩
    · rw [m₂.mem, o₁.mem]
      exact fm.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using []))
    · rw [m₂.mem, o₁.mem]
      by_cases hj' : j < n
      · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hj'])) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide), got j hj']
      · rw [show j = n by omega_using [hj, hj'], Mem.readW_writeW_self64, e₁]

/-- With `pc`, our stack arguments 16 and 17, `pre` and `pre_len`, to the
call's 12 and 13. -/
theorem preArgs_ok {u : State} (h12 : u.gpr .r12 = pb pc s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr)
    (hm : Frame [kS pc s, SC Ss s] s.mem u.mem) :
    WP isa (.block (preArgs pc)) u fun u' => Keep [.r0] u u' ∧
      Frame [⟨pb pc s + BitVec.ofNat 64 192, privBytes pc - 192⟩] u.mem u'.mem ∧
      (pc = true → u'.mem.readW (pb pc s + BitVec.ofNat 64 192) 64 = stackArg s 16 ∧
        u'.mem.readW (pb pc s + BitVec.ofNat 64 200) 64 = stackArg s 17) := by
  cases pc with
  | false => exact wp_nil ⟨Keep.refl _ _, Frame.refl _ _, fun h => nomatch h⟩
  | true =>
    have hb : u.gpr .r12 = fb s - BitVec.ofNat 64 (privBytes true) := h12
    obtain in18 : ∀ {j : Nat}, j < 18 → (aR true s).Contains (stackArgAddr s j) 8 := fun hj => by
      rw [VG.Proof.RsaOaep.PPC64LE.stackArgAddr_eq s _]
      exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])
    refine wp_argS P (j := 16) (o := privBytes true) (in18 (by decide)) hb hrd hm (fun u₁ o₁ e₁ => ?_)
      ⟨by decide, by decide⟩
    refine wp_std (a := pb true s + BitVec.ofNat 64 192) (by rw [o₁.get .r12, h12])
      (by rw [o₁.wr, hwr]; exact psa_in (by decide) (by decide)) fun u₂ m₂ => ?_
    obtain f₂ : Frame [⟨pb true s + BitVec.ofNat 64 192, privBytes true - 192⟩] u.mem u₂.mem := by
      rw [m₂.mem, o₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by simp only [privBytes, ↓reduceIte]; omega_using []) (by decide))
    obtain hm₂ : Frame [kS true s, SC Ss s] s.mem u₂.mem := hm.trans (f₂.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kS true s, List.mem_cons_self .., pb_sub s (by decide)⟩)
    refine wp_argS P (j := 17) (o := privBytes true) (in18 (by decide)) (by rw [m₂.gpr, o₁.get .r12, hb])
      (by rw [m₂.rd, o₁.rd, hrd]) hm₂ (fun u₃ o₃ e₃ => ?_) ⟨by decide, by decide⟩
    refine wp_std (a := pb true s + BitVec.ofNat 64 200) (by rw [o₃.get .r12, m₂.gpr, o₁.get .r12, h12])
      (by rw [o₃.wr, m₂.wr, o₁.wr, hwr]; exact psa_in (by decide) (by decide)) fun u₄ m₄ => wp_nil ?_
    refine ⟨(o₁.keep.trans (m₂.keep.trans (o₃.keep.trans m₄.keep))).mono, ?_, fun _ => ⟨?_, ?_⟩⟩
    · rw [m₄.mem, o₃.mem]
      exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by simp only [privBytes, ↓reduceIte]; omega_using []) (by decide))
    · rw [m₄.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), o₃.mem,
        m₂.mem, Mem.readW_writeW_self64, e₁]
    · rw [m₄.mem, Mem.readW_writeW_self64, e₃]

theorem privArgs_ok {t : State} (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) :
    WP isa (.block (privArgs pc)) (allocated (privBytes pc) t) (AtPriv pc s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have usp : (allocated (privBytes pc) t).sp = pb pc s := by rw [allocated_sp, hsp]
  have uwr : (allocated (privBytes pc) t).wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr := by
    rw [allocated_wr, h.sv.wr, frameR, hsp]; rfl
  have urd : (allocated (privBytes pc) t).rd = s.rd := by rw [allocated_rd, h.rd]
  have um : Frame [PB pc s] t.mem (allocated (privBytes pc) t).mem := by
    rw [allocated_mem]
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [hsp, show fb s - BitVec.ofNat 64 (privBytes pc) = pb pc s + BitVec.ofNat 64 0 by rw [BitVec.add_zero]]
    exact pb_in s (pbd (by decide))
  have ug : (allocated (privBytes pc) t).gpr = t.gpr := rfl
  have hmS : ∀ {x : State}, Frame [PB pc s] t.mem x.mem → Frame [kS pc s, SC Ss s] s.mem x.mem := fun hx =>
    (h.mem.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨kS pc s, List.mem_cons_self .., kR_sub⟩
      · exact ⟨SC Ss s, by simp, fun _ h => h⟩).trans
      (hx.sub fun r hr => ⟨kS pc s, List.mem_cons_self .., by rw [List.mem_singleton.mp hr]; exact PB_sub⟩)
  rw [privArgs_eq, WP.block_append_iff, WP.block_append_iff]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [usp, BitVec.add_zero] at e₁
  refine wp_std (a := pb pc s + BitVec.ofNat 64 96) (by rw [e₁]) (by rw [o₁.wr, uwr]; exact psa_in (by decide) (pbd (by decide)))
    fun u₂ m₂ => ?_
  refine wp_std (a := pb pc s + BitVec.ofNat 64 104) (by rw [m₂.gpr, e₁])
    (by rw [m₂.wr, o₁.wr, uwr]; exact psa_in (by decide) (pbd (by decide))) fun u₃ m₃ => wp_nil ?_
  have k₃ : Keep [.r12] (allocated (privBytes pc) t) u₃ := (o₁.keep.trans (m₂.keep.trans m₃.keep)).mono
  have f₃ : Frame [PB pc s] t.mem u₃.mem := by
    rw [m₃.mem, m₂.mem, o₁.mem]
    exact (um.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))).writeW (List.mem_singleton_self _) _
      (pb_in s (pbd (by decide)))
  have r₃₉₆ : u₃.mem.readW (pb pc s + BitVec.ofNat 64 96) 64 = s.gpr .r9 := by
    rw [m₃.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₂.mem,
      Mem.readW_writeW_self64, o₁.get .r17, ug, Base.r17 h]
  have r₃₁₀₄ : u₃.mem.readW (pb pc s + BitVec.ofNat 64 104) 64 = s.gpr .r10 := by
    rw [m₃.mem, Mem.readW_writeW_self64, m₂.gpr, o₁.get .r18, ug, Base.r18 h]
  have g₃ : u₃.gpr .r12 = pb pc s := by rw [m₃.gpr, m₂.gpr, e₁]
  refine WP.mono (copies_ok P (t₀ := u₃) g₃ (by rw [k₃.rd, urd]) (by rw [k₃.wr, uwr]) (hmS f₃) 8 (Nat.le_refl 8))
    fun u₄ ⟨k₄, f₄, got⟩ => ?_
  have g₄ : u₄.gpr .r12 = pb pc s := by rw [k₄.get .r12, g₃]
  have w₄ : u₄.wr = ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ :: fr s :: s.wr := by rw [k₄.wr, k₃.wr, uwr]
  have f₄' : Frame [PB pc s] t.mem u₄.mem := f₃.trans (f₄.sub fun r hr => ⟨PB pc s, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (pbd (by decide))⟩)
  refine wp_li (by decide) fun u₅ o₅ e₅ => wp_add fun u₆ o₆ e₆ => ?_
  have g₆ : u₆.gpr .r12 = pb pc s := by rw [o₆.get .r12, o₅.get .r12, g₄]
  refine wp_std (a := pb pc s + BitVec.ofNat 64 176) (by rw [g₆]) (by rw [o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (pbd (by decide)))
    fun u₇ m₇ => ?_
  have f₇ : Frame [PB pc s] t.mem u₇.mem := by
    rw [m₇.mem, o₆.mem, o₅.mem]; exact f₄'.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))
  have rd₇ : u₇.rd = s.rd := by rw [m₇.rd, o₆.rd, o₅.rd, k₄.rd, k₃.rd, urd]
  refine wp_argS P (j := 13) (o := privBytes pc) (in_aR (by decide)) (by rw [m₇.gpr, g₆]) rd₇ (hmS f₇)
    (fun u₈ o₈ e₈ => ?_) ⟨by have := privBytes_rng pc; unfold arg frameBytes; omega_using [this],
      by have := privBytes_mod pc; unfold arg frameBytes; omega_using [this]⟩
  refine wp_subi fun u₉ o₉ e₉ => ?_
  refine wp_std (a := pb pc s + BitVec.ofNat 64 184) (by rw [o₉.get .r12, o₈.get .r12, m₇.gpr, g₆])
    (by rw [o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, w₄]; exact psa_in (by decide) (pbd (by decide))) fun u₁₀ m₁₀ => ?_
  have f₁₀ : Frame [PB pc s] t.mem u₁₀.mem := by
    rw [m₁₀.mem, o₉.mem, o₈.mem]; exact f₇.writeW (List.mem_singleton_self _) _ (pb_in s (pbd (by decide)))
  show WP isa (.block (preArgs pc ++ _)) _ _
  rw [WP.block_append_iff]
  refine WP.mono (preArgs_ok P (u := u₁₀) (by rw [m₁₀.gpr, o₉.get .r12, o₈.get .r12, m₇.gpr, g₆])
    (by rw [m₁₀.rd, o₉.rd, o₈.rd, rd₇]) (by rw [m₁₀.wr, o₉.wr, o₈.wr, m₇.wr, o₆.wr, o₅.wr, w₄]) (hmS f₁₀))
    fun u₁₀' ⟨kp, fp, hp⟩ => ?_
  refine wp_mov fun u₁₁ o₁₁ e₁₁ => wp_mov fun u₁₂ o₁₂ e₁₂ => wp_mov fun u₁₃ o₁₃ e₁₃ =>
    wp_mov fun u₁₄ o₁₄ e₁₄ => wp_mov fun u₁₅ o₁₅ e₁₅ => wp_mov fun u₁₆ o₁₆ e₁₆ => wp_addi fun u₁₇ o₁₇ e₁₇ =>
    wp_mov fun w ow ew => wp_nil ?_
  have K : Keep [.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] (allocated (privBytes pc) t) w :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      (m₁₀.keep.trans (kp.trans (o₁₁.keep.trans (o₁₂.keep.trans (o₁₃.keep.trans (o₁₄.keep.trans (o₁₅.keep.trans
      (o₁₆.keep.trans (o₁₇.keep.trans ow.keep)))))))))))))))).mono
  have kt : ∀ r ∉ [Reg.r12, .r0, .r11, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], w.gpr r = t.gpr r :=
    fun r hr => by rw [K.gpr r hr]; rfl
  have K₁₀ : Keep [.r12, .r0, .r11] (allocated (privBytes pc) t) u₁₀ :=
    ((k₃.trans (k₄.trans ((o₅.keep.trans o₆.keep).trans (m₇.keep.trans (o₈.keep.trans (o₉.keep.trans
      m₁₀.keep))))))).mono
  have k10 : ∀ r ∉ [Reg.r12, .r0, .r11], u₁₀'.gpr r = t.gpr r := fun r hr => by
    rw [kp.gpr r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; decide)), K₁₀.gpr r hr]; rfl
  have hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have v184 : u₉.gpr .r11 = psa s 11 := by rw [e₉, e₈]; exact sub_ofNat hl
  have v176 : u₆.gpr .r0 = psa s 10 := by
    rw [e₆, o₅.get .r14, e₅, k₄.get .r14, k₃.get .r14, ug, h.r14]; rfl
  have wm0 : w.mem = u₁₀'.mem := by
    rw [ow.mem, o₁₇.mem, o₁₆.mem, o₁₅.mem, o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem]
  have wm : u₁₀.mem = (u₇.mem.writeW (pb pc s + BitVec.ofNat 64 184) (psa s 11)) := by
    rw [m₁₀.mem, o₉.mem, o₈.mem, v184]
  have m7 : u₇.mem = (u₄.mem.writeW (pb pc s + BitVec.ofNat 64 176) (psa s 10)) := by
    rw [m₇.mem, o₆.mem, o₅.mem, v176]
  have fw : Frame [PB pc s] t.mem w.mem := by
    rw [wm0]
    exact f₁₀.trans (fp.sub fun r hr => ⟨PB pc s, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by have := privBytes_rng pc; omega_using [this])⟩)
  have sl : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [PB pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r :=
    fun hd r hr => by
      rw [List.mem_singleton.mp hr]
      have h := Offset.disjoint_below_above (fb s) (m := privBytes pc) (a := 0) (l := frameBytes)
        (by have := privBytes_rng pc; unfold frameBytes; omega_using [this])
      rw [BitVec.add_zero] at h
      exact (h.sub_right (Offset.sub_base _ hd)).symm
  have sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ privBytes pc → b + 8 ≤ privBytes pc →
      Mem.Sep (pb pc s + BitVec.ofNat 64 a) (64 / 8) (pb pc s + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    Offset.sep _ h (by have := privBytes_rng pc; omega_using [ha, this]) (by have := privBytes_rng pc; omega_using [hb, this])
  have hpsa : ∀ i < nP pc, w.mem.readW (pb pc s + BitVec.ofNat 64 (96 + 8 * i)) 64 = psa s i := by
    intro i hi'
    rw [wm0]
    by_cases hi : i < 12
    rotate_left
    · cases pc with
      | false => exact absurd hi' (by simp only [nP, Bool.false_eq_true, ↓reduceIte]; omega_using [hi])
      | true =>
        rcases (by simp only [nP, ↓reduceIte] at hi'; omega_using [hi, hi'] : i = 12 ∨ i = 13) with rfl | rfl
        · exact (hp rfl).1
        · exact (hp rfl).2
    rw [fp.readW (r := ⟨pb pc s + BitVec.ofNat 64 (96 + 8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by have := privBytes_rng pc; omega_using [this])) (by decide), wm]
    by_cases h11 : i = 11
    · subst h11; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h11]) (by have := privBytes_rng pc; omega_using [hi, this]) (pbd (by decide))) (by decide), m7]
    by_cases h10 : i = 10
    · subst h10; exact Mem.readW_writeW_self64 _ _ _
    rw [Mem.readW_writeW_sep (sep (by omega_using [h10]) (by have := privBytes_rng pc; omega_using [hi, this]) (pbd (by decide))) (by decide)]
    have fr4 : ∀ {d : Nat}, d + 8 ≤ 112 → u₄.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 =
        u₃.mem.readW (pb pc s + BitVec.ofNat 64 d) 64 := fun hd =>
      f₄.readW (r := ⟨pb pc s + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl hd) (by omega_using [hd]) (by decide)) (by decide)
    by_cases h0 : i = 0
    · subst h0; rw [fr4 (by decide)]; exact r₃₉₆
    by_cases h1 : i = 1
    · subst h1; rw [fr4 (by decide)]; exact r₃₁₀₄
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega_using [h0, h1]⟩
      rw [show 96 + 8 * (j + 2) = 112 + 8 * j by omega_using [], got j (by omega_using [hi, h11, h10])]
      rcases (by omega_using [hi, h11, h10] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hemw : Spec.Rsa.bytesAt w.mem (off (Ss s) oEm) (kk s) = em := by
    rw [← hem]
    have hk2 : kk s ≤ 1024 := P.k2
    have hR : Region.Sub ⟨off (Ss s) oEm, kk s⟩ (scR s) := fun a ha =>
      sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by unfold oEm oRsa; omega_using [hk2]) a ha)
    have hd : (PB pc s).Disjoint ⟨off (Ss s) oEm, kk s⟩ := (P.ks.sub_left PB_sub).sub_right hR
    exact VG.Proof.RsaOaep.PPC64LE.bytes_entry (A := PB pc s) (B := PB pc s)
      (fw.mono fun r hr => by simp at hr ⊢; exact hr) hd hd
      (by have := (fits P).wS; unfold oEm oRsa at *; omega_using [hk2])
  refine ⟨by rw [K.sp, usp], by rw [K.rd, urd], by rw [K.wr, uwr], hmS fw, hemw,
    h.sv.sv.frame fw fun p hp r hr => sl (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr,
    by rw [fw.readW (Region.contains_self _ _) (sl (by decide)) (by decide)]; exact h.sv.ls,
    fun r hr => by rw [kt r (by revert r; decide)]; exact h.sv.hi r hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpsa⟩
  · rw [ow.get .r3, o₁₇.get .r3, o₁₆.get .r3, o₁₅.get .r3, o₁₄.get .r3, o₁₃.get .r3, o₁₂.get .r3, e₁₁,
      k10 .r16 (by decide), Base.r16 h]
  · rw [ow.get .r4, o₁₇.get .r4, o₁₆.get .r4, o₁₅.get .r4, o₁₄.get .r4, o₁₃.get .r4, e₁₂, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r5, o₁₇.get .r5, o₁₆.get .r5, o₁₅.get .r5, o₁₄.get .r5, e₁₃, o₁₂.get .r20, o₁₁.get .r20,
      k10 .r20 (by decide), Base.r20 h]
  · rw [ow.get .r6, o₁₇.get .r6, o₁₆.get .r6, o₁₅.get .r6, e₁₄, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]
  · rw [ow.get .r7, o₁₇.get .r7, o₁₆.get .r7, e₁₅, o₁₄.get .r21, o₁₃.get .r21, o₁₂.get .r21, o₁₁.get .r21,
      k10 .r21 (by decide), Base.r21 h]
  · rw [ow.get .r8, o₁₇.get .r8, e₁₆, o₁₅.get .r22, o₁₄.get .r22, o₁₃.get .r22, o₁₂.get .r22, o₁₁.get .r22,
      k10 .r22 (by decide), Base.r22 h]
  · rw [ow.get .r9, e₁₇, o₁₆.get .r14, o₁₅.get .r14, o₁₄.get .r14, o₁₃.get .r14, o₁₂.get .r14, o₁₁.get .r14,
      k10 .r14 (by decide), h.r14]
  · rw [ew, o₁₇.get .r15, o₁₆.get .r15, o₁₅.get .r15, o₁₄.get .r15, o₁₃.get .r15, o₁₂.get .r15, o₁₁.get .r15,
      k10 .r15 (by decide), Base.r15 h]

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: the private operation

Untrusted: everything here is checked by Lean. The call's narrowed entry
state (`callE`: it reads `n`, `e`, `EM`, the private key and its stack
arguments, and writes `out` and the rest of `scratch`), its precondition
(`preP_at`) and regions (`call_covers`); `priv_ok`: the private operation's
frame, its arguments and the call of `vg_rsa_private_checked` write RSASP1
of `EM`, checked against `e`, to `out` and return its code (`privOut`), and
leave what the restores need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr Saves saved_offs)

/-- `out`, `EM` and the rest of `scratch`. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, kk s⟩
abbrev emR (s : State) : Region := ⟨off (Ss s) oEm, kk s⟩
abbrev rsR (s : State) : Region := ⟨Ss s + BitVec.ofNat 64 oRsa, ((stackArg s 13).toNat - 1024) * 8⟩
/-- The call's stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨pb pc s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [psaR pc s]
abbrev callWr (s : State) : List Region := [outR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE pc s t).sp = t.sp := rfl

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtPriv pc s em t) {i : Nat} (hi : i < nP pc) :
    stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} {em : List Byte} (A : AtPriv pc s em t) :
    stackArgAddr (callE pc s t) 0 = pb pc s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

theorem privP_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.codeP = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

section
variable {D : Nat} {s : State} (P : PreS pc D s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) := fun a ha =>
  sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by have := P.k2; unfold kk oEm oRsa at *; omega_using [this]) a ha)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega_using [this])

omit P in
theorem psa_subS : Region.Sub (psaR pc s) (kS pc s) := pb_sub s (by have := privBytes_rng pc; cases pc <;> decide)

theorem em_rs : (emR s).Disjoint (rsR s) := by
  obtain h := Offset.disjoint_base (Ss s) (d := oRsa) (n := ((stackArg s 13).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega_using [this]) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega_arith)
  obtain e : emR s = ⟨Ss s, kk s⟩ := by simp only [emR, off, show oEm = 0 from rfl, BitVec.add_zero]
  rw [e]; exact h.symm

theorem out_eq : outR s = oR s := by simp only [outR, oR, kk, P.ok]

omit P in
theorem kD'_sub : Region.Sub ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kS pc s) := by
  have := Offset.sub_base (s.sp - BitVec.ofNat 64 (stackBytes pc)) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
    (k := stackBytes pc) (by have := stackBytes_ge pc; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [this])
  rwa [BitVec.add_zero] at this

theorem preP_at {t : State} {em : List Byte} (A : AtPriv pc s em t) : Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := P.k2
  have hk1 := P.k1
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  have hsp : (callE pc s t).sp = pb pc s := A.sp
  have sp1 := P.sp1
  obtain pr := privBytes_rng pc
  obtain hpbt : (pb pc s).toNat = s.sp.toNat - (256 + privBytes pc) := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes pc)
      (by unfold frameBytes; omega_using [pr])]
    unfold stackBytes Impl.Rsa.PPC64LE.Priv.frameBytes at sp1; unfold frameBytes at *; omega_using [sp1]
  obtain g3 : (callE pc s t).gpr .r3 = s.gpr .r3 := (callE_gpr s t).trans A.r3
  obtain g4 : (callE pc s t).gpr .r4 = s.gpr .r6 := (callE_gpr s t).trans A.r4
  obtain g5 : (callE pc s t).gpr .r5 = s.gpr .r5 := (callE_gpr s t).trans A.r5
  obtain g6 : (callE pc s t).gpr .r6 = s.gpr .r6 := (callE_gpr s t).trans A.r6
  obtain g7 : (callE pc s t).gpr .r7 = s.gpr .r7 := (callE_gpr s t).trans A.r7
  obtain g8 : (callE pc s t).gpr .r8 = s.gpr .r8 := (callE_gpr s t).trans A.r8
  obtain g9 : (callE pc s t).gpr .r9 = off (Ss s) oEm := (callE_gpr s t).trans A.r9
  obtain g10 : (callE pc s t).gpr .r10 = s.gpr .r6 := (callE_gpr s t).trans A.r10
  obtain hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, P.ok]
  obtain hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  obtain hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  obtain hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, emR, kk]
  obtain hP : Rsa.PPC64LE.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]; rfl
  obtain hQ : Rsa.PPC64LE.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]; rfl
  obtain hDP : Rsa.PPC64LE.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]; rfl
  obtain hDQ : Rsa.PPC64LE.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]; rfl
  obtain hQI : Rsa.PPC64LE.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]; rfl
  obtain hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain w11 : (BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)).toNat = (stackArg s 13).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega_using [])]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE pc s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  obtain hA : Rsa.PPC64LE.Priv.aR pc (callE pc s t) = psaR pc s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  obtain hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨s.sp - BitVec.ofNat 64 (stackBytes pc),
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  obtain kD' := kD'_sub (pc := pc) (s := s)
  obtain ka : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 (stackBytes pc), Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨pb pc s + BitVec.ofNat 64 96, if pc then 112 else 96⟩
    rw [pb_base, Offset.add_add]
    cases pc <;> exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  obtain es := em_sub P
  obtain rss := rs_sub P
  have ps : Region.Sub (psaR pc s) (kS pc s) := psa_subS
  obtain s1 := sa 1 (by decide)
  obtain s3 := sa 3 (by decide)
  obtain s5 := sa 5 (by decide)
  obtain s7 := sa 7 (by decide)
  obtain s9 := sa 9 (by decide)
  obtain s11 := sa 11 (by decide)
  simp only [psa] at s1 s3 s5 s7 s9 s11
  obtain wS : (Ss s + BitVec.ofNat 64 oRsa).toNat = (stackArg s 12).toNat + oRsa := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oRsa) (by decide),
      Nat.mod_eq_of_lt (by
        have e : (Ss s).toNat = (stackArg s 12).toNat := rfl
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega_arith)]
  obtain q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE pc s t).sp.toNat := by
    rw [hsp, hpbt]; unfold stackBytes at sp1; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [sp1]
  obtain q2 : (callE pc s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; omega_using []
  have hkk : kk s = (s.gpr .r6).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show callRd pc s = Rsa.PPC64LE.Priv.rdL pc (callE pc s t)
    simp only [Rsa.PPC64LE.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide), psa]
      rfl
  · rw [hO, hS, ← out_eq P]; rfl
  · rw [hO, hN]; exact P.on
  · rw [hO, hE]; exact P.oe
  · rw [hO, hI]; exact P.os.sub_right es
  · rw [hO, hP]; exact P.op
  · rw [hO, hQ]; exact P.oq
  · rw [hO, hDP]; exact P.odp
  · rw [hO, hDQ]; exact P.odq
  · rw [hO, hQI]; exact P.oqi
  · rw [hO, hS]; exact P.os.sub_right rss
  · rw [hO, hA]; exact (P.ko.sub_left ps).symm
  · rw [hN, hS]; exact P.ns.sub_right rss
  · rw [hE, hS]; exact P.es.sub_right rss
  · rw [hI, hS]; exact em_rs P
  · rw [hP, hS]; exact P.ps.sub_right rss
  · rw [hQ, hS]; exact P.qs.sub_right rss
  · rw [hDP, hS]; exact P.dps.sub_right rss
  · rw [hDQ, hS]; exact P.dqs.sub_right rss
  · rw [hQI, hS]; exact P.qis.sub_right rss
  · rw [hS, hA]; exact ((P.ks.sub_left ps).sub_right rss).symm
  · rw [hK, hO]; exact P.ko.sub_left kD'
  · rw [hK, hN]; exact P.kn.sub_left kD'
  · rw [hK, hE]; exact P.ke.sub_left kD'
  · rw [hK, hI]; exact (P.ks.sub_left kD').sub_right es
  · rw [hK, hP]; exact P.kp.sub_left kD'
  · rw [hK, hQ]; exact P.kq.sub_left kD'
  · rw [hK, hDP]; exact P.kdp.sub_left kD'
  · rw [hK, hDQ]; exact P.kdq.sub_left kD'
  · rw [hK, hQI]; exact P.kqi.sub_left kD'
  · rw [hK, hS]; exact (P.ks.sub_left kD').sub_right rss
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; have := P.wo; rw [P.ok] at this; exact this
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10]
    show (Ss s + BitVec.ofNat 64 oEm).toNat + _ ≤ _
    rw [show oEm = 0 from rfl, BitVec.add_zero]
    show (stackArg s 12).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega_using [hk, wS]
  · rw [sa 0 (by decide), s1]; exact P.wp
  · rw [sa 2 (by decide), s3]; exact P.wq
  · rw [sa 4 (by decide), s5]; exact P.wdp
  · rw [sa 6 (by decide), s7]; exact P.wdq
  · rw [sa 8 (by decide), s9]; exact P.wqi
  · rw [sa 10 (by decide), s11, w11]; simp only [psa]; rw [wS]; have := P.wsc; unfold oRsa; omega_using [hl, this]
  · rw [g6]; exact hk1
  · rw [g6]; exact hk
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact P.e1
  · rw [g8, g6]; exact P.e2
  · rw [s1]; exact P.p1
  · rw [s1, g6]; exact P.p2
  · rw [s3]; exact P.q1
  · rw [s3, g6]; exact P.q2
  · rw [s5, s1]; exact P.h3
  · rw [s9, s1]; exact P.h7
  · rw [s7, s3]; exact P.h5
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega_using [this]

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 13).toNat * 8) :
    Covers [⟨Ss s + BitVec.ofNat 64 d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} {em : List Byte} (A : AtPriv pc s em t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  obtain hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · rw [out_eq P]
      exact Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [P.hwr]; simp))
    · have := cov_sc P (d := oRsa) (n := ((stackArg s 13).toNat - 1024) * 8) (by unfold oRsa; omega_using [hl])
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  obtain hleft : r ∈ rdS pc D s → Covers [r] (rdS pc D s ++ ⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩ ::
      fr s :: s.wr) := fun h => Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp)
  · exact hleft (by simp)
  · have := cov_sc P (d := oEm) (n := kk s) (by have := scLen P; have := P.k2; unfold kk oEm oRsa at *; omega_using [hl, this])
    exact Covers.right fun a n hi => let ⟨r, hr, hc⟩ := this a n hi;
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · exact hleft (by simp)
  · cases pc
    · simp at hp
    · simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact hleft (by simp)
  · exact Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨pb pc s + BitVec.ofNat 64 32, privBytes pc - 32⟩, List.mem_cons_self .., 64, by
        show pb pc s + BitVec.ofNat 64 96 = pb pc s + BitVec.ofNat 64 32 + BitVec.ofNat 64 64
        rw [Offset.add_add], by show 64 + (if pc then 112 else 96) ≤ privBytes pc - 32; cases pc <;> decide⟩)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} {em : List Byte} (A : AtPriv pc s em t) {R : Region} (hd : (kS pc s).Disjoint R)
    (hs : (SC Ss s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaOaep.PPC64LE.bytes_entry A.mem hd hs hl

omit P in
theorem fb_base (s : State) :
    fb s = (s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 (stackBytes pc - frameBytes) := by
  rw [← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by have := stackBytes_ge pc; unfold frameBytes; omega_using []),
    show stackBytes pc - (stackBytes pc - frameBytes) = frameBytes by have := stackBytes_ge pc; unfold frameBytes; omega_using [this]]

/-- The slots of our frame and what the call writes. -/
theorem slot_dis {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ callWr s ++ [below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  obtain pr := privBytes_rng pc
  obtain hk : Region.Sub ⟨fb s + BitVec.ofNat 64 d, 8⟩ (kS pc s) := by
    rw [fb_base, Offset.add_add]
    exact Offset.sub_base _ (by unfold stackBytes; unfold frameBytes at *; omega_using [hd])
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [out_eq P]; exact P.ko.sub_left hk
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have e : below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes =
        ⟨(s.sp - BitVec.ofNat 64 (stackBytes pc)) + BitVec.ofNat 64 0, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
      simp only [below, pb_base, BitVec.add_sub_cancel, BitVec.add_zero]
    rw [e, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using []))
      (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd, pr]) (by decide)

omit P in
/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_at {t : State} {em : List Byte} (P' : PreS true D s) (X : PreXS s) (A : AtPriv true s em t) :
    Rsa.PPC64LE.Priv.PreX (callE true s t) := by
  obtain sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = pb true s := A.sp
  obtain hpbt : (pb true s).toNat = s.sp.toNat - 464 := by
    have sp1 := P'.sp1
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes true) (by decide)]
    rw [stackBytes_true] at sp1; unfold frameBytes; simp only [privBytes, ↓reduceIte]; omega_using [sp1]
  obtain hPre : Rsa.PPC64LE.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.PPC64LE.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  obtain hO : Rsa.PPC64LE.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, callE_gpr s t (r := .r3), callE_gpr s t (r := .r4), A.r3, A.r4, oR, P'.ok]
  obtain hl : 1024 ≤ (stackArg s 13).toNat := by
    have := P'.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  obtain w11 : (BitVec.ofNat 64 ((stackArg s 13).toNat - 1024)).toNat = (stackArg s 13).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 13).isLt; omega_using [])]
  obtain hS : Rsa.PPC64LE.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  obtain hK : Rsa.PPC64LE.Priv.kR (callE true s t) = ⟨s.sp - BitVec.ofNat 64 (stackBytes true),
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P'),
    by rw [hK, hPre]; exact X.kP.sub_left kD'_sub, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr s t (r := .r6), A.r6]; exact X.pl
  · rw [hsp, hpbt]; have := P'.sp2; omega_using []
  · -- `pre`'s values, as the caller's precondition gives them.
    obtain hb := fun {p : Addr} {len : Nat} (hd : (kS true s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
      (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P')) hl
    obtain hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 16) (n := (stackArg s 17).toNat)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [Nat.mul_comm]; exact X.kP.symm
        · rw [Nat.mul_comm]; exact (X.sP.sub_left (sc_sub P')).symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem, callE_gpr s t (r := .r5),
      callE_gpr s t (r := .r6), A.r5, A.r6, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
      sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P'.kn P'.ns.symm (by have := P'.wn; omega_using []), hb P'.kp P'.ps.symm (by have := P'.wp; omega_using []),
      hb P'.kq P'.qs.symm (by have := P'.wq; omega_using [])]
    exact X.hyp rfl

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {u : State} {em : List Byte} (X : pc = true → PreXS s) (A : AtPriv pc s em u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [below (pb pc s) Impl.Rsa.PPC64LE.Priv.frameBytes]) u.mem v.mem ∧
      (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
      Rsa.PPC64LE.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      (Rsa.PPC64LE.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      (Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P A) (preX_at P (X rfl) A)) hc hw
      (fun v hrd hwr hsp' hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp', hf, hpres, hpost⟩

/-- After the private operation. -/
def AfterS (pc : Bool) (s : State) (em : List Byte) (w : State) : Prop :=
  Saves s w ∧ w.rd = s.rd ∧
    (HypS pc s → Spec.Rsa.writtenOutcome w.mem (s.gpr .r3) (kk s) ((w.gpr .r3).setWidth 32) (privOut s em))

omit P in
/-- `writtenOutcome` of a memory with the same octets at `out`. -/
theorem writtenOutcome_lost {m m' : Mem} {out : Addr} {k : Nat} {r r' : BitVec 32} {o : Spec.Rsa.Outcome}
    (hr : r' = r) (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k)
    (h : Spec.Rsa.writtenOutcome m out k r o) : Spec.Rsa.writtenOutcome m' out k r' o := by
  subst hr
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

theorem priv_ok {t : State} (X : pc = true → PreXS s) (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) : WP isa (priv pc) t (AfterS pc s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have hk := P.k2
  obtain pr := privBytes_rng pc
  unfold priv
  refine WP.alloc (by cases pc <;> exact ⟨by decide, by decide, by decide⟩) (by
    rw [hsp]; have := P.sp1
    rw [fb, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes) (by decide)]
    unfold stackBytes at this; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [this]) ?_
  refine WP.seq (WP.mono (privArgs_ok P h hem) fun u A => ?_)
  refine WP.mono (call_priv P X A) fun v ⟨hrd, hwr, hsp', hf, hpres, hpost⟩ mL _ fl => ?_
  -- Whatever the released frame's bytes hold: the saved slots and the output lie apart from it.
  obtain fl' : Frame [PB pc s] v.mem mL := by rw [hsp] at fl; exact fl
  obtain slotPB : ∀ {d : Nat}, d + 8 ≤ frameBytes →
      ∀ r ∈ [PB pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := fun {d} hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨pb pc s, privBytes pc⟩
    rw [pb_base, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [pr]))
      (by unfold stackBytes; unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd, pr])
      (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [pr])
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (Nat.lt_of_lt_of_le hi (by cases pc <;> decide))
  obtain hb := fun {p : Addr} {len : Nat} (hd : (kS pc s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P)) hl
  -- The state after the frame's release.
  obtain fsp : (freed (privBytes pc) v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 (privBytes pc) = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  obtain fwr : (freed (privBytes pc) v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  obtain svs : Spill.Saved (fb s) s.gpr saved mL :=
    (A.sv.frame hf fun p hp r hr => slot_dis P (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr).frame
      fl' fun p hp r hr => slotPB (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr
  obtain lss : mL.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [fl'.readW (Region.contains_self _ _) (slotPB (by decide)) (by decide),
      hf.readW (Region.contains_self _ _) (slot_dis P (by decide)) (by decide)]; exact A.ls
  obtain hbo : Spec.Rsa.bytesAt mL (s.gpr .r3) (kk s) = Spec.Rsa.bytesAt v.mem (s.gpr .r3) (kk s) :=
    List.map_congr_left fun i hi => lost_byte fl' (R := outR s)
      (by rw [out_eq P]; exact (P.ko.sub_left PB_sub).symm) (List.mem_range.mp hi)
  refine ⟨⟨fsp, fwr, fun r hr => ?_, svs, lss⟩, by show v.rd = _; exact hrd.trans A.rd, fun hyp => ?_⟩
  · show v.gpr r = _; rw [hpres r (by revert r; decide)]; exact A.hi r hr
  simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr s u (r := .r3), callE_gpr s u (r := .r5), callE_gpr s u (r := .r6),
    callE_gpr s u (r := .r7), callE_gpr s u (r := .r8), callE_gpr s u (r := .r9), A.r3, A.r5, A.r6, A.r7, A.r8,
    A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide),
    sa 6 (by decide), sa 8 (by decide), psa] at hpost
  rw [A.em, hb P.kn P.ns.symm (by have := P.wn; omega_using []), hb P.ke P.es.symm (by have := P.we; omega_using []),
    hb P.kp P.ps.symm (by have := P.wp; omega_using []), hb P.kq P.qs.symm (by have := P.wq; omega_using []),
    hb (by have := P.kdp; simp only [dpR, P.h3] at this; exact this)
      (by have := P.dps; simp only [dpR, P.h3] at this; exact this.symm) (by have := P.wdp; rw [P.h3] at this; omega_using []),
    hb (by have := P.kdq; simp only [dqR, P.h5] at this; exact this)
      (by have := P.dqs; simp only [dqR, P.h5] at this; exact this.symm) (by have := P.wdq; rw [P.h5] at this; omega_using []),
    hb (by have := P.kqi; simp only [qiR, P.h7] at this; exact this)
      (by have := P.qis; simp only [qiR, P.h7] at this; exact this.symm) (by have := P.wqi; rw [P.h7] at this; omega_using [])]
    at hpost
  exact writtenOutcome_lost rfl hbo hpost

end
end VG.Proof.RsaPss.PPC64LE.Sg

end

end

/-! ### `RsaPss.PPC64LE.Sg.Enc`, which only this module used -/

section

/-! ### `RsaPss.PPC64LE.Sg.EnView`, which only this module used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: the bytes written, as views

Untrusted: everything here is checked by Lean. Pure facts about the views of
our part of `scratch` (`view`): `M'`'s bytes after `mPrime` (`mPrime_bytes`);
`EM` before masking (`emPre`) after `clearEm`, `putSalt` and `putH`
(`emPre_of`); and `EM` after MGF1's mask and `clearTop` is `emT`
(`emT_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Proof.RsaOaep.PPC64LE (off off_off view view_wb view_w8)
open VG.Proof.RsaOaep (mixV range_ext)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss (getD_app)

theorem getD_rep0 (n i : Nat) : (List.replicate n (0 : Byte)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem bytesAt_eq_view (m : Mem) (S : Addr) (d n : Nat) :
    Spec.Rsa.bytesAt m (off S d) n = (List.range n).map fun i => view m S (d + i) := by
  simp only [Spec.Rsa.bytesAt, view]
  exact List.map_congr_left fun i _ => by rw [← off_off]

/-- `M'` after `mPrime`. -/
theorem mPrime_bytes (m : Mem) (S : Addr) {D : Nat} (dig salt : List Byte) (hd : dig.length = D)
    (hl : oY + 8 + D + salt.length ≤ oRsa) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes (writeBytes m (off S oY) (List.replicate 8 0)) (off S (oY + 8)) dig)
      (off S (oY + 8 + D)) salt) (off S oY) (8 + D + salt.length) = Spec.RsaPss.zeros 8 ++ dig ++ salt := by
  rw [bytesAt_eq_view]
  refine range_ext (by simp [Spec.RsaPss.zeros, hd]; omega_using []) fun i hi => ?_
  rw [view_wb _ _ (by omega_using [hl]) (by omega_using [hl, hi]), view_wb _ _ (by rw [hd]; omega_using [hl]) (by omega_using [hl, hi]),
    view_wb _ _ (by simp; omega_using [hl]) (by omega_using [hl, hi]), getD_app, getD_app]
  simp only [List.length_replicate, hd, Spec.RsaPss.zeros, List.length_append, getD_rep0]
  by_cases h1 : i < 8
  · rw [ifn (by omega_using [h1]), ifn (by omega_using [h1]), ifp ⟨by omega_using [], by omega_using [h1]⟩, ifp (by omega_using [h1]), ifp h1]
  by_cases h2 : i < 8 + D
  · rw [ifn (by omega_using [h2]), ifp ⟨by omega_using [h1], by omega_using [h2]⟩, ifp (by omega_using [h2]), ifn h1, show oY + i - (oY + 8) = i - 8 by omega_using []]
  · rw [ifp ⟨by omega_using [h2], by omega_using [hi]⟩, ifn (by omega_using [h2]), show oY + i - (oY + 8 + D) = i - (8 + D) by omega_using [],
      show i - (8 + D) = i - 8 - D by omega_using []]

/-- `EM` before masking, at offset `o < k`: zeros, `0x01`, the salt, `H` and
`0xbc`. -/
def emPre (k D sl : Nat) (salt h : List Byte) (o : Nat) : Byte :=
  if o = k - 1 then 0xbc else if k - D - 1 ≤ o then h.getD (o - (k - D - 1)) 0
  else if k - sl - D - 1 ≤ o then salt.getD (o - (k - sl - D - 1)) 0 else if o = k - sl - D - 2 then 1 else 0

/-- `EM` before masking, from the writes of `clearEm`, `putSalt` and `putH`. -/
theorem emPre_of {m m₁ m₂ m₃ : Mem} {S : Addr} {k D sl : Nat} {salt h : List Byte} (hs : salt.length = sl)
    (hh : h.length = D) (hk : k ≤ 1024) (hfit : sl + D + 2 ≤ k)
    (h₁ : m₁ = writeBytes m (off S oEm) (List.replicate k 0))
    (h₂ : m₂ = writeBytes (m₁.writeW (off S (oEm + (k - sl - D - 2))) (1 : Byte)) (off S (oEm + (k - sl - D - 1)))
      salt)
    (h₃ : m₃ = (writeBytes m₂ (off S (oEm + (k - D - 1))) h).writeW (off S (oEm + (k - 1))) (0xbc : Byte))
    {o : Nat} (ho : o < k) : view m₃ S o = emPre k D sl salt h o := by
  have hE : oEm = 0 := rfl
  have hR : oRsa = 8192 := rfl
  subst h₁ h₂ h₃
  rw [view_w8 _ _ (by omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR]), view_wb _ _ (by rw [hh]; omega_using [hk, hfit, hE, hR]) (by omega_using [hk, ho, hR]),
    view_wb _ _ (by rw [hs]; omega_using [hk, hfit, hE, hR]) (by omega_using [hk, ho, hR]), view_w8 _ _ (by omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR]),
    view_wb _ _ (by simp; omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR])]
  simp only [emPre, hE, Nat.zero_add, hs, hh, List.length_replicate, getD_rep0]
  rcases (by omega_using [ho] : o = k - 1 ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨
      o = k - sl - D - 2 ∨ o < k - sl - D - 2) with h | h | h | h | h <;>
    simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]

/-- `EM` after the mask with `mk` on `DB` (at `lo`, `db` bytes) and its first
byte ANDed with `c`: `emT`. -/
theorem emT_of {k D sl lo db : Nat} (salt h mk : List Byte) (c : Byte) (hh : h.length = D) (hlo : lo ≤ 1)
    (hdb : db = k - lo - D - 1) (hfit : sl + D + 2 ≤ k - lo) {V : Nat → Byte}
    (hV : ∀ o < k, V o = emPre k D sl salt h o) {o : Nat} (ho : o < k) :
    (if o = lo then mixV V mk lo db o &&& c else mixV V mk lo db o) = RsaPss.emT lo db sl salt h mk c o := by
  simp only [RsaPss.emT, mixV, hV o ho, emPre, hh]
  by_cases hol : o < lo
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  -- `k` and `o` by what they exceed, and the bounds as sums: `omega` then splits on no
  -- truncated subtraction.
  obtain ⟨e, rfl⟩ : ∃ e, k = lo + (sl + D + 2 + e) := ⟨k - lo - (sl + D + 2), by omega_using [hfit]⟩
  obtain ⟨t, rfl⟩ : ∃ t, o = lo + t := ⟨o - lo, by omega_using [hol]⟩
  subst hdb
  have e1 : lo + (sl + D + 2 + e) - 1 = lo + (sl + D + 1 + e) := by omega_using []
  have e2 : lo + (sl + D + 2 + e) - D - 1 = lo + (sl + 1 + e) := by omega_using []
  have e3 : lo + (sl + D + 2 + e) - sl - D - 1 = lo + (1 + e) := by omega_using []
  have e4 : lo + (sl + D + 2 + e) - sl - D - 2 = lo + e := by omega_using []
  have e5 : sl + D + 2 + e - D - 1 = sl + 1 + e := by omega_using []
  have e7 : sl + 1 + e - sl = 1 + e := by omega_using []
  have ht : t < sl + D + 2 + e := by omega_using [ho]
  simp only [e1, e2, e3, e4, e5, e7, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.add_left_cancel_iff,
    Nat.add_le_add_iff_left, Nat.add_lt_add_iff_left, Nat.le_add_right, true_and, Nat.add_eq_left, hol,
    ↓reduceIte]
  clear hfit hV ho hol e1 e2 e3 e4 e5 e7
  rcases (by omega_using [ht] : t < e ∨ t = e ∨ (e < t ∧ t < sl + 1 + e) ∨
      (sl + 1 + e ≤ t ∧ t < sl + 1 + e + D) ∨ t = sl + D + 1 + e) with h | h | h | h | h
  · by_cases h0 : t = 0 <;> simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h0 : t = 0 <;> simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: the encoding

Untrusted: everything here is checked by Lean. `signEnc_ok`: after the
checks, `M'` and its hash `H`, `EM`'s writes, MGF1's mask and `clearTop`
leave `encEm` (`Sg/Spec.lean`) at `scratch`, with `Base`, for the private
operation that follows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_wb view_w8 fx hiRegs offs mgfXorT_ok MFit TabS)
open VG.Impl.RsaPss.PPC64LE (MdFns)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.RsaOaep (mixV srcB range_ext map_range_getD')
open VG.Proof.RsaPss.PPC64LE (hashFixedG_ok MdTabS)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreS pc Gs.len s) {H : Hash} (hH : HashOK H)
  (hGl : Gs.len = H.D) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Ss s (stackArg s 15))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Ss s (stackArg s 14))
include P hH hGl hG Tg hGmh hGml hGmv T

theorem signEnc_ok (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State} (E : Entered s t) (sy : t.syms = s.syms)
    (h0 : s.mem (s.gpr .r5) ≠ 0) (hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s) {Q : State → Prop}
    (k : ∀ t', Base Ss vS s t' → t'.syms = s.syms → Spec.Rsa.bytesAt t'.mem (off (Ss s) oEm) (kk s) = encEm Gs Gm s →
      WP isa (priv pc) t' Q) :
    WP isa (signMain H f g pc) t Q := by
  have F := fits P
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hDF := hH.hDF
  have hFD := hH.hFD64
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  obtain ⟨hE, hSt, hDg, _, _, hR⟩ := offs
  have hY : oY = 2560 := rfl
  have hsalt : (saltB s).length = (stackArg s 11).toNat := bytesAt_length _ _ _
  have hhl : (hS Gs s).length = Gs.len := by
    rw [hS, hGh, hH.hashLen, hGl]
  unfold signMain
  -- `M'` and `H`.
  refine WP.seq (WP.mono_syms (mPrime_ok P hGl.symm hD0 hD64 E.base (by omega_using [hfit, hk2])) fun t₁ ⟨b₁, _, m₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hashFixedG_ok F hH T hGl.symm (sl := (stackArg s 11).toNat)
    (by show stackArg s 11 = _; rw [ofNat_toNat]) b₁ (y₁.trans sy) (by omega_using [hfit, hk2])) fun t₂ ⟨⟨b₂, _, _, d₂⟩, y₂⟩ => ?_)
  have hM : Spec.Sha256.bytesAt t₁.mem (off (Ss s) oY) (8 + Gs.len + (stackArg s 11).toNat) =
      Spec.RsaPss.zeros 8 ++ digB Gs.len s ++ saltB s := by
    have := mPrime_bytes t.mem (Ss s) (digB Gs.len s) (saltB s) (bytesAt_length _ _ _) (by rw [hsalt]; omega_using [hfit, hk2, hR, hY])
    rw [hsalt] at this
    rw [m₁]; exact this
  have hh : ∀ i < Gs.len, view t₂.mem (Ss s) (oDig + i) = (hS Gs s).getD i 0 := by
    intro i hi
    have := congrArg (fun l => l.getD i 0) d₂
    simp only [show Spec.Sha256.bytesAt t₂.mem (off (Ss s) oDig) H.FD = Spec.Rsa.bytesAt t₂.mem (off (Ss s) oDig) H.FD
      from rfl, bytesAt_eq_view, map_range_getD' _ (show i < H.FD by omega_using [hGl, hDF, hi]), hM] at this
    rw [this, hS, hGh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega_using [hGl, hi]]
  -- `EM` before masking.
  refine WP.seq (WP.mono_syms (clearEm_ok P b₂) fun t₃ ⟨b₃, _, m₃⟩ y₃ => ?_)
  refine WP.seq (WP.mono_syms (putSalt_ok P hGl.symm hD64 b₃ (by omega_using [hfit])) fun t₄ ⟨b₄, _, m₄⟩ y₄ => ?_)
  have hdig : Spec.Rsa.bytesAt t₄.mem (off (Ss s) oDig) Gs.len = hS Gs s := by
    rw [bytesAt_eq_view]
    refine range_ext hhl fun i hi => ?_
    rw [m₄, view_wb _ _ (by rw [hsalt]; omega_using [hfit, hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]), ifn (by omega_using [hfit, hk2, hE, hDg, hsalt]), view_w8 _ _ (by omega_using [hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]),
      ifn (by omega_using [hk2, hE, hDg]), m₃, view_wb _ _ (by simp; omega_using [hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]), ifn (by simp only [List.length_replicate]; omega_using [hk2, hE, hDg])]
    exact hh i (by omega_using [hi])
  refine WP.seq (WP.mono_syms (putH_ok P hGl.symm hD0 hD64 b₄ (by omega_using [hfit])) fun t₅ ⟨b₅, _, m₅⟩ y₅ => ?_)
  have hpre : ∀ o < kk s, view t₅.mem (Ss s) o = emPre (kk s) Gs.len (stackArg s 11).toNat (saltB s) (hS Gs s) o :=
    fun o ho => emPre_of hsalt hhl hk2 (by omega_using [hfit]) m₃ m₄ (by rw [m₅, hdig]) ho
  -- MGF1 and `clearTop`.
  refine WP.seq (WP.mono_syms (dbArgs_ok P hGl.symm hD64 b₅ h0 (by omega_using [hfit])) fun t₆ ⟨b₆, v₆, x24, x25, x26, x27⟩ y₆ =>
    ?_)
  have hsrc : srcB (view t₆.mem (Ss s)) (oEm + (kk s - Gs.len - 1)) Gs.len = hS Gs s := by
    refine range_ext hhl fun i hi => ?_
    rw [v₆, hpre _ (by omega_using [hfit, hE, hi])]
    simp only [emPre, hE, Nat.zero_add]
    rw [ifn (by omega_using [hfit, hi]), ifp (by omega_using []), show kk s - Gs.len - 1 + i - (kk s - Gs.len - 1) = i by omega_using []]
  refine WP.seq (WP.mono (mgfXorT_ok F hG Tg hGmh hGml hGmv (src := oEm + (kk s - Gs.len - 1)) (srcLen := Gs.len)
    (dst := oEm + loN s) (dstLen := kk s - loN s - Gs.len - 1) ⟨by omega_using [hfit, hk2, hE], by omega_using [hfit, hk2, hE], .inr (by omega_using [hfit]), by omega_using [hfit]⟩
    b₆ (y₆.trans (y₅.trans (y₄.trans (y₃.trans y₂)))) x24 (by rw [x25]) x26 x27) fun t₇ ⟨⟨b₇, v₇⟩, y₇⟩ => ?_)
  refine WP.seq (WP.mono_syms (clearTop_ok P b₇ h0) fun t₈ ⟨b₈, m₈⟩ y₈ => ?_)
  refine k t₈ b₈ (y₈.trans y₇) ?_
  rw [bytesAt_eq_view]
  unfold encEm
  refine List.map_congr_left fun o ho => ?_
  have ho := List.mem_range.mp ho
  rw [m₈, view_w8 _ _ (by omega_using [hl1, hE, hR]) (by omega_using [hk2, hE, hR, ho]), hE, Nat.zero_add, Nat.zero_add]
  have e7 : ∀ x < kk s, view t₇.mem (Ss s) x = mixV (view t₆.mem (Ss s)) (Spec.Mgf1.mgf1 Gm (hS Gs s)
      (kk s - loN s - Gs.len - 1)) (loN s) (kk s - loN s - Gs.len - 1) x := fun x hx => by
    rw [v₇ x (by omega_using [hk2, hSt, hx]), hsrc, hE, Nat.zero_add]
  rw [e7 o ho, e7 (loN s) (by omega_using [hfit])]
  have := emT_of (saltB s) (hS Gs s) (Spec.Mgf1.mgf1 Gm (hS Gs s) (kk s - loN s - Gs.len - 1)) (cS s)
    (k := kk s) (sl := (stackArg s 11).toNat) hhl hl1 rfl (by omega_using [hfit]) (V := view t₆.mem (Ss s))
    (fun x hx => by rw [v₆]; exact hpre x hx) ho
  by_cases hl : o = loN s
  · subst hl; rw [ifp rfl]; rw [ifp rfl] at this; exact this
  · rw [ifn hl]; rw [ifn hl] at this; exact this

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`signOut_zero`), and an encoding too short
for the digest (`chkEm`) or the salt (`chkSalt`: `signOut_long`) write zeros
and return 0; otherwise the encoding (`signEnc_ok`) and the private operation
(`priv_ok`) give `signOut` (`signOut_eq`). `sign_ok`: the function, from
an entry state whose hash function's table holds the index of the code's
sizes, through `byIdx`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore Fns tword)
open VG.Impl.RsaPss.PPC64LE (MdFns byIdx idxs shapeOf)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Saves restore_ok freed_gpr freed_mem TabS)
open VG.Proof.RsaPss.PPC64LE (MdTabS twordA_ok byIdx_ok idxs_certs tab_sub)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only eval_zero eval_nonzero wp_nil)

/-- The result and `out`, from the entry state `s`. -/
def Post (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32) (signOut Gs Gm s))

/-- Before the restores. -/
def Done (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32) (signOut Gs Gm s))

theorem n0_eq {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r5) = 0 := by
  have h : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [n0, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .r5)).isLt; omega_using [])] at this
  simpa using this

theorem n0_ne {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r5) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

/-- The frame's body depends on the hash function only by its digest
length. -/
theorem body_D {H H' : Hash} (hD : H.D = H'.D) (f : MdFns) (g : Fns) (pc : Bool) :
    body H f g pc = body H' f g pc := by
  simp only [body, checks, signMain, mPrime, chkEm, chkSalt, putSalt, putH, dbArgs,
    Impl.RsaPss.PPC64LE.hashFixed, hD]

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreS pc Gs.len s)
include P

theorem fail_done {t : State} (h : Base Ss vS s t) (hv : signOut Gs Gm s = .invalid) :
    WP isa Impl.RsaOaep.PPC64LE.encFail t (Done pc Gs Gm s) :=
  WP.mono (fail_ok P h) fun u ⟨sv, _, h3, hb⟩ => ⟨sv, fun _ => by rw [hv, h3]; exact ⟨rfl, hb⟩⟩

variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Ss s (stackArg s 15))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Ss s (stackArg s 14))
include hH hGh hGl hHv hG Tg hGmh hGml hGmv T

theorem checks_done (X : pc = true → PreXS s) {t : State} (E : Entered s t) (sy : t.syms = s.syms) :
    WP isa (checks H f g pc) t (Done pc Gs Gm s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : H.D ≤ 64 := hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_done P E.base (signOut_zero Gs Gm (by omega_using [hk1]) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  refine WP.seq (WP.mono_syms (chkEm_ok P hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₃.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega_using [hGl, hc]
  have hem : H.D + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega_using [hc]
  refine WP.seq (WP.mono_syms (chkSalt_ok P hD64 E₃ h0 hem) fun t₄ ⟨E₄, r3'⟩ y₄ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₄.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc; simp at hc; omega_using [hGl, hc]
  have hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by rw [r3'] at hc; simp at hc; omega_using [hGl, hem, hc]
  refine signEnc_ok P hH hGl hG Tg hGmh hGml hGmv T hGh E₄ (y₄.trans (y₃.trans sy)) h0 hfit fun t' b' _ hb => ?_
  refine WP.mono (priv_ok P X b' hb) fun u ⟨sv, _, hw⟩ => ⟨sv, fun hy => ?_⟩
  rw [signOut_eq Gs Gm hHv hGmv (by omega_using [hk1]) h0 hfit]
  exact hw hy

theorem body_ok (X : pc = true → PreXS s) {u : State} (hu : Only [.r11, .r12] (allocated frameBytes s) u)
    (sy : u.syms = s.syms) : WP isa (body H f g pc) u fun w => Post pc Gs Gm s (freed frameBytes w) := by
  refine WP.seq (WP.mono_syms (entry_ok P hu) fun t E y => WP.seq (WP.mono
    (checks_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X E (y.trans sy)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hy => ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res hy

/-- `vg_rsa_pss_sign`, from an entry state whose hash function's table holds
the index `i`, whose code is for `H`'s digest length. -/
theorem sign_ok (X : pc = true → PreXS s) {i : Nat}
    (hidx : s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
    (hi : i ∈ idxs) (hD : (shapeOf i).1.D = H.D) : WP isa (signG f g pc) s (Post pc Gs Gm s) := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine WP.alloc (by decide) (by have := P.sp1; have := stackBytes_ge pc; unfold frameBytes; omega_arith) ?_
  show WP isa (.seq (.block (tword .r11 hArg 5 ++ [])) _) _ _
  refine WP.seq (WP.of_syms (twordA_ok (j := hArg) (k := 5) (p := stackArg s 14) (by decide) (by decide)
    ⟨aR pc s, by rw [P.hrd]; simp, in_aR (by decide)⟩
    ((P.ka.sub_left kR_sub).sub_right (in_aR_sub (pc := pc) (by decide))).symm
    rfl ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide) (by decide)⟩
    ((P.kth.sub_left kR_sub).sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm fun u o e => wp_nil fun y => ?_))
  rw [show 8 * 5 = 40 from rfl, hidx] at e
  refine byIdx_ok (D := i) (by omega_using [hi8])
    (F := fun u' => Only [.r11, .r12] (allocated frameBytes s) u' ∧ u'.syms = s.syms ∧
      u'.gpr .r11 = BitVec.ofNat 64 i)
    (fun _ h => h.2.2) (fun u₁ u₂ ⟨o₁, y₁, e₁⟩ o y => ⟨(o₁.trans o).mono, y.trans y₁, by rw [o.get .r11]; exact e₁⟩)
    (fun u' ⟨o', y', _⟩ => ?_) hi (fun x hx => (idxs_certs x hx).1) u ⟨o.mono, y.trans rfl, e⟩
  rw [body_D hD]
  -- The `free` loses the frame's bytes, which lie apart from the output.
  refine WP.mono (body_ok P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X o' y') fun w h mL _ fl =>
    ⟨abiPreserved_lost h.1, fun hy => writtenOutcome_lost rfl ?_ (h.2 hy)⟩
  rw [freed_mem_eq]
  exact List.map_congr_left fun i hi => lost_byte fl (R := outR s)
    (by rw [out_eq P]; exact (P.ko.sub_left (Offset.sub_below _ (by have := stackBytes_ge pc; unfold frameBytes; omega_using [this])
      (by have := stackBytes_ge pc; unfold frameBytes; omega_using [this]))).symm) (List.mem_range.mp hi)

end

end VG.Proof.RsaPss.PPC64LE.Sg
