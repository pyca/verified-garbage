module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifySpec
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts

/-!
# RSASSA-PSS verification on AArch64: the checks

`body_ok`: after the prologue (`AtChk`), the checks of the modulus' first
byte and of the lengths, and either 0 returned or `main_ok`: `x0` is
`verifyOut P.Hs P.Gs s`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_subImm wp_addImm wp_sub wp_lsr wp_orr eval_zero
  eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off loV maskV smear_ok emLen_ok borrow_or expLen_ok)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR fb kb frame_sub setWidth_byte maskV_lt maskV_setWidth in_frame)

/-- `saltFits`, with the salt's length in `x12`. -/
theorem saltFitsR_ok {D : Nat} (hD : D + 2 < 4096) {u : State} {F : Addr} (hsp : u.sp = F)
    (hrH : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 sHLen) 8)
    (hsD : u.mem.readW (F + BitVec.ofNat 64 sHLen) 64 = BitVec.ofNat 64 D) {a : Nat} (ha : D + 2 ≤ a)
    (ha' : a < 2 ^ 32) (h9 : u.gpr .x9 = BitVec.ofNat 64 a) {y : BitVec 64} (h12 : u.gpr .x12 = y) :
    WP isa (.block saltFits) u fun u' => Only [.x9, .x10, .x13] u u' ∧
      u'.gpr .x9 = BitVec.ofNat 64 (a - (D + 2)) ∧ (u'.gpr .x10 != 0) = decide (a - (D + 2) < y.toNat) := by
  unfold saltFits hLen2 ld
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) (by rw [hsp]; exact hrH) fun u₁' o₁' e₁' => ?_
  refine wp_addImm (by decide) fun u₁'' o₁'' e₁'' => wp_sub fun u₂ o₂ e₂ =>
    wp_sub fun u₃ o₃ e₃ => wp_lsr (by decide) fun u₄ o₄ e₄ => wp_lsr (by decide) fun u₅ o₅ e₅ =>
    wp_orr fun u₆ o₆ e₆ => wp_nil ⟨(o₁'.trans (o₁''.trans (o₂.trans (o₃.trans (o₄.trans
      (o₅.trans o₆)))))).mono, ?_, ?_⟩
  · have x13 : u₁''.gpr .x13 = BitVec.ofNat 64 (D + 2) := by
      rw [e₁'', e₁', hsp, hsD, BitVec.ofNat_add_ofNat]
    rw [o₆.get .x9, o₅.get .x9, o₄.get .x9, o₃.get .x9, e₂, o₁''.get .x9, o₁'.get .x9, h9, x13,
      Offset.ofNat_sub_ofNat ha]
  · have h12' : u.gpr .x12 = BitVec.ofNat 64 y.toNat := by rw [h12, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have x13 : u₁''.gpr .x13 = BitVec.ofNat 64 (D + 2) := by
      rw [e₁'', e₁', hsp, hsD, BitVec.ofNat_add_ofNat]
    rw [e₆, o₅.get .x10, e₄, e₃, e₂, o₁''.get .x9, o₁'.get .x9, h9, x13, Offset.ofNat_sub_ofNat ha,
      o₂.get .x12, o₁''.get .x12, o₁'.get .x12, h12', e₅, o₄.get .x12, o₃.get .x12, o₂.get .x12, o₁''.get .x12,
      o₁'.get .x12, h12']
    exact borrow_or (by omega) y.isLt

/-- 0 returned. -/
theorem fail_ok {s t : State} (hm : Mid s t) :
    WP isa verifyFail t fun t' => Mid s t' ∧ (t'.gpr .x0).setWidth 32 = 0 := by
  unfold verifyFail movi
  exact wp_movz fun w o e => wp_nil ⟨⟨by rw [o.sp, hm.sp], by rw [o.rd, hm.rd], by rw [o.wr, hm.wr],
    fun r hr => by rw [o.vcs r hr, hm.v r hr], by rw [o.mem]; exact hm.fr⟩, by rw [e]; rfl⟩

theorem mid_frame {s t t' : State} (hm : Mid s t) {rs : List Reg} (k : Keep rs t t') {d₁ d₂ : Nat}
    (h₁ : 248 ≤ d₁ ∧ d₁ + 8 ≤ 264) (h₂ : 248 ≤ d₂ ∧ d₂ + 8 ≤ 264) {v₁ v₂ : BitVec 64}
    (hmem : t'.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 d₁) v₁).writeW (fb s + BitVec.ofNat 64 d₂) v₂) :
    Mid s t' := by
  refine ⟨k.sp.trans hm.sp, k.rd.trans hm.rd, k.wr.trans hm.wr, fun r hr => (k.vcs r hr).trans (hm.v r hr), ?_⟩
  rw [hmem]
  have f : Frame [⟨fb s + BitVec.ofNat 64 d₁, 8⟩, ⟨fb s + BitVec.ofNat 64 d₂, 8⟩] t.mem
      ((t.mem.writeW (fb s + BitVec.ofNat 64 d₁) v₁).writeW (fb s + BitVec.ofNat 64 d₂) v₂) :=
    ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)
  refine hm.fr.frame f (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by decide) (by omega)

theorem body_ok {hs : List Hash} (c : PdChecked) {K : Nat} {s u : State} (P : Pick hs s)
    (hp : PreV P.H.D K s) (hK : 16 ≤ K) (hcK : c.stack ≤ K) (hu : AtChk s u) :
    WP isa (.ite (.zero .x .x10) verifyFail (seqs [.block smear, emLen,
      .ite (.nonzero .x .x10) verifyFail (seqs [expLen, .block saltFits,
        .ite (.nonzero .x .x10) verifyFail (verifyMain hs c.name c.code)])])) u fun t => Mid s t ∧
      (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut P.Hs P.Gs s then 1 else 0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := P.hH.sizes.DN
  have hN := P.hH.N_le
  have hGl := P.hHl
  have hk : 1 ≤ (s.gpr .x1).toNat := by omega
  have Mu : Mid s u := ⟨hu.sp, hu.rd, hu.wr, hu.v, hu.fr⟩
  have hx10 : u.gpr .x10 = BitVec.ofNat 64 (s.mem (s.gpr .x0)).toNat := by rw [hu.x10, setWidth_byte]
  have hn₀ := (s.mem (s.gpr .x0)).isLt
  have f0 : ∀ {t : State}, Mid s t ∧ (t.gpr .x0).setWidth 32 = 0 → verifyOut P.Hs P.Gs s = false →
      Mid s t ∧ (Cons s → (t.gpr .x0).setWidth 32 = if verifyOut P.Hs P.Gs s then 1 else 0) :=
    fun ⟨m, r⟩ h => ⟨m, fun _ => by rw [h]; exact r⟩
  refine WP.ite _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · -- `n₀ = 0`.
    have h0 : s.mem (s.gpr .x0) = 0 := by
      rw [hx10, beq_iff_eq] at hb
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat hb
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact this
    exact WP.mono (fail_ok Mu) fun t h => f0 h (verifyOut_zero P.Hs P.Gs hk h0)
  have h0 : s.mem (s.gpr .x0) ≠ 0 := fun h => by
    rw [hx10, h] at hb; exact absurd hb (by decide)
  have h0' : (s.mem (s.gpr .x0)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have hsl := verifyOut_short P.Hs P.Gs hk h0
  have hiff := verifyOut_iff P.Hs P.Gs P.hGv hk h0
  have hmz := mask_z hk h0
  generalize hx : (s.mem (s.gpr .x0)).toNat = x at hx10 hn₀ h0' hsl hiff hmz
  have hlo : loV x ≤ 1 := by unfold loV; split <;> omega
  have L := rsa_lay hp hK hu.sp hu.wr hu.x20
  have hsD0 : u.mem.readW (fb s + BitVec.ofNat 64 sHLen) 64 = BitVec.ofNat 64 P.H.D := by
    rw [hu.fr.rs (.x5, sHLen) (by simp [regSlots]), ← hp.dl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hrsl : ∀ {t : State}, t.sp = fb s → t.rd = s.rd → t.wr = ⟨fb s, frameBytes⟩ :: s.wr → ∀ {d : Nat},
      d + 8 ≤ frameBytes → InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) 8 := fun _ hrd hwr _ hd => by
    rw [hrd, hwr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  unfold seqs seqs seqs
  -- `smear` and `emLen`.
  refine WP.seq (WP.mono (smear_ok u (x := x) hn₀ h0' hx10) fun u₁ ⟨O₁, h11⟩ => ?_)
  refine WP.seq (WP.mono (emLen_ok (D := P.H.D) (by omega) (F := fb s) (by rw [O₁.sp, hu.sp]) hn₀ h0'
    (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide)) (by rw [O₁.wr, hu.wr]; exact in_frame s _ (by decide))
    (hrsl (by rw [O₁.sp, hu.sp]) (by rw [O₁.rd, hu.rd]) (by rw [O₁.wr, hu.wr]) (by decide))
    (by rw [O₁.mem]; exact hsD0)
    (k := (s.gpr .x1).toNat) (by rw [O₁.get .x23, hu.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk (by omega) h11)
    fun u₂ ⟨K₂, m₂, x9₂, x10₂⟩ => ?_)
  have M₂ : Mid s u₂ := mid_frame Mu (O₁.keep.trans K₂) (d₁ := sC) (d₂ := sLo) (by decide) (by decide)
    (by rw [m₂, O₁.mem])
  refine WP.ite _ (eval_nonzero _ _) (fun hb₂ => ?_) (fun hb₂ => ?_)
  · -- `emLen < hLen + 2`.
    rw [x10₂, decide_eq_true_eq] at hb₂
    exact WP.mono (fail_ok M₂) fun t h => f0 h (hsl (by rw [hGl]; omega))
  rw [x10₂, decide_eq_false_iff_not] at hb₂
  unfold seqs seqs
  -- The expected salt length, and whether it fits.
  have L₂ : Lay u₂ (fb s) (scr s) := L.congr (K₂.sp.trans O₁.sp) (K₂.wr.trans O₁.wr)
    (by rw [K₂.get .x20, O₁.get .x20])
  refine WP.seq (WP.mono (expLen_ok L₂ (any := anyV s) (sv := stackArg s 1)
    (by rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), O₁.mem]; exact hu.fr.any)
    (by rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), O₁.mem]
        exact hu.fr.sl))
    fun u₃ ⟨O₃, x12₃⟩ => ?_)
  refine WP.seq (WP.mono (saltFitsR_ok (D := P.H.D) (by omega) (F := fb s) (by rw [O₃.sp, K₂.sp, O₁.sp, hu.sp])
    (hrsl (by rw [O₃.sp, K₂.sp, O₁.sp, hu.sp]) (by rw [O₃.rd, K₂.rd, O₁.rd, hu.rd])
      (by rw [O₃.wr, K₂.wr, O₁.wr, hu.wr]) (by decide))
    (by rw [O₃.mem, M₂.fr.rs (.x5, sHLen) (by simp [regSlots]), ← hp.dl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (a := (s.gpr .x1).toNat - loV x) (by omega) (by omega)
    (by rw [O₃.get .x9, x9₂]) x12₃) fun u₄ ⟨O₄, x9₄, x10₄⟩ => ?_)
  have M₄ : Mid s u₄ := ⟨O₄.sp.trans (O₃.sp.trans M₂.sp), O₄.rd.trans (O₃.rd.trans M₂.rd),
    O₄.wr.trans (O₃.wr.trans M₂.wr), fun r hr => (O₄.vcs r hr).trans ((O₃.vcs r hr).trans (M₂.v r hr)),
    O₄.mem ▸ O₃.mem ▸ M₂.fr⟩
  have hsv : (if anyV s = 0 then stackArg s 1 else 0).toNat = (sLenV s).getD 0 := by
    unfold sLenV; split <;> rfl
  rw [hsv] at x10₄
  refine WP.ite _ (eval_nonzero _ _) (fun hb₃ => ?_) (fun hb₃ => ?_)
  · -- The salt does not fit.
    rw [x10₄, decide_eq_true_eq] at hb₃
    exact WP.mono (fail_ok M₄) fun t h => f0 h (hsl (by rw [hGl]; omega))
  rw [x10₄, decide_eq_false_iff_not] at hb₃
  have hm₄ : u₄.mem = (u.mem.writeW (fb s + BitVec.ofNat 64 sC) (maskV x)).writeW (fb s + BitVec.ofNat 64 sLo)
      (BitVec.ofNat 64 (loV x)) := by rw [O₄.mem, O₃.mem, m₂, O₁.mem]
  have gK : ∀ r ∈ [Reg.x19, .x20, .x21, .x23], u₄.gpr r = u.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [O₄.get _ (by decide), O₃.get _ (by decide), K₂.get _ (by decide), O₁.get _ (by decide)]
  have hA : AtMain P.H.D s (loV x) ((maskV x).setWidth 8) u₄ := {
    sp := M₄.sp
    rd := M₄.rd
    wr := M₄.wr
    x9 := x9₄
    x19 := by rw [gK .x19 (by decide), hu.x19]
    x20 := by rw [gK .x20 (by decide), hu.x20]
    x21 := by rw [gK .x21 (by decide), hu.x21]
    x23 := by rw [gK .x23 (by decide), hu.x23]
    v := M₄.v
    mem := by
      rw [hm₄]
      exact (hu.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    fr := M₄.fr
    lo := by rw [hm₄, Mem.readW_writeW_self64]
    c := by
      rw [hm₄, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, ← maskV_setWidth x hn₀] }
  have hfit : P.Hs.len + (sLenV s).getD 0 + 2 ≤ (s.gpr .x1).toNat - loV x := by rw [hGl]; omega
  refine WP.mono (main_ok c P hp hK hcK hA hlo (by omega) hmz (fun ha => ?_)) fun t ⟨m, r⟩ =>
    ⟨m, ?_⟩
  · have : (sLenV s).getD 0 = (stackArg s 1).toNat := by unfold sLenV; rw [ite_eq_left ha]; rfl
    omega
  intro hcons
  rw [hGl] at hiff hfit
  rw [r hcons (verifyOut P.Hs P.Gs s) (hiff hfit)]
  split <;> rfl

end VG.Proof.RsaPss.AArch64.Vfy
