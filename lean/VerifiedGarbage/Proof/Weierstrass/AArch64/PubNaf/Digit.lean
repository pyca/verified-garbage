module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafNeg
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# The public NAF's digits

The entry of a digit's magnitude into `E` (`entry_ok`), negated for a
negative digit (`signedEntry_ok`), and added to `D` into `R`, or `R = D` for
a zero digit (`digit_ok`): from `D = [2 r_{j+1}]P`, `R = [r_j]P`, for the
residuals `r_j` of the recoding (`Naf5.residual`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- Entry `a` (`1 … 8`, in `x2`) into `E`. -/
theorem entry_ok {K : WinCfg} {size : Nat} (hL : NafLay K size) {s : State} {base : Addr} {a : Nat}
    (hs : Scr s base size) (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha1 : 1 ≤ a) (ha8 : a ≤ 8) :
    WP isa (.block (entry K)) s fun t =>
      (∀ c < 3, wordsVal t.mem base (K.E.x + 8 * K.M.n * c) K.M.n =
        wordsVal s.mem base (K.tbl + 8 * K.M.n * (3 * (a - 1) + c)) K.M.n) ∧
      KeepRegs [.x2, .x4, .x16, .x17] s t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hW := hL.win
  have hn0 := hW.n0
  have hst : stride K < 65536 := by have := hL.n6; simp only [stride]; omega
  have hEx : K.E.x ∈ winOther K := by win_in
  have hEz : K.E.z ∈ winOther K := by win_in
  have tx := hW.tbl K.E.x (List.mem_append_right _ hEx)
  have tz := hW.tbl K.E.z (List.mem_append_right _ hEz)
  have ez := hW.lay.le K.E.z (winOther_mem hEz)
  have e8 := hL.al.sl K.E.x (winOther_mem hEx)
  have t8 := tbl8 hL.al
  have hle := tbl_le hW (i := 3 * (a - 1) + 2) (by omega)
  have exz := hL.exz
  have hstr : stride K = 24 * K.M.n := rfl
  rw [exz] at tz ez
  have hm8 : 24 * K.M.n * (a - 1) + 24 * K.M.n ≤ 24 * K.M.n * 8 := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have hmul : 8 * K.M.n * (3 * (a - 1) + 2) = 24 * K.M.n * (a - 1) + 16 * K.M.n := by grind
  rw [entry, WP.block_append_iff]
  refine WP.mono (entryAddr_ok K hs.x0 h2 ha1 hst) fun s₁ ⟨h16, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ldOff_ok (p := stride K * (a - 1)) (o := K.tbl) (dst := K.E.x) (n := 3 * K.M.n) hs₁ h16
    (by omega) e8 t8 (by rw [hstr]; omega) (by rw [hstr]; omega) (3 * K.M.n) (Nat.le_refl _))
    fun t ⟨e, kt, O⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · have := coord_words (n := K.M.n) hc (dst := K.E.x) (src := stride K * (a - 1) + K.tbl) e
    rw [this, k₁.mem]
    congr 1
    rw [hstr]; grind
  · exact ((Keeps.regs k₁).mono (by sub_regs)).trans (kt.mono (by sub_regs))
  · have U := unch_of_outside O
    rw [k₁.mem] at U
    refine U.mono fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [hL.exy]))
    · exact Or.inr (Or.inr (by rw [hL.exz]; congr 1; omega))

theorem E_unch_loopW {K : WinCfg} {base : Addr} {m m' : Mem}
    (h : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] m m') :
    Unch base (loopW K) m m' := h.mono fun w hw => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
  refine Or.inl ⟨w.1, E_other K w.1 (by rcases hw with rfl | rfl | rfl <;> simp), ?_⟩
  rcases hw with rfl | rfl | rfl <;> rfl

/-- The entry of a nonzero digit `j` into `E`: `[d_j]P` (`Naf5.point`). -/
theorem signedEntry_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {P : Point C} {s₀ s : State}
    (h : NSt K C base size P s₀ s) (hF : NafFixed K C base s₀ P k) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h19 : s.gpr .x19 = BitVec.ofNat 64 j)
    (h2 : s.gpr .x2 = (Naf5.byte k j).setWidth 64) (hm0 : Naf5.magnitude k j ≠ 0) :
    WP isa (signedEntry K) s fun t => NSt K C base size P s₀ t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧
      (∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal t.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y) (tmv C K.M.n base t K.E.z)
        (Naf5.point C P k j) ∧
      (∀ x ∈ winSlots K, x ∉ [K.E.x, K.E.y, K.E.z] →
        wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have hmag := Naf5.magnitude_le k j
  have hodd := (Naf5.magnitude_odd_or_zero k j).resolve_left hm0
  let a := (Naf5.magnitude k j + 1) / 2
  have ha1 : 1 ≤ a := by omega
  have ha8 : a ≤ 8 := by omega
  have ha : 2 * a - 1 = Naf5.magnitude k j := by omega
  rw [signedEntry]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (nafIndex_ok h2) fun u ⟨u2, ku⟩ => ?_
  rw [nafMagnitude_byte] at u2
  have Su := h.regs hW ku (fun r hr => nafClob_mem (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    (by decide)
  refine WP.mono (entry_ok hL Su.scr u2 ha1 ha8) fun v ⟨ev, kv, Uv⟩ => ?_
  have Sv := Su.next hW (Su.scr.of_keepRegs kv (by decide)) (kv.mono fun r hr => nafClob_mem (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp)) (E_unch_loopW Uv)
  -- `E` is entry `a`.
  obtain ⟨tl, tJ⟩ := Su.tbl a ha1 ha8
  have eEx : wordsVal v.mem base K.E.x K.M.n = wordsVal u.mem base (K.tblPt a).x K.M.n := by
    have := ev 0 (by decide); rw [tblPt_x]; simpa using this
  have eEy : wordsVal v.mem base K.E.y K.M.n = wordsVal u.mem base (K.tblPt a).y K.M.n := by
    have := ev 1 (by decide); rw [tblPt_y, hL.exy]; simpa using this
  have eEz : wordsVal v.mem base K.E.z K.M.n = wordsVal u.mem base (K.tblPt a).z K.M.n := by
    have := ev 2 (by decide)
    rw [tblPt_z, hL.exz, show K.E.x + 16 * K.M.n = K.E.x + 8 * K.M.n * 2 by omega]
    exact this
  have lE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal v.mem base x K.M.n < C.p := by
    intro x hx
    rcases mem3 hx with rfl | rfl | rfl
    · rw [eEx]; exact tl _ (by simp)
    · rw [eEy]; exact tl _ (by simp)
    · rw [eEz]; exact tl _ (by simp)
  have JE : InvJ C (tmv C K.M.n base v K.E.x) (tmv C K.M.n base v K.E.y) (tmv C K.M.n base v K.E.z)
      (mul (Naf5.magnitude k j) P) := by
    show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [eEx, eEy, eEz, ← ha]
    exact tJ
  have v19 : v.gpr .x19 = BitVec.ofNat 64 j := by
    rw [kv.gpr _ (by decide), ku.gpr _ (by decide), h19]
  have keepE : ∀ x ∈ winSlots K, x ∉ [K.E.x, K.E.y, K.E.z] →
      wordsVal v.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx hxE
    rw [← ku.mem]
    refine Uv.wordsVal (fun w hw => ?_) (by have := hW.lay.le x hx; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hW.lay.apart x _ hx (winOther_mem (E_other K _ (by simp))) (fun e => hxE (by simp [e]))
    · exact hW.lay.apart x _ hx (winOther_mem (E_other K _ (by simp))) (fun e => hxE (by simp [e]))
    · exact hW.lay.apart x _ hx (winOther_mem (E_other K _ (by simp))) (fun e => hxE (by simp [e]))
  -- The sign.
  have hb4 := hL.al.bits4
  have hbits := hW.bits
  have hdig := hL.digits
  apply WP.seq
  refine WP.mono (nafSignRead_ok Sv.scr (by omega) (by omega) v19 (Sv.digits hL hF j hj))
    fun w ⟨w3, kw⟩ => ?_
  rw [nafNegative_byte] at w3
  have Sw := Sv.regs hW kw (fun r hr => nafClob_mem (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by decide)
  have w19 : w.gpr .x19 = BitVec.ofNat 64 j := (kw.gpr _ (by decide)).trans v19
  have tw : ∀ x, tmv C K.M.n base w x = tmv C K.M.n base v x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [kw.mem]
  have lw : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal w.mem base x K.M.n < C.p := by
    rw [kw.mem]; exact lE
  refine WP.ite (Naf5.negative k j) (by
    change some (w.read .x .x3 != 0) = some (Naf5.negative k j)
    rw [read_x, w3]; cases Naf5.negative k j <;> decide) (fun hneg => ?_) (fun hneg => ?_)
  · -- Negate `y`.
    obtain ⟨rol, hz⟩ := Sw.ro hW hF
    have hzs : K.zero ∈ winSlots K := winRo_slots K _ (by simp [winRo])
    let V := [K.E.x, K.E.y, K.E.z, K.zero]
    have hVs : ∀ x ∈ V, x ∈ winSlots K := by
      intro x hx
      simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> subst h
      · exact winOther_mem (E_other K _ (by simp))
      · exact winOther_mem (E_other K _ (by simp))
      · exact winOther_mem (E_other K _ (by simp))
      · exact hzs
    have hVl : ∀ x ∈ V, wordsVal w.mem base x K.M.n < C.p := by
      intro x hx
      simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h <;> subst h
      · exact lw _ (by simp)
      · exact lw _ (by simp)
      · exact lw _ (by simp)
      · exact rol _ (by simp [winRo])
    have I := inv_of Sw.scr Sw.mod hVs hVl
    obtain ⟨-, -, -, -, exy, -, eyz, -⟩ := hW.other_ne
    have hz' : tmv C K.M.n base w K.zero = 0 := by
      show toM _ _ _ = 0; rw [hz]; exact toM_zero _ _
    have JEw : InvJ C (tmv C K.M.n base w K.E.x) (tmv C K.M.n base w K.E.y) (tmv C K.M.n base w K.E.z)
        (mul (Naf5.magnitude k j) P) := by rw [tw, tw, tw]; exact JE
    refine WP.mono (nafNeg_ok hW.lay hL.al.al hp I (fun x hx => hx) exy (Ne.symm eyz) hz' JEw)
      fun t ⟨kt, it, jt⟩ => ?_
    have hU : Unch base (loopW K) w.mem t.mem := kt.unch.mono fun w hw => by
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
      simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · subst hy
        exact Or.inl ⟨_, E_other K _ (by simp), rfl⟩
      · exact Or.inr rfl
    have St := Sw.next hW it.scr ((⟨kt.gpr, kt.rd, kt.wr, kt.sp⟩ : KeepRegs (clob K.M.n) w t).mono
      clob_nafClob) hU
    refine ⟨St, (kt.gpr _ (x19_not_clob _)).trans w19, fun x hx => it.lt x (by
        rcases mem3 hx with rfl | rfl | rfl <;> simp [V]), ?_, fun x hx hxE => ?_⟩
    · have := it.point_tmv (p := K.E) (fun x hx => by rcases mem3 hx with rfl | rfl | rfl <;> simp [V]) jt
      simp only [Naf5.point, hneg, ↓reduceIte]; exact this
    · rw [← keepE x hx hxE, ← kw.mem]
      refine kt.unch.wordsVal (fun w' hw => ?_) (by have := hW.lay.le x hx; omega)
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · subst hy
        exact hW.lay.apart x _ hx (winOther_mem (E_other K _ (by simp))) (fun e => hxE (by simp [e]))
      · exact hW.lay.tmp x hx
  · apply WP.block_nil
    refine ⟨Sw, w19, lw, ?_, fun x hx hxE => ?_⟩
    · rw [tw, tw, tw]; simp only [Naf5.point, hneg, Bool.false_eq_true, ↓reduceIte]; exact JE
    · rw [kw.mem]; exact keepE x hx hxE

theorem byteTest : ∀ b : BitVec 8,
    (b.setWidth 64 != 0) = decide (nafMagnitude b ≠ 0) := by decide +kernel

/-- What a digit's step keeps of `s₀`: the loop's state and `x19`, and `R = [e]P`. -/
structure NInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State)
    (j e : Nat) : Prop where
  st : NSt K C base size P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  rlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  r : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul e P)

/-- `R = D + [d_j]P`, from `D = [2 r_{j+1}]P`: `R = [r_j]P`. -/
theorem digit_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ s : State}
    (h : NSt K C base size P s₀ s) (hF : NafFixed K C base s₀ P k) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h19 : s.gpr .x19 = BitVec.ofNat 64 j)
    (Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s.mem base x K.M.n < C.p)
    (DJ : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y) (tmv C K.M.n base s K.D.z)
      (mul (2 * Naf5.residual k (j + 1)) P)) :
    WP isa (PubNaf.digit K) s fun t => NInv K C base size P s₀ t j (Naf5.residual k j) := by
  have hW := hL.win
  have hn := h.scr.nowrap
  have hb4 := hL.al.bits4
  have hbits := hW.bits
  have hdig := hL.digits
  have h10 : K.M.n < 10 := by have := hL.n6; omega
  obtain ⟨-, a2, -, a4, -, -, -, -⟩ := rcbApart_naf hW
  have sD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (D_other K x hx)
  have sE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (E_other K x hx)
  rw [PubNaf.digit]
  apply WP.seq
  refine WP.mono (nafRead_ok h.scr (by omega) (by omega) h19 (h.digits hL hF j hj) .x2)
    fun u ⟨u2, ku⟩ => ?_
  have Su := h.regs hW ku (fun r hr => nafClob_mem (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
    (by decide)
  have u19 : u.gpr .x19 = BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans h19
  have tu : ∀ x, tmv C K.M.n base u x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [ku.mem]
  have Dlu : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal u.mem base x K.M.n < C.p := by rw [ku.mem]; exact Dl
  have DJu : InvJ C (tmv C K.M.n base u K.D.x) (tmv C K.M.n base u K.D.y) (tmv C K.M.n base u K.D.z)
      (mul (2 * Naf5.residual k (j + 1)) P) := by rw [tu, tu, tu]; exact DJ
  have rol := (Su.ro hW hF).1
  refine WP.ite (decide (Naf5.magnitude k j ≠ 0)) (by
    change some (u.read .x .x2 != 0) = _
    rw [read_x, u2, byteTest, nafMagnitude_byte]) (fun hnz => ?_) (fun hz => ?_)
  · have hm0 : Naf5.magnitude k j ≠ 0 := of_decide_eq_true hnz
    apply WP.seq
    refine WP.mono (signedEntry_ok hL hp Su hF hj u19 u2 hm0) fun v ⟨Sv, v19, El, EJ, keepE⟩ => ?_
    -- `D` survives the entry.
    have Dv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal v.mem base x K.M.n = wordsVal u.mem base x K.M.n := by
      intro x hx
      refine keepE x (winOther_mem (D_other K x hx)) fun hE => ?_
      have := hW.other_ne
      obtain ⟨-, -, -, -, -, -, -, hEn, -, -⟩ := this
      exact hEn x hE (List.mem_cons_of_mem _ (by
        rcases mem3 hx with rfl | rfl | rfl <;> simp [rcbW]))
    have tv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base v x = tmv C K.M.n base u x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [Dv x hx]
    let V := winRo K ++ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]
    have hVs : ∀ x ∈ V, x ∈ winSlots K := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h | h | h | h <;> subst h <;> win_in
    have hVl : ∀ x ∈ V, wordsVal v.mem base x K.M.n < C.p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (Sv.ro hW hF).1 x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h' | h' | h' | h' | h' | h' <;> subst h'
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · rw [Dv _ (by simp)]; exact Dlu _ (by simp)
        · exact El _ (by simp)
        · exact El _ (by simp)
        · exact El _ (by simp)
    have hRV : ∀ x ∈ rcbR K.S K.D K.E, x ∈ V := by
      intro x hx
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
    have sl := winJ_sl (o := K.R) (p := K.D) (q := K.E) (R_other K) sD sE
    have DJv : InvJ C (tmv C K.M.n base v K.D.x) (tmv C K.M.n base v K.D.y) (tmv C K.M.n base v K.D.z)
        (mul (2 * Naf5.residual k (j + 1)) P) := by
      rw [tv _ (by simp), tv _ (by simp), tv _ (by simp)]; exact DJu
    refine WP.mono (jacAddB_ok hW.lay hL.al.al hL.n4 hp hC hM3 a2 sl.1 (hL.al.low sl.2.2)
      (inv_of Sv.scr Sv.mod hVs hVl) hRV hone (hC.onCurve_mul hP _) (Naf5.onCurve_point hC hP k j)
      DJv EJ) fun t ht => ?_
    obtain ⟨sct, kt, Ut, Mt, rlt, rJ, -, -⟩ := jacPost_frame hW Sv.scr Sv.mod (Or.inl rfl) ht
    rw [Naf5.add_step hC hP k j] at rJ
    exact ⟨Sv.next hW sct (kt.mono clob_nafClob) Ut, (kt.gpr _ (x19_not_clob _)).trans v19, rlt, rJ⟩
  · have hm0 : Naf5.magnitude k j = 0 := by simpa only [ne_eq, not_not] using of_decide_eq_false hz
    have he : Naf5.residual k j = 2 * Naf5.residual k (j + 1) := by
      have hh := Naf5.recurrence k j
      rw [hm0] at hh
      split at hh <;> omega
    -- `R = D`.
    have a4' : RcbApart K.S K.D K.D K.R := by
      obtain ⟨-, a2', -, -, -, -, -, -⟩ := rcbApart_naf hW
      exact ⟨a2'.nodup, fun x hx => a2'.apart x (rcbR_self_mem _ _ _ hx)⟩
    let V := winRo K ++ [K.D.x, K.D.y, K.D.z]
    have hVs : ∀ x ∈ V, x ∈ winSlots K := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact winRo_slots K x hx
      · exact winOther_mem (D_other K x hx)
    have hVl : ∀ x ∈ V, wordsVal u.mem base x K.M.n < C.p := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact rol x hx
      · exact Dlu x hx
    have hRV : ∀ x ∈ rcbR K.S K.D K.D, x ∈ V := by
      intro x hx
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
    have sl := winJ_sl (o := K.R) (p := K.D) (q := K.D) (R_other K) sD sD
    refine WP.mono (copyPointJ_ok hW.lay hL.al.al a4' sl.1 (inv_of Su.scr Su.mod hVs hVl) hRV DJu)
      fun t ht => ?_
    obtain ⟨sct, kt, Ut, Mt, rlt, rJ, -, -⟩ := jacPost_frame hW Su.scr Su.mod (Or.inl rfl) ht
    rw [← he] at rJ
    exact ⟨Su.next hW sct (kt.mono clob_nafClob) Ut, (kt.gpr _ (x19_not_clob _)).trans u19, rlt, rJ⟩

/-- An iteration: `D = 2R`, then the digit. -/
theorem step_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) (hone : K.one < C.p)
    {P : Point C} (hP : onCurve C P = true) {s₀ s : State} (hF : NafFixed K C base s₀ P k) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : NInv K C base size P s₀ s (j + 1) (Naf5.residual k (j + 1))) :
    WP isa (PubNaf.step K) s fun t => NInv K C base size P s₀ t j (Naf5.residual k j) := by
  have hW := hL.win
  rw [PubNaf.step]
  refine WP.seq (WP.mono (decCounter_ok s (by omega) (by have := hL.n6; omega) h.x19)
    fun s₁ ⟨x₁, k₁⟩ => ?_)
  have S₁ := h.st.regs hW k₁ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₁.mem]
  obtain ⟨-, -, -, -, a5, -, -, -⟩ := rcbApart_naf hW
  have sR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winRo K ++ winOther K :=
    fun x hx => List.mem_append_right _ (R_other K x hx)
  have sl := winJ_sl (o := K.D) (p := K.R) (q := K.R) (D_other K) sR sR
  let V := winRo K ++ [K.R.x, K.R.y, K.R.z]
  have hVs : ∀ x ∈ V, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · exact winOther_mem (R_other K x hx)
  have hVl : ∀ x ∈ V, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (S₁.ro hW hF).1 x hx
    · rw [k₁.mem]; exact h.rlt x hx
  have hRV : ∀ x ∈ rcbR K.S K.R K.R, x ∈ V := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> simp [V, winRo]
  have RJ₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y) (tmv C K.M.n base s₁ K.R.z)
      (mul (Naf5.residual k (j + 1)) P) := by rw [t₁, t₁, t₁]; exact h.r
  have hd := dblB_ok false hW.lay hL.al.al hp hC hM3 a5 sl.1 (hL.al.low sl.2.2)
    (inv_of S₁.scr S₁.mod hVs hVl) hRV (hC.onCurve_mul hP _) RJ₁
  simp only [Bool.false_eq_true, ite_false] at hd
  refine WP.seq (WP.mono hd fun s₂ h₂ => ?_)
  obtain ⟨sc₂, k₂, U₂, M₂, dl, dJ, -, -⟩ := jacPost_frame hW S₁.scr S₁.mod (Or.inr (Or.inl rfl)) h₂
  rw [hC.add_mul_mul hP, show Naf5.residual k (j + 1) + Naf5.residual k (j + 1) =
    2 * Naf5.residual k (j + 1) by omega] at dJ
  have S₂ := S₁.next hW sc₂ (k₂.mono clob_nafClob) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    rw [k₂.gpr _ (x19_not_clob _), x₁, Nat.add_sub_cancel]
  exact digit_ok hL hp hC hM3 hone hP S₂ hF hj x₂ dl dJ

end VG.Proof.Weierstrass.AArch64.PubNaf
