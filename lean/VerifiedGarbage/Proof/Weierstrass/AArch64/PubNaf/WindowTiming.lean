module

public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-! ### `Weierstrass.AArch64.PubNaf.StepDTiming`, which this module and modules that import it used -/

section

/-!
# Timing of the public NAF's iterations with a given doubling

`stepDRaw_relCT`: an iteration whose doubling does what the field program's
does (`DblSpec`) and is constant-time given `x0` leaks the same trace in two
runs with the same field values, as `stepRaw_relCT` for the field
program's: the doubling's results are those values' doubling in both runs,
and it writes only the loop's slots (`ro_unch`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The read-only slots and the table's keep their numbers through what the
loop writes. -/
theorem ro_unch {K : WinCfg} {size : Nat} (hL : WinLay K size) {base : Addr} {m m' : Mem}
    (hU : Unch base (loopW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) {x : Nat}
    (hx : x ∈ winRo K ++ winTblSlots K) : wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hs : x ∈ winSlots K := by
    simp only [winSlots, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hs; omega_using [hn, this])
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · refine hL.lay.apart x y hs (winOther_mem hy) fun e => ?_
    subst e
    rcases List.mem_append.mp hx with hx | hx
    · exact hL.ro x hx hy
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have ht := hL.tbl _ (List.mem_append_right _ hy)
      have hn0 := hL.n0
      have hi' : 8 * K.M.n * i < 8 * K.M.n * 24 :=
        Nat.mul_lt_mul_of_pos_left (List.mem_range.mp hi) (by omega_using [hn0])
      have h24 : 24 * (8 * K.M.n) = 8 * K.M.n * 24 := Nat.mul_comm _ _
      omega_using [ht, hi']
  · exact hL.lay.tmp x hs

/-- An iteration with the doubling `d`, for the values it computes. -/
theorem stepDRaw_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hone : K.one < C.p) (hc : StepChecks K)
    {d : Prog isa} (hd : DblSpec K C base size d K.R K.D (dblVR K))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) d)
    {P : Point C} {s₀ t₀ : State} (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k)
    (hj : j < 64 * K.M.n + 1) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j + 1))
      (PubNaf.stepD K d)
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E' s t) := by
  have hW := hL.win
  have dec : RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j + 1))
      (.block [decCounter])
      (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
        NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
        CacheOk K C base s ∧ CacheOk K C base t ∧
        s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j) := by
    intro s t ts tt s' t' ⟨⟨E, hp⟩, ss, st, cs, ct, s19, t19⟩ es et
    obtain ⟨_, _, xs, vs, ks⟩ := decCounter_ok s (j := j + 1) (by omega_using []) (by have := hL.n6; omega_using [hj, this]) s19
    obtain ⟨_, _, xt, vt, kt⟩ := decCounter_ok t (j := j + 1) (by omega_using []) (by have := hL.n6; omega_using [hj, this]) t19
    obtain ⟨_, rfl⟩ := Exec.det es xs
    obtain ⟨_, rfl⟩ := Exec.det et xt
    have kc : ∀ r ∈ [Reg.x19], r ∈ nafClob K.M.n := fun r hr => nafClob_mem (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    exact ⟨hc.dec _ _ _ _ _ _ trivial trivial (agree_of hp (s19.trans t19.symm)) es et,
      ⟨E, hp.left.of_keeps ks (by decide), hp.right.of_keeps kt (by decide),
        ks.sp.trans (hp.sp.trans kt.sp.symm)⟩,
      ss.regs hW ks kc (by decide), st.regs hW kt kc (by decide),
      CacheUpTo.ofMem ks.mem cs, CacheUpTo.ofMem kt.mem ct,
      by rw [vs, Nat.add_sub_cancel], by rw [vt, Nat.add_sub_cancel]⟩
  rw [PubNaf.stepD]
  apply RelCT.seq dec
  intro s t ts tt s' t' ⟨⟨E, hp⟩, ss, st, cs, ct, s19, t19⟩ es et
  cases es with
  | seq es₁ es₂ =>
    cases et with
    | seq et₁ et₂ =>
      have hV : ∀ x ∈ dblVR K, x ∈ loopLive K := by
        intro x hx
        simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h | h | h | h <;> subst h <;> simp [loopLive, jacCoords, winRo]
      have he₁ := hct _ _ _ _ _ _ trivial trivial hp.public es₁ et₁
      -- Each run's state after the doubling.
      have side : ∀ {a a' : State} {ta : List Leak} {a₀ : State}, Exec isa d a ta a' →
          Inv K.M base size C.p (· ∈ winSlots K) (loopLive K) E a → NSt K C base size P a₀ a →
          CacheOk K C base a → a.gpr .x19 = BitVec.ofNat 64 j →
          NSt K C base size P a₀ a' ∧ CacheOk K C base a' ∧ a'.gpr .x19 = BitVec.ofNat 64 j ∧
          Unch base (loopW K) a.mem a'.mem ∧ ∃ E' : Nat → Fe C,
            Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ dblVR K) E' a' ∧
            (E' K.D.x, E' K.D.y, E' K.D.z) =
              (runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S K.R K.R K.D y)) 6,
                runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S K.R K.R K.D y)) 7,
                runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S K.R K.R K.D y)) 8) := by
        intro a a' ta a₀ ea ia sa ca xa
        obtain ⟨_, _, xa', ka, Ua, E', Ia, va⟩ := hd E a (ia.sub hV)
        obtain ⟨_, rfl⟩ := Exec.det ea xa'
        have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
          (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
        exact ⟨sa.next hW Ia.scr (ka.mono fun _ h => List.mem_cons_of_mem _ (winSaved_combClob h)) Ua,
          CacheOk.unch hW hL.cache ca Ua sa.scr.nowrap, (ka.gpr _ n19).trans xa, Ua, E', Ia, va⟩
      obtain ⟨ss₁, cs₁, s19₁, Us, E₁, I₁, v₁⟩ := side es₁ hp.left ss cs s19
      obtain ⟨st₁, ct₁, t19₁, Ut, E₂, I₂, v₂⟩ := side et₁ hp.right st ct t19
      have v : (E₂ K.D.x, E₂ K.D.y, E₂ K.D.z) = (E₁ K.D.x, E₁ K.D.y, E₁ K.D.z) := v₂.trans v₁.symm
      simp only [Prod.mk.injEq] at v
      -- Both runs hold the same values in the digit's slots.
      let E' : Nat → Fe C := fun x => if x ∈ [K.D.x, K.D.y, K.D.z] then E₁ x else E x
      have hro : ∀ x ∈ digitLive K, x ∉ [K.D.x, K.D.y, K.D.z] → x ∈ winRo K ++ winTblSlots K := by
        intro x hx hn
        simp only [digitLive, jacCoords, List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ hx
        · exact absurd hx hn
      have hloop : ∀ x ∈ winRo K ++ winTblSlots K, x ∈ loopLive K := by
        intro x hx
        simp only [loopLive, List.mem_append] at hx ⊢
        exact Or.inl hx
      have inv : ∀ {a a' : State} {Ea : Nat → Fe C}, Inv K.M base size C.p (· ∈ winSlots K) (loopLive K) E a →
          Unch base (loopW K) a.mem a'.mem →
          Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ dblVR K) Ea a' →
          (∀ x ∈ [K.D.x, K.D.y, K.D.z], Ea x = E₁ x) →
          Inv K.M base size C.p (· ∈ winSlots K) (digitLive K) E' a' := by
        intro a a' Ea ia Ua Ia hEa
        refine ⟨Ia.scr, Ia.mod, digitLive_slots K, fun x hx => ?_, fun x hx => ?_⟩
        · by_cases hD : x ∈ [K.D.x, K.D.y, K.D.z]
          · exact Ia.lt x (List.mem_append_left _ hD)
          · rw [ro_unch hW Ua ia.scr.nowrap (hro x hx hD)]
            exact ia.lt x (hloop x (hro x hx hD))
        · by_cases hD : x ∈ [K.D.x, K.D.y, K.D.z]
          · simp only [E', hD, ↓reduceIte]
            rw [← hEa x hD]
            exact Ia.val x (List.mem_append_left _ hD)
          · simp only [E', hD, ↓reduceIte]
            rw [ro_unch hW Ua ia.scr.nowrap (hro x hx hD)]
            exact ia.val x (hloop x (hro x hx hD))
      have pair₁ : FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E' _ _ :=
        ⟨inv hp.left Us I₁ (fun _ _ => rfl), inv hp.right Ut I₂ (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          exacts [v.1, v.2.1, v.2.2]),
          (Exec.rdwr es₁).2.2.trans (hp.sp.trans (Exec.rdwr et₁).2.2.symm)⟩
      obtain ⟨he₂, E'', pair₂⟩ := digit_relCT hL hm hone hc.digit hF₁ hF₂ hj
        _ _ _ _ _ _ ⟨pair₁, ss₁, st₁, cs₁, ct₁, s19₁, t19₁⟩ es₂ et₂
      refine ⟨by rw [he₁, he₂], E'', pair₂.sub fun x hx => ?_⟩
      simp only [loopLive, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hx))
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hx))
      · exact List.mem_append_left _ hx

end VG.Proof.Weierstrass.AArch64.PubNaf

end

end

/-! ### `Weierstrass.AArch64.PubNaf.TableTiming`, which only this module used -/

section

/-!
# Timing of the public NAF's table

From two runs with the same values of `P` and of the slots read only, the
table's construction leaks the same trace and leaves the same values in the
table (`table_relCT`): the stores' addresses are public (`x20`), and the
co-Z programs do not branch.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `R` into entry `m + 1`, with `R`'s values. -/
theorem storeFields_ok {K : WinCfg} {base : Addr} {size m : Nat} {C : Curve}
    (hL : NafLay K size) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hm : m < 8)
    (h20 : s.gpr .x20 = off base (stride K * m)) (hR : ∀ x ∈ jacCoords K.R, x ∈ V) :
    WP isa (.block (store K)) s fun t =>
      ProgKeep K.M base (jacCoords (K.tblPt (m + 1))) s t ∧
      Inv K.M base size C.p (· ∈ winSlots K) (jacCoords (K.tblPt (m + 1)) ++ V) (tmv C K.M.n base t) t ∧
      (tmv C K.M.n base t (K.tblPt (m + 1)).x, tmv C K.M.n base t (K.tblPt (m + 1)).y,
        tmv C K.M.n base t (K.tblPt (m + 1)).z) = (E K.R.x, E K.R.y, E K.R.z) := by
  have hW := hL.win
  refine WP.mono (store_ok hL hI.scr hm h20) fun t ⟨cw, kt, Ut⟩ => ?_
  have ex : wordsVal t.mem base (K.tblPt (m + 1)).x K.M.n = wordsVal s.mem base K.R.x K.M.n := by
    have := cw 0 (by decide); rw [tblPt_x]; simpa using this
  have ey : wordsVal t.mem base (K.tblPt (m + 1)).y K.M.n = wordsVal s.mem base K.R.y K.M.n := by
    have := cw 1 (by decide); rw [tblPt_y, hL.rxy]; simpa using this
  have ez : wordsVal t.mem base (K.tblPt (m + 1)).z K.M.n = wordsVal s.mem base K.R.z K.M.n := by
    have := cw 2 (by decide)
    rw [tblPt_z, hL.rxz, show K.R.x + 16 * K.M.n = K.R.x + 8 * K.M.n * 2 by omega_arith]
    simpa using this
  have kp : ProgKeep K.M base (jacCoords (K.tblPt (m + 1))) s t := by
    refine ⟨fun r hr => kt.gpr r (fun h => hr (by
        simp only [List.mem_singleton] at h; subst h; simp [clob])), kt.rd, kt.wr, kt.sp,
      fun x hx _ => Ut x (fun w hw => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx _ (by simp [jacCoords])
    · exact hx _ (by simp [jacCoords])
    · exact hx _ (by simp [jacCoords])
  have hlt : ∀ x ∈ jacCoords (K.tblPt (m + 1)), wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact hI.lt _ (hR _ (by simp [jacCoords]))
    · rw [ey]; exact hI.lt _ (hR _ (by simp [jacCoords]))
    · rw [ez]; exact hI.lt _ (hR _ (by simp [jacCoords]))
  have hTs : ∀ x ∈ jacCoords (K.tblPt (m + 1)), x ∈ winSlots K := fun x hx =>
    tbl_slot (a := m + 1) (by omega_arith) (by omega_arith) x (by simpa [jacCoords] using hx)
  refine ⟨kp, hI.of_progKeep hW.lay kp hTs hlt, ?_⟩
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · show toM _ _ _ = _; rw [ex, hI.val _ (hR _ (by simp [jacCoords]))]
  · show toM _ _ _ = _; rw [ey, hI.val _ (hR _ (by simp [jacCoords]))]
  · show toM _ _ _ = _; rw [ez, hI.val _ (hR _ (by simp [jacCoords]))]

/-- The store into entry `m + 1`, at the public `x20`. -/
theorem store_relCT {K : WinCfg} {base : Addr} {size m : Nat} {C : Curve}
    (hL : NafLay K size) (hm : m < 8) {V : List Nat} {E : Nat → Fe C}
    (hR : ∀ x ∈ jacCoords K.R, x ∈ V)
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x20]))
      (.block (store K))) :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) V E s t ∧
      s.gpr .x20 = off base (stride K * m) ∧ t.gpr .x20 = off base (stride K * m))
      (.block (store K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K)
        (jacCoords (K.tblPt (m + 1)) ++ V) E' s t) := by
  have hW := hL.win
  let F := fun x => if x = (K.tblPt (m + 1)).x then E K.R.x
    else if x = (K.tblPt (m + 1)).y then E K.R.y else E K.R.z
  have hn0 := hW.n0
  have qxy : (K.tblPt (m + 1)).y ≠ (K.tblPt (m + 1)).x := by simp only [WinCfg.tblPt]; omega_arith
  have qxz : (K.tblPt (m + 1)).z ≠ (K.tblPt (m + 1)).x := by simp only [WinCfg.tblPt]; omega_arith
  have qyz : (K.tblPt (m + 1)).z ≠ (K.tblPt (m + 1)).y := by simp only [WinCfg.tblPt]; omega_arith
  apply fieldWrite_relCT (F := F) (W := jacCoords (K.tblPt (m + 1)))
    (Pre := fun s => s.gpr .x20 = off base (stride K * m)) hW.lay hct
  · intro s t hp ps pt
    exact agree_of hp (ps.trans pt.symm)
  · exact fun x hx => tbl_slot (a := m + 1) (by omega_arith) (by omega_arith) x (by simpa [jacCoords] using hx)
  · intro x hx; exact List.mem_append.mp hx
  · intro s hi hp
    refine WP.mono (storeFields_ok hL hi hm hp hR) fun t ⟨hk, it, ht⟩ => ⟨_, hk, it, ?_⟩
    intro x _ hx
    simp only [Prod.mk.injEq] at ht
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa only [F, ite_true] using ht.1
    · simpa only [F, qxy, ite_false, ite_true] using ht.2.1
    · simpa only [F, qxz, qyz, ite_false] using ht.2.2

/-- A public control register may be saved and restored inside a called kernel. -/
theorem relCT_keepGprExec {P Q : State → State → Prop} {c : Prog isa} {r : Reg} {v : BitVec 64}
    (h : RelCT isa P c Q) (hk : ∀ {s t tr}, Exec isa c s tr t → t.gpr r = s.gpr r) :
    RelCT isa (fun s t => P s t ∧ s.gpr r=v ∧ t.gpr r=v) c
      (fun s t => Q s t ∧ s.gpr r=v ∧ t.gpr r=v) := by
  intro s t ts tt s' t' ⟨hp,ps,pt⟩ es et
  obtain ⟨he,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨he,hq,(hk es).trans ps,(hk et).trans pt⟩

/-- Timing certificates and semantic preservation of table control registers. -/
structure TableChecks (K : WinCfg) : Prop where
  copyP : FieldCT (.block (copyPt K.M.n K.R K.P))
  ptr : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block [.addImm .x .x20 .x0 0])
  store : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x20]))
    (.block (store K))
  set : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x20]))
    (.block [.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0])
  dblu : FieldCT (fprogB K.M (dbluOps K))
  zaddu : FieldCT (fprogB K.M (zadduOps K))
  bump : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x19, .x20]))
    (.block [.addImm .x .x20 .x20 (stride K), decCounter])
  keepD : ∀ r ∈ [Reg.x19, .x20], ∀ {s t tr}, Exec isa (fprogB K.M (dbluOps K)) s tr t → t.gpr r = s.gpr r
  keep : ∀ r ∈ [Reg.x19, .x20], ∀ {s t tr}, Exec isa (fprogB K.M (zadduOps K)) s tr t → t.gpr r = s.gpr r

/-- The slots the construction reads after `m` entries. -/
def tblLive (K : WinCfg) (m : Nat) : List Nat :=
  winRo K ++ jacCoords K.R ++ [K.E.x, K.E.y] ++ (List.range (3 * m)).map (K.tbl + 8 * K.M.n * ·)

theorem tblLive_succ (K : WinCfg) {m : Nat} :
    ∀ x ∈ tblLive K (m + 1), x ∈ jacCoords (K.tblPt (m + 1)) ++ tblLive K m := by
  intro x hx
  simp only [tblLive, List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact List.mem_append_right _ (by simp only [tblLive, List.mem_append]; exact Or.inl (Or.inl (Or.inl hx)))
  · exact List.mem_append_right _ (by simp only [tblLive, List.mem_append]; exact Or.inl (Or.inl (Or.inr hx)))
  · exact List.mem_append_right _ (by simp only [tblLive, List.mem_append]; exact Or.inl (Or.inr hx))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi := List.mem_range.mp hi
    rcases Nat.lt_or_ge i (3 * m) with h | h
    · exact List.mem_append_right _ (by
        simp only [tblLive, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩))
    · apply List.mem_append_left
      simp only [jacCoords, tblPt_x, tblPt_y, tblPt_z, Nat.add_sub_cancel, List.mem_cons,
        List.not_mem_nil, or_false]
      rcases (show i = 3 * m ∨ i = 3 * m + 1 ∨ i = 3 * m + 2 by omega_arith) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- A co-Z program on the window method's slots, for the values it computes. -/
theorem coZ_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {σ : Nat → Nat} (hσ : Ren K σ) {N : List FOp}
    (hout : ∀ op ∈ N, op.out < 11) {Rd : List Nat} (hR : readsOk N Rd = true) {V : List Nat}
    {E : Nat → Fe C} (hv : ∀ i ∈ Rd, σ i ∈ V) (hct : FieldCT (fprogB K.M (N.map (CoZ.rename σ)))) :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) V E) (fprogB K.M (N.map (CoZ.rename σ)))
      (FieldPair K.M base size C.p (· ∈ winSlots K) (validAfter (N.map (FOp.rename σ)) V)
        (runOps (N.map (FOp.rename σ)) E)) :=
  fieldWP_relCT hct fun _ hi =>
    WP.mono (coZ_ok hL hp hσ hout hR hi hv) fun _ ⟨hk, _, hI, _⟩ => ⟨hI, hk.sp⟩

/-- Storing an entry writes only `x4`. -/
theorem store_dst (K : WinCfg) {r : Reg} (hr : r = .x19 ∨ r = .x20) :
    ∀ i ∈ instrs (.block (store K) : Prog isa), clobbers i r = false := by
  intro i hi
  simp only [store, instrs, List.mem_flatMap, List.mem_range] at hi
  obtain ⟨j, _, hj⟩ := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> rcases hr with rfl | rfl <;> simp [clobbers, dstOf, ld]

/-- Moving to the next entry and counting it. -/
theorem bump_ok {K : WinCfg} {size : Nat} (hL : NafLay K size) (a : State) {j : Nat} (hj : 1 ≤ j)
    (hj' : j < 2 ^ 64) (hb : a.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x20 .x20 (stride K), decCounter]) a
      (fun a' => Keeps [.x20, .x19] a a' ∧
        a'.gpr .x20 = a.gpr .x20 + BitVec.ofNat 64 (stride K) ∧
        a'.gpr .x19 = BitVec.ofNat 64 (j - 1)) := by
  rw [show ([.addImm .x .x20 .x20 (stride K), decCounter] : List Instr) =
    [.addImm .x .x20 .x20 (stride K)] ++ [decCounter] from rfl, WP.block_append_iff]
  have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega_arith
  refine WP.mono (addImm_ok a (d := .x20) (n := .x20) hst) fun a₁ ⟨v₁, k₁⟩ => ?_
  have b₁ : a₁.gpr .x19 = BitVec.ofNat 64 j := (k₁.gpr _ (by decide)).trans hb
  refine WP.mono (decCounter_ok a₁ hj hj' b₁) fun a₂ ⟨v₂, k₂⟩ => ?_
  exact ⟨(k₁.mono (by decide)).trans (k₂.mono (by decide)), (k₂.gpr _ (by decide)).trans v₁, v₂⟩

/-- An iteration of the construction, for the values it computes. -/
theorem tableStepRaw_relCT {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : NafLay K size) (hp : UnitMod C.p (2^(64*K.M.n))) (hc : TableChecks K)
    (hm1 : 1 ≤ m) (hm : m < 8) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K m) E s t) ∧
      s.gpr .x20 = off base (stride K * m) ∧ t.gpr .x20 = off base (stride K * m) ∧
      s.gpr .x19 = BitVec.ofNat 64 (8 - m) ∧ t.gpr .x19 = BitVec.ofNat 64 (8 - m))
      (tableStep K)
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K (m + 1)) E' s t) ∧
        s.gpr .x20 = off base (stride K * (m + 1)) ∧ t.gpr .x20 = off base (stride K * (m + 1)) ∧
        s.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1)) ∧ t.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1))) := by
  have hW := hL.win
  let V' := validAfter (CoZ.zaddu.map (FOp.rename (coZσ K))) (tblLive K m)
  have hV' : ∀ x ∈ tblLive K m, x ∈ V' := fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  have add : RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K m) E s t))
      (fprogB K.M (zadduOps K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) V' E' s t) := by
    apply RelCT.exists_
    intro E
    have hv : ∀ i ∈ [0, 1, 8, 9, 10], coZσ K i ∈ tblLive K m := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [tblLive, coZσ, jacCoords]
    exact (coZ_relCT hL hp (coZσ_ren hW) CoZTable.zaddu_out CoZTable.zaddu_reads hv hc.zaddu).mono
      (fun _ _ h => h) (fun _ _ h => ⟨_, h⟩)
  have add' := relCT_keepGprExec (r := .x19) (v := BitVec.ofNat 64 (8 - m))
    (relCT_keepGprExec (r := .x20) (v := off base (stride K * m)) add (hc.keep .x20 (by simp)))
    (hc.keep .x19 (by simp))
  rw [tableStep]
  refine RelCT.seq (add'.mono (fun _ _ ⟨h, a, b, c, d⟩ => ⟨⟨h, a, b⟩, c, d⟩) (fun _ _ h => h)) ?_
  apply RelCT.block_append
  intro s t ts tt s' t' ⟨⟨⟨E, hp⟩, s20, t20⟩, s19, t19⟩ es et
  cases es with
  | seq es₁ es₂ =>
    cases et with
    | seq et₁ et₂ =>
      have hRv : ∀ x ∈ jacCoords K.R, x ∈ V' :=
        fun x hx => hV' x (by simp only [tblLive, List.mem_append]; exact Or.inl (Or.inl (Or.inr hx)))
      obtain ⟨he₁, E', pair⟩ := store_relCT hL hm hRv hc.store _ _ _ _ _ _ ⟨hp, s20, t20⟩ es₁ et₁
      -- The pointer and the count.
      have s20' := (Exec.gpr (store_dst K (Or.inr rfl)) es₁ (.inr (by decide))).trans s20
      have t20' := (Exec.gpr (store_dst K (Or.inr rfl)) et₁ (.inr (by decide))).trans t20
      have s19' := (Exec.gpr (store_dst K (Or.inl rfl)) es₁ (.inr (by decide))).trans s19
      have t19' := (Exec.gpr (store_dst K (Or.inl rfl)) et₁ (.inr (by decide))).trans t19
      have he₂ := hc.bump _ _ _ _ _ _ trivial trivial (by
        refine ⟨pair.sp, fun r hr => ?_⟩
        simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact pair.left.scr.x0.trans pair.right.scr.x0.symm
        · exact s19'.trans t19'.symm
        · exact s20'.trans t20'.symm) es₂ et₂
      have mem : ∀ {a a' : State} {ta : List Leak}, a.gpr .x19 = BitVec.ofNat 64 (8 - m) →
          a.gpr .x20 = off base (stride K * m) →
          Exec isa (.block [.addImm .x .x20 .x20 (stride K), decCounter]) a ta a' → a'.mem = a.mem ∧
            a'.sp = a.sp ∧ a'.gpr .x0 = a.gpr .x0 ∧ a'.wr = a.wr ∧
            a'.gpr .x20 = off base (stride K * (m + 1)) ∧ a'.gpr .x19 = BitVec.ofNat 64 (8 - (m + 1)) := by
        intro a a' ta h19 h20 ea
        obtain ⟨_, _, xa, ka, v20, v19⟩ := bump_ok hL a (j := 8 - m) (by omega_arith) (by omega_arith) h19
        obtain ⟨_, rfl⟩ := Exec.det ea xa
        refine ⟨ka.mem, ka.sp, ka.gpr _ (by decide), ka.wr, ?_, by rw [v19]; congr 1⟩
        rw [v20, h20]
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        congr 2
      obtain ⟨ms, sps, x0s, wrs, s20'', s19''⟩ := mem s19' s20' es₂
      obtain ⟨mt, spt, x0t, wrt, t20'', t19''⟩ := mem t19' t20' et₂
      refine ⟨by rw [he₁, he₂], ⟨E', ?_⟩, s20'', t20'', s19'', t19''⟩
      have keepI : ∀ {a a' : State}, a'.mem = a.mem → a'.gpr .x0 = a.gpr .x0 → a'.wr = a.wr →
          Inv K.M base size C.p (· ∈ winSlots K) (jacCoords (K.tblPt (m + 1)) ++ V') E' a →
          Inv K.M base size C.p (· ∈ winSlots K) (jacCoords (K.tblPt (m + 1)) ++ V') E' a' :=
        fun hm h0 hw hi => ⟨⟨h0.trans hi.scr.x0, hw ▸ hi.scr.wr, hi.scr.nowrap, hi.scr.enc⟩,
          hm ▸ hi.mod, hi.sl, hm ▸ hi.lt, hm ▸ hi.val⟩
      exact (⟨keepI ms x0s wrs pair.left, keepI mt x0t wrt pair.right,
        sps.trans (pair.sp.trans spt.symm)⟩ : FieldPair _ _ _ _ _ _ _ _ _).sub fun x hx => by
          rcases List.mem_append.mp (tblLive_succ K x hx) with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (hV' x h)

/-- `R = P` into the first entry, and the count of the others. -/
theorem tableInit_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hc : TableChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K) E)
      (.block (copyPt K.M.n K.R K.P ++ ([.addImm .x .x20 .x0 0] : List Instr) ++ store K ++
        ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr)))
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K)
          (jacCoords (K.tblPt (0 + 1)) ++ ([K.R.x, K.R.y, K.R.z] ++ winRo K)) E' s t) ∧
        s.gpr .x20 = off base (stride K * 1) ∧ t.gpr .x20 = off base (stride K * 1) ∧
        s.gpr .x19 = BitVec.ofNat 64 7 ∧ t.gpr .x19 = BitVec.ofNat 64 7) := by
  have hW := hL.win
  -- `R = P`.
  rw [List.append_assoc, List.append_assoc]
  apply RelCT.block_append
  have os : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winSlots K := fun x hx => winOther_mem (R_other K x hx)
  have pv : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx
    rcases mem3 hx with rfl | rfl | rfl <;> simp [winRo]
  refine RelCT.seq (copyPoint_relCT hW.lay hL.al.al os pv hc.copyP) ?_
  -- `x20 = base`.
  rw [← List.singleton_append]
  apply RelCT.block_append
  have ptr := keepsField_relCT (M := K.M) (base := base) (size := size) (m := C.p)
    (Sl := (· ∈ winSlots K)) (pub := [.x0]) (rs := [.x20]) (Pre := fun _ => True)
    (Post := fun a => a.gpr .x20 = off base (stride K * 0)) (by decide) hc.ptr
    (V := [K.R.x, K.R.y, K.R.z] ++ winRo K) (E := copyPointEnv E K.R K.P)
    (fun a b hp _ _ => ⟨hp.sp, fun q hq => pub_x0 hp (Taint.mem_ofRegs.mp hq)⟩)
    (fun a hi _ => WP.mono (addImm_ok a (d := .x20) (n := .x0) (imm := 0) (by decide))
      fun a' ⟨v, k⟩ => ⟨by rw [v, hi.scr.x0]; simp [off], k⟩)
  refine RelCT.seq (ptr.mono (fun _ _ h => ⟨h, trivial, trivial⟩) (fun _ _ h => h)) ?_
  -- Entry 1.
  apply RelCT.block_append
  have hR : ∀ x ∈ jacCoords K.R, x ∈ [K.R.x, K.R.y, K.R.z] ++ winRo K :=
    fun x hx => List.mem_append_left _ hx
  have st := relCT_keepGpr (r := .x20) (v := off base (stride K * 0))
    (store_relCT hL (base := base) (C := C) (m := 0) (by decide) hR hc.store
      (E := copyPointEnv E K.R K.P)) (store_dst K (Or.inr rfl)) (by decide)
  refine RelCT.seq (st.mono (fun _ _ ⟨h, a, b⟩ => ⟨⟨h, a, b⟩, a, b⟩) (fun _ _ h => h)) ?_
  refine RelCT.mono (P := fun (s t : State) => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K)
      (jacCoords (K.tblPt (0 + 1)) ++ ([K.R.x, K.R.y, K.R.z] ++ winRo K))
      E' s t ∧ s.gpr .x20 = off base (stride K * 0) ∧ t.gpr .x20 = off base (stride K * 0))
    ?_ (fun _ _ ⟨⟨E', h⟩, a, b⟩ => ⟨E', h, a, b⟩) (fun _ _ h => h)
  apply RelCT.exists_
  intro E'
  have set := keepsField_relCT (M := K.M) (base := base) (size := size) (m := C.p)
    (Sl := (· ∈ winSlots K)) (pub := [.x0, .x20]) (rs := [.x20, .x19])
    (Pre := fun a => a.gpr .x20 = off base (stride K * 0))
    (Post := fun a => a.gpr .x20 = off base (stride K * 1) ∧ a.gpr .x19 = BitVec.ofNat 64 7)
    (by decide) hc.set (V := jacCoords (K.tblPt (0 + 1)) ++ ([K.R.x, K.R.y, K.R.z] ++ winRo K))
    (E := E')
    (fun a b hp pa pb => agree_of hp (pa.trans pb.symm))
    (fun a _ pa => by
      rw [show ([.addImm .x .x20 .x20 (stride K), .movz .x .x19 7 0] : List Instr) =
        [.addImm .x .x20 .x20 (stride K)] ++ [.movz .x .x19 (BitVec.ofNat 16 7) 0] from rfl,
        WP.block_append_iff]
      have hst : stride K < 4096 := by have := hL.n6; simp only [stride]; omega_arith
      refine WP.mono (addImm_ok a (d := .x20) (n := .x20) hst) fun a₁ ⟨v₁, k₁⟩ => ?_
      refine WP.mono (setCounter_ok a₁ (j := 7) (by decide)) fun a₂ ⟨v₂, k₂⟩ => ?_
      refine ⟨⟨?_, v₂⟩, (k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
      rw [k₂.gpr _ (by decide), v₁, pa]
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2)
  refine (set.mono (fun _ _ ⟨h, a, b⟩ => ⟨h, a, b⟩) ?_)
  intro a b ⟨h, ⟨a20, a19⟩, ⟨b20, b19⟩⟩
  exact ⟨⟨_, h⟩, a20, b20, a19, b19⟩

/-- DBLU, for the values it computes: the slots of the first iteration. -/
theorem dblu_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hp : UnitMod C.p (2^(64*K.M.n))) (hc : TableChecks K) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K)
          (jacCoords (K.tblPt (0 + 1)) ++ ([K.R.x, K.R.y, K.R.z] ++ winRo K)) E s t) ∧
        s.gpr .x20 = off base (stride K * 1) ∧ t.gpr .x20 = off base (stride K * 1) ∧
        s.gpr .x19 = BitVec.ofNat 64 7 ∧ t.gpr .x19 = BitVec.ofNat 64 7)
      (fprogB K.M (dbluOps K))
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K (8 - 7)) E' s t) ∧
        s.gpr .x20 = off base (stride K * (8 - 7)) ∧ t.gpr .x20 = off base (stride K * (8 - 7)) ∧
        s.gpr .x19 = BitVec.ofNat 64 7 ∧ t.gpr .x19 = BitVec.ofNat 64 7) := by
  have hW := hL.win
  let V := jacCoords (K.tblPt (0 + 1)) ++ ([K.R.x, K.R.y, K.R.z] ++ winRo K)
  let ops := CoZ.dblu.map (FOp.rename (dbluσ K))
  have hv : ∀ i ∈ [13, 14, 15], dbluσ K i ∈ V := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [V, winRo, dbluσ]
  have hout : ∀ i ∈ [4, 5, 8, 9, 10], dbluσ K i ∈ ops.map FOp.out := by
    intro i hi
    exact out_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
  have d : RelCT isa (fun s t => ∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) V E s t)
      (fprogB K.M (dbluOps K))
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K 1) E' s t) := by
    apply RelCT.exists_
    intro E
    refine (coZ_relCT hL hp (dbluσ_ren hW) CoZTable.dblu_out CoZTable.dblu_reads hv hc.dblu).mono
      (fun _ _ h => h) (fun _ _ h => ⟨_, h.sub fun x hx => ?_⟩)
    rw [mem_validAfter]
    simp only [tblLive, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact Or.inl (List.mem_append_right _ (List.mem_append_right _ hx))
    · simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      exacts [Or.inr (hout 5 (by simp)), Or.inr (hout 4 (by simp)), Or.inr (hout 10 (by simp))]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      exacts [Or.inr (hout 8 (by simp)), Or.inr (hout 9 (by simp))]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi := List.mem_range.mp hi
      refine Or.inl (List.mem_append_left _ ?_)
      simp only [jacCoords, tblPt_x, tblPt_y, tblPt_z, Nat.add_sub_cancel, List.mem_cons,
        List.not_mem_nil, or_false]
      rcases (show i = 3 * 0 ∨ i = 3 * 0 + 1 ∨ i = 3 * 0 + 2 by omega_arith) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  exact (relCT_keepGprExec (r := .x19) (v := BitVec.ofNat 64 7)
    (relCT_keepGprExec (r := .x20) (v := off base (stride K * 1)) d (hc.keepD .x20 (by simp)))
    (hc.keepD .x19 (by simp))).mono (fun _ _ ⟨h, a, b, c, d⟩ => ⟨⟨h, a, b⟩, c, d⟩)
    (fun _ _ ⟨⟨h, a, b⟩, c, d⟩ => ⟨h, a, b, c, d⟩)

/-- The table's construction, for the values it computes: two runs from the
same values of the slots read only leak the same trace. -/
theorem table_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : NafLay K size) (hp : UnitMod C.p (2^(64*K.M.n))) (hc : TableChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K) E) (table K)
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K 8) E' s t) := by
  let I := fun j s t => 1 ≤ j ∧ j ≤ 7 ∧
    ((∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K (8 - j)) E s t) ∧
      s.gpr .x20 = off base (stride K * (8 - j)) ∧ t.gpr .x20 = off base (stride K * (8 - j)) ∧
      s.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x19 = BitVec.ofNat 64 j)
  have step : ∀ j, RelCT isa (I j) (tableStep K) (fun s t =>
      eval (.nonzero .x .x19) s = eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s = some false →
        ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (tblLive K 8) E' s t) ∧
      (eval (.nonzero .x .x19) s = some true → ∃ n < j, I n s t)) := by
    intro j
    by_cases hj : 1 ≤ j
    · by_cases hj7 : j ≤ 7
      · have e8 : 8 - (8 - j) = j := by omega_arith
        refine (tableStepRaw_relCT (base := base) (C := C) hL hp hc (m := 8 - j) (by omega_arith)
          (by omega_arith)).mono (P' := I j) (fun _ _ h => by rw [e8]; exact h.2.2) ?_
        intro s t ⟨e, s20, t20, s19, t19⟩
        have cn : 8 - (8 - j + 1) = j - 1 := by omega_arith
        rw [cn] at s19 t19
        refine ⟨by simp only [eval, State.read, s19, t19], fun he => ?_, fun he => ?_⟩
        · have hz : j - 1 = 0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j - 1) != 0) = true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : j - 1 < 2 ^ 64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s = some true := by
              change some (s.read .x .x19 != 0) = some true
              rw [read_x, s19, hb]
            rw [htrue] at he; cases he
          have hx : 8 - j + 1 = 8 := by omega_arith
          rw [hx] at e
          exact e
        · have hz : j - 1 ≠ 0 := by
            intro hz; simp only [eval, State.read, s19, hz] at he; cases he
          have hx : 8 - j + 1 = 8 - (j - 1) := by omega_arith
          rw [hx] at e s20 t20
          exact ⟨j - 1, by omega_arith, by omega_arith, by omega_arith, e, s20, t20, s19, t19⟩
      · exact RelCT.of_false (fun _ _ h => hj7 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  rw [table]
  apply RelCT.seq (tableInit_relCT hL hc)
  apply RelCT.seq (dblu_relCT hL hp hc)
  exact (RelCT.loop I step 7).mono (fun _ _ h => ⟨by decide, by decide, h⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64.PubNaf

end

end


/-!
# Timing of the public NAF multiplication

The pieces of the multiplication whose timing taint tracking checks
(`WindowChecks`); the cache of the table's `Z²` and `Z³` (`cache_relCT`)
and `D = O` and the count (`head_relCT`), for the values they set, in two
runs multiplying the same point by the same scalar.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The pieces of the multiplication whose timing taint tracking checks. -/
structure WindowChecks (K : WinCfg) : Prop where
  table : TableChecks K
  cache : FieldCT (cache K)
  infinity : FieldCT (.block (Jacobian.infinity K K.D))
  counter : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block [.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0])
  step : StepChecks K
  finish : FieldCT (finish K)

theorem digitLive_sub (K : WinCfg) :
    ∀ x ∈ digitLive K, x ∈ [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K) := by
  intro x hx
  simp only [digitLive, jacCoords, List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)
  · exact Or.inl hx

/-- The slots read only and the table survive the cache. -/
theorem cache_keep {K : WinCfg} {size : Nat} (hL : NafLay K size) {base : Addr} {m m' : Mem}
    (hU : Unch base (cacheW K ++ loopW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) :
    ∀ x ∈ winRo K ++ winTblSlots K, wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hW := hL.win
  have hC := hL.cache
  intro x hx
  have hs : x ∈ winSlots K := by
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · simp only [winSlots, List.mem_append]; exact Or.inr hx
  refine hU.wordsVal (fun w hw => ?_) (by have := hW.lay.le x hs; omega_using [hn, this])
  rcases List.mem_append.mp hw with hw | hw
  · simp only [cacheW, List.mem_singleton] at hw; subst hw; exact Or.inl (hC.slots x hs)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hW.ro_w hx w (loopW_sub K w hw)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi' := List.mem_range.mp hi
      simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · exact (hW.tbl_apart (List.mem_append_right _ hy) hi').symm
      · exact hW.lay.tmp _ hs

/-- The cache, for the values of the table: the slots read only and the table keep their values. -/
theorem cache_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hc : WindowChecks K) {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E s t ∧
        OddTbl K C base P 8 s ∧ OddTbl K C base P 8 t)
      (cache K) (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E) := by
  apply relCT_of_ct hc.cache (fun s t h => h.1.public)
  intro s t ⟨hp', Ts, Tt⟩
  let F := fun (a : State) (b : State) => Scr b base size ∧ KeepRegs (nafClob K.M.n) a b ∧
    Unch base (cacheW K ++ loopW K) a.mem b.mem ∧ ModOkA K.M size C.p b.mem base ∧
    OddTbl K C base P 8 b ∧ CacheUpTo K C base 8 b
  refine ⟨F s, F t, cacheTo_ok hL hp hp'.left.scr hp'.left.mod Ts 8 (Nat.le_refl _),
    cacheTo_ok hL hp hp'.right.scr hp'.right.mod Tt 8 (Nat.le_refl _), fun s' t' fs ft => ?_⟩
  obtain ⟨ss, ks, Us, Ms, -, -⟩ := fs
  obtain ⟨st, kt, Ut, Mt, -, -⟩ := ft
  have inv : ∀ {a b : State}, Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E a →
      Scr b base size → ModOkA K.M size C.p b.mem base → Unch base (cacheW K ++ loopW K) a.mem b.mem →
      Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E b :=
    fun ia sb mb ub => ⟨sb, mb, ia.sl, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.lt x hx, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.val x hx⟩
  exact ⟨inv hp'.left ss Ms Us, inv hp'.right st Mt Ut, ks.sp.trans (hp'.sp.trans kt.sp.symm)⟩

/-- `D = O` and the count, for the values they set. -/
theorem head_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hone : K.one < C.p) (hc : WindowChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E)
      (.block (Jacobian.infinity K K.D ++
        ([.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0] : List Instr)))
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E' s t) ∧
        s.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n) ∧ t.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) := by
  have hW := hL.win
  have hDs : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winSlots K := fun x hx => winOther_mem (D_other K x hx)
  apply RelCT.block_append
  refine RelCT.seq (infinity_relCT hW.lay hL.al.al hDs hone hc.infinity) ?_
  have cnt := keepsField_relCT (M := K.M) (base := base) (size := size) (m := C.p)
    (Sl := (· ∈ winSlots K)) (V := [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K))
    (E := infinityEnv K.M C.p K.one E K.D) (pub := [.x0]) (rs := [.x19]) (Pre := fun _ => True)
    (Post := fun a => a.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) (by decide) hc.counter
    (fun a b hp _ _ => ⟨hp.sp, fun q hq => pub_x0 hp (Taint.mem_ofRegs.mp hq)⟩)
    (fun a _ _ => setCounter_ok a (j := 64 * K.M.n) (by have := hL.n6; omega_arith))
  exact cnt.mono (fun _ _ h => ⟨h, trivial, trivial⟩)
    (fun _ _ ⟨h, a, b⟩ => ⟨⟨_, h.sub (digitLive_sub K)⟩, a, b⟩)

end VG.Proof.Weierstrass.AArch64.PubNaf
