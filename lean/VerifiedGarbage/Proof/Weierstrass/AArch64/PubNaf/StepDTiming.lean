module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepD
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# Timing of the public NAF's iterations with a given doubling

`stepDRaw_relCT`: an iteration whose doubling does what the field program's
does (`DblSpec`) and is constant-time given `x0` leaks the same trace in two
runs with the same field values, as `stepRaw_relCT` for the field
program's: the doubling's results are those values' doubling in both runs,
and it writes only the loop's slots (`ro_unch`). `stepOfRaw_relCT`, for either.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The doubling a window is given, if any, is constant-time given `x0`. -/
def NafDblCT (dd : Option (Prog isa)) : Prop :=
  ∀ d, dd = some d → ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) d

theorem NafDblCT.none : NafDblCT none := fun _ h => by cases h

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
  refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le x hs; omega)
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
        Nat.mul_lt_mul_of_pos_left (List.mem_range.mp hi) (by omega)
      have h24 : 24 * (8 * K.M.n) = 8 * K.M.n * 24 := Nat.mul_comm _ _
      omega
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
    obtain ⟨_, _, xs, vs, ks⟩ := decCounter_ok s (j := j + 1) (by omega) (by have := hL.n6; omega) s19
    obtain ⟨_, _, xt, vt, kt⟩ := decCounter_ok t (j := j + 1) (by omega) (by have := hL.n6; omega) t19
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

/-- An iteration, with the doubling given, if any, for the values it computes. -/
theorem stepOfRaw_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k j : Nat}
    (hL : NafLay K size) (hm : UnitMod C.p (2^(64*K.M.n))) (hone : K.one < C.p) (hc : StepChecks K)
    {dd : Option (Prog isa)} (hD : NafDblOk K C base size dd) (hT : NafDblCT dd)
    {P : Point C} {s₀ t₀ : State} (hF₁ : NafFixed K C base s₀ P k) (hF₂ : NafFixed K C base t₀ P k)
    (hj : j < 64 * K.M.n + 1) :
    RelCT isa (fun s t => (∃ E, FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E s t) ∧
      NSt K C base size P s₀ s ∧ NSt K C base size P t₀ t ∧
      CacheOk K C base s ∧ CacheOk K C base t ∧
      s.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .x19 = BitVec.ofNat 64 (j + 1))
      (PubNaf.stepOf K dd)
      (fun s t => ∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (loopLive K) E' s t) := by
  cases dd with
  | none => exact stepRaw_relCT hL hm hone hc hF₁ hF₂ hj
  | some d => exact stepDRaw_relCT hL hm hone hc (hD d rfl) (hT d rfl) hF₁ hF₂ hj

end VG.Proof.Weierstrass.AArch64.PubNaf
