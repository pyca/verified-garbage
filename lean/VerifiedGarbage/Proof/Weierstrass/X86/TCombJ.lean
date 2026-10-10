import VerifiedGarbage.Proof.Weierstrass.X86.TCombJFirst
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJStep
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- `[k]G` into `A`, in projective coordinates, for `k < kmax` (`BoothOk`)
whose bits are the table at `K.bits`; only `powClob` and `tcombW` change. -/
theorem tcombJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hsp : SpOk K.combJ 20) :
    WP isa K.combJ s fun s' => KeepRegs (powClob) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hJ2 := hB.J2
  have hw := hL.w
  have hnn := hL.n
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hNZ : NeZero C.p := ⟨by omega⟩
  have hspS : SpOk K.stepJ 20 := ⟨NoSp.loop hsp.right.left.1, hsp.right.left.2⟩
  unfold TCombCfg.combJ
  refine WP.seq (WP.mono (firstJ_ok hL hC hG hV hpn hb1 hs hM hF hsp.left) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J)
    (Inv := fun r s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s'
      (K.J - r)) (n := K.J - 1)
    (fun r s' h1 h2 hi => WP.mono (stepJ_ok hL hC hM3 hG hV hpn hb1 hB hk hF (j := K.J - r) (by omega)
      (by omega) hi hspS) fun s'' ⟨h, z⟩ => ⟨by rw [show K.J - (r - 1) = K.J - r + 1 by omega]; exact h, by
        rw [z]; congr 1; exact decide_eq_decide.mpr (by omega)⟩)
    (fun s' hi => by rw [Nat.sub_zero] at hi; exact hi) (by omega)
    (by rw [show K.J - (K.J - 1) = 1 by omega]; exact I₁)) fun s₂ I₂ => ?_)
  -- `Y = 1` where `Z = 0`.
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [I₂.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have ayz : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y := by
    have := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb]) (K.A.y, 8 * K.M.n)
      (by simp [combW, combWs, TCombCfg.toComb])
    dsimp only [TCombCfg.toComb] at this; omega
  refine WP.seq (WP.mono (outFix_ok K I₂.scr hnn.1 (Nat.lt_trans hV.one_lt hpn) (hle _ (by tcomb_mem))
    (hle _ (by tcomb_mem)) (hle _ (by tcomb_mem)) ayz hz₂) fun s₃ ⟨ey₃, k₃, O₃⟩ => ?_)
  have hs₃ := I₂.scr.of_keepRegs k₃ (by decide)
  have b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  have ex₃ : wordsVal s₃.mem base K.A.x K.M.n = wordsVal s₂.mem base K.A.x K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by grind)) (b64 _ (by tcomb_mem))
  have ez₃ : wordsVal s₃.mem base K.A.z K.M.n = wordsVal s₂.mem base K.A.z K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by grind)) (b64 _ (by tcomb_mem))
  have UA : Unch base [(K.A.y, 8 * K.M.n)] s₂.mem s₃.mem := O₃.unch
  have hmoW := tcombW_mo hL hM
  have hAyW : (K.A.y, 8 * K.M.n) ∈ tcombW K := List.mem_append_left _ (by
    simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      TCombCfg.toComb]; simp)
  have U₃ : Unch base (tcombW K) s.mem s₃.mem := (I₂.unch.trans UA).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact hAyW
  have hM₃ : ModOkW K.M size C.p s₃.mem base := hM.unch U₃ hmoW (by omega)
  have hlt₃ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₃]; exact I₂.lt _ (by simp)
    · rw [ey₃]; split
      · exact hV.one_lt
      · exact I₂.lt _ (by simp)
    · rw [ez₃]; exact I₂.lt _ (by simp)
  have hSlA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], x ∈ combSlots K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> tcomb_mem
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) [K.A.x, K.A.y, K.A.z] (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, hM₃, hSlA, hlt₃, fun _ _ => rfl⟩
  have hS : ∀ op ∈ K.outOps, ∀ x ∈ op.out :: op.ins, x ∈ combSlots K.toComb := by
    intro op hop x hx
    simp only [TCombCfg.outOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
  have hR : readsOk K.outOps [K.A.x, K.A.y, K.A.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out]
  refine WP.mono (fprog_ok hL.comb.lay (hL.wkOk hV.fn) hV.unit K.outOps I₃ hS hR)
    fun s₄ ⟨P₄, I₄⟩ => ?_
  have hval : ∀ x ∈ [K.A.x, K.A.y, K.A.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps K.outOps (tmv C K.M.n base s₃) x ∧ wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
    have hm : x ∈ validAfter K.outOps [K.A.x, K.A.y, K.A.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₄.val x hm, I₄.lt x hm⟩
  have U₄ : Unch base (tcombW K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      simp only [TCombCfg.outOps, FOp.out, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hy
      refine List.mem_append_left _ ?_
      simp only [combWx, combW, combWs, rcbW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false, TCombCfg.toComb]
      rcases hy with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact List.mem_append_left _ (by simp [combWx, combW, TCombCfg.toComb])
  refine ⟨?_, U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hM.unch (U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h)
      hmoW (by omega), fun x hx => (hval x hx).2, ?_⟩
  · exact (I₂.keep.trans (k₃.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob])).trans
      (Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob)
  · -- The values.
    have e : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₄ x = runOps K.outOps (tmv C K.M.n base s₃) x :=
      fun x hx => (hval x hx).1
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]
    have hxt : K.A.x ≠ K.S.t0 := by grind
    have hzt : K.A.z ≠ K.S.t0 := by grind
    have hxz : K.A.x ≠ K.A.z := by grind
    have hxy : K.A.x ≠ K.A.y := by grind
    have hyt : K.A.y ≠ K.S.t0 := by grind
    have hyz : K.A.y ≠ K.A.z := by grind
    simp only [TCombCfg.outOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
    have hy : tmv C K.M.n base s₃ K.A.y = if tmv C K.M.n base s₂ K.A.z = 0 then 1
        else tmv C K.M.n base s₂ K.A.y := by
      show toM _ _ _ = _
      rw [ey₃]
      by_cases h : wordsVal s₂.mem base K.A.z K.M.n = 0
      · have h' : tmv C K.M.n base s₂ K.A.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
        simp only [h, h', ↓reduceIte]; exact hV.one
      · have h' : tmv C K.M.n base s₂ K.A.z ≠ 0 := fun h0 =>
          h ((toM_eq_zero_iff hV.unit (I₂.lt _ (by simp))).mp h0)
        simp only [h, h', ↓reduceIte]
    have ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s₂ K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [ex₃]
    have ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s₂ K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [ez₃]
    rw [hy, ex, ez]
    have h := InvJ.out hC I₂.rep
    rwa [bpart_top (by omega) (Nat.lt_of_lt_of_le hk hB.kmax), zmul_natCast] at h

end VG.Proof.Weierstrass.X86
