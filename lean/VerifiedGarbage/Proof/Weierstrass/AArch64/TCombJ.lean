import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJFirst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJOut

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

theorem combJLoop_ok {arithmetic : Mod → List FOp → Prog isa} {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    (hcompiler : FieldCompilerCorrect arithmetic size) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {s : State}
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s 1) :
    WP isa (.loop (K.stepJWith arithmetic) (.nonzero .x .x4)) s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' K.J := by
  have hJ2 := hB.J2
  refine WP.loop (M:=isa) (fun r s' => 1≤r ∧ r≤K.J-1 ∧
    TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (K.J-r))
    (fun r s' ⟨hr,hrJ,hi⟩ => ?_) (K.J-1) s ⟨by omega,by omega,by simpa [show K.J-(K.J-1)=1 by omega] using hI⟩
  refine WP.mono (stepJWith_ok hL hA hcompiler hJenc hC hM3 hG hV hpn hb1 hB hk hF
    (j:=K.J-r) (by omega) (by omega) hi) fun t ⟨ht,hx⟩ => ?_
  have hz : (t.read .x .x4 != 0)=decide (r-1≠0) := by
    rw [read_x,hx]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,BitVec.sub_eq_iff_eq_add]
    have eqn : BitVec.ofNat 64 (K.J-r+1)=BitVec.ofNat 64 K.J ↔ K.J-r+1=K.J := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : K.J-r+1<2^64),
          Nat.mod_eq_of_lt (by omega : K.J<2^64)] using this
      · exact congrArg (BitVec.ofNat 64)
    change (¬BitVec.ofNat 64 (K.J-r+1) = (0#64) + BitVec.ofNat 64 K.J) ↔ ¬r-1=0
    rw [BitVec.zero_add, eqn]
    omega
  by_cases hr1 : r-1=0
  · refine Or.inl ⟨?_,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz,hr1]; rfl
    · simpa only [show K.J-r+1=K.J by omega] using ht
  · refine Or.inr ⟨?_,r-1,by omega,by omega,by omega,?_⟩
    · show some (t.read .x .x4 != 0)=some true
      rw [hz,decide_eq_true hr1]
    · simpa only [show K.J-(r-1)=K.J-r+1 by omega] using ht

/-- `[k]G` into `A`, in projective coordinates, for `k < kmax` (`BoothOk`)
whose bits are the table at `K.bits`; only `tcombClob` and `tcombW` change. -/
theorem tcombJWith_ok {arithmetic : Mod → List FOp → Prog isa} {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    (hcompiler : FieldCompilerCorrect arithmetic size) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (K.combJWith arithmetic) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧ Unch base (tcombW K) s.mem s'.mem ∧
      ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hJ2 := hB.J2
  have hw := hL.w
  have hn0 := hM.n0
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hNZ : NeZero C.p := ⟨by omega⟩
  unfold TCombCfg.combJWith
  refine WP.seq (WP.mono (firstJ_ok hL hA hC hG hV hpn hb1 hs hM hF) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (combJLoop_ok hL hA hcompiler hJenc hC hM3 hG hV hpn hb1 hB hk hF I₁) fun s₂ I₂ => ?_)
  -- `Y = 1` where `Z = 0`.
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [I₂.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega), hF.zero]
  have ayz : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y := by
    have := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb]) (K.A.y, 8 * K.M.n)
      (by simp [combW, combWs, TCombCfg.toComb])
    dsimp only [TCombCfg.toComb] at this; omega
  refine WP.seq (WP.mono (outFix_ok K I₂.scr hn0 (Nat.lt_trans hV.one_lt hpn) (hle _ (by tcomb_mem))
    (hle _ (by tcomb_mem)) (hle _ (by tcomb_mem)) (hA.sl _ (by tcomb_mem)) (hA.sl _ (by tcomb_mem))
    (hA.sl _ (by tcomb_mem)) ayz hz₂) fun s₃ ⟨ey₃, k₃, O₃⟩ => ?_)
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
    simp only [combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      TCombCfg.toComb]; simp)
  have U₃ : Unch base (tcombW K) s.mem s₃.mem := (I₂.unch.trans UA).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact hAyW
  have hM₃ : ModOkA K.M size C.p s₃.mem base := hM.unch U₃ hmoW hn
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
  refine WP.mono (hcompiler K.M base C.p (·∈combSlots K.toComb) hL.comb.lay ⟨hA.sl,hA.mod⟩ hV.unit K.outOps _ _ _ I₃ hS hR)
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
      simp only [combW, combWs, rcbW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false, TCombCfg.toComb]
      rcases hy with rfl | rfl | rfl <;> simp
    · rw [List.mem_singleton.mp h]
      exact List.mem_append_left _ (by simp [combW,TCombCfg.toComb])
  refine ⟨?_, U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hM.unch (U₃.trans U₄ |>.mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h)
      hmoW hn, fun x hx => (hval x hx).2, ?_⟩
  · have hc : ∀ r∈clob K.M.n,r∈tcombClob K.M.n := fun r hr =>
      List.mem_append_right _ (by simp only [combClob,List.mem_cons,List.mem_append]; exact Or.inr hr)
    exact (I₂.keep.trans (k₃.mono fun r hr => tcombClob_sub _ hL.n8 r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp))).trans
      ((⟨P₄.gpr,P₄.rd,P₄.wr,P₄.sp⟩ : KeepRegs (clob K.M.n) s₃ s₄).mono hc)
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

end VG.Proof.Weierstrass.AArch64
