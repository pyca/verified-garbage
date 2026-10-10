import VerifiedGarbage.Proof.Weierstrass.X86.TCombJInvariant
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.CombFrame

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- Advance the public window counter and test whether it reached the end. -/
theorem incCmpEsi_ok (s : State) {j J : Nat} (hj : j + 1 ≤ J) (hJ : J < 2 ^ 31)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 J))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j + 1) ∧ t.zf = some (decide (j + 1 = J)) ∧ CKeeps [.esi] s t := by
  have he : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by rw [BitVec.ofNat_add]; rfl
  have hz : (BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 J == 0) = decide (j + 1 = J) := by
    by_cases h : j + 1 = J
    · rw [h, BitVec.sub_self, decide_eq_true rfl]; rfl
    · rw [decide_eq_false h, beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      have h0 : (0 : BitVec 32).toNat = 0 := rfl
      omega_using [hj, hJ, h, this, h0]
  crun [hb, he, RegUpd.zf_arithFlags, hz]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- An iteration, `1 ≤ j < J`. -/
theorem stepJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j < K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (hsp : SpOk K.stepJ 20) :
    WP isa K.stepJ s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
        s'.zf = some (decide (j + 1 = K.J)) := by
  have hn := hI.scr.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  have hsz : size ≤ 2 ^ 64 := by have := hL.sz; omega_using [this]
  -- The working space of the field calls and the output words: apart from the comb's slots.
  have hX : ∀ x ∈ combWs K.toComb, ∀ w ∈ [(K.wk, 64 * K.M.n), Mont.outW],
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
    intro x hx w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inl (hL.wsl x (combWs_slots _ x hx))
    · have h1 := hle x (combWs_slots _ x hx); have := hL.sz
      exact .inl (by dsimp only [Mont.outW]; omega_using [h1, this])
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  have hNZ : NeZero C.p := ⟨by omega_using [hp0]⟩
  have hsp₀ : s.gpr .esp = s₀.gpr .esp := hI.keep.gpr _ (by decide)
  have hwr₀ : s.wr = s₀.wr := hI.keep.wr
  refine WP.withSp hsp (by rw [hsp₀]; exact hF.sp_lo) ?_
  unfold TCombCfg.stepJ
  refine WP.seq ?_
  have hz : wordsVal s.mem base K.zero K.M.n = 0 := by
    rw [hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  refine WP.mono (tentryJ_ok hL hC hV hpn hI.scr hI.mod hjn hI.esi hb1 (c := true) (Or.inl ⟨rfl, hj⟩)
    hI.bits hz hI.tsym hI.tbl) fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ E₃ => ?_)
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW], w ∈ combWx K := fun w hw =>
    (List.mem_append.mp (show w ∈ combEntryW K.toComb ++ [(K.wk, 64 * K.M.n), Mont.outW] from hw)).elim
      (fun h => List.mem_append_left _ (combEntryW_sub w h)) (fun h => List.mem_append_right _ h)
  have U₁₃ : Unch base (combWx K) s.mem s₃.mem := E₃.unch.mono hEW
  have hmoW := tcombW_mo hL hI.mod
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega_using [hn])
  -- What `A` and the read-only slots hold at `s₃`.
  have hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    hL.comb.wordsVal_entryX hsz hX E₃.unch
  have U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  have hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega_using [hn, this])
  have hSl : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hro _ (by simp [combRo, TCombCfg.toComb])]; exact hF.ro_lt _ (by simp [combRo, TCombCfg.toComb])
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · rw [hAx _ (by simp)]; exact hI.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
    · exact E₃.lt _ (by simp)
  have I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  have hSl' : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq (WP.mono (maddJ_ok hL.comb.lay (hL.wkOk hV.fn) hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄⟩ => ?_)
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  have hs₄ := I₄.scr
  have hb₄ : s₄.gpr .esi = BitVec.ofNat 32 j := by
    rw [P₄.gpr _ esi_not_clob, E₃.keep.gpr _ esi_not_clob, hI.esi]
  have U₄ : Unch base (combWx K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [progW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h | h | h
    · exact Or.inl (Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩)
    · exact Or.inl (Or.inr (by rw [h]; rfl))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- `A` and `E` are not written by the addition.
  have hAE₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := hL.comb.wordsVal_addX hsz hX P₄.unch
  have hbl := hL.bits
  have hz' : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hw := hL.w
  have hnn := hL.n
  -- `D = E` where `A` is `O`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs₄ hnn.1 (hle K.A.z (by tcomb_mem))) fun s₅ ⟨c₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅.keeps (by decide)
  have hsel := fun (x : Nat) (hx : x ∈ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]) =>
    hle x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem)
  refine WP.mono (selPtKeep_ok hs₅ (decide (wordsVal s₄.mem base K.A.z K.M.n ≠ 0)) (by rw [c₅])
    (n := K.M.n) (o := K.D) (a := K.E) hsel
    hL.comb.apart_D hL.comb.apart_DE) fun s₆ ⟨dx₆, dy₆, dz₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  rw [m₅] at dx₆ dy₆ dz₆ O₆
  have UD₆ : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s₄.mem s₆.mem :=
    fun x hx => O₆ x (hx (K.D.x, 8 * K.M.n) (by simp)) (hx (K.D.y, 8 * K.M.n) (by simp))
      (hx (K.D.z, 8 * K.M.n) (by simp))
  have U₆ : Unch base (combWx K) s₄.mem s₆.mem :=
    UD₆.mono fun w hw => List.mem_append_left _ (combSelW_D_sub (K := K.toComb) w hw)
  have hA₆ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => ((hL.comb.wordsVal_selD hsz UD₆ x hx : wordsVal s₆.mem base x K.M.n = wordsVal s₄.mem base x K.M.n).trans
      (hAE₄ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))).trans
      (hAx x hx)
  have hb₆ : s₆.gpr .esi = BitVec.ofNat 32 j := by
    rw [k₆.gpr _ (by decide), k₅.1 _ (by decide), hb₄]
  have hbits₆ : ∀ t < K.w * K.J, s₆.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [(U₁₃.trans (U₄.trans U₆)).byte (fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with h | h | h <;> exact combW_bits hL ht w h)
      (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  have hwi : K.w * j + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  -- The digit again, and `A = D` unless it is zero.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (bdigit_ok K hs₆ (k := k) (j := j) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb1 hb₆ hbits₆ (Or.inl ⟨rfl, hj⟩)) fun s₇ ⟨_, r₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇.keeps (by decide)
  have hmag : bmag K.w k j ≤ 128 := by
    have := bmag_le hw.1 k j
    exact Nat.le_trans this (Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₇ (v := 0) (a := bmag K.w k j) (by decide) (by omega_using [hmag]) r₇)
    fun s₈ ⟨c₈, k₈, _⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₈ (decide (bmag K.w k j = 0)) (by rw [c₈]) (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    hL.comb.apart_A hL.comb.apart_AD) fun s₉ ⟨ex₉, ey₉, ez₉, k₉, O₉⟩ => ?_
  have hs₉ := hs₈.of_keepRegs k₉ (by decide)
  have hb₉ : s₉.gpr .esi = BitVec.ofNat 32 j := by
    rw [k₉.gpr _ (by decide), k₈.1 _ (by decide), k₇.1 _ (by decide), hb₆]
  refine WP.mono (incCmpEsi_ok s₉ (j := j) (J := K.J) (by omega_using [hjn]) (by omega_using [hJ]) hb₉)
    fun s₁₀ ⟨b₁₀, z₁₀, k₁₀⟩ fr => ?_
  have m₁₀ : s₁₀.mem = s₉.mem := k₁₀.2.1
  have m₈ : s₈.mem = s₆.mem := by rw [k₈.2.1, k₇.2.1]
  rw [m₈] at ex₉ ey₉ ez₉ O₉
  have U₁₀ : Unch base (combWx K) s₆.mem s₁₀.mem := by
    rw [m₁₀]
    refine Unch.mono (W := [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)])
      (fun x hx => O₉ x (hx (K.A.x, 8 * K.M.n) (by simp)) (hx (K.A.y, 8 * K.M.n) (by simp))
        (hx (K.A.z, 8 * K.M.n) (by simp))) fun w hw =>
      List.mem_append_left _ (combSelW_A_sub (K := K.toComb) w hw)
  have U : Unch base (combWx K) s.mem s₁₀.mem :=
    (U₁₃.trans (U₄.trans (U₆.trans U₁₀))).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with h | h | h | h <;> exact h
  have hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E :=
    fun _ hx => List.mem_append_left _ hx
  have hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  refine ⟨⟨hs₉.of_keeps k₁₀.keeps (by decide), b₁₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by
      rw [unch_read32 U (by have := hL.ptr_le; omega_using [hn, this]) (combW_ptr hL)]
      exact hI.tsym⟩, z₁₀⟩
  · have c₃ : KeepRegs (powClob) s s₃ := E₃.keep.mono clob_powClob
    have c₄ : KeepRegs (powClob) s₃ s₄ :=
      Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob
    have hcl : ∀ r ∈ [Reg.eax, .ecx, .edx, .ebx], r ∈ powClob := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
    have c₅ : KeepRegs (powClob) s₄ s₅ := (CKeeps.regs k₅).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₆ : KeepRegs (powClob) s₅ s₆ := k₆.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₇ : KeepRegs (powClob) s₆ s₇ := (CKeeps.regs k₇).mono hcl
    have c₈ : KeepRegs (powClob) s₇ s₈ := (CKeeps.regs k₈).mono fun r hr => hcl r (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    have c₉ : KeepRegs (powClob) s₈ s₉ := k₉.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    have c₁₀ : KeepRegs (powClob) s₉ s₁₀ := (CKeeps.regs k₁₀).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact hI.keep.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans (c₈.trans (c₉.trans c₁₀)))))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega_using [hn])
  · have hA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
      rw [hA₆ x hx]; exact hI.lt x hx
    have hE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
      rw [hAE₄ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])]
      exact E₃.lt x hx
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₁₀, ex₉]; split
      · exact hA _ (by simp)
      · rw [dx₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
    · rw [m₁₀, ey₉]; split
      · exact hA _ (by simp)
      · rw [dy₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
    · rw [m₁₀, ez₉]; split
      · exact hA _ (by simp)
      · rw [dz₆]; split
        · exact hDlt _ (by simp)
        · exact hE _ (by simp)
  · -- The point.
    have e : ∀ {x y : Nat} {t : State}, wordsVal s₁₀.mem base x K.M.n = wordsVal t.mem base y K.M.n →
        tmv C K.M.n base s₁₀ x = tmv C K.M.n base t y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    have eA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s x :=
      fun x hx => by show toM _ _ _ = toM _ _ _; rw [hAx x hx]
    have eE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ x :=
      fun x hx => by
        show toM _ _ _ = toM _ _ _
        rw [hAE₄ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h])]
    rw [bpart_succ_pt hC hG hw.1]
    have hErep := E₃.rep
    have hEz := E₃.z
    by_cases h0 : bmag K.w k j = 0
    · simp only [decide_eq_true h0, ↓reduceIte] at ex₉ ey₉ ez₉
      rw [e (t := s) (by rw [m₁₀, ex₉, hA₆ _ (by simp)]), e (t := s) (by rw [m₁₀, ey₉, hA₆ _ (by simp)]),
        e (t := s) (by rw [m₁₀, ez₉, hA₆ _ (by simp)])]
      have hQ : bentry C K.w k j = .infinity := by
        unfold bentry
        rw [h0, show combPtW C K.w j 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
        split <;> rfl
      rw [hQ, add_infinity]
      exact hI.rep
    · have h1 : 1 ≤ bmag K.w k j := by omega_using [h0]
      simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte] at ex₉ ey₉ ez₉
      simp only [h1, ↓reduceIte] at hEz
      rw [hEz] at hErep
      have hQa := Rep.eq_affine hC hErep
      have hZiff : wordsVal s₄.mem base K.A.z K.M.n = 0 ↔ tmv C K.M.n base s K.A.z = 0 := by
        rw [hAE₄ _ (by simp), hAx _ (by simp)]
        exact (toM_eq_zero_iff hV.unit (hI.lt _ (by simp))).symm
      by_cases hz0 : wordsVal s₄.mem base K.A.z K.M.n = 0
      · simp only [hz0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆]), eE _ (by simp), eE _ (by simp), eE _ (by simp)]
        have hP : zmul (bpart K.w k j) (G C) = .infinity := by
          have h := hI.rep
          rw [hZiff.mp hz0] at h
          exact InvJ.eq_infinity h
        rw [hP, infinity_add']
        rw [← hEz] at hErep
        exact InvJ.of_rep01 hErep (Or.inl hEz)
      · simp only [hz0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆])]
        have hD : (tmv C K.M.n base s₄ K.D.x, tmv C K.M.n base s₄ K.D.y, tmv C K.M.n base s₄ K.D.z) =
            maddJF (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y) (tmv C K.M.n base s₃ K.A.z)
              (tmv C K.M.n base s₃ K.E.x) (tmv C K.M.n base s₃ K.E.y) := by
          rw [← t₄]
          show (toM _ _ _, toM _ _ _, toM _ _ _) = _
          rw [I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp))]
        have hrepA : InvJ C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
            (tmv C K.M.n base s₃ K.A.z) (zmul (bpart K.w k j) (G C)) := by
          rw [eA _ (by simp), eA _ (by simp), eA _ (by simp)]; exact hI.rep
        have hZ : tmv C K.M.n base s₃ K.A.z ≠ 0 := by
          rw [eA _ (by simp)]; exact fun h => hz0 (hZiff.mpr h)
        have hon : onCurve C (bentry C K.w k j) = true := by
          rw [bentry_eq hw.1]; exact hC.onCurve_zmul hG _
        have hne : zmul (bpart K.w k j) (G C) ≠ bentry C K.w k j := by
          rw [bentry_eq hw.1]
          exact booth_ne hC hG hB.n hB.n0 hB.cop hB.safe hw.1 hB.J2 hB.kmax hk hj hjn h0
        rw [hQa] at hon hne ⊢
        have h := InvJ.madd hC hM3 (hC.onCurve_zmul hG _) hon hrepA hZ hne
        rw [← hD] at h
        exact h
  · intro t ht
    rw [U.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  · exact hF.tblAt hwr₀ hsp₀ hI.tbl (by rw [k₁₀.2.2.1, k₁₀.2.2.2, k₉.rd, k₉.wr, k₈.2.2.1, k₈.2.2.2,
      k₇.2.2.1, k₇.2.2.2, k₆.rd, k₆.wr, k₅.2.2.1, k₅.2.2.2, P₄.rd, P₄.wr, E₃.keep.rd, E₃.keep.wr]) fr

end VG.Proof.Weierstrass.X86
