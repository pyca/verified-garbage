module

public import VerifiedGarbage.Impl.Weierstrass.X86.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJSelect
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombJEntry
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.CombFrame
import VerifiedGarbage.Proof.Weierstrass.X86.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! ### `Weierstrass.X86.TCombJStep`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- Advance the public window counter and test whether it reached the end. -/
theorem incCmpEsi_ok (s : State) {j J : Nat} (hj : j + 1 ≤ J) (hJ : J < 2 ^ 31)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm (BitVec.ofNat 32 J))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j + 1) ∧ t.zf = some (decide (j + 1 = J)) ∧ CKeeps [.esi] s t := by
  obtain he : BitVec.ofNat 32 j + 1 = BitVec.ofNat 32 (j + 1) := by rw [BitVec.ofNat_add]; rfl
  obtain hz : (BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 J == 0) = decide (j + 1 = J) := by
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
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain hsz : size ≤ 2 ^ 64 := by have := hL.sz; omega_using [this]
  -- The working space of the field calls and the output words: apart from the comb's slots.
  obtain hX : ∀ x ∈ combWs K.toComb, ∀ w ∈ [(K.wk, 64 * K.M.n), Mont.outW],
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
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  obtain hNZ : NeZero C.p := ⟨by omega_using [hp0]⟩
  obtain hsp₀ : s.gpr .esp = s₀.gpr .esp := hI.keep.gpr _ (by decide)
  have hwr₀ : s.wr = s₀.wr := hI.keep.wr
  refine WP.withSp hsp (by rw [hsp₀]; exact hF.sp_lo) ?_
  unfold TCombCfg.stepJ
  refine WP.seq ?_
  obtain hz : wordsVal s.mem base K.zero K.M.n = 0 := by
    rw [hI.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_using [hn, this]), hF.zero]
  refine WP.mono (tentryJ_ok hL hC hV hpn hI.scr hI.mod hjn hI.esi hb1 (c := true) (Or.inl ⟨rfl, hj⟩)
    hI.bits hz hI.tsym hI.tbl hF.out) fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ E₃ => ?_)
  obtain hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW], w ∈ combWx K := fun w hw =>
    (List.mem_append.mp (show w ∈ combEntryW K.toComb ++ [(K.wk, 64 * K.M.n), Mont.outW] from hw)).elim
      (fun h => List.mem_append_left _ (combEntryW_sub w h)) (fun h => List.mem_append_right _ h)
  obtain U₁₃ : Unch base (combWx K) s.mem s₃.mem := E₃.unch.mono hEW
  obtain hmoW := tcombW_mo hL hI.mod
  obtain hM₃ : ModOkW K.M size C.p s₃.mem base :=
    hI.mod.unch U₁₃ (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega_using [hn])
  -- What `A` and the read-only slots hold at `s₃`.
  obtain hAx : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    hL.comb.wordsVal_entryX hsz hX E₃.unch
  obtain U₃ : Unch base (tcombW K) s₀.mem s₃.mem :=
    (hI.unch.trans U₁₃).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  obtain hro : ∀ x ∈ combRo K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s₀.mem base x K.M.n :=
    fun x hx => U₃.wordsVal (tcombW_ro hL hx) (by have := hle x (combRo_slots x hx); omega_using [hn, this])
  obtain hSl : ∀ x ∈ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  obtain hlt₃ : ∀ x ∈ rcbR K.S K.A K.E, wordsVal s₃.mem base x K.M.n < C.p := by
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
  obtain I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E) (tmv C K.M.n base s₃) s₃ :=
    ⟨E₃.scr, hM₃, hSl, hlt₃, fun _ _ => rfl⟩
  obtain hSl' : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [combSlots, List.mem_append, TCombCfg.toComb]; exact Or.inr hx
    · exact hSl x hx
  refine WP.seq (WP.mono (maddJ_ok hL.comb.lay (hL.wkOk hV.fn) hV.unit hL.comb.add hSl' I₃
    (fun _ h => h)) fun s₄ ⟨P₄, I₄, t₄⟩ => ?_)
  dsimp only [TCombCfg.toComb] at P₄ I₄ t₄
  have hs₄ := I₄.scr
  obtain hb₄ : s₄.gpr .esi = BitVec.ofNat 32 j := by
    rw [P₄.gpr _ esi_not_clob, E₃.keep.gpr _ esi_not_clob, hI.esi]
  obtain U₄ : Unch base (combWx K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
    simp only [progW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | h | h | h
    · exact Or.inl (Or.inl ⟨y, by simp only [combWs, List.mem_append, TCombCfg.toComb]; exact Or.inr hy, rfl⟩)
    · exact Or.inl (Or.inr (by rw [h]; rfl))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- `A` and `E` are not written by the addition.
  obtain hAE₄ : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := hL.comb.wordsVal_addX hsz hX P₄.unch
  have hbl := hL.bits
  obtain hz' : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_using []
  have hw := hL.w
  have hnn := hL.n
  -- `D = E` where `A` is `O`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs₄ hnn.1 (hle K.A.z (by tcomb_mem))) fun s₅ ⟨c₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅.keeps (by decide)
  obtain hsel := fun (x : Nat) (hx : x ∈ [K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]) =>
    hle x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem)
  refine WP.mono (selPtKeep_ok hs₅ (decide (wordsVal s₄.mem base K.A.z K.M.n ≠ 0)) (by rw [c₅])
    (n := K.M.n) (o := K.D) (a := K.E) hsel
    hL.comb.apart_D hL.comb.apart_DE) fun s₆ ⟨dx₆, dy₆, dz₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  rw [m₅] at dx₆ dy₆ dz₆ O₆
  obtain UD₆ : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s₄.mem s₆.mem :=
    fun x hx => O₆ x (hx (K.D.x, 8 * K.M.n) (by simp)) (hx (K.D.y, 8 * K.M.n) (by simp))
      (hx (K.D.z, 8 * K.M.n) (by simp))
  obtain U₆ : Unch base (combWx K) s₄.mem s₆.mem :=
    UD₆.mono fun w hw => List.mem_append_left _ (combSelW_D_sub (K := K.toComb) w hw)
  obtain hA₆ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => ((hL.comb.wordsVal_selD hsz UD₆ x hx : wordsVal s₆.mem base x K.M.n = wordsVal s₄.mem base x K.M.n).trans
      (hAE₄ x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))).trans
      (hAx x hx)
  obtain hb₆ : s₆.gpr .esi = BitVec.ofNat 32 j := by
    rw [k₆.gpr _ (by decide), k₅.1 _ (by decide), hb₄]
  obtain hbits₆ : ∀ t < K.w * K.J, s₆.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    rw [(U₁₃.trans (U₄.trans U₆)).byte (fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with h | h | h <;> exact combW_bits hL ht w h)
      (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  obtain hwi : K.w * j + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  -- The digit again, and `A = D` unless it is zero.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (bdigit_ok K hs₆ (k := k) (j := j) (N := K.w * K.J) hw.1 hw.2 hwi
    (by omega_using [hbl, hz', hn]) hb1 hb₆ hbits₆ (Or.inl ⟨rfl, hj⟩)) fun s₇ ⟨_, r₇, k₇⟩ => ?_
  obtain hs₇ := hs₆.of_keeps k₇.keeps (by decide)
  obtain hmag : bmag K.w k j ≤ 128 := by
    have := bmag_le hw.1 k j
    exact Nat.le_trans this (Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (eqMask_ok s₇ (v := 0) (a := bmag K.w k j) (by decide) (by omega_using [hmag]) r₇)
    fun s₈ ⟨c₈, k₈, _⟩ => ?_
  obtain hs₈ := hs₇.of_keeps k₈.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₈ (decide (bmag K.w k j = 0)) (by rw [c₈]) (n := K.M.n) (o := K.A) (a := K.D)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hle _ (by tcomb_mem))
    hL.comb.apart_A hL.comb.apart_AD) fun s₉ ⟨ex₉, ey₉, ez₉, k₉, O₉⟩ => ?_
  obtain hs₉ := hs₈.of_keepRegs k₉ (by decide)
  obtain hb₉ : s₉.gpr .esi = BitVec.ofNat 32 j := by
    rw [k₉.gpr _ (by decide), k₈.1 _ (by decide), k₇.1 _ (by decide), hb₆]
  refine WP.mono (incCmpEsi_ok s₉ (j := j) (J := K.J) (by omega_using [hjn]) (by omega_using [hJ]) hb₉)
    fun s₁₀ ⟨b₁₀, z₁₀, k₁₀⟩ fr => ?_
  have m₁₀ : s₁₀.mem = s₉.mem := k₁₀.2.1
  obtain m₈ : s₈.mem = s₆.mem := by rw [k₈.2.1, k₇.2.1]
  rw [m₈] at ex₉ ey₉ ez₉ O₉
  obtain U₁₀ : Unch base (combWx K) s₆.mem s₁₀.mem := by
    rw [m₁₀]
    refine Unch.mono (W := [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)])
      (fun x hx => O₉ x (hx (K.A.x, 8 * K.M.n) (by simp)) (hx (K.A.y, 8 * K.M.n) (by simp))
        (hx (K.A.z, 8 * K.M.n) (by simp))) fun w hw =>
      List.mem_append_left _ (combSelW_A_sub (K := K.toComb) w hw)
  obtain U : Unch base (combWx K) s.mem s₁₀.mem :=
    (U₁₃.trans (U₄.trans (U₆.trans U₁₀))).mono fun w hw => by
      simp only [List.mem_append] at hw; rcases hw with h | h | h | h <;> exact h
  obtain hDv : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E :=
    fun _ hx => List.mem_append_left _ hx
  obtain hDlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => I₄.lt x (hDv x hx)
  refine ⟨⟨hs₉.of_keeps k₁₀.keeps (by decide), b₁₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by
      rw [unch_read32 U (by have := hL.ptr_le; omega_using [hn, this]) (combW_ptr hL)]
      exact hI.tsym⟩, z₁₀⟩
  · have c₃ : KeepRegs (powClob) s s₃ := E₃.keep.mono clob_powClob
    obtain c₄ : KeepRegs (powClob) s₃ s₄ :=
      Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob
    obtain hcl : ∀ r ∈ [Reg.eax, .ecx, .edx, .ebx], r ∈ powClob := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
      · exact clob_powClob _ (by simp [clob])
    obtain c₅ : KeepRegs (powClob) s₄ s₅ := (CKeeps.regs k₅).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    obtain c₆ : KeepRegs (powClob) s₅ s₆ := k₆.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    obtain c₇ : KeepRegs (powClob) s₆ s₇ := (CKeeps.regs k₇).mono hcl
    obtain c₈ : KeepRegs (powClob) s₇ s₈ := (CKeeps.regs k₈).mono fun r hr => hcl r (by
      simp only [List.mem_singleton] at hr; subst hr; simp)
    obtain c₉ : KeepRegs (powClob) s₈ s₉ := k₉.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])
    obtain c₁₀ : KeepRegs (powClob) s₉ s₁₀ := (CKeeps.regs k₁₀).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact hI.keep.trans (c₃.trans (c₄.trans (c₅.trans (c₆.trans (c₇.trans (c₈.trans (c₉.trans c₁₀)))))))
  · exact (hI.unch.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ hw
  · exact hI.mod.unch U (fun w hw => hmoW w (List.mem_append_left _ hw)) (by omega_using [hn])
  · have hA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
      rw [hA₆ x hx]; exact hI.lt x hx
    obtain hE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
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
    obtain e : ∀ {x y : Nat} {t : State}, wordsVal s₁₀.mem base x K.M.n = wordsVal t.mem base y K.M.n →
        tmv C K.M.n base s₁₀ x = tmv C K.M.n base t y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    obtain eA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s x :=
      fun x hx => by show toM _ _ _ = toM _ _ _; rw [hAx x hx]
    obtain eE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₃ x :=
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
      obtain hQ : bentry C K.w k j = .infinity := by
        unfold bentry
        rw [h0, show combPtW C K.w j 0 = .infinity by simp [combPtW, Spec.Weierstrass.mul]]
        split <;> rfl
      rw [hQ, add_infinity]
      exact hI.rep
    · have h1 : 1 ≤ bmag K.w k j := by omega_using [h0]
      simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte] at ex₉ ey₉ ez₉
      simp only [h1, ↓reduceIte] at hEz
      rw [hEz] at hErep
      obtain hQa := Rep.eq_affine hC hErep
      obtain hZiff : wordsVal s₄.mem base K.A.z K.M.n = 0 ↔ tmv C K.M.n base s K.A.z = 0 := by
        rw [hAE₄ _ (by simp), hAx _ (by simp)]
        exact (toM_eq_zero_iff hV.unit (hI.lt _ (by simp))).symm
      by_cases hz0 : wordsVal s₄.mem base K.A.z K.M.n = 0
      · simp only [hz0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆]), eE _ (by simp), eE _ (by simp), eE _ (by simp)]
        obtain hP : zmul (bpart K.w k j) (G C) = .infinity := by
          have h := hI.rep
          rw [hZiff.mp hz0] at h
          exact InvJ.eq_infinity h
        rw [hP, infinity_add']
        rw [← hEz] at hErep
        exact InvJ.of_rep01 hErep (Or.inl hEz)
      · simp only [hz0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at dx₆ dy₆ dz₆
        rw [e (t := s₄) (by rw [m₁₀, ex₉, dx₆]), e (t := s₄) (by rw [m₁₀, ey₉, dy₆]),
          e (t := s₄) (by rw [m₁₀, ez₉, dz₆])]
        obtain hD : (tmv C K.M.n base s₄ K.D.x, tmv C K.M.n base s₄ K.D.y, tmv C K.M.n base s₄ K.D.z) =
            maddJF (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y) (tmv C K.M.n base s₃ K.A.z)
              (tmv C K.M.n base s₃ K.E.x) (tmv C K.M.n base s₃ K.E.y) := by
          rw [← t₄]
          show (toM _ _ _, toM _ _ _, toM _ _ _) = _
          rw [I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp)), I₄.val _ (hDv _ (by simp))]
        obtain hrepA : InvJ C (tmv C K.M.n base s₃ K.A.x) (tmv C K.M.n base s₃ K.A.y)
            (tmv C K.M.n base s₃ K.A.z) (zmul (bpart K.w k j) (G C)) := by
          rw [eA _ (by simp), eA _ (by simp), eA _ (by simp)]; exact hI.rep
        obtain hZ : tmv C K.M.n base s₃ K.A.z ≠ 0 := by
          rw [eA _ (by simp)]; exact fun h => hz0 (hZiff.mpr h)
        obtain hon : onCurve C (bentry C K.w k j) = true := by
          rw [bentry_eq hw.1]; exact hC.onCurve_zmul hG _
        obtain hne : zmul (bpart K.w k j) (G C) ≠ bentry C K.w k j := by
          rw [bentry_eq hw.1]
          exact booth_ne hC hG hB.n hB.n0 hB.cop hB.safe hw.1 hB.J2 hB.kmax hk hj hjn h0
        rw [hQa] at hon hne ⊢
        obtain h := InvJ.madd hC hM3 (hC.onCurve_zmul hG _) hon hrepA hZ hne
        rw [← hD] at h
        exact h
  · intro t ht
    rw [U.byte (combW_bits hL ht) (by omega_using [hbl, hz', ht, hn])]
    exact hI.bits t ht
  · exact hF.tblAt hwr₀ hsp₀ hI.tbl (by rw [k₁₀.2.2.1, k₁₀.2.2.2, k₉.rd, k₉.wr, k₈.2.2.1, k₈.2.2.2,
      k₇.2.2.1, k₇.2.2.2, k₆.rd, k₆.wr, k₅.2.2.1, k₅.2.2.2, P₄.rd, P₄.wr, E₃.keep.rd, E₃.keep.wr]) fr

end VG.Proof.Weierstrass.X86

end

end

/-! ### `Weierstrass.X86.TCombJFirst`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- Window zero initializes the Jacobian accumulator with its Booth entry. -/
theorem firstJ_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hsp : SpOk K.first 20) :
    WP isa K.first s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' 1 := by
  have hn := hs.nowrap
  have hJ := hL.comb.J
  rw [TCombCfg.toComb_J] at hJ
  have hw := hL.w
  have hnd := hL.comb.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  obtain hsl : ∀ x ∈ combSlots K.toComb, K.bits + K.kbytes + 4 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes :=
    fun x hx => hL.bits_sl x (List.mem_cons_of_mem _ hx)
  have hbz := hL.bits
  obtain hzw : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_arith
  obtain hk : k < 2 ^ (K.w * K.J) :=
    Nat.lt_of_lt_of_le hF.k_lt (Nat.pow_le_pow_right (by decide) hL.kbytes)
  obtain hmo := tcombW_mo hL hM
  refine WP.withSp hsp hF.sp_lo ?_
  unfold TCombCfg.first
  refine WP.seq ?_
  obtain e : K.clearBits ++ [.mov .esi (.imm 0)] ++ K.bdigit false ++ K.select = [.mov .eax (.imm 0)] ++
      ((List.range K.zw).map (fun i => .store (sc (K.bits + K.kbytes + 4 * i)) .eax) ++
        ([.mov .esi (.imm (BitVec.ofNat 32 0))] ++ (K.bdigit false ++ K.select))) := by
    unfold TCombCfg.clearBits
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e, WP.block_append_iff]
  refine WP.mono (zeroEax_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zstores_ok hs₁ z₁ K.zw hL.bits) fun s₂ ⟨k₂, O₂, z₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (movEsi_ok s₂ (j := 0) (by decide)) fun s₃ ⟨b₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃.keeps (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain U₃ : Unch base [(K.bits + K.kbytes, 4 * K.zw)] s.mem s₃.mem := by
    rw [m₃, ← k₁.2.1]; exact O₂.unch
  obtain U₃' : Unch base (tcombW K) s.mem s₃.mem := U₃.mono fun w hw => List.mem_append_right _ hw
  obtain hro : ∀ x ∈ combSlots K.toComb, wordsVal s₃.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => by rw [m₃, O₂.wordsVal (by have := hsl x hx; omega_arith) (b64 x hx), k₁.2.1]
  obtain hM₃ : ModOkW K.M size C.p s₃.mem base := hM.unch U₃' hmo (by omega_arith)
  obtain hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [hro _ (by tcomb_mem)]; exact hF.zero
  obtain hbits₃ : ∀ t < K.w * K.J, s₃.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 := by
    intro t ht
    by_cases htk : t < K.kbytes
    · rw [U₃.byte (fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; dsimp only; omega_arith)
        (by omega_using [hbz, hzw, ht, hn])]
      exact hF.bits t htk
    · have := z₂ (t - K.kbytes) (by omega_arith)
      rw [show K.bits + K.kbytes + (t - K.kbytes) = K.bits + t by omega_arith] at this
      rw [m₃, this, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF.k_lt
        (Nat.pow_le_pow_right (by decide) (by omega_arith)))]
      rfl
  obtain hT₃ : (s₃.mem.readW (off base K.ptr) 32).setWidth 64 = T := by
    rw [unch_read32 U₃ (by have := hL.ptr_le; omega_arith) (fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw
      have := hL.ptr_bits; dsimp only; omega_arith)]
    exact hF.tsym
  obtain hTM₃ : TblMem s₃ T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) :=
    TblMem.of_unch hF.tbl (by rw [k₃.2.2.1, k₃.2.2.2, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]) U₃
      (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact hL.bits) hF.out
  refine WP.mono (tentryJ_ok hL hC hV hpn hs₃ hM₃ (i := 0) (by omega_arith) b₃ hb1 (c := false)
    (Or.inr ⟨rfl, rfl⟩) hbits₃ hz₃ hT₃ hTM₃ hF.out) fun s₄ h₄ => WP.seq (WP.mono h₄ fun s₅ E₅ => ?_)
  rw [WP.block_append_iff]
  obtain hAE : ∀ x ∈ [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z], x ∈ combWs K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  refine WP.mono (copyPt_ok E₅.scr (o := K.A) (a := K.E) (n := K.M.n)
    (fun x hx => hle x (combWs_slots _ x (hAE x hx)))
    (fun x hx y hy hxy => hL.comb.apart₂ (hAE x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with h | h | h <;> simp [h]))
      (hAE y hy) hxy)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> grind)
    ⟨by grind, by grind, by grind⟩) fun s₆ ⟨ex₆, ey₆, ez₆, k₆, U₆⟩ => ?_
  refine WP.mono (movEsi_ok s₆ (j := 1) (by decide)) fun s₇ ⟨b₇, k₇⟩ fr => ?_
  have m₇ : s₇.mem = s₆.mem := k₇.2.1
  obtain hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n), (K.wk, 64 * K.M.n), Mont.outW], w ∈ combWx K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h | h | h | h | h <;> subst h <;> simp
  obtain hAW : ∀ w ∈ [(K.A.x, 8 * K.M.n), (K.A.y, 8 * K.M.n), (K.A.z, 8 * K.M.n)], w ∈ combWx K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false, TCombCfg.toComb]
    rcases hw with h | h | h <;> subst h <;> simp
  obtain U : Unch base (combWx K) s₃.mem s₇.mem := by
    rw [m₇]; exact (E₅.unch.trans U₆).mono fun w hw => by
      rcases List.mem_append.mp hw with h | h
      · exact hEW w h
      · exact hAW w h
  obtain UT : Unch base (tcombW K) s.mem s₇.mem := (U₃'.trans U).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · exact List.mem_append_left _ h
  refine ⟨E₅.scr.of_keepRegs k₆ (by decide) |>.of_keeps k₇.keeps (by decide), b₇, ?_, UT, hM.unch UT hmo (by omega_arith),
    ?_, ?_, fun t ht => ?_, ?_, by
      rw [unch_read32 UT (by have := hL.ptr_le; omega_arith) (tcombW_ptr hL)]
      exact hF.tsym⟩
  · have c : ∀ r ∈ [Reg.eax], r ∈ powClob := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
    obtain cb : ∀ r ∈ [Reg.esi], r ∈ powClob := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
    exact (((((CKeeps.regs k₁).mono c).trans (k₂.mono fun r hr => absurd hr List.not_mem_nil)).trans
      ((CKeeps.regs k₃).mono cb)).trans (E₅.keep.mono clob_powClob)).trans
      ((k₆.mono c).trans ((CKeeps.regs k₇).mono cb))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [m₇, ex₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ey₆]; exact E₅.lt _ (by simp)
    · rw [m₇, ez₆]; exact E₅.lt _ (by simp)
  · have e : ∀ {x y : Nat}, wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base y K.M.n →
        tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
    rw [e (by rw [m₇, ex₆]), e (by rw [m₇, ey₆]), e (by rw [m₇, ez₆])]
    rw [show (1 : Nat) = 0 + 1 from rfl, bpart_succ_pt hC hG hw.1, bpart_zero,
      show zmul (0 : Int) (G C) = .infinity by simp [zmul, Spec.Weierstrass.mul], infinity_add']
    refine InvJ.of_rep01 E₅.rep ?_
    rw [E₅.z]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [U.byte (combW_bits hL ht) (by omega_using [hbz, hzw, ht, hn])]
    exact hbits₃ t ht
  · exact TblMem.of_frame hF.tbl (by rw [k₇.2.2.1, k₇.2.2.2, k₆.rd, k₆.wr, E₅.keep.rd, E₅.keep.wr,
      k₃.2.2.1, k₃.2.2.2, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]) fr hF.apart

end VG.Proof.Weierstrass.X86

end

end

@[expose] public section

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
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hV.one_lt
  obtain hNZ : NeZero C.p := ⟨by omega_arith⟩
  obtain hspS : SpOk K.stepJ 20 := ⟨NoSp.loop hsp.right.left.1, hsp.right.left.2⟩
  unfold TCombCfg.combJ
  refine WP.seq (WP.mono (firstJ_ok hL hC hG hV hpn hb1 hs hM hF hsp.left) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s' K.J)
    (Inv := fun r s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s s'
      (K.J - r)) (n := K.J - 1)
    (fun r s' h1 h2 hi => WP.mono (stepJ_ok hL hC hM3 hG hV hpn hb1 hB hk hF (j := K.J - r) (by omega_arith)
      (by omega_arith) hi hspS) fun s'' ⟨h, z⟩ => ⟨by rw [show K.J - (r - 1) = K.J - r + 1 by omega_arith]; exact h, by
        rw [z]; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩)
    (fun s' hi => by rw [Nat.sub_zero] at hi; exact hi) (by omega_arith)
    (by rw [show K.J - (K.J - 1) = 1 by omega_arith]; exact I₁)) fun s₂ I₂ => ?_)
  -- `Y = 1` where `Z = 0`.
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [I₂.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); omega_arith), hF.zero]
  obtain ayz : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y := by
    have := combW_ro hL.comb (x := K.zero) (by simp [combRo, TCombCfg.toComb]) (K.A.y, 8 * K.M.n)
      (by simp [combW, combWs, TCombCfg.toComb])
    dsimp only [TCombCfg.toComb] at this; omega_arith
  refine WP.seq (WP.mono (outFix_ok K I₂.scr hnn.1 (Nat.lt_trans hV.one_lt hpn) (hle _ (by tcomb_mem))
    (hle _ (by tcomb_mem)) (hle _ (by tcomb_mem)) ayz hz₂) fun s₃ ⟨ey₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := I₂.scr.of_keepRegs k₃ (by decide)
  obtain b64 : ∀ x ∈ combSlots K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hle x hx; omega_using [this, hn]
  obtain ex₃ : wordsVal s₃.mem base K.A.x K.M.n = wordsVal s₂.mem base K.A.x K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by nd_find hnd)) (b64 _ (by tcomb_mem))
  obtain ez₃ : wordsVal s₃.mem base K.A.z K.M.n = wordsVal s₂.mem base K.A.z K.M.n :=
    O₃.wordsVal (hL.comb.apart₂ (by tcomb_mem) (by tcomb_mem) (by nd_find hnd)) (b64 _ (by tcomb_mem))
  have UA : Unch base [(K.A.y, 8 * K.M.n)] s₂.mem s₃.mem := O₃.unch
  obtain hmoW := tcombW_mo hL hM
  obtain hAyW : (K.A.y, 8 * K.M.n) ∈ tcombW K := List.mem_append_left _ (by
    simp only [combWx, combW, combWs, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false,
      TCombCfg.toComb]; simp)
  obtain U₃ : Unch base (tcombW K) s.mem s₃.mem := (I₂.unch.trans UA).mono fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact hAyW
  obtain hM₃ : ModOkW K.M size C.p s₃.mem base := hM.unch U₃ hmoW (by omega_arith)
  obtain hlt₃ : ∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₃]; exact I₂.lt _ (by simp)
    · rw [ey₃]; split
      · exact hV.one_lt
      · exact I₂.lt _ (by simp)
    · rw [ez₃]; exact I₂.lt _ (by simp)
  obtain hSlA : ∀ x ∈ [K.A.x, K.A.y, K.A.z], x ∈ combSlots K.toComb := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> tcomb_mem
  obtain I₃ : Inv K.M base size C.p (· ∈ combSlots K.toComb) [K.A.x, K.A.y, K.A.z] (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, hM₃, hSlA, hlt₃, fun _ _ => rfl⟩
  obtain hS : ∀ op ∈ K.outOps, ∀ x ∈ op.out :: op.ins, x ∈ combSlots K.toComb := by
    intro op hop x hx
    simp only [TCombCfg.outOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> tcomb_mem
  obtain hR : readsOk K.outOps [K.A.x, K.A.y, K.A.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out]
  refine WP.mono (fprog_ok hL.comb.lay (hL.wkOk hV.fn) hV.unit K.outOps I₃ hS hR)
    fun s₄ ⟨P₄, I₄⟩ => ?_
  obtain hval : ∀ x ∈ [K.A.x, K.A.y, K.A.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₄.mem base x K.M.n) =
      runOps K.outOps (tmv C K.M.n base s₃) x ∧ wordsVal s₄.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ validAfter K.outOps [K.A.x, K.A.y, K.A.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₄.val x hm, I₄.lt x hm⟩
  obtain U₄ : Unch base (tcombW K) s₃.mem s₄.mem := P₄.unch.mono fun w hw => by
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
      hmoW (by omega_arith), fun x hx => (hval x hx).2, ?_⟩
  · exact (I₂.keep.trans (k₃.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob])).trans
      (Keeps.mono ⟨P₄.gpr, P₄.rd, P₄.wr⟩ clob_powClob)
  · -- The values.
    obtain e : ∀ x ∈ [K.A.x, K.A.y, K.A.z], tmv C K.M.n base s₄ x = runOps K.outOps (tmv C K.M.n base s₃) x :=
      fun x hx => (hval x hx).1
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]
    obtain hxt : K.A.x ≠ K.S.t0 := by grind
    obtain hzt : K.A.z ≠ K.S.t0 := by grind
    obtain hxz : K.A.x ≠ K.A.z := by grind
    obtain hxy : K.A.x ≠ K.A.y := by grind
    obtain hyt : K.A.y ≠ K.S.t0 := by grind
    obtain hyz : K.A.y ≠ K.A.z := by grind
    simp only [TCombCfg.outOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
    obtain hy : tmv C K.M.n base s₃ K.A.y = if tmv C K.M.n base s₂ K.A.z = 0 then 1
        else tmv C K.M.n base s₂ K.A.y := by
      show toM _ _ _ = _
      rw [ey₃]
      by_cases h : wordsVal s₂.mem base K.A.z K.M.n = 0
      · have h' : tmv C K.M.n base s₂ K.A.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
        simp only [h, h', ↓reduceIte]; exact hV.one
      · have h' : tmv C K.M.n base s₂ K.A.z ≠ 0 := fun h0 =>
          h ((toM_eq_zero_iff hV.unit (I₂.lt _ (by simp))).mp h0)
        simp only [h, h', ↓reduceIte]
    obtain ex : tmv C K.M.n base s₃ K.A.x = tmv C K.M.n base s₂ K.A.x := by
      show toM _ _ _ = toM _ _ _; rw [ex₃]
    obtain ez : tmv C K.M.n base s₃ K.A.z = tmv C K.M.n base s₂ K.A.z := by
      show toM _ _ _ = toM _ _ _; rw [ez₃]
    rw [hy, ex, ez]
    obtain h := InvJ.out hC I₂.rep
    rwa [bpart_top (by omega_arith) (Nat.lt_of_lt_of_le hk hB.kmax), zmul_natCast] at h

end VG.Proof.Weierstrass.X86
