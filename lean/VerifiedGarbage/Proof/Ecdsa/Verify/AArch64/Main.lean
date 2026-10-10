import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdh.AArch64.Main

/-! ## `ProjectiveArithmetic` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (projectiveOps)
variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

abbrev projectiveSlots : List Nat := [X, XM, RZ, W, RX, ACC, XN]
abbrev projectiveReads : List Nat := [XM, RZ, RX, ACC]
abbrev projectiveWrites : List Nat := [X, W, XM, X, XN, TMP]

theorem projectiveOps_rename (sl : Nat → Nat) :
    projectiveOps sl = (projectiveOps id).map (FOp.rename sl) := rfl

theorem projectiveOps_run (hc : BaseCfgOk c) (e : Nat → Fe c.C) :
    runOps (projectiveOps c.sl) e (c.sl W) = e (c.sl RX) - e (c.sl XM) * e (c.sl RZ) ∧
    runOps (projectiveOps c.sl) e (c.sl XN) =
      e (c.sl RX) - (e (c.sl XM) + e (c.sl ACC)) * e (c.sl RZ) := by
  have hout : ∀ op ∈ projectiveOps id, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 82 := by decide
  have H := runOps_rename c.sl (projectiveOps id) e (fun op hop _ h =>
    sl_inj c hc.n0 h (.inr (hout op hop).2) (.inl (hout op hop).1))
  rw [← projectiveOps_rename] at H
  exact ⟨congrFun H W, congrFun H XN⟩

/-- The five field operations compute both projective differences. -/
theorem projectiveOps_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ projectiveReads, sv c base s i < c.C.p) :
    WP isa (fprogB c.MP' (projectiveOps c.sl)) s fun t =>
      Scr t base size ∧ Unch base (slW c projectiveWrites) s.mem t.mem ∧
      sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - tmv c.C c.n base s (c.sl XM) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (tmv c.C c.n base s (c.sl XM) + tmv c.C c.n base s (c.sl ACC)) * tmv c.C c.n base s (c.sl RZ) := by
  have hL : Lay c.MP' size (· ∈ projectiveSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ projectiveSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 c i, MP'_A c,
    fun f m' h => (hc.call_p f m' h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ projectiveSlots.map c.sl) (projectiveReads.map c.sl)
      (tmv c.C c.n base s) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ projectiveReads, i ∈ projectiveSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  have reads : readsOk (projectiveOps c.sl) (projectiveReads.map c.sl) = true := by
    rw [projectiveOps_rename]
    exact readsOk_rename c.sl (by decide)
  have hS : ∀ op ∈ projectiveOps c.sl, ∀ x ∈ op.out :: op.ins, x ∈ projectiveSlots.map c.sl := by
    intro op hop x hx
    simp only [projectiveOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by decide)
  have hLo : ∀ op ∈ projectiveOps c.sl, Low c.MP' (op.out :: op.ins) := fun op hop =>
    Low.of_call fun _ _ _ x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hS op hop x hx)
      have key : ∀ i ∈ projectiveSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own c hc.n10 (key i hi).1 (key i hi).2
  refine WP.mono (fprogB_ok hL hAl (unitMod_pow_two hc.p_odd _) _ I hS hLo reads)
    fun t ⟨keep, It⟩ => ?_
  have w : c.sl W ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have xn : c.sl XN ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  have run := projectiveOps_run hc (tmv c.C c.n base s)
  exact ⟨It.scr, keep.unch, It.lt _ w, It.lt _ xn, (It.val _ w).trans run.1, (It.val _ xn).trans run.2⟩


abbrev projectivePrepareW : List Nat := [XM, ACC, MN]
abbrev projectiveAllW : List Nat := [XM, ACC, MN, X, W, XN, TMP]

theorem projectivePrepare_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare c)) s fun t =>
      Scr t base size ∧ Unch base (slW c projectivePrepareW) s.mem t.mem ∧
      sv c base t XM = c.R * c.R % c.C.p ∧ sv c base t ACC = c.mont c.C.n ∧
      sv c base t MN = c.C.p - c.C.n := by
  have hp := hc.p_ge
  have hpR := hc.p_lt
  have r2 : c.R * c.R % c.C.p < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpR
  have mont : c.mont c.C.n < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega)) hpR
  have sub : c.C.p - c.C.n < 2 ^ (64 * c.n) := by omega
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs (o := XM) (by decide) r2) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₁ (o := ACC) (by decide) mont) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setSl_ok hc hs₂ (o := MN) (by decide) sub) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  have o : ∀ {s t : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem t.mem → i < 45 → i ≠ j →
      j ≠ 54 ∧ j ≠ 82 → sv c base t i = sv c base s i := fun O hi hij hj => sv_out O hc.n10 hs.nowrap hi hij hj
  exact ⟨hs₂.of_keepRegs k₃ (by decide), O₁.unch.trans (O₂.unch.trans O₃.unch),
    by rw [o O₃ (by decide) (by decide) (by decide), o O₂ (by decide) (by decide) (by decide), e₁],
    by rw [o O₃ (by decide) (by decide) (by decide), e₂], e₃⟩

/-- Prepare constants, convert `r`, and compute both differences. -/
theorem projectiveArithmetic_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hmp : sv c base s MP = c.C.p)
    (hrx : sv c base s RX < c.C.p) (hrz : sv c base s RZ < c.C.p) :
    WP isa (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.projectivePrepare c))
      (.seq (.block (mul c.MP' (c.sl XM) (c.sl K) (c.sl XM)))
        (fprogB c.MP' (projectiveOps c.sl)))) s fun t =>
      Scr t base size ∧ Unch base (slW c projectiveAllW) s.mem t.mem ∧
      sv c base t MN = c.C.p - c.C.n ∧ sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - Fin.ofNat c.C.p (sv c base s K) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (Fin.ofNat c.C.p (sv c base s K) + Fin.ofNat c.C.p c.C.n) * tmv c.C c.n base s (c.sl RZ) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (projectivePrepare_ok hc hs) fun s₁ ⟨hs₁,U₁,xm₁,acc₁,mn₁⟩ => ?_)
  have v₁ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → sv c base s₁ i = sv c base s i :=
    fun hi hl => sv_unch U₁ h7 hn hi (apart_slW hl)
  have M₁ : ModOkA c.MP' size c.C.p s₁.mem base := modP_of hc
    ((v₁ (i := MP) (by decide) (by decide)).trans hmp)
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) h7 hs₁ M₁ (MP'_A c) (o := XM) (a := K) (b := XM)
    (by decide) (by decide) (by decide) (by rw [xm₁]; exact Nat.mod_lt _ (by omega)))
    fun s₂ ⟨k₂,lt₂,e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i :=
    fun hi hio hit => sv_keep (MP'_n c) rfl h7 hn k₂ hi hio hit
  have M₂ := M₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have xm₂ : tmv c.C c.n base s₂ (c.sl XM) = Fin.ofNat c.C.p (sv c base s K) := by
    show toM _ _ (sv c base s₂ XM) = _
    rw [toM_r2 (A := sv c base s₁ K) hpR (by rw [e₂, xm₁]; rfl), v₁ (by decide) (by decide)]
  have acc₂ : tmv c.C c.n base s₂ (c.sl ACC) = Fin.ofNat c.C.p c.C.n := by
    show toM _ _ (sv c base s₂ ACC) = _
    rw [v₂ (by decide) (by decide) (by decide), acc₁]
    exact toM_cmont hc _
  have tv₂ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → i ≠ TMP →
      tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun {i} hi hl ht => by
    show toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [v₂ hi (fun he => hl (by rw [he]; decide)) ht, v₁ hi hl]
  refine WP.mono (projectiveOps_ok hc hs₂ M₂ (fun i hi => ?_)) fun s₃ ⟨hs₃,U₃,wlt,xnlt,wval,xnval⟩ => ?_
  · simp only [projectiveReads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact lt₂
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrz
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrx
    · rw [v₂ (by decide) (by decide) (by decide), acc₁]; exact Nat.mod_lt _ (by omega)
  have U₂ : Unch base (slW c [XM, TMP]) s₁.mem s₂.mem := k₂.unch
  have U : Unch base (slW c projectiveAllW) s.mem s₃.mem :=
    ((U₁.trans U₂).trans U₃).mono (by
      intro w hw
      simp only [slW, projectivePrepareW, projectiveWrites, projectiveAllW, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with ((h | h | h) | (h | h)) | (h | h | h | h | h | h) <;> simp [h])
  have mn₃ : sv c base s₃ MN = c.C.p - c.C.n := by
    have kept : sv c base s₃ MN = sv c base s₂ MN :=
      sv_unch U₃ h7 hn (i := MN) (by decide) (apart_slW (by decide))
    rw [kept, v₂ (by decide) (by decide) (by decide), mn₁]
  refine ⟨hs₃,U,mn₃,wlt,xnlt,?_,?_⟩
  · rw [wval, xm₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]
  · rw [xnval, xm₂, acc₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `ProjectiveFinal` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : FinalState c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.projectiveFinal c) s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .x0).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  let A := KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
    (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)
  let fx := tmv c.C c.n base s (c.sl RX)
  let fz := tmv c.C c.n base s (c.sl RZ)
  let xo := (fx * fz ^ (c.C.p - 2)).val
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  have v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slW hl)
  have saved := Saved.unch hP.fixed.saved (fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_ge64 c i) U
  have flag : word t.mem base (c.sl FLAG) = mask A := by
    rw [U.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
    · exact hP.flag
    · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
        (fun h => Or.inl (by have := hc.n0; omega)) Or.inr
  have wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  have z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,ret⟩ => ?_
  refine ⟨keep, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
  simp only [v (i := RZ) (by decide) (by decide), v (i := K) (by decide) (by decide), hP.k, mn, wz, xnz] at ret
  have iff : (A ∧ sv c base s RZ ≠ 0 ∧
      (fx = Fin.ofNat c.C.p (sigR c s₀) * fz ∨
        (sigR c s₀ < c.C.p - c.C.n ∧ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz))) ↔
      (A ∧ sv c base s RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mpr hm⟩
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mp hm⟩
  simpa only [iff] using ret

theorem tail_dispatch_ok (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : FinalState c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail c) s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.AArch64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .x0).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.AArch64.Cfg.tail
  split
  · rename_i h
    exact projectiveFinal_ok hc hC h.2.1 h.2.2 hP
  · exact tail_ok hc hP

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Main` -/

section

/-!
# ECDSA verification on AArch64: the whole function

`verify_ok`: `Cfg.verify` returns 1 exactly if the specification's
verification of the signature holds, for any curve the proof of the code
supports (`CfgOk`) whose group law the proofs support (`Law`), and
restores the callee-saved registers. `front_ok`, `mid_ok`, `points_ok` and
`tail_dispatch_ok` compute what `verify_eq` connects to the specification.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- The result the contract asks for: 1 exactly if the specification's
verification holds. -/
def VPost (c : Cfg) (s₀ s' : State) : Prop :=
  (s'.gpr .x0).setWidth 32 =
    if Spec.Ecdsa.verify c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) c.C.len))
      (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)) then 1 else 0

theorem verify_eq'' (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.verify c =
    .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c)
      (.seq c.nPow (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c)
      (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.points c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c))))))))) := rfl

/-- What the slot of Montgomery's one stands for. -/
theorem onep_tmv (hc : BaseCfgOk c) {base : Addr} {g : Reg → BitVec 64} {s : State}
    (F : Fixed c base g s.mem) : tmv c.C c.n base s (c.sl ONEP) = 1 := by
  show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = _
  rw [F.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem verify_ok (hc : CfgOk c) (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    {s₀ : State} (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.verify c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [verify_eq'']
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The point the window method multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hG : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
      (wordsVal s₂.mem (s₀.gpr .x3) (c.sl ONEP) c.n) = 1 from h1]
    exact rep_affine' hC _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  have hu : sv c (s₀.gpr .x3) s₂ U < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hv : sv c (s₀.gpr .x3) s₂ V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  refine points_ok hc hM
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ V >>> j) P))
    hC hT hp.tbl (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) hPc hQ
    (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP.toFinalState) fun s' ⟨saved, xo, hxo, hx, ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr), ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (s₀.gpr .x3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (s₀.gpr .x3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.AArch64

end
