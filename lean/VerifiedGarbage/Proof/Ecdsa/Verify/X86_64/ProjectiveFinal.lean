module
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Points
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.ProjectiveFlags
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Final
import VerifiedGarbage.Proof.Ecdsa.Projective

/-! ### `Ecdsa.Verify.X86_64.ProjectiveArithmetic`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Impl.Ecdsa.Verify.X86_64.Cfg (projectiveOps)
variable {c : VG.Impl.Ecdsa.X86_64.Cfg}

abbrev projectiveSlots : List Nat := [X, XM, RZ, W, RX, ACC, XN]
abbrev projectiveReads : List Nat := [XM, RZ, RX, ACC]
abbrev projectiveWrites : List Nat := [X, W, XM, X, XN, TMP]

theorem projectiveOps_rename (sl : Nat → Nat) :
    projectiveOps sl = (projectiveOps id).map (FOp.rename sl) := rfl

theorem projectiveOps_run (hc : BaseCfgOk c) (e : Nat → Fe c.C) :
    runOps (projectiveOps c.sl) e (c.sl W) = e (c.sl RX) - e (c.sl XM) * e (c.sl RZ) ∧
    runOps (projectiveOps c.sl) e (c.sl XN) =
      e (c.sl RX) - (e (c.sl XM) + e (c.sl ACC)) * e (c.sl RZ) := by
  obtain H := runOps_rename c.sl (projectiveOps id) e (fun _ _ _ h => sl_inj c hc.n0 h)
  rw [← projectiveOps_rename] at H
  exact ⟨congrFun H W, congrFun H XN⟩

/-- The five field operations compute both projective differences. -/
theorem projectiveOps_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ projectiveReads, sv c base s i < c.C.p) :
    WP isa (fprogB c.MP' (projectiveOps c.sl)).inline s fun t =>
      Scr t base size ∧ Unch base (slW c projectiveWrites) s.mem t.mem ∧
      sv c base t W < c.C.p ∧ sv c base t XN < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t W) =
        tmv c.C c.n base s (c.sl RX) - tmv c.C c.n base s (c.sl XM) * tmv c.C c.n base s (c.sl RZ) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t XN) =
        tmv c.C c.n base s (c.sl RX) -
          (tmv c.C c.n base s (c.sl XM) + tmv c.C c.n base s (c.sl ACC)) * tmv c.C c.n base s (c.sl RZ) := by
  obtain hL : Lay c.MP' size (· ∈ projectiveSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain I : Inv c.MP' base size c.C.p (· ∈ projectiveSlots.map c.sl) (projectiveReads.map c.sl)
      (tmv c.C c.n base s) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ projectiveReads, i ∈ projectiveSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  obtain reads : readsOk (projectiveOps c.sl) (projectiveReads.map c.sl) = true := by
    rw [projectiveOps_rename]
    exact readsOk_rename c.sl (by decide)
  refine (WP.mono (fprogB_ok hL (unitMod_pow_two hc.p_odd _) _ I ?_ reads)
    fun t ⟨keep, It⟩ => ?_)
  · intro op hop x hx
    simp only [projectiveOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by decide)
  obtain w : c.sl W ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  obtain xn : c.sl XN ∈ validAfter (projectiveOps c.sl) (projectiveReads.map c.sl) := by
    simp [mem_validAfter, projectiveOps, FOp.out]
  obtain run := projectiveOps_run hc (tmv c.C c.n base s)
  exact ⟨It.scr, keep.unch, It.lt _ w, It.lt _ xn, (It.val _ w).trans run.1, (It.val _ xn).trans run.2⟩


abbrev projectivePrepareW : List Nat := [XM, ACC, MN]
abbrev projectiveAllW : List Nat := [XM, ACC, MN, X, W, XN, TMP]

theorem projectivePrepare_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.X86_64.Cfg.projectivePrepare c)) s fun t =>
      Scr t base size ∧ Unch base (slW c projectivePrepareW) s.mem t.mem ∧
      sv c base t XM = c.R * c.R % c.C.p ∧ sv c base t ACC = c.mont c.C.n ∧
      sv c base t MN = c.C.p - c.C.n := by
  have hp := hc.p_ge
  have hpR := hc.p_lt
  obtain r2 : c.R * c.R % c.C.p < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) hpR
  obtain mont : c.mont c.C.n < 2 ^ (64 * c.n) :=
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) hpR
  obtain sub : c.C.p - c.C.n < 2 ^ (64 * c.n) := by omega_using [hpR]
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.projectivePrepare, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs (o := XM) (by decide) r2) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setSl_ok hc hs₁ (o := ACC) (by decide) mont) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setSl_ok hc hs₂ (o := MN) (by decide) sub) fun s₃ ⟨e₃,k₃,O₃⟩ => ?_
  obtain o : ∀ {s t : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem t.mem → i < 45 → i ≠ j →
      sv c base t i = sv c base s i := fun O hi hij => sv_out O hc.n10 hs.nowrap hi hij
  exact ⟨hs₂.of_keepRegs k₃ (by decide), O₁.unch.trans (O₂.unch.trans O₃.unch),
    by rw [o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁],
    by rw [o O₃ (by decide) (by decide), e₂], e₃⟩

/-- Prepare constants, convert `r`, and compute both differences. -/
theorem projectiveArithmetic_ok (hc : BaseCfgOk c) {s : State} {base : Addr}
    (hs : Scr s base size) (hmp : sv c base s MP = c.C.p)
    (hrx : sv c base s RX < c.C.p) (hrz : sv c base s RZ < c.C.p) :
    WP isa (Code.seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.projectivePrepare c))
      (.seq (.block (mul c.MP' (c.sl XM) (c.sl K) (c.sl XM)))
        (fprogB c.MP' (projectiveOps c.sl)))).inline s fun t =>
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
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (projectivePrepare_ok hc hs) fun s₁ ⟨hs₁,U₁,xm₁,acc₁,mn₁⟩ => ?_)
  obtain v₁ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → sv c base s₁ i = sv c base s i :=
    fun hi hl => sv_unch U₁ h7 hn hi (apart_slW hl)
  obtain M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc
    ((v₁ (i := MP) (by decide) (by decide)).trans hmp)
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) rfl rfl h7 hs₁ M₁ (o := XM) (a := K) (b := XM)
    (by decide) (by decide) (by decide) (by decide) (by rw [xm₁]; exact Nat.mod_lt _ (by omega_using [hrx])))
    fun s₂ ⟨k₂,lt₂,e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i :=
    fun hi hio hit => sv_keep (MP'_n c) rfl h7 hn k₂ hi hio hit
  obtain M₂ := M₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain xm₂ : tmv c.C c.n base s₂ (c.sl XM) = Fin.ofNat c.C.p (sv c base s K) := by
    show toM _ _ (sv c base s₂ XM) = _
    rw [toM_r2 (A := sv c base s₁ K) hpR (by rw [e₂, xm₁]; rfl), v₁ (by decide) (by decide)]
  obtain acc₂ : tmv c.C c.n base s₂ (c.sl ACC) = Fin.ofNat c.C.p c.C.n := by
    show toM _ _ (sv c base s₂ ACC) = _
    rw [v₂ (by decide) (by decide) (by decide), acc₁]
    exact toM_cmont hc _
  obtain tv₂ : ∀ {i}, i < 45 → i ∉ projectivePrepareW → i ≠ TMP →
      tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun {i} hi hl ht => by
    show toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [v₂ hi (fun he => hl (by rw [he]; decide)) ht, v₁ hi hl]
  refine WP.mono (projectiveOps_ok hc hs₂ M₂ (fun i hi => ?_)) fun s₃ ⟨hs₃,U₃,wlt,xnlt,wval,xnval⟩ => ?_
  · simp only [projectiveReads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact lt₂
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrz
    · rw [v₂ (by decide) (by decide) (by decide), v₁ (by decide) (by decide)]; exact hrx
    · rw [v₂ (by decide) (by decide) (by decide), acc₁]; exact Nat.mod_lt _ (by omega_using [hrx])
  have U₂ : Unch base (slW c [XM, TMP]) s₁.mem s₂.mem := k₂.unch
  obtain U : Unch base (slW c projectiveAllW) s.mem s₃.mem :=
    ((U₁.trans U₂).trans U₃).mono (by
      intro w hw
      simp only [slW, projectivePrepareW, projectiveWrites, projectiveAllW, List.map_cons, List.map_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with ((h | h | h) | (h | h)) | (h | h | h | h | h | h) <;> simp [h])
  obtain mn₃ : sv c base s₃ MN = c.C.p - c.C.n := by
    obtain kept : sv c base s₃ MN = sv c base s₂ MN :=
      sv_unch U₃ h7 hn (i := MN) (by decide) (apart_slW (by decide))
    rw [kept, v₂ (by decide) (by decide) (by decide), mn₁]
  refine ⟨hs₃,U,mn₃,wlt,xnlt,?_,?_⟩
  · rw [wval, xm₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]
  · rw [xnval, xm₂, acc₂, tv₂ (by decide) (by decide) (by decide), tv₂ (by decide) (by decide) (by decide)]

end VG.Proof.Ecdsa.Verify.X86_64

end

end


@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
variable {c : VG.Impl.Ecdsa.X86_64.Cfg}

/-- The final public comparison needs the canonical X/Z fields and the saved verifier inputs. -/
structure ProjectiveInput (c : VG.Impl.Ecdsa.X86_64.Cfg) (s₀ : State) (base : Addr)
    (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s base size
  fixed : Fixed c base g s.mem
  k : sv c base s K = sigR c s₀
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rx_lt : sv c base s RX < c.C.p
  rz_lt : sv c base s RZ < c.C.p

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_fields_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hP : ProjectiveInput c s₀ base g s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  let A := KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
    (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)
  let fx := tmv c.C c.n base s (c.sl RX)
  let fz := tmv c.C c.n base s (c.sl RZ)
  let xo := (fx * fz ^ (c.C.p - 2)).val
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal]
  refine WP.seq (WP.mono (projectiveArithmetic_ok hc hP.scr hP.fixed.mp hP.rx_lt hP.rz_lt)
    fun t ⟨ht,U,mn,wlt,xnlt,wval,xnval⟩ => ?_)
  obtain v : ∀ {i}, i < 45 → i ∉ projectiveAllW → sv c base t i = sv c base s i :=
    fun hi hl => sv_unch U h7 hn hi (apart_slW hl)
  obtain saved := Saved.unch hP.fixed.saved (fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    show 48 ≤ c.sl i
    rw [sl_eq']; omega_using []) U
  obtain flag : word t.mem base (c.sl FLAG) = mask A := by
    rw [U.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega_using [h0, hn, this])]
    · exact hP.flag
    · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
        (fun h => Or.inl (by have := hc.n0; omega_using [h0, h])) Or.inr
  obtain wz : sv c base t W = 0 ↔ fx = Fin.ofNat c.C.p (sigR c s₀) * fz := by
    rw [← toM_eq_zero_iff hpR wlt, wval, hP.k]
    change fx - Fin.ofNat c.C.p (sigR c s₀) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  obtain xnz : sv c base t XN = 0 ↔ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz := by
    rw [← toM_eq_zero_iff hpR xnlt, xnval, hP.k]
    change fx - (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz = 0 ↔ _
    constructor <;> intro h <;> grind
  obtain z : fz ≠ 0 ↔ sv c base s RZ ≠ 0 := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  refine WP.mono (projectiveChecks_ok hc ht saved A flag) fun s' ⟨keep,ret⟩ => ?_
  refine ⟨keep, xo, (fx * fz ^ (c.C.p - 2)).isLt, Fin.ofNat_val_eq_self _, ?_⟩
  simp only [v (i := RZ) (by decide) (by decide), v (i := K) (by decide) (by decide), hP.k, mn, wz, xnz] at ret
  obtain iff : (A ∧ sv c base s RZ ≠ 0 ∧
      (fx = Fin.ofNat c.C.p (sigR c s₀) * fz ∨
        (sigR c s₀ < c.C.p - c.C.n ∧ fx = (Fin.ofNat c.C.p (sigR c s₀) + Fin.ofNat c.C.p c.C.n) * fz))) ↔
      (A ∧ sv c base s RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mpr hm⟩
    · rintro ⟨ha,hz,hm⟩
      exact ⟨ha,hz,(Proof.Ecdsa.projective_matches hC hnp hpn (z.mpr hz) ha.2.1.2).mp hm⟩
  simpa only [iff] using ret

/-- The inversion-free final check has the same result as affine conversion. -/
theorem projectiveFinal_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnp : c.C.n < c.C.p)
    (hpn : c.C.p ≤ 2 * c.C.n) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {u v : Nat} {P : Point c.C} {s : State} (hP : Pts c s₀ base g u v P s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.projectiveFinal c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 :=
  projectiveFinal_fields_ok hc hC hnp hpn ⟨hP.scr,hP.fixed,hP.k,hP.flag,hP.rx_lt,hP.rz_lt⟩

theorem tail_dispatch_ok (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {u v : Nat} {P : Point c.C} {s : State} (hP : Pts c s₀ base g u v P s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.tail c).inline s fun s' =>
      (∀ r ∈ VG.Impl.Ecdsa.X86_64.Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        (s'.gpr .rax).setWidth 32 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  unfold Impl.Ecdsa.Verify.X86_64.Cfg.tail
  split
  · rename_i h
    exact projectiveFinal_ok hc hC h.2.1 h.2.2 hP
  · show WP isa (Code.seq c.pPow.inline (Impl.Ecdsa.Verify.X86_64.Cfg.final c).inline) s _
    exact tail_ok hc hP

end VG.Proof.Ecdsa.Verify.X86_64
