import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# Windows in Jacobian coordinates on x86-64: the table

As `build_ok` (`Window.lean`), but each entry `[m]P` stored in Jacobian
coordinates (`toJ`, through `R`), a triple whose `(XZ : Y : Z³)` represents
it (`RepJ`): which needs `[m]P ≠ O` for `m ≤ 8` (`buildJ_ok`). The entries
are stored from `R` (`storeEntryOf_ok`, as `storeEntry_ok` from `D`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The slots the Jacobian window method's field programs use are apart:
`toJ` from `E` and `D` into `R`, the doublings between `R` and `D`, and
`fromJ` from `R` and `E` into `D` (`z` the slots of zero). -/
theorem _root_.VG.Proof.Weierstrass.WinLay.rcbApart_winJ {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    RcbApart K.S K.E ⟨K.zero, K.zero, K.zero⟩ K.R ∧ RcbApart K.S K.D ⟨K.zero, K.zero, K.zero⟩ K.R ∧
      RcbApart K.S K.R K.R K.D ∧ RcbApart K.S K.D K.D K.R ∧
      RcbApart K.S K.R ⟨K.zero, K.zero, K.zero⟩ K.D ∧ RcbApart K.S K.E ⟨K.zero, K.zero, K.zero⟩ K.D := by
  have hnd := hL.nodup
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  have hz := hL.ro K.zero (by simp [winRo])
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd ha hb hz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [rcbW, rcbR, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, forall_eq_or_imp, forall_eq] <;> grind

/-- What a copy from `src` (slots written but the table's) into entry `m` of
the table needs. -/
theorem copySrc_tbl {K : WinCfg} {size : Nat} (hL : WinLay K size) {src : Pt}
    (hsrc : ∀ y ∈ [src.x, src.y, src.z], y ∈ winOther K) {m : Nat} (hm1 : 1 ≤ m) (hm8 : m ≤ 8) :
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, src.x, src.y, src.z], x + 8 * K.M.n ≤ size) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z],
      ∀ y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, src.x, src.y, src.z], x ≠ y →
        x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x) ∧
    (∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], x ∉ [src.x, src.y, src.z]) ∧
    ((K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z) := by
  have st := tblPt_slots K hm1 hm8
  have sl : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z, src.x, src.y, src.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [src.x, src.y, src.z] by simpa using hx) with h | h
    · exact (st x h).1
    · exact winOther_mem (hsrc x h)
  have td : ∀ x ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z], ∀ y ∈ [src.x, src.y, src.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hm1 hm8 x hx
    exact (hL.tbl_apart (List.mem_append_right _ (hsrc y hy)) hi).symm
  have ne : (K.tblPt m).x ≠ (K.tblPt m).y ∧ (K.tblPt m).x ≠ (K.tblPt m).z ∧ (K.tblPt m).y ≠ (K.tblPt m).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega), hL.tbl_ne₂ (by omega)⟩
  refine ⟨fun x hx => hL.lay.le x (sl x hx), fun x hx y hy hxy => ?_, fun x hx hy => ?_, ne⟩
  · rcases List.mem_append.mp (show y ∈ [(K.tblPt m).x, (K.tblPt m).y, (K.tblPt m).z] ++
      [src.x, src.y, src.z] by simpa using hy) with h | h
    · exact hL.apart₂ (st x hx).2 (st y h).2 hxy
    · exact td x hx y h
  · have := td x hx x hy
    have := hL.n0
    omega

/-- `src` into entry `8 - i` of the table, for `rbx = i ≤ j ≤ 6`. -/
theorem storeEntryOf_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) {src : Pt}
    (hsrc : ∀ y ∈ [src.x, src.y, src.z], y ∈ winOther K) {base : Addr} {i : Nat} :
    ∀ (j : Nat) {s : State}, i ≤ j → j ≤ 6 → Scr s base size → s.gpr .rbx = BitVec.ofNat 64 i →
      WP isa (WinCfg.storeEntryOf K src j) s fun t =>
        wordsVal t.mem base (K.tblPt (8 - i)).x K.M.n = wordsVal s.mem base src.x K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).y K.M.n = wordsVal s.mem base src.y K.M.n ∧
        wordsVal t.mem base (K.tblPt (8 - i)).z K.M.n = wordsVal s.mem base src.z K.M.n ∧
        KeepRegs [.rax] s t ∧
        Unch base [((K.tblPt (8 - i)).x, 8 * K.M.n), ((K.tblPt (8 - i)).y, 8 * K.M.n),
          ((K.tblPt (8 - i)).z, 8 * K.M.n)] s.mem t.mem
  | 0, s, hi, _, hs, _ => by
    obtain rfl : i = 0 := by omega
    rw [WinCfg.storeEntryOf]
    obtain ⟨a, c, d, e⟩ := copySrc_tbl hL hsrc (m := 8) (by decide) (Nat.le_refl _)
    exact copyPt_ok hs a c d e
  | j + 1, s, hi, hj, hs, hb => by
    rw [WinCfg.storeEntryOf]
    refine WP.seq (WP.mono (cmpRbx_ok s (j := i) (i := j + 1) (by omega) (by omega) hb)
      fun t ⟨ev, kt⟩ => ?_)
    have hst := hs.of_keeps kt (by decide)
    have mt : t.mem = s.mem := kt.2.1
    have kt' : KeepRegs [.rax] s t := (Keeps.regs kt).mono fun r hr => by simp at hr
    refine WP.ite _ ev (fun he => ?_) (fun he => ?_)
    · obtain rfl : i = j + 1 := of_decide_eq_true he
      obtain ⟨a, c, d, e⟩ := copySrc_tbl hL hsrc (m := 7 - j) (by omega) (by omega)
      rw [show 8 - (j + 1) = 7 - j by omega]
      exact WP.mono (copyPt_ok hst a c d e) fun u ⟨e1, e2, e3, k, U⟩ =>
        ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k, by rw [← mt]; exact U⟩
    · have hne : i ≠ j + 1 := of_decide_eq_false he
      exact WP.mono (storeEntryOf_ok hL hsrc j (by omega) (by omega) hst ((kt.1 _ (by decide)).trans hb))
        fun u ⟨e1, e2, e3, k, U⟩ => ⟨by rw [e1, mt], by rw [e2, mt], by rw [e3, mt], kt'.trans k,
          by rw [← mt]; exact U⟩

/-- The table's invariant in Jacobian coordinates: entries `[1 … m]P` built. -/
structure BuildInvJ (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOkR K C base (RepJ C) P m s

/-- The table's entries `[1 … m]P` in Jacobian coordinates, `E = [m]P`, and
`rbx = 8 - m`. -/
structure BuildInvJE (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (m : Nat) (s : State) : Prop where
  inv : BuildInvJ K C base size P s₀ m s
  lt : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) (mul m P)
  rbx : s.gpr .rbx = BitVec.ofNat 64 (8 - m)

/-- A table slot is apart from what the loop's field programs write. -/
theorem tbl_apart_loopW {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    {x : Nat} (hx : x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z]) :
    ∀ w ∈ loopW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hj1 hj8 x hx
  intro w hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
  · exact hL.lay.tmp _ (by simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

/-- The slots of a point, written. -/
theorem pt_other {K : WinCfg} {p : Pt} (h : p = K.R ∨ p = K.E ∨ p = K.D) :
    ∀ x ∈ [p.x, p.y, p.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases h with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> win_mem

/-- An entry of the table: `D = E + P` (`[m + 1]P`), `E = D`, and `D` in
Jacobian coordinates into entry `m + 1`. -/
theorem buildStepJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixed K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) (hne : mul (m + 1) P ≠ .infinity) {s : State} (hI : BuildInvJE K C base size P s₀ m s) :
    WP isa (WinCfg.buildStepJ K) s fun s' =>
      BuildInvJE K C base size P s₀ (m + 1) s' ∧ s'.zf = some (decide (8 - (m + 1) = 0)) := by
  have hn := hI.inv.scr.nowrap
  rw [WinCfg.buildStepJ]
  refine WP.seq (WP.mono (decRbx_ok s (j := 8 - m) (by omega_using [h1, h7]) (by omega_using [h1, h7]) hI.rbx) fun s₁ ⟨x₁, k₁⟩ => ?_)
  have hs₁ := hI.inv.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have tb : tmv C K.M.n base s₁ K.S.b3 = Fin.ofNat C.p C.b := by
    show toM _ _ _ = _; rw [m₁, winRo_val hL hI.inv.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s₁.mem base x K.M.n < C.p := fun x hx => by
    rw [m₁, winRo_val hL hI.inv.unch hn hx]; exact hF.ro_lt x hx
  have tP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx; show toM _ _ _ = toM _ _ _; rw [m₁, winRo_val hL hI.inv.unch hn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])]
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> win_mem
  have hlt : ∀ x ∈ rcbR K.S K.E K.P, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
  have hI₁ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.E K.P) (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, by rw [m₁]; exact hI.inv.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt,
      fun _ _ => rfl⟩
  have W := rcb3_ok hL.lay hp hL.rcbApart_EP hO hI₁ (fun x hx => hx)
  refine WP.seq ((fprogB_wp _ _).mpr (WP.mono W fun s₂ ⟨k₂, I₂, v₂⟩ => ?_))
  -- `D` is `[m + 1]P`.
  have hox : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have hoz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.E K.P := by simp
  have dlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact I₂.lt _ hox
    · exact I₂.lt _ hoy
    · exact I₂.lt _ hoz
  have dRep : Rep C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (m + 1) P) := by
    have hS : (tmv C K.M.n base s₂ K.D.x, tmv C K.M.n base s₂ K.D.y, tmv C K.M.n base s₂ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd3 (tmv C K.M.n base s₁ K.S.b3)
          (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
          (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y) (tmv C K.M.n base s₁ K.P.z) := by
      rw [← v₂]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₂.val _ hox, I₂.val _ hoy, I₂.val _ hoz]
    rw [tb, tP K.P.x (by simp), tP K.P.y (by simp), tP K.P.z (by simp)] at hS
    have hE : Rep C (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
        (mul m P) := by
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _; rw [m₁]; exact hI.rep
    have hPr : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y)
        (tmv C K.M.n base s₀ K.P.z) (mul 1 P) := by rw [mul_one_pt]; exact hF.pt
    have hR := hC.add3 hM3 (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) hE hPr hS.symm
    rw [hC.add_mul_mul hP] at hR
    exact hR
  have hs₂ := k₂.scr hs₁
  have U₂ : Unch base (loopW K) s₁.mem s₂.mem := k₂.unch.mono fun w hw => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, List.mem_append_right _ hy, rfl⟩
    · exact Or.inr rfl
  -- `E = D`.
  have eO : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain ⟨-, -, -, -, exy, exz, eyz, hED, -, -⟩ := hL.other_ne
  have hEd : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ [K.D.x, K.D.y, K.D.z] := by
    intro x hx hd
    refine hED x hx (List.mem_cons_of_mem _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [rcbW]
  refine WP.seq (WP.mono (copyPt_ok hs₂ (o := K.E) (a := K.D) (n := K.M.n)
    (fun x hx => hL.lay.le x (winOther_mem (eO x hx)))
    (fun x hx y hy hxy => hL.apart₂ (winOther_ws K x (eO x (by simp at hx ⊢; omega_using [hx])))
      (winOther_ws K y (eO y hy)) hxy) hEd ⟨exy, exz, eyz⟩) fun s₃ ⟨e1, e2, e3, k₃, U₃⟩ => ?_)
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [this, hn]
  have dE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (by simp at hx ⊢; omega_using [hx]))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxE : ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := fun y hy hxy => hEd y hy (hxy ▸ hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only <;>
      exact hL.apart₂ (winOther_ws K x (eO x (by simp at hx ⊢; omega_using [hx])))
        (winOther_ws K _ (eO _ (by simp))) (hxE _ (by simp))
  have U₃' : Unch base (loopW K) s₂.mem s₃.mem := U₃.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
  have hM₃ : ModOkW K.M size C.p s₃.mem base :=
    (k₂.scr hs₁ |> fun _ => I₂.mod).unch U₃' (fun w hw => winW_mo hL I₂.mod w (loopW_sub K w hw)) hn
  -- `D` into Jacobian coordinates, in `R`.
  obtain ⟨-, aDR, -, -, -, -⟩ := hL.rcbApart_winJ
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  have w4 := winJ_sl oR (fun x hx => winOther_mem (oD x hx)) sZ
  let V := [K.S.a, K.S.b3, K.zero, K.D.x, K.D.y, K.D.z, K.E.x, K.E.y, K.E.z]
  have hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by
    have := hL.ro_w (x := K.zero) (by simp [winRo])
    rw [U₃'.wordsVal (fun w hw => this w (loopW_sub K w hw)) (b64 _ (by win_mem)),
      U₂.wordsVal (fun w hw => this w (loopW_sub K w hw)) (b64 _ (by win_mem)), m₁,
      winRo_val hL hI.inv.unch hn (by simp [winRo])]
    exact hF.zero
  have V3 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (dlt _ (by simp : K.D.x ∈ _))
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    have ra : ∀ y ∈ [K.S.a, K.S.b3], wordsVal s₃.mem base y K.M.n < C.p := by
      intro y hy
      have hro : y ∈ winRo K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [winRo]
      have := hL.ro_w hro
      rw [U₃'.wordsVal (fun w hw => this w (loopW_sub K w hw)) (b64 _ (winRo_slots K _ hro)),
        U₂.wordsVal (fun w hw => this w (loopW_sub K w hw)) (b64 _ (winRo_slots K _ hro))]
      exact ro_lt y hro
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_mem, ra _ (by simp)⟩
    · exact ⟨by win_mem, ra _ (by simp)⟩
    · exact ⟨by win_mem, by rw [hz₃]; exact hp0⟩
    · exact ⟨by win_mem, by rw [dE _ (by simp)]; exact dlt _ (by simp)⟩
    · exact ⟨by win_mem, by rw [dE _ (by simp)]; exact dlt _ (by simp)⟩
    · exact ⟨by win_mem, by rw [dE _ (by simp)]; exact dlt _ (by simp)⟩
    · exact ⟨by win_mem, by rw [e1]; exact dlt _ (by simp)⟩
    · exact ⟨by win_mem, by rw [e2]; exact dlt _ (by simp)⟩
    · exact ⟨by win_mem, by rw [e3]; exact dlt _ (by simp)⟩
  have I₃ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, hM₃, fun x hx => (V3 x hx).1, fun x hx => (V3 x hx).2, fun _ _ => rfl⟩
  rw [toJ_eq]
  refine WP.seq (WP.mono (winN_ok hL hp toJN_ok aDR w4.1 w4.2 I₃ (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
    fun s₄ ⟨k₄, U₄, E₄, I₄, o₄, v₄⟩ => ?_)
  have hs₄ := I₄.scr
  have J₄ : RepJ C (E₄ K.R.x) (E₄ K.R.y) (E₄ K.R.z) (mul (m + 1) P) := by
    refine RepJ.of_toJ (z := tmv C K.M.n base s₃ K.zero) hC (X := tmv C K.M.n base s₃ K.D.x)
      (Y := tmv C K.M.n base s₃ K.D.y) (Z := tmv C K.M.n base s₃ K.D.z) ?_ hne
      (show toM _ _ _ = 0 by rw [hz₃]; exact toM_zero _ _) (v₄.trans (toJN_run _))
    have e : ∀ x ∈ [K.D.x, K.D.y, K.D.z], tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [dE x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact dRep
  have x₄ : s₄.gpr .rbx = BitVec.ofNat 64 (7 - m) := by
    rw [k₄.gpr _ (rbx_not_clob _), k₃.gpr _ (by decide), k₂.gpr _ (rbx_not_clob _), x₁]
    congr 1; omega_using [h1, h7]
  -- `R` into entry `m + 1`.
  refine WP.seq (WP.mono (storeEntryOf_ok hL oR (i := 7 - m) 6 (by omega_using [h1, h7]) (Nat.le_refl _) hs₄ x₄)
    fun s₅ ⟨f1, f2, f3, k₅, U₅⟩ => ?_)
  rw [show 8 - (7 - m) = m + 1 by omega_using [h1, h7]] at f1 f2 f3 U₅
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have x₅ : s₅.gpr .rbx = BitVec.ofNat 64 (7 - m) := by rw [k₅.gpr _ (by decide), x₄]
  refine WP.mono (testRbx_ok s₅ (j := 7 - m) (by omega_using [h1, h7]) x₅) fun s₆ ⟨z₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  have sT := tblPt_slots K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7])
  have U₅' : Unch base ((winWs K).map (·, 8 * K.M.n)) s₄.mem s₅.mem := U₅.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_map]
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, (sT _ (by simp)).2, rfl⟩
    · exact ⟨_, (sT _ (by simp)).2, rfl⟩
    · exact ⟨_, (sT _ (by simp)).2, rfl⟩
  -- What stays: `E` (apart from the entry).
  have tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₅.mem base x K.M.n = wordsVal s₄.mem base x K.M.n := by
    intro x hx
    refine U₅.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (by simp at hx ⊢; omega_using [hx]))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x (by simp at hx ⊢; omega_using [hx]))
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  have hEV : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ [K.R.x, K.R.y, K.R.z] ++ V := by
    intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
      List.nil_append] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ [K.R.x, K.R.y, K.R.z] ++ V := fun x hx =>
    List.mem_append_left _ hx
  -- `E` kept by `toJ`, which writes `R` and the temporaries.
  have eE4 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], E₄ x = tmv C K.M.n base s₃ x := by
    intro x hx
    refine o₄ x fun h => ?_
    obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at h
    have hD : ∀ y ∈ [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5], y ∈ K.neg :: rcbW K.S K.D := by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rcbW]
    have hR : ∀ y ∈ [K.R.x, K.R.y, K.R.z], x = y → False := by
      intro y hy e
      subst e
      refine hRo x hy (List.mem_append_left _ ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]
    rcases h with h | h | h | h | h | h | h | h | h
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hR _ (by simp) h
    · exact hR _ (by simp) h
    · exact hR _ (by simp) h
  -- What the step writes: `loopW` and the entry.
  have U : Unch base (winW K) s.mem s₆.mem := by
    rw [← m₁, m₆]
    refine ((U₂.trans (U₃'.trans U₄)).trans U₅').mono fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with (h | h | h) | h
    · exact loopW_sub K w h
    · exact loopW_sub K w h
    · exact loopW_sub K w h
    · exact List.mem_append_left _ h
  have keep : KeepRegs (powClob K.M.n) s s₆ := by
    have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
    exact ((Keeps.regs k₁).mono fun r hr => by simp at hr; simp [hr, powClob]).trans
      ((⟨fun r hr => k₂.gpr r fun h => hr (List.mem_cons_of_mem _ h), k₂.rd, k₂.wr⟩ :
        KeepRegs (powClob K.M.n) s₁ s₂).trans ((k₃.mono c1).trans ((k₄.mono clob_powClob).trans
          ((k₅.mono c1).trans ((Keeps.regs k₆).mono fun r hr => by simp at hr)))))
  have UU : Unch base (loopW K) s₁.mem s₄.mem := (U₂.trans (U₃'.trans U₄)).mono fun w hw => by
    simp only [List.mem_append] at hw
    rcases hw with h | h | h <;> exact h
  refine ⟨⟨⟨hs₅.of_keeps k₆ (by decide), hI.inv.keep.trans keep,
    (hI.inv.unch.trans U).mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hI.inv.mod.unch U (winW_mo hL hI.inv.mod) hn, fun j hj1 hjm => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · -- An entry built before keeps its numbers.
      have Tj := hI.inv.tbl j hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have sj := tblPt_slots K (m := j) hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          wordsVal s₆.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
        intro x hx
        rw [← m₁, m₆, U₅.wordsVal (fun w hw => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl | rfl <;>
              exact tbl_apart_entry (K := K) (m := m + 1) hj1 (by omega_using [h7, hj]) (by omega_using [h1, h7])
                (by omega_using [h1, h7]) (by omega_using [hj]) x hx _ (by simp))
            (b64 _ (sj _ hx).1),
          UU.wordsVal (tbl_apart_loopW hL hj1 (by omega_using [h7, hj]) hx) (b64 _ (sj _ hx).1)]
      refine ⟨fun x hx => by rw [e x hx]; exact Tj.1 x hx, ?_⟩
      have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          tmv C K.M.n base s₆ x = tmv C K.M.n base s x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
      exact Tj.2
    · obtain rfl : j = m + 1 := by omega_using [hjm, hj]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [m₆, f1]; exact I₄.lt _ (hRV _ (by simp))
        · rw [m₆, f2]; exact I₄.lt _ (hRV _ (by simp))
        · rw [m₆, f3]; exact I₄.lt _ (hRV _ (by simp))
      · show RepJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [m₆, f1, f2, f3, I₄.val _ (hRV _ (by simp)), I₄.val _ (hRV _ (by simp)),
          I₄.val _ (hRV _ (by simp))]
        exact J₄
  · intro x hx
    rw [m₆, tE x hx]; exact I₄.lt _ (hEV x hx)
  · have ev : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₆ x = tmv C K.M.n base s₃ x := by
      intro x hx
      show toM _ _ _ = _
      rw [m₆, tE x hx, I₄.val _ (hEV x hx), eE4 x hx]
    rw [ev _ (by simp), ev _ (by simp), ev _ (by simp)]
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [e1, e2, e3]; exact dRep
  · rw [k₆.1 _ (by decide), x₅]; congr 1; omega_using [h1, h7]
  · rw [z₆]; congr 1; simp only [decide_eq_decide]; omega_using [h1, h7]

/-- The table `[1 … 8]P` in Jacobian coordinates, for `P` whose multiples
up to `8` are not `O`. -/
theorem buildJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : WinFixed K C base s P k) :
    WP isa (WinCfg.buildJ K) s (BuildInvJ K C base size P s 8) := by
  have hn := hs.nowrap
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega)
  have pRo : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  have eO := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega
  rw [WinCfg.buildJ]
  -- `E = P`.
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  have eP : ∀ x ∈ [K.E.x, K.E.y, K.E.z], ∀ y ∈ [K.P.x, K.P.y, K.P.z], x ≠ y := fun x hx y hy h =>
    hL.ro y (pRo y hy) (h ▸ eO x hx)
  have slE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.E.x, K.E.y, K.E.z] ++ [K.P.x, K.P.y, K.P.z] by
      simpa using hx) with h | h
    · exact winOther_mem (eO x h)
    · exact winRo_slots K x (pRo x h)
  refine WP.seq (WP.mono (copyPt_ok hs (o := K.E) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slE x hx))
    (fun x hx y hy hxy => hL.lay.apart x y (slE x (by simp at hx ⊢; omega)) (slE y hy) hxy)
    (fun x hx h => eP x hx x h rfl) ⟨exy, exz, eyz⟩) fun s₁ ⟨c1, c2, c3, k₁, U₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁' : Unch base (loopW K) s.mem s₁.mem := U₁.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
    · exact Or.inl ⟨_, eO _ (by simp), rfl⟩
  have kP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    exact U₁'.wordsVal (fun w hw => hL.ro_w (pRo x hx) w (loopW_sub K w hw)) (b64 x (winRo_slots K x (pRo x hx)))
  have hM₁ : ModOkW K.M size C.p s₁.mem base := hM.unch U₁' (fun w hw => winW_mo hL hM w (loopW_sub K w hw)) hn
  -- `[1]P` in Jacobian coordinates, in `R`.
  obtain ⟨aER, -, -, -, -, -⟩ := hL.rcbApart_winJ
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  have w2 := winJ_sl oR (fun x hx => winOther_mem (eO x hx)) sZ
  have hz₁ : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [U₁'.wordsVal (fun w hw => hL.ro_w (x := K.zero) (by simp [winRo]) w (loopW_sub K w hw))
      (b64 _ (by win_mem))]
    exact hF.zero
  let V := [K.S.a, K.S.b3, K.zero, K.E.x, K.E.y, K.E.z]
  have V1 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    have ro : ∀ y ∈ winRo K, wordsVal s₁.mem base y K.M.n < C.p := fun y hy => by
      rw [U₁'.wordsVal (fun w hw => hL.ro_w hy w (loopW_sub K w hw)) (b64 _ (winRo_slots K _ hy))]
      exact hF.ro_lt y hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_mem, ro _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro _ (by simp [winRo])⟩
    · exact ⟨by win_mem, by rw [c1]; exact hF.ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, by rw [c2]; exact hF.ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, by rw [c3]; exact hF.ro_lt _ (by simp [winRo])⟩
  have I₁ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, hM₁, fun x hx => (V1 x hx).1, fun x hx => (V1 x hx).2, fun _ _ => rfl⟩
  rw [toJ_eq]
  refine WP.seq (WP.mono (winN_ok hL hp toJN_ok aER w2.1 w2.2 I₁ (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
    fun s₂ ⟨k₂, U₂, E₂, I₂, o₂, v₂⟩ => ?_)
  have hs₂ := I₂.scr
  have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ [K.R.x, K.R.y, K.R.z] ++ V := fun x hx =>
    List.mem_append_left _ hx
  have hEV : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ [K.R.x, K.R.y, K.R.z] ++ V := by
    intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
      List.nil_append] at hx ⊢
    rcases hx with rfl | rfl | rfl <;> simp
  have J₂ : RepJ C (E₂ K.R.x) (E₂ K.R.y) (E₂ K.R.z) (mul 1 P) := by
    refine RepJ.of_toJ (z := tmv C K.M.n base s₁ K.zero) hC (X := tmv C K.M.n base s₁ K.E.x)
      (Y := tmv C K.M.n base s₁ K.E.y) (Z := tmv C K.M.n base s₁ K.E.z) ?_ (hne 1 (Nat.le_refl _) (by decide))
      (show toM _ _ _ = 0 by rw [hz₁]; exact toM_zero _ _) (v₂.trans (toJN_run _))
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [c1, c2, c3, mul_one_pt]; exact hF.pt
  -- `[1]P` into its entry.
  obtain ⟨a, c, d, e⟩ := copySrc_tbl hL oR (m := 1) (Nat.le_refl _) (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₂ a c d e) fun s₃ ⟨f1, f2, f3, k₃, U₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (mov32Rbx_ok s₃ (j := 7) (by decide)) fun s₄ ⟨x₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  -- What stays: `E` (apart from the entry).
  have tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by decide) _ (by simp : (K.tblPt 1).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by decide) _ (by simp : (K.tblPt 1).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by decide) _ (by simp : (K.tblPt 1).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  have eE2 : ∀ x ∈ [K.E.x, K.E.y, K.E.z], E₂ x = tmv C K.M.n base s₁ x := by
    intro x hx
    refine o₂ x fun h => ?_
    obtain ⟨-, -, -, hRo, -, -, -, hED, -⟩ := hL.other_ne
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at h
    have hD : ∀ y ∈ [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5], y ∈ K.neg :: rcbW K.S K.D := by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rcbW]
    have hR : ∀ y ∈ [K.R.x, K.R.y, K.R.z], x = y → False := by
      intro y hy e
      subst e
      refine hRo x hy (List.mem_append_left _ ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]
    rcases h with h | h | h | h | h | h | h | h | h
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hED x hx (h ▸ hD _ (by simp))
    · exact hR _ (by simp) h
    · exact hR _ (by simp) h
    · exact hR _ (by simp) h
  have sT := tblPt_slots K (m := 1) (Nat.le_refl _) (by decide)
  have U : Unch base (winW K) s.mem s₄.mem := by
    rw [m₄]
    refine ((U₁'.trans U₂).trans U₃).mono fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with (h | h) | h
    · exact loopW_sub K w h
    · exact loopW_sub K w h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, (sT _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (sT _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (sT _ (by simp)).2, rfl⟩
  have c1' : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
  have I₄ : BuildInvJE K C base size P s 1 s₄ := by
    refine ⟨⟨hs₃.of_keeps k₄ (by decide), ((k₁.mono c1').trans (k₂.mono clob_powClob)).trans
      ((k₃.mono c1').trans ((Keeps.regs k₄).mono fun r hr => by simp at hr; simp [hr, powClob])),
      U, hM.unch U (winW_mo hL hM) hn, fun j hj1 hj => ?_⟩, fun x hx => ?_, ?_, by rw [x₄]⟩
    · obtain rfl : j = 1 := by omega
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [m₄, f1]; exact I₂.lt _ (hRV _ (by simp))
        · rw [m₄, f2]; exact I₂.lt _ (hRV _ (by simp))
        · rw [m₄, f3]; exact I₂.lt _ (hRV _ (by simp))
      · show RepJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [m₄, f1, f2, f3, I₂.val _ (hRV _ (by simp)), I₂.val _ (hRV _ (by simp)),
          I₂.val _ (hRV _ (by simp))]
        exact J₂
    · rw [m₄, tE x hx]; exact I₂.lt _ (hEV x hx)
    · have ev : ∀ x ∈ [K.E.x, K.E.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₁ x := by
        intro x hx
        show toM _ _ _ = _
        rw [m₄, tE x hx, I₂.val _ (hEV x hx), eE2 x hx]
      rw [ev _ (by simp), ev _ (by simp), ev _ (by simp)]
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [c1, c2, c3, mul_one_pt]
      exact hF.pt
  exact countLoop_ok (Inv := fun j t => BuildInvJE K C base size P s (8 - j) t) (n := 7)
    (fun j t h1 h2 hi => WP.mono (buildStepJ_ok hL hp hC hM3 hP hF (m := 8 - j) (by omega) (by omega)
      (hne _ (by omega) (by omega)) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show 8 - (j - 1) = 8 - j + 1 by omega]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega⟩)
    (fun t hi => hi.inv) (by decide) I₄

end VG.Proof.Weierstrass.X86_64
