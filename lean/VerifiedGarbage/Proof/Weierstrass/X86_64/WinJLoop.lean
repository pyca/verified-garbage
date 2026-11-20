module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.WindowJ
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJNorm
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Algebra.GroupWithZero.Nat
public import VerifiedGarbage.Proof.Weierstrass.Booth
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! ### `Weierstrass.X86_64.WinJStep`, which this module and modules that import it used -/

section

/-!
# Windows in Jacobian coordinates on x86-64: an iteration

`R = 16 R` in place in Jacobian coordinates (`quadJ_ok`: two pairs of
doublings between `R` and `D`), the masks of a point's `Z` being zero
(`zmask_ok`), and the mixed addition of the affine entry `E` into `D` with
the selection of `E`, `R` or `D` (`sumJ_ok`), for an iteration but the last
(`winStepJ_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- `x ∈ l₂` from `h : x ∈ l₁`, for literal lists with `l₁`'s elements in `l₂`: not by
`omega` on the disjunctions, which splits cases exponentially. -/
macro "sub_mem " h:term : tactic => `(tactic| plain_simp_names (
                   refine (show (_ : List _) ⊆ _ from ?_) $h
                   simp only [List.cons_subset, List.nil_subset, List.mem_cons, eq_self_iff_true, true_or,
                     or_true, and_true, and_self]))

/-- `R = 16 R` in Jacobian coordinates, in place: from `(X : Y : Z)` standing
for `[e]P` (or with `Z = 0`) to a triple standing for `[16 e]P`. -/
theorem quadJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadJ K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  obtain ⟨aRD, aDR, -⟩ := hL.rcbApart_winJ
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  obtain w2 := winJ_sl oD (sl _ oR) (sl _ oR)
  obtain w3 := winJ_sl oR (sl _ oD) (sl _ oD)
  let V := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]
  obtain V0 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
  obtain I₀ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  obtain hQ := fun (a : Nat) => hC.onCurve_mul hP a
  rw [WinCfg.quadJ]
  simp only [Code.inline]
  refine WP.seq (WP.mono (quadStart_ok s hb) fun s₂ ⟨b₂, kc₂⟩ => ?_)
  let LI := fun j st => WinStR K C base size Rp P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ E : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) V E st ∧
    InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul (4 ^ (2 - j) * e) P)
  obtain start : LI 2 s₂ := ⟨hS.rbxKeeps hL kc₂, b₂, _, I₀.rbxKeeps kc₂, by simpa using hR⟩
  obtain body : ∀ j st, 1 ≤ j → j ≤ 2 → LI j st →
      WP isa (WinCfg.jacPairOn K K.R K.D).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    simp only [WinCfg.jacPairOn, WinCfg.double, dblJXChoice_eq]
    refine WP.seq (WP.mono (winN_ok hL hp (dblJXChoiceN_ok (K.M.n ≤ 6 : Bool)) aRD w2.1 w2.2 I (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
      fun st₁ ⟨k₁', U₁', E₁', I₁', _, v₁'⟩ => ?_)
    obtain S₁' := S.next hL I₁'.scr (k₁'.mono clob_powClob) U₁'
    obtain J₁' := InvJ.dbl' hC hM3 (hQ _) J (v₁'.trans (dblJXChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₁'
    refine WP.seq (WP.mono (winN_ok hL hp (dblJXChoiceN_ok (K.M.n ≤ 6 : Bool)) aDR w3.1 w3.2 I₁' (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
        List.nil_append] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
      fun st₂ ⟨k₂', U₂', E₂', I₂', _, v₂'⟩ => ?_)
    obtain S₂' := S₁'.next hL I₂'.scr (k₂'.mono clob_powClob) U₂'
    obtain J₂' := InvJ.dbl' hC hM3 (hQ _) J₁' (v₂'.trans (dblJXChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₂'
    obtain ar : 2 * (2 * (4 ^ (2 - j) * e)) = 4 ^ (2 - (j - 1)) * e := by
      obtain hj12 : j = 1 ∨ j = 2 := by omega_using [hj, hj']
      rcases hj12 with rfl | rfl <;> simp <;> omega_using []
    rw [ar] at J₂'
    obtain b' : st₂.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) := by
      rw [k₂'.gpr _ (rbx_not_clob _), k₁'.gpr _ (rbx_not_clob _), b]
    refine WP.mono (quadCount_ok st₂ hi hj hj' b') fun st₃ ⟨b₃, c₃, kc₃⟩ => ?_
    obtain I₂'' : Inv K.M base size C.p (· ∈ winSlots K) V E₂' st₂ :=
      I₂'.sub (by
        intro x hx
        simp only [V, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with h | h | h | h | h | h <;> simp [h])
    exact ⟨⟨S₂'.rbxKeeps hL kc₃, b₃, E₂', I₂''.rbxKeeps kc₃, J₂'⟩, c₃⟩
  refine WP.mono (quadLoop_ok body (fun _ h => h) start) fun s₅ ⟨S₅, b₅, E₅, I₅, J₅⟩ => ?_
  obtain rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  obtain J₅ : InvJ C (E₅ K.R.x) (E₅ K.R.y) (E₅ K.R.z) (mul (16 * e) P) := by simpa using J₅
  obtain hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ V := by
    intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h <;> simp [h]
  refine ⟨S₅, rb₅, fun x hx => I₅.lt x (hRV x hx), ?_⟩
  show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
  rw [I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp))]
  exact J₅

/-! ## The mask of `Z = 0` -/

/-- The mask `rdx` of `[z] = 0`. -/
theorem zmask_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0 < K.M.n) {z : Nat} (ha : z + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.zmask K z)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base z K.M.n = 0) ∧ Keeps [.rdx] s s' := by
  rw [WinCfg.zmask, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc z))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base z ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := z) (by omega_using [hn, ha]),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := z) (K.M.n - 1) (by omega_using [hn, ha])) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  obtain hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base z K.M.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega_using [hj])
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega_using [hj])⟩
  rw [show ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) =
    [.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (zmCmp_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  refine WP.mono (zmSbb_ok s₃ c₃) fun s₄ ⟨e₄, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (fun _ h => absurd h List.not_mem_nil))).trans k₄⟩
  rw [e₄]
  simp only [mask, decide_eq_true_eq, hz]

/-- `o = b` if `c`, in place: `selPt n o o b`, for `o`'s words apart from
each other and from `b`'s. -/
theorem selPtA_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o o b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base o.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base o.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base o.z n) ∧
      KeepRegs [.rax, .rdx] s s' ∧
      Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs hc iox iox iax (Or.inl (Nat.le_refl _)) (by omega_using [xax]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n hs₁ (by rw [k₁.gpr _ (by decide), hc]) ioy ioy iay (Or.inl (Nat.le_refl _))
    (by omega_using [yay])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (sel_ok c n hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz ioz iaz
    (Or.inl (Nat.le_refl _)) (by omega_using [zaz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x hx => ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := o.y) (by omega_using [xy]) (by omega_using [ioy, hn]),
      O₁.wordsVal (d := b.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := o.z) (by omega_using [yz]) (by omega_using [ioz, hn]),
      O₂.wordsVal (d := b.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := o.z) (by omega_using [xz]) (by omega_using [ioz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · have h₁ := hx _ (List.mem_cons_self ..)
    obtain h₂ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain h₃ := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]

/-! ## The Jacobian sum, selected -/

/-- `rcx = rdx`. -/
theorem movRcxRdx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx)]) s fun t => t.gpr .rcx = s.gpr .rdx ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem toM_ite {m R : Nat} [NeZero m] (p : Prop) [Decidable p] (a b : Nat) :
    toM m R (if p then a else b) = if p then toM m R a else toM m R b := by
  split <;> rfl

/-- `R`, `E` and `D`: in the working space and apart, as the selection after
the sum needs. -/
theorem winRED_lay {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    ((K.D.x + 8 * K.M.n ≤ K.D.y ∨ K.D.y + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.x + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.y + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.y)) ∧
    ((K.R.x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.x + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.y + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.y)) ∧
    (∀ d ∈ [K.D.x, K.D.y, K.D.z], ∀ e ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) ∧
    (∀ d ∈ [K.R.x, K.R.y, K.R.z], ∀ e ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) := by
  -- The nine slots by index, apart by `Nodup` of a sublist (not by rewriting `Nodup` per pair).
  let L : List Nat := [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z]
  obtain sub : L.Sublist (winOther K) := by
    simp only [L, winOther, rcbW, List.cons_append, List.nil_append]
    repeat first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  obtain nd := sub.nodup hL.nodup
  obtain hw : ∀ x ∈ L, x ∈ winWs K := fun x hx => winOther_ws K x (sub.subset hx)
  obtain A : ∀ i j (hi : i < 9) (hj : j < 9), i ≠ j → L[i] + 8 * K.M.n ≤ L[j] ∨ L[j] + 8 * K.M.n ≤ L[i] :=
    fun i j hi hj h => hL.apart₂ (hw _ (List.getElem_mem _)) (hw _ (List.getElem_mem _))
      (fun e => h ((nd.getElem_inj (hi := hi) (hj := hj)).mp e))
  refine ⟨fun x hx => hL.lay.le _ (winWs_slots K _ (hw _ hx)),
    ⟨A 6 7 (by decide) (by decide) (by decide), A 6 8 (by decide) (by decide) (by decide),
      A 7 8 (by decide) (by decide) (by decide)⟩,
    ⟨A 0 1 (by decide) (by decide) (by decide), A 0 2 (by decide) (by decide) (by decide),
      A 1 2 (by decide) (by decide) (by decide)⟩, ?_, ?_⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 6 0 (by decide) (by decide) (by decide), A 6 1 (by decide) (by decide) (by decide),
        A 6 2 (by decide) (by decide) (by decide), A 6 3 (by decide) (by decide) (by decide),
        A 6 4 (by decide) (by decide) (by decide), A 6 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 7 0 (by decide) (by decide) (by decide), A 7 1 (by decide) (by decide) (by decide),
        A 7 2 (by decide) (by decide) (by decide), A 7 3 (by decide) (by decide) (by decide),
        A 7 4 (by decide) (by decide) (by decide), A 7 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 8 0 (by decide) (by decide) (by decide), A 8 1 (by decide) (by decide) (by decide),
        A 8 2 (by decide) (by decide) (by decide), A 8 3 (by decide) (by decide) (by decide),
        A 8 4 (by decide) (by decide) (by decide), A 8 5 (by decide) (by decide) (by decide)⟩⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 0 3 (by decide) (by decide) (by decide), A 0 4 (by decide) (by decide) (by decide),
        A 0 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 1 3 (by decide) (by decide) (by decide), A 1 4 (by decide) (by decide) (by decide),
        A 1 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 2 3 (by decide) (by decide) (by decide), A 2 4 (by decide) (by decide) (by decide),
        A 2 5 (by decide) (by decide) (by decide)⟩⟩

/-- The value `selSum` leaves in a coordinate of `R`: `E`'s where `R` is
`O` (`Z = 0`), else `R`'s where `E` is `O`, else `D`'s. -/
def selVal (m : Mem) (base : Addr) (K : WinCfg) (r e d : Nat) : Nat :=
  if wordsVal m base K.R.z K.M.n = 0 then wordsVal m base e K.M.n
  else if wordsVal m base K.E.z K.M.n = 0 then wordsVal m base r K.M.n else wordsVal m base d K.M.n

/-- `D = R` where `E` is `O`, then `R = E` where `R` is `O`, else `D`. -/
theorem selSum_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) :
    WP isa (.block (WinCfg.selSum K)) s fun s' =>
      wordsVal s'.mem base K.R.x K.M.n = selVal s.mem base K K.R.x K.E.x K.D.x ∧
      wordsVal s'.mem base K.R.y K.M.n = selVal s.mem base K K.R.y K.E.y K.D.y ∧
      wordsVal s'.mem base K.R.z K.M.n = selVal s.mem base K K.R.z K.E.z K.D.z ∧
      KeepRegs [.rax, .rcx, .rdx] s s' ∧ Unch base (loopW K) s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨le, aD, aR, dRE, rE⟩ := winRED_lay hL
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  rw [WinCfg.selSum]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zmask_ok K hs hL.n0 (le K.E.z (by simp))) fun s₂ ⟨m₂, k₂⟩ => ?_
  obtain hs₂ := hs.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRcxRdx_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain m₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (selPtA_ok hs₃ (decide (wordsVal s.mem base K.E.z K.M.n = 0))
    (by rw [c₃, m₂]; simp only [mask, decide_eq_true_eq]) (o := K.D) (b := K.R)
    (fun d hd => le d (by sub_mem hd))
    aD (fun d hd e he => dRE d hd e (by sub_mem he)))
    fun s₄ ⟨d4x, d4y, d4z, k₄, U₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [m₃] at d4x d4y d4z U₄
  obtain keepD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₄.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (by have := le x (by sub_mem hx); omega_using [hn, this])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> exact (dRE _ (by simp) x hx).symm
  rw [WP.block_append_iff]
  refine WP.mono (zmask_ok K hs₄ hL.n0 (le K.R.z (by simp))) fun s₅ ⟨m₅, k₅⟩ => ?_
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRcxRdx_ok s₅) fun s₆ ⟨c₆, k₆⟩ => ?_
  obtain hs₆ := hs₅.of_keeps k₆ (by decide)
  obtain m₆ : s₆.mem = s₄.mem := by rw [k₆.2.1, k₅.2.1]
  refine WP.mono (selPt_ok hs₆ (decide (wordsVal s₄.mem base K.R.z K.M.n = 0))
    (by rw [c₆, m₅]; simp only [mask, decide_eq_true_eq]) (o := K.R) (a := K.D) (b := K.E)
    (fun d hd => le d (by sub_mem hd))
    aR (fun d hd e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)))
    fun s₇ ⟨r7x, r7y, r7z, k₇, F₇⟩ => ?_
  rw [m₆] at r7x r7y r7z F₇
  obtain U₇ : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₄.mem s₇.mem :=
    fun x hx => F₇ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  obtain inL : ∀ {P : Pt}, (∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) →
      ∀ w ∈ [(P.x, 8 * K.M.n), (P.y, 8 * K.M.n), (P.z, 8 * K.M.n)], w ∈ loopW K := by
    intro P hP w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
  obtain rz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s.mem base K.R.z K.M.n := keepD _ (by simp)
  refine ⟨?_, ?_, ?_, ?_, (U₄.trans U₇).mono fun w hw => ?_⟩
  · rw [r7x, d4x, rz, keepD K.E.x (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · rw [r7y, d4y, rz, keepD K.E.y (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · rw [r7z, d4z, rz, keepD K.E.z (by simp), selVal]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;> simp [h1]
  · exact ((Keeps.regs k₂).mono (by decide)).trans (((Keeps.regs k₃).mono (by decide)).trans
      ((k₄.mono (by decide)).trans (((Keeps.regs k₅).mono (by decide)).trans
      (((Keeps.regs k₆).mono (by decide)).trans (k₇.mono (by decide))))))
  · rcases List.mem_append.mp hw with h | h
    · exact inL oD w h
    · exact inL oR w h

/-- `selVal` in the field. -/
theorem toM_selVal {C : Curve} {K : WinCfg} {m : Mem} {base : Addr} (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    {r e d : Nat} {Z1 Z2 a b c : Fe C}
    (hz1 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.R.z K.M.n) = Z1)
    (hl1 : wordsVal m base K.R.z K.M.n < C.p)
    (hz2 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.E.z K.M.n) = Z2)
    (hl2 : wordsVal m base K.E.z K.M.n < C.p)
    (ha : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base r K.M.n) = a)
    (hb : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base e K.M.n) = b)
    (hc : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base d K.M.n) = c) :
    toM C.p (2 ^ (64 * K.M.n)) (selVal m base K r e d) = if Z1 = 0 then b else if Z2 = 0 then a else c := by
  obtain i1 : wordsVal m base K.R.z K.M.n = 0 ↔ Z1 = 0 := by rw [← hz1]; exact (toM_eq_zero_iff hp hl1).symm
  obtain i2 : wordsVal m base K.E.z K.M.n = 0 ↔ Z2 = 0 := by rw [← hz2]; exact (toM_eq_zero_iff hp hl2).symm
  unfold selVal
  rw [toM_ite, toM_ite, ha, hb, hc]
  simp only [i1, i2]

/-- `R = R + E` for `R` in Jacobian coordinates and `E` affine (or `O`), by
the mixed addition into `D`, with `R = E` where `R` is `O` and `R` kept where
`E` is `O`: for `R` and `E` standing for points not equal unless one is `O`. -/
theorem sumJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {QR QE : Point C} (hQR : onCurve C QR = true)
    (hQE : onCurve C QE = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) QR)
    (hE : RepA C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) QE)
    (hsep : QR ≠ .infinity → QE ≠ .infinity → QR ≠ QE) :
    WP isa (WinCfg.sumJ K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add QR QE) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  obtain w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  obtain V0 : ∀ x ∈ rcbR K.S K.R K.E, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
  obtain I₀ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  rw [WinCfg.sumJ, maddJ_eq]
  simp only [Code.inline]
  refine WP.seq (WP.mono (winN_ok hL hp maddJN_ok (hL.rcbApart_D (Or.inr rfl)) w1.1 w1.2 I₀
    (fun x hx => hx)) fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  obtain S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  -- `R` and `E` kept, `D` the sum.
  obtain ⟨-, -, -, hRo, -, -, -, hEo, -, -⟩ := hL.other_ne
  obtain nD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := by
    intro x hx h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain h1 : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hRo y hy (List.mem_append_right _ h)
    obtain h2 : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hEo y hy (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
  obtain inV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain v₁' : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = tmv C K.M.n base s x := fun x hx => by
    rw [I₁.val x (inV x (by sub_mem hx)), o₁ x (nD x hx)]
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      wordsVal s₁.mem base x K.M.n < C.p := fun x hx => I₁.lt x (inV x hx)
  obtain vD : (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.x K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.y K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.z K.M.n)) =
      maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
    refine Eq.trans ?_ (v₁.trans (maddJN_run _))
    rw [I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp))]
  obtain jx := congrArg Prod.fst vD
  obtain jy := congrArg (fun t => t.2.1) vD
  obtain jz := congrArg (fun t => t.2.2) vD
  dsimp only at jx jy jz
  refine WP.mono (selSum_ok hL I₁.scr) fun s₂ ⟨r2x, r2y, r2z, k₂, U₂⟩ => ?_
  obtain c : ∀ r ∈ [Reg.rax, .rcx, .rdx], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  obtain S₂ := S₁.next hL (I₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c) U₂
  obtain tz1 := v₁' K.R.z (by simp)
  obtain tz2 := v₁' K.E.z (by simp)
  obtain l1 := lt₁ K.R.z (by simp)
  obtain l2 := lt₁ K.E.z (by simp)
  refine ⟨S₂, by rw [k₂.gpr _ (by decide), k₁.gpr _ (rbx_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [r2x, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2y, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2z, selVal]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
  · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [r2x, r2y, r2z, toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jx,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jy,
      toM_selVal hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jz]
    exact InvJ.sumSelM hC hM3 hQR hQE hR hE hsep

/-! ## An iteration but the last -/

/-- The Jacobian loop's invariant at `rbx = j`: `R` stands for `[winE k J j]P`
in Jacobian coordinates, the table affine. -/
structure WinInvJ (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinStR K C base size (RepA C) P s₀ s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-- What the entry's selection writes is in `loopW`. -/
theorem entryW_loopW (K : WinCfg) : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inr rfl

/-- `R` is apart from what the entry's selection writes. -/
theorem R_apart_entry {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ [K.R.x, K.R.y, K.R.z]) :
    ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  obtain hxw : x ∈ winWs K := winOther_ws K x (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  obtain hne : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ≠ y := fun y hy e => hRo x hx (by
    rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp)
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.lay.tmp x (winWs_slots K x hxw)

/-- An iteration but the last, `rbx = j ≥ 2` to `j - 1`: adds digit `j - 1`. -/
theorem winStepJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} (hj : 2 ≤ j) (hjn : j ≤ K.J)
    (hb : 16 * winE k K.J j + 8 < C.n) {s : State} (hI : WinInvJ K C base size k P s₀ s j) :
    WP isa (WinCfg.stepJ K).inline s fun s' =>
      WinInvJ K C base size k P s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 1)) := by
  have hJ := hL.J
  rw [WinCfg.stepJ]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega_using [hj]) (by omega_using [hjn, hJ]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain hS₁ := hI.st.rbxKeeps hL k₁
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  obtain rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    obtain e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hp hC hM3 hP hF hS₁ (i := j - 1) (by omega_using [hjn, hJ]) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  obtain hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  obtain hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by have := S₅.scr.nowrap; omega_arith)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hX (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := j - 1) (by omega_using [hjn, hJ]) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆
      fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  obtain S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono (entryW_loopW K))
  obtain eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_using [hn, this])
  obtain lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  obtain rep₇ : InvJ C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  obtain hsep := win_sep hC hO hP hP0 (k := k) (J := K.J) (j := j - 1)
    (by rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)]; exact hb)
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hsep
  refine WP.seq (WP.mono (sumJ_ok hL hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep (fun h1 _ => (hsep h1).1))
    fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  obtain hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hadd
  rw [hadd] at r₈
  obtain hx₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [E₇.keep.gpr _ (rbx_not_clob _), hx₅]
  obtain hx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (cmpRbx_ok s₈ (j := j - 1) (i := 1) (by decide) (by omega_using [hjn, hJ]) hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  refine ⟨S₈.rbxKeeps hL ((Keeps.mono k₉ (fun _ h => absurd h List.not_mem_nil))), by rw [k₉.1 _ (by simp), hx₈],
    by rw [k₉.2.1]; exact l₈, ?_⟩
  obtain e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.2.1]
  rw [e, e, e]; exact r₈

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# Windows in Jacobian coordinates on x86-64: the last iteration and the loop

The last iteration (`stepLast_ok`): `R = 16 R` in Jacobian coordinates, `R`
into projective coordinates with `Y = 1` where `Z = 0` (`toProjR_ok`), and its
sum with the entry of digit `0` (affine, so projective) by the complete
formulas (`sumStep_ok`). The method (`windowJ_ok`): the table (`build_ok`)
into affine coordinates (`normTbl_ok`), then from `R = O` the iterations of
`winStepJ_ok` for the digits `J - 1` down to `1`, and the last.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- `R` from Jacobian coordinates into projective coordinates, `(XZ : Y : Z³)`,
with `Y` Montgomery's one where `Z = 0`. -/
theorem toProjR_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {Q : Point C}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q) :
    WP isa (WinCfg.toProjR K).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z) Q := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hF
  obtain ⟨-, -, aRD⟩ := hL.rcbApart_winJ
  obtain oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  obtain oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  obtain sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  obtain w1 := winJ_sl oD (fun x hx => winOther_mem (oR x hx)) sZ
  let V := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]
  obtain V0 : ∀ x ∈ V, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
  obtain I₀ : Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  rw [WinCfg.toProjR, fromJ_eq]
  simp only [Code.inline]
  refine WP.seq (WP.mono (winN_ok hL hp fromJN_ok aRD w1.1 w1.2 I₀ (by
      intro x hx
      simp only [rcbR, V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))
    fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  obtain S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  obtain v : (E₁ K.D.x, E₁ K.D.y, E₁ K.D.z) = (tmv C K.M.n base s K.R.x * tmv C K.M.n base s K.R.z,
      tmv C K.M.n base s K.R.y + tmv C K.M.n base s K.zero,
      tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z * tmv C K.M.n base s K.R.z) :=
    v₁.trans (fromJN_run _)
  obtain hDV : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ [K.D.x, K.D.y, K.D.z] ++ V := fun x hx =>
    List.mem_append_left _ hx
  obtain z0 : tmv C K.M.n base s K.zero = 0 := by
    show toM _ _ _ = 0; rw [hz]; exact toM_zero _ _
  -- `R = D`.
  obtain ⟨hle, hap, hne, ho⟩ := winRD hL
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok I₁.scr hle hap hne ho) fun s₂ ⟨wx, wy, wz, k₂, U₂⟩ => ?_
  obtain hs₂ := I₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  obtain hRz : K.R.z + 8 * K.M.n ≤ size := hle _ (by simp)
  obtain hRy : K.R.y + 8 * K.M.n ≤ size := hle _ (by simp)
  obtain hRx : K.R.x + 8 * K.M.n ≤ size := hle _ (by simp)
  refine WP.mono (zmask_ok K hs₂ hL.n0 hRz) fun s₃ ⟨m₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (ySelWords_ok hs₃ K _ m₃ K.M.n hRy) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hn := hs₂.nowrap
  have m₃' : s₃.mem = s₂.mem := k₃.2.1
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  obtain ay : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y → x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ x :=
    fun x hx h => hap x (by simp at hx ⊢; omega_using [hx]) _ (by simp) h
  obtain vRx : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) rxy; omega_arith) (by omega_arith), m₃', wx]
  obtain vRz : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [O₄.wordsVal (by have := ay _ (by simp) (Ne.symm ryz); omega_arith) (by omega_arith), m₃', wz]
  obtain hone' : K.one < 2 ^ (64 * K.M.n) := Nat.lt_trans hone_lt hpn
  obtain vRy : wordsVal s₄.mem base K.R.y K.M.n =
      if wordsVal s₁.mem base K.D.z K.M.n = 0 then K.one else wordsVal s₁.mem base K.D.y K.M.n := by
    rw [← wz, ← wy]
    by_cases hz0 : wordsVal s₂.mem base K.R.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ hone' fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← m₃']
      exact wordsVal_congr₂ _ _ _ fun j hj => by simp only [e₄ j hj, hz0, ↓reduceIte]
  -- What changed: `loopW`.
  obtain inR : ∀ w ∈ [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)], w ∈ loopW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
    · exact Or.inl ⟨_, oR _ (by simp), rfl⟩
  obtain U₄ : Unch base (loopW K) s₁.mem s₄.mem := by
    refine (U₂.trans (m₃' ▸ O₄.unch)).mono fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · exact inR w h
    · simp only [List.mem_singleton] at h; rw [h]; exact inR _ (by simp)
  obtain c : ∀ r ∈ [Reg.rax, .rdx, .r8], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [powClob, clob]
    · simp [powClob, clob]
    · exact mem_powClob_of_clob (r8_mem_clob _)
  obtain kk : KeepRegs (powClob K.M.n) s₁ s₄ :=
    (k₂.mono fun r hr => c r (by simp at hr ⊢; simp [hr])).trans (((Keeps.regs k₃).mono
      fun r hr => c r (by simp at hr ⊢; simp [hr])).trans (k₄.mono fun r hr => c r (by
        simp at hr ⊢; rcases hr with h | h <;> simp [h])))
  obtain S₄ := S₁.next hL (hs₃.of_keepRegs k₄ (by decide)) kk U₄
  -- The values.
  obtain eD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = E₁ x :=
    fun x hx => I₁.val x (hDV x hx)
  simp only [Prod.mk.injEq] at v
  obtain ⟨vx, vy, vz⟩ := v
  obtain hZ : (wordsVal s₁.mem base K.D.z K.M.n = 0) ↔ tmv C K.M.n base s K.R.z = 0 := by
    rw [← toM_eq_zero_iff hp (I₁.lt _ (hDV _ (by simp))), eD _ (by simp), vz]
    constructor
    · intro h; by_contra hn0; exact cube_ne_zero hC hn0 h
    · intro h; rw [h]; simp only [Fin.mul_zero]
  refine ⟨S₄, by rw [k₄.gpr _ (by decide), k₃.1 _ (by decide), k₂.gpr _ (by decide),
    k₁.gpr _ (rbx_not_clob _)], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vRx]; exact I₁.lt _ (hDV _ (by simp))
    · rw [vRy]; split
      · exact hone_lt
      · exact I₁.lt _ (hDV _ (by simp))
    · rw [vRz]; exact I₁.lt _ (hDV _ (by simp))
  · have h := InvJ.out hC hR
    show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vRx, vRy, vRz, toM_ite, hone, eD _ (by simp), eD _ (by simp), eD _ (by simp), vx, vy, vz]
    simp only [hZ]
    rw [z0, show ∀ y : Fe C, y + 0 = y from Fin.add_zero]
    exact h

/-- The last iteration, `rbx = 1` to `0`: adds digit `0` by the complete
formulas, leaving `R` in projective coordinates. -/
theorem stepLast_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    {P : Point C} (hP : onCurve C P = true)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {s : State} (hI : WinInvJ K C base size k P s₀ s 1) :
    WP isa (WinCfg.stepLast K).inline s fun s' =>
      WinStR K C base size (RepA C) P s₀ s' ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (winE k K.J 0) P) := by
  have hJ := hL.J
  rw [WinCfg.stepLast]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega_arith) (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain hS₁ := hI.st.rbxKeeps hL k₁
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  obtain rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J 1) P) := by
    obtain e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hp hC hM3 hP hF hS₁ (i := 0) (by omega_arith) b₁ lt₁ rep₁)
    fun s₂ ⟨S₂, x₂, l₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (toProjR_ok hL hp hC hpn hone_lt hone hF S₂ l₂ r₂)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  obtain hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 0 := by rw [x₅, x₂, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  obtain hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_arith) (by have := S₅.scr.nowrap; omega_arith)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hX (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := 0) (by omega_arith) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆
      fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  obtain S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono (entryW_loopW K))
  obtain eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_arith)
  obtain lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  obtain rep₇ : Rep C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J 1) P) := by
    rw [tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp)), tmv_congr (eR _ (by simp))]; exact r₅
  refine WP.mono (sumStep_ok hL hp hC hM3 hF S₇ (hC.onCurve_mul hP _) (onCurve_winPt hC hP k 0)
    lt₇ E₇.lt rep₇ E₇.rep.1) fun s₉ ⟨S₉, _, l₉, r₉⟩ => ⟨S₉, l₉, ?_⟩
  obtain hadd := win_add hC hP (k := k) (J := K.J) (j := 0) hk8 (by omega_arith)
  rw [hadd] at r₉
  exact r₉

/-- What is read only, and the table of bits, survive writes apart from them. -/
theorem WinFixed.unch {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {P : Point C} {s s' : State} (hF : WinFixed K C base s P k) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hro : ∀ x ∈ winRo K, ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hbits : ∀ w ∈ W, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits) : WinFixed K C base s' P k := by
  obtain e : ∀ x ∈ winRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (hro x hx) (by have := hL.lay.le x (winRo_slots K x hx); omega_arith)
  have hb := hL.bits
  refine ⟨?_, ?_, fun x hx => by rw [e x hx]; exact hF.ro_lt x hx, by rw [e _ (by simp [winRo])]; exact hF.zero,
    ?_, fun t ht => ?_⟩
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.a
  · rw [tmv_congr (e _ (by simp [winRo]))]; exact hF.b
  · rw [tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo])), tmv_congr (e _ (by simp [winRo]))]
    exact hF.pt
  · rw [hU.byte (fun w hw => by have := hbits w hw; omega_arith) (by omega_arith)]
    exact hF.bits t ht

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`, by windows in Jacobian coordinates with an affine
table (by the inversion `inv`, writing `IW`): for `P ≠ O` on a curve of
prime order `n` (`PrimeOrder`), with `16 winE k J 2 + 8 < n` (so that no
addition but the last is of equal or opposite points); only `invClob`,
`winW` and `IW` change. -/
theorem windowJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {inv : Prog isa} {IW : List (Nat × Nat)}
    (hI : InvSpecW K C base size inv IW) {s₀ : State} (hs : Scr s₀ base size)
    (hM : ModOkW K.M size C.p s₀.mem base) (hF₀ : WinFixed K C base s₀ P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) (hJ2 : 2 ≤ K.J) (hb : 16 * winE k K.J 2 + 8 < C.n) :
    WP isa (WinCfg.windowJ K inv).inline s₀ fun s' => KeepRegs (invClob K.M.n) s₀ s' ∧
      Unch base (winW K ++ IW) s₀.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  obtain hne : ∀ m, 1 ≤ m → m ≤ 8 → mul m P ≠ .infinity := by
    intro m h1 h8 h
    obtain h0 : zmul (m : Int) P = zmul 0 P := by
      rw [zmul_natCast, h, show (0 : Int) = ((0 : Nat) : Int) from rfl, zmul_natCast]
      rw [Spec.Weierstrass.mul]; simp
    have := hO.zmul_eq hC hP hP0 (by omega_arith) h0
    omega_arith
  obtain pc : ∀ r ∈ powClob K.M.n, r ∈ invClob K.M.n := fun r h => List.mem_cons_of_mem _ h
  rw [WinCfg.windowJ]
  simp only [Code.inline]
  refine WP.seq (WP.mono (build_ok hL hp hC hM3 hP hs hM hF₀) fun sb B => ?_)
  refine WP.seq (WP.mono (normTbl_ok hL hp hC hpn hone_lt hone hne hI B.scr B.mod B.tbl)
    fun s ⟨hs', Kn, Un, hM', T⟩ => ?_)
  obtain U₀ : Unch base (winW K ++ IW) s₀.mem s.mem := (B.unch.trans Un).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢; rcases hw with hw | hw | hw <;> simp [hw]
  obtain hF : WinFixed K C base s P k := by
    refine hF₀.unch hL U₀ hn (fun x hx w hw => ?_) (fun w hw => ?_)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.ro_w hx w hw
      · rcases hI.w w hw with rfl | rfl | ⟨-, h⟩
        · exact hL.lay.apart x _ (winRo_slots K x hx) (winOther_mem (by win_mem))
            fun e => hL.ro x hx (e ▸ by win_mem)
        · exact hL.lay.tmp x (winRo_slots K x hx)
        · exact h x (winRo_slots K x hx)
    · rcases List.mem_append.mp hw with hw | hw
      · exact hL.bits_w w hw
      · exact hI.bits w hw
  obtain S₁ : WinStR K C base size (RepA C) P s s := ⟨hs', ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hM', T⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  obtain wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := pt_other (Or.inl rfl)
  obtain le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  obtain ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  obtain axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  obtain axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  obtain ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  obtain W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  obtain W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega_arith)) fun s₅ ⟨b₅, k₅⟩ => ?_
  obtain hU : Unch base (loopW K) s.mem s₅.mem := by
    rw [k₅.2.1]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  obtain c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
  obtain S₅ : WinStR K C base size (RepA C) P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [powClob]))) hU
  obtain b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_arith
  obtain vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.2.1, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  obtain vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.2.1, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  obtain vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.2.1, e₄]
  obtain I₅ : WinInvJ K C base size k P s s₅ K.J := by
    refine ⟨S₅, b₅, fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hp0
      · rw [vy]; exact hone_lt
      · rw [vz]; exact hp0
    · refine Or.inl ⟨by rw [winE_top hk, mul_zero_pt'], ?_⟩
      show toM _ _ _ = 0
      rw [vz]; exact toM_zero _ _
  refine WP.seq (countLoop_ok (Inv := fun i t => WinInvJ K C base size k P s t (i + 1)) (n := K.J - 1)
    (fun i t h1 h2 hi => WP.mono (winStepJ_ok hL hX hp hC hM3 hO hP hP0 hpn hone_lt hone hF hk8
      (j := i + 1) (by omega_arith) (by omega_arith)
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _
        (winE_le_of_le hk8 (by omega_arith) (by omega_arith))) _) hb) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega_arith]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega_arith⟩)
    (fun t hi => WP.mono (stepLast_ok hL hX hp hC hM3 hP hpn hone_lt hone hF hk8 hi)
      fun u ⟨S, l, r⟩ => ⟨((B.keep.mono pc).trans Kn).trans (S.keep.mono pc),
        (U₀.trans S.unch).mono fun w hw => by
          simp only [List.mem_append] at hw ⊢; rcases hw with (hw | hw) | hw <;> simp [hw],
        S.mod, l, by rw [← winE_zero]; exact r⟩)
    (by omega_arith) (by rw [Nat.sub_add_cancel (by omega_arith)]; exact I₅))

end VG.Proof.Weierstrass.X86_64
