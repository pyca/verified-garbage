module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# The complete addition by a call, on AArch64

`addP M S p q o pa` (`Impl/Weierstrass/AArch64/Comb.lean`) is `o = p + q` by
Algorithm 4: inline (`pa = none`), or (`pa = some (name, bAt)`) by a call of
the function `name`, whose code is the same formula reading `b` at `bAt`,
with `x30` kept in `v29` around the call. Either way it does what `rcb3_ok`
says the inline formula does (`addP_ok`), given what the call needs
(`AddOk`): `bAt` a slot apart from the formula's, and a callee that writes
no vector register, keeps the callee-saved registers and has no frames; and
of the state (`AddReady`): `b`, the number at `S.b3`, already at `bAt`. The
caller puts it there once, and it survives what does not write `bAt` or
`S.b3` (`AddReady.unch`, `AddFar`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps)


/-! ## Environments -/

/-- `rcbσ` of the slots with `b` at `b`, but for `b`'s index. -/
theorem rcbσ_b3 (S : RcbSlots) (p q o : Pt) (b : Nat) {y : Nat} (hy : y ≠ 10) :
    rcbσ { S with b3 := b } p q o y = rcbσ S p q o y := by
  simp only [rcbσ, rcbW, rcbR, List.cons_append, List.nil_append]
  match y, hy with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 11, _ | 12, _ | 13, _
  | 14, _ | 15, _ | 16, _ | _ + 17, _ => rfl

/-- Algorithm 4 with `b` read at `b` instead, from the environment with `b`
there: the same values but at `b`. -/
theorem runOps_rcb3_b3 {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) {b : Nat} (hb : b ∉ rcbW S o ++ rcbR S p q) (E : Nat → F) {x : Nat}
    (hx : x ≠ b) :
    runOps (rcb3 { S with b3 := b } p q o) (Function.update E b (E S.b3)) x =
      runOps (rcb3 S p q o) E x := by
  have hA₂ : RcbApart { S with b3 := b } p q o :=
    ⟨hA.nodup, fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hA.apart _ (List.mem_cons_self ..)
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun h => hb (List.mem_append_left _ (show y ∈ rcbW S o from h))
      · exact hA.apart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))⟩
  have he : (fun y => Function.update E b (E S.b3) (rcbσ { S with b3 := b } p q o y)) =
      fun y => E (rcbσ S p q o y) := by
    funext y
    by_cases hy : y = 10
    · subst hy
      simp [rcbσ, rcbW, rcbR]
    · rw [rcbσ_b3 S p q o b hy, Function.update_of_ne fun h => hb (by rw [← h]; exact rcbσ_mem S p q o y)]
  by_cases hw : x ∈ rcbW S o
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have e : (rcbW S o)[i] = rcbσ S p q o i := by
      rw [rcbσ, getD_append_left hi]
    have e₂ : (rcbW S o)[i] = rcbσ { S with b3 := b } p q o i :=
      (getD_append_left (W := rcbW S o) (R := rcbR { S with b3 := b } p q) (d := S.a) hi).symm
    rw [rcb3_eq, rcb3_eq]
    conv => lhs; rw [e₂]
    rw [e, ofN_run rcb3N_ok hA₂, ofN_run rcb3N_ok hA, he]
  · have hout : ∀ (S' : RcbSlots), rcbW S' o = rcbW S o → ∀ op ∈ rcb3 S' p q o, op.out ≠ x :=
      fun S' hS op hop h => hw (hS ▸ h ▸ (rcb3_eq S' p q o ▸ ofN_out rcb3N_ok) op hop)
    rw [runOps_of_not_out _ _ (hout { S with b3 := b } rfl), runOps_of_not_out _ _ (hout S rfl),
      Function.update_of_ne hx]

/-! ## The call -/

/-- The modulus survives a change of memory apart from it. -/
theorem _root_.VG.Proof.Mont.AArch64.ModOkA.outside {M : Mod} {size m : Nat} {base : Addr} {mem mem' : Mem}
    (hM : ModOkA M size m mem base) {o : Nat} (hO : Outside base o (8 * M.n) mem mem')
    (ho : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOkA M size m mem' base :=
  ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [hO.wordsVal (by omega) (by have := hM.mo; omega)]; exact hM.val, hM.inv, hM.red, hM.call⟩

/-- `x30` into lane 0 of `v29`. -/
theorem insLr_ok (s : State) :
    WP isa (.block [.vop (.ins .d2 .v29 0 .x30)]) s fun s₁ =>
      s₁ = s.setV .v29 (setLane (s.v .v29) 64 0 (s.gpr .x30)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Mont.exec_ins (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']

/-- `Inv` depends on the state only through the working space and memory. -/
theorem Inv.of_mem {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s t : State} (h : Inv M base size m Sl V E s) (hs : Scr t base size)
    (hm : t.mem = s.mem) : Inv M base size m Sl V E t :=
  ⟨hs, hm ▸ h.mod, h.sl, hm ▸ h.lt, hm ▸ h.val⟩

/-- What the call of the addition's function needs: `b`'s slot `bAt`
aligned, apart from the slots `Sl` (`lay`, the slots with `bAt` laid out)
and from the formula's, at most four words (so that its products are
inline), and a callee that writes no vector register, keeps the
callee-saved registers and has no frames. -/
structure AddCallOk (M : Mod) (size : Nat) (Sl : Nat → Prop) (S : RcbSlots) (p q o : Pt) (bAt : Nat) :
    Prop where
  lay : Lay M size fun x => Sl x ∨ x = bAt
  al : bAt % 8 = 0
  apart : bAt ∉ rcbW S o ++ rcbR S p q
  n4 : M.n ≤ 4
  pres : ∀ r ∈ preserved, r ∉ clob M.n
  vec : ∀ i ∈ instrs (fprogB M (rcb3 { S with a := bAt, b3 := bAt } p q o)), vdstOf i = none
  nf : (fprogB M (rcb3 { S with a := bAt, b3 := bAt } p q o)).noFrames = true

/-- What a call needs of the state: `b` (the number at `S.b3`) at `bAt`. -/
def AddReady (base : Addr) (M : Mod) (mem : Mem) (S : RcbSlots) : Option (String × Nat) → Prop
  | none => True
  | some (_, bAt) => wordsVal mem base bAt M.n = wordsVal mem base S.b3 M.n

/-- What `addP` needs: nothing inline, `AddCallOk` for a call. -/
def AddOk (M : Mod) (size : Nat) (Sl : Nat → Prop) (S : RcbSlots) (p q o : Pt) :
    Option (String × Nat) → Prop
  | none => True
  | some (_, bAt) => AddCallOk M size Sl S p q o bAt

/-- What a frame `W` must keep apart from for a call's `AddReady` to survive
it: `bAt` and `S.b3`. -/
def AddFar (M : Mod) (S : RcbSlots) (W : List (Nat × Nat)) : Option (String × Nat) → Prop
  | none => True
  | some (_, bAt) => ∀ w ∈ W, (bAt + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ bAt) ∧
      (S.b3 + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ S.b3)

theorem AddFar.mono {M : Mod} {S : RcbSlots} {W W' : List (Nat × Nat)} {pa : Option (String × Nat)}
    (h : AddFar M S W pa) (hW : ∀ w ∈ W', w ∈ W) : AddFar M S W' pa :=
  match pa, h with
  | none, _ => trivial
  | some _, h => fun w hw => h w (hW w hw)

/-- `AddReady` survives a change of memory apart from `bAt` and `S.b3`. -/
theorem AddReady.unch {M : Mod} {size : Nat} {Sl : Nat → Prop} {S : RcbSlots} {p q o : Pt}
    {pa : Option (String × Nat)} (hpa : AddOk M size Sl S p q o pa) (hb3 : Sl S.b3) (hn : size ≤ 2 ^ 64)
    {base : Addr} {mem mem' : Mem} (hr : AddReady base M mem S pa) {W : List (Nat × Nat)}
    (hU : Unch base W mem mem') (hW : AddFar M S W pa) : AddReady base M mem' S pa := by
  match pa, hpa, hr, hW with
  | none, _, _, _ => trivial
  | some (_, bAt), hc, hr, hW =>
    show wordsVal mem' base bAt M.n = wordsVal mem' base S.b3 M.n
    have h1 := hc.lay.le bAt (Or.inr rfl)
    have h2 := hc.lay.le S.b3 (Or.inl hb3)
    rw [hU.wordsVal (fun w hw => (hW w hw).1) (by omega), hU.wordsVal (fun w hw => (hW w hw).2) (by omega)]
    exact hr

theorem Inv.mono_sl {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl Sl' : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) (hS : ∀ x, Sl x → Sl' x) :
    Inv M base size m Sl' V E s :=
  ⟨h.scr, h.mod, fun x hx => hS x (h.sl x hx), h.lt, h.val⟩

/-- The callee's contract at a call: `rcb3_ok`'s, for `b` at `bAt`, and the
vector registers kept. -/
def addK (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (S : RcbSlots) (p q o : Pt)
    (V : List Nat) (E : Nat → Fin m) : Contract isa where
  pre t := Inv M base size m Sl V E t
  post t t' := ProgKeep M base (rcbW S o) t t' ∧
    Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) t' ∧
    (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
      VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) ∧
    t'.v = t.v
  pub _ _ := True

/-- `o = p + q` by Algorithm 4, inline or by a call: what `rcb3_ok` says. -/
theorem addP_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q))
    {pa : Option (String × Nat)} (hpa : AddOk M size Sl S p q o pa) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    (hr : AddReady base M s.mem S pa) :
    WP isa (addP M S p q o pa) s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) s' ∧
      (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  match pa, hpa, hr with
  | none, _, _ => exact rcb3_ok hL hAl hm hA hSl hLow hI hV
  | some (name, bAt), hc, hr =>
  let Sl' := fun x => Sl x ∨ x = bAt
  have hL' : Lay M size Sl' := hc.lay
  have hAl' : Aligned M Sl' := ⟨fun x hx => hx.elim (hAl.sl x) (fun h => h ▸ hc.al), hAl.mod, hAl.call⟩
  have hbS : Sl' bAt := Or.inr rfl
  have hs := hI.scr
  have hn := hs.nowrap
  have hb3V : S.b3 ∈ V := hV _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have outW : ∀ x ∈ rcbW S o, x ≠ bAt := fun x hx h => hc.apart (List.mem_append_left _ (h ▸ hx))
  have outR : ∀ x ∈ rcbR S p q, x ≠ bAt := fun x hx h => hc.apart (List.mem_append_right _ (h ▸ hx))
  let E₂ := Function.update E bAt (E S.b3)
  have hr3 : rcb3 { S with a := bAt, b3 := bAt } p q o = rcb3 { S with b3 := bAt } p q o := rfl
  rw [addP]
  refine WP.seq (WP.mono (insLr_ok s) fun s₁ e₁ => ?_)
  have hs₁ : Scr s₁ base size := by
    rw [e₁]; exact ⟨by rw [RegUpd.gpr_setV]; exact hs.x0, hs.wr, hs.nowrap, hs.enc⟩
  have m₁ : s₁.mem = s.mem := by rw [e₁, RegUpd.mem_setV]
  -- `b` at `bAt`
  have hI₁ : Inv M base size m Sl' (bAt :: V) E₂ s₁ := by
    refine ⟨hs₁, by rw [m₁]; exact hI.mod, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hbS
      · exact Or.inl (hI.sl x hx)
    · rw [m₁]
      by_cases hxb : x = bAt
      · rw [hxb, hr]; exact hI.lt _ hb3V
      · exact hI.lt x ((List.mem_cons.mp hx).resolve_left hxb)
    · rw [m₁]
      by_cases hxb : x = bAt
      · rw [hxb, hr, hI.val _ hb3V]; exact (Function.update_self bAt (E S.b3) E).symm
      · rw [hI.val x ((List.mem_cons.mp hx).resolve_left hxb)]; exact (Function.update_of_ne hxb ..).symm
  -- the call
  have hcov : Covers [⟨base, size⟩] s₁.wr := Covers.one ⟨_, hs₁.wr, by
    have := hs.contains (d := 0) (n := size) (by have := hL'.le bAt hbS; omega) (by
      have := hL'.le bAt hbS; have := hI.mod.n0; omega)
    simpa [off] using this⟩
  have hp₂ : RcbApart { S with a := bAt, b3 := bAt } p q o :=
    ⟨hA.nodup, fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun h => hc.apart (List.mem_append_left _ (show y ∈ rcbW S o from h))
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun h => hc.apart (List.mem_append_left _ (show y ∈ rcbW S o from h))
      · exact hA.apart _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))⟩
  have hSl₂ : ∀ x ∈ rcbW { S with a := bAt, b3 := bAt } o ++ rcbR { S with a := bAt, b3 := bAt } p q,
      Sl' x := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (hSl x (List.mem_append_left _ hx))
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbS
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbS
    · exact Or.inl (hSl x (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))))
  have hV₂ : ∀ x ∈ rcbR { S with a := bAt, b3 := bAt } p q, x ∈ bAt :: V := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hV x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  refine WP.seq (WP.callV (k := addK M base size m Sl' { S with a := bAt, b3 := bAt } p q o (bAt :: V) E₂)
    (fun t ht => by
      obtain ⟨tr, t', he, K, I', v'⟩ := rcb3_ok hL' hAl' hm hp₂ hSl₂ (Low.small hc.n4 _) ht hV₂
      exact ⟨tr, t', he, ⟨fun r hr => K.gpr r (hc.pres r hr), K.sp, Exec.preservedV he (by
        rw [Code.allInstrs_eq]
        exact List.all_eq_true.mpr fun i hi => by unfold keepsV; rw [hc.vec i hi])⟩, K, I', v',
        funext fun r => Exec.vec (fun i hi e => by rw [hc.vec i hi] at e; cases e) he⟩)
    (rd := []) (wr := [⟨base, size⟩])
    (hI₁.of_mem ⟨by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hs₁.x0], by simp,
      hs.nowrap, hs.enc⟩ (by rw [State.withRegions_mem, State.callEntry_mem]))
    (Covers.right hcov) hcov ?_ hc.nf)
  intro s₄ r₄ w₄ p₄ _ _ _ _ ⟨K, I₄, vals₄, V₄⟩
  have V₄' : s₄.v = s₁.v := V₄
  have g₄ : ∀ r, r ∉ clob M.n → r ∉ linkRegs → s₄.gpr r = s₁.gpr r := fun r hr hl => by
    have := K.gpr r hr
    simp only [State.withRegions_gpr] at this
    rw [this, State.callEntry_gpr _ hl]
  have x0c : Reg.x0 ∉ clob M.n := x0_not_clob' _
  have hs₄ : Scr s₄ base size :=
    ⟨by rw [g₄ _ x0c (by decide), hs₁.x0], by rw [w₄]; exact hs₁.wr, hs.nowrap, hs.enc⟩
  have I₄' := I₄.of_mem (t := s₄) hs₄ rfl
  have mK : ∀ x, (∀ w ∈ rcbW S o, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
      (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s₄.mem x = s₁.mem x := K.mem
  refine WP.mono (Mont.lr_ok s₄) fun s₅ ⟨l₅, k₅⟩ => ?_
  have hx16 : Reg.x16 ∈ clob M.n := by simp [clob]
  have hx17 : Reg.x17 ∈ clob M.n := by simp [clob]
  have hK : ProgKeep M base (rcbW S o) s s₅ := by
    refine ⟨fun r hr => ?_, by rw [k₅.rd, r₄, e₁, RegUpd.rd_setV],
      by rw [k₅.wr, w₄, e₁, RegUpd.wr_setV], by rw [k₅.sp, p₄, e₁, RegUpd.sp_setV],
      fun x hx ht => by rw [k₅.mem, mK x hx ht, m₁]⟩
    by_cases h30 : r = .x30
    · subst h30
      have := Mont.extract_setLane (s.v .v29) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide)
      simp only [Nat.mul_zero, ite_true] at this
      rw [l₅, V₄', e₁, RegUpd.v_setV_self, this]
    · rw [k₅.gpr r (by simpa using h30), g₄ r hr (by
        simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hr (h ▸ hx16), fun h => hr (h ▸ hx17), h30⟩), e₁, RegUpd.gpr_setV]
  -- the values
  have m₅ : s₅.mem = s₄.mem := k₅.mem
  have hrun : ∀ x, x ≠ bAt → runOps (rcb3 { S with a := bAt, b3 := bAt } p q o) E₂ x =
      runOps (rcb3 S p q o) E x := fun x hx => by rw [hr3]; exact runOps_rcb3_b3 hA hc.apart E hx
  have hmem : ∀ x ∈ [o.x, o.y, o.z] ++ V, x ∈ [o.x, o.y, o.z] ++ bAt :: V := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  have hoW : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW S o := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [rcbW, List.mem_cons]
    rcases hx with rfl | rfl | rfl <;> simp
  have hbV : ∀ x ∈ [o.x, o.y, o.z] ++ V, x = bAt → x ∈ V := fun x hx hb => by
    rcases List.mem_append.mp hx with hx | hx
    · exact absurd hb (outW x (hoW x hx))
    · exact hx
  have outs : ∀ (S' : RcbSlots), rcbW S' o = rcbW S o → ∀ op ∈ rcb3 S' p q o, op.out ≠ bAt :=
    fun S' hS op hop h => outW _ (hS ▸ (rcb3_eq S' p q o ▸ ofN_out rcb3N_ok) op hop) h
  have Eb : runOps (rcb3 S p q o) E bAt = E bAt := runOps_of_not_out _ _ (outs S rfl)
  have Eb₂ : bAt ∈ V → runOps (rcb3 { S with a := bAt, b3 := bAt } p q o) E₂ bAt = E bAt := fun hbV' => by
    rw [runOps_of_not_out _ _ (outs { S with a := bAt, b3 := bAt } rfl)]
    show Function.update E bAt (E S.b3) bAt = _
    rw [Function.update_self, ← hI.val _ hb3V, ← hr, hI.val _ hbV']
  refine ⟨hK, ⟨hK.scr hs, by rw [m₅]; exact I₄'.mod, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩, ?_⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hSl x (List.mem_append_left _ (hoW x hx))
    · exact hI.sl x hx
  · rw [m₅]; exact I₄'.lt x (hmem x hx)
  · rw [m₅, I₄'.val x (hmem x hx)]
    by_cases hxb : x = bAt
    · subst hxb; rw [Eb₂ (hbV _ hx rfl), Eb]
    · exact hrun x hxb
  · have hp : ∀ x ∈ [p.x, p.y, p.z, q.x, q.y, q.z], E₂ x = E x := fun x hx =>
      Function.update_of_ne (outR x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) ..
    rw [← hrun _ (outW _ (hoW _ (by simp))), ← hrun _ (outW _ (hoW _ (by simp))),
      ← hrun _ (outW _ (hoW _ (by simp))), vals₄]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
    rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]
    change VG.Proof.Weierstrass.rcbAdd3 (Function.update E bAt (E S.b3) bAt) _ _ _ _ _ _ = _
    rw [Function.update_self]

/-! ## A copy, then the addition -/

/-- Algorithm 4 is symmetric in its two points. -/
theorem rcbAdd3_comm {F : Type _} [Lean.Grind.CommRing F] (b X1 Y1 Z1 X2 Y2 Z2 : F) :
    VG.Proof.Weierstrass.rcbAdd3 b X1 Y1 Z1 X2 Y2 Z2 = VG.Proof.Weierstrass.rcbAdd3 b X2 Y2 Z2 X1 Y1 Z1 := by
  simp only [VG.Proof.Weierstrass.rcbAdd3, Prod.mk.injEq]
  exact ⟨by grind, by grind, by grind⟩

/-- The modulus survives a change of memory apart from it. -/
theorem _root_.VG.Proof.Mont.AArch64.ModOkA.unch {M : Mod} {size m : Nat} {base : Addr} {mem mem' : Mem}
    (hM : ModOkA M size m mem base) {W : List (Nat × Nat)} (hU : Unch base W mem mem')
    (hW : ∀ w ∈ W, M.mo + 8 * M.n ≤ w.1 ∨ w.1 + w.2 ≤ M.mo) (hn : base.toNat + size ≤ 2 ^ 64) :
    ModOkA M size m mem' base :=
  ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep,
    by rw [hU.wordsVal hW (by have := hM.mo; omega)]; exact hM.val, hM.inv, hM.red, hM.call⟩


/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hal : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x % 8 = 0)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.x1] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hal hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok n hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 hal.1 hal.2.2.2.1 (by omega_using [pxa]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy_ok n hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 hal.2.1 hal.2.2.2.2.1
    (by omega_using [pyb])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok n hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 hal.2.2.1 hal.2.2.2.2.2
    (by omega_using [pzc])) fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega_using [pxz]) (by omega_using [hn, hle]), O₂.wordsVal (by omega_using [pxy]) (by omega_using [hn, hle]), e₁]
  · rw [O₃.wordsVal (by omega_using [pyz]) (by omega_using [hn, hle]), e₂, O₁.wordsVal (by omega_using [pxb]) (by omega_using [hn, hle])]
  · rw [e₃, O₂.wordsVal (by omega_using [pyc]) (by omega_using [hn, hle]), O₁.wordsVal (by omega_using [pxc]) (by omega_using [hn, hle])]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

/-- `E` with `r`'s coordinates set to `c`'s. -/
def rext {α : Type _} (E : Nat → α) (r c : Pt) (x : Nat) : α :=
  if x = r.x then E c.x else if x = r.y then E c.y else if x = r.z then E c.z else E x

theorem rext_of {α : Type _} {E : Nat → α} {r c : Pt} {x : Nat} (h : x ∉ [r.x, r.y, r.z]) :
    rext E r c x = E x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [rext, h.1, h.2.1, h.2.2]

theorem rext_r {α : Type _} (E : Nat → α) {r : Pt} (c : Pt) (hr : r.x ≠ r.y ∧ r.x ≠ r.z ∧ r.y ≠ r.z) :
    rext E r c r.x = E c.x ∧ rext E r c r.y = E c.y ∧ rext E r c r.z = E c.z := by
  refine ⟨by simp [rext], by simp [rext, Ne.symm hr.1], by simp [rext, Ne.symm hr.2.1, Ne.symm hr.2.2]⟩

/-- `r = c`, then `o = p + q` by `addP`: what `addP_ok` says, from the
environment with `r`'s coordinates `c`'s (`rext`). -/
theorem copyAdd_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o r c : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q))
    {pa : Option (String × Nat)} (hpa : AddOk M size Sl S p q o pa) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s)
    (hrSl : ∀ x ∈ [r.x, r.y, r.z], Sl x) (hcV : ∀ x ∈ [c.x, c.y, c.z], x ∈ V)
    (hrV : ∀ x ∈ [r.x, r.y, r.z], x ∉ V) (hrd : r.x ≠ r.y ∧ r.x ≠ r.z ∧ r.y ≠ r.z)
    (hV : ∀ x ∈ rcbR S p q, x ∈ [r.x, r.y, r.z] ++ V) (hr : AddReady base M s.mem S pa)
    (hfar : AddFar M S [(r.x, 8 * M.n), (r.y, 8 * M.n), (r.z, 8 * M.n)] pa) :
    WP isa (.seq (.block (copyPt M.n r c)) (addP M S p q o pa)) s fun s' =>
      ProgKeep M base ([r.x, r.y, r.z] ++ rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ ([r.x, r.y, r.z] ++ V))
        (runOps (rcb3 S p q o) (rext E r c)) s' ∧
      (runOps (rcb3 S p q o) (rext E r c) o.x, runOps (rcb3 S p q o) (rext E r c) o.y,
        runOps (rcb3 S p q o) (rext E r c) o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (rext E r c S.b3) (rext E r c p.x) (rext E r c p.y)
          (rext E r c p.z) (rext E r c q.x) (rext E r c q.y) (rext E r c q.z) := by
  have hs := hI.scr
  have hn := hs.nowrap
  have hcS : ∀ x ∈ [c.x, c.y, c.z], Sl x := fun x hx => hI.sl x (hcV x hx)
  have hne : ∀ x ∈ [r.x, r.y, r.z], ∀ y, y ∈ V → x ≠ y := fun x hx y hy e => hrV x hx (e ▸ hy)
  have rx : r.x ∈ [r.x, r.y, r.z] := by simp
  have ry : r.y ∈ [r.x, r.y, r.z] := by simp
  have rz : r.z ∈ [r.x, r.y, r.z] := by simp
  have cx : c.x ∈ [c.x, c.y, c.z] := by simp
  have cy : c.y ∈ [c.x, c.y, c.z] := by simp
  have cz : c.z ∈ [c.x, c.y, c.z] := by simp
  refine WP.seq (WP.mono (copyPt_ok hs (o := r) (a := c) (n := M.n)
    (fun x hx => hL.le x (List.mem_append.mp (show x ∈ [r.x, r.y, r.z] ++ [c.x, c.y, c.z] from hx)
      |>.elim (hrSl x) (hcS x)))
    (fun x hx => hAl.sl x (List.mem_append.mp (show x ∈ [r.x, r.y, r.z] ++ [c.x, c.y, c.z] from hx)
      |>.elim (hrSl x) (hcS x)))
    (fun x hx y hy hxy => hL.apart x y (hrSl x hx)
      ((List.mem_append.mp (show y ∈ [r.x, r.y, r.z] ++ [c.x, c.y, c.z] from hy)).elim (hrSl y) (hcS y)) hxy)
    (fun x hx hc => hne x hx x (hcV x hc) rfl) hrd) fun s₁ ⟨e₁, e₂, e₃, k₁, U₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have wv : ∀ y ∈ V, wordsVal s₁.mem base y M.n = wordsVal s.mem base y M.n := fun y hy =>
    U₁.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> dsimp only <;>
        exact (hL.apart _ _ (hI.sl y hy) (hrSl _ (by simp)) (fun e => hne _ (by simp) y hy e.symm)))
      (by have := hL.le y (hI.sl y hy); omega)
  have er := rext_r E c hrd
  have hI₁ : Inv M base size m Sl ([r.x, r.y, r.z] ++ V) (rext E r c) s₁ := by
    refine ⟨hs₁, hI.mod.unch U₁ (fun w hw => ?_) hn, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> dsimp only <;>
        exact (hL.mo _ (hrSl _ (by simp))).symm
    · rcases List.mem_append.mp hx with hx | hx
      · exact hrSl x hx
      · exact hI.sl x hx
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [e₁]; exact hI.lt _ (hcV _ cx)
        · rw [e₂]; exact hI.lt _ (hcV _ cy)
        · rw [e₃]; exact hI.lt _ (hcV _ cz)
      · rw [wv x hx]; exact hI.lt x hx
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [e₁, er.1]; exact hI.val _ (hcV _ cx)
        · rw [e₂, er.2.1]; exact hI.val _ (hcV _ cy)
        · rw [e₃, er.2.2]; exact hI.val _ (hcV _ cz)
      · rw [wv x hx, rext_of (fun h => hrV x h hx)]; exact hI.val x hx
  have hr₁ := hr.unch hpa (hSl _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (by omega) U₁ hfar
  refine WP.mono (addP_ok hL hAl hm hA hSl hLow hpa hI₁ hV hr₁) fun s₂ ⟨k₂, I₂, v₂⟩ => ⟨?_, I₂, v₂⟩
  have hx1 : Reg.x1 ∈ clob M.n := by simp [clob]
  refine ⟨fun r' hr' => (k₂.gpr r' hr').trans (k₁.gpr r' (by intro h; simp only [List.mem_singleton] at h; exact hr' (h ▸ hx1))),
    k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩
  rw [k₂.mem x (fun w hw => hx w (List.mem_append_right _ hw)) ht]
  exact U₁ x fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact hx _ (by simp)

end VG.Proof.Weierstrass.AArch64
