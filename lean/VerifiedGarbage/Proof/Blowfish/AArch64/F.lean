import VerifiedGarbage.Proof.Blowfish.AArch64.Sbox
import VerifiedGarbage.Proof.Blowfish.F

/-!
# F on sixteen words

`f_run`: from the byte planes of sixteen words `x n` in `idxReg` (`planes`),
`f sch` leaves `F(x n)` in word `n % 4` of `fReg (n / 4)`, under the
schedule at `sch`.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-- What `combine j` does to a register of F and a register of words. -/
def cop (j : Nat) (x y : BitVec 128) : BitVec 128 :=
  if j = 0 then y else if j = 2 then x ^^^ y else VArr.s4.map2 (fun _ a b => a + b) x y

theorem vword_cop (j : Nat) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (cop j x y) l =
      if j = 0 then vword y l else if j = 2 then vword x l ^^^ vword y l else vword x l + vword y l := by
  simp only [cop]
  split
  · rfl
  · split
    · exact vword_xor x y l
    · exact vword_map2 _ x y hl

theorem exec_combine (s : State) (j : Nat) {k : Nat} (hk : k < 4) :
    exec ((combine j).getD k (.vop (.movi0 .v0))) s =
      some (s.setV (fReg k) (cop j (s.v (fReg k)) (s.v (wordReg k)))) := by
  simp only [combine, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, cop]
  split
  · rfl
  · split <;> rfl

def fRegs : List VReg := [.v12, .v13, .v14, .v15]

theorem wordReg_ne_fReg : ∀ k < 4, ∀ k' < 4, wordReg k ≠ fReg k' := by decide
theorem fReg_ne : ∀ k < 4, ∀ k' < 4, k ≠ k' → fReg k ≠ fReg k' := by decide

theorem combine_run (s : State) (j : Nat) :
    ∃ s', runBlock isa (combine j) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = cop j (s.v (fReg k)) (s.v (wordReg k))) ∧ VOnly fRegs s s' := by
  let t (k : Nat) (u : State) := u.setV (fReg k) (cop j (u.v (fReg k)) (u.v (wordReg k)))
  let s₁ := t 0 s
  let s₂ := t 1 s₁
  let s₃ := t 2 s₂
  let s₄ := t 3 s₃
  have e : ∀ (k : Nat) (u : State), k < 4 →
      exec ((combine j).getD k (.vop (.movi0 .v0))) u = some (t k u) := fun k u hk => by
    rw [exec_combine _ _ hk]
  have hl : combine j = [(combine j).getD 0 (.vop (.movi0 .v0)), (combine j).getD 1 (.vop (.movi0 .v0)),
      (combine j).getD 2 (.vop (.movi0 .v0)), (combine j).getD 3 (.vop (.movi0 .v0))] := by
    simp only [combine, List.getD_eq_getElem?_getD]; rfl
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, e 0 s (by decide), runStep_some, runBlock_cons, e 1 s₁ (by decide),
      runStep_some, runBlock_cons, e 2 s₂ (by decide), runStep_some, runBlock_cons,
      e 3 s₃ (by decide), runStep_some, runBlock_nil]
  · have wk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → (t k' u).v (wordReg k) = u.v (wordReg k) :=
      fun k hk u k' hk' => v_setV_of_ne _ _ (wordReg_ne_fReg k hk k' hk')
    have fk : ∀ k < 4, ∀ (u : State) (k' : Nat), k' < 4 → k ≠ k' → (t k' u).v (fReg k) = u.v (fReg k) :=
      fun k hk u k' hk' hne => v_setV_of_ne _ _ (fReg_ne k hk k' hk' hne)
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [fk 0 (by decide) _ 3 (by decide) (by decide), fk 0 (by decide) _ 2 (by decide) (by decide),
        fk 0 (by decide) _ 1 (by decide) (by decide)]
      exact v_setV_self _ _ _
    · rw [fk 1 (by decide) _ 3 (by decide) (by decide), fk 1 (by decide) _ 2 (by decide) (by decide)]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self, fk 1 (by decide) _ 0 (by decide) (by decide), wk 1 (by decide) _ 0 (by decide)]
    · rw [fk 2 (by decide) _ 3 (by decide) (by decide)]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self, fk 2 (by decide) _ 1 (by decide) (by decide), fk 2 (by decide) _ 0 (by decide) (by decide),
        wk 2 (by decide) _ 1 (by decide), wk 2 (by decide) _ 0 (by decide)]
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self, fk 3 (by decide) _ 2 (by decide) (by decide), fk 3 (by decide) _ 1 (by decide) (by decide),
        fk 3 (by decide) _ 0 (by decide) (by decide), wk 3 (by decide) _ 2 (by decide),
        wk 3 (by decide) _ 1 (by decide), wk 3 (by decide) _ 0 (by decide)]
  · exact (((VOnly.setV s (by simp [fRegs, fReg]) _).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans
      (VOnly.setV _ (by simp [fRegs, fReg]) _)).trans (VOnly.setV _ (by simp [fRegs, fReg]) _)

/-! ## One S-box of F -/

/-- Word `n` of sixteen in the registers `R`. -/
def lane (v : VReg → BitVec 128) (R : Nat → VReg) (n : Nat) : Word := vword (v (R (n / 4))) (n % 4)

def stepRegs : List VReg := lookupRegs ++ wordsRegs ++ fRegs

theorem fAcc_step (K : Schedule) (x : Word) {j : Nat} (hj : j < 4) (prev : Word)
    (hp : 0 < j → prev = fAcc K x (j - 1)) :
    (if j = 0 then sq K x j else if j = 2 then prev ^^^ sq K x j else prev + sq K x j) = fAcc K x j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rfl
  · rw [hp (by decide)]; rfl
  · rw [hp (by decide)]; rfl
  · rw [hp (by decide)]; rfl

theorem fReg_notin : ∀ k < 4, fReg k ∉ lookupRegs ∧ fReg k ∉ wordsRegs := by decide

theorem sbox_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) {j : Nat} (hj : j < 4)
    (x : Nat → Word) (hx : ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j)
    (hprev : 0 < j → ∀ n < 16, lane s.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) (j - 1)) :
    ∃ s', runBlock isa (lookup sch j ++ words ++ combine j) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = fAcc (scheduleAt s.mem (s.gpr sch)) (x n) j) ∧
      VOnly stepRegs s s' := by
  let K := scheduleAt s.mem (s.gpr sch)
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run hR hc hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := combine_run s₂ j
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_, ?_⟩
  · intro n hn
    have hk : n / 4 < 4 := by omega
    have hl : n % 4 < 4 := by omega
    -- the words of S-box `j`
    have w : vword (s₂.v (wordReg (n / 4))) (n % 4) = sq K (x n) j := by
      refine word_ext fun b hb => ?_
      rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega, v₁ _ hb _ hn, hx n hn,
        sq, sEntry_byte _ _ hj hb]
      rfl
    have f₂ : s₂.v (fReg (n / 4)) = s.v (fReg (n / 4)) := by
      rw [o₂.2 _ (fReg_notin _ hk).2, o₁.2 _ (fReg_notin _ hk).1]
    simp only [lane]
    rw [v₃ _ hk, vword_cop _ _ _ hl, w, f₂]
    exact fAcc_step K (x n) hj _ fun h => hprev h n hn
  · exact ((VOnly.mono o₁ (by decide)).trans (VOnly.mono o₂ (by decide))).trans (VOnly.mono o₃ (by decide))

theorem idx_notin_step : ∀ j < 4, idxReg j ∉ stepRegs := by decide
theorem const_notin_step : c64 ∉ stepRegs ∧ c128 ∉ stepRegs := by decide

theorem f_eq (sch : Reg) :
    f sch = (lookup sch 0 ++ words ++ combine 0) ++ ((lookup sch 1 ++ words ++ combine 1) ++
      ((lookup sch 2 ++ words ++ combine 2) ++ ((lookup sch 3 ++ words ++ combine 3) ++ []))) := rfl

/-- F of sixteen words whose byte planes are in `idxReg`. -/
theorem f_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) (x : Nat → Word)
    (hx : ∀ j < 4, ∀ n < 16, vbyte (s.v (idxReg j)) n = quarter (x n) j) :
    ∃ s', runBlock isa (f sch) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = Spec.Blowfish.f (scheduleAt s.mem (s.gpr sch)) (x n)) ∧
      VOnly stepRegs s s' := by
  have keep : ∀ {t : State}, VOnly stepRegs s t →
      Readable t sch ∧ Consts t ∧ (∀ j < 4, ∀ n < 16, vbyte (t.v (idxReg j)) n = quarter (x n) j) ∧
        t.mem = s.mem ∧ t.gpr = s.gpr := by
    intro t ht
    refine ⟨fun off hoff => ?_, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj n hn => ?_, ht.mem, ht.gpr⟩
    · rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
    · rw [ht.2 _ const_notin_step.1]; exact hc.1 e he
    · rw [ht.2 _ const_notin_step.2]; exact hc.2 e he
    · rw [ht.2 _ (idx_notin_step j hj)]; exact hx j hj n hn
  obtain ⟨s₀, r₀, v₀, o₀⟩ := sbox_run hR hc (by decide : 0 < 4) x (hx 0 (by decide)) (by intro h; omega)
  have k₀ := keep o₀
  obtain ⟨s₁, r₁, v₁, o₁⟩ := sbox_run k₀.1 k₀.2.1 (by decide : 1 < 4) x (k₀.2.2.1 1 (by decide))
    (fun _ n hn => by rw [v₀ n hn, k₀.2.2.2.1, k₀.2.2.2.2])
  have p₁ := o₀.trans o₁
  have k₁ := keep p₁
  obtain ⟨s₂, r₂, v₂, o₂⟩ := sbox_run k₁.1 k₁.2.1 (by decide : 2 < 4) x (k₁.2.2.1 2 (by decide))
    (fun _ n hn => by rw [v₁ n hn, k₀.2.2.2.1, k₀.2.2.2.2, k₁.2.2.2.1, k₁.2.2.2.2])
  have p₂ := p₁.trans o₂
  have k₂ := keep p₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := sbox_run k₂.1 k₂.2.1 (by decide : 3 < 4) x (k₂.2.2.1 3 (by decide))
    (fun _ n hn => by rw [v₂ n hn, k₁.2.2.2.1, k₁.2.2.2.2, k₂.2.2.2.1, k₂.2.2.2.2])
  have p₃ := p₂.trans o₃
  refine ⟨s₃, ?_, fun n hn => ?_, p₃⟩
  · rw [f_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · rw [v₃ n hn, k₂.2.2.2.1, k₂.2.2.2.2, fAcc_three]

end VG.Proof.Blowfish.AArch64
