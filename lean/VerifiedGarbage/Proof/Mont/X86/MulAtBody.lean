module

public import VerifiedGarbage.Proof.Mont.X86.MulAtABI
import VerifiedGarbage.Proof.Framework.Omega

/-! # The callable multiplication's body

`mulAtBody_ok`: from the contract's precondition, the body saves the
callee-saved registers in slot 1, copies `b` beside them, multiplies, copies
the product to `o` and restores the registers; it changes only slots 1 and 2
and the result's bytes.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Spec.Rsa.MontMulAt

theorem atSlots_fits {n : Nat} (hn : 2 ≤ n) : Fits (contextBytes n) (atSlots n) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [atSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only [atSave, contextBytes, slot, stride] <;> omega
  · simp [atSlots]

/-- The four saved words, at `atSave n`. -/
theorem saveMem_atSlots (m : Mem) (base : Addr) (g : Reg → BitVec 32) (n : Nat)
    (h : atSave n + 16 ≤ 2 ^ 64) :
    Outside base (atSave n) 16 m (saveMem m (off base) g (atSlots n)) := by
  simp only [atSlots, saveMem]
  exact (((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
    ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))).trans
    (((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)))

/-- The save block: `edi` the working space's base, the caller's registers
saved in slot 1, `esi` at `b`. -/
theorem saveAt_ok {n : Nat} (hn : 2 ≤ n) {s : State} (A : MulABI n s) :
    WP isa (.block (atSaveCode n ++ pointAt argB)) s fun t =>
      Scr t (wsOf s) (contextBytes n) ∧ Saved t.mem (off (wsOf s)) s.gpr (atSlots n) ∧
      Outs (wsOf s) [(atSave n, 16)] s.mem t.mem ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (arg s 3).toNat ∧
      Keeps [.eax, .edi, .esi] s t := by
  have nw := A.nowrap
  have hfit := atSlots_fits hn
  have hsz : atSave n + 16 ≤ contextBytes n := by simp only [atSave, contextBytes, slot, stride]; omega
  have ha0 : (arg s 0).toNat = (wsOf s).toNat := by
    simp only [wsOf, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]
  have hwr : (⟨wsOf s, contextBytes n⟩ : Region) ∈ s.wr := by
    rw [A.wr, contextBytes_div]; exact List.mem_singleton_self _
  unfold atSaveCode pointAt
  simp only [List.append_assoc, List.singleton_append]
  refine wp_movS (A.readArg (i := 0) (by decide)) fun u U _ => ?_
  change WP isa (.block (saveCode .eax (atSlots n) ++ (.mov .edi (.reg .eax) :: pointAt argB))) u _
  refine save_ofNat_ok (atSlots n) hfit (by rw [U.gpr]; omega) (fun p hp => ?_) fun v V => ?_
  · rw [U.gpr, U.wr]
    exact ⟨_, hwr, Offset.contains_base _ (by have := hfit.1 p hp; omega) (by have := hfit.1 p hp; omega)⟩
  refine wp_mov fun w W => ?_
  have M : v.mem = saveMem s.mem (off (wsOf s)) s.gpr (atSlots n) := by
    rw [V.mem, U.mem, U.gpr]
    apply saveMem_congr (atSlots n) s.mem (fun _ _ => rfl)
    intro p hp
    apply U.other
    simp only [atSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  have Ov : Outs (wsOf s) [(atSave n, 16)] s.mem v.mem := by
    rw [M]; exact Outs.of_outside (saveMem_atSlots _ _ _ n (by omega)) (List.mem_singleton_self _)
  have Kw : Keeps [.eax, .edi, .esi] s w :=
    ((U.keeps.mono (by decide)).trans ⟨fun r hr => by rw [V.gpr], V.rd, V.wr⟩).trans (W.keeps.mono (by decide))
  have hB : readSrc w (.mem argB) = some (arg s 3) := by
    show readSrc w (.mem (at_ .esp (4 + 4 * 3))) = _
    rw [readSrc_keep (A.argFar (i := 3) (by decide)) (by rw [W.mem]; exact Ov)
      (by simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega)
      (Kw.1 _ (by decide)) Kw.2.1 Kw.2.2]
    exact A.readArg (i := 3) (by decide)
  refine wp_movS hB fun x X _ => wp_addS rfl fun y Y _ => WP.block_nil ⟨⟨?_, ?_, nw, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Y.other _ (by decide), X.other _ (by decide), W.gpr, V.gpr, U.gpr]
  · rw [Y.wr, X.wr, W.wr, V.wr, U.wr]; exact hwr
  · rw [Y.other _ (by decide), X.other _ (by decide), Kw.1 _ (by decide)]; exact A.stk
  · rw [Y.mem, X.mem, W.mem, M]; exact saveMem_saved_ofNat s.mem (wsOf s) s.gpr hfit (by omega)
  · rw [Y.mem, X.mem, W.mem]; exact Ov
  · rw [Y.gpr, Y.other .edi (by decide), X.gpr, X.other .edi (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm]
  · exact (Kw.trans (X.keeps.mono (by decide))).trans (Y.keeps.mono (by decide))

/-- The saved words lie at `atSave n`, 16 bytes. -/
theorem atSlots_range {n : Nat} : ∀ p ∈ atSlots n, atSave n ≤ p.2 ∧ p.2 + 4 ≤ atSave n + 16 := by
  intro p hp
  simp only [atSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> omega

/-- A word apart from every range that changed. -/
theorem Outs.readW32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega

/-- Changes within one range, as changes within a range around it. -/
theorem outside_of_outs1 {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outs base [(o', n')] m m')
    (h₁ : o ≤ o') (h₂ : o' + n' ≤ o + n) : Outside base o n m m' :=
  fun x hx => h x (by simp only [List.mem_singleton, forall_eq]; omega)

/-- `mulAt`'s changes, within slots 1 and 2. -/
theorem outside_of_mulAt {base : Addr} {n : Nat} {m m' : Mem}
    (h : Outs base [((contextMod n).tmp, 8 * (contextMod n).n), (slot n 2, accLen (contextMod n))] m m') :
    Outside base (slot n 1) (2 * stride n) m m' := by
  have e1 : slot n 1 = 64 + (16 * n + 8) := by unfold slot stride; omega
  have e2 : slot n 2 = 64 + 2 * (16 * n + 8) := by unfold slot stride; omega
  have eA : accLen (contextMod n) = 16 * n + 4 := by simp only [accLen, words, contextMod]; omega
  have eT : (contextMod n).tmp = slot n 1 := rfl
  have eN : (contextMod n).n = n := rfl
  intro x hx
  apply h x
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> simp only [stride] at hx ⊢ <;> omega

theorem mulAtBody_ok {n : Nat} (hn : 2 ≤ n) {s : State} (A : MulABI n s) :
    WP isa (mulAtBody n) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outs (wsOf s) [(slot n 1, 2 * stride n), ((arg s 1).toNat, 8 * n)] s.mem t.mem ∧
      wordsVal t.mem (wsOf s) (arg s 1).toNat n < wordsVal s.mem (wsOf s) (slot n 0) n ∧
      wordsVal t.mem (wsOf s) (arg s 1).toNat n * 2 ^ (64 * n) % wordsVal s.mem (wsOf s) (slot n 0) n =
        wordsVal s.mem (wsOf s) (arg s 2).toNat n * wordsVal s.mem (wsOf s) (arg s 3).toNat n %
          wordsVal s.mem (wsOf s) (slot n 0) n := by
  have nw := A.nowrap
  have e0 : slot n 0 = 64 := by unfold slot stride; omega
  have e1 : slot n 1 = 64 + (16 * n + 8) := by unfold slot stride; omega
  have e2 : slot n 2 = 64 + 2 * (16 * n + 8) := by unfold slot stride; omega
  have eS : stride n = 16 * n + 8 := rfl
  have eC : contextBytes n = 64 + 9 * (16 * n + 8) := by unfold contextBytes slot stride; omega
  have eB : atB n = slot n 1 + 4 := rfl
  have eV : atSave n = slot n 1 + 4 + 8 * n := rfl
  have eAcc : accLen (contextMod n) = 16 * n + 4 := by simp only [accLen, words, contextMod]; omega
  have eT : (contextMod n).tmp = slot n 1 := rfl
  have eMo : (contextMod n).mo = slot n 0 := rfl
  have eN : (contextMod n).n = n := rfl
  have ediv : 8 * (contextBytes n / 8) = contextBytes n := by rw [Nat.mul_comm]; exact contextBytes_div n
  have oL := A.o_le; have aL := A.a_le; have bL := A.b_le
  rw [ediv] at oL aL bL
  have oS := A.o_scr; have aS := A.a_scr; have bS := A.b_scr
  simp only [Apart] at oS aS bS
  have hsub : ∀ r ∈ [(slot n 1, 2 * stride n)], r ∈ [(slot n 1, 2 * stride n), ((arg s 1).toNat, 8 * n)] :=
    fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
  unfold mulAtBody
  -- Save the registers, `esi` at `b`.
  refine WP.seq (WP.mono (saveAt_ok hn A) fun t₁ ⟨S₁, Sv₁, O₁, E₁, K₁⟩ => ?_)
  -- Copy `b` into slot 1.
  refine WP.seq (WP.mono (copyIn_ok S₁ (k := 2 * n) (src := (arg s 3).toNat) (dst := atB n) (by omega)
    (by omega) (by omega) (by omega) E₁) fun t₂ ⟨V₂, O₂, _, K₂⟩ => ?_)
  have S₂ := S₁.of_keeps K₂ (by decide)
  have Ow : Outside (wsOf s) (slot n 1) (2 * stride n) s.mem t₂.mem :=
    (outside_of_outs1 O₁ (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))
  have OS₂ : Outs (wsOf s) [(slot n 1, 2 * stride n)] s.mem t₂.mem := Outs.of_outside Ow (List.mem_singleton_self _)
  have hrS : ∀ r ∈ [(slot n 1, 2 * stride n)], r.1 + r.2 ≤ contextBytes n := by
    simp only [List.mem_singleton, forall_eq]; omega
  have esp₂ : t₂.gpr .esp = s.gpr .esp := (K₂.1 _ (by decide)).trans (K₁.1 _ (by decide))
  have rd₂ : t₂.rd = s.rd := K₂.2.1.trans K₁.2.1
  have wr₂ : t₂.wr = s.wr := K₂.2.2.trans K₁.2.2
  have hb₂ : wordsVal t₂.mem (wsOf s) (atB n) n = wordsVal s.mem (wsOf s) (arg s 3).toNat n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, V₂,
      O₁.val32 (by simp only [List.mem_singleton, forall_eq]; omega) (by omega)]
  have ha₂ : wordsVal t₂.mem (wsOf s) (arg s 2).toNat n = wordsVal s.mem (wsOf s) (arg s 2).toNat n :=
    Ow.wordsVal (by omega) (by omega)
  -- Multiply.
  have hM : Modulus (contextMod n) (contextBytes n) (wordsVal s.mem (wsOf s) (slot n 0) n) t₂.mem (wsOf s) :=
    ⟨by omega, by omega, by omega, by omega, Ow.wordsVal (d := slot n 0) (k := n) (by omega) (by omega)⟩
  have hinv₂ : (wordsVal s.mem (wsOf s) (slot n 0) n * w32 t₂.mem (wsOf s) 0 + 1) % 2 ^ 32 = 0 := by
    rw [Ow.w32 (d := 0) (by omega) (by omega), ← numAt_eq4, ← numAt_eq8]; exact A.inv
  have hB : wordsVal t₂.mem (wsOf s) (atB n) (contextMod n).n < wordsVal s.mem (wsOf s) (slot n 0) n := by
    show wordsVal t₂.mem (wsOf s) (atB n) n < _
    rw [hb₂, ← numAt_eq8, ← numAt_eq8]; exact A.bLt
  have hA : readSrc t₂ (.mem argA) = some (BitVec.ofNat 32 (arg s 2).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show readSrc t₂ (.mem (at_ .esp (4 + 4 * 2))) = _
    rw [readSrc_keep (A.argFar (i := 2) (by decide)) OS₂ hrS esp₂ rd₂ wr₂]
    exact A.readArg (by decide)
  refine WP.seq (WP.mono (mulAt_ok S₂ hM (inv := 0) (acc := slot n 2) (a := (arg s 2).toNat) (b := atB n)
    (by omega) (.inl (by omega)) hinv₂ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hB (by omega) (.inr (by omega)) (.inl (by omega)) hA
    ((A.argFar (i := 2) (by decide)).keep esp₂)) fun t₃ ⟨K₃, O₃, L₃, C₃⟩ => ?_)
  have S₃ := S₂.of_keeps K₃ (by decide)
  have O₃' : Outs (wsOf s) [(slot n 1, 2 * stride n)] t₂.mem t₃.mem :=
    Outs.of_outside (outside_of_mulAt O₃) (List.mem_singleton_self _)
  have esp₃ : t₃.gpr .esp = s.gpr .esp := (K₃.1 _ (by decide)).trans esp₂
  have rd₃ : t₃.rd = s.rd := K₃.2.1.trans rd₂
  have wr₃ : t₃.wr = s.wr := K₃.2.2.trans wr₂
  have hO : readSrc t₃ (.mem argO) = some (arg s 1) := by
    show readSrc t₃ (.mem (at_ .esp (4 + 4 * 1))) = _
    rw [readSrc_keep (A.argFar (i := 1) (by decide)) (OS₂.trans O₃') hrS esp₃ rd₃ wr₃]
    exact A.readArg (by decide)
  -- `esi` at `o`.
  refine WP.seq (wp_movS hO fun u U _ => wp_addS rfl fun v V _ => WP.block_nil ?_)
  have S₄ : Scr v (wsOf s) (contextBytes n) := S₃.of_keeps (U.keeps.trans V.keeps) (by decide)
  have E₄ : v.gpr .esi = v.gpr .edi + BitVec.ofNat 32 (arg s 1).toNat := by
    rw [V.gpr, V.other .edi (by decide), U.gpr, U.other .edi (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm]
  have mem₄ : v.mem = t₃.mem := by rw [V.mem, U.mem]
  -- Copy the product to `o`.
  refine WP.seq (WP.mono (copyOut_ok S₄ (k := 2 * n) (src := slot n 2) (dst := (arg s 1).toNat) (by omega)
    (by omega) (by omega) (by omega) E₄) fun t₅ ⟨V₅, O₅, _, K₅⟩ => ?_)
  have S₅ := S₄.of_keeps K₅ (by decide)
  have esp₅ : t₅.gpr .esp = s.gpr .esp := by
    rw [K₅.1 _ (by decide), V.other _ (by decide), U.other _ (by decide)]; exact esp₃
  have Sv₅ : Saved t₅.mem (off (wsOf s)) s.gpr (atSlots n) := Sv₁.of_readW fun p hp => by
    have hp' := atSlots_range p hp
    have hp2 : p.2 + 4 ≤ 2 ^ 64 := by omega
    rw [Outs.readW32 (d := p.2) (Outs.of_outside O₅ (List.mem_singleton_self _))
        (by simp only [List.mem_singleton, forall_eq]; omega) hp2, mem₄,
      Outs.readW32 (d := p.2) O₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> dsimp only <;> omega) hp2,
      Outs.readW32 (d := p.2) (Outs.of_outside O₂ (List.mem_singleton_self _))
        (by simp only [List.mem_singleton, forall_eq]; omega) hp2]
  -- Restore the registers.
  change WP isa (.block (restoreCode .edi ([(.ebx, atSave n), (.esi, atSave n + 4), (.ebp, atSave n + 8)] ++
    [(.edi, atSave n + 12)]) ++ [])) t₅ _
  refine restoreBase_ok (g := s.gpr) _ (by simp) (fun p hp => ?_) (fun p hp => ?_) fun t₆ R => WP.block_nil ?_
  · have := (atSlots_fits hn).1 p hp
    rw [addr_eq (by rw [S₅.edi_toNat]; omega), S₅.edi]; exact S₅.read (by omega)
  · have := (atSlots_fits hn).1 p hp
    rw [addr_eq (by rw [S₅.edi_toNat]; omega), S₅.edi]; exact Sv₅ p hp
  have hv : wordsVal t₆.mem (wsOf s) (arg s 1).toNat n = wordsVal t₃.mem (wsOf s) (slot n 2) n := by
    rw [R.mem, wordsVal_eq_val32, wordsVal_eq_val32, V₅, mem₄]
  refine ⟨R.abi (by simp [calleeSaved]) (by simp) esp₅, ?_, ?_, ?_, hv ▸ L₃, ?_⟩
  · rw [R.rd, K₅.2.1, V.rd, U.rd]; exact rd₃
  · rw [R.wr, K₅.2.2, V.wr, U.wr]; exact wr₃
  · rw [R.mem]
    exact (((Outs.mono OS₂ hsub).trans (Outs.mono O₃' hsub)).trans (mem₄ ▸ Outs.refl _ _ _)).trans
      (Outs.of_outside O₅ (by
        rw [show 4 * (2 * n) = 8 * n by omega]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · rw [hv, ← hb₂, ← ha₂]; exact C₃

end VG.Proof.Mont.X86.Dynamic
