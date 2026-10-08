import VerifiedGarbage.Proof.Blowfish.X86_64.Lookup
import VerifiedGarbage.Proof.Blowfish.F

/-! # F: four lookups, combined in the low doubleword of `fReg` -/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The vector registers F writes. -/
def fXRegs : List XReg := fReg :: lookXRegs

/-- Only F's registers and the flags change. -/
structure FOnly (s s' : State) : Prop where
  xmm : ∀ d, d ∉ fXRegs → s'.xmm d = s.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → g ≠ .r11 → s'.gpr g = s.gpr g
  eq : s' = { s with gpr := s'.gpr, xmm := s'.xmm, cf := s'.cf, zf := s'.zf, sf := s'.sf, of := s'.of }

/-- `a` is `c` with other registers and flags. -/
def Upd (c a : State) : Prop :=
  a = { c with gpr := a.gpr, xmm := a.xmm, cf := a.cf, zf := a.zf, sf := a.sf, of := a.of }

theorem Upd.trans {a b c : State} (h1 : Upd b a) (h2 : Upd c b) : Upd c a := by
  unfold Upd at *; rw [h1]; rw [h2]

theorem Upd.setXmm {a c : State} (h : Upd c a) (d : XReg) (v : BitVec 128) : Upd c (a.setXmm d v) := by
  unfold Upd at *; rw [h]; rfl

theorem FOnly.refl (s : State) : FOnly s s := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, state_eta s⟩

theorem FOnly.env {sch : Reg} {S : Addr} {s t : State} (E : LookEnv sch S s) (h : FOnly s t) : LookEnv sch S t := by
  have hrd : t.rd = s.rd := by rw [h.eq]
  have hwr : t.wr = s.wr := by rw [h.eq]
  refine ⟨by rw [h.gpr _ E.ne8 E.ne9 E.ne11, E.hsch], E.ne8, E.ne9, E.ne11, fun off ho => ?_,
    by rw [h.xmm _ (by decide), E.ones], by rw [h.xmm _ (by decide), E.sixteen], by rw [h.xmm _ (by decide), E.low]⟩
  rw [hrd, hwr]; exact E.rd off ho

theorem combineX_0 : combineX 0 = .bin .movdqa fReg (accReg 0) := rfl
theorem combineX_1 : combineX 1 = .bin .paddd fReg (accReg 0) := rfl
theorem combineX_2 : combineX 2 = .bin .pxor fReg (accReg 0) := rfl
theorem combineX_3 : combineX 3 = .bin .paddd fReg (accReg 0) := rfl

theorem dword_xor (a b : BitVec 128) : dword (a ^^^ b) 0 = dword a 0 ^^^ dword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, decide_eq_true hi, Bool.true_and]

/-- A lookup, then its combination, from a state that F's registers alone
separate from `s`. -/
theorem fstep {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) {j : Nat} (hj : j < 4) {t : State}
    (O : FOnly s t) (hf : 0 < j → dword (t.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1)) :
    WP isa (.seq (lookup sch j) (.block [combine j])) t (fun t' =>
      dword (t'.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) j ∧ FOnly s t') := by
  have hm : t.mem = s.mem := by rw [O.eq]
  have hx : t.xmm xL = s.xmm xL := O.xmm _ (by decide)
  apply WP.seq
  refine WP.mono (lookup_run (O.env E) hj) fun u ⟨hu, L⟩ => ?_
  rw [hm, hx] at hu
  refine WP.of_runBlock ⟨(combineX j).exec u, runXops [combineX j] u, ?_, ?_⟩
  · have hf' : 0 < j → dword (u.xmm fReg) 0 = fAcc (scheduleAt s.mem S) (dword (s.xmm xL) 0) (j - 1) :=
      fun h => by rw [L.xmm _ (by decide)]; exact hf h
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp only [combineX_0, XOp.exec, xmm_setXmm_self, eval_movdqa]; exact hu
    · simp only [combineX_1, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
    · simp only [combineX_2, XOp.exec, xmm_setXmm_self, XBinOp.eval]
      rw [dword_xor, hf' (by decide), hu]; rfl
    · simp only [combineX_3, XOp.exec, xmm_setXmm_self, XBinOp.eval, dword_ofDwords_0]
      rw [hf' (by decide), hu]; rfl
  · have hx : ((combineX j).exec u) = u.setXmm fReg (((combineX j).exec u).xmm fReg) := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp only [combineX_0, combineX_1, combineX_2, combineX_3, XOp.exec, xmm_setXmm_self] <;> rfl
    refine ⟨fun d hd => ?_, fun g h8 h9 h11 => ?_, ?_⟩
    · have n : d ≠ fReg := fun e => hd (by rw [e]; decide)
      have hl : d ∉ lookXRegs := fun h => hd (List.mem_cons_of_mem _ h)
      rw [hx, xmm_setXmm_of_ne _ _ n, L.xmm _ hl, O.xmm _ hd]
    · rw [hx, gpr_setXmm, L.gpr _ h8 h9 h11, O.gpr _ h8 h9 h11]
    · rw [hx]; exact Upd.setXmm (Upd.trans L.eq O.eq) _ _

theorem f_run {sch : Reg} {S : Addr} {s : State} (E : LookEnv sch S s) :
    WP isa (f sch) s (fun s' =>
      dword (s'.xmm fReg) 0 = Spec.Blowfish.f (scheduleAt s.mem S) (dword (s.xmm xL) 0) ∧ FOnly s s') := by
  rw [Impl.Blowfish.X86_64.f]
  have st := fun (j : Nat) (hj : j < 4) (t : State) (O : FOnly s t) hf => WP.seq_iff.mp (fstep E hj O hf)
  apply WP.seq
  refine WP.mono (st 0 (by decide) s (FOnly.refl s) (fun h => absurd h (by decide))) fun t0 h0 => ?_
  apply WP.seq
  refine WP.mono h0 fun u0 ⟨v0, O0⟩ => ?_
  apply WP.seq
  refine WP.mono (st 1 (by decide) u0 O0 (fun _ => v0)) fun t1 h1 => ?_
  apply WP.seq
  refine WP.mono h1 fun u1 ⟨v1, O1⟩ => ?_
  apply WP.seq
  refine WP.mono (st 2 (by decide) u1 O1 (fun _ => v1)) fun t2 h2 => ?_
  apply WP.seq
  refine WP.mono h2 fun u2 ⟨v2, O2⟩ => ?_
  apply WP.seq
  refine WP.mono (st 3 (by decide) u2 O2 (fun _ => v2)) fun t3 h3 => ?_
  refine WP.mono h3 fun u3 ⟨v3, O3⟩ => ⟨by rw [v3, fAcc_three], O3⟩

end VG.Proof.Blowfish.X86_64
