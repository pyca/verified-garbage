import VerifiedGarbage.Proof.Weierstrass.X86.Pow
import VerifiedGarbage.Impl.Weierstrass.X86.PowChain

/-! # State and frames for fixed exponentiation chains -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

structure PowerState (P : PowCfg) (base : Addr) (size m : Nat) [NeZero m]
    (B : Fin m) (a t : Nat) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW P.M size m s.mem base
  base_lt : wordsVal s.mem base P.base P.M.n < m
  base_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) = B
  acc_lt : wordsVal s.mem base P.acc P.M.n < m
  acc_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.acc P.M.n) = B ^ a
  tmp_lt : wordsVal s.mem base P.tmp P.M.n < m
  tmp_val : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.tmp P.M.n) = B ^ t

theorem powWx_mo {P : PowCfg} {size wk : Nat} (hL : PowLay P size) (hW : PowWk P size wk) :
    ∀ w ∈ powWx P wk, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo := by
  intro w hw
  simp only [powWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.mo_w w hw
  · exact .inl hW.mo

theorem powWx_base {P : PowCfg} {size wk : Nat} (hL : PowLay P size) (hW : PowWk P size wk) :
    ∀ w ∈ powWx P wk, P.base + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.base := by
  intro w hw
  simp only [powWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.base_w w hw
  · exact .inl hW.base

theorem PowerState.rebuild {P : PowCfg} {base : Addr} {size wk m a t a' t' : Nat} [NeZero m]
    {B : Fin m} {s u : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P size wk)
    (hs : Scr u base size) (U : Unch base (powWx P wk) s.mem u.mem)
    (ha : wordsVal u.mem base P.acc P.M.n < m)
    (va : toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) = B ^ a')
    (ht : wordsVal u.mem base P.tmp P.M.n < m)
    (vt : toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.tmp P.M.n) = B ^ t') :
    PowerState P base size m B a' t' u := by
  have hn := I.scr.nowrap
  have hmo := I.mod.mo
  have hbase := hL.base
  have em := U.wordsVal (powWx_mo hL hW) (by omega)
  have eb := U.wordsVal (powWx_base hL hW) (by omega)
  exact ⟨hs, ⟨I.mod.n0, I.mod.mo, I.mod.tmp, I.mod.sep, em.trans I.mod.val, I.mod.inv, I.mod.red⟩,
    eb ▸ I.base_lt, by rw [eb]; exact I.base_val, ha, va, ht, vt⟩

theorem PowerState.regs {P : PowCfg} {base : Addr} {size m a t : Nat} [NeZero m]
    {B : Fin m} {s u : State} (I : PowerState P base size m B a t s)
    {rs : List Reg} (K : Keeps rs s u) (he : Reg.edi ∉ rs) (hm : u.mem = s.mem) :
    PowerState P base size m B a t u := by
  refine ⟨I.scr.of_keeps K he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hm]
  · exact I.mod
  · exact I.base_lt
  · exact I.base_val
  · exact I.acc_lt
  · exact I.acc_val
  · exact I.tmp_lt
  · exact I.tmp_val

end VG.Proof.Weierstrass.X86
