module

import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
import VerifiedGarbage.Proof.Curve448.AArch64.Copy

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Move

import VerifiedGarbage.Proof.Ed448.AArch64.Window.Checks
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK
public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.FinalSwap
import VerifiedGarbage.Proof.X448.AArch64.Ladder
import VerifiedGarbage.Proof.X448.AArch64.Weak.Ladder
import VerifiedGarbage.Proof.X448.AArch64.Finish
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.X448.AArch64.Fast.SaveX
public import VerifiedGarbage.Proof.X448.AArch64.Fast.VSave
public import VerifiedGarbage.Proof.X448.AArch64.Env
public import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Ed448 verification on AArch64: the result

Untrusted: everything here is checked by Lean. `wfinish`: slots 12 and 13,
then 14 and 15, compared by two passes of `wcmp` (`eqSlotsF_ok`, each check
ORed into `x20`, then slots 14 and 15 copied into 12 and 13; `wloop_ok`), the
result `x0 = (x20 == 0)`, and the callee-saved registers restored
(`wfinish_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC X2)
open VG.Impl.X448.AArch64.Fast (saved)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved restore_ok workRegs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV restoreX_ok)
open VG.Proof.Ed448.AArch64 (CFrame CKeep eqSlotsF_ok isZero_ok or_eq_zero64)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-! ## What the comparisons write -/

/-- Memory beyond `X2`, `CAN`, the coefficients and slots 12–13 is unchanged. -/
def LFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < X2 ∨ X2 + 128 ≤ ofs base x) → (ofs base x < CAN ∨ CAN + 128 ≤ ofs base x) →
    (ofs base x < ACC ∨ ACC + 512 ≤ ofs base x) → (ofs base x < slot 12 ∨ slot 14 ≤ ofs base x) → m' x = m x

theorem LFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : LFrame base m₁ m₂) (h₂ : LFrame base m₂ m₃) :
    LFrame base m₁ m₃ := fun x a b c d => (h₂ x a b c d).trans (h₁ x a b c d)

theorem LFrame.of_c {base : Addr} {m m' : Mem} (h : CFrame base m m') : LFrame base m m' :=
  fun x a b c _ => h x a b c

theorem LFrame.of_out {base : Addr} {m m' : Mem} {o : Nat} (ho : slot 12 ≤ o ∧ o + 128 ≤ slot 14)
    (h : Outside base o 128 m m') : LFrame base m m' :=
  fun x _ _ _ d => h x (by omega_arith)

theorem LFrame.word {base : Addr} {m m' : Mem} (h : LFrame base m m') {d : Nat}
    (h1 : d + 8 ≤ X2 ∨ X2 + 128 ≤ d) (h2 : d + 8 ≤ CAN ∨ CAN + 128 ≤ d) (h3 : d + 8 ≤ ACC ∨ ACC + 512 ≤ d)
    (h4 : d + 8 ≤ slot 12 ∨ slot 14 ≤ d) (hd : d + 8 ≤ 8192) : word m' base d = word m base d :=
  Mem.readW_congr fun i hi => h _ (by
      simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega_arith)]; omega_arith)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega_arith)]; omega_arith)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega_arith)]; omega_arith)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega_arith)]; omega_arith)

theorem LFrame.saved {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : LFrame base m m') (hs : Saved base g m) :
    Saved base g m' :=
  ⟨(h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.1,
    (h.word (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)).trans hs.2⟩

theorem LFrame.lrs {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : LFrame base m m')
    (hs : VG.Proof.Ed448.AArch64.LrSaved base g m) : VG.Proof.Ed448.AArch64.LrSaved base g m' :=
  (h.word (Or.inr (by simp only [X2, slot, LRS]; omega_arith)) (Or.inl (by simp only [CAN, LRS]; omega_arith))
    (Or.inl (by simp only [ACC, LRS]; omega_arith)) (Or.inr (by simp only [slot, LRS]; omega_arith))
    (by simp only [LRS]; omega_arith)).trans hs

theorem LFrame.savedX {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : LFrame base m m') (hs : SavedX base g m) :
    SavedX base g m' := fun k hk =>
  (h.word (Or.inr (by simp only [X2, slot, Impl.X448.AArch64.Fast.SAVE]; omega_arith))
    (Or.inl (by simp only [CAN, Impl.X448.AArch64.Fast.SAVE]; omega_arith))
    (Or.inl (by simp only [ACC, Impl.X448.AArch64.Fast.SAVE]; omega_arith))
    (Or.inr (by simp only [slot, Impl.X448.AArch64.Fast.SAVE]; omega_arith))
    (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega_arith)).trans (hs k hk)

theorem LFrame.savedV {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : LFrame base m m') (hs : SavedV base v m) :
    SavedV base v m' := by
  have hV : Impl.X448.AArch64.Fast.VSAVE = 4736 := rfl
  refine hs.frame fun d h1 h2 => ?_
  have ho : ofs base (off base d) = d := ofs_off0' base (by omega_arith)
  exact h _ (by rw [ho]; simp only [X2, slot]; omega_arith) (by rw [ho]; simp only [CAN]; omega_arith)
    (by rw [ho]; simp only [ACC]; omega_arith) (by rw [ho]; simp only [slot]; omega_arith)

/-- A slot but 1, 12 and 13 is unchanged. -/
theorem LFrame.limbs {base : Addr} {m m' : Mem} (h : LFrame base m m') {i : Index} (hi : i.val ≠ 1)
    (h12 : i.val ≠ 12) (h13 : i.val ≠ 13) {j : Nat} (hj : j < 8) :
    limbs m' base (slot i.val) j = limbs m base (slot i.val) j := by
  have := i.isLt
  exact congrArg BitVec.toNat (h.word (by simp only [X2, slot]; omega_arith) (by simp only [CAN, slot]; omega_arith)
    (by simp only [ACC, slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith))

/-! ## The comparisons -/

/-- The registers the comparisons change. -/
abbrev cmpRegs : List Reg := .x19 :: .x20 :: workRegs

theorem decX19_ok (s : State) {n : Nat} (hn : n < 2) (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  have e : BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
    rcases (by omega_arith : n = 0 ∨ n = 1) with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    e, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- **One pass**: slots 12 and 13 compared into `x20`, then 14 and 15 copied into them. -/
theorem wcmp_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (hn : n < 2)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1))
    (hb : ∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs s.mem base (slot i.val) j < 2 ^ 118) :
    WP isa wcmp s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ EV s.mem base 12 = EV s.mem base 13) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      t.gpr .x19 = BitVec.ofNat 64 n ∧ Keeps cmpRegs s t ∧ LFrame base s.mem t.mem ∧
      EV t.mem base 12 = EV s.mem base 14 ∧ EV t.mem base 13 = EV s.mem base 15 ∧
      (∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs t.mem base (slot i.val) j < 2 ^ 118) := by
  unfold wcmp
  refine WP.seq (WP.mono (eqSlotsF_ok hs 12 13 (hb 12 (by decide) (by decide)) (hb 13 (by decide) (by decide))
    (by decide) (by decide)) fun s1 ⟨cmp, k1, _⟩ => ?_)
  have hs1 := k1.scr hs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs1 (o := slot 12) (a := slot 14) (by decide) (by decide)
    (by decide) (by decide) (Or.inr (Or.inl (by decide)))) fun s2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs2 (o := slot 13) (a := slot 15) (by decide) (by decide)
    (by decide) (by decide) (Or.inr (Or.inl (by decide)))) fun s3 ⟨v3, o3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have c3 : s3.gpr .x19 = BitVec.ofNat 64 (n + 1) := by
    rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.regs.1 _ (by decide), hc]
  refine WP.mono (decX19_ok s3 hn c3) fun t ⟨ct, kt, mt⟩ => ?_
  have f : LFrame base s.mem t.mem := by
    rw [mt]
    exact ((LFrame.of_c k1.mem).trans (LFrame.of_out (by decide) o2)).trans (LFrame.of_out (by decide) o3)
  -- Slots 14 and 15, kept by the comparison and the copies.
  have l1 : ∀ i : Index, i.val ≠ 1 → i.val ≠ 12 → i.val ≠ 13 → ∀ j < 8,
      limbs s1.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i h1 _ _ j hj =>
    k1.mem.limbs (fun e => h1 (congrArg Fin.val e)) (by omega_arith)
  have l12 : ∀ j < 8, limbs t.mem base (slot 12) j = limbs s.mem base (slot 14) j := fun j hj => by
    rw [mt, o3.limbs (by decide) (by decide) (by omega_arith), v2 j hj]; exact l1 14 (by decide) (by decide) (by decide) j hj
  have l13 : ∀ j < 8, limbs t.mem base (slot 13) j = limbs s.mem base (slot 15) j := fun j hj => by
    rw [mt, v3 j hj, o2.limbs (by decide) (by decide) (by omega_arith)]
    exact l1 15 (by decide) (by decide) (by decide) j hj
  refine ⟨?_, ct, ?_, f, congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr l12),
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr l13), fun i h1 h2 j hj => ?_⟩
  · obtain ⟨c, hc, x⟩ := cmp
    exact ⟨c, hc, by rw [kt.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), x]⟩
  · exact ((k1.regs.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans
      ((k2.mono (by decide)).trans (k3.mono (by decide)))).trans (kt.mono (by decide))
  · rcases (by omega_arith : i.val = 12 ∨ i.val = 13 ∨ (i.val ≠ 12 ∧ i.val ≠ 13)) with e | e | ⟨e1, e2⟩
    · rw [e, l12 j hj]; exact hb 14 (by decide) (by decide) j hj
    · rw [e, l13 j hj]; exact hb 15 (by decide) (by decide) j hj
    · rw [f.limbs (by omega_arith) e1 e2 hj]; exact hb i h1 h2 j hj

theorem setX19_ok (s : State) :
    WP isa (.block [.movz .x .x19 2 0]) s fun t => t.gpr .x19 = BitVec.ofNat 64 2 ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- **The comparisons**: two passes of `wcmp`. -/
theorem wloop_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs s.mem base (slot i.val) j < 2 ^ 118) :
    WP isa (.seq (.block [.movz .x .x19 2 0]) (.loop wcmp (.nonzero .x .x19))) s fun t =>
      Scr t base ∧ Keeps cmpRegs s t ∧ LFrame base s.mem t.mem ∧
      (t.gpr .x20 = 0 ↔ s.gpr .x20 = 0 ∧ EV s.mem base 12 = EV s.mem base 13 ∧ EV s.mem base 14 = EV s.mem base 15) := by
  refine WP.seq (WP.mono (setX19_ok s) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
  refine WP.loop (M := isa) (fun n (t : State) => (n = 1 ∨ n = 2) ∧ t.gpr .x19 = BitVec.ofNat 64 n ∧
      Scr t base ∧ Keeps cmpRegs s t ∧ LFrame base s.mem t.mem ∧
      (∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs t.mem base (slot i.val) j < 2 ^ 118) ∧
      (n = 2 → EV t.mem base 12 = EV s.mem base 12 ∧ EV t.mem base 13 = EV s.mem base 13 ∧
        EV t.mem base 14 = EV s.mem base 14 ∧ EV t.mem base 15 = EV s.mem base 15 ∧ t.gpr .x20 = s.gpr .x20) ∧
      (n = 1 → EV t.mem base 12 = EV s.mem base 14 ∧ EV t.mem base 13 = EV s.mem base 15 ∧
        (t.gpr .x20 = 0 ↔ s.gpr .x20 = 0 ∧ EV s.mem base 12 = EV s.mem base 13))) ?_ 2 s₁
    ⟨.inr rfl, c₁, hs.of_keeps k₁ (by decide), k₁.mono (by decide), by rw [m₁]; exact fun _ _ _ _ _ => rfl,
      by rw [m₁]; exact hb, fun _ => by rw [m₁, k₁.1 _ (by decide)]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩,
      fun h => absurd h (by decide)⟩
  intro n t ⟨hn, ct, ht, kt, ft, bt, e2, e1⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_arith⟩
  refine WP.mono (wcmp_ok ht (n := k) (by omega_arith) ct bt) fun u ⟨⟨c, hc, xu⟩, cu, ku, fu, u12, u13, bu⟩ => ?_
  have hu := ht.of_keeps ku (by decide)
  have kU : Keeps cmpRegs s u := kt.trans ku
  have fU : LFrame base s.mem u.mem := ft.trans fu
  simp only [eval, State.read, BitVec.setWidth_eq, cu]
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · -- The second pass: done.
    obtain ⟨t12, t13, ht0⟩ := e1 rfl
    refine .inl ⟨by decide, hu, kU, fU, ?_⟩
    rw [xu, or_eq_zero64, ht0, hc, t12, t13, and_assoc]
  · -- The first pass: on to the second.
    obtain ⟨t12, t13, t14, t15, t20⟩ := e2 rfl
    refine .inr ⟨by decide, 1, by omega_arith, .inl rfl, rfl, hu, kU, fU, bu, fun h => absurd h (by decide),
      fun _ => ⟨by rw [u12, t14], by rw [u13, t15], ?_⟩⟩
    rw [xu, or_eq_zero64, t20, hc, t12, t13]

theorem wresult_eq : wresult = ([.addImm .x .x5 .x20 0] : List Instr) ++ (isZero ++
    (([.addImm .x .x0 .x5 0] : List Instr) ++ (([ld .x19 0, ld .x20 8] : List Instr) ++ (([ld .x30 LRS] : List Instr) ++
      (Impl.X448.AArch64.Fast.restore ++ Impl.X448.AArch64.Fast.vrestore))))) := by
  simp only [wresult, List.append_assoc]; rfl

/-- **The result** of the comparisons, and the registers restored. -/
theorem wfinish_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : ∀ i : Index, 12 ≤ i.val → i.val < 16 → ∀ j < 8, limbs s.mem base (slot i.val) j < 2 ^ 118)
    {g : Reg → BitVec 64} (sv : Saved base g s.mem) (svx : SavedX base g s.mem)
    (lrs : VG.Proof.Ed448.AArch64.LrSaved base g s.mem)
    {gv : VReg → BitVec 128} (svv : SavedV base gv s.mem) :
    WP isa wfinish s fun t =>
      t.gpr .x0 = (if s.gpr .x20 = 0 ∧ EV s.mem base 12 = EV s.mem base 13 ∧ EV s.mem base 14 = EV s.mem base 15
        then 1 else 0) ∧
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      t.gpr .x30 = g .x30 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold wfinish
  refine WP.seq (WP.mono (wloop_ok hs hb) fun s2 ⟨hs2, k2, f02, h20⟩ => ?_)
  rw [wresult_eq, WP.block_append_iff]
  refine WP.mono (mov_ok .x5 .x20 s2) fun s3 ⟨v3, m3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s3) fun s4 ⟨v4, m4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mov_ok .x0 .x5 s4) fun s5 ⟨v5, m5, k5⟩ => ?_
  have k25 : Keeps (.x0 :: .x5 :: .x6 :: .x7 :: []) s2 s5 :=
    ((k3.mono (by decide)).trans (k4.mono (by decide))).trans (k5.mono (by decide))
  have hs5 : Scr s5 base := hs2.of_keeps k25 (by decide)
  have m25 : s5.mem = s2.mem := by rw [m5, m4, m3]
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hs5 (g := g) (by rw [m25]; exact LFrame.saved f02 sv)) fun s6 ⟨t19, t20, m6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.ld_ok hs6 .x30 (d := LRS) (by decide) (by decide))
    fun s6' ⟨t30, m6', k6'⟩ => ?_
  have hs6' : Scr s6' base := hs6.of_keeps k6' (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restoreX_ok hs6' (g := g) (by rw [m6', m6, m25]; exact LFrame.savedX f02 svx))
    fun s7 ⟨tx, m7, k7⟩ => ?_
  have hs7 : Scr s7 base := hs6'.of_keeps k7 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.vrestore_ok hs7 (by rw [m7, m6', m6, m25]; exact LFrame.savedV f02 svv))
    fun t ⟨tv, mt, gt, rdt, wrt⟩ => ⟨?_, ?_, ?_, fun k hk => by rw [gt]; exact tx k hk, tv, ?_, ?_, ?_⟩
  · rw [gt, k7.1 _ (by decide), k6'.1 _ (by decide), k6.1 _ (by decide), v5, v4, v3]
    exact if_congr h20 rfl rfl
  · rw [gt, k7.1 _ (by decide), k6'.1 _ (by decide)]; exact t19
  · rw [gt, k7.1 _ (by decide), k6'.1 _ (by decide)]; exact t20
  · rw [gt, k7.1 _ (by decide), t30, m6, m25]; exact LFrame.lrs f02 lrs
  · rw [rdt, k7.2.1, k6'.2.1, k6.2.1, k25.2.1, k2.2.1]
  · rw [wrt, k7.2.2, k6'.2.2, k6.2.2, k25.2.2, k2.2.2]

end VG.Proof.Ed448.AArch64.Window
