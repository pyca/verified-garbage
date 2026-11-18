module

public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
meta import VerifiedGarbage.Proof.Ed25519.Group.Extended
meta import VerifiedGarbage.Proof.Ed25519.Recover
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
meta import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
meta import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
public import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
meta import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring
public import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
public import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
public import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.WindowConstants
public import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.Ring.RingNF
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverSign
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
meta import VerifiedGarbage.Proof.Ed25519.Decode
meta import VerifiedGarbage.Proof.Ed25519.Canonical64
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
meta import Mathlib.Tactic.NormNum.Prime
meta import Mathlib.Data.Nat.Totient
meta import Mathlib.Tactic.Positivity.Finset
meta import Mathlib.Algebra.Order.Field.Basic
meta import Mathlib.Tactic.NormNum.GCD
meta import Mathlib.Data.Sym.Sym2.Init
meta import Mathlib.Tactic.ContinuousFunctionalCalculus
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Power
meta import VerifiedGarbage.Proof.Ed25519.WindowConstants
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Points
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import Mathlib.Tactic.Ring.RingNF
meta import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
meta import VerifiedGarbage.Proof.Framework.ConstMem

/-! ### `Ed25519.AArch64.VerifyContext`, which this module and modules that import it used -/

section

/-! ### `Ed25519.AArch64.VerifyPoints`, which this module and modules that import it used -/

section

/-! ### `Ed25519.AArch64.VerifyTbl`, which this module and modules that import it used -/

section

/-!
# Ed25519 verification on AArch64: the cached `-[1]B … -[15]B` in a static

Untrusted: everything here is checked by Lean. The words of the static `bSym`
(`bWords`), as a contract states them (`BHeld`) and as the copy into the
working space reads them (`BTblAt`), and a memory holding them for contracts'
witnesses (`bSatMem`). Nothing here evaluates the table: each lemma holds for
its words by their definition (`bWord`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {i : Nat} (hi : i < 240) : bWords.getD i 0 = bWord i := by
  simp [bWords, List.getD_eq_getElem?_getD, hi]

theorem bConsts_eq : bConsts = [(bSym, bWords)] := rfl

/-- Word `w` of coordinate `c` of entry `j`. -/
theorem bWord_eq (j c w : Nat) (hc : c < 4) (hw : w < 4) :
    bWord (16 * j + 4 * c + w) = BitVec.ofNat 64
      ((pointCoord (Impl.Ed25519.negBaseCached j) c).val / 2 ^ (64 * w)) := by
  unfold bWord
  rw [show (16 * j + 4 * c + w) / 16 = j by omega_using [hc, hw], show (16 * j + 4 * c + w) / 4 % 4 = c by omega_using [hc, hw],
    show (16 * j + 4 * c + w) % 4 = w by omega_using [hw]]

/-- The static, in `s`, as a contract states it: its words, not wrapping around, apart from the
regions `wr`. -/
def BHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0) ∧
  (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r

/-- The static's words at `T` in `m`. -/
def BWords (T : Addr) (m : Mem) : Prop :=
  ∀ i < 240, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0

/-- The static at `T`: readable, beyond the working space at `base`, word `i` its `bWord i`. -/
structure BTblAt (s : State) (base T : Addr) : Prop where
  rd : ∀ i < 240, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (8 * i)) 8
  far : ∀ i < 1920, 8192 ≤ ofs base (T + BitVec.ofNat 64 i)
  val : ∀ i < 240, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = bWord i

/-- The static survives what keeps the regions and the memory beyond the working space. -/
theorem BTblAt.of_far {s t : State} {base T : Addr} (h : BTblAt s base T)
    (hrw : t.rd ++ t.wr = s.rd ++ s.wr) (hm : ∀ x, 8192 ≤ ofs base x → t.mem x = s.mem x) :
    BTblAt t base T :=
  ⟨fun i hi => hrw ▸ h.rd i hi, h.far, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega_using [hi, hb])⟩

/-- The static, from a contract's facts: readable, and apart from the working space at `base`,
one of the regions `wr`. -/
theorem BHeld.tblAt {s : State} {wr : List Region} {base : Addr} (h : BHeld s wr)
    (hrd : (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : (⟨base, 8192⟩ : Region) ∈ wr) : BTblAt s base (s.syms bSym) := by
  obtain ⟨held, fit, dj⟩ := h
  refine ⟨fun i hi => ⟨_, hrd, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩, fun i hi => ?_,
    fun i hi => by rw [held i hi, bWords_getD hi]⟩
  refine Nat.le_of_not_lt fun hlt => dj _ hsc _
    (Offset.contains_base _ (d := i) (n := 1) (k := 1920) (by omega_using [hi]) (by omega_using [hi])) ?_
  simp only [Region.Contains]; simp only [ofs] at hlt; omega_using [hlt]

/-- The memory of the contracts' witnesses: the static at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the table). -/
@[irreducible] def bSatMem : Mem := constMem 0x100000 bWords

theorem bSatMem_held : ∀ i < 240,
    bSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  unfold bSatMem
  intro i hi
  exact constMem_held _ _ (by rw [bWords_length]; omega_using []) i (by rw [bWords_length]; exact hi)

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.PointAccumulate`, which only this module used -/

section

/-! The scalar bit mask and the selection of the saved point. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega_using []) (Or.inr (by simp only [offset]; omega_using [hi]))

end VG.Proof.Ed25519.AArch64

end

end


/-! Merged from `Proof.Ed25519.AArch64.WindowTables`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.AArch64.VerifyTables`. -/
section
/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => t.gpr .x19 = 0 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableRead_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [pointTableRead, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  obtain kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  obtain kbr : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok ((kar.trans kbr).scr hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  refine ⟨(kar.trans kbr).trans (CounterKeep.of_keep (Keep.of_table kt)), ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · intro i hi
    rw [tableLoad_high kt i hi, kb.mem, ka.mem]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.BaseBatchTable`. -/
section
/-!
# Writing a batch's cached powers into the local table

Each constant field is four immediate words stored at a constant offset of
`x0`; the batch is chosen by subtracting each index from the public counter
`x19` and testing the difference for zero.
-/

end

/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

The table of multiples of `A` is built by repeated addition of `A`, which
stays in slots 4–7, each entry representing its multiple (`Rep`); the table of
negated multiples of `B` is stored from constants.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open VG.Impl.Ed25519 (negBaseCached)
open Fin.CommRing

/-! ## `[i]A` -/

private theorem aNext_cmp : ∀ n < 15,
    (BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 15 != 0) = decide (n + 1 ≠ 15) := by decide

theorem aNext_ok (s : State) (n : Nat) (hn : n < 15) (hc : s.gpr .x19 = BitVec.ofNat 64 n) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (n + 1) ∧ eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      Keeps [.x19, .x8] s t := by
  obtain ha : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) := by
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (1 : Nat) < 4096 from by decide, show (15 : Nat) < 4096 from by decide, ite_true,
    RegUpd.gpr_write, hc, ha, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, ite_false, reduceCtorEq,
      aNext_cmp n hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 = cache (point e 0 1 2 3) := by
  have h : point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 =
      ⟨e 1 - e 0, e 1 + e 0, (e 3 + e 3) * e 16, e 2 + e 2⟩ := rfl
  rw [h, hd]
  simp only [cache, point]
  congr 1 <;> ring

theorem saveCache_eval (e : Env) :
    point (evalOps (savePointOps ++ cacheOps) e) 4 5 6 7 = point e 4 5 6 7 ∧
    point (evalOps (savePointOps ++ cacheOps) e) 17 18 19 20 = point e 0 1 2 3 ∧
    evalOps (savePointOps ++ cacheOps) e 16 = e 16 := ⟨rfl, rfl, rfl⟩

theorem restore_eval (e : Env) :
    point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 ∧
    evalOps restorePointOps e 16 = e 16 := ⟨rfl, rfl⟩

theorem pointAddCached_q (e : Env) :
    point (evalOps pointAddCachedOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem PowersKeep.of_tableKeep {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t) :
    PowersKeep base o n s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp, TableFrame.table h.mem⟩

theorem storeCached_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 15)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block storeCached) s fun t =>
      tablePoint t.mem base (5376 + 128 * j) = cache (point (env s.mem base) 0 1 2 3) ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 ∧
      env t.mem base 16 = env s.mem base 16 ∧ t.gpr .x19 = s.gpr .x19 ∧
      PowersKeep base (5376 + 128 * j) 128 s t := by
  rw [storeCached, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (savePointOps ++ cacheOps) hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.scr hs).x0 5376 j (by omega_arith) ((ka.gpr _ (by decide)).trans hc))
    fun b ⟨bp, kb⟩ => ?_
  obtain kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok ((ka.trans kbe).scr hs) bp (by omega_arith) (by omega_arith)) fun c ⟨cp, kc⟩ => ?_
  obtain ce : env c.mem base = env a.mem base := by rw [table_env kc.mem (by omega_arith), kb.mem]
  refine WP.mono (fieldCode_ok restorePointOps (kc.scratch ((ka.trans kbe).scr hs)))
    fun t ⟨kt, vt⟩ => ?_
  obtain ⟨s4, s17, s16⟩ := saveCache_eval (env s.mem base)
  obtain ⟨r4, r16⟩ := restore_eval (env c.mem base)
  refine ⟨?_, ?_, ?_, ?_, by rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kbe.gpr _ (by decide),
    ka.gpr _ (by decide)], ((PowersKeep.of_keep (ka.trans kbe)).trans
    (PowersKeep.of_tableKeep kc)).trans (PowersKeep.of_keep kt)⟩
  · rw [workspace_tablePoint kt.mem (by omega_arith) (by omega_arith), cp, kb.mem, va, cacheOps_eval _ hd]
  · rw [vt, restorePoint_eval, ce, va, s17]
  · rw [vt, r4, ce, va, s4]
  · rw [vt, r16, ce, va, s16]

/-- The table of `A`'s multiples, cached, with `n` entries, `[n]A` in slots 0–3 and `A`
cached in slots 4–7. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) (n • A)
  q : ∃ qa, point (env s.mem base) 4 5 6 7 = cache qa ∧ Rep qa A
  table : ∀ j < n, ∃ q, tablePoint s.mem base (5376 + 128 * j) = cache q ∧ Rep q ((j + 1) • A)
  keep : PowersKeep base 5376 1920 s₀ s

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 15)
    (h : ATableInv s₀ base A n s) :
    WP isa (.block aTableBody) s fun t => eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      ATableInv s₀ base A (n + 1) t := by
  obtain ⟨qa, hq, hA⟩ := h.q
  rw [aTableBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointAddCachedOps h.scratch) fun c ⟨kc, vc⟩ => ?_
  obtain crep : Rep (point (env c.mem base) 0 1 2 3) ((n + 1) • A) := by
    rw [vc, pointAddCached_eval _ qa hq, succ_nsmul]
    exact pointAdd_rep h.value hA
  obtain cq : point (env c.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 := by
    rw [vc, pointAddCached_q]
  obtain cd : env c.mem base 16 = Spec.Ed25519.d := by
    rw [vc, pointAddCached_high _ 16 (by decide)]; exact h.d
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kc.scr h.scratch) n hn ((kc.gpr _ (by decide)).trans h.counter) cd)
    fun d ⟨dt, d0, d4, d16, d19, kd⟩ => ?_
  refine WP.mono (aNext_ok d n hn (d19.trans
    ((kc.gpr _ (by decide)).trans h.counter))) fun t ⟨tc, tz, kt⟩ => ?_
  obtain kall : PowersKeep base 5376 1920 s t :=
    ((PowersKeep.of_keep kc).trans (kd.mono (by omega_arith) (by omega_arith))).trans
      (PowersKeep.of_keeps kt (by decide))
  refine ⟨tz, by omega_arith, by omega_arith, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [kt.mem, d16]; exact cd
  · rw [kt.mem, d0]; exact crep
  · exact ⟨qa, by rw [kt.mem, d4, cq]; exact hq, hA⟩
  · intro j hj
    rw [kt.mem]
    by_cases hjn : j < n
    · rw [kd.mem.point (by omega_arith) (Or.inl (by omega_arith)) (by omega_arith),
        workspace_tablePoint kc.mem (by omega_arith) (by omega_arith)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega_arith
      exact ⟨_, dt, crep⟩

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (.block aTableInit) s (ATableInv s base A 1) := by
  rw [aTableInit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hs 7424 (by decide) (by decide)) fun a ⟨ka, ap, ah⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok a) fun b ⟨bz, kb⟩ => ?_
  obtain kab := (PowersKeep.of_counter ka : PowersKeep base 5376 1920 s a).trans
    (PowersKeep.of_keeps kb (by decide))
  obtain bd : env b.mem base 16 = Spec.Ed25519.d := by rw [kb.mem, ah 16 (by decide)]; exact hd
  obtain bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [kb.mem, ap]; exact hA
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kab.scratch hs) 0 (by decide) bz bd) fun c ⟨ct, c0, _, c16, c19, kc⟩ => ?_
  obtain kac := kab.trans (kc.mono (by omega_arith) (by omega_arith))
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kac.scratch hs).x0 5376 0 (by decide)
    (c19.trans bz)) fun d ⟨dp, kd⟩ => ?_
  obtain kde : Keep base c d := Keep.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kde.scr (kac.scratch hs)) dp (by decide) (by decide))
    fun e ⟨ep, ke⟩ => ?_
  obtain kee := Keep.of_tableQ ke
  obtain o := tableQ_other ke
  refine WP.mono (movzW_ok e .x19 1) fun t ⟨tc, kt⟩ => ?_
  obtain kall : PowersKeep base 5376 1920 s t :=
    ((kac.trans (PowersKeep.of_keep (kde.trans kee))).trans (PowersKeep.of_keeps kt (by decide)))
  obtain e0 : point (env e.mem base) 0 1 2 3 = point (env c.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kd.mem]
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, kall⟩
  · rw [kt.mem, o 16 (by decide), kd.mem, c16]; exact bd
  · rw [kt.mem, e0, c0, one_nsmul]; exact bA
  · refine ⟨point (env b.mem base) 0 1 2 3, ?_, bA⟩
    rw [kt.mem, ep, kd.mem]
    simpa using ct
  · intro j hj
    obtain rfl : j = 0 := by omega_arith
    refine ⟨point (env b.mem base) 0 1 2 3, ?_, by rw [zero_add, one_nsmul]; exact bA⟩
    rw [kt.mem, workspace_tablePoint kee.mem (by decide) (by decide), workspace_tablePoint kde.mem
      (by decide) (by decide)]
    simpa using ct

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa aTable s (ATableInv s base A 15) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (15 - n) t ∧ 0 < n) (n := 14)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 15 - n) (by omega_arith) h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨uz.trans (by rw [he]; rfl), by rw [← he]; exact hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true he]), n - 1, by omega_arith,
        by rw [show 15 - (n - 1) = 15 - n + 1 by omega_arith]; exact hu, by have := hu.bound; omega_arith⟩
  · exact ⟨ha, by decide⟩

/-! ## Cached `-[i]B`, copied from the static -/

/-- Word `w` of coordinate `c` of the static's entry `j`, at `x9 + d`, into `r`. -/
theorem bLoad_ok {s : State} {base T : Addr} (ht : BTblAt s base T) {j c w d : Nat} (hj : j < 15)
    (hc : c < 4) (hw : w < 4) (hd : d = 32 * c + 8 * w)
    (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * j)) (r : Reg) :
    WP isa (.block [.ldr .x r .x9 d]) s fun t =>
      t.gpr r = bWord (16 * j + 4 * c + w) ∧ Keeps [r] s t := by
  obtain hi : 16 * j + 4 * c + w < 240 := by omega_arith
  obtain ha : s.gpr .x9 + BitVec.ofNat 64 d = T + BitVec.ofNat 64 (8 * (16 * j + 4 * c + w)) := by
    rw [h9, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact congrArg (fun n => T + BitVec.ofNat 64 n) (by omega_arith)
  apply WP.of_runBlock
  rw [runBlock_cons, exec_ldr_x ⟨by omega_arith, by omega_arith⟩ (by rw [ha]; exact ht.rd _ hi), runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, ⟨fun r' hr' => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr'), rfl, rfl,
    rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, ha, ht.val _ hi]

theorem BTblAt.of_keeps {s t : State} {base T : Addr} {rs : List Reg} (h : BTblAt s base T)
    (k : Keeps rs s t) : BTblAt t base T :=
  h.of_far (by rw [k.rd, k.wr]) fun x _ => by rw [k.mem]

theorem BTblAt.of_powers {s t : State} {base T : Addr} {o n : Nat} (h : BTblAt s base T)
    (k : PowersKeep base o n s t) (hn : o + n ≤ 8192) : BTblAt t base T :=
  h.of_far (by rw [k.rd, k.wr]) fun x hx => k.mem x (Or.inr (by omega_arith)) (Or.inr (by omega_arith))

/-- Coordinate `c` of the static's entry `j`, at `x9`, into `x4`–`x7`. -/
theorem bLoads_ok {s : State} {base T : Addr} (ht : BTblAt s base T) {j c : Nat} (hj : j < 15)
    (hc : c < 4) (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * j)) :
    WP isa (.block [.ldr .x .x4 .x9 (32 * c), .ldr .x .x5 .x9 (32 * c + 8),
      .ldr .x .x6 .x9 (32 * c + 16), .ldr .x .x7 .x9 (32 * c + 24)]) s fun t =>
      Word64.val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (pointCoord (Impl.Ed25519.negBaseCached j) c).val ∧ Keeps [.x4, .x5, .x6, .x7] s t := by
  change WP isa (.block (([.ldr .x .x4 .x9 (32 * c)] : List Instr) ++
    (([.ldr .x .x5 .x9 (32 * c + 8)] : List Instr) ++ (([.ldr .x .x6 .x9 (32 * c + 16)] : List Instr) ++
      ([.ldr .x .x7 .x9 (32 * c + 24)] : List Instr))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (bLoad_ok ht hj hc (w := 0) (by omega_arith) (by omega_arith) h9 .x4) fun a ⟨a4, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bLoad_ok (ht.of_keeps ka) hj hc (w := 1) (by omega_arith) (by omega_arith)
    ((ka.gpr _ (by decide)).trans h9) .x5) fun b ⟨b5, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bLoad_ok ((ht.of_keeps ka).of_keeps kb) hj hc (w := 2) (by omega_arith) (by omega_arith)
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans h9)) .x6) fun d ⟨d6, kd⟩ => ?_
  refine WP.mono (bLoad_ok (((ht.of_keeps ka).of_keeps kb).of_keeps kd) hj hc (w := 3) (by omega_arith)
    (by omega_arith) ((kd.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans
      ((ka.gpr _ (by decide)).trans h9))) .x7) fun t ⟨t7, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((kd.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [kt.gpr .x4 (by decide), kd.gpr .x4 (by decide), kb.gpr .x4 (by decide), a4,
    kt.gpr .x5 (by decide), kd.gpr .x5 (by decide), b5, kt.gpr .x6 (by decide), d6, t7,
    bWord_eq j c 0 hc (by decide), bWord_eq j c 1 hc (by decide), bWord_eq j c 2 hc (by decide),
    bWord_eq j c 3 hc (by decide)]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.reduceMul]
  refine limbs_nat _ ?_
  have := (pointCoord (Impl.Ed25519.negBaseCached j) c).isLt
  simp only [Spec.X25519.P] at this; omega_arith

/-- Coordinate `c` of the static's entry `j` to the table entry at `x8`. -/
theorem bCopyCoord_ok {s : State} {base T : Addr} (hs : Scr s base) (ht : BTblAt s base T)
    {j c : Nat} (hj : j < 15) (hc : c < 4) (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * j))
    (h8 : s.gpr .x8 = off base (2048 + 128 * j)) :
    WP isa (.block (bCopyCoord c)) s fun t =>
      F t.mem base (2048 + 128 * j + 32 * c) = pointCoord (Impl.Ed25519.negBaseCached j) c ∧
        TableKeep base (2048 + 128 * j + 32 * c) 32 s t := by
  rw [bCopyCoord, WP.block_append_iff]
  refine WP.mono (bLoads_ok ht hj hc h9) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide)) ((hk.gpr _ (by decide)).trans h8)
    (32 * c) (by omega_arith) (by omega_arith)) fun u ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.gpr r hr), hrd.trans hk.rd, hwr.trans hk.wr,
    hsp.trans hk.sp, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega_arith), hv, Proof.X25519.toFe_self]
  · rw [hm, hk.mem]; exact st4_outside _ _ (by omega_arith) _ _ _ _

theorem bCopyPrefix_ok {s : State} {base T : Addr} (hs : Scr s base) (ht : BTblAt s base T)
    {j : Nat} (hj : j < 15) (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * j))
    (h8 : s.gpr .x8 = off base (2048 + 128 * j)) (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap bCopyCoord)) s fun t =>
      (∀ c < n, F t.mem base (2048 + 128 * j + 32 * c) = pointCoord (Impl.Ed25519.negBaseCached j) c) ∧
        TableKeep base (2048 + 128 * j) (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun c hc => by omega_arith, ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs ht h9 h8 (by omega_arith)) fun t ⟨hv, hk⟩ => ?_
    obtain htt : BTblAt t base T :=
      ht.of_far (by rw [hk.rd, hk.wr]) fun x hx => hk.mem x (Or.inr (by omega_arith))
    refine WP.mono (bCopyCoord_ok (hk.scratch hs) htt hj (c := n) (by omega_arith)
      ((hk.gpr _ (by decide)).trans h9) ((hk.gpr _ (by decide)).trans h8)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun c hc => ?_, (hk.mono (by omega_arith) (by omega_arith)).trans (ku.mono (by omega_arith) (by omega_arith))⟩
    by_cases h : c < n
    · rw [Outside_F ku.mem (by omega_arith) (Or.inl (by omega_arith)), hv c h]
    · obtain rfl : c = n := by omega_arith
      exact hu

/-- The static's entry `j` to the table's entry `j`. -/
theorem bCopyEntry_ok {s : State} {base T : Addr} (hs : Scr s base) (ht : BTblAt s base T)
    {j : Nat} (hj : j < 15) (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * j))
    (h8 : s.gpr .x8 = off base (2048 + 128 * j)) :
    WP isa (.block ((List.range 4).flatMap bCopyCoord)) s fun t =>
      tablePoint t.mem base (2048 + 128 * j) = Impl.Ed25519.negBaseCached j ∧
        TableKeep base (2048 + 128 * j) 128 s t := by
  refine WP.mono (bCopyPrefix_ok hs ht hj h9 h8 4 (by decide)) fun t ⟨hv, hk⟩ => ⟨?_, hk⟩
  obtain h0 := hv 0 (by decide)
  obtain h1 := hv 1 (by decide)
  obtain h2 := hv 2 (by decide)
  obtain h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.add_assoc] at h0 h1 h2 h3
  simp only [tablePoint, Nat.add_assoc, h0, h1, h2, h3]
  rfl

/-- The table's first `n` entries copied, `x19 = n`, and `x9` at the static's entry `n`. -/
structure BInv (s₀ : State) (base T : Addr) (n : Nat) (s : State) : Prop where
  bound : n ≤ 15
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  src : s.gpr .x9 = T + BitVec.ofNat 64 (128 * n)
  tbl : BTblAt s base T
  table : ∀ i < n, tablePoint s.mem base (2048 + 128 * i) = Impl.Ed25519.negBaseCached i
  keep : PowersKeep base 2048 1920 s₀ s
  out : Outside base 2048 1920 s₀.mem s.mem

theorem bNext_ok (s : State) {T : Addr} (n : Nat) (h9 : s.gpr .x9 = T + BitVec.ofNat 64 (128 * n)) :
    WP isa (.block [.addImm .x .x9 .x9 128]) s fun t =>
      t.gpr .x9 = T + BitVec.ofNat 64 (128 * (n + 1)) ∧ Keeps [.x9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (128 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, h9, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    Nat.mul_succ]

theorem bTableBody_ok {s₀ s : State} {base T : Addr} {n : Nat} (hn : n < 15) (h : BInv s₀ base T n s) :
    WP isa (.block bTableBody) s fun t => eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      BInv s₀ base T (n + 1) t := by
  rw [bTableBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok h.scratch.x0 2048 n (by omega_arith) h.counter) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bCopyEntry_ok (h.scratch.of_keeps ka (by decide)) (h.tbl.of_keeps ka) hn
    ((ka.gpr _ (by decide)).trans h.src) ap) fun b ⟨bt, kb⟩ => ?_
  change WP isa (.block (([.addImm .x .x9 .x9 128] : List Instr) ++
    [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15])) b _
  rw [WP.block_append_iff]
  refine WP.mono (bNext_ok b n ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans h.src)))
    fun c ⟨c9, kc⟩ => ?_
  refine WP.mono (aNext_ok c n hn ((kc.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans
    ((ka.gpr _ (by decide)).trans h.counter)))) fun t ⟨tc, tz, kt⟩ => ?_
  obtain kab : TableKeep base 2048 1920 a b := kb.mono (by omega_arith) (by omega_arith)
  obtain kall : PowersKeep base 2048 1920 s t :=
    ((PowersKeep.of_keeps ka (by decide)).trans (PowersKeep.of_tableKeep kab)).trans
      ((PowersKeep.of_keeps kc (by decide)).trans (PowersKeep.of_keeps kt (by decide)))
  obtain oall : Outside base 2048 1920 s.mem t.mem := by
    rw [kt.mem, kc.mem, ← ka.mem]; exact kab.mem
  refine ⟨tz, by omega_arith, kall.scratch h.scratch, tc, ?_, ?_, ?_, h.keep.trans kall, h.out.trans oall⟩
  · rw [kt.gpr _ (by decide)]; exact c9
  · exact (h.tbl.of_far (by rw [kall.rd, kall.wr]) fun x hx => oall x (Or.inr (by omega_arith)))
  · intro i hi
    rw [kt.mem, kc.mem]
    by_cases hin : i < n
    · rw [(TableFrame.table kb.mem).point (by omega_arith) (Or.inl (by omega_arith)) (by omega_arith), ka.mem]
      exact h.table i hin
    · obtain rfl : i = n := by omega_arith
      exact bt

theorem bTableInit_ok (s : State) :
    WP isa (.block [.adrSym .x9 bSym, .movz .w .x19 0 0]) s fun t =>
      t.gpr .x9 = s.syms bSym ∧ t.gpr .x19 = BitVec.ofNat 64 0 ∧ Keeps [.x9, .x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

theorem bTable_ok {s : State} {base : Addr} (hs : Scr s base) (ht : BTblAt s base (s.syms bSym)) :
    WP isa bTable s fun t =>
      (∀ i < 15, tablePoint t.mem base (2048 + 128 * i) = Impl.Ed25519.negBaseCached i) ∧
      PowersKeep base 2048 1920 s t ∧ Outside base 2048 1920 s.mem t.mem := by
  rw [bTable]
  refine WP.seq (WP.mono (bTableInit_ok s) fun a ⟨a9, a19, ka⟩ => ?_)
  obtain h0 : BInv s base (s.syms bSym) 0 a :=
    ⟨by decide, hs.of_keeps ka (by decide), a19, by rw [a9, Nat.mul_zero, BitVec.add_zero],
      ht.of_keeps ka, fun i hi => by omega_arith, PowersKeep.of_keeps ka (by decide),
      by rw [ka.mem]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (Q := BInv s base (s.syms bSym) 15) ?_ fun t h => ⟨h.table, h.keep, h.out⟩
  apply WP.loop (fun n t => BInv s base (s.syms bSym) (15 - n) t ∧ 0 < n ∧ n ≤ 15) (n := 15)
  · intro n t ⟨h, hn, hn15⟩
    have hn' : 0 < n := hn
    have hn15' : n ≤ 15 := hn15
    refine WP.mono (bTableBody_ok (n := 15 - n) (by omega_arith) h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨uz.trans (by rw [he]; rfl), by rw [← he]; exact hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true he]), n - 1, by omega_arith,
        by rw [show 15 - (n - 1) = 15 - n + 1 by omega_arith]; exact hu, by omega_arith, by omega_arith⟩
  · exact ⟨h0, by decide, by decide⟩

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.PointMul`. -/
section
/-! Checkpoint generation before the batch descent. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scr s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  rw [mulCounterInit, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 (BitVec.ofNat 64 count)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc (hs.of_keeps ka (by decide)) (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ka.gpr r (by simpa only [List.mem_singleton] using hr), ka.rd, ka.wr, ka.sp, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact av
  · rw [ka.mem]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's equation, from the windows

The windows leave a representative of `[k]A - [S]B`, compared with `-R`: they
are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent
points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block negR) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  obtain kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 7552 0 (by decide) az) fun b ⟨pb, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at pb
  obtain kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kbe.scr (kar.scr hs)) pb (by decide) (by decide))
    fun c ⟨pc, kc⟩ => ?_
  obtain kce := Keep.of_tableQ kc
  obtain o := tableQ_other kc
  obtain c0 : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kb.mem,
      ka.mem]
  refine WP.mono (fieldCode_ok _ (kce.scr (kbe.scr (kar.scr hs)))) fun t ⟨kt, vt⟩ => ?_
  refine ⟨kar.trans (CounterKeep.of_keep ((kbe.trans kce).trans kt)), ?_, ?_⟩
  · rw [vt, (negR_eval _).1, c0]
  · rw [vt, (negR_eval _).2, pc, kb.mem, ka.mem]

/-- Verification's code before the windows, regrouped. -/
def windowPrep : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) aTable) bTable) (.block windowInit)

theorem PowersKeep.of_table {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t)
    (ho : 56 ≤ o) (hn : o + n ≤ 7808) : PowersKeep base 56 7752 s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by omega_arith) (by omega_arith))⟩

/-- After `windowPrep`: the tables, `d`, an accumulator representing `0` and the counter at 128. -/
structure PrepDone (s : State) (base sig challenge : Addr) (Aa : EPoint dZ) (e : State) : Prop where
  scratch : Scr e base
  sHeader : e.mem.readW (off base 7944) 64 = sig
  kHeader : e.mem.readW (off base 7952) 64 = challenge
  d : env e.mem base 16 = Spec.Ed25519.d
  counter : e.mem.readW (off base 56) 64 = BitVec.ofNat 64 128
  value : RepP (point (env e.mem base) 0 1 2 3) 0
  aTab : TableOf cache e.mem base 5376 Aa
  bTab : TableOf cache e.mem base 2048 (-baseAff)
  keep : PowersKeep base 56 7752 s e
  r : tablePoint e.mem base 7552 = tablePoint s.mem base 7552

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 128. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa) (ht : BTblAt s base (s.syms bSym)) :
    WP isa windowPrep s (PrepDone s base sig challenge Aa) := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono_syms (constField_ok hs 16 Spec.Ed25519.d)
    fun a ⟨ka, va⟩ sya => ?_)))
  obtain ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  obtain aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  obtain aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  obtain ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono_syms (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb syb => ?_
  obtain ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  obtain bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch (by rw [syb, sya]; exact ht.of_powers ksb (by decide)))
    fun c ⟨ct, kc, oc⟩ => ?_
  obtain ksc := ksb.trans (kc.mono (by decide) (by decide))
  obtain cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table oc).point (by decide) (Or.inr (by decide)) (by decide), bR]
  obtain cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env oc (by decide)]; exact hb.d
  obtain cA : TableOf cache c.mem base 5376 Aa := fun j hj => by
    obtain ⟨q, hq, hr⟩ := hb.table j hj
    exact ⟨q, by rw [(TableFrame.table oc).point (by omega_arith) (Or.inr (by omega_arith)) (by omega_arith)]; exact hq,
      hr⟩
  obtain cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [ct j hj, hq], hr⟩
  -- The accumulator and the nibble counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (ksc.scratch hs))
    fun d ⟨kd, vd⟩ => ?_
  obtain kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 128)
    fun e ⟨ec, eg, er, ew, esp, em⟩ => ?_
  obtain kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, esp, em.mono (by decide) (by decide)⟩
  obtain kce : ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  obtain kse := ksc.trans (PowersKeep.of_byte kce)
  refine ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hp,
    (kse.header (by decide) (by decide) (by decide)).trans hc,
    by rw [header_env em, vd]; exact cd, ec, ?_,
    cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide), kse,
    by rw [win_tablePoint kce.mem (by decide) (by decide), cR]⟩
  rw [header_env em, vd, constPoint_eval]
  exact identity_rep.proj

theorem nib_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 768 192 m m') {d : Nat}
    (hd : 960 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega_arith) (Or.inr (by omega_arith)), Outside_F h (by omega_arith) (Or.inr (by omega_arith)),
    Outside_F h (by omega_arith) (Or.inr (by omega_arith)), Outside_F h (by omega_arith) (Or.inr (by omega_arith))]

theorem TableOf.of_nib {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 768 192 m m')
    (ho : 960 ≤ o) (hb : o + 1920 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [nib_tablePoint k (by omega_arith) (by omega_arith)]; exact hq, hr⟩

/-- The windows' start: the nibbles of the scalars, beside `windowPrep`'s. -/
theorem windowStart_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (ht : BTblAt s base (s.syms bSym)) :
    WP isa (.seq windowPrep (.block nibbles)) s fun f => WinLoop f base Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 128 f ∧
      PowersKeep base 56 7752 s f ∧ tablePoint f.mem base 7552 = tablePoint s.mem base 7552 := by
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hA ht) fun e he => ?_)
  have kse := he.keep
  obtain eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  obtain eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine WP.mono (nibbles_ok he.scratch he.kHeader he.sHeader
    (fun d hd => by rw [kse.rd, kse.wr]; exact hcr d hd) (fun d hd => by rw [kse.rd, kse.wr]; exact hr d hd)
    hcf hf) fun f ⟨fk, fs, fm, fg, fr, fw, fsp⟩ => ?_
  obtain kef : PowersKeep base 56 7752 e f :=
    ⟨fun r _ _ hr => fg r (fun h => hr (by rw [h]; decide)) (fun h => hr (by rw [h]; decide)), fr, fw, fsp,
      TableFrame.table (fm.mono (by decide) (by decide))⟩
  obtain hf' : Scr f base := kef.scratch he.scratch
  obtain hK := decodeLE_lt64 s.mem challenge
  obtain hS := decodeLE_lt32 s.mem (off sig 32)
  obtain fe : env f.mem base = env e.mem base := by
    funext i
    exact Outside_F fm (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith))
  refine ⟨⟨⟨hf', fun j hj => by rw [fk j hj, eK], fun j hj => by rw [fs j hj, eS],
    he.aTab.of_nib fm (by decide) (by decide), he.bTab.of_nib fm (by decide) (by decide)⟩,
    by rw [fe]; exact he.d, (fm.word (d := 56) (Or.inl (by decide)) (by decide)).trans he.counter,
    hK, hS, ?_, ByteKeep.refl _ _⟩, kse.trans kef,
    by rw [nib_tablePoint fm (by decide) (by decide), he.r]⟩
  rw [Nat.div_eq_of_lt (show _ < 16 ^ 128 from hK),
    Nat.div_eq_of_lt (show _ < 16 ^ 128 from Nat.lt_trans hS (by decide)), zero_smul, zero_smul,
    add_zero, fe]
  exact he.value

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra)
    (ht : BTblAt s base (s.syms bSym)) :
    WP isa verifyEquationPoints s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowStart_ok hs hp hc hr hf hcr hcf hA ht) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc64, hc128, hf'⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok hc64 hc128 hf') fun g hg => ?_)
  refine WP.seq (WP.mono (loopB_ok hg) fun h hh => ?_)
  obtain ksh := kse.trans (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  obtain ksu := ksh.trans (PowersKeep.of_counter ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hv := hh.value
  simp only [pow_zero, Nat.div_one] at hv
  rw [tv, u0, u4, win_tablePoint hh.keep.mem (by decide) (by decide), eR,
    window_equation hA hR hv hR.neg.proj]

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.RecoverPoint`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Ed25519.AArch64.RecoverCandidate`. -/

@[expose] public section

section
/-! Candidate root and its squared check agree with the decoding specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recoverCandidate_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa recoverCandidate s fun t => CounterKeep base s t ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  rw [recoverCandidate]
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hs) fun a ⟨ka, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_ok (ka.scr hs)) fun b ⟨kb, vb⟩ => ?_)
  have kbr : CounterKeep base a b := ⟨kb.gpr, kb.rd, kb.wr, kb.sp, kb.mem.mono (by decide) (by decide)⟩
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    exact Outside_F kb.mem (by simp only [offset]; omega_using []) (Or.inl (by simp only [offset]; omega_using [hi]))
  refine WP.mono (fieldCode_ok recoverFinishOps (kbr.scr (ka.scr hs))) fun t ⟨kt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootPower_eq, va, au, av3, az]
    rfl
  have kar : CounterKeep base s a := CounterKeep.of_keep ka
  have ktr : CounterKeep base b t := CounterKeep.of_keep kt
  refine ⟨kar.trans (kbr.trans ktr), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.AArch64
end

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => CounterKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨CounterKeep.of_keep kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa recoverPoint s fun t => CounterKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.scr hs) 11 6) fun c ⟨cz, kc, ce⟩ => ?_)
  have kac := ka.trans (CounterKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by simp only [eval, read_x, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.scr hs) b ((kac.gpr _ (by decide) (by decide)).trans hb)
      _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kac.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.scr hs) 11 12) fun d ⟨dz, kd, de⟩ => ?_)
    have kacd := kac.trans (CounterKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by simp only [eval, read_x, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kacd.scr hs))
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (CounterKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.scr hs) b ((kacde.gpr _ (by decide) (by decide)).trans hb)
        _ _ ex ey) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kacd.trans (CounterKeep.of_keep kt), by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.PointDecode`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.AArch64.DecodeLoad`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.AArch64.CanonicalY`. -/
section
/-! Canonical decoding checks y before reduction modulo p. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = n) :
    WP isa (.block canonicalY) s fun t => (t.gpr .x8 == 0) = decide (n < Spec.X25519.P) ∧
      Keeps [.x10, .x11, .x21, .x22, .x23, .x24, .x8] s t := by
  have H := (add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (by rw [hv]; omega_using [hn])).1
  have hz (w : Word) (hw : 0 - w = mask (decide (Spec.X25519.P ≤ n))) :
      (w == 0) = decide (n < Spec.X25519.P) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    have he : w = 0 ↔ mask (decide (Spec.X25519.P ≤ n)) = 0 := by
      rw [← hw]
      change w = 0#64 ↔ 0#64 - w = 0#64
      rw [BitVec.zero_sub, BitVec.neg_eq_zero_iff]
    rw [he]
    by_cases h : Spec.X25519.P ≤ n
    · simp only [decide_eq_true h, mask, ite_true]
      exact iff_of_false (by decide) (by omega_using [h])
    · simp only [decide_eq_false h, mask, Bool.false_eq_true, ite_false]
      exact iff_of_true True.intro (by omega_using [h])
  rw [hv] at H
  have H' := hz _ H
  apply WP.of_runBlock
  simp only [canonicalY, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, show 63 < Size.x.bits from by decide,
    show 16 * 0 < Size.w.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H' ⊢
    exact H'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : DecodeKeep base s t) (k : DecodeKeep base t u) : DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : DecodeKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_counter {base : Addr} {s t : State} (h : CounterKeep base s t) : DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.sp, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .x19 ∨ r = .x1) : DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => DecodeKeep base s t ∧
      t.gpr .x1 = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      (t.gpr .x8 == 0) = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P) := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.gpr _ (by decide)).trans hp)
    (by intro d hd; rw [ka.rd, ka.wr]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.mem] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok (kab.scratch hs) (slot_range 1)) fun c hc => ?_
  subst c
  have cmem := st4_outside b.mem base (show offset 1 + 32 < 2 ^ 64 by decide)
    (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)
  have kc : DecodeKeep base b { b with mem := (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) } :=
    ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, cmem.mono (by decide) (by decide)⟩
  have cy : env (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) base 1 =
      Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change Proof.X25519.toFe (fe _ base (offset 1)) = _
    rw [fe_st4 _ _ (by decide), byval]
  refine WP.mono (canonicalY_ok _ _ (Nat.mod_lt _ (by decide)) byval) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz⟩
  · rw [kt.gpr .x1 (by decide), kb.gpr .x1 (by decide)]; exact asign
  · rw [kt.mem]; exact cy

end VG.Proof.Ed25519.AArch64
end

/-! Canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa pointDecode s fun t => DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [eval, read_x, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_counter (CounterKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.AArch64

end

end


/-! The verification inputs remain readable and outside the workspace. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, h.sp, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scr s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarQ : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  challengeQ : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)
  /-- The static of the cached `-[1]B … -[15]B`, which the equation copies. -/
  tbl : BTblAt s base (s.syms bSym)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) (k : VerifyKeep base s t) (hy : t.syms = s.syms) :
    VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar,
    by rw [hy]; exact h.tbl.of_powers k (by decide)⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarQ _ ‹_›
  · exact h.challengeQ _ ‹_›

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

end VG.Proof.Ed25519.AArch64

end

end

/-! ### `Ed25519.AArch64.WindowCT`, which this module and modules that import it used -/

section

/-! ### `Ed25519.AArch64.RecoverCTBlocks`, which this module and modules that import it used -/

section

/-! Fixed-trace arithmetic blocks used in point recovery. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem x0_agree {base : Addr} {s t : State} (hs : s.gpr .x0 = base) (ht : t.gpr .x0 = base) :
    ∀ r ∈ Taint.ofRegs [.x0], s.gpr r = t.gpr r := agree_ofRegs (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r; exact hs.trans ht.symm)

theorem recoverCandidate_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) recoverCandidate (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem parityBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (freeze (offset 0) ++ recoverParity)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem zeroBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldZero 0)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem negateBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (fieldCode [.const 5 0, .sub 0 5 0])) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem successBlock_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block recoverSuccess) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem recoverInvalid_ct : CT (fun _ _ => True) recoverInvalid (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
  exact fun _ _ _ => agree_ofRegs (by simp)

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.PointEqualCT`. -/

@[expose] public section

section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      Keep base s t ∧
      eval (.zero .x .x8) t = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · change some (t.gpr .x8 == 0) = _
    rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    CT (fun _ _ => True) (.block [.movz .w .x8 (if b then 1 else 0) 0]) (fun _ _ => True) := by
  cases b
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The nibbles are
split out of the inputs through pointers in the scratch, and the digits read
from them through a counter there, the same in both runs by correctness;
everything else is public by the taint analysis. The skipped nibbles of `k`
are its leading zeros, the same in both runs. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : CT (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  CT.seq ((CT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_x0 {x y : State} (h : x.gpr .x0 = y.gpr .x0) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [.x0], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-- Code the taint analysis proves constant time with `x0` alone public. -/
theorem x0_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .x0 = base)
    (h : CT (fun x y => x.gpr .x0 = y.gpr .x0) c (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree2 {x y : State} {a b : Reg} (h : x.gpr a = y.gpr a ∧ x.gpr b = y.gpr b) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [a, b], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

/-! ## Digits -/

/-- A digit's code: its counter by correctness, the rest by the taint analysis. -/
theorem digit_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {o : Nat}
    (hrest : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o]) (fun _ _ => True)) :
    CT (fun x y => (WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base K S A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (digitAt o)) (fun _ _ => True) := by
  have hpre : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block [ld .x8 56]) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  have w (x : State) (h : WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) :
      WP isa (.block [ld .x8 56]) x fun t => t.gpr .x0 = base ∧ t.gpr .x8 = C :=
    WP.mono (loadPointer_ok h.1.scratch .x8 56 (by decide) (by decide)) fun t ⟨tp, kt⟩ =>
      ⟨(kt.gpr _ (by decide)).trans h.1.scratch.x0, tp.trans h.2⟩
  rw [digitAt, show ([ld .x8 56, .add .x .x8 .x0 .x8, .ldrb .x19 .x8 o] : List Instr) =
    [ld .x8 56] ++ [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o] from rfl]
  refine blockAppend_ct ((CT.wp (x0_ct (fun x h => h.1.scratch.x0) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

theorem digitRest_ct (o : Nat) (ho : o = 768 ∨ o = 896) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o]) (fun _ _ => True) := by
  rcases ho with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base : Addr) (K S : Nat) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  CT (fun x y => (WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base K S A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitK_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} :
    DigitCT base K S A C (digitAt 768) :=
  digit_ct (digitRest_ct _ (.inl rfl))

theorem digitS_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} :
    DigitCT base K S A C (digitAt 896) :=
  digit_ct (digitRest_ct _ (.inr rfl))

/-! ## Windows -/

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base : Addr) (K S : Nat) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base K S A s
  d : env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, RepP (point (env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigit_ct (o : Nat) (add : List Instr) (h : o = 5376 ∧ add = pointAddCachedP ∨
    o = 5376 ∧ add = pointAddCached ∨ o = 2048 ∧ add = pointAddCachedP) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v o : Nat} (hdig : DigitCT base K S A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base K S A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .x0 = base ∧ u.gpr .x19 = BitVec.ofNat 64 v :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, ku⟩ =>
      ⟨(ku.gpr _ (by decide)).trans h.ctx.scratch.x0, uv⟩
  refine CT.seq ((CT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  rw [addDigit]
  refine CT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ h => ⟨h.1, trivial⟩)
  · simp only [eval, read_x, h.1.2, h.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.trans h.1.2.2.symm⟩)
      (fun _ _ h => h)

theorem doubleWindow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) doubleWindow (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem windowWith_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v : Nat} (hdig : DigitCT base K S A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (windowWith digit add) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base K S A C digit v x) :
      WP isa doubleWindow x (WinPre base K S A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (doubleWindow_ok h.ctx.scratch ha) fun b ⟨br, bh, bk⟩ => ?_
    have kb := WinKeep.of_double bk
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br.proj⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowWith]
  exact seq_same (x0_ct (fun x h => h.ctx.scratch.x0) doubleWindow_ct) hw (digitAdd_ct hdig hadd)

theorem windowA_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : DigitCT base K S A C digit) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (windowA digit) (fun _ _ => True) :=
  windowWith_ct hdig (addDigit_ct _ _ (.inl ⟨rfl, rfl⟩))

/-- After a window of `k`, the next digit's start. -/
theorem windowWith_next {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr}
    {digit next add : List Instr} {full : Bool} (hadd : AddSpec add cache full) {v w : Nat} {x : State}
    (h : WinPre base K S A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowWith digit add) x (WinPre base K S A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowWith_ok h.1.ctx h.1.d ha hadd h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br.proj⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowAB_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : DigitCT base K S A C digitA) (hB : DigitCT base K S A C digitB) :
    CT (fun x y => (WinPre base K S A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (WinPre base K S A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact seq_same ((windowWith_ct hA (addDigit_ct _ _ (.inr (.inl ⟨rfl, rfl⟩)))).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowWith_next pointAddCached_spec h)
    (digitAdd_ct hB (addDigit_ct _ _ (.inr (.inr ⟨rfl, rfl⟩))))

/-! ## Nibbles -/

theorem batchBegin_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchBegin) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem batchTest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchTest) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem aboveLow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block aboveLow) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

/-- After `batchBegin`: the counter is `i`. -/
theorem nibBegin_ok {s₀ x : State} {base : Addr} {A : EPoint dZ} {K S i : Nat}
    (h : WinLoop s₀ base A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base K S A a ∧ env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, RepP (point (env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_
  have ka : ByteKeep base x a := ByteKeep.of_counter ag ar aw asp am
  exact ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩, av⟩

theorem nibStepA_ct {base : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 128) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base A K S (i + 1) y)) nibStepA (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let v := K / 16 ^ i % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base A K S (i + 1) x) :
      WP isa (.block batchBegin) x (WinPre base K S A C (digitAt 768) v) := by
    obtain ⟨s₀, h⟩ := h
    exact WP.mono (nibBegin_ok h) fun a ⟨actx, ad, av, ac⟩ =>
      ⟨actx, ad, av, ac, digitK actx hi ac, Nat.mod_lt _ (by decide)⟩
  have w2 (x : State) (h : WinPre base K S A C (digitAt 768) v x) :
      WP isa (windowA (digitAt 768)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).x0
  rw [nibStepA]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  exact seq_same (windowA_ct digitK_ct) w2 (x0_ct (fun _ h => h) aboveLow_ct)

theorem nibStepAB_ct {base : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base A K S (i + 1) y)) nibStepAB (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kv := K / 16 ^ i % 16
  let sv := S / 16 ^ i % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        WinPre base K S A C (digitAt 768) kv a ∧ DigitSpec base a (digitAt 896) sv ∧ sv < 16 := by
    obtain ⟨s₀, h⟩ := h
    exact WP.mono (nibBegin_ok h) fun a ⟨actx, ad, av, ac⟩ =>
      ⟨⟨actx, ad, av, ac, digitK actx (by omega_using [hi]) ac, Nat.mod_lt _ (by decide)⟩, digitS actx hi ac,
        Nat.mod_lt _ (by decide)⟩
  have w2 (x : State) (h : WinPre base K S A C (digitAt 768) kv x ∧
      DigitSpec base x (digitAt 896) sv ∧ sv < 16) :
      WP isa (windowAB (digitAt 768) (digitAt 896)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).x0
  rw [nibStepAB]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  exact seq_same (windowAB_ct digitK_ct digitS_ct) w2 (x0_ct (fun _ h => h) batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` nibbles left. -/
def LoopRun (R₀ : State → Prop) (base : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base A K S c x

theorem loopA_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 64) :
    CT (fun x y => LoopRun R₀ base A K S (64 + n) x ∧ LoopRun R₀ base A K S (64 + n) y)
      (.loop nibStepA (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base A K S (64 + n) x ∧
    LoopRun R₀ base A K S (64 + n) y) ∧ 0 < n ∧ n ≤ 64) ?_ n).mono
      (fun _ _ h => ⟨h, hn0, hn⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 64
  · have hw (x : State) (h : LoopRun R₀ base A K S (64 + (j + 1)) x) :
        WP isa nibStepA x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base A K S (64 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((nibStepA_ct (i := 64 + j) (by omega_using [hj])).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega_using [], ⟨hx, hy⟩, by omega_using [this], by omega_using [hj]⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

theorem windowsA_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc64 : 64 ≤ c) (hc128 : c ≤ 128) :
    CT (fun x y => LoopRun R₀ base A K S c x ∧ LoopRun R₀ base A K S c y) windowsA
      (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y) := by
  have hw (x : State) (h : LoopRun R₀ base A K S c x) : WP isa (.block aboveLow) x fun u =>
      eval (.nonzero .x .x19) u = some (decide (c ≠ 64)) ∧ LoopRun R₀ base A K S c u := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact WP.mono (aboveLow_ok h.ctx.scratch c hc128 h.counter) fun u ⟨uz, ku⟩ =>
      ⟨uz, s₀, r₀, h.of_keeps ku (by decide)⟩
  rw [windowsA]
  refine CT.seq ((CT.wp (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0)
    aboveLow_ct) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => h.1.1.trans h.2.1.symm) ?_ ?_
  · obtain ⟨n, rfl⟩ : ∃ n, c = 64 + n := ⟨c - 64, by omega_using [hc64]⟩
    by_cases hn : n = 0
    · subst hn
      exact CT.of_false fun x y h => by
        have := h.2; rw [h.1.1.1] at this; cases this
    · exact (loopA_ct n (by omega_using [hn]) (by omega_using [hc128])).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩)
        (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y h => ⟨h.1, ?_⟩
    have hc : c = 64 := by
      by_contra hne
      have := h.2.2; rw [h.2.1.1.1, decide_eq_true hne] at this; cases this
    subst hc
    exact ⟨h.2.1.1.2, h.2.1.2.2⟩

theorem loopB_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y)
      (.loop nibStepAB (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base A K S 0 x ∧ LoopRun R₀ base A K S 0 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base A K S n x ∧
    LoopRun R₀ base A K S n y) ∧ 0 < n ∧ n ≤ 64) ?_ 64).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 64
  · have hw (x : State) (h : LoopRun R₀ base A K S (j + 1) x) :
        WP isa nibStepAB x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((nibStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega_using [], ⟨hx, hy⟩, by omega_using [this], by omega_using [hj]⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

/-! ## Skipping the leading zero nibbles of `k` -/

/-- A run of the skipping: from a state satisfying `R₀`, with `64 + n` nibbles left. -/
def SkipRun (R₀ : State → Prop) (base : Addr) (A : EPoint dZ) (K S n : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipInv s₀ base A K S n x

/-- The counter, less one. -/
def skipPrefix : List Instr := [ld .x8 56, .subImm .x .x8 .x8 1]

theorem skipPrefix_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block skipPrefix) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipRest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
    (.block [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

theorem skipPrefix_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipPrefix) s fun t => t.gpr .x0 = base ∧ t.gpr .x8 = BitVec.ofNat 64 j := by
  rw [skipPrefix, show ([ld .x8 56, .subImm .x .x8 .x8 1] : List Instr) =
    [ld .x8 56] ++ [.subImm .x .x8 .x8 1] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun t ⟨tv, kt⟩ => ?_
  exact ⟨(kt.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hs.x0), tv⟩

theorem movzZero_ct : CT (fun _ _ => True) (.block [.movz .w .x19 0 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs []) (fun _ _ _ => agree_ofRegs (by simp)) (by taint_decide)

theorem skipStore_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0)
    (.block [st .x8 56, .subImm .x .x19 .x8 64]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipBody_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S j : Nat} :
    CT (fun x y => SkipRun R₀ base A K S (j + 1) x ∧ SkipRun R₀ base A K S (j + 1) y)
      skipBody (fun _ _ => True) := by
  let P := SkipRun R₀ base A K S (j + 1)
  have hx0 (x : State) (h : P x) : x.gpr .x0 = base := by
    obtain ⟨_, _, h, _⟩ := h; exact h.ctx.scratch.x0
  have hpre (x : State) (h : P x) : WP isa (.block skipPrefix) x fun t =>
      t.gpr .x0 = base ∧ t.gpr .x8 = BitVec.ofNat 64 (64 + j) := by
    obtain ⟨_, _, h, _⟩ := h
    exact skipPrefix_ok h.ctx.scratch (64 + j) (by rw [h.counter]; rfl)
  have hload : CT (fun x y => P x ∧ P y) (.block skipLoad) (fun _ _ => True) := by
    rw [show skipLoad = skipPrefix ++ [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768] from rfl]
    refine blockAppend_ct ((CT.wp (x0_ct hx0 skipPrefix_ct) fun x y h => ⟨hpre x h.1, hpre y h.2⟩).mono
      (fun _ _ h => h) ?_) skipRest_ct
    intro x y ⟨_, hx, hy⟩
    exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
  have hw (x : State) (h : P x) : WP isa (.block skipLoad) x fun u => u.gpr .x0 = base ∧
      u.gpr .x19 = BitVec.ofNat 64 (K / 16 ^ (64 + j) % 16) := by
    obtain ⟨_, _, hl, _, _, hn⟩ := h
    refine WP.mono (skipLoad_ok hl.ctx.scratch (64 + j) (by omega_using [hn]) (by rw [hl.counter]; rfl))
      fun u ⟨_, uv, ku⟩ => ⟨(ku.gpr _ (by decide)).trans hl.ctx.scratch.x0,
        by rw [uv, hl.ctx.kNib _ (by omega_using [hn])]⟩
  rw [skipBody]
  refine CT.seq ((CT.wp hload fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => by simp only [eval, read_x, h.1.2, h.2.2]) ?_ ?_
  · exact movzZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact skipStore_ct.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem skipZero_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => SkipRun R₀ base A K S 64 x ∧ SkipRun R₀ base A K S 64 y) skipZero
      (fun x y => ∃ c, 64 ≤ c ∧ c ≤ 128 ∧ LoopRun R₀ base A K S c x ∧
        LoopRun R₀ base A K S c y) := by
  rw [skipZero]
  refine CT.loop (fun n x y => SkipRun R₀ base A K S n x ∧ SkipRun R₀ base A K S n y)
    ?_ 64
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, h, _⟩ := h.1; exact Nat.lt_irrefl 0 h
  by_cases hj : j < 64
  · have hw (x : State) (h : SkipRun R₀ base A K S (j + 1) x) : WP isa skipBody x fun u =>
        eval (.nonzero .x .x19) u = some (skipOn K j) ∧
        (skipOn K j = false → LoopRun R₀ base A K S (skipEnd K j) u) ∧
        (skipOn K j = true → SkipRun R₀ base A K S j u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (skipBody_ok h) fun u ⟨uz, uf, ut⟩ =>
        ⟨uz, fun hf => ⟨s₀, r₀, uf hf⟩, fun ht => ⟨s₀, r₀, ut ht⟩⟩
    refine (CT.wp skipBody_ct fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipOn K j = false := Option.some.inj (xz.symm.trans he)
      exact ⟨skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2, xf hs, yf hs⟩
    · have hs : skipOn K j = true := Option.some.inj (xz.symm.trans he)
      exact ⟨j, by omega_using [], xt hs, yt hs⟩
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, _, h⟩ := h.1; exact hj (by omega_using [h])

/-! ## The nibbles -/

/-- What the nibbles' code needs, in one run. -/
structure NibPre (base sig challenge : Addr) (s : State) : Prop where
  scratch : Scr s base
  kHeader : s.mem.readW (off base 7952) 64 = challenge
  sHeader : s.mem.readW (off base 7944) 64 = sig
  kRead : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16
  sRead : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  kFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)

/-- After `k`'s nibbles, what `S`'s need. -/
structure SNibPre (base sig : Addr) (s : State) : Prop where
  scratch : Scr s base
  sHeader : s.mem.readW (off base 7944) 64 = sig
  sRead : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  mask : s.v .v7 = mask15

/-- A block's trace, with what each run reaches. -/
theorem stage_ct {P F : State → Prop} {xs : List Instr}
    (h : CT (fun x y => P x ∧ P y) (.block xs) (fun _ _ => True))
    (w : ∀ x, P x → WP isa (.block xs) x F) :
    CT (fun x y => P x ∧ P y) (.block xs) (fun x y => F x ∧ F y) :=
  (CT.wp h fun x y hh => ⟨w x hh.1, w y hh.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem ldPtr_ct (d : Nat) (hd : d = 7952 ∨ d = 7944) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block [ld .x2 d]) (fun _ _ => True) := by
  rcases hd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

/-- The nibbles' trace: the scalars' pointers by correctness, the rest by the taint analysis. -/
theorem nibbles_ct {base sig challenge : Addr} :
    CT (fun x y => NibPre base sig challenge x ∧ NibPre base sig challenge y) (.block nibbles)
      (fun _ _ => True) := by
  have c1 := stage_ct (P := NibPre base sig challenge)
    (F := fun x => NibPre base sig challenge x ∧ x.gpr .x2 = challenge)
    (x0_ct (fun x h => h.scratch.x0) (ldPtr_ct 7952 (.inl rfl))) fun x h =>
      WP.mono (loadPointer_ok h.scratch .x2 7952 (by decide) (by decide)) fun t ⟨tp, kt⟩ =>
        ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.mem]; exact h.kHeader,
          by rw [kt.mem]; exact h.sHeader, by rw [kt.rd, kt.wr]; exact h.kRead,
          by rw [kt.rd, kt.wr]; exact h.sRead, h.kFar, h.sFar⟩, tp.trans h.kHeader⟩
  have c2 := stage_ct (P := fun x => NibPre base sig challenge x ∧ x.gpr .x2 = challenge)
    (F := SNibPre base sig)
    ((CT.taint (Taint.ofRegs [.x0, .x2]) (fun _ _ h => agree2 h) (by taint_decide) :
      CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x2 = y.gpr .x2) (.block kNibblesAt)
        (fun _ _ => True)).mono
      (fun x y h => ⟨h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm, h.1.2.trans h.2.2.symm⟩)
      (fun _ _ h => h)) fun x h =>
      WP.mono (kNibblesAt_ok h.1.scratch h.2 h.1.kRead h.1.kFar) fun t ⟨_, tm, tg, tr, tw, _, t7⟩ =>
        ⟨⟨by rw [tg _ (by decide)]; exact h.1.scratch.x0, by rw [tw]; exact h.1.scratch.wr,
          h.1.scratch.nowrap⟩, (tm.word (d := 7944) (Or.inr (by decide)) (by decide)).trans h.1.sHeader,
          by rw [tr, tw]; exact h.1.sRead, h.1.sFar, t7⟩
  have c3 := stage_ct (P := SNibPre base sig) (F := fun x => SNibPre base sig x ∧ x.gpr .x2 = sig)
    (x0_ct (fun x h => h.scratch.x0) (ldPtr_ct 7944 (.inr rfl))) fun x h =>
      WP.mono (loadPointerV_ok h.scratch .x2 7944 (by decide) (by decide)) fun t ⟨tp, kt, tv⟩ =>
        ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.mem]; exact h.sHeader,
          by rw [kt.rd, kt.wr]; exact h.sRead, h.sFar, by rw [tv]; exact h.mask⟩, tp.trans h.sHeader⟩
  have c4 : CT (fun x y => (SNibPre base sig x ∧ x.gpr .x2 = sig) ∧ (SNibPre base sig y ∧ y.gpr .x2 = sig))
      (.block (nibBlocks 32 896 2)) (fun _ _ => True) :=
    (CT.taint (Taint.ofRegs [.x0, .x2]) (fun _ _ h => agree2 h) (by taint_decide) :
      CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x2 = y.gpr .x2) (.block (nibBlocks 32 896 2))
        (fun _ _ => True)).mono
      (fun x y h => ⟨h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm, h.1.2.trans h.2.2.symm⟩)
      (fun _ _ h => h)
  rw [nibbles, kNibbles, sNibbles, List.append_assoc]
  exact blockAppend_ct c1 (blockAppend_ct c2 (blockAppend_ct c3 c4))

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scr s base ∧ RepP (point (env s.mem base) 0 1 2 3) P ∧ RepP (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact repP_cross_y h.2.1 h.2.2
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : CT (fun s t => (Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scr t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw2 (s : State) (h : Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      change some (t.gpr .x8 == 0) = _
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := CT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine CT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (CT.ite ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64

end

end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTPublic`. -/

@[expose] public section

section
/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs
  /-- The static's address, the same in both runs. -/
  sym : s.syms bSym = T

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) (kt : VerifyKeep base s t)
    (hy : t.syms = s.syms) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t :=
  ⟨h.context.of_keep kt hy, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes, by rw [hy]; exact h.sym⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    CT (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r t) verifyEquationPoints (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x) :
      WP isa (.seq windowPrep (.block nibbles)) x (SkipRun R₀ base Aa K S 64) := by
    have c := h.1.context
    refine WP.mono (windowStart_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarQ
      c.scalarFar c.challengeQ c.challengeFar (by rw [h.2.1]; exact hA) c.tbl) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we, Nat.div_eq_of_lt we.kLt, by decide, by decide⟩
  have wp (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x) :
      WP isa windowPrep x (NibPre base sig challenge) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader
      (by rw [h.2.1]; exact hA) c.tbl) fun e he => ?_
    exact ⟨he.scratch, he.kHeader, he.sHeader, by rw [he.keep.rd, he.keep.wr]; exact c.challengeQ,
      by rw [he.keep.rd, he.keep.wr]; exact c.scalarQ, c.challengeFar, c.scalarFar⟩
  have wn (x : State) (h : LoopRun R₀ base Aa K S 0 x) :
      WP isa (.block negR) x (EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [pow_zero, Nat.div_one] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨ku.scr hx.ctx.scratch, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg.proj
  have prepCT : CT (fun x y => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r y) windowPrep (fun _ _ => True) := by
    rw [windowPrep]
    refine CT.taintS (L := [bSym]) (Taint.ofRegs [.x0]) (fun x y h => ⟨agree_x0
      (h.1.1.context.scratch.x0.trans h.2.1.context.scratch.x0.symm), fun n hn => ?_⟩) (by taint_decide)
    simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.1.sym.trans h.2.1.sym.symm
  have startCT : CT (fun x y => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r y) (.seq windowPrep (.block nibbles))
      (fun _ _ => True) :=
    seq_same prepCT wp nibbles_ct
  have negRCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block negR) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  refine CT.seq ((CT.wp startCT fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.seq skipZero_ct ?_
  refine CT.seq (fun x y tx ty x' y' ⟨hsp, c, hc64, hc128, hx, hy⟩ ex ey =>
    windowsA_ct hc64 hc128 x y tx ty x' y' ⟨hsp, hx, hy⟩ ex ey) ?_
  refine CT.seq loopB_ct ?_
  exact seq_same (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0) negRCT) wn
    (pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTAdjust`. -/
section
/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ eval (.zero .x .x8) t = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  change some (t.gpr .x8 == 0) = _
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    CT (fun x y => Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y)
      (.seq (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine CT.seq (R := fun x y => x.gpr .x0 = base ∧ y.gpr .x0 = base)
    (CT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : CT (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => agree_ofRegs (by simp)
    have hw := CT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some true) =>
        And.intro (WP.block_nil h.1.1.x0) (WP.block_nil h.1.2.1.x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct base).mono
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        ⟨h.1.1.x0, h.1.2.1.x0⟩) (fun _ _ h => h)
    have hw := CT.wp ht
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        And.intro (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) fun _ k => (k.1.scr h.1.1).x0)
          (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) fun _ k => (k.1.scr h.1.2.1).x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.scr h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.AArch64
end

/-! The negative-zero check leaks only the public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem testThenSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.ite (.nonzero .x .x1) recoverInvalid recoverAdjustSign) (fun _ _ => True) := by
  refine CT.ite ?_ ?_ ?_
  · intro s t h
    simp only [eval, read_x, h.1.2.1, h.2.2.1]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => h.1) (fun _ _ h => h)

theorem recoverSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverSign (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ eval (.zero .x .x8) t = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨tz, kt, tm⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩, ?_⟩
    · rw [tm]; exact h.2.2
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · intro s t h
    exact h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def RootCTState (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ eval (.zero .x .x8) s = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ eval (.zero .x .x8) t = some (rootCheckValue y minus))) := by
  have ht : CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ eval (.zero .x .x8) t = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨tz, kt, te⟩ => ?_
    refine ⟨⟨⟨kt.scr h.1.1, (kt.gpr _ (by decide)).trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    change some (t.gpr .x8 == 0) = _
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1) fun t ⟨kt, te⟩ => ?_
    refine ⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
        (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))
      (fun _ _ => True) := by
  refine CT.seq (rootCheck_ct base b y true) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 6)) (.ite (.zero .x .x8) recoverSign
        (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
          (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))))
      (fun _ _ => True) := by
  refine CT.seq (rootCheck_ct base b y false) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ env s.mem base 1 = y

theorem recoverPoint_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      recoverPoint (fun _ _ => True) := by
  have ht := (recoverCandidate_ct base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa recoverCandidate s (RootCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverPoint]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PointDecodeCT`. -/
section
/-! Canonical point decoding leaks only its public bytes. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


def DecodeCTPre (base p : Addr) (bs : List Byte) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x2 = p ∧
    (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) ∧ Spec.Ed25519.bytesAt s.mem p 32 = bs

theorem pointDecode_ct (base p : Addr) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (.block pointDecodeLoad) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base p bs s) :
      WP isa (.block pointDecodeLoad) s fun t => RecoverCTPre base b y t ∧
        eval (.zero .x .x8) t = some (decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P)) := by
    refine WP.mono (pointDecodeLoad_ok h.1 h.2.1 h.2.2.1) fun t ⟨kt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.scratch h.1, ?_, ?_⟩, ?_⟩
    · rw [tb, h.2.2.2]
    · rw [ty, h.2.2.2]
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : Addr} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .x8 = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.AArch64
end

/-! The canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem verifyScalar_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0])
      (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0]) s
        (fun t => t.gpr .x2 = off sig 32) := by
    change WP isa (.block (([ld .x2 7944] : List Instr) ++
      ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr))) s _
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, _⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add32_ok a .x2) fun b ⟨bp, _⟩ => ?_
    refine WP.mono (setZeroX10_ok b) fun t ⟨_, kt⟩ => ?_
    have tp := (kt.gpr .x2 (by decide)).trans bp
    rw [tp, ap, h.sigHeader]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : CT (fun s t => s.gpr .x2 = off sig 32 ∧ t.gpr .x2 = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  change CT _ (.block (([ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] : List Instr) ++
    (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr)))) _
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

end VG.Proof.Ed25519.AArch64
