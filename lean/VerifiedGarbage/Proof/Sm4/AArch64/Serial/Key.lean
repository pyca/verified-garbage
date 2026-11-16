module

public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Round
public import VerifiedGarbage.Proof.Sm4.Rounds
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.ModeCore
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.State
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Key
meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Round
meta import VerifiedGarbage.Proof.Sm4.Rounds
meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.ModeCore
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Proof.Sm4.AArch64.Serial.State
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Aes.Bitsliced
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SM4 key expansion on AArch64, one word at a time, meets its contract

`keyRound_run`: a round of the key schedule is `sround .key` with `CK`'s
word, and stores its round key. `keyRounds_run`: the rounds in turn
(`ksteps`), with the round keys stored so far; a round key is the word of the
group of four rounds it was computed in (`ksteps_rk`), which is `rkOf`.
`expandKey_verified`: `vg_sm4_expand_key` meets `Spec.Sm4.expandKeyContract`
with no stack, and is constant time by the taint analysis with the pointers
public.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl
open VG.Impl.Sm4.AArch64.Serial
open VG.Impl.Sm4 (Lin)
open VG.Proof.Sm4 (sround quad quads rkOf keyInit)

/-! ## Constants and the linear layer -/

theorem movzk32 (x : BitVec 32) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (x.extractLsb' 0 16))) &&& (0xFFFF : BitVec 32) |||
        BitVec.setWidth 32 (x.extractLsb' 16 16) <<< 16) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.ofNat_eq_ofNat, BitVec.getLsbD_ofNat,
    VG.AArch64.testBit_65535, hi, decide_true, Bool.true_and, Nat.zero_add]
  rcases (by omega_using [] : i < 16 ∨ 16 ≤ i) with h | h <;>
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.and_true, Bool.not_true, Bool.not_false]
  all_goals exact congrArg _ (by omega_using [h])

theorem const32_run (s : State) (v : BitVec 32) :
    ∃ t, runBlock isa (const32 v) s = some t ∧ t.gpr .x10 = v.setWidth 64 ∧
      (∀ r, r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let a := s.write .w .x10 ((v.extractLsb' 0 16).setWidth 32)
  let b := a.write .w .x10 ((a.gpr .x10).setWidth 32 &&& (0xFFFF : BitVec 32) |||
    (v.extractLsb' 16 16).setWidth 32 <<< 16)
  refine ⟨b, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [const32, runBlock_cons, exec_movz_w, runStep_some, runBlock_cons, exec_movk_w, runStep_some,
      runBlock_nil]
  · simp only [b, a, gpr_write_self]
    exact congrArg (BitVec.setWidth 64) (movzk32 v)
  · intro r hr
    simp only [b, a, gpr_write_of_ne _ _ _ hr]

theorem keyLinear_eq (x : BitVec 32) :
    x ^^^ x.rotateRight 19 ^^^ x.rotateRight 9 = Spec.Sm4.keyLinear x := by
  rw [show 19 = 32 - 13 by rfl, rotate_complement x 13 (by decide) (by decide),
    show 9 = 32 - 23 by rfl, rotate_complement x 23 (by decide) (by decide)]
  rfl

theorem keyLinear_run (s : State) :
    ∃ t, runBlock isa keyLinear s = some t ∧
      t.gpr .x11 = (Spec.Sm4.keyLinear ((s.gpr .x10).setWidth 32)).setWidth 64 ∧
      (∀ r, r ≠ .x11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  let x := (s.gpr .x10).setWidth 32
  let a := s.write .w .x11 (x ^^^ x.rotateRight 19)
  let b := a.write .w .x11 ((a.read .w .x11) ^^^ x.rotateRight 9)
  refine ⟨b, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [keyLinear, runBlock_cons, exec_logicRor (sz := .w) (sh := 19) (by decide),
      exec_logicRor (sz := .w) (sh := 9) (by decide), runStep_some, runBlock_nil]
    rfl
  · simp only [b, a, gpr_write_self, State.read, Size.bits]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rw [keyLinear_eq]
  · intro r hr
    simp only [b, a, gpr_write_of_ne _ _ _ hr]

/-! ## The key's words -/

theorem wordReg_ne_args : ∀ j < 4, wordReg j ≠ .x0 ∧ wordReg j ≠ .x1 := by decide

theorem loadKeyWord_run {s : State} {i : Nat} (hi : i < 4)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa (loadKeyWord i) s = some t ∧
      words t i = rev32 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 32) ^^^ Spec.Sm4.fk.getD i 0 ∧
      (∀ q, q ≠ wordReg i → q ≠ .x10 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  have hr10 : wordReg i ≠ .x10 := (wordReg_ne i hi).1
  let a := s.write .w (wordReg i) (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 32)
  let b := a.write .w (wordReg i) (rev32 (a.read .w (wordReg i)))
  obtain ⟨c, ce, cv, cg, cm, crd, cwr, csp, cvec⟩ := const32_run b (Spec.Sm4.fk.getD i 0)
  let t := c.write .w (wordReg i) (c.read .w (wordReg i) ^^^ c.read .w .x10)
  refine ⟨t, ?_, ?_, ?_, cm, crd, cwr, csp, cvec⟩
  · rw [loadKeyWord, List.append_assoc, List.cons_append, List.cons_append, List.nil_append,
      runBlock_cons, exec_ldr_w ⟨by omega_using [], by omega_using [hi]⟩ hread, runStep_some,
      runBlock_cons, exec_rev32, runStep_some, VG.Interleave.runBlock_append, ce, Option.bind_some,
      runBlock_cons, exec_logic, runStep_some, runBlock_nil]
  · simp only [words, t, gpr_write_self, State.read, Size.bits, cv, cg _ hr10, b, a,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  · intro q hq h10
    simp only [t, gpr_write_of_ne _ _ _ hq, cg _ h10, b, a]

theorem keyLoads_run (s : State) (n : Nat) (hn : n ≤ 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap loadKeyWord) s = some t ∧
      (∀ j < n, words t j =
        rev32 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) ^^^ Spec.Sm4.fk.getD j 0) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  induction n with
  | zero => exact ⟨s, rfl, fun _ h => absurd h (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ag, am, ard, awr, asp, avec⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x0 = s.gpr .x0 := ag _ (by decide)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [ard, awr, ab]
      exact hread n (by omega_using [hn])
    obtain ⟨b, be, bv, bg, bm, brd, bwr, bsp, bvec⟩ := loadKeyWord_run (by omega_using [hn]) ar
    refine ⟨b, ?_, ?_, ?_, bm.trans am, brd.trans ard, bwr.trans awr, bsp.trans asp, bvec.trans avec⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · intro j hj
      by_cases h : j = n
      · subst j
        simpa only [am, ab] using bv
      · rw [words, bg _ (fun e => h (wordReg_inj _ (by omega_using [hn, hj]) _ (by omega_using [hn]) e))
          (wordReg_ne j (by omega_using [hn, hj])).1]
        exact aw j (by omega_using [hj, h])
    · intro r hr
      have hreg : r ≠ wordReg n := fun he => hr (he ▸ wordReg_mem _ (by omega_using [hn]))
      have h10 : r ≠ .x10 := fun he => hr (by simp [written, he])
      exact (bg r hreg h10).trans (ag r hr)

/-! ## A round -/

theorem keyInput_run {s : State} {i : Nat} :
    ∃ t, runBlock isa (keyInput i) s = some t ∧
      t.gpr .x10 = (((Spec.Sm4.ck i ^^^ words s ((i + 1) % 4)) ^^^ words s ((i + 2) % 4)) ^^^
        words s ((i + 3) % 4)).setWidth 64 ∧
      (∀ r, r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  have hb := (wordReg_ne ((i + 1) % 4) (Nat.mod_lt _ (by decide))).1
  have hc := (wordReg_ne ((i + 2) % 4) (Nat.mod_lt _ (by decide))).1
  have hd := (wordReg_ne ((i + 3) % 4) (Nat.mod_lt _ (by decide))).1
  obtain ⟨a, ae, av, ag, am, ard, awr, asp, avec⟩ := const32_run s (Spec.Sm4.ck i)
  let e := a.write .w .x10 (a.read .w .x10 ^^^ a.read .w (wordReg ((i + 1) % 4)))
  let f := e.write .w .x10 (e.read .w .x10 ^^^ e.read .w (wordReg ((i + 2) % 4)))
  let g := f.write .w .x10 (f.read .w .x10 ^^^ f.read .w (wordReg ((i + 3) % 4)))
  refine ⟨g, ?_, ?_, ?_, am, ard, awr, asp, avec⟩
  · rw [keyInput, VG.Interleave.runBlock_append, ae, Option.bind_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_nil]
  · simp only [g, f, e, gpr_write_self, State.read, Size.bits,
      gpr_write_of_ne _ _ _ hc, gpr_write_of_ne _ _ _ hd, av, ag _ hb, ag _ hc, ag _ hd, words]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  · intro r hr
    simp only [g, f, e, gpr_write_of_ne _ _ _ hr, ag _ hr]

theorem keyRound_run {s : State} {i : Nat} (hi : i < 32) (hc : Constants s) (ht : Table s)
    (hw : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa (keyRound i) s = some t ∧
      (∀ w < 4, words t w = sround .key (Spec.Sm4.ck i) (i % 4) (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 (4 * i))
        (sround .key (Spec.Sm4.ck i) (i % 4) (words s) (i % 4)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let ra := wordReg (i % 4)
  have hlt : i % 4 < 4 := Nat.mod_lt _ (by decide)
  have ha10 : ra ≠ .x10 := (wordReg_ne _ hlt).1
  have ha11 : ra ≠ .x11 := (wordReg_ne _ hlt).2
  have ha1 : ra ≠ .x1 := (wordReg_ne_args _ hlt).2
  obtain ⟨a, ae, av, ag, am, ard, awr, asp, avec⟩ := keyInput_run (s := s) (i := i)
  have ac : Constants a := by simpa only [Constants, avec] using hc
  have atab : Table a := by simpa only [Table, avec] using ht
  obtain ⟨b, be, bv, bg, bm, brd, bwr, bsp, bvec⟩ := substitute_run a ac atab
  obtain ⟨c, ce, cv, cg, cm, crd, cwr, csp, cvec⟩ := keyLinear_run b
  let d := c.write .w ra (c.read .w ra ^^^ c.read .w .x11)
  let t : State := { d with mem := d.mem.writeW (d.gpr .x1 + BitVec.ofNat 64 (4 * i)) ((d.gpr ra).setWidth 32) }
  have cra : c.read .w ra = words s (i % 4) := by
    simp only [State.read, Size.bits, cg _ ha11, bg _ ha10, ag _ ha10, words, ra]
  have val : c.read .w .x11 = Lin.key.t
      (words s ((i % 4 + 1) % 4) ^^^ words s ((i % 4 + 2) % 4) ^^^ words s ((i % 4 + 3) % 4) ^^^
        Spec.Sm4.ck i) := by
    simp only [State.read, Size.bits, cv, bv, av,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    rw [show (i % 4 + 1) % 4 = (i + 1) % 4 by omega_using [],
      show (i % 4 + 2) % 4 = (i + 2) % 4 by omega_using [],
      show (i % 4 + 3) % 4 = (i + 3) % 4 by omega_using [], Lin.t_key]
    unfold Spec.Sm4.keyT
    congr 2
    ac_rfl
  have dra : (d.gpr ra).setWidth 32 = sround .key (Spec.Sm4.ck i) (i % 4) (words s) (i % 4) := by
    simp only [d, gpr_write_self, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    rw [cra, val]
    simp only [sround, ite_true]
  have d1 : d.gpr .x1 = s.gpr .x1 := by
    rw [gpr_write_of_ne _ _ _ (Ne.symm ha1), cg _ (by decide), bg _ (by decide), ag _ (by decide)]
  have other : ∀ r, r ≠ ra → r ≠ .x10 → r ≠ .x11 → t.gpr r = s.gpr r := by
    intro r hra h10 h11
    change d.gpr r = s.gpr r
    rw [gpr_write_of_ne _ _ _ hra, cg _ h11, bg _ h10, ag _ h10]
  have tv : ∀ v, v ∉ [.v0, .v1, .v2, .v3] → t.v v = s.v v := by
    intro v hv
    rw [show t.v v = c.v v from rfl, cvec, bvec _ hv, avec]
  have dwr : InRegions d.wr (d.gpr .x1 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [d1, show d.wr = s.wr from cwr.trans (bwr.trans awr)]
    exact hw
  refine ⟨t, ?_, ?_, hc.of_preserved tv, ht.of_preserved tv, ?_, ?_, crd.trans (brd.trans ard),
    cwr.trans (bwr.trans awr), csp.trans (bsp.trans asp)⟩
  · rw [keyRound, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, ae, Option.bind_some, be,
      Option.bind_some, ce, Option.bind_some]
    have e1 : runBlock isa (roundOutput i) c = some d := by
      rw [roundOutput, runBlock_cons, exec_logic, runStep_some, runBlock_nil]
    rw [e1, Option.bind_some, runBlock_cons, exec_str_w ⟨by omega_using [], by omega_using [hi]⟩ dwr,
      runStep_some, runBlock_nil]
  · intro w hw'
    by_cases h : w = i % 4
    · subst w
      exact dra
    · have hreg : wordReg w ≠ ra := fun e => h (wordReg_inj w hw' _ hlt e)
      rw [words, other _ hreg (wordReg_ne w hw').1 (wordReg_ne w hw').2]
      simp only [sround, h, ite_false, words]
  · intro r hr
    have hreg : r ≠ ra := fun he => hr (he ▸ wordReg_mem _ hlt)
    have h10 : r ≠ .x10 := fun he => hr (by simp [written, he])
    have h11 : r ≠ .x11 := fun he => hr (by simp [written, he])
    exact other r hreg h10 h11
  · change d.mem.writeW _ _ = _
    rw [d1, dra]
    exact congrArg (fun m => Mem.writeW m _ _) (cm.trans (bm.trans am))

/-! ## The rounds -/

/-- The first `n` rounds of the key schedule, in place. -/
def ksteps (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .key (Spec.Sm4.ck i) (i % 4) z) x

theorem ksteps_succ (n : Nat) (x : Nat → BitVec 32) :
    ksteps (n + 1) x = sround .key (Spec.Sm4.ck n) (n % 4) (ksteps n x) := by
  simp only [ksteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ksround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .key k a x w = sround .key k a y w := by
  unfold sround
  split
  · rw [h a ha, h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide)),
      h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem ksteps_congr (n : Nat) (x y : Nat → BitVec 32) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, ksteps n x w = ksteps n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [ksteps_succ, ksteps_succ]
    exact ksround_congr _ (Nat.mod_lt _ (by decide)) ih hw

theorem ksteps_quads (x : Nat → BitVec 32) (n : Nat) :
    ksteps (4 * n) x = quads .key Spec.Sm4.ck n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ksteps, VG.Proof.Sm4.range_four, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change sround .key (Spec.Sm4.ck (4 * n + 3)) ((4 * n + 3) % 4)
      (sround .key (Spec.Sm4.ck (4 * n + 2)) ((4 * n + 2) % 4)
        (sround .key (Spec.Sm4.ck (4 * n + 1)) ((4 * n + 1) % 4)
          (sround .key (Spec.Sm4.ck (4 * n)) ((4 * n) % 4) (ksteps (4 * n) x)))) = _
    rw [ih, show (4 * n) % 4 = 0 by omega_using [], show (4 * n + 1) % 4 = 1 by omega_using [],
      show (4 * n + 2) % 4 = 2 by omega_using [], show (4 * n + 3) % 4 = 3 by omega_using []]
    rfl

/-- The rounds after round `i` of its group of four leave its word alone. -/
theorem ksteps_stable (x : Nat → BitVec 32) (i j : Nat) (hij : i < j) (hj : j ≤ 4 * (i / 4 + 1)) :
    ksteps j x (i % 4) = ksteps (i + 1) x (i % 4) := by
  induction j with
  | zero => exact absurd hij (by omega_using [])
  | succ j ih =>
    by_cases h : j = i
    · subst h; rfl
    · rw [ksteps_succ]
      have hne : ¬i % 4 = j % 4 := by omega_using [hij, hj, h]
      simp only [sround, hne, ↓reduceIte]
      exact ih (by omega_using [hij, h]) (by omega_using [hj])

/-- Round key `i` is its word after round `i`. -/
theorem ksteps_rk (key : Spec.Sm4.Block) (i : Nat) :
    ksteps (i + 1) (keyInit key) (i % 4) = rkOf key i := by
  rw [rkOf, ← ksteps_quads]
  exact (ksteps_stable _ i _ (by omega_using []) (Nat.le_refl _)).symm

theorem keyRounds_run (s : State) (n : Nat) (hn : n ≤ 32) (hc : Constants s) (ht : Table s)
    (hw : ∀ i < 32, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap keyRound) s = some t ∧
      (∀ w < 4, words t w = ksteps n (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      (∀ i < n, t.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 32 = ksteps (i + 1) (words s) (i % 4)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero =>
    exact ⟨s, rfl, fun _ _ => rfl, hc, ht, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), rfl, rfl,
      rfl⟩
  | succ n ih =>
    obtain ⟨a, ae, aw, ac, atab, ag, amem, ard, awr, asp⟩ := ih (by omega_using [hn])
    have ab : a.gpr .x1 = s.gpr .x1 := ag _ (by decide)
    have ar : InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [awr, ab]
      exact hw n (by omega_using [hn])
    obtain ⟨b, be, bw, bc, bt, bg, bm, brd, bwr, bsp⟩ := keyRound_run (by omega_using [hn]) ac atab ar
    have val : sround .key (Spec.Sm4.ck n) (n % 4) (words a) (n % 4) = ksteps (n + 1) (words s) (n % 4) := by
      rw [ksteps_succ]
      exact ksround_congr _ (Nat.mod_lt _ (by decide)) aw (Nat.mod_lt _ (by decide))
    refine ⟨b, ?_, ?_, bc, bt, fun r hr => (bg r hr).trans (ag r hr), ?_, brd.trans ard, bwr.trans awr,
      bsp.trans asp⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        VG.Interleave.runBlock_append, ae, Option.bind_some, be]
    · intro w hw'
      rw [bw w hw', ksteps_succ]
      exact ksround_congr _ (Nat.mod_lt _ (by decide)) aw hw'
    · intro i hi
      rw [bm, ab, val]
      by_cases h : i = n
      · subst i
        rw [Mem.readW_writeW_self32]
      · rw [(frame_write_word _ _ _).readW (w := 32) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact VG.Offset.disjoint (s.gpr .x1) (by omega_using [h]) (by omega_using [hn, hi])
            (by omega_using [hn])) (by decide)]
        exact amem i (by omega_using [hi, h])

/-! ## The function -/

/-- `vg_sm4_expand_key`'s contract on the machine. -/
def keyContract : Contract AArch64.isa where
  pre s := s.rd = [⟨s.gpr .x0, 16⟩] ∧ s.wr = [⟨s.gpr .x1, 128⟩]
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (s.gpr .x1) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

theorem expandKey_wp {s : State} (hp : keyContract.pre s) :
    WP isa expandKey s fun s' => (∀ r, r ∉ written → r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      keyContract.post s s' := by
  obtain ⟨hrd, hwr⟩ := hp
  have hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * i)) 4 := fun i hi =>
    ⟨⟨s.gpr .x0, 16⟩, by rw [hrd]; simp, VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have hwrite : ∀ i < 32, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 4 := fun i hi =>
    ⟨⟨s.gpr .x1, 128⟩, by rw [hwr]; simp, VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  change WP isa (.block (Impl.Tbl.AArch64.loadTable _ ++ quarterConstants ++
    (List.range 4).flatMap loadKeyWord ++ (List.range 32).flatMap keyRound)) s _
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadTable_ok s _) fun a ⟨atab, av, ag, am, ard, awr, asp⟩ => ?_
  obtain ⟨b, be, bc, bg, bm, brd, bwr, bsp, bv⟩ := quarterConstants_run a
  have btab : Table b := fun k hk => by
    rw [tbyte_congr' (fun j hj => bv _ (treg_ne8 j hj).2.2.2.2.1 (treg_ne8 j hj).2.2.2.2.2.1
      (treg_ne8 j hj).2.2.2.2.2.2.1) k hk]
    exact atab k hk
  have b0 : b.gpr .x0 = s.gpr .x0 := (bg _ (by decide)).trans (ag _ (by decide) (by decide))
  obtain ⟨c, ce, cw, cg, cm, crd, cwr, csp, cvec⟩ := keyLoads_run b 4 (Nat.le_refl _) (fun i hi => by
    rw [brd, bwr, ard, awr, b0]
    exact hread i hi)
  have cc : Constants c := by simpa only [Constants, cvec] using bc
  have ctab : Table c := by simpa only [Table, cvec] using btab
  have c1 : c.gpr .x1 = s.gpr .x1 :=
    (cg _ (by decide)).trans ((bg _ (by decide)).trans (ag _ (by decide) (by decide)))
  obtain ⟨d, de, dw, dc, dtab, dg, dmem, drd, dwr, dsp⟩ := keyRounds_run c 32 (Nat.le_refl _) cc ctab
    (fun i hi => by
      rw [cwr, bwr, awr, c1]
      exact hwrite i hi)
  refine WP.of_runBlock ⟨d, ?_, ?_, dsp.trans (csp.trans (bsp.trans asp)), ?_⟩
  · rw [VG.Interleave.runBlock_append, be, Option.bind_some, VG.Interleave.runBlock_append, ce,
      Option.bind_some, de]
  · intro r hr h15
    rw [dg r hr, cg r hr, bg r h15,
      ag r (fun he => hr (by simp [written, he])) (fun he => hr (by simp [written, he]))]
  · change Spec.Sm4.scheduleAt d.mem (s.gpr .x1) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .x0))
    rw [VG.Proof.Sm4.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    have hk : ∀ j < 4, words c j = keyInit (Spec.Sm4.blockAt s.mem (s.gpr .x0)) j := fun j hj => by
      rw [cw j hj, bm, am, b0, readBE_word _ _ j hj]
      rfl
    have hm := dmem i hi
    rw [c1, schedule_readW _ _ i hi, VG.Proof.Aes.getD_eq _ hi] at hm
    rw [hm, ksteps_congr (i + 1) _ _ hk (i % 4) (Nat.mod_lt _ (by decide)), ksteps_rk]

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hpost⟩ := expandKey_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp, Exec.preservedV he (by lit_decide)⟩, hpost⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hg _ (by decide) (by decide)

theorem keyTaint_agree (s₁ s₂ : State) (_ : keyContract.pre s₁) (_ : keyContract.pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1]) s₁ s₂ := by
  obtain ⟨h1, h2, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa keyContract.pre keyContract.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) keyTaint_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

/-- `vg_sm4_expand_key` meets its contract, with no stack. -/
theorem expandKey_verified : Verified AArch64.target expandKey (Spec.Sm4.expandKeyContract AArch64.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, keyContract, AArch64.abi,
      AArch64.argRegs] [keySat] using keySat)

end VG.Proof.Sm4.AArch64.Serial
