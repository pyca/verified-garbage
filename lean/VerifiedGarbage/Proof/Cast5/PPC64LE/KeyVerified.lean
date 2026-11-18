module

import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Cast5.PPC64LE
public import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Cast5.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Cast5.KeyMem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Ecb
meta import VerifiedGarbage.Impl.Cast5.PPC64LE
meta import VerifiedGarbage.Proof.Cast5.Table
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Cast5.KeyMem

/-! ### `Cast5.PPC64LE.Key`, which only this module used -/

section

/-! ### `Cast5.PPC64LE.KeyStep`, which this module and modules that import it used -/

section

/-! ### `Cast5.PPC64LE.KeySteps`, which this module and modules that import it used -/

section

/-!
# CAST5 key expansion on PPC64LE: the steps of a half

As on ARMv7 (`Proof/Cast5/Arm/KeySteps.lean`), for this
implementation's steps: it runs each half of §2.4 as 40 steps (`halfSteps`): for each
group of four lines, its extra lookups, then its lines, each with its extra
lookup from those (`lineE`). Run on the arrays, the subkeys so far and the
extra lookups (`KSt`), the steps of a half compute `halfImpl`
(`runSteps_half`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

/-- What the steps of key expansion work on: the arrays, the subkeys so far
and the group's extra lookups (`S8, S7, S6, S5` of its extra bytes). -/
structure KSt where
  xz : XZ
  ws : List Spec.Cast5.Word
  ex : Nat → Spec.Cast5.Word

/-- A line's value, its extra lookup taken from `ex`. -/
def lineE (xz : XZ) (ex : Nat → Spec.Cast5.Word) (l : Line) : Spec.Cast5.Word :=
  let v := Spec.Cast5.S8 (xz.get l.main.2.2.2) ^^^ Spec.Cast5.S7 (xz.get l.main.2.2.1) ^^^
    Spec.Cast5.S6 (xz.get l.main.2.1) ^^^ Spec.Cast5.S5 (xz.get l.main.1) ^^^ ex (8 - l.extra.1)
  match l.word with
  | some (a, q) => v ^^^ quadOf (xz.arr a) q
  | none => v

theorem lineE_eq {xz : XZ} {ex : Nat → Spec.Cast5.Word} {l : Line}
    (h : ex (8 - l.extra.1) = sbox l.extra.1 (xz.get l.extra.2)) : lineE xz ex l = lineVal xz l := by
  simp only [lineE, lineVal]
  rcases hw : l.word with _ | ⟨a, q⟩ <;> simp only [h]

/-- A step on the state of key expansion. -/
def stepRun : Step → KSt → KSt
  | .extras a b c d, k => { k with ex := exVal k.xz a b c d }
  | .line l (.quad a q), k => { k with xz := k.xz.put a q (lineE k.xz k.ex l) }
  | .line l (.key _), k => { k with ws := k.ws ++ [lineE k.xz k.ex l] }

/-- Steps in order. -/
def runSteps (ss : List Step) (k : KSt) : KSt := ss.foldl (fun k s => stepRun s k) k

theorem runSteps_append (a b : List Step) (k : KSt) : runSteps (a ++ b) k = runSteps b (runSteps a k) := by
  simp only [runSteps, List.foldl_append]

theorem runSteps_cons (s : Step) (ss : List Step) (k : KSt) : runSteps (s :: ss) k = runSteps ss (stepRun s k) := rfl

theorem runSteps_nil (k : KSt) : runSteps [] k = k := rfl

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

/-- The extra lookups of a group. -/
def exOf (xz : XZ) (ls : List Line) : Nat → Spec.Cast5.Word :=
  exVal xz (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)

theorem lineQ_run (a : Arr) {ls : List Line} (hg : GroupOk (some a) ls) (xz : XZ) (ws : List Spec.Cast5.Word)
    {j : Nat} (hj : j < 4) :
    stepRun (.line (ls.getD j default) (.quad a j)) ⟨runQ a ls j xz, ws, exOf xz ls⟩ =
      ⟨runQ a ls (j + 1) xz, ws, exOf xz ls⟩ := by
  obtain ⟨hok, hex, hna⟩ := hg.1 j hj
  have he := hok
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  simp only [stepRun, runQ_succ]
  rw [lineE_eq]
  rw [exOf, exVal_sbox _ _ he.1.1.2 he.1.2, hex, get_runQ _ _ _ _ fun e => hna (by rw [e])]

theorem lineK_run {ls : List Line} (hg : GroupOk none ls) (xz : XZ) (ws : List Spec.Cast5.Word) (b : Nat)
    {j : Nat} (hj : j < 4) :
    stepRun (.line (ls.getD j default) (.key (b + j))) ⟨xz, ws ++ (keys4 ls xz).take j, exOf xz ls⟩ =
      ⟨xz, ws ++ (keys4 ls xz).take (j + 1), exOf xz ls⟩ := by
  obtain ⟨hok, hex, _⟩ := hg.1 j hj
  have he := hok
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  simp only [stepRun]
  rw [lineE_eq (by rw [exOf, exVal_sbox _ _ he.1.1.2 he.1.2, hex]), take_keys4 _ _ hj, List.append_assoc]

theorem groupQ_run (a : Arr) {ls : List Line} (hg : GroupOk (some a) ls) (k : KSt) :
    runSteps (groupSteps ls (.quad a)) k = ⟨runQ a ls 4 k.xz, k.ws, exOf k.xz ls⟩ := by
  obtain ⟨xz, ws, ex⟩ := k
  simp only [groupSteps, range4, List.map_cons, List.map_nil, runSteps_cons, runSteps_nil]
  have e0 : stepRun (.extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ⟨xz, ws, ex⟩ =
      ⟨runQ a ls 0 xz, ws, exOf xz ls⟩ := rfl
  rw [e0, lineQ_run a hg xz ws (by decide), lineQ_run a hg xz ws (by decide), lineQ_run a hg xz ws (by decide),
    lineQ_run a hg xz ws (by decide)]

theorem groupK_run {ls : List Line} (hg : GroupOk none ls) (b : Nat) (k : KSt) :
    runSteps (groupSteps ls fun j => .key (b + j)) k = ⟨k.xz, k.ws ++ keys4 ls k.xz, exOf k.xz ls⟩ := by
  obtain ⟨xz, ws, ex⟩ := k
  simp only [groupSteps, range4, List.map_cons, List.map_nil, runSteps_cons, runSteps_nil]
  have e0 : stepRun (.extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ⟨xz, ws, ex⟩ =
      ⟨xz, ws ++ (keys4 ls xz).take 0, exOf xz ls⟩ := by
    simp only [stepRun, exOf, List.take_zero, List.append_nil]
  rw [e0, lineK_run hg xz ws b (j := 0) (by decide), lineK_run hg xz ws b (j := 1) (by decide),
    lineK_run hg xz ws b (j := 2) (by decide), lineK_run hg xz ws b (j := 3) (by decide)]
  rfl

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem key_zero : groupSteps aLines Store.key = groupSteps aLines fun j => .key (0 + j) := by
  simp only [Nat.zero_add]

/-- The steps of a half compute `halfImpl`. -/
theorem runSteps_half (k : KSt) :
    (runSteps halfSteps k).xz = (halfImpl k.xz).2 ∧ (runSteps halfSteps k).ws = k.ws ++ (halfImpl k.xz).1 := by
  unfold halfSteps
  rw [key_zero]
  simp only [runSteps_append, groupQ_run _ gZ, groupQ_run _ gX, groupK_run gA, groupK_run gB, groupK_run gC,
    groupK_run gD, runQ_z, runQ_x]
  exact ⟨rfl, by simp only [halfImpl, List.append_assoc]⟩

end VG.Proof.Cast5.PPC64LE

end

end

/-!
# CAST5 key expansion on PPC64LE: a step

`step` chooses the step's bytes by the step's number in `stp` (`sel_ok`),
gathers them into `r14`–`r17` (`gather_ok`), scans `VG_CAST5_S5678`, and
chooses what to do with the four values (`postE_ok`, `postL_ok`): the step of
the spec's `stepRun`.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

/-! ## The chain of comparisons -/

/-- The code chosen by the step's number `j` in `stp`: `cs[j - i]`. -/
theorem sel_ok (cs : List (List Instr)) (i : Nat) {s : State} {j : Nat} (hij : i ≤ j) (hj : j < i + cs.length)
    (hlen : i + cs.length ≤ 2 ^ 15) (h2 : s.gpr stp = BitVec.ofNat 64 j) {Q : State → Prop}
    (hQ : ∀ u : State, Keep [tmp] s u → u.mem = s.mem → WP isa (.block (cs.getD (j - i) [])) u Q) :
    WP isa (sel cs i) s Q := by
  induction cs generalizing i s with
  | nil => simp at hj; omega_arith
  | cons c cs ih =>
    unfold sel
    simp only [List.length_cons] at hj hlen
    refine WP.seq (wp_subi (by decide) (by omega_arith) fun u hu => wp_nil ?_)
    have uk : Keep [tmp] s u := hu.keep
    have ev : isa.eval (.zero .d tmp) u = some (decide (j = i)) := by
      rw [eval_zero, hu.gpr, h2]
      congr 1
      by_cases e : j = i
      · subst e; simp
      · rw [decide_eq_false e]
        have : BitVec.ofNat 64 j - BitVec.ofNat 64 i ≠ 0 := fun h0 => e (by
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
          simp at this; omega_arith)
        simpa using this
    by_cases e : j = i
    · subst e
      refine WP.ite true (by rw [ev, decide_eq_true rfl]) (fun _ => ?_) (fun h => absurd h (by decide))
      have := hQ u uk hu.mem
      rwa [Nat.sub_self, List.getD_cons_zero] at this
    · refine WP.ite false (by rw [ev, decide_eq_false e]) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine ih (i + 1) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hu.other _ (by decide), h2])
        fun v vk vm => ?_
      have := hQ v ((uk.trans vk).mono (by decide)) (vm.trans hu.mem)
      rwa [show j - i = (j - (i + 1)) + 1 by omega_arith, List.getD_cons_succ] at this

/-! ## The state of key expansion -/

/-- The registers a step writes. -/
def stepRegs : List Reg := [tmp, wd, num, ep, .r18, .r19, .r20, .r21, .r14, .r15, .r16, .r17, vI, stp]

/-- The state of key expansion from the memory `m0`: the working space at
`cb` in `wkK`, the schedule at `kb`, the arrays, subkeys and extra lookups
of `k` in memory; zero in `r0`; and the table `VG_CAST5_S5678` at `T` in
`tbl`, readable, held in `m0` and apart from the working space's first 64
bytes and the schedule. -/
structure KS (m0 : Mem) (cb kb T : Addr) (s : State) (k : KSt) : Prop where
  wk : s.gpr wkK = cb
  mem : KMem m0 s.mem cb kb k.xz k.ws
  ex : ∀ i < 4, s.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k.ex i
  len : k.ws.length ≤ 32
  cfit : cb.toNat + 256 ≤ 2 ^ 64
  kfit : kb.toNat + 128 ≤ 2 ^ 64
  scr : (⟨cb, 256⟩ : Region) ∈ s.wr
  sch : (⟨kb, 128⟩ : Region) ∈ s.wr
  dKS : Region.Disjoint ⟨kb, 128⟩ ⟨cb, 256⟩
  zero : s.gpr .r0 = 0
  tblR : s.gpr tbl = T
  trd : (⟨T, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held0 : Held m0 T s5678
  dTS : Region.Disjoint ⟨T, 4096⟩ ⟨cb, 64⟩
  dTK : Region.Disjoint ⟨T, 4096⟩ ⟨kb, 128⟩

theorem s5678_len : 8 * s5678.length = 4096 := by rw [s5678, table_length]

section
variable {m0 : Mem} {cb kb T : Addr} {s : State} {k : KSt} (h : KS m0 cb kb T s k)
include h

theorem KS.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (cb + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by have := h.cfit; omega_arith)⟩

theorem KS.inS' {off w : Nat} (hw : off + w ≤ 256) : InRegions (s.rd ++ s.wr) (cb + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by have := h.cfit; omega_arith)⟩

theorem KS.dKS64 : Region.Disjoint ⟨kb, 128⟩ ⟨cb, 64⟩ :=
  h.dKS.sub_right (Region.sub_prefix (by decide))

/-- The same state, later: other registers and memory. -/
theorem KS.update {u : State} {k' : KSt} {rs : List Reg} (hk : Keep rs s u)
    (hm : KMem m0 u.mem cb kb k'.xz k'.ws)
    (he : ∀ i < 4, u.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k'.ex i)
    (hl : k'.ws.length ≤ 32) (hrs : wkK ∉ rs ∧ Reg.r0 ∉ rs ∧ tbl ∉ rs := by decide) : KS m0 cb kb T u k' :=
  ⟨(hk.gpr hrs.1).trans h.wk, hm, he, hl, h.cfit, h.kfit, by rw [hk.2.2]; exact h.scr,
    by rw [hk.2.2]; exact h.sch, h.dKS, (hk.gpr hrs.2.1).trans h.zero, (hk.gpr hrs.2.2).trans h.tblR,
    by rw [hk.2.1, hk.2.2]; exact h.trd, h.held0, h.dTS, h.dTK⟩

/-- The table, still held. -/
theorem KS.held : Held s.mem T s5678 := by
  refine held_frame h.mem.fr (fun r hr => ?_) (by rw [s5678_len]; decide) h.held0
  rw [s5678_len]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTS
  · exact h.dTK

end

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q + 1 ≤ 48 := by
  obtain ⟨a, i⟩ := q
  have := off_lt a
  simp only [srcOff] at hq ⊢
  omega_arith

/-! ## Gathering the bytes -/

theorem gather_ok {m0 : Mem} {cb kb T : Addr} {s : State} {k : KSt} (h : KS m0 cb kb T s k)
    {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16) (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.gpr .r14 = (k.xz.get d).setWidth 64 ∧ u.gpr .r15 = (k.xz.get c).setWidth 64 ∧
      u.gpr .r16 = (k.xz.get b).setWidth 64 ∧ u.gpr .r17 = (k.xz.get a).setWidth 64 ∧
      Keep [.r14, .r15, .r16, .r17] s u ∧ u.mem = s.mem := by
  have ia := h.inS' (off := srcOff a) (w := 1) (by have := srcOff_lt ha; omega_arith)
  have ib := h.inS' (off := srcOff b) (w := 1) (by have := srcOff_lt hb; omega_arith)
  have ic := h.inS' (off := srcOff c) (w := 1) (by have := srcOff_lt hc; omega_arith)
  have id := h.inS' (off := srcOff d) (w := 1) (by have := srcOff_lt hd; omega_arith)
  have xa := h.mem.xz.pos ha
  have xb := h.mem.xz.pos hb
  have xc := h.mem.xz.pos hc
  have xd := h.mem.xz.pos hd
  have oa : srcOff a < 2 ^ 15 := by have := srcOff_lt ha; omega_arith
  have ob : srcOff b < 2 ^ 15 := by have := srcOff_lt hb; omega_arith
  have oc : srcOff c < 2 ^ 15 := by have := srcOff_lt hc; omega_arith
  have od : srcOff d < 2 ^ 15 := by have := srcOff_lt hd; omega_arith
  have hw := h.wk
  unfold gather
  c5run [hw, ia, ib, ic, id, xa, xb, xc, xd, oa, ob, oc, od]
  refine ⟨fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## What a step does with the values -/

theorem ex_off {i : Nat} (hi : i < 4) : extraOff + 4 * i + 4 ≤ 64 := by unfold extraOff; omega_arith

/-- The extra lookups of a group to their slots. -/
theorem postE_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) (a b c d : Pos)
    (v : Nat → Spec.Cast5.Word) (hv : ∀ i < 4, lo (u.gpr (accReg i)) = v i) :
    WP isa (.block (Step.extras a b c d).post) u fun w =>
      KS m0 cb kb T w { k with ex := v } ∧ Keep [] u w := by
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have v0 : lo (u.gpr .r18) = v 0 := hv 0 (by decide)
  have v1 : lo (u.gpr .r19) = v 1 := hv 1 (by decide)
  have v2 : lo (u.gpr .r20) = v 2 := hv 2 (by decide)
  have v3 : lo (u.gpr .r21) = v 3 := hv 3 (by decide)
  have hw := h.wk
  simp only [Step.post]
  unfold extraOff
  c5run [hw, inS, v0, v1, v2, v3]
  have dKS := h.dKS64
  have hl := h.len
  refine ⟨h.update (Keep.refl [] _) ?_ (fun i hi => ?_) hl, Keep.refl _ _⟩
  · exact (((h.mem.write dKS hl _ (by decide) (by decide)).write dKS hl _ (by decide) (by decide)).write dKS hl _
      (by decide) (by decide)).write dKS hl _ (by decide) (by decide)
  · simp only [extraOff]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd] <;>
    repeat (first
      | rw [Mem.readW_writeW_self32]
      | rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)])

/-- The XORs of a line's lookups and its extra lookup, into `vI`. -/
theorem lineHead_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) {e : Nat}
    (he : 5 ≤ e ∧ e ≤ 8) :
    WP isa (.block [.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2),
      .logic .xor vI vI (accReg 3), .load .w tmp wkK (extraOff + 4 * (8 - e)), .logic .xor vI vI tmp]) u fun w =>
      lo (w.gpr vI) = lo (u.gpr .r18) ^^^ lo (u.gpr .r19) ^^^ lo (u.gpr .r20) ^^^ lo (u.gpr .r21) ^^^
        k.ex (8 - e) ∧ Keep [vI, tmp] u w ∧ w.mem = u.mem := by
  have ho : extraOff + 4 * (8 - e) < 2 ^ 15 := by unfold extraOff; omega_arith
  have hin := h.inS' (off := extraOff + 4 * (8 - e)) (w := 4) (by unfold extraOff; omega_arith)
  have hx := h.ex (8 - e) (by omega_arith)
  have hw := h.wk
  c5run [hw, hin, hx, ho]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [lo_xor, lo_ext]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]

/-- The quadruple a line XORs in, if any. -/
def wordCode : Option (Arr × Nat) → List Instr
  | some (a, q) => [.li wd (off a + 4 * q), .loadRev .w tmp wkK wd, .logic .xor vI vI tmp]
  | none => []

/-- `v` with the quadruple `wd` of the arrays XORed in, if any. -/
def withQuad (xz : XZ) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ quadOf (xz.arr a) q
  | none => v

theorem wordCode_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k)
    (w : Option (Arr × Nat)) (hq : ∀ a q, w = some (a, q) → q < 4) :
    WP isa (.block (wordCode w)) u fun v =>
      lo (v.gpr vI) = withQuad k.xz (lo (u.gpr vI)) w ∧ Keep [vI, tmp, wd] u v ∧ v.mem = u.mem := by
  cases w with
  | none => exact wp_nil ⟨rfl, Keep.refl _ _, rfl⟩
  | some aq =>
    obtain ⟨a, q⟩ := aq
    have hq4 := hq a q rfl
    have := off_lt a
    have ho : off a + 4 * q < 2 ^ 15 := by omega_arith
    have hin := h.inS' (off := off a + 4 * q) (w := 4) (by omega_arith)
    have hx := h.mem.xz.quad a hq4
    have hw := h.wk
    unfold wordCode
    c5run [hw, hin, ho, rev32_eq]
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
    · simp only [lo_xor, lo_ext, hx, withQuad]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- Where a line's value goes. -/
def storeCode : Store → List Instr
  | .quad a q => [.li wd (off a + 4 * q), .storeRev .w vI wkK wd]
  | .key k => [.store .w vI out (4 * k)]

theorem post_line (l : Impl.Cast5.Line) (st : Store) :
    (Step.line l st).post = ([.logic .xor vI (accReg 0) (accReg 1), .logic .xor vI vI (accReg 2),
      .logic .xor vI vI (accReg 3), .load .w tmp wkK (extraOff + 4 * (8 - l.extra.1)),
      .logic .xor vI vI tmp] : List Instr) ++ wordCode l.word ++ storeCode st := by
  obtain ⟨main, extra, word⟩ := l
  rcases word with _ | ⟨a, q⟩ <;> cases st <;> rfl

theorem storeQuad_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) (a : Arr)
    {q : Nat} (hq : q < 4) {v : Spec.Cast5.Word} (h0 : lo (u.gpr vI) = v) :
    WP isa (.block (storeCode (.quad a q))) u fun w =>
      KS m0 cb kb T w { k with xz := k.xz.put a q v } ∧ Keep [wd] u w := by
  have := off_lt a
  have := off_ge a
  have ho : off a + 4 * q < 2 ^ 15 := by omega_arith
  have hin := h.inS (off := off a + 4 * q) (w := 4) (by omega_arith)
  have hw := h.wk
  unfold storeCode
  c5run [hw, hin, ho, h0, rev32_eq]
  refine ⟨h.update (rs := [wd]) ⟨fun r hr => ?_, rfl, rfl⟩ (h.mem.quad h.dKS64 h.len a hq v) (fun i hi => ?_)
    h.len, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [List.mem_singleton] at hr; exact ite_eq_right hr
  rotate_left
  · simp only [List.mem_singleton] at hr; exact ite_eq_right hr
  rw [Mem.readW_writeW_sep (Offset.sep _ (d := extraOff + 4 * i) (n := 32 / 8) (e := off a + 4 * q) (k := 32 / 8)
    (by unfold extraOff; omega_arith) (by unfold extraOff; omega_arith) (by omega_arith)) (by decide)]
  exact h.ex i hi

theorem storeKey_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k) {j hh : Nat}
    (hj : j < 16) (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen : k.ws.length = 16 * hh + j)
    (hl : k.ws.length < 32) {v : Spec.Cast5.Word} (h0 : lo (u.gpr vI) = v) :
    WP isa (.block (storeCode (.key j))) u fun w =>
      KS m0 cb kb T w { k with ws := k.ws ++ [v] } ∧ Keep [] u w := by
  have hkf := h.kfit
  have ea : u.gpr out + BitVec.ofNat 64 (4 * j) = kb + BitVec.ofNat 64 (4 * k.ws.length) := by
    rw [hout, Offset.add_add, hlen]; congr 2; omega_arith
  have hin : InRegions u.wr (kb + BitVec.ofNat 64 (4 * k.ws.length)) 4 :=
    ⟨_, h.sch, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold storeCode
  refine wp_stw (by decide) (by omega_arith) ea hin fun w hw => wp_nil ?_
  have hk : Keep [] u w := ⟨fun r _ => by rw [hw.gpr], hw.rd, hw.wr⟩
  have h0' : (u.gpr vI).setWidth 32 = v := h0
  rw [h0'] at hw
  refine ⟨h.update hk (by rw [hw.mem]; exact h.mem.key h.dKS64 hl v) (fun i hi => ?_) (by simp; omega_arith), hk⟩
  rw [hw.mem, Mem.readW_writeW_sep (h.dKS.symm.sep (Offset.contains_base _ (by have := ex_off hi; omega_arith)
      (by unfold extraOff; omega_arith))
    (Offset.contains_base _ (by omega_arith) (by omega_arith))) (by decide)]
  exact h.ex i hi

/-- What a step needs to be run by the code: bytes of `x` and `z`, a line
`lineOk`, a quadruple of four, a subkey of the half's sixteen. -/
def stepOk : Step → Bool
  | .extras a b c d => a.2 < 16 && b.2 < 16 && c.2 < 16 && d.2 < 16
  | .line l (.quad _ q) => lineOk l && q < 4
  | .line l (.key j) => lineOk l && j < 16

/-- A line, after the scan of its bytes: its value, then its store. -/
theorem postL_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k : KSt} (h : KS m0 cb kb T u k)
    {l : Impl.Cast5.Line} {st : Store} (hok : stepOk (.line l st) = true)
    (h8 : lo (u.gpr .r18) = Spec.Cast5.S8 (k.xz.get l.main.2.2.2))
    (h9 : lo (u.gpr .r19) = Spec.Cast5.S7 (k.xz.get l.main.2.2.1))
    (h10 : lo (u.gpr .r20) = Spec.Cast5.S6 (k.xz.get l.main.2.1))
    (h11 : lo (u.gpr .r21) = Spec.Cast5.S5 (k.xz.get l.main.1))
    {hh : Nat} (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh))
    (hkey : ∀ j, st = .key j → k.ws.length = 16 * hh + j ∧ k.ws.length < 32) :
    WP isa (.block (Step.line l st).post) u fun w =>
      KS m0 cb kb T w (stepRun (.line l st) k) ∧ Keep [vI, tmp, wd] u w := by
  have hl : lineOk l = true := by cases st <;> simp only [stepOk, Bool.and_eq_true] at hok <;> exact hok.1
  have he := hl
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  have hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q hw
    have := he.2
    rw [hw] at this
    simpa using this
  rw [post_line, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (lineHead_ok h ⟨he.1.1.2, he.1.2⟩) fun v ⟨v0, vk, vm⟩ => ?_
  have hv : KS m0 cb kb T v k := h.update vk (by rw [vm]; exact h.mem)
    (fun i hi => by rw [vm]; exact h.ex i hi) h.len
  refine WP.mono (wordCode_ok hv l.word hq) fun w ⟨w0, wk, wm⟩ => ?_
  have hw : KS m0 cb kb T w k := hv.update wk (by rw [wm]; exact hv.mem)
    (fun i hi => by rw [wm]; exact hv.ex i hi) hv.len
  have wv : lo (w.gpr vI) = lineE k.xz k.ex l := by
    rw [w0, v0, h8, h9, h10, h11]
    unfold lineE
    clear hq he hok hl hkey h8 h9 h10 h11
    obtain ⟨main, extra, word⟩ := l
    rcases word with _ | ⟨a, q⟩ <;> rfl
  have kuw := vk.trans wk
  cases st with
  | quad a q =>
    have hq4 : q < 4 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    exact WP.mono (storeQuad_ok hw a hq4 wv) fun x ⟨hx, xk⟩ => ⟨hx, (kuw.trans xk).mono (by decide)⟩
  | key j =>
    have hj : j < 16 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    obtain ⟨hlen, hl32⟩ := hkey j rfl
    exact WP.mono (storeKey_ok hw hj (by rw [kuw.gpr (by decide)]; exact hout) hlen hl32 wv)
      fun x ⟨hx, xk⟩ => ⟨hx, (kuw.trans xk).mono (by decide)⟩

end VG.Proof.Cast5.PPC64LE

end

end

/-! ### `Cast5.PPC64LE.KeyHalf`, which only this module used -/

section

/-!
# CAST5 key expansion on PPC64LE: the steps of a half, run

`keyStep_ok`: step `j` of a half (its number in `stp`) is the spec's
`stepRun`; `half_ok`: the 40 steps of a half compute `halfImpl`
(`runSteps_half`), writing its sixteen subkeys from `out`.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

/-! ## Facts about the steps, by evaluation -/

def isKey : Step → Bool
  | .line _ (.key _) => true
  | _ => false

/-- The number of subkey steps. -/
def countKeys (ss : List Step) : Nat := (ss.filter isKey).length

theorem ws_length : ∀ (ss : List Step) (k : KSt), (runSteps ss k).ws.length = k.ws.length + countKeys ss
  | [], _ => rfl
  | s :: ss, k => by
    rw [runSteps_cons, ws_length ss]
    unfold countKeys
    rcases s with ⟨⟩ | ⟨l, ⟨⟩ | ⟨⟩⟩ <;> simp [stepRun, isKey, List.filter_cons] <;> omega_arith

/-- The bytes a step looks up: `S5[a], S6[b], S7[c], S8[d]`. -/
def stepPos : Step → Pos × Pos × Pos × Pos
  | .extras a b c d => (a, b, c, d)
  | .line l _ => l.main

theorem Step.gather_eq (st : Step) :
    st.gather = gather (stepPos st).1 (stepPos st).2.1 (stepPos st).2.2.1 (stepPos st).2.2.2 := by
  cases st <;> rfl

/-- What each step needs, and the place of each subkey, checked by evaluation. -/
def stepsOk : Bool :=
  halfSteps.length == 40 && (List.range 40).all fun j =>
    let st := halfSteps.getD j default
    stepOk st && (stepPos st).1.2 < 16 && (stepPos st).2.1.2 < 16 && (stepPos st).2.2.1.2 < 16 &&
      (stepPos st).2.2.2.2 < 16 &&
      match st with
      | .line _ (.key jj) => countKeys (halfSteps.take j) == jj
      | _ => true

theorem stepsOk_true : stepsOk = true := by decide +kernel

theorem halfSteps_length : halfSteps.length = 40 := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem step_facts {j : Nat} (hj : j < 40) :
    stepOk (halfSteps.getD j default) = true ∧ (stepPos (halfSteps.getD j default)).1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.1.2 < 16 ∧ (stepPos (halfSteps.getD j default)).2.2.1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.2.2.2 < 16 ∧
      (∀ l jj, halfSteps.getD j default = .line l (.key jj) → countKeys (halfSteps.take j) = jj) := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  obtain h := this.2 j hj
  simp only [decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun l jj e => ?_⟩
  rw [e] at h6
  simpa using h6

theorem take_succ_steps {j : Nat} (hj : j < 40) :
    halfSteps.take (j + 1) = halfSteps.take j ++ [halfSteps.getD j default] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem getD_map_steps {α : Type} (f : Step → α) (d : α) {j : Nat} (hj : j < 40) :
    (halfSteps.map f).getD j d = f (halfSteps.getD j default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem ofNat_setWidth8 (x : Byte) : BitVec.ofNat 8 (x.setWidth 64).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

theorem setWidth8_lt (x : Byte) : (x.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega_arith

/-! ## A step -/

theorem keyStep_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {j hh : Nat} (hj : j < 40)
    (h : KS m0 cb kb T u (runSteps (halfSteps.take j) k0)) (h2 : u.gpr stp = BitVec.ofNat 64 j)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa Impl.Cast5.PPC64LE.step u fun v => KS m0 cb kb T v (runSteps (halfSteps.take (j + 1)) k0) ∧
      v.gpr stp = BitVec.ofNat 64 (j + 1) ∧ v.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧
      Keep stepRegs u v := by
  obtain ⟨hok, p1, p2, p3, p4, hkeys⟩ := step_facts hj
  obtain ⟨st, hst⟩ : ∃ st, halfSteps.getD j default = st := ⟨_, rfl⟩
  rw [hst] at hok p1 p2 p3 p4 hkeys
  obtain ⟨kj, hkj⟩ : ∃ kj, runSteps (halfSteps.take j) k0 = kj := ⟨_, rfl⟩
  rw [hkj] at h
  obtain hnext : runSteps (halfSteps.take (j + 1)) k0 = stepRun st kj := by
    rw [take_succ_steps hj, runSteps_append, hkj, hst]; rfl
  rw [hnext]
  obtain hlen40 : 0 + (halfSteps.map Step.gather).length ≤ 2 ^ 15 := by simp [halfSteps_length]
  unfold Impl.Cast5.PPC64LE.step
  -- The step's bytes.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) hlen40 h2
    fun u1 k1 m1 => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst, Step.gather_eq]
  obtain h1 : KS m0 cb kb T u1 kj := h.update k1 (by rw [m1]; exact h.mem) (fun i hi => by rw [m1]; exact h.ex i hi)
    h.len
  refine WP.mono (gather_ok h1 p1 p2 p3 p4) fun v ⟨v4, v5, v6, v7, vk, vm⟩ => ?_
  obtain hv : KS m0 cb kb T v kj := h1.update vk (by rw [vm]; exact h1.mem)
    (fun i hi => by rw [vm]; exact h1.ex i hi) h1.len
  -- The scan.
  obtain hidx : ∀ i < 4, (v.gpr (idxReg i)).toNat < 256 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show (v.gpr .r14).toNat < 256; rw [v4]; exact setWidth8_lt _
    · show (v.gpr .r15).toNat < 256; rw [v5]; exact setWidth8_lt _
    · show (v.gpr .r16).toNat < 256; rw [v6]; exact setWidth8_lt _
    · show (v.gpr .r17).toNat < 256; rw [v7]; exact setWidth8_lt _
  obtain sp : ScanPre v := ⟨hidx, hv.zero, by rw [hv.tblR]; exact hv.trd⟩
  refine WP.seq (WP.mono (scan_ok v sp) fun w ⟨wa, wk, wm⟩ => ?_)
  obtain hw : KS m0 cb kb T w kj := hv.update wk (by rw [wm]; exact hv.mem) (fun i hi => by rw [wm]; exact hv.ex i hi)
    hv.len
  have ent (i : Nat) (hi : i < 4) (x : Byte) (hx : v.gpr (idxReg i) = x.setWidth 64) :
      lo (w.gpr (accReg i)) = tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
        (x.setWidth 64).toNat i := by
    rw [wa i hi, hx, lo_ext, hv.tblR]; exact ent_table hv.held (setWidth8_lt _) hi
  obtain a0 : lo (w.gpr .r18) = Spec.Cast5.S8 (kj.xz.get (stepPos st).2.2.2) := by
    rw [show Reg.r18 = accReg 0 from rfl, ent 0 (by decide) _ v4]; simp only [tableEnt, ofNat_setWidth8]
  obtain a1 : lo (w.gpr .r19) = Spec.Cast5.S7 (kj.xz.get (stepPos st).2.2.1) := by
    rw [show Reg.r19 = accReg 1 from rfl, ent 1 (by decide) _ v5]; simp only [tableEnt, ofNat_setWidth8]
  obtain a2 : lo (w.gpr .r20) = Spec.Cast5.S6 (kj.xz.get (stepPos st).2.1) := by
    rw [show Reg.r20 = accReg 2 from rfl, ent 2 (by decide) _ v6]; simp only [tableEnt, ofNat_setWidth8]
  obtain a3 : lo (w.gpr .r21) = Spec.Cast5.S5 (kj.xz.get (stepPos st).1) := by
    rw [show Reg.r21 = accReg 3 from rfl, ent 3 (by decide) _ v7]; simp only [tableEnt, ofNat_setWidth8]
  obtain kuw' := (k1.trans vk).trans wk
  obtain kuw : Keep stepRegs u w := kuw'.mono (by decide)
  obtain w2 : w.gpr stp = BitVec.ofNat 64 j := by rw [kuw'.gpr (by decide), h2]
  obtain wout : w.gpr out = kb + BitVec.ofNat 64 (64 * hh) := by rw [kuw'.gpr (by decide), hout]
  -- What it does with the values.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) (by simp [halfSteps_length]) w2
    fun x kx mx => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst]
  obtain hx : KS m0 cb kb T x kj := hw.update kx (by rw [mx]; exact hw.mem) (fun i hi => by rw [mx]; exact hw.ex i hi)
    hw.len
  have gx (q : Reg) (hq : q ≠ tmp) : x.gpr q = w.gpr q := kx.gpr (by simpa using hq)
  have tail (y : State) (hy : KS m0 cb kb T y (stepRun st kj)) (ky : Keep stepRegs u y)
      (y2 : y.gpr stp = BitVec.ofNat 64 j) :
      WP isa (.block [.addi stp stp 1, .subi tmp stp 40]) y fun z =>
        KS m0 cb kb T z (stepRun st kj) ∧ z.gpr stp = BitVec.ofNat 64 (j + 1) ∧
          z.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧ Keep stepRegs u z := by
    refine wp_addi (by decide) (by decide) fun z₁ h₁ => wp_subi (by decide) (by decide) fun z₂ h₂ => wp_nil ?_
    obtain kz : Keep [stp, tmp] y z₂ := (h₁.keep.trans h₂.keep).mono (by decide)
    refine ⟨hy.update kz (by rw [h₂.mem, h₁.mem]; exact hy.mem) (fun i hi => by rw [h₂.mem, h₁.mem]; exact hy.ex i hi)
      hy.len, ?_, ?_, (ky.trans kz).mono (by decide)⟩
    · rw [h₂.other _ (by decide), h₁.gpr, y2, BitVec.ofNat_add]
    · rw [h₂.gpr, h₁.gpr, y2, BitVec.ofNat_add]
  cases st with
  | extras a b c d =>
    refine WP.mono (postE_ok hx a b c d (exVal kj.xz a b c d) fun i hi => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    · rw [gx _ (by unfold accReg; split <;> decide)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
  | line l store =>
    refine WP.mono (postL_ok hx hok (by rw [gx _ (by decide)]; exact a0) (by rw [gx _ (by decide)]; exact a1)
      (by rw [gx _ (by decide)]; exact a2) (by rw [gx _ (by decide)]; exact a3)
      (by rw [gx _ (by decide)]; exact wout) fun jj e => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    subst e
    obtain hc := hkeys l jj rfl
    obtain hl := ws_length (halfSteps.take j) k0
    rw [hkj] at hl
    obtain hlim : countKeys (halfSteps.take j) < 16 := by
      have := hok; simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    exact ⟨by rw [hl, hc, hlen0], by rw [hl, hlen0]; omega_arith⟩

/-! ## A half -/

/-- The registers a half writes. -/
def halfRegs : List Reg := stepRegs ++ [out, hlv]

theorem take_steps_40 : halfSteps.take 40 = halfSteps := by
  rw [List.take_of_length_le (by rw [halfSteps_length])]

theorem tmp_step_ne {j : Nat} (hj : j < 40) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 != 0) = !decide (j + 1 = 40) := by
  by_cases he : j + 1 = 40
  · rw [he]; rfl
  · rw [decide_eq_false he]
    have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      simp at this; omega_using [hj, he, this]
    simpa using this

theorem half_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {hh : Nat} (h : KS m0 cb kb T u k0)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa half u fun v => ∃ k, KS m0 cb kb T v k ∧ k.xz = (halfImpl k0.xz).2 ∧
      k.ws = k0.ws ++ (halfImpl k0.xz).1 ∧ v.gpr out = kb + BitVec.ofNat 64 (64 * (hh + 1)) ∧
      v.gpr hlv = u.gpr hlv - 1#64 ∧ Keep halfRegs u v := by
  unfold half
  refine WP.seq (wp_li (by decide) fun u0 hu0 => wp_nil ?_)
  obtain k0u : Keep stepRegs u u0 := hu0.keep.mono (by decide)
  obtain h0 : KS m0 cb kb T u0 (runSteps (halfSteps.take 0) k0) :=
    h.update hu0.keep (by rw [hu0.mem]; exact h.mem) (fun i hi => by rw [hu0.mem]; exact h.ex i hi) h.len
  obtain loop : WP isa (.loop Impl.Cast5.PPC64LE.step (.nonzero .d tmp)) u0
      (fun v => KS m0 cb kb T v (runSteps halfSteps k0) ∧ Keep stepRegs u v) := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = 40 - j ∧ j < 40 ∧
      KS m0 cb kb T v (runSteps (halfSteps.take j) k0) ∧ v.gpr stp = BitVec.ofNat 64 j ∧ Keep stepRegs u v)
      ?_ 40 u0 ⟨0, rfl, by decide, h0, hu0.gpr, k0u⟩
    rintro m v ⟨j, rfl, hj, hv, v2, kv⟩
    refine WP.mono (keyStep_ok hj hv v2 (by rw [kv.gpr (by decide), hout]) hlen0 hhh)
      fun w ⟨hw, w2, wt, kw⟩ => ?_
    obtain ev : isa.eval (.nonzero .d tmp) w = some (!decide (j + 1 = 40)) := by
      rw [eval_nonzero, wt, tmp_step_ne hj]
    by_cases he : j + 1 = 40
    · refine .inl ⟨by rw [ev, decide_eq_true he]; rfl, ?_, (kv.trans kw).mono (by decide)⟩
      rw [he, take_steps_40] at hw; exact hw
    · exact .inr ⟨by rw [ev, decide_eq_false he]; rfl, 40 - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, hw, w2, (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono loop fun v ⟨hv, kv⟩ => ?_)
  refine wp_addi (by decide) (by decide) fun v₁ h₁ => wp_subi (by decide) (by decide) fun v₂ h₂ => wp_nil ?_
  obtain ⟨hx, hw⟩ := runSteps_half k0
  obtain k12 : Keep [out, hlv] v v₂ := (h₁.keep.trans h₂.keep).mono (by decide)
  refine ⟨runSteps halfSteps k0, hv.update k12 (by rw [h₂.mem, h₁.mem]; exact hv.mem)
    (fun i hi => by rw [h₂.mem, h₁.mem]; exact hv.ex i hi) hv.len, hx, hw, ?_, ?_, (kv.trans k12).mono (by decide)⟩
  · rw [h₂.other _ (by decide), h₁.gpr, kv.gpr (by decide), hout, Offset.add_add, Nat.mul_succ]
  · rw [h₂.gpr, h₁.other _ (by decide), kv.gpr (by decide)]

end VG.Proof.Cast5.PPC64LE

end

end


/-!
# CAST5 key expansion on PPC64LE

`expandKey` saves `LR` and the callee-saved registers in the working space,
pads the key with zeros into `x` (§2.5), runs both halves of §2.4
(`half_ok`) and restores the registers (`key_wp`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

/-! ## The key, padded -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the first 64 bytes of the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_dword (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 64)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) {cb : Addr} (hc : s.gpr wkK = cb) (h0 : s.gpr .r0 = 0)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (cb + BitVec.ofNat 64 off) w) (key : Addr) :
    WP isa (.block [.store .d zero wkK xOff, .store .d zero wkK (xOff + 8), .addi dst wkK xOff]) s fun u =>
      CInv s.mem key cb 0 u.mem ∧ u.gpr dst = cb + BitVec.ofNat 64 16 ∧ Keep [dst] s u := by
  obtain i16 := hin (off := 16) (w := 8) (by decide)
  obtain i24 := hin (off := 24) (w := 8) (by decide)
  unfold xOff
  refine wp_std (a := cb + BitVec.ofNat 64 16) (by decide) (by decide) (by rw [hc]) i16 fun u₁ h₁ => ?_
  refine wp_std (a := cb + BitVec.ofNat 64 24) (by decide) (by decide) (by rw [h₁.gpr]; exact congrArg (· + _) hc)
    (by rw [h₁.wr]; exact i24) fun u₂ h₂ => ?_
  refine wp_addi (by decide) (by decide) fun u₃ h₃ => wp_nil ?_
  obtain mem : u₃.mem = (s.mem.writeW (cb + BitVec.ofNat 64 16) (0 : BitVec 64)).writeW
      (cb + BitVec.ofNat 64 24) (0 : BitVec 64) := by
    rw [h₃.mem, h₂.mem, h₁.mem, h₁.gpr, h0]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, by rw [h₃.gpr, h₂.gpr, h₁.gpr, hc], ?_⟩
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith)]
    repeat' split
    all_goals first | rfl | omega_arith
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith),
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · rw [mem]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide)))
  · exact ⟨fun r hr => by rw [h₃.other _ (by simpa using hr), h₂.gpr, h₁.gpr], by rw [h₃.rd, h₂.rd, h₁.rd],
      by rw [h₃.wr, h₂.wr, h₁.wr]⟩

theorem copyStep_ok (u : State) {m0 : Mem} {kp cb : Addr} {j : Nat} (hj : j < 16)
    (hI : CInv m0 kp cb j u.mem)
    (h0 : u.gpr key = kp + BitVec.ofNat 64 j) (h3 : u.gpr dst = cb + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (kp + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (cb + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (kp + BitVec.ofNat 64 j) = m0 (kp + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 kp cb (j + 1) v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 (j + 1) ∧
      v.gpr dst = cb + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr klen = u.gpr klen - 1#64 ∧
      Keep [tmp, key, dst, klen] u v := by
  unfold copyStep
  c5run [hr, hw, hk, h0, h3]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [byte_write _ _ _ (by omega_arith) (by omega_arith)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_arith⟩, ite_eq_left (by omega_arith), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_arith), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hl, ite_eq_right (by omega_arith)]
  · rw [byte_write _ _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    exact hI.z i hi
  · exact hI.fr.write List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]
  · rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add, Nat.add_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The whole function -/

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, the working space apart from both, none wrapping
around, a valid key length; and the table `VG_CAST5_S5678`, readable and
apart from the schedule and the working space. -/
structure KeyPre (s : State) : Prop where
  key : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  sch : (⟨s.gpr .r5, 128⟩ : Region) ∈ s.wr
  Kfit : (s.gpr .r5).toNat + 128 ≤ 2 ^ 64
  scr : (⟨s.gpr .r6, 256⟩ : Region) ∈ s.wr
  sfit : (s.gpr .r6).toNat + 256 ≤ 2 ^ 64
  keyScr : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  schScr : (⟨s.gpr .r5, 128⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  valid : Spec.Cast5.validKey (s.gpr .r4).toNat
  trd : (⟨s.syms s5678Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (s.syms s5678Sym) s5678
  tblSch : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r5, 128⟩
  tblScr : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r
  lr : s'.lr = s.lr

theorem ofNat_sub_one64 {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1#64 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem key_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  obtain ⟨n, hnn⟩ : ∃ n, (s.gpr .r4).toNat = n := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, s.gpr .r3 = kp := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, s.gpr .r5 = kb := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb, s.gpr .r6 = cb := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, s.syms s5678Sym = T := ⟨_, rfl⟩
  have hkey := h.key; have hkf := h.kfit; have hsch := h.sch; have hKf := h.Kfit; have hscr := h.scr
  have hcf := h.sfit; have dkS := h.keyScr; have dKS := h.schScr; have hn := h.valid
  have htrd := h.trd; have hheld := h.held; have dTK := h.tblSch; have dTS := h.tblScr
  rw [hnn] at hkey hkf dkS hn
  rw [hkp] at hkey hkf dkS
  rw [hkb] at hsch hKf dKS dTK
  rw [hcb] at hscr hcf dkS dKS dTS
  rw [hT] at htrd hheld dTK dTS
  have hn5 : 5 ≤ n ∧ n ≤ 16 := hn
  have inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (cb + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨cb, 256⟩, hscr, Offset.contains_base _ hw (by omega_arith)⟩
  have hw : ∀ p ∈ allSlots, InRegions s.wr (cb + BitVec.ofNat 64 p.2) 8 := fun p hp =>
    inC (by have := allSlots_lt p hp; omega_arith)
  have sub144 : Region.Sub ⟨cb + BitVec.ofNat 64 64, 144⟩ ⟨cb, 256⟩ := Offset.sub_base _ (by decide)
  unfold expandKey
  apply WP.seq
  refine prologue_ok s wkK (by decide) _ hcb hw fun s₀ sv₀ fr₀ k₀ t₀ c₀ z₀ sy₀ => ?_
  have g₀ (q : Reg) (hq : q ∉ [Reg.r0, tbl, c255] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  -- `x` zeroed.
  refine WP.mono (zero_ok s₀ (cb := cb) (by rw [g₀ wkK, hcb]) z₀ (fun hw => by rw [k₀.2.2]; exact inC hw) kp)
    fun s₁ ⟨ci₁, d₁, k₁⟩ => ?_
  obtain ⟨M, hM⟩ : ∃ M, s₀.mem = M := ⟨_, rfl⟩
  rw [hM] at ci₁ sv₀ fr₀
  have dkC : Region.Disjoint ⟨kp, n⟩ ⟨cb, 64⟩ := dkS.sub_right (Region.sub_prefix (by decide))
  have hkM (j : Nat) (hj : j < n) : M (kp + BitVec.ofNat 64 j) = s.mem (kp + BitVec.ofNat 64 j) :=
    fr₀.bytes (R := ⟨kp, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dkS.sub_right sub144)
      (by show n ≤ 2 ^ 64; omega_arith) hj
  -- The key, copied.
  have hrK : ∀ j < n, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨kp, n⟩, hkey, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have r3₁ : s₁.gpr key = kp := by rw [k₁.gpr (by decide), g₀ key, hkp]
  have r4₁ : s₁.gpr klen = BitVec.ofNat 64 n := by
    rw [k₁.gpr (by decide), g₀ klen, ← hnn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have rw₁ : s₁.rd = s.rd ∧ s₁.wr = s.wr := ⟨by rw [k₁.2.1, k₀.2.1], by rw [k₁.2.2, k₀.2.2]⟩
  have copy : WP isa (.loop (.block copyStep) (.nonzero .d klen)) s₁ fun v =>
      CInv M kp cb n v.mem ∧ Keep [tmp, key, dst, klen] s₁ v := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = n - j ∧ j < n ∧
      CInv M kp cb j v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 j ∧
      v.gpr dst = cb + BitVec.ofNat 64 (16 + j) ∧ v.gpr klen = BitVec.ofNat 64 (n - j) ∧
      Keep [tmp, key, dst, klen] s₁ v) ?_ n s₁
      ⟨0, rfl, by omega_arith, ci₁, by rw [r3₁]; simp, by rw [d₁], by rw [r4₁, Nat.sub_zero], Keep.refl _ _⟩
    rintro m v ⟨j, rfl, hj, cv, v0, v3, v1, kv⟩
    have hk : v.mem (kp + BitVec.ofNat 64 j) = M (kp + BitVec.ofNat 64 j) :=
      cv.fr.bytes (R := ⟨kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkC)
        (by show n ≤ 2 ^ 64; omega_arith) hj
    refine WP.mono (copyStep_ok v (by omega_arith) cv v0 v3
      (by rw [kv.2.1, kv.2.2, rw₁.1, rw₁.2]; exact hrK j hj)
      (by rw [kv.2.2, rw₁.2]; exact inC (by omega_arith)) hk) fun w ⟨cw, w0, w3, w1, kw⟩ => ?_
    rw [v1, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at w1
    have ev : isa.eval (.nonzero .d klen) w = some (BitVec.ofNat 64 (n - j - 1) != 0) := by
      rw [eval_nonzero, w1]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : j + 1 = n
    · refine .inl ⟨by rw [ev, show n - j - 1 = 0 by omega_arith]; rfl, he ▸ cw, (kv.trans kw).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, n - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, cw, w0, w3, by rw [w1, Nat.sub_sub], (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono copy fun v ⟨cv, kv⟩ => ?_)
  have kv' := (k₁.trans kv)
  have gv (q : Reg) (hq : q ∉ [dst] ++ [tmp, key, dst, klen] := by decide) : v.gpr q = s₀.gpr q := kv'.gpr hq
  refine WP.seq (wp_li (by decide) fun w hw => wp_nil ?_)
  have kw := kv'.trans hw.keep
  have rdw : w.rd = s.rd := by rw [kw.2.1, k₀.2.1]
  have wrw : w.wr = s.wr := by rw [kw.2.2, k₀.2.2]
  -- The state of key expansion: `x` the padded key, no subkeys yet.
  let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem kp n).getD j 0, fun j => M (cb + BitVec.ofNat 64 (32 + j))⟩
  have ks0 : KS M cb kb T w ⟨st0, [], fun i => w.mem.readW (cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32⟩ :=
    { wk := by rw [kw.gpr (by decide), g₀ wkK, hcb]
      mem := ⟨fun a i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), by
        rw [hw.mem]; exact cv.fr.mono (by simp)⟩
      ex := fun _ _ => rfl
      len := Nat.zero_le _
      cfit := hcf
      kfit := hKf
      scr := by rw [wrw]; exact hscr
      sch := by rw [wrw]; exact hsch
      dKS := dKS
      zero := by rw [kw.gpr (by decide), z₀]
      tblR := by rw [kw.gpr (by decide), t₀, hT]
      trd := by rw [rdw, wrw]; exact htrd
      held0 := by
        rw [← hM]
        refine held_frame (hM ▸ fr₀) (fun r hr => ?_) (by rw [s5678_len]; decide) hheld
        simp only [List.mem_singleton] at hr; subst hr
        rw [s5678_len]; exact dTS.sub_right sub144
      dTS := dTS.sub_right (Region.sub_prefix (by decide))
      dTK := dTK }
  case refine_1 =>
    rw [hw.mem]
    cases a with
    | x =>
      rw [show off .x + i = 16 + i from rfl, cv.x i hi]
      show _ = (Spec.Cast5.bytesAt s.mem kp n).getD i 0
      rw [Proof.Cast5.bytesAt_getD]
      split
      · rw [hkM i (by omega_arith)]
      · rfl
    | z => exact cv.z i hi
  -- The halves.
  have halves_loop : WP isa (.loop half (.nonzero .d hlv)) w fun u => ∃ k, KS M cb kb T u k ∧
      k.xz = (halves st0 2).1 ∧ k.ws = (halves st0 2).2 ∧ Keep halfRegs w u := by
    refine WP.loop (M := isa) (fun m (u : State) => ∃ hh, m = 2 - hh ∧ hh < 2 ∧ ∃ k, KS M cb kb T u k ∧
      k.xz = (halves st0 hh).1 ∧ k.ws = (halves st0 hh).2 ∧ u.gpr out = kb + BitVec.ofNat 64 (64 * hh) ∧
      u.gpr hlv = BitVec.ofNat 64 (2 - hh) ∧ Keep halfRegs w u) ?_ 2 w
      ⟨0, rfl, by decide, _, ks0, rfl, rfl, by rw [kw.gpr (by decide), g₀ out, hkb]; simp, by rw [hw.gpr],
        Keep.refl _ _⟩
    rintro m u ⟨hh, rfl, hhh, k, hk, kx, kws, uout, u3, ku⟩
    refine WP.mono (half_ok hk uout (by rw [kws, halves_length]) hhh)
      fun x ⟨k', hk', kx', kw', xout, x3, kh⟩ => ?_
    have nx : k'.xz = (halves st0 (hh + 1)).1 ∧ k'.ws = (halves st0 (hh + 1)).2 := by
      rw [halves_succ, kx', kw', kx, kws]; exact ⟨rfl, rfl⟩
    rw [u3, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at x3
    have ev : isa.eval (.nonzero .d hlv) x = some (BitVec.ofNat 64 (2 - hh - 1) != 0) := by
      rw [eval_nonzero, x3]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : hh + 1 = 2
    · exact .inl ⟨by rw [ev, show 2 - hh - 1 = 0 by omega_arith]; rfl, k', hk', he ▸ nx.1, he ▸ nx.2,
        (ku.trans kh).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, 2 - (hh + 1), by omega_arith, hh + 1, rfl,
        by omega_arith, k', hk', nx.1, nx.2, xout, by rw [x3, Nat.sub_sub], (ku.trans kh).mono (by decide)⟩
  refine WP.seq (WP.mono halves_loop fun u ⟨k, hk, kxz, kws, ku⟩ => ?_)
  -- The saved registers, restored.
  rw [epilogue_eq]
  have r6 : u.gpr wkK = cb := hk.wk
  have hsv : Spill.Saved cb (s.write .r0 s.lr).gpr (savedSlots ++ [(.r0, lrOff)]) u.mem := by
    refine (sv₀.sub (by decide)).frame hk.mem.fr fun p hp r hr => ?_
    have hl := restoreSlots_lt p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (dKS.symm.sub_left (slot_sub _ hl))
  refine Spill.restore_ok (by decide) r6 restoreSlots_ok (by decide) (fun p hp => ?_) hsv fun s' R => ?_
  · rw [ku.2.1, ku.2.2, rdw, wrw]
    exact ⟨_, List.mem_append_right _ hscr, Offset.contains_base _
      (by have := restoreSlots_lt p hp; omega_arith) (by have := restoreSlots_lt p hp; omega_arith)⟩
  refine WP.cons exec_mtlr (wp_nil ⟨?_, fun r hr => ?_, ?_⟩)
  · show Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) = _
    rw [R.mem, hkb, hkp, hnn, scheduleAt_keys hk.mem.keys (by rw [kws, halves_length]), kws,
      Proof.Cast5.expandKey_eq _ st0.z, halves_two]
  · show s'.gpr r = s.gpr r
    have hm : (r, savedOff + 8 * saved.idxOf r) ∈ savedSlots ++ [(.r0, lrOff)] := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    rw [R.gpr _ hm, RegUpd.gpr_write_of_ne s s.lr h0]
  · show s'.gpr .r0 = s.lr
    rw [R.gpr (.r0, lrOff) (by decide)]
    exact RegUpd.gpr_write_self s _ _

end VG.Proof.Cast5.PPC64LE

end

end

/-!
# CAST5 key expansion on PPC64LE: verified

Constant time by the taint analysis: `r3`–`r6` (the pointers and the key's
length) and the table's address are public; the step and half counts, the
copy's pointers and the schedule's pointer are computed from them.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- Key expansion's contract on PPC64LE, as its proof states it. -/
def keyP : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sch : Region := ⟨s.gpr .r5, 128⟩
    let scr : Region := ⟨s.gpr .r6, 256⟩
    s.rd = [key] ∧ s.wr = [sch, scr] ∧ key.Disjoint sch ∧ key.Disjoint scr ∧ sch.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 256 ≤ 2 ^ 64 ∧ Spec.Cast5.validKey (s.gpr .r4).toNat
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- Key expansion's contract with the table, as the proof states it. -/
def keyPC : Contract isa where
  pre s := keyP.pre (stripConsts keyConsts s) ∧ ConstsOk keyConsts 0 s
  post := keyP.post
  pub s₁ s₂ := keyP.pub s₁ s₂ ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

/-- The registers key expansion writes. -/
def keyRegs : List Reg := [.r0, .r3, .r4, .r5, .r7, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
  .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30]

theorem s5678_len' : 8 * s5678.length = 4096 := s5678_len

theorem key_ok (hw : writesOnly keyRegs expandKey = true) (hn : expandKey.noCalls = true)
    (s : State) (hs : keyPC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyPC.post s s' := by
  obtain ⟨⟨hrd, hwr, _, dkS, dKS, hkf, hKf, hcf, hn'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dkS dKS hkf hKf hcf hn'
  have trd : (⟨s.syms s5678Sym, 4096⟩ : Region) ∈ s.rd := s5678_len' ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ r := s5678_len' ▸ ConstsOk.wr1 hk
  have pre : KeyPre s :=
    { key := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
      kfit := hkf
      sch := by rw [hwr]; simp
      Kfit := hKf
      scr := by rw [hwr]; simp
      sfit := hcf
      keyScr := dkS
      schScr := dKS
      valid := hn'
      trd := List.mem_append_left _ trd
      held := ConstsOk.held1 hk
      tblSch := twr _ (by rw [hwr]; simp)
      tblScr := twr _ (by rw [hwr]; simp) }
  obtain ⟨t, s', he, hp, hk'⟩ := WP.keep keyRegs (key_wp pre) hw hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hp.lr⟩, hp.sched⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk'.gpr (by decide)

theorem key_agree : ∀ s₁ s₂, keyPC.pre s₁ → keyPC.pre s₂ → keyPC.pub s₁ s₂ →
    (taintSym [s5678Sym]).Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  intro s₁ s₂ _ _ ⟨h, hsy⟩
  refine ⟨⟨h.2.2.2.2, fun r hr => ?_⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem expandKey_ct : ConstantTime isa keyPC.pre keyPC.pub expandKey :=
  VG.Taint.constantTime (A := vectorTaintSym [s5678Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6]) key_agree
    (by taint_decide)

/-- A state satisfying the precondition without the table: a key of five bytes. -/
def keySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 5 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 5⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem key_implies : keyP.Implies (Spec.Cast5.expandKeyContract abi) := by
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, abi, argRegs, keyP, Spec.Cast5.validKey] [keySat] using keySat

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 s5678

theorem keySatMem_held : ∀ i < s5678.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [Impl.Cast5.s5678, table_length]; decide)

/-- A state satisfying the precondition with the table. -/
def keySatC : State :=
  { keySat with mem := keySatMem, rd := [⟨0x1000, 5⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem key_sat : (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)).pre keySatC := by
  have hl : s5678.length = 512 := by rw [Impl.Cast5.s5678, table_length]
  have held := keySatMem_held
  rw [keyConsts_eq]
  generalize s5678 = W at hl held ⊢
  generalize e : keySatC = s
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, abi, argRegs,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Spec.Cast5.validKey]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, by decide, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem keyPC_implies : keyPC.Implies (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts keyConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts keyConsts s₁) (stripConsts keyConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := ⟨keySatC, key_sat⟩

theorem expandKey_verified :
    Verified target expandKey (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) :=
  Verified.of_correct (key_ok (by lit_decide) (by lit_decide)) expandKey_ct keyPC_implies

end VG.Proof.Cast5.PPC64LE
