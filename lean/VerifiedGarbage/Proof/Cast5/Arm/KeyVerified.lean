module

import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.Arm.Lit
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Cast5.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.Arm.Lit
meta import VerifiedGarbage.Proof.Cast5.Table
meta import VerifiedGarbage.Proof.Cast5.Arm.Ecb
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Impl.Cast5.Arm
public import VerifiedGarbage.Proof.Cast5.KeyMem
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Impl.Cast5.Arm
meta import VerifiedGarbage.Proof.Cast5.KeyMem
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-! ### `Cast5.Arm.Key`, which only this module used -/

section

/-! ### `Cast5.Arm.KeyHalf`, which only this module used -/

section

/-! ### `Cast5.Arm.KeyStep`, which only this module used -/

section

/-! ### `Cast5.Arm.KeySteps`, which only this module used -/

section

/-!
# CAST5 key expansion on ARMv7: the steps of a half

The implementation runs each half of §2.4 as 40 steps (`halfSteps`): for each
group of four lines, its extra lookups, then its lines, each with its extra
lookup from those (`lineE`). Run on the arrays, the subkeys so far and the
extra lookups (`KSt`), the steps of a half compute `halfImpl`
(`runSteps_half`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

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
  obtain e0 : stepRun (.extras (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8)) ⟨xz, ws, ex⟩ =
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

end VG.Proof.Cast5.Arm

end

end


/-!
# CAST5 key expansion on ARMv7: a step

`step` chooses the step's bytes by the step's number in `r2` (`sel_ok`),
gathers them into `r4`–`r7` (`gather_ok`), scans `VG_CAST5_S5678`, and chooses what
to do with the four values (`postE_ok`, `postL_ok`): the step of the spec's
`stepRun` (`step_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-! ## The chain of comparisons -/

/-- The code chosen by the step's number `j` in `r2`: `cs[j - i]`. -/
theorem sel_ok (cs : List (List Instr)) (i : Nat) {s : State} {j : Nat} (hij : i ≤ j) (hj : j < i + cs.length)
    (hlen : i + cs.length ≤ 256) (h2 : s.gpr .r2 = BitVec.ofNat 32 j) {Q : State → Prop}
    (hQ : ∀ u : State, (∀ r, u.gpr r = s.gpr r) → u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      u.syms = s.syms → WP isa (.block (cs.getD (j - i) [])) u Q) :
    WP isa (sel cs i) s Q := by
  induction cs generalizing i s with
  | nil => simp at hj; omega_arith
  | cons c cs ih =>
    unfold sel
    obtain hiv := toNat_ofNat_lt (j := i) (by simp at hlen; omega_arith)
    obtain hj256 : j < 256 := by simp at hj hlen; omega_arith
    obtain hi256 : i < 256 := by simp at hlen; omega_arith
    refine WP.seq ?_
    crun [hiv]
    refine wp_ite_eq (fun hz => ?_) (fun hz => ?_)
    · have hji : j = i := by
        rw [z_sub, h2] at hz
        obtain h0 := beq_iff_eq.mp hz
        have := congrArg BitVec.toNat h0
        simp at hlen
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      subst hji
      have := hQ (putSub s (s.gpr .r2) (BitVec.ofNat 32 j)) (fun r => rfl) rfl rfl rfl rfl rfl
      rwa [Nat.sub_self, List.getD_cons_zero] at this
    · have hne : j ≠ i := by
        intro e; subst e
        rw [z_sub, h2] at hz
        simp at hz
      refine ih (i + 1) (by omega_arith) (by simp at hj; omega_arith) (by simp at hlen ⊢; omega_arith) (by rw [gpr_sub, h2])
        fun u hg hm hrd hwr hsp hsy => ?_
      have := hQ u (fun r => (hg r).trans (gpr_sub _ _ _ _)) hm hrd hwr hsp hsy
      rwa [show j - i = (j - (i + 1)) + 1 by omega_arith, List.getD_cons_succ] at this

/-! ## The memory of key expansion -/

/-- `KMem`, with a scan's ten words (at `spillKey` in the working space)
written too. -/
structure KMemA (m0 m : Mem) (c K : Addr) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  xz : HoldsXZ m c st
  keys : Keys m K ws
  fr : Frame [⟨c, 64⟩, ⟨K, 128⟩, ⟨c + BitVec.ofNat 64 spillKey, 40⟩] m0 m

section
variable {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word} (h : KMemA m0 m c K st ws)
include h

/-- The memory of key expansion, from now. -/
theorem KMemA.self : KMem m m c K st ws := ⟨h.xz, h.keys, Frame.refl _ _⟩

/-- A step of `KMem` from it. -/
theorem KMemA.of {m' : Mem} {st' : XZ} {ws' : List Spec.Cast5.Word} (h' : KMem m m' c K st' ws') :
    KMemA m0 m' c K st' ws' :=
  ⟨h'.xz, h'.keys, h.fr.trans (h'.fr.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl))⟩

theorem KMemA.write (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length ≤ 32) {d w : Nat} (v : BitVec w)
    (hd : d + w / 8 ≤ 64) (hx : d + w / 8 ≤ 16 ∨ 48 ≤ d) :
    KMemA m0 (m.writeW (c + BitVec.ofNat 64 d) v) c K st ws := h.of (h.self.write dKS hws v hd hx)

theorem KMemA.quad (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length ≤ 32) (a : Arr) {q : Nat} (hq : q < 4)
    (w : Spec.Cast5.Word) :
    KMemA m0 (m.writeW (c + BitVec.ofNat 64 (off a + 4 * q)) (byteRev32 w)) c K (st.put a q w) ws :=
  h.of (h.self.quad dKS hws a hq w)

theorem KMemA.key (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length < 32) (w : Spec.Cast5.Word) :
    KMemA m0 (m.writeW (K + BitVec.ofNat 64 (4 * ws.length)) w) c K st (ws ++ [w]) := h.of (h.self.key dKS hws w)

/-- A scan's ten words written. -/
theorem KMemA.scan (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 256⟩) (hws : ws.length ≤ 32) {m' : Mem}
    (hf : Frame [⟨c + BitVec.ofNat 64 spillKey, 40⟩] m m') : KMemA m0 m' c K st ws where
  xz a i hi := by
    have := off_lt a
    rw [hf.bytes (R := ⟨c, 48⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint c (by decide) (by decide)) (show (48 : Nat) ≤ 2 ^ 64 by decide)
      (show off a + i < 48 by omega_using [this, hi])]
    exact h.xz a i hi
  keys i hi := by
    rw [hf.readW (r := ⟨K + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dKS.sub_left (Offset.sub_base _ (by omega_using [hws, hi]))).sub_right (Offset.sub_base _ (by decide)))
      (by decide)]
    exact h.keys i hi
  fr := h.fr.trans (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

end

/-! ## The state of key expansion -/

/-- The state of key expansion from the memory `m0`: the working space at
`cb` in `r12`, the schedule at `kb`, the arrays, subkeys and extra lookups
of `k` in memory; the table `VG_CAST5_S5678`, readable, held in `m0` and
apart from the working space and the schedule. -/
structure KS (m0 : Mem) (cb kb : BitVec 32) (s : State) (k : KSt) : Prop where
  r12 : s.gpr .r12 = cb
  mem : KMemA m0 s.mem (State.addr cb) (State.addr kb) k.xz k.ws
  ex : ∀ i < 4, s.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k.ex i
  len : k.ws.length ≤ 32
  cfit : cb.toNat + 256 ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr cb, 256⟩ : Region) ∈ s.wr
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.wr
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr cb, 256⟩
  tfit : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s5678Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held0 : Held m0 (State.addr (s.syms s5678Sym)) s5678
  dTS : Region.Disjoint ⟨State.addr (s.syms s5678Sym), 4096⟩ ⟨State.addr cb, 256⟩
  dTK : Region.Disjoint ⟨State.addr (s.syms s5678Sym), 4096⟩ ⟨State.addr kb, 128⟩

theorem s5678_len : 8 * s5678.length = 4096 := by rw [s5678, table_length]

section
variable {m0 : Mem} {cb kb : BitVec 32} {s : State} {k : KSt} (h : KS m0 cb kb s k)
include h

theorem KS.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem KS.inS' {off w : Nat} (hw : off + w ≤ 256) :
    InRegions (s.rd ++ s.wr) (State.addr cb + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem KS.dKS64 : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr cb, 64⟩ :=
  h.dKS.sub_right (Region.sub_prefix (by decide))

/-- The same state, later: other registers, memory and flags. -/
theorem KS.update {u : State} {k' : KSt} (hc : u.gpr .r12 = s.gpr .r12)
    (hm : KMemA m0 u.mem (State.addr cb) (State.addr kb) k'.xz k'.ws)
    (he : ∀ i < 4, u.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k'.ex i)
    (hl : k'.ws.length ≤ 32) (hwr : u.wr = s.wr) (hsy : u.syms = s.syms) (hrd : u.rd = s.rd) : KS m0 cb kb u k' :=
  ⟨hc.trans h.r12, hm, he, hl, h.cfit, h.kfit, by rw [hwr]; exact h.scr, by rw [hwr]; exact h.sch, h.dKS,
    by rw [hsy]; exact h.tfit, by rw [hsy, hrd, hwr]; exact h.trd, by rw [hsy]; exact h.held0,
    by rw [hsy]; exact h.dTS, by rw [hsy]; exact h.dTK⟩

/-- The table, still held. -/
theorem KS.held : Held s.mem (State.addr (s.syms s5678Sym)) s5678 := by
  refine held_frame h.mem.fr (fun r hr => ?_) (by rw [s5678_len]; decide) h.held0
  rw [s5678_len]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.dTS.sub_right (Region.sub_prefix (by decide))
  · exact h.dTK
  · exact h.dTS.sub_right (Offset.sub_base _ (by decide))

end

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q + 1 ≤ 48 := by
  obtain ⟨a, i⟩ := q
  have := off_lt a
  simp only [srcOff] at hq ⊢
  omega_arith

/-! ## Gathering the bytes -/

theorem gather_ok {m0 : Mem} {cb kb : BitVec 32} {s : State} {k : KSt} (h : KS m0 cb kb s k)
    {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16) (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.gpr .r4 = (k.xz.get d).setWidth 32 ∧ u.gpr .r5 = (k.xz.get c).setWidth 32 ∧
      u.gpr .r6 = (k.xz.get b).setWidth 32 ∧ u.gpr .r7 = (k.xz.get a).setWidth 32 ∧
      Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  obtain aS := addr_off h.cfit
  obtain ia := h.inS' (off := srcOff a) (w := 1) (by have := srcOff_lt ha; omega_arith)
  obtain ib := h.inS' (off := srcOff b) (w := 1) (by have := srcOff_lt hb; omega_arith)
  obtain ic := h.inS' (off := srcOff c) (w := 1) (by have := srcOff_lt hc; omega_arith)
  obtain id := h.inS' (off := srcOff d) (w := 1) (by have := srcOff_lt hd; omega_arith)
  obtain xa := h.mem.xz.pos ha
  obtain xb := h.mem.xz.pos hb
  obtain xc := h.mem.xz.pos hc
  obtain xd := h.mem.xz.pos hd
  obtain la : srcOff a < 256 := by have := srcOff_lt ha; omega_arith
  obtain lb : srcOff b < 256 := by have := srcOff_lt hb; omega_arith
  obtain lc : srcOff c < 256 := by have := srcOff_lt hc; omega_arith
  obtain ld : srcOff d < 256 := by have := srcOff_lt hd; omega_arith
  obtain oa : srcOff a < 4096 := by omega_arith
  obtain ob : srcOff b < 4096 := by omega_arith
  obtain oc : srcOff c < 4096 := by omega_arith
  obtain od : srcOff d < 4096 := by omega_arith
  unfold gather
  crun [h.r12, aS _ la, aS _ lb, aS _ lc, aS _ ld, ia, ib, ic, id, xa, xb, xc, xd, oa, ob, oc, od]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-! ## What a step does with the values -/

theorem ex_off {i : Nat} (hi : i < 4) : extraOff + 4 * i + 4 ≤ 64 := by unfold extraOff; omega_arith

/-- The extra lookups of a group to their slots. -/
theorem postE_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) (a b c d : Pos)
    (v : Nat → Spec.Cast5.Word) (hv : ∀ i < 4, u.gpr (accReg i) = v i) :
    WP isa (.block (Step.extras a b c d).post) u fun w =>
      KS m0 cb kb w { k with ex := v } ∧ Keep [] u w := by
  obtain aS := addr_off h.cfit
  obtain inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  obtain v0 : u.gpr .r8 = v 0 := hv 0 (by decide)
  obtain v1 : u.gpr .r9 = v 1 := hv 1 (by decide)
  obtain v2 : u.gpr .r10 = v 2 := hv 2 (by decide)
  obtain v3 : u.gpr .r11 = v 3 := hv 3 (by decide)
  simp only [Step.post]
  unfold extraOff
  crun [h.r12, aS, inS, v0, v1, v2, v3]
  have dKS := h.dKS64
  have hl := h.len
  refine ⟨h.update rfl ?_ (fun i hi => ?_) hl rfl rfl rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · exact (((h.mem.write dKS hl _ (by decide) (by decide)).write dKS hl _ (by decide) (by decide)).write dKS hl _
      (by decide) (by decide)).write dKS hl _ (by decide) (by decide)
  · simp only [extraOff]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceAdd, Mem.readW_writeW_self32] <;>
    repeat (first
      | rw [Mem.readW_writeW_self32]
      | rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)])

/-- The XORs of a line's lookups and its extra lookup, into `r0`. -/
theorem lineHead_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) {e : Nat}
    (he : 5 ≤ e ∧ e ≤ 8) :
    WP isa (.block [.dp .eor .r0 .r8 (.reg .r9), .dp .eor .r0 .r0 (.reg .r10), .dp .eor .r0 .r0 (.reg .r11),
      .ldr .r1 .r12 (extraOff + 4 * (8 - e)), .dp .eor .r0 .r0 (.reg .r1)]) u fun w =>
      w.gpr .r0 = u.gpr .r8 ^^^ u.gpr .r9 ^^^ u.gpr .r10 ^^^ u.gpr .r11 ^^^ k.ex (8 - e) ∧
      Keep [.r0, .r1] u w ∧ w.mem = u.mem := by
  obtain aS := addr_off h.cfit
  obtain ho : extraOff + 4 * (8 - e) < 256 := by unfold extraOff; omega_arith
  obtain ho' : extraOff + 4 * (8 - e) < 4096 := by omega_arith
  obtain hin := h.inS' (off := extraOff + 4 * (8 - e)) (w := 4) (by unfold extraOff; omega_arith)
  obtain hx := h.ex (8 - e) (by omega_arith)
  crun [h.r12, aS _ ho, hin, hx, ho']
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-- The quadruple a line XORs in, if any. -/
def wordCode : Option (Arr × Nat) → List Instr
  | some (a, q) => [.ldr .r1 .r12 (off a + 4 * q), .rev .r1 .r1, .dp .eor .r0 .r0 (.reg .r1)]
  | none => []

/-- `v` with the quadruple `wd` of the arrays XORed in, if any. -/
def withQuad (xz : XZ) (v : Spec.Cast5.Word) : Option (Arr × Nat) → Spec.Cast5.Word
  | some (a, q) => v ^^^ quadOf (xz.arr a) q
  | none => v

theorem wordCode_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k)
    (wd : Option (Arr × Nat)) (hq : ∀ a q, wd = some (a, q) → q < 4) :
    WP isa (.block (wordCode wd)) u fun w =>
      w.gpr .r0 = withQuad k.xz (u.gpr .r0) wd ∧
      Keep [.r0, .r1] u w ∧ w.mem = u.mem := by
  cases wd with
  | none => exact WP.block_nil ⟨rfl, Keep.refl _ _, rfl⟩
  | some aq =>
    obtain ⟨a, q⟩ := aq
    obtain hq4 := hq a q rfl
    have := off_lt a
    obtain aS := addr_off h.cfit
    obtain ho : off a + 4 * q < 256 := by omega_arith
    obtain ho' : off a + 4 * q < 4096 := by omega_arith
    obtain hin := h.inS' (off := off a + 4 * q) (w := 4) (by omega_arith)
    obtain hx := h.mem.xz.quad a hq4
    unfold wordCode
    crun [h.r12, aS _ ho, hin, ho', rev_eq, hx]
    exact ⟨rfl, ⟨by keep_regs, rfl, rfl, rfl⟩⟩

/-- Where a line's value goes. -/
def storeCode : Store → List Instr
  | .quad a q => [.rev .r0 .r0, .str .r0 .r12 (off a + 4 * q)]
  | .key k => [.str .r0 .lr (4 * k)]

theorem post_line (l : Impl.Cast5.Line) (st : Store) :
    (Step.line l st).post = ([.dp .eor .r0 .r8 (.reg .r9), .dp .eor .r0 .r0 (.reg .r10), .dp .eor .r0 .r0 (.reg .r11),
      .ldr .r1 .r12 (extraOff + 4 * (8 - l.extra.1)), .dp .eor .r0 .r0 (.reg .r1)] : List Instr) ++ wordCode l.word ++
      storeCode st := by
  obtain ⟨main, extra, word⟩ := l
  rcases word with _ | ⟨a, q⟩ <;> cases st <;> rfl

theorem storeQuad_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) (a : Arr)
    {q : Nat} (hq : q < 4) {v : Spec.Cast5.Word} (h0 : u.gpr .r0 = v) :
    WP isa (.block (storeCode (.quad a q))) u fun w =>
      KS m0 cb kb w { k with xz := k.xz.put a q v } ∧ Keep [.r0] u w := by
  have := off_lt a
  have := off_ge a
  obtain aS := addr_off h.cfit
  obtain ho : off a + 4 * q < 256 := by omega_arith
  obtain ho' : off a + 4 * q < 4096 := by omega_arith
  obtain hin := h.inS (off := off a + 4 * q) (w := 4) (by omega_arith)
  unfold storeCode
  crun [h.r12, aS _ ho, hin, ho', h0, rev_eq]
  refine ⟨h.update rfl (h.mem.quad h.dKS64 h.len a hq v) (fun i hi => ?_) h.len rfl rfl rfl,
    ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  rw [Mem.readW_writeW_sep (Offset.sep _ (d := extraOff + 4 * i) (n := 32 / 8) (e := off a + 4 * q) (k := 32 / 8)
    (by unfold extraOff; omega_arith) (by unfold extraOff; omega_arith) (by omega_arith)) (by decide)]
  exact h.ex i hi

theorem storeKey_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) {j hh : Nat}
    (hj : j < 16) (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen : k.ws.length = 16 * hh + j)
    (hl : k.ws.length < 32) {v : Spec.Cast5.Word} (h0 : u.gpr .r0 = v) :
    WP isa (.block (storeCode (.key j))) u fun w =>
      KS m0 cb kb w { k with ws := k.ws ++ [v] } ∧ Keep [] u w := by
  have hkf := h.kfit
  obtain ea : State.addr (u.gpr .lr + BitVec.ofNat 32 (4 * j)) = State.addr kb + BitVec.ofNat 64 (4 * k.ws.length) := by
    rw [hlr, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_arith), hlen]
    congr 2; omega_arith
  obtain hin : InRegions u.wr (State.addr kb + BitVec.ofNat 64 (4 * k.ws.length)) 4 :=
    ⟨_, h.sch, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain ho : 4 * j < 4096 := by omega_arith
  unfold storeCode
  crun [ea, hin, ho, h0]
  refine ⟨h.update rfl (h.mem.key h.dKS64 hl v) (fun i hi => ?_) (by simp; omega_arith) rfl rfl rfl,
    ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [Mem.readW_writeW_sep (h.dKS.symm.sep (Offset.contains_base _ (by have := ex_off hi; omega_arith)
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
theorem postL_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k)
    {l : Impl.Cast5.Line} {st : Store} (hok : stepOk (.line l st) = true)
    (h8 : u.gpr .r8 = Spec.Cast5.S8 (k.xz.get l.main.2.2.2)) (h9 : u.gpr .r9 = Spec.Cast5.S7 (k.xz.get l.main.2.2.1))
    (h10 : u.gpr .r10 = Spec.Cast5.S6 (k.xz.get l.main.2.1)) (h11 : u.gpr .r11 = Spec.Cast5.S5 (k.xz.get l.main.1))
    {hh : Nat} (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh))
    (hkey : ∀ j, st = .key j → k.ws.length = 16 * hh + j ∧ k.ws.length < 32) :
    WP isa (.block (Step.line l st).post) u fun w => KS m0 cb kb w (stepRun (.line l st) k) ∧ Keep [.r0, .r1] u w := by
  obtain hl : lineOk l = true := by cases st <;> simp only [stepOk, Bool.and_eq_true] at hok <;> exact hok.1
  have he := hl
  simp only [lineOk, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain hq : ∀ a q, l.word = some (a, q) → q < 4 := by
    intro a q hw
    have := he.2
    rw [hw] at this
    simpa using this
  rw [post_line, WP.block_append_iff, WP.block_append_iff]
  refine VG.Arm.WP.mono_syms (lineHead_ok h ⟨he.1.1.2, he.1.2⟩) fun v ⟨v0, vk, vm⟩ vsy => ?_
  obtain hv : KS m0 cb kb v k := h.update (vk.gpr _ (by decide)) (by rw [vm]; exact h.mem)
    (fun i hi => by rw [vm]; exact h.ex i hi) h.len vk.wr vsy vk.rd
  refine VG.Arm.WP.mono_syms (wordCode_ok hv l.word hq) fun w ⟨w0, wk, wm⟩ wsy => ?_
  obtain hw : KS m0 cb kb w k := hv.update (wk.gpr _ (by decide)) (by rw [wm]; exact hv.mem)
    (fun i hi => by rw [wm]; exact hv.ex i hi) hv.len wk.wr wsy wk.rd
  obtain wv : w.gpr .r0 = lineE k.xz k.ex l := by
    rw [w0, v0, h8, h9, h10, h11]
    unfold lineE
    clear hq he hok hl hkey h8 h9 h10 h11
    obtain ⟨main, extra, word⟩ := l
    rcases word with _ | ⟨a, q⟩ <;> rfl
  obtain kuw := vk.trans wk
  cases st with
  | quad a q =>
    obtain hq4 : q < 4 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    exact WP.mono (storeQuad_ok hw a hq4 wv) fun x ⟨hx, xk⟩ => ⟨hx, kuw.trans (xk.mono (by decide))⟩
  | key j =>
    obtain hj : j < 16 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    obtain ⟨hlen, hl32⟩ := hkey j rfl
    exact WP.mono (storeKey_ok hw hj (by rw [kuw.gpr _ (by decide)]; exact hlr) hlen hl32 wv)
      fun x ⟨hx, xk⟩ => ⟨hx, kuw.trans (xk.mono (by decide))⟩

end VG.Proof.Cast5.Arm

end

end


/-!
# CAST5 key expansion on ARMv7: the steps of a half, run

`keyStep_ok`: step `j` of a half (its number in `r2`) is the spec's `stepRun`;
`half_ok`: the 40 steps of a half compute `halfImpl` (`runSteps_half`),
writing its sixteen subkeys from `lr`.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

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

theorem ofNat_setWidth8 (x : Byte) : BitVec.ofNat 8 (x.setWidth 32).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

theorem setWidth8_lt (x : Byte) : (x.setWidth 32).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega_arith

/-! ## A step -/

/-- The registers a step writes. -/
def stepRegs : List Reg := [.r0, .r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem keyStep_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k0 : KSt} {j hh : Nat} (hj : j < 40)
    (h : KS m0 cb kb u (runSteps (halfSteps.take j) k0)) (h2 : u.gpr .r2 = BitVec.ofNat 32 j)
    (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa Impl.Cast5.Arm.step u fun v => KS m0 cb kb v (runSteps (halfSteps.take (j + 1)) k0) ∧
      v.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ v.z = decide (j + 1 = 40) ∧ Keep stepRegs u v := by
  obtain ⟨hok, p1, p2, p3, p4, hkeys⟩ := step_facts hj
  obtain ⟨st, hst⟩ : ∃ st, halfSteps.getD j default = st := ⟨_, rfl⟩
  rw [hst] at hok p1 p2 p3 p4 hkeys
  obtain ⟨kj, hkj⟩ : ∃ kj, runSteps (halfSteps.take j) k0 = kj := ⟨_, rfl⟩
  rw [hkj] at h
  obtain hnext : runSteps (halfSteps.take (j + 1)) k0 = stepRun st kj := by
    rw [take_succ_steps hj, runSteps_append, hkj, hst]; rfl
  rw [hnext]
  obtain hlen40 : 0 + (halfSteps.map Step.gather).length ≤ 256 := by simp [halfSteps_length]
  unfold Impl.Cast5.Arm.step
  -- The step's bytes.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) hlen40 h2
    fun u1 g1 m1 rd1 wr1 sp1 sy1 => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst, Step.gather_eq]
  obtain h1 : KS m0 cb kb u1 kj := h.update (g1 _) (by rw [m1]; exact h.mem) (fun i hi => by rw [m1]; exact h.ex i hi)
    h.len wr1 sy1 rd1
  refine VG.Arm.WP.mono_syms (gather_ok h1 p1 p2 p3 p4) fun v ⟨v4, v5, v6, v7, vk, vm⟩ vsy => ?_
  obtain hv : KS m0 cb kb v kj := h1.update (vk.gpr _ (by decide)) (by rw [vm]; exact h1.mem)
    (fun i hi => by rw [vm]; exact h1.ex i hi) h1.len vk.wr vsy vk.rd
  -- The scan.
  obtain hidx : ∀ i < 4, (v.gpr (idxReg i)).toNat < 256 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show (v.gpr .r4).toNat < 256; rw [v4]; exact setWidth8_lt _
    · show (v.gpr .r5).toNat < 256; rw [v5]; exact setWidth8_lt _
    · show (v.gpr .r6).toNat < 256; rw [v6]; exact setWidth8_lt _
    · show (v.gpr .r7).toNat < 256; rw [v7]; exact setWidth8_lt _
  have v12 : v.gpr .r12 = cb := hv.r12
  have hcf := hv.cfit
  obtain sp : ScanPre s5678Sym spillKey v :=
    { idx := hidx
      cfit := by rw [v12]; unfold spillKey; omega_arith
      ofit := by decide
      inS := fun {off w} hw => by
        rw [v12, Offset.add_add]; exact hv.inS (by unfold spillKey; omega_using [hw])
      tfit := hv.tfit
      trd := hv.trd
      dTS := by rw [v12]; exact hv.dTS.sub_right (Offset.sub_base _ (by decide)) }
  refine WP.seq (VG.Arm.WP.mono_syms (scan_ok v s5678Sym spillKey sp) fun w ⟨wa, wk, wf⟩ wsy => ?_)
  rw [v12] at wf
  obtain hw : KS m0 cb kb w kj := by
    refine hv.update (wk.gpr _ (by decide)) (hv.mem.scan hv.dKS hv.len wf) (fun i hi => ?_) hv.len wk.wr wsy wk.rd
    have := ex_off hi
    rw [wf.readW (r := ⟨State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by unfold spillKey; omega_using [this])) (by omega_using [this]) (by decide))
      (by decide)]
    exact hv.ex i hi
  have hTf := hv.tfit
  have ent (i : Nat) (hi : i < 4) (x : Byte) (hx : v.gpr (idxReg i) = x.setWidth 32) :
      w.gpr (accReg i) = tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5 (x.setWidth 32).toNat i := by
    rw [wa i hi, hx]; exact tw_table hTf hv.held (setWidth8_lt _) hi
  obtain a0 : w.gpr .r8 = Spec.Cast5.S8 (kj.xz.get (stepPos st).2.2.2) := by
    rw [show Reg.r8 = accReg 0 from rfl, ent 0 (by decide) _ v4]; simp only [tableEnt, ofNat_setWidth8]
  obtain a1 : w.gpr .r9 = Spec.Cast5.S7 (kj.xz.get (stepPos st).2.2.1) := by
    rw [show Reg.r9 = accReg 1 from rfl, ent 1 (by decide) _ v5]; simp only [tableEnt, ofNat_setWidth8]
  obtain a2 : w.gpr .r10 = Spec.Cast5.S6 (kj.xz.get (stepPos st).2.1) := by
    rw [show Reg.r10 = accReg 2 from rfl, ent 2 (by decide) _ v6]; simp only [tableEnt, ofNat_setWidth8]
  obtain a3 : w.gpr .r11 = Spec.Cast5.S5 (kj.xz.get (stepPos st).1) := by
    rw [show Reg.r11 = accReg 3 from rfl, ent 3 (by decide) _ v7]; simp only [tableEnt, ofNat_setWidth8]
  obtain kuw : Keep stepRegs u w := (Keep.mono (show Keep [.r4, .r5, .r6, .r7] u v from
    ⟨fun r hr => (vk.gpr r hr).trans (g1 r), vk.rd.trans rd1, vk.wr.trans wr1, vk.sp.trans sp1⟩) (by decide)).trans
    (wk.mono (by decide))
  obtain w2 : w.gpr .r2 = BitVec.ofNat 32 j := by rw [wk.gpr _ (by decide), vk.gpr _ (by decide), g1, h2]
  obtain wlr : w.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) := by rw [kuw.gpr _ (by decide), hlr]
  -- What it does with the values.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) (by simp [halfSteps_length]) w2
    fun x gx mx rdx wrx spx syx => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst]
  obtain hx : KS m0 cb kb x kj := hw.update (gx _) (by rw [mx]; exact hw.mem) (fun i hi => by rw [mx]; exact hw.ex i hi)
    hw.len wrx syx rdx
  have tail (y : State) (hy : KS m0 cb kb y (stepRun st kj)) (ky : Keep stepRegs u y)
      (y2 : y.gpr .r2 = BitVec.ofNat 32 j) :
      WP isa (.block [.dp .add .r2 .r2 (.imm 1), .cmp .r2 (.imm 40)]) y fun z =>
        KS m0 cb kb z (stepRun st kj) ∧ z.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ z.z = decide (j + 1 = 40) ∧
          Keep stepRegs u z := by
    crun [y2]
    refine ⟨hy.update rfl hy.mem hy.ex hy.len rfl rfl rfl, by rw [BitVec.ofNat_add]; rfl, ?_,
      ky.trans ⟨fun r hr => by
        simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact hr (by decide)), rfl, rfl, rfl⟩⟩
    by_cases he : j = 39
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 j + 1 - 40 ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        simp at this; omega_arith
      simpa using this
  cases st with
  | extras a b c d =>
    refine WP.mono (postE_ok hx a b c d (exVal kj.xz a b c d) fun i hi => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans ⟨fun r _ => gx r, rdx, wrx, spx⟩).trans (ky.mono (by decide)))
        (by rw [ky.gpr _ (by decide), gx, w2])) fun z hz => hz
    · rw [gx]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
  | line l store =>
    refine WP.mono (postL_ok hx hok (by rw [gx]; exact a0) (by rw [gx]; exact a1) (by rw [gx]; exact a2)
      (by rw [gx]; exact a3) (by rw [gx]; exact wlr) fun jj e => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans ⟨fun r _ => gx r, rdx, wrx, spx⟩).trans (ky.mono (by decide)))
        (by rw [ky.gpr _ (by decide), gx, w2])) fun z hz => hz
    subst e
    obtain hc := hkeys l jj rfl
    obtain hl := ws_length (halfSteps.take j) k0
    rw [hkj] at hl
    obtain hlim : countKeys (halfSteps.take j) < 16 := by
      have := hok; simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    exact ⟨by rw [hl, hc, hlen0], by rw [hl, hlen0]; omega_arith⟩

/-! ## A half -/

/-- The registers a half writes. -/
def halfRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem take_steps_40 : halfSteps.take 40 = halfSteps := by
  rw [List.take_of_length_le (by rw [halfSteps_length])]

theorem half_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k0 : KSt} {hh : Nat} (h : KS m0 cb kb u k0)
    (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa half u fun v => ∃ k, KS m0 cb kb v k ∧ k.xz = (halfImpl k0.xz).2 ∧ k.ws = k0.ws ++ (halfImpl k0.xz).1 ∧
      v.gpr .lr = kb + BitVec.ofNat 32 (64 * (hh + 1)) ∧ v.gpr .r3 = u.gpr .r3 - 1 ∧
      v.z = (u.gpr .r3 - 1 == 0) ∧ Keep halfRegs u v := by
  unfold half
  refine WP.seq ?_
  crun
  obtain ⟨u0, hu0⟩ : ∃ u0, u.setReg .r2 0 = u0 := ⟨_, rfl⟩
  rw [hu0]
  obtain k0u : Keep stepRegs u u0 := by
    rw [← hu0]; exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by intro e; subst e; exact hr (by decide)), rfl, rfl, rfl⟩
  obtain h0 : KS m0 cb kb u0 (runSteps (halfSteps.take 0) k0) := by
    rw [← hu0]; exact h.update rfl h.mem h.ex h.len rfl rfl rfl
  obtain loop : WP isa (.loop Impl.Cast5.Arm.step .ne) u0
      (fun v => KS m0 cb kb v (runSteps halfSteps k0) ∧ Keep stepRegs u v) := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = 40 - j ∧ j < 40 ∧
      KS m0 cb kb v (runSteps (halfSteps.take j) k0) ∧ v.gpr .r2 = BitVec.ofNat 32 j ∧ Keep stepRegs u v)
      ?_ 40 u0 ⟨0, rfl, by decide, h0, by rw [← hu0]; rfl, k0u⟩
    rintro m v ⟨j, rfl, hj, hv, v2, kv⟩
    refine WP.mono (keyStep_ok hj hv v2 (by rw [kv.gpr _ (by decide), hlr]) hlen0 hhh) fun w ⟨hw, w2, wz, kw⟩ => ?_
    by_cases he : j + 1 = 40
    · refine .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, ?_, kv.trans kw⟩
      rw [he, take_steps_40] at hw; exact hw
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 40 - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, hw, w2, kv.trans kw⟩
  refine WP.seq (WP.mono loop fun v ⟨hv, kv⟩ => ?_)
  obtain vlr : v.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) := by rw [kv.gpr _ (by decide), hlr]
  obtain v3 : v.gpr .r3 = u.gpr .r3 := kv.gpr _ (by decide)
  crun [vlr, v3]
  obtain ⟨hx, hw⟩ := runSteps_half k0
  refine ⟨runSteps halfSteps k0, hv.update (by simp only [gpr_setReg, gpr_sub, reduceCtorEq, ite_false]) hv.mem
    hv.ex hv.len rfl rfl rfl, hx, hw, ?_, (kv.mono (by decide)).trans ⟨?_, rfl, rfl, rfl⟩⟩
  rotate_left
  · intro r hr
    obtain h3 : ¬r = .r3 := by intro e; subst e; exact hr (by decide)
    obtain hl : ¬r = .lr := by intro e; subst e; exact hr (by decide)
    rw [gpr_setReg_of_ne _ _ h3, gpr_sub, gpr_setReg_of_ne _ _ hl]
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl]

end VG.Proof.Cast5.Arm

end

end


/-!
# CAST5 key expansion on ARMv7

`expandKey` takes the working space from the stack, saves the callee-saved
registers in it, pads the key with zeros into `x` (§2.5), runs both halves
of §2.4 (`half_ok`) and restores the registers (`key_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-! ## The key, padded -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the first 64 bytes of the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_word (m : Mem) (c : Addr) {d e : Nat} (hd : d + 4 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 32)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 4 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) {cb : BitVec 32} (hc : s.gpr .r12 = cb) (hcf : cb.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w) (key : Addr) :
    WP isa (.block [.mov .r3 (.imm 0), .str .r3 .r12 xOff, .str .r3 .r12 (xOff + 4), .str .r3 .r12 (xOff + 8),
      .str .r3 .r12 (xOff + 12), .dp .add .r3 .r12 (.imm (BitVec.ofNat 32 xOff))]) s fun u =>
      CInv s.mem key (State.addr cb) 0 u.mem ∧ u.gpr .r3 = cb + BitVec.ofNat 32 16 ∧ Keep [.r3] s u := by
  obtain aS := addr_off hcf
  unfold xOff
  crun [hc, aS, hin]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [zero_word _ _ (by decide) (by omega_arith), zero_word _ _ (by decide) (by omega_arith), zero_word _ _ (by decide) (by omega_arith),
      zero_word _ _ (by decide) (by omega_arith)]
    repeat' split
    all_goals first | rfl | omega_arith
  · rw [zero_word _ _ (by decide) (by omega_arith), zero_word _ _ (by decide) (by omega_arith), zero_word _ _ (by decide) (by omega_arith),
      zero_word _ _ (by decide) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), ite_eq_right (by omega_arith),
      ite_eq_right (by omega_arith)]
  · exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem copyStep_ok (u : State) {m0 : Mem} {kp cb : BitVec 32} {j : Nat} (hj : j < 16)
    (hI : CInv m0 (State.addr kp) (State.addr cb) j u.mem) (hcf : cb.toNat + 256 ≤ 2 ^ 32)
    (hkf : kp.toNat + (j + 1) ≤ 2 ^ 32)
    (h0 : u.gpr .r0 = kp + BitVec.ofNat 32 j) (h3 : u.gpr .r3 = cb + BitVec.ofNat 32 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (State.addr cb + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (State.addr kp + BitVec.ofNat 64 j) = m0 (State.addr kp + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 (State.addr kp) (State.addr cb) (j + 1) v.mem ∧ v.gpr .r0 = kp + BitVec.ofNat 32 (j + 1) ∧
      v.gpr .r3 = cb + BitVec.ofNat 32 (16 + (j + 1)) ∧ v.gpr .r1 = u.gpr .r1 - 1 ∧
      v.z = (u.gpr .r1 - 1 == 0) ∧ Keep [.r0, .r1, .r3, .r4] u v := by
  obtain e0 : State.addr (kp + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = State.addr kp + BitVec.ofNat 64 j := by
    rw [BitVec.add_zero, addr_add (by omega_arith)]
  obtain e3 : State.addr (cb + BitVec.ofNat 32 (16 + j) + BitVec.ofNat 32 0) =
      State.addr cb + BitVec.ofNat 64 (16 + j) := by
    rw [BitVec.add_zero, addr_add (by omega_arith)]
  unfold copyStep
  crun [e0, e3, hr, hw, hk, h0, h3]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_arith) (by omega_arith)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_arith⟩, ite_eq_left (by omega_arith), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_arith), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hl, ite_eq_right (by omega_arith)]
  · simp only [Mem.writeW]
    rw [byte_write _ _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    exact hI.z i hi
  · exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [BitVec.add_assoc, BitVec.ofNat_add j 1]; rfl
  · rw [BitVec.add_assoc, show 16 + (j + 1) = (16 + j) + 1 by omega_arith, BitVec.ofNat_add (16 + j) 1]; rfl

/-! ## The whole function -/

/-- Key expansion's contract on ARMv7, as its proof states it. -/
def keyArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let sch : Region := ⟨State.addr (s.gpr .r2), 128⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 256⟩
    s.rd = [key] ∧ s.wr = [sch, scr] ∧ key.Disjoint sch ∧ key.Disjoint scr ∧ sch.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 256 ≤ 2 ^ 32 ∧ Spec.Cast5.validKey (s.gpr .r1).toNat
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (State.addr (s.gpr .r2)) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem key_correct (s : State) (hs : keyArm.pre (stripConsts keyConsts s)) (hkc : ConstsOk keyConsts 0 s) :
    WP isa expandKey s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyArm.post s s' := by
  obtain ⟨hrd, hwr, dkK, dkS, dKS, hkf, hKf, hcf, hn⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dkK dkS dKS hkf hKf hcf hn
  have tfit : (s.syms s5678Sym).toNat + 4096 ≤ 2 ^ 32 := s5678_len ▸ hkc.fit List.mem_cons_self
  have trd : (⟨State.addr (s.syms s5678Sym), 4096⟩ : Region) ∈ s.rd := s5678_len ▸ ConstsOk.rd1 hkc
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr (s.syms s5678Sym), 4096⟩ r := s5678_len ▸ ConstsOk.wr1 hkc
  have held : Held s.mem (State.addr (s.syms s5678Sym)) s5678 := ConstsOk.held1 hkc
  obtain ⟨n, hnn⟩ : ∃ n, (s.gpr .r1).toNat = n := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, s.gpr .r0 = kp := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, s.gpr .r2 = kb := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb, s.gpr .r3 = cb := ⟨_, rfl⟩
  rw [hnn] at hrd dkK dkS hkf hn
  rw [hkp] at hrd dkK dkS hkf
  rw [hkb] at hwr dkK dKS hKf
  rw [hcb] at hwr dkS dKS hcf
  have hn5 : 5 ≤ n ∧ n ≤ 16 := hn
  have inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨State.addr cb, 256⟩, by rw [hwr]; simp, Offset.contains_base _ hw (by omega_arith)⟩
  unfold expandKey
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- The working space in `r12`, and the saved registers.
  have h1 : WP isa (.block [.mov .r12 (.reg .r3)]) s fun s₁ => s₁ = s.setReg .r12 cb := by
    crun [hcb]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff, save_eq]
  refine VG.Arm.WP.mono_syms (WP.keep [] (Spill.save_block_ok savedSlots_ok (s := s.setReg .r12 cb)
    (by simp only [gpr_setReg_self]; omega_arith) fun d _ hd => by simp only [gpr_setReg_self, wr_setReg]; exact inC (by omega_arith))
    (by decide)) fun s₂ ⟨⟨g₂, rd₂, wr₂, m₂⟩, k₂⟩ sy₂ => ?_
  simp only [gpr_setReg_self] at m₂
  obtain ⟨M, hM⟩ : ∃ M, s₂.mem = M := ⟨_, rfl⟩
  have c₂ : s₂.gpr .r12 = cb := by rw [g₂, gpr_setReg_self]
  have g₂' (r : Reg) (hr : r ≠ .r12) : s₂.gpr r = s.gpr r := by rw [g₂]; exact gpr_setReg_of_ne _ _ hr
  have hMf : Frame [⟨State.addr cb, 256⟩] s.mem M := by
    rw [← hM, m₂]; exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have hkM (j : Nat) (hj : j < n) : M (State.addr kp + BitVec.ofNat 64 j) = s.mem (State.addr kp + BitVec.ofNat 64 j) :=
    hMf.bytes (R := ⟨State.addr kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkS)
      (by show n ≤ 2 ^ 64; omega_arith) hj
  refine VG.Arm.WP.mono_syms (zero_ok s₂ c₂ hcf (fun hw => by rw [wr₂]; exact inC hw) (State.addr kp))
    fun s₃ ⟨ci₃, r3₃, k₃⟩ sy₃ => ?_
  rw [hM] at ci₃
  -- The key, copied.
  have hrK : ∀ j < n, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨State.addr kp, n⟩, List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp)),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dkC : Region.Disjoint ⟨State.addr kp, n⟩ ⟨State.addr cb, 64⟩ := dkS.sub_right (Region.sub_prefix (by decide))
  have r0₃ : s₃.gpr .r0 = kp := by rw [k₃.gpr _ (by decide), g₂' _ (by decide), hkp]
  have r1₃ : s₃.gpr .r1 = BitVec.ofNat 32 n := by
    rw [k₃.gpr _ (by decide), g₂' _ (by decide), ← hnn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have copy : WP isa (.loop (.block copyStep) .ne) s₃ fun v =>
      CInv M (State.addr kp) (State.addr cb) n v.mem ∧ Keep [.r0, .r1, .r3, .r4] s₃ v := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = n - j ∧ j < n ∧
      CInv M (State.addr kp) (State.addr cb) j v.mem ∧ v.gpr .r0 = kp + BitVec.ofNat 32 j ∧
      v.gpr .r3 = cb + BitVec.ofNat 32 (16 + j) ∧ v.gpr .r1 = BitVec.ofNat 32 (n - j) ∧
      Keep [.r0, .r1, .r3, .r4] s₃ v) ?_ n s₃
      ⟨0, rfl, by omega_arith, ci₃, by rw [r0₃, BitVec.add_zero], by rw [r3₃], by rw [r1₃, Nat.sub_zero], Keep.refl _ _⟩
    rintro m v ⟨j, rfl, hj, cv, v0, v3, v1, kv⟩
    have hk : v.mem (State.addr kp + BitVec.ofNat 64 j) = M (State.addr kp + BitVec.ofNat 64 j) :=
      cv.fr.bytes (R := ⟨State.addr kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkC)
        (by show n ≤ 2 ^ 64; omega_arith) hj
    refine WP.mono (copyStep_ok v (by omega_arith) cv hcf (by omega_arith) v0 v3
      (by rw [kv.rd, kv.wr, k₃.rd, k₃.wr, rd₂, wr₂]; exact hrK j hj)
      (by rw [kv.wr, k₃.wr, wr₂]; exact inC (by omega_arith)) hk) fun w ⟨cw, w0, w3, w1, wz, kw⟩ => ?_
    rw [v1, ofNat_sub_one (by omega_arith) (by omega_arith)] at w1 wz
    by_cases he : j + 1 = n
    · refine .inl ⟨by show some (!w.z) = _; rw [wz, show n - j - 1 = 0 by omega_arith]; rfl, he ▸ cw, kv.trans kw⟩
    · refine .inr ⟨?_, n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, cw, w0, w3, by rw [w1, Nat.sub_sub], kv.trans kw⟩
      show some (!w.z) = _
      have : BitVec.ofNat 32 (n - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      rw [wz]; simpa using this
  refine WP.seq (VG.Arm.WP.mono_syms copy fun v ⟨cv, kv⟩ syv => ?_)
  have r2v : v.gpr .r2 = kb := by rw [kv.gpr _ (by decide), k₃.gpr _ (by decide), g₂' _ (by decide), hkb]
  have r12v : v.gpr .r12 = cb := by rw [kv.gpr _ (by decide), k₃.gpr _ (by decide), c₂]
  have rdv : v.rd = s.rd := by rw [kv.rd, k₃.rd, rd₂]; rfl
  have wrv : v.wr = s.wr := by rw [kv.wr, k₃.wr, wr₂]; rfl
  refine WP.seq ?_
  crun [r2v]
  obtain ⟨w, hw⟩ : ∃ w, (v.setReg .lr kb).setReg .r3 2 = w := ⟨_, rfl⟩
  rw [hw]
  have wlr : w.gpr .lr = kb := by rw [← hw]; rfl
  have w3 : w.gpr .r3 = 2 := by rw [← hw]; rfl
  have w12 : w.gpr .r12 = cb := by rw [← hw]; exact r12v
  have wm : w.mem = v.mem := by rw [← hw]; rfl
  have wwr : w.wr = s.wr := by rw [← hw]; exact wrv
  have wrd : w.rd = s.rd := by rw [← hw]; exact rdv
  have hsw : w.syms = s.syms := by rw [← hw]; exact syv.trans (sy₃.trans sy₂)
  -- The state of key expansion: `x` the padded key, no subkeys yet.
  let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem (State.addr kp) n).getD j 0,
    fun j => M (State.addr cb + BitVec.ofNat 64 (32 + j))⟩
  have ks0 : KS M cb kb w ⟨st0, [], fun i => w.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32⟩ :=
    { r12 := w12
      mem := ⟨fun a i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), by
        rw [wm]; exact cv.fr.mono (by simp)⟩
      ex := fun _ _ => rfl
      len := Nat.zero_le _
      cfit := hcf
      kfit := hKf
      scr := by rw [wwr, hwr]; simp
      sch := by rw [wwr, hwr]; simp
      dKS := dKS
      tfit := by rw [hsw]; exact tfit
      trd := by rw [hsw, wrd]; exact List.mem_append_left _ trd
      held0 := by
        rw [hsw]
        refine held_frame hMf (fun r hr => ?_) (by rw [s5678_len]; decide) held
        simp only [List.mem_singleton] at hr; subst hr
        rw [s5678_len]; exact twr _ (by rw [hwr]; simp)
      dTS := by
        rw [hsw]
        exact twr ⟨State.addr cb, 256⟩ (by rw [hwr]; simp)
      dTK := by rw [hsw]; exact twr _ (by rw [hwr]; simp) }
  case refine_1 =>
    rw [wm]
    cases a with
    | x =>
      rw [show off .x + i = 16 + i from rfl, cv.x i hi]
      show _ = (Spec.Cast5.bytesAt s.mem (State.addr kp) n).getD i 0
      rw [Proof.Cast5.bytesAt_getD]
      split
      · rw [hkM i (by omega_arith)]
      · rfl
    | z => exact cv.z i hi
  -- The halves.
  have halves_loop : WP isa (.loop half .ne) w fun u => ∃ k, KS M cb kb u k ∧ k.xz = (halves st0 2).1 ∧
      k.ws = (halves st0 2).2 ∧ Keep halfRegs w u := by
    refine WP.loop (M := isa) (fun m (u : State) => ∃ hh, m = 2 - hh ∧ hh < 2 ∧ ∃ k, KS M cb kb u k ∧
      k.xz = (halves st0 hh).1 ∧ k.ws = (halves st0 hh).2 ∧ u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) ∧
      u.gpr .r3 = BitVec.ofNat 32 (2 - hh) ∧ Keep halfRegs w u) ?_ 2 w
      ⟨0, rfl, by decide, _, ks0, rfl, rfl, by rw [wlr, Nat.mul_zero, BitVec.add_zero], by rw [w3]; rfl,
        Keep.refl _ _⟩
    rintro m u ⟨hh, rfl, hhh, k, hk, kx, kw, ulr, u3, ku⟩
    refine WP.mono (half_ok hk ulr (by rw [kw, halves_length]) hhh)
      fun x ⟨k', hk', kx', kw', xlr, x3, xz, kh⟩ => ?_
    have nx : k'.xz = (halves st0 (hh + 1)).1 ∧ k'.ws = (halves st0 (hh + 1)).2 := by
      rw [halves_succ, kx', kw', kx, kw]; exact ⟨rfl, rfl⟩
    rw [u3, ofNat_sub_one (by omega_arith) (by omega_arith)] at x3 xz
    by_cases he : hh + 1 = 2
    · exact .inl ⟨by show some (!x.z) = _; rw [xz, show 2 - hh - 1 = 0 by omega_arith]; rfl, k', hk', he ▸ nx.1,
        he ▸ nx.2, ku.trans kh⟩
    · refine .inr ⟨?_, 2 - (hh + 1), by omega_arith, hh + 1, rfl, by omega_arith, k', hk', nx.1, nx.2, xlr,
        by rw [x3, Nat.sub_sub], ku.trans kh⟩
      have : hh = 0 := by omega_arith
      subst this
      show some (!x.z) = _; rw [xz]; rfl
  refine WP.seq (WP.mono halves_loop fun u ⟨k, hk, kxz, kws, ku⟩ => ?_)
  -- The saved registers, restored.
  have hsv : Spill.Saved u.mem (State.addr (u.gpr .r12)) (s.setReg .r12 cb).gpr savedSlots := by
    rw [hk.r12]
    refine (Spill.saveMem_saved _ _ _ _ savedSlots_ok).frame savedSlots_ok ((by rw [← m₂, hM]; exact hk.mem.fr) :
      Frame [⟨State.addr cb, 64⟩, ⟨State.addr kb, 128⟩, ⟨State.addr cb + BitVec.ofNat 64 spillKey, 40⟩]
        (Spill.saveMem (s.setReg .r12 cb).mem (State.addr cb) (s.setReg .r12 cb).gpr savedSlots) u.mem)
      fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (dKS.symm.sub_left (Offset.sub_base _ (by decide)))
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok savedSlots_ok savedSlots_restorable (by rw [hk.r12]; omega_arith)
    (fun d _ hd => by
      rw [ku.rd, ku.wr, wrd, wwr, hwr, hk.r12]
      exact ⟨⟨State.addr cb, 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) hsv)
    fun s' ⟨hg, _, hm, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rw [Spill.restored_reg hg (savedSlots_preserved r hr)]
    exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact absurd hr (by decide))
  · show Spec.Cast5.scheduleAt s'.mem (State.addr (s.gpr .r2)) = _
    rw [hm, hkb, hkp, hnn, scheduleAt_keys hk.mem.keys (by rw [kws, halves_length]), kws,
      Proof.Cast5.expandKey_eq _ st0.z, halves_two]



end VG.Proof.Cast5.Arm

end

end

/-!
# CAST5 key expansion on ARMv7: verified

Constant time by the taint analysis: `r0`–`r3` (the pointers and the key's
length) and the table's address are public, `r3` the working space's base;
the step and half counts and the schedule's pointer are computed from them.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- The initial taint: `r0`–`r3` public, `r3` the base of writable region 1. -/
def τKey : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [128, 256], bases := [(.r3, 1)] }

theorem τKey_wf {s : State} (h : keyArm.pre (stripConsts keyConsts s)) : VG.Arm.Taint.Wf τKey s := by
  obtain ⟨_, hwr, _, _, dKS, _, hKf, hcf, _⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr] at hwr dKS hKf hcf
  refine ⟨fun _ => ⟨by simp [hwr, τKey], by simpa [hwr] using dKS, ?_⟩, fun p hp => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega_arith
  · simp only [τKey, List.mem_singleton] at hp; subst hp
    simp only [VG.Arm.Taint.region, hwr]
    rfl

theorem τKey_agree {s₁ s₂ : State} (h₁ : keyArm.pre (stripConsts keyConsts s₁))
    (h₂ : keyArm.pre (stripConsts keyConsts s₂)) (hp : keyArm.pub s₁ s₂) : VG.Arm.Taint.Agree τKey s₁ s₂ := by
  obtain ⟨_, p0, p1, p2, p3⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τKey_wf h₁, τKey_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (by decide),
    fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [τKey, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · have w₁ := h₁.2.1
    have w₂ := h₂.2.1
    simp only [stripConsts_wr, stripConsts_gpr] at w₁ w₂
    rw [w₁, w₂, p2, p3]

/-- Key expansion's contract with the table, as the proof states it. -/
def keyArmC : Contract isa where
  pre s := keyArm.pre (stripConsts keyConsts s) ∧ ConstsOk keyConsts 0 s
  post := keyArm.post
  pub s₁ s₂ := keyArm.pub s₁ s₂ ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

theorem expandKey_constantTime : ConstantTime isa keyArmC.pre keyArmC.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) τKey (fun _ _ h₁ h₂ hp => ⟨τKey_agree h₁.1 h₂.1 hp.1,
    fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hp.2⟩) (by taint_decide)

theorem keyArmC_correct (s : State) (hs : keyArmC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyArmC.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_correct s hs.1 hs.2
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

/-- A state satisfying the precondition without the table: a key of five bytes. -/
def keySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 5 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 5⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem key_implies : keyArm.Implies (Spec.Cast5.expandKeyContract abi) := by
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, keyArm,
    Spec.Cast5.validKey] [keySat] using keySat

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
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Spec.Cast5.validKey]
  subst e
  rw [hl]
  refine ⟨by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem keyC_implies : keyArmC.Implies (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts keyConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts keyConsts s₁) (stripConsts keyConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
  sat := ⟨keySatC, key_sat⟩

theorem expandKey_verified :
    Verified target expandKey (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) :=
  Verified.of_correct keyArmC_correct expandKey_constantTime keyC_implies

end VG.Proof.Cast5.Arm
