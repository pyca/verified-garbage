import VerifiedGarbage.Proof.Cast5.Arm.KeySteps
import VerifiedGarbage.Proof.Cast5.Arm.Block

/-!
# CAST5 key expansion on ARMv7: a step

`step` chooses the step's bytes by the step's number in `r2` (`sel_ok`),
gathers them into `r4`–`r7` (`gather_ok`), scans `tab5678`, and chooses what
to do with the four values (`postE_ok`, `postL_ok`): the step of the spec's
`stepRun` (`step_ok`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-! ## The chain of comparisons -/

/-- The code chosen by the step's number `j` in `r2`: `cs[j - i]`. -/
theorem sel_ok (cs : List (List Instr)) (i : Nat) {s : State} {j : Nat} (hij : i ≤ j) (hj : j < i + cs.length)
    (hlen : i + cs.length ≤ 256) (h2 : s.gpr .r2 = BitVec.ofNat 32 j) {Q : State → Prop}
    (hQ : ∀ u : State, (∀ r, u.gpr r = s.gpr r) → u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      WP isa (.block (cs.getD (j - i) [])) u Q) :
    WP isa (sel cs i) s Q := by
  induction cs generalizing i s with
  | nil => simp at hj; omega
  | cons c cs ih =>
    unfold sel
    have hiv := toNat_ofNat_lt (j := i) (by simp at hlen; omega)
    have hj256 : j < 256 := by simp at hj hlen; omega
    have hi256 : i < 256 := by simp at hlen; omega
    refine WP.seq ?_
    crun [hiv]
    refine wp_ite_eq (fun hz => ?_) (fun hz => ?_)
    · have hji : j = i := by
        rw [z_sub, h2] at hz
        have h0 := beq_iff_eq.mp hz
        have := congrArg BitVec.toNat h0
        simp at hlen
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega
      subst hji
      have := hQ (putSub s (s.gpr .r2) (BitVec.ofNat 32 j)) (fun r => rfl) rfl rfl rfl rfl
      rwa [Nat.sub_self, List.getD_cons_zero] at this
    · have hne : j ≠ i := by
        intro e; subst e
        rw [z_sub, h2] at hz
        simp at hz
      refine ih (i + 1) (by omega) (by simp at hj; omega) (by simp at hlen ⊢; omega) (by rw [gpr_sub, h2])
        fun u hg hm hrd hwr hsp => ?_
      have := hQ u (fun r => (hg r).trans (gpr_sub _ _ _ _)) hm hrd hwr hsp
      rwa [show j - i = (j - (i + 1)) + 1 by omega, List.getD_cons_succ] at this

/-! ## The state of key expansion -/

/-- The state of key expansion from the memory `m0`: the working space at
`cb` in `r12`, the schedule at `kb`, the arrays, subkeys and extra lookups
of `k` in memory. -/
structure KS (m0 : Mem) (cb kb : BitVec 32) (s : State) (k : KSt) : Prop where
  r12 : s.gpr .r12 = cb
  mem : KMem m0 s.mem (State.addr cb) (State.addr kb) k.xz k.ws
  ex : ∀ i < 4, s.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k.ex i
  len : k.ws.length ≤ 32
  cfit : cb.toNat + 256 ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr cb, 256⟩ : Region) ∈ s.wr
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.wr
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr cb, 256⟩

section
variable {m0 : Mem} {cb kb : BitVec 32} {s : State} {k : KSt} (h : KS m0 cb kb s k)
include h

theorem KS.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (State.addr cb + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by omega)⟩

theorem KS.inS' {off w : Nat} (hw : off + w ≤ 256) :
    InRegions (s.rd ++ s.wr) (State.addr cb + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by omega)⟩

theorem KS.dKS64 : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr cb, 64⟩ :=
  h.dKS.sub_right (Region.sub_prefix (by decide))

/-- The same state, later: other registers, memory and flags. -/
theorem KS.update {u : State} {k' : KSt} (hc : u.gpr .r12 = s.gpr .r12)
    (hm : KMem m0 u.mem (State.addr cb) (State.addr kb) k'.xz k'.ws)
    (he : ∀ i < 4, u.mem.readW (State.addr cb + BitVec.ofNat 64 (extraOff + 4 * i)) 32 = k'.ex i)
    (hl : k'.ws.length ≤ 32) (hwr : u.wr = s.wr) : KS m0 cb kb u k' :=
  ⟨hc.trans h.r12, hm, he, hl, h.cfit, h.kfit, by rw [hwr]; exact h.scr, by rw [hwr]; exact h.sch, h.dKS⟩

end

theorem srcOff_lt {q : Pos} (hq : q.2 < 16) : srcOff q + 1 ≤ 48 := by
  obtain ⟨a, i⟩ := q
  have := off_lt a
  simp only [srcOff] at hq ⊢
  omega

/-! ## Gathering the bytes -/

theorem gather_ok {m0 : Mem} {cb kb : BitVec 32} {s : State} {k : KSt} (h : KS m0 cb kb s k)
    {a b c d : Pos} (ha : a.2 < 16) (hb : b.2 < 16) (hc : c.2 < 16) (hd : d.2 < 16) :
    WP isa (.block (gather a b c d)) s fun u =>
      u.gpr .r4 = (k.xz.get d).setWidth 32 ∧ u.gpr .r5 = (k.xz.get c).setWidth 32 ∧
      u.gpr .r6 = (k.xz.get b).setWidth 32 ∧ u.gpr .r7 = (k.xz.get a).setWidth 32 ∧
      Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  have aS := addr_off h.cfit
  have ia := h.inS' (off := srcOff a) (w := 1) (by have := srcOff_lt ha; omega)
  have ib := h.inS' (off := srcOff b) (w := 1) (by have := srcOff_lt hb; omega)
  have ic := h.inS' (off := srcOff c) (w := 1) (by have := srcOff_lt hc; omega)
  have id := h.inS' (off := srcOff d) (w := 1) (by have := srcOff_lt hd; omega)
  have xa := h.mem.xz.pos ha
  have xb := h.mem.xz.pos hb
  have xc := h.mem.xz.pos hc
  have xd := h.mem.xz.pos hd
  have la : srcOff a < 256 := by have := srcOff_lt ha; omega
  have lb : srcOff b < 256 := by have := srcOff_lt hb; omega
  have lc : srcOff c < 256 := by have := srcOff_lt hc; omega
  have ld : srcOff d < 256 := by have := srcOff_lt hd; omega
  have oa : srcOff a < 4096 := by omega
  have ob : srcOff b < 4096 := by omega
  have oc : srcOff c < 4096 := by omega
  have od : srcOff d < 4096 := by omega
  unfold gather
  crun [h.r12, aS _ la, aS _ lb, aS _ lc, aS _ ld, ia, ib, ic, id, xa, xb, xc, xd, oa, ob, oc, od]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-! ## What a step does with the values -/

theorem ex_off {i : Nat} (hi : i < 4) : extraOff + 4 * i + 4 ≤ 64 := by unfold extraOff; omega

/-- The extra lookups of a group to their slots. -/
theorem postE_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) (a b c d : Pos)
    (v : Nat → Spec.Cast5.Word) (hv : ∀ i < 4, u.gpr (accReg i) = v i) :
    WP isa (.block (Step.extras a b c d).post) u fun w =>
      KS m0 cb kb w { k with ex := v } ∧ Keep [] u w := by
  have aS := addr_off h.cfit
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have v0 : u.gpr .r8 = v 0 := hv 0 (by decide)
  have v1 : u.gpr .r9 = v 1 := hv 1 (by decide)
  have v2 : u.gpr .r10 = v 2 := hv 2 (by decide)
  have v3 : u.gpr .r11 = v 3 := hv 3 (by decide)
  simp only [Step.post]
  unfold extraOff
  crun [h.r12, aS, inS, v0, v1, v2, v3]
  have dKS := h.dKS64
  have hl := h.len
  refine ⟨h.update rfl ?_ (fun i hi => ?_) hl rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · exact (((h.mem.write dKS hl _ (by decide) (by decide)).write dKS hl _ (by decide) (by decide)).write dKS hl _
      (by decide) (by decide)).write dKS hl _ (by decide) (by decide)
  · simp only [extraOff]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
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
  have aS := addr_off h.cfit
  have ho : extraOff + 4 * (8 - e) < 256 := by unfold extraOff; omega
  have ho' : extraOff + 4 * (8 - e) < 4096 := by omega
  have hin := h.inS' (off := extraOff + 4 * (8 - e)) (w := 4) (by unfold extraOff; omega)
  have hx := h.ex (8 - e) (by omega)
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
    have hq4 := hq a q rfl
    have := off_lt a
    have aS := addr_off h.cfit
    have ho : off a + 4 * q < 256 := by omega
    have ho' : off a + 4 * q < 4096 := by omega
    have hin := h.inS' (off := off a + 4 * q) (w := 4) (by omega)
    have hx := h.mem.xz.quad a hq4
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
  have aS := addr_off h.cfit
  have ho : off a + 4 * q < 256 := by omega
  have ho' : off a + 4 * q < 4096 := by omega
  have hin := h.inS (off := off a + 4 * q) (w := 4) (by omega)
  unfold storeCode
  crun [h.r12, aS _ ho, hin, ho', h0, rev_eq]
  refine ⟨h.update rfl (h.mem.quad h.dKS64 h.len a hq v) (fun i hi => ?_) h.len rfl, ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  rw [Mem.readW_writeW_sep (Offset.sep _ (d := extraOff + 4 * i) (n := 32 / 8) (e := off a + 4 * q) (k := 32 / 8)
    (by unfold extraOff; omega) (by unfold extraOff; omega) (by omega)) (by decide)]
  exact h.ex i hi

theorem storeKey_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k : KSt} (h : KS m0 cb kb u k) {j hh : Nat}
    (hj : j < 16) (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen : k.ws.length = 16 * hh + j)
    (hl : k.ws.length < 32) {v : Spec.Cast5.Word} (h0 : u.gpr .r0 = v) :
    WP isa (.block (storeCode (.key j))) u fun w =>
      KS m0 cb kb w { k with ws := k.ws ++ [v] } ∧ Keep [] u w := by
  have hkf := h.kfit
  have ea : State.addr (u.gpr .lr + BitVec.ofNat 32 (4 * j)) = State.addr kb + BitVec.ofNat 64 (4 * k.ws.length) := by
    rw [hlr, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), hlen]
    congr 2; omega
  have hin : InRegions u.wr (State.addr kb + BitVec.ofNat 64 (4 * k.ws.length)) 4 :=
    ⟨_, h.sch, Offset.contains_base _ (by omega) (by omega)⟩
  have ho : 4 * j < 4096 := by omega
  unfold storeCode
  crun [ea, hin, ho, h0]
  refine ⟨h.update rfl (h.mem.key h.dKS64 hl v) (fun i hi => ?_) (by simp; omega) rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [Mem.readW_writeW_sep (h.dKS.symm.sep (Offset.contains_base _ (by have := ex_off hi; omega)
      (by unfold extraOff; omega))
    (Offset.contains_base _ (by omega) (by omega))) (by decide)]
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
  have hv : KS m0 cb kb v k := h.update (vk.gpr _ (by decide)) (by rw [vm]; exact h.mem)
    (fun i hi => by rw [vm]; exact h.ex i hi) h.len vk.wr
  refine WP.mono (wordCode_ok hv l.word hq) fun w ⟨w0, wk, wm⟩ => ?_
  have hw : KS m0 cb kb w k := hv.update (wk.gpr _ (by decide)) (by rw [wm]; exact hv.mem)
    (fun i hi => by rw [wm]; exact hv.ex i hi) hv.len wk.wr
  have wv : w.gpr .r0 = lineE k.xz k.ex l := by
    rw [w0, v0, h8, h9, h10, h11]
    unfold lineE
    clear hq he hok hl hkey h8 h9 h10 h11
    obtain ⟨main, extra, word⟩ := l
    rcases word with _ | ⟨a, q⟩ <;> rfl
  have kuw := vk.trans wk
  cases st with
  | quad a q =>
    have hq4 : q < 4 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    exact WP.mono (storeQuad_ok hw a hq4 wv) fun x ⟨hx, xk⟩ => ⟨hx, kuw.trans (xk.mono (by decide))⟩
  | key j =>
    have hj : j < 16 := by simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    obtain ⟨hlen, hl32⟩ := hkey j rfl
    exact WP.mono (storeKey_ok hw hj (by rw [kuw.gpr _ (by decide)]; exact hlr) hlen hl32 wv)
      fun x ⟨hx, xk⟩ => ⟨hx, kuw.trans (xk.mono (by decide))⟩

end VG.Proof.Cast5.Arm
