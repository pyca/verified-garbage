module

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Dom
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RISC-V: straight-line bitwise code, by evaluation

As on PPC64LE (`Proof/Framework/PPC64LE/Straight.lean`): a block of `ld`,
`sd`, `and`, `or`, `xor`, `andi`, `ori`, `xori`, `mv` (`addi d, n, 0`) and
shifts by immediates on 64-bit registers and on two memory areas
(read-write *slots* `8k(base)`, `k < slots`, and read-only *external words*
`8k(ext)`, `k < exts`), both 8-byte aligned, is evaluated over an abstract
domain (`VG.Bitslice.Dom`) by `eval`. `run` says that the machine then runs
the block without faulting, and that its registers and memory words are
related to the abstract result as they were to the abstract initial values.

RV64I has no rotation: a rotation is two shifts combined by `or` (or `xor`),
`slli t, x, k`, `srli d, x, 64 - k`, `or d, d, t`. A register may therefore
hold a value shifted left or right (`Val.shl`, `Val.shr`) of an abstract
word, and an `or` or `xor` of a word shifted right by `k` and the same word
shifted left by `64 - k` is its rotation right by `k`. That needs the
relation of abstract and concrete words to be a function (`run`'s `hR`),
so that the two shifted words are of the same concrete word. A right shift
of a word is the domain's (`Dom.shr`) when it has one, and a word shifted
left by `k` that is combined with a word is the domain's rotation right by
`64 - k` masked by its constant of the high `64 - k` bits (`shlD`), when it
has those.

The evaluator rejects (`none`) any other instruction, any other memory
operand, any write of the two base registers and any use of an unknown
value.
-/

@[expose] public section

namespace VG.RISCV64.Straight

open VG.Bitslice

/-- The two memory areas: slots `8k(base)` for `k < slots` (read and
written), and external words `8k(ext)` for `k < exts` (only read). -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- What a register holds: an abstract word, or one shifted left or right. -/
inductive Val (α : Type) where
  | v (a : α)
  | shl (a : α) (k : Nat)
  | shr (a : α) (k : Nat)
  deriving DecidableEq, Repr

/-- The abstract values of the registers and slots; `none` if unknown. -/
structure Env (α : Type) where
  reg : Reg → Option (Val α)
  slot : Nat → Option α

variable {α : Type}

def Env.setReg (e : Env α) (d : Reg) (v : Val α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r }

def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α :=
  { e with slot := fun j => if j = k then some v else e.slot j }

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

/-- The slot or external word that `off(b)` addresses, if any. -/
def Cfg.loc (c : Cfg) (b : Reg) (off : Nat) : Option Where :=
  if off < 2048 ∧ off % 8 = 0 then
    if b = c.base ∧ off / 8 < c.slots then some (.slot (off / 8))
    else if b = c.ext ∧ off / 8 < c.exts then some (.ext (off / 8))
    else none
  else none

section
variable (D : Dom α 64) (c : Cfg) (ext : Nat → Option α)

def binop : LogicOp → α → α → Option α
  | .xor => D.xor
  | .and => D.and
  | .or => D.or

/-- A word shifted left by `0 < k < 64`, in the domain: its rotation right
by `64 - k`, masked by the constant of the `64 - k` high bits. -/
def shlD (k : Nat) (a : α) : Option α :=
  if 0 < k ∧ k < 64 then
    (D.ror (64 - k) a).bind fun r => (D.const (BitVec.allOnes 64 <<< k)).bind (D.and r)
  else none

/-- A logical operation on two register values: of abstract words, of an
abstract word and one shifted left (`shlD`), or (`or` or `xor`) of a word
shifted right by `k` and the same word shifted left by `64 - k` (its
rotation right by `k`, whose two parts do not overlap). -/
def combine [DecidableEq α] (op : LogicOp) : Val α → Val α → Option α
  | .v a, .v b => binop D op a b
  | .shr a k, .shl b k' => if op ≠ .and ∧ a = b ∧ 0 < k ∧ k < 64 ∧ k' = 64 - k then D.ror k a else none
  | .shl b k', .shr a k => if op ≠ .and ∧ a = b ∧ 0 < k ∧ k < 64 ∧ k' = 64 - k then D.ror k a else none
  | .v a, .shl b k => (shlD D k b).bind (binop D op a)
  | .shl b k, .v a => (shlD D k b).bind fun c => binop D op c a
  | _, _ => none

/-- A shift of a register value by `0 < k < 64`. -/
def shiftV : ShiftOp → Nat → Val α → Option (Val α)
  | .sll, k, .v a => some (.shl a k)
  | .srl, k, .v a => some ((D.shr k a).elim (.shr a k) .v)
  | _, _, _ => none

/-- The instruction's effect on the abstract values. -/
def step [DecidableEq α] (e : Env α) : Instr → Option (Env α)
  | .load .d d b off =>
    if d = c.base ∨ d = c.ext then none else
    match c.loc b off with
    | some (.slot k) => (e.slot k).map (e.setReg d ∘ .v)
    | some (.ext k) => (ext k).map (e.setReg d ∘ .v)
    | none => none
  | .store .d r b off => match c.loc b off, e.reg r with
    | some (.slot k), some (.v a) => some (e.setSlot k a)
    | _, _ => none
  | .logic op d n m =>
    if d = c.base ∨ d = c.ext then none else
    match e.reg n, e.reg m with
    | some a, some b => (combine D op a b).map (e.setReg d ∘ .v)
    | _, _ => none
  | .logicImm op d n imm =>
    if d = c.base ∨ d = c.ext ∨ ¬ imm12 imm then none else
    match e.reg n, D.const (BitVec.ofInt 64 imm) with
    | some (.v a), some b => (binop D op a b).map (e.setReg d ∘ .v)
    | _, _ => none
  | .shift op .d d n sh =>
    if d = c.base ∨ d = c.ext ∨ ¬(0 < sh ∧ sh < 64) then none else
    match e.reg n with
    | some a => (shiftV D op sh a).map (e.setReg d)
    | none => none
  | .addi d n 0 =>
    if d = c.base ∨ d = c.ext then none else (e.reg n).map (e.setReg d)
  | _ => none

/-- The block's effect on the abstract values. -/
def eval [DecidableEq α] : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c ext e i).bind (eval is)

/-- Evaluates the block and checks `post` of the result: for `decide`. -/
def check [DecidableEq α] (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c ext is e with
  | some e' => post e'
  | none => false

theorem of_check [DecidableEq α] {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c ext is e post = true) : ∃ e', eval D c ext is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` (or external word `k`) of the base address `b`. -/
abbrev wordAddr (b : Addr) (k : Nat) : Addr := b + BitVec.ofNat 64 (8 * k)

/-- A register value related to a concrete word. -/
def ValRel (R : α → BitVec 64 → Prop) : Val α → BitVec 64 → Prop
  | .v a, x => R a x
  | .shl a k, x => ∃ y, R a y ∧ x = y <<< k
  | .shr a k, x => ∃ y, R a y ∧ x = y >>> k

/-- The machine state's registers, slots and external words are related by
`R` to the abstract ones that are known. -/
structure Rel (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e : Env α)
    (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ValRel R a (s.gpr r)
  slot : ∀ k a, k < c.slots → e.slot k = some a →
    R a (s.mem.readW (wordAddr (s.gpr c.base) k) 64)
  ext : ∀ k a, k < c.exts → ext k = some a → R a (s.mem.readW (wordAddr (s.gpr c.ext) k) 64)

/-- What the machine needs for the memory areas: they are accessible and
8-byte aligned, the slots do not wrap around, and the external words do
not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (wordAddr (s.gpr c.base) k) 8
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.ext) k) 8
  baseAl : (s.gpr c.base).toNat % 8 = 0
  extAl : (s.gpr c.ext).toNat % 8 = 0
  slots : 8 * c.slots < 2 ^ 64
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (wordAddr (s.gpr c.base) k) 8 (wordAddr (s.gpr c.ext) j) 8

/-- The slot area. -/
def slotRegion (c : Cfg) (s : State) : Region := ⟨s.gpr c.base, 8 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  baseAl := by rw [hb]; exact h.baseAl
  extAl := by rw [he]; exact h.extAl
  slots := h.slots
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem slot_sep (b : Addr) {j k : Nat} (hj : 8 * j < 2 ^ 64) (hk : 8 * k < 2 ^ 64) (h : j ≠ k) :
    Mem.Sep (wordAddr b j) 8 (wordAddr b k) 8 := by
  intro x h₁ h₂
  simp only [wordAddr, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (x - b).isLt
  omega

theorem slot_contains (b : Addr) {n k : Nat} (hk : k < n) (hn : 8 * n < 2 ^ 64) :
    (⟨b, 8 * n⟩ : Region).Contains (wordAddr b k) (64 / 8) := by
  simp only [Region.Contains, wordAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word at an 8-byte aligned offset of an 8-byte aligned base is aligned. -/
theorem wordAddr_al {b : Addr} (hb : b.toNat % 8 = 0) (k : Nat) (hk : 8 * k < 2048) :
    (wordAddr b k).toNat % 8 = 0 := by
  simp only [wordAddr]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega)]
  have := b.isLt
  omega

theorem loc_some_slot {c : Cfg} {b : Reg} {off k : Nat} (h : c.loc b off = some (.slot k)) :
    b = c.base ∧ off = 8 * k ∧ off < 2048 ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega, h1.1, h2.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_some_ext {c : Cfg} {b : Reg} {off k : Nat} (h : c.loc b off = some (.ext k)) :
    b = c.ext ∧ off = 8 * k ∧ off < 2048 ∧ k < c.exts := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega, h1.1, h2.2⟩
      · cases h
  · cases h

section
variable [DecidableEq α] {D : Dom α 64} {R : α → BitVec 64 → Prop} {c : Cfg} {ext : Nat → Option α}

/-- The facts about one step, and so about a block. -/
structure Post (R : α → BitVec 64 → Prop) (c : Cfg) (ext : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : Reg → Prop) : Prop where
  rel : Rel R c ext e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

omit [DecidableEq α] in
theorem Post.writes {e' : Env α} {s s' : State} {W W' : Reg → Prop}
    (p : Post R c ext e' s s' W) (h : ∀ r, W r → W' r) : Post R c ext e' s s' W' :=
  { p with other := fun r hr => p.other r fun hw => hr (h r hw) }

omit [DecidableEq α] in
theorem post_write {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) {d : Reg}
    {a : Val α} {v : BitVec 64} (hv : ValRel R a v) (hb : d ≠ c.base) (he : d ≠ c.ext) :
    Post R c ext (e.setReg d a) s (s.write d v) (· = d) := by
  have hbase : (s.write d v).gpr c.base = s.gpr c.base := by
    simp [State.write, Ne.symm hb]
  have hext : (s.write d v).gpr c.ext = s.gpr c.ext := by
    simp [State.write, Ne.symm he]
  refine ⟨⟨fun r b h => ?_, fun k b hk h => ?_, fun k b hk h => ?_⟩,
    hok.congr hbase hext rfl rfl, rfl, rfl, rfl, hbase, hext, fun r hr => ?_, Frame.refl _ _⟩
  · simp only [Env.setReg, State.write] at h ⊢
    split at h
    · cases h; simp_all
    · simp_all [hrel.reg r b h]
  · rw [hbase]; exact hrel.slot k b hk h
  · rw [hext]; exact hrel.ext k b hk h
  · simp [State.write, hr]

/-- The destination of the instructions `eval` accepts. -/
def dst : Instr → Option Reg
  | .load _ d _ _ => some d
  | .logic _ d _ _ => some d
  | .logicImm _ d _ _ => some d
  | .shift _ _ d _ _ => some d
  | .addi d _ _ => some d
  | _ => none

/-- A logical operation on words. -/
def lop : LogicOp → BitVec 64 → BitVec 64 → BitVec 64
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y

theorem lop_eq (op : LogicOp) (x y : BitVec 64) :
    (match op with | .and => x &&& y | .or => x ||| y | .xor => x ^^^ y) = lop op x y := by
  cases op <;> rfl

omit [DecidableEq α] in
theorem binop_sound (hD : D.Sound R) {op : LogicOp} {a b r : α} {x y : BitVec 64} (ha : R a x)
    (hb : R b y) (h : binop D op a b = some r) : R r (lop op x y) := by
  cases op <;> simp only [binop] at h
  · exact hD.and ha hb h
  · exact hD.or ha hb h
  · exact hD.xor ha hb h

/-- A word shifted right by `k` with the same word shifted left by `64 - k`. -/
theorem shr_shl (y : BitVec 64) {k : Nat} (hk : 0 < k) (hk' : k < 64) {op : LogicOp} (hop : op ≠ .and) :
    lop op (y >>> k) (y <<< (64 - k)) = y.rotateRight k := by
  have e : y.rotateRight k = y >>> k ||| y <<< (64 - k) := by
    rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hk']
  rw [e]
  cases op
  · exact absurd rfl hop
  · rfl
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lop, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft]
    by_cases h : i < 64 - k
    · simp [h]
    · simp [h, hi, BitVec.getLsbD_of_ge y (k + i) (by omega)]

theorem lop_comm {op : LogicOp} (hop : op ≠ .and) (x y : BitVec 64) : lop op x y = lop op y x := by
  cases op
  · exact absurd rfl hop
  · exact BitVec.or_comm _ _
  · exact BitVec.xor_comm _ _

/-- A left shift is a rotation masked by the high bits. -/
theorem ror_and_shl (y : BitVec 64) {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    y.rotateRight (64 - k) &&& BitVec.allOnes 64 <<< k = y <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt (show 64 - k < 64 by omega)]
  by_cases h : i < k
  · simp [h]
  · have e : i - (64 - (64 - k)) = i - k := by omega
    simp [h, hi, show ¬ i < 64 - (64 - k) by omega, e, show i - k < 64 by omega]

omit [DecidableEq α] in
theorem shlD_sound (hD : D.Sound R) {k : Nat} {b r : α} {y : BitVec 64} (hb : R b y)
    (h : shlD D k b = some r) : R r (y <<< k) := by
  unfold shlD at h
  split at h
  · rename_i hk
    obtain ⟨r₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, h₂, h⟩ := Option.bind_eq_some_iff.mp h
    rw [← ror_and_shl y hk.1 hk.2]
    exact hD.and (hD.ror hb h₁) (hD.const h₂) h
  · cases h

theorem combine_sound (hD : D.Sound R) (hR : ∀ a x y, R a x → R a y → x = y) {op : LogicOp}
    {a b : Val α} {r : α} {x y : BitVec 64} (ha : ValRel R a x) (hb : ValRel R b y)
    (h : combine D op a b = some r) : R r (lop op x y) := by
  cases a <;> cases b <;> simp only [combine, reduceCtorEq] at h
  · exact binop_sound hD ha hb h
  · obtain ⟨c, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y₁, h₂, rfl⟩ := hb
    exact binop_sound hD ha (shlD_sound hD h₂ h₁) h
  · obtain ⟨c, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y₁, h₂, rfl⟩ := ha
    exact binop_sound hD (shlD_sound hD h₂ h₁) hb h
  · split at h
    · rename_i hc
      obtain ⟨hop, rfl, hk, hk', rfl⟩ := hc
      obtain ⟨y₁, h₁, rfl⟩ := ha
      obtain ⟨y₂, h₂, rfl⟩ := hb
      rw [← hR _ _ _ h₁ h₂, lop_comm hop, shr_shl y₁ hk hk' hop]
      exact hD.ror h₁ h
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨hop, rfl, hk, hk', rfl⟩ := hc
      obtain ⟨y₁, h₁, rfl⟩ := ha
      obtain ⟨y₂, h₂, rfl⟩ := hb
      rw [← hR _ _ _ h₁ h₂, shr_shl y₁ hk hk' hop]
      exact hD.ror h₁ h
    · cases h

/-- A shift of a word. -/
def sop : ShiftOp → BitVec 64 → Nat → BitVec 64
  | .sll, x, k => x <<< k
  | .srl, x, k => x >>> k
  | .sra, x, k => x.sshiftRight k

theorem exec_logic' {op : LogicOp} {s : State} {d n m : Reg} :
    exec (.logic op d n m) s = some (s.write d (lop op (s.gpr n) (s.gpr m))) := by
  cases op <;> rfl

theorem exec_logicImm' {op : LogicOp} {s : State} {d n : Reg} {imm : Int} (h : imm12 imm) :
    exec (.logicImm op d n imm) s = some (s.write d (lop op (s.gpr n) (BitVec.ofInt 64 imm))) := by
  rw [exec_logicImm h]; cases op <;> rfl

theorem exec_shift' {op : ShiftOp} {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.shift op .d d n sh) s = some (s.write d (sop op (s.gpr n) sh)) := by
  rw [exec_shift_d h]; cases op <;> rfl

omit [DecidableEq α] in
theorem shiftV_sound (hD : D.Sound R) {op : ShiftOp} {k : Nat} {a b : Val α} {x : BitVec 64}
    (ha : ValRel R a x) (h : shiftV D op k a = some b) : ValRel R b (sop op x k) := by
  cases op <;> cases a <;> simp only [shiftV, reduceCtorEq] at h
  · cases h; exact ⟨_, ha, rfl⟩
  · rename_i a
    cases hs : D.shr k a with
    | none => rw [hs] at h; cases h; exact ⟨_, ha, rfl⟩
    | some c => rw [hs] at h; cases h; exact hD.shr ha hs

theorem step_ok (hD : D.Sound R) (hR : ∀ a x y, R a x → R a y → x = y) {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c ext e s) {i : Instr} (h : step D c ext e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c ext e' s s' (fun r => dst i = some r) := by
  cases i with
  | load sz d b off =>
    cases sz
    case b | h | w => simp [step] at h
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hoff, ho, hlt⟩ := loc_some_slot hk
        subst hb hoff
        obtain ⟨r, hr, hc⟩ := hok.slotIn k hlt
        have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr c.base) k) 8 :=
          ⟨r, List.mem_append_right _ hr, hc⟩
        refine ⟨_, exec_load_d ho (wordAddr_al hok.baseAl k ho) hin, ?_⟩
        exact (post_write (a := .v a) hok hrel (hrel.slot k a hlt ha) hd.1 hd.2).writes
          fun r h => by simp [dst, h]
      · rename_i k hk
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hoff, ho, hlt⟩ := loc_some_ext hk
        subst hb hoff
        refine ⟨_, exec_load_d ho (wordAddr_al hok.extAl k ho) (hok.extIn k hlt), ?_⟩
        exact (post_write (a := .v a) hok hrel (hrel.ext k a hlt ha) hd.1 hd.2).writes
          fun r h => by simp [dst, h]
      · cases h
  | store sz r b off =>
    cases sz
    case b | h | w => simp [step] at h
    simp only [step] at h
    split at h
    · rename_i k a hk ha
      cases h
      obtain ⟨hb, hoff, ho, hlt⟩ := loc_some_slot hk
      subst hb hoff
      have hin := hok.slotIn k hlt
      refine ⟨_, exec_store_d ho (wordAddr_al hok.baseAl k ho) hin, ?_⟩
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (wordAddr (s.gpr c.base) j) (64 / 8)
          (wordAddr (s.gpr c.base) k) (64 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.slots; omega) (by have := hok.slots; omega) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_⟩,
        hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · simp only [Env.setSlot] at hjb
        split at hjb
        · rename_i hjk
          subst hjk
          rw [← Option.some.inj hjb]
          simpa [Mem.readW_writeW_self64, ValRel] using hrel.reg r _ ha
        · rename_i hjk
          rw [Mem.readW_writeW_sep (hsep j hj hjk) (by decide)]
          exact hrel.slot j b hj hjb
      · have hs : Mem.Sep (wordAddr (s.gpr c.ext) j) (64 / 8) (wordAddr (s.gpr c.base) k) (64 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        rw [Mem.readW_writeW_sep hs (by decide)]
        exact hrel.ext j b hj hjb
      · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (slot_contains _ hlt hok.slots)
    · cases h
  | logic op d n m =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or] at hd
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_logic', ?_⟩
        exact (post_write (a := .v r) hok hrel
          (combine_sound hD hR (hrel.reg n a ha) (hrel.reg m b hb) hr) hd.1 hd.2).writes
          fun r' h => by simp [dst, h]
      · cases h
  | logicImm op d n imm =>
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or, Classical.not_not] at hd
      obtain ⟨hdb, hde, himm⟩ := hd
      split at h
      · rename_i a b ha hb
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_logicImm' himm, ?_⟩
        exact (post_write (a := .v r) hok hrel
          (binop_sound hD (hrel.reg n _ ha) (hD.const hb) hr) hdb hde).writes
          fun r' h => by simp [dst, h]
      · cases h
  | shift op sz d n sh =>
    cases sz
    case w => simp [step] at h
    simp only [step] at h
    split at h
    · cases h
    · rename_i hd
      simp only [not_or, Classical.not_not] at hd
      obtain ⟨hdb, hde, hsh⟩ := hd
      split at h
      · rename_i a ha
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_shift' hsh.2, ?_⟩
        exact (post_write hok hrel (shiftV_sound hD (hrel.reg n a ha) hr) hdb hde).writes
          fun r' h => by simp [dst, h]
      · cases h
  | addi d n imm =>
    by_cases h0 : imm = 0
    · subst h0
      simp only [step] at h
      split at h
      · cases h
      · rename_i hd
        simp only [not_or] at hd
        obtain ⟨hdb, hde⟩ := hd
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_addi (by decide), ?_⟩
        rw [show BitVec.ofInt 64 0 = 0 from rfl, show s.gpr n + 0 = s.gpr n from BitVec.add_zero _]
        exact (post_write hok hrel (hrel.reg n a ha) hdb hde).writes fun r h => by simp [dst, h]
    · simp [step, h0] at h
  | _ => simp [step] at h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) (hR : ∀ a x y, R a x → R a y → x = y) {is : List Instr} {e e' : Env α}
    {s : State} (hok : Ok c s) (hrel : Rel R c ext e s) (h : eval D c ext is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c ext e' s s' (fun r => (is.all fun i => dst i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hR hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.sp.trans p₁.sp,
      p.base.trans p₁.base, p.ext.trans p₁.ext, fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

end VG.RISCV64.Straight
