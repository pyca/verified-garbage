module

public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
public import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: an evaluator of SSE2 code, as `Straight` is of code on the general-purpose registers

/-!
# x86 (32-bit): straight-line bitwise SSE2 code, by evaluation

As `Straight`, for the 128-bit `xmm` registers of two-operand SSE2 code: a
block of `pxor`, `pand`, `por`, `movdqa`, quadword shifts (`psllq`,
`psrlq`), shuffles of dwords and words (`pshufd`, `pshuflw`, `pshufhw`,
`punpcklqdq`), and `movdqu` loads and stores of 16-byte *slots* `[base +
16k]` and loads of *external words* `[ext + 16k]` is evaluated over an
abstract domain on 128-bit words (`Bitslice.Dom`). A constant is made by
`mov r, v`, `movd x, r` and a shuffle. Unlike x86-64's `StraightX`, which
follows each quadword apart, a value is the whole register, so that the
shuffles may move bits between quadwords: each is an XOR of rotations of
the register, masked (`permD`).

The environment's registers and slots are lists, written with `List.set`,
so that the kernel evaluates each once. `linear_ok` is `Linear.lean`'s for
this evaluator: a linear layer, checked on words of atoms.
-/

@[expose] public section

namespace VG.X86.StraightX

open VG.Bitslice

/-- The two memory areas: slots `[base + 16k]` for `k < slots` (read and
written), and external words `[ext + 16k]` for `k < exts` (only read). -/
structure Cfg where
  base : Reg
  slots : Nat
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the registers, slots and external words (`none`
if unknown), and the constants of general-purpose registers. -/
structure Env (α : Type) where
  regs : List (Option α) := List.replicate 8 none
  slots : List (Option α)
  ext : List (Option α) := []
  gc : List (Option (BitVec 32)) := List.replicate 8 none

variable {α : Type}

def Env.reg (e : Env α) (r : XReg) : Option α := e.regs.getD r.ctorIdx none
def Env.slot (e : Env α) (k : Nat) : Option α := e.slots.getD k none
def Env.gcOf (e : Env α) (r : Reg) : Option (BitVec 32) := e.gc.getD r.ctorIdx none
def Env.setReg (e : Env α) (d : XReg) (v : α) : Env α := { e with regs := e.regs.set d.ctorIdx (some v) }
def Env.setSlot (e : Env α) (k : Nat) (v : α) : Env α := { e with slots := e.slots.set k (some v) }
def Env.setGc (e : Env α) (d : Reg) (v : BitVec 32) : Env α := { e with gc := e.gc.set d.ctorIdx (some v) }

theorem getD_set {β : Type} {l : List (Option β)} {i j : Nat} {a b : β}
    (h : (l.set i (some a)).getD j none = some b) : (i = j ∧ a = b) ∨ (i ≠ j ∧ l.getD j none = some b) := by
  by_cases hij : i = j
  · subst hij
    refine .inl ⟨rfl, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self'] at h
    cases hl : l[i]? <;> simp [hl] at h
    exact h
  · refine .inr ⟨hij, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij] at h
    rwa [List.getD_eq_getElem?_getD]

theorem xidx_inj {a b : XReg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

theorem ridx_inj {a b : Reg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- Where a memory operand points. -/
inductive Where
  | slot (k : Nat)
  | ext (k : Nat)
  deriving DecidableEq

def Cfg.loc (c : Cfg) (m : MemOp) : Option Where :=
  if m.disp % 16 = 0 then
    if m.base = c.base ∧ m.disp / 16 < c.slots then some (.slot (m.disp / 16))
    else if m.base = c.ext ∧ m.disp / 16 < c.exts then some (.ext (m.disp / 16))
    else none
  else none

/-! ## Moving chunks of a word -/

/-- All ones in the chunks `k < n` of `s` bits with `p k`. -/
def chunkMask (s : Nat) (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => chunkMask s p n ||| (if p n then (2 ^ s - 1) <<< (s * n) else 0)

theorem testBit_chunkMask {s : Nat} (p : Nat → Bool) (hs : 0 < s) (n i : Nat) :
    (chunkMask s p n).testBit i = (decide (i / s < n) && p (i / s)) := by
  induction n with
  | zero => simp [chunkMask]
  | succ n ih =>
    simp only [chunkMask, Nat.testBit_or, ih]
    have hd := Nat.div_add_mod i s
    have hm := Nat.mod_lt i hs
    have key : ((2 ^ s - 1) <<< (s * n)).testBit i = decide (i / s = n) := by
      simp only [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases h : i / s = n
      · subst h
        simp only [decide_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> omega_using [hd, hm]
      · simp only [h, decide_false]
        by_cases h2 : s * n ≤ i
        · have : n ≤ i / s := (Nat.le_div_iff_mul_le hs).mpr (by rw [Nat.mul_comm]; exact h2)
          have h3 : s * (n + 1) ≤ i := Nat.le_trans
            (Nat.mul_le_mul_left s (by omega_using [this, h])) (Nat.mul_div_le i s)
          rw [Nat.mul_add, Nat.mul_one] at h3
          simp [show ¬ i - s * n < s by omega_using [h3]]
        · simp [h2]
    by_cases hp : p n
    · rw [ite_eq_left hp, key]
      by_cases h : i / s = n
      · subst h; simp [hp]
      · simp [h, show (i / s < n + 1) = (i / s < n) by
          apply propext; constructor <;> intro h' <;> omega_using [h, h']]
    · rw [ite_eq_right hp]
      by_cases h : i / s = n
      · subst h; simp [hp]
      · simp [show (i / s < n + 1) = (i / s < n) by
          apply propext; constructor <;> intro h' <;> omega_using [h, h']]

section
variable (D : Dom α 128) (c : Cfg)

/-- The chunks `k < n` (of `s` bits, `s * n = 128`) with `sel k`, each the
chunk `o k` of `a`, the other chunks zero: an XOR of `a` rotated by each
number `r` of chunks in the list, masked by the chunks it brings in place. -/
def permD (s n : Nat) (sel : Nat → Bool) (o : Nat → Nat) (a : α) : List Nat → Option α
  | [] => D.const 0
  | r :: rs =>
    let M := chunkMask s (fun k => sel k && o k == (k + r) % n) n
    if M = 0 then permD s n sel o a rs else
    (D.ror (s * r) a).bind fun t => (D.const (BitVec.ofNat 128 M)).bind fun v => (D.and t v).bind fun u =>
      (permD s n sel o a rs).bind fun w => D.xor u w

/-- The value `permD` follows. -/
def permV (s n : Nat) (sel : Nat → Bool) (o : Nat → Nat) (x : BitVec 128) : List Nat → BitVec 128
  | [] => 0
  | r :: rs => (x.rotateRight (s * r) &&&
      BitVec.ofNat 128 (chunkMask s (fun k => sel k && o k == (k + r) % n) n)) ^^^ permV s n sel o x rs

/-- The dword a shuffle of dwords by `o` puts in dword `k`. -/
def shufOf (o : BitVec 8) (k : Nat) : Nat := (o.extractLsb' (2 * k) 2).toNat

def lowOf (o : BitVec 8) (k : Nat) : Nat := if k < 4 then shufOf o k else k
def highOf (o : BitVec 8) (k : Nat) : Nat := if k < 4 then k else 4 + shufOf o (k - 4)

/-- The instruction's effect on the abstract values. -/
def step (e : Env α) : Instr → Option (Env α)
  | .xop (.bin .movdqa d r) => (e.reg r).map (e.setReg d)
  | .xop (.bin .punpcklqdq d r) =>
    match e.reg d, e.reg r with
    | some x, some y => (permD D 64 2 (· == 0) (fun k => k) x [0]).bind fun u =>
        (permD D 64 2 (· == 1) (fun _ => 0) y [1]).bind fun v => (D.xor u v).map (e.setReg d)
    | _, _ => none
  | .xop (.bin .pxor d r) =>
    match e.reg d, e.reg r with
    | some x, some y => (D.xor x y).map (e.setReg d)
    | _, _ => none
  | .xop (.bin .pand d r) =>
    match e.reg d, e.reg r with
    | some x, some y => (D.and x y).map (e.setReg d)
    | _, _ => none
  | .xop (.bin .por d r) =>
    match e.reg d, e.reg r with
    | some x, some y => (D.or x y).map (e.setReg d)
    | _, _ => none
  | .xop (.shift op d n) =>
    if 1 ≤ n.toNat ∧ n.toNat ≤ 63 then
      match op, e.reg d with
      | .psrlq, some a => (D.ror n.toNat a).bind fun t =>
          (D.const (BitVec.ofNat 128 (rep 64 (2 ^ (64 - n.toNat) - 1) 1))).bind fun m =>
          (D.and t m).map (e.setReg d)
      | .psllq, some a => (D.ror (128 - n.toNat) a).bind fun t =>
          (D.const (BitVec.ofNat 128 (rep 64 ((2 ^ (64 - n.toNat) - 1) <<< n.toNat) 1))).bind fun m =>
          (D.and t m).map (e.setReg d)
      | _, _ => none
    else none
  | .xop (.pshufd d r o) => (e.reg r).bind fun a =>
      (permD D 32 4 (fun _ => true) (shufOf o) a [0, 1, 2, 3]).map (e.setReg d)
  | .xop (.pshuflw d r o) => (e.reg r).bind fun a =>
      (permD D 16 8 (fun _ => true) (lowOf o) a [0, 1, 2, 3, 4, 5, 6, 7]).map (e.setReg d)
  | .xop (.pshufhw d r o) => (e.reg r).bind fun a =>
      (permD D 16 8 (fun _ => true) (highOf o) a [0, 1, 2, 3, 4, 5, 6, 7]).map (e.setReg d)
  | .xop (.movd d r) => (e.gcOf r).bind fun v => (D.const ((0 : BitVec 96) ++ v)).map (e.setReg d)
  | .movdquLoad d m => match c.loc m with
    | some (.slot k) => (e.slot k).map (e.setReg d)
    | some (.ext k) => (e.ext.getD k none).map (e.setReg d)
    | none => none
  | .movdquStore m r => match c.loc m with
    | some (.slot k) => (e.reg r).map (e.setSlot k)
    | _ => none
  | .mov d (.imm v) => if d = c.base ∨ d = c.ext then none else some (e.setGc d v)
  | _ => none

/-- The block's effect on the abstract values. -/
def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c e i).bind (eval is)

/-- Evaluates the block and checks `post` of the result: for `decide`. -/
def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c is e post = true) : ∃ e', eval D c is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## The bits of the shuffles -/

theorem rot_idx {s n i r : Nat} (hsn : s * n = 128) (hk : i / s < n) (hs : 0 < s) :
    (i + s * r) % 128 = s * ((i / s + r) % n) + i % s := by
  have hn : 0 < n := by omega_using [hk]
  have e : i + s * r = 128 * ((i / s + r) / n) + (s * ((i / s + r) % n) + i % s) := by
    have h1 := Nat.div_add_mod i s
    have h2 := Nat.div_add_mod (i / s + r) n
    rw [← hsn, Nat.mul_assoc, ← Nat.add_assoc, ← Nat.mul_add, h2, Nat.mul_add]
    omega_using [h1]
  have hlt : s * ((i / s + r) % n) + i % s < 128 := by
    have h1 : s * ((i / s + r) % n + 1) ≤ s * n := Nat.mul_le_mul_left s (Nat.mod_lt _ hn)
    rw [Nat.mul_add, Nat.mul_one, hsn] at h1
    have h2 := Nat.mod_lt i hs
    omega_using [h1, h2]
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem getLsbD_permV {s n : Nat} (hs : 0 < s) (hsn : s * n = 128) {sel : Nat → Bool} {o : Nat → Nat}
    (ho : ∀ k < n, o k < n) (x : BitVec 128) (rs : List Nat) (hnd : rs.Nodup) (hlt : ∀ r ∈ rs, r < n) {i : Nat}
    (hi : i < 128) :
    (permV s n sel o x rs).getLsbD i =
      (sel (i / s) && decide ((o (i / s) + n - i / s) % n ∈ rs) && x.getLsbD (s * o (i / s) + i % s)) := by
  have hk : i / s < n := (Nat.div_lt_iff_lt_mul hs).mpr (by rw [Nat.mul_comm, hsn]; exact hi)
  have hok := ho _ hk
  have hd := Nat.div_add_mod i s
  have hm := Nat.mod_lt i hs
  induction rs with
  | nil => simp [permV]
  | cons r rs ih =>
    simp only [List.nodup_cons] at hnd
    have hr : r < n := hlt r (List.mem_cons_self)
    have hrot : (x.rotateRight (s * r)).getLsbD i = x.getLsbD ((i + s * r) % 128) :=
      getLsbD_rotateRight_lt x (s * r) i hi
    simp only [permV, BitVec.getLsbD_xor, BitVec.getLsbD_and, hrot, BitVec.getLsbD_ofNat, hi, decide_true,
      Bool.true_and, testBit_chunkMask _ hs, hk, ih hnd.2 (fun r h => hlt r (List.mem_cons_of_mem _ h)),
      List.mem_cons]
    have hiff : (o (i / s) = (i / s + r) % n) ↔ ((o (i / s) + n - i / s) % n = r) := by
      generalize i / s = k at *
      generalize o k = y at *
      rcases Nat.lt_or_ge (k + r) n with h | h
      · rw [Nat.mod_eq_of_lt h]
        constructor
        · intro e; rw [e, show k + r + n - k = r + n by omega_using [], Nat.add_mod_right, Nat.mod_eq_of_lt hr]
        · intro e
          rcases Nat.lt_or_ge (y + n - k) n with h1 | h1
          · rw [Nat.mod_eq_of_lt h1] at e; omega_using [e, h, h1, hok, hk]
          · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega_using [hok, hk, h1])] at e
            omega_using [e, h1, hk]
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega_using [hk, hr, h])]
        constructor
        · intro e
          rw [e, show k + r - n + n - k = r by omega_using [h], Nat.mod_eq_of_lt hr]
        · intro e
          rcases Nat.lt_or_ge (y + n - k) n with h1 | h1
          · rw [Nat.mod_eq_of_lt h1] at e; omega_using [e, h, h1, hk]
          · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega_using [hok, hk, h1])] at e
            omega_using [e, h, h1, hk, hok]
    by_cases hsel : sel (i / s)
    · by_cases he : (o (i / s) + n - i / s) % n = r
      · have he' := hiff.mpr he
        have hidx : (i + s * r) % 128 = s * o (i / s) + i % s := by
          rw [he']; exact rot_idx hsn hk hs
        have hnm : r ∉ rs := hnd.1
        rw [hidx]
        simp [hsel, he, ← he', hnm]
      · simp [hsel, he, show (o (i / s) == (i / s + r) % n) = false from beq_eq_false_iff_ne.mpr fun h => he (hiff.mp h)]
    · simp [hsel]

/-- Every rotation is in the list, so the chunk is found. -/
theorem getLsbD_permV_all {s n : Nat} (hs : 0 < s) (hn : 0 < n) (hsn : s * n = 128) {sel : Nat → Bool}
    {o : Nat → Nat} (ho : ∀ k < n, o k < n) (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (permV s n sel o x (List.range n)).getLsbD i = (sel (i / s) && x.getLsbD (s * o (i / s) + i % s)) := by
  rw [getLsbD_permV hs hsn ho x _ List.nodup_range (fun r h => List.mem_range.mp h) hi,
    decide_eq_true (List.mem_range.mpr (Nat.mod_lt _ hn)), Bool.and_true]

theorem shufOf_lt (o : BitVec 8) (k : Nat) : shufOf o k < 4 := (o.extractLsb' (2 * k) 2).isLt

theorem bit_dword (x : BitVec 128) (i : Nat) : x.getLsbD i = (dword x (i / 32)).getLsbD (i % 32) := by
  rw [getLsbD_dword, decide_eq_true (Nat.mod_lt i (by decide)), Bool.true_and, Nat.div_add_mod]

theorem bit_word (x : BitVec 128) (i : Nat) : x.getLsbD i = (word x (i / 16)).getLsbD (i % 16) := by
  rw [getLsbD_word _ _ _ (Nat.mod_lt i (by decide)), Nat.div_add_mod]

theorem dword_bit (x : BitVec 128) (k i : Nat) : (dword x k).getLsbD (i % 32) = x.getLsbD (32 * k + i % 32) := by
  rw [getLsbD_dword, decide_eq_true (Nat.mod_lt i (by decide)), Bool.true_and]

theorem word_bit (x : BitVec 128) (k i : Nat) : (word x k).getLsbD (i % 16) = x.getLsbD (16 * k + i % 16) :=
  getLsbD_word _ _ _ (Nat.mod_lt i (by decide))

theorem shufDwords_permV (x : BitVec 128) (o : BitVec 8) :
    shufDwords x o = permV 32 4 (fun _ => true) (shufOf o) x [0, 1, 2, 3] := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [show [0, 1, 2, 3] = List.range 4 from rfl,
    getLsbD_permV_all (by decide) (by decide) (by decide) (fun k _ => shufOf_lt o k) x hi, Bool.true_and,
    bit_dword, dword_shufDwords x o (by omega_using [hi]), dword_bit]
  rfl

theorem shufLowWords_permV (x : BitVec 128) (o : BitVec 8) :
    shufLowWords x o = permV 16 8 (fun _ => true) (lowOf o) x [0, 1, 2, 3, 4, 5, 6, 7] := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [show [0, 1, 2, 3, 4, 5, 6, 7] = List.range 8 from rfl,
    getLsbD_permV_all (by decide) (by decide) (by decide)
      (fun k hk => by unfold lowOf; have := shufOf_lt o k; split <;> omega_using [hk, this]) x hi, Bool.true_and,
    bit_word, shufLowWords, word_ofWords _ (by omega_using [hi]), lowOf]
  split <;> rw [word_bit]
  rfl

theorem shufHighWords_permV (x : BitVec 128) (o : BitVec 8) :
    shufHighWords x o = permV 16 8 (fun _ => true) (highOf o) x [0, 1, 2, 3, 4, 5, 6, 7] := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [show [0, 1, 2, 3, 4, 5, 6, 7] = List.range 8 from rfl,
    getLsbD_permV_all (by decide) (by decide) (by decide)
      (fun k hk => by unfold highOf; have := shufOf_lt o (k - 4); split <;> omega_using [hk, this]) x hi,
    Bool.true_and, bit_word, shufHighWords, word_ofWords _ (by omega_using [hi]), highOf]
  split <;> rw [word_bit]
  rfl

theorem punpcklqdq_permV (x y : BitVec 128) :
    XBinOp.eval .punpcklqdq x y = permV 64 2 (· == 0) (fun k => k) x [0] ^^^ permV 64 2 (· == 1) (fun _ => 0) y [1] := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor,
    getLsbD_permV (by decide) (by decide) (fun k hk => hk) x _ (by decide) (by decide) hi,
    getLsbD_permV (by decide) (by decide) (fun k _ => by decide) y _ (by decide) (by decide) hi,
    show XBinOp.eval .punpcklqdq x y = qword y 0 ++ qword x 0 from rfl, BitVec.getLsbD_append]
  rcases (by omega_using [hi] : i < 64 ∨ 64 ≤ i ∧ i < 128) with h | ⟨h, h'⟩
  · rw [show i / 64 = 0 by omega_using [h], show i % 64 = i by omega_using [h], ite_eq_left h]
    simp [qword, h]
  · rw [show i / 64 = 1 by omega_using [h, h'], show i % 64 = i - 64 by omega_using [h, h'],
      ite_eq_right (show ¬ i < 64 by omega_using [h])]
    simp [qword, show i - 64 < 64 by omega_using [h, h']]

/-- The bits `psrlq` by `n` keeps. -/
theorem srlMask_bit {n i : Nat} (hi : i < 128) :
    (BitVec.ofNat 128 (rep 64 (2 ^ (64 - n) - 1) 1)).getLsbD i = decide (i % 64 + n < 64) := by
  rw [BitVec.getLsbD_ofNat, testBit_rep (two_pow_sub_one_lt (Nat.sub_le 64 n)), Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_and, Bool.true_and]
  exact decide_eq_decide.mpr ⟨fun h => by omega_using [h], fun h => by omega_using [h]⟩

/-- The bits `psllq` by `n` keeps. -/
theorem sllMask_bit {n i : Nat} (hn : n ≤ 64) (hi : i < 128) :
    (BitVec.ofNat 128 (rep 64 ((2 ^ (64 - n) - 1) <<< n) 1)).getLsbD i = decide (n ≤ i % 64) := by
  have hc := high_mask_lt (Nat.sub_le 64 n)
  rw [show 64 - (64 - n) = n by omega_using [hn]] at hc
  rw [BitVec.getLsbD_ofNat, testBit_rep hc, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_and, Bool.true_and]
  have := Nat.mod_lt i (show 0 < 64 by decide)
  by_cases h : n ≤ i % 64
  · rw [decide_eq_true h, decide_eq_true (show i % 64 - n < 64 - n by omega_using [h, this])]; rfl
  · rw [decide_eq_false h]; rfl

theorem qwords_srl (x : BitVec 128) (k : Nat) :
    qword x 1 >>> k ++ qword x 0 >>> k =
      x.rotateRight k &&& BitVec.ofNat 128 (rep 64 (2 ^ (64 - k) - 1) 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, srlMask_bit hi, getLsbD_rotateRight_lt x k i hi]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, qword, BitVec.getLsbD_extractLsb']
  rcases (by omega_using [hi] : i < 64 ∨ 64 ≤ i ∧ i < 128) with h | ⟨h, h'⟩
  · rw [ite_eq_left h, show i % 64 = i by omega_using [h]]
    by_cases h2 : i + k < 64
    · rw [decide_eq_true h2, decide_eq_true (show k + i < 64 by omega_using [h2]),
        show (i + k) % 128 = k + i by omega_using [h2], Bool.and_true, Bool.true_and]
      exact congrArg _ (by omega_using [])
    · rw [decide_eq_false h2, decide_eq_false (show ¬ k + i < 64 by omega_using [h2]), Bool.and_false,
        Bool.false_and]
  · rw [ite_eq_right (show ¬ i < 64 by omega_using [h]), show i % 64 = i - 64 by omega_using [h, h']]
    by_cases h2 : i - 64 + k < 64
    · rw [decide_eq_true h2, decide_eq_true (show k + (i - 64) < 64 by omega_using [h2]),
        show (i + k) % 128 = 64 * 1 + (k + (i - 64)) by omega_using [h2, h], Bool.and_true, Bool.true_and]
    · rw [decide_eq_false h2, decide_eq_false (show ¬ k + (i - 64) < 64 by omega_using [h2]), Bool.and_false,
        Bool.false_and]

theorem qwords_sll (x : BitVec 128) {k : Nat} (h1 : 1 ≤ k) (hk : k ≤ 63) :
    qword x 1 <<< k ++ qword x 0 <<< k =
      x.rotateRight (128 - k) &&& BitVec.ofNat 128 (rep 64 ((2 ^ (64 - k) - 1) <<< k) 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, sllMask_bit (by omega_using [hk]) hi, getLsbD_rotateRight_lt x (128 - k) i hi]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, qword, BitVec.getLsbD_extractLsb']
  rcases (by omega_using [hi] : i < 64 ∨ 64 ≤ i ∧ i < 128) with h | ⟨h, h'⟩
  · rw [ite_eq_left h, show i % 64 = i by omega_using [h], decide_eq_true h, Bool.true_and,
      decide_eq_true (show i - k < 64 by omega_using [h]), Bool.true_and]
    by_cases h2 : k ≤ i
    · rw [decide_eq_true h2, decide_eq_false (show ¬ i < k by omega_using [h2]),
        show (i + (128 - k)) % 128 = i - k by omega_using [h2, h, hk, h1], Bool.and_true, Bool.not_false,
        Bool.true_and]
      exact congrArg _ (by omega_using [])
    · rw [decide_eq_false h2, decide_eq_true (show i < k by omega_using [h2]), Bool.and_false, Bool.not_true,
        Bool.false_and]
  · rw [ite_eq_right (show ¬ i < 64 by omega_using [h]), show i % 64 = i - 64 by omega_using [h, h'],
      decide_eq_true (show i - 64 < 64 by omega_using [h, h']), Bool.true_and,
      decide_eq_true (show i - 64 - k < 64 by omega_using [h, h']), Bool.true_and]
    by_cases h2 : k ≤ i - 64
    · rw [decide_eq_true h2, decide_eq_false (show ¬ i - 64 < k by omega_using [h2]),
        show (i + (128 - k)) % 128 = 64 * 1 + (i - 64 - k) by omega_using [h2, h, h', hk, h1], Bool.and_true,
        Bool.not_false, Bool.true_and]
    · rw [decide_eq_false h2, decide_eq_true (show i - 64 < k by omega_using [h2]), Bool.and_false, Bool.not_true,
        Bool.false_and]

theorem psrlq_ror (x : BitVec 128) (n : BitVec 8) (hn : 1 ≤ n.toNat ∧ n.toNat ≤ 63) :
    XShiftOp.eval .psrlq x n =
      x.rotateRight n.toNat &&& BitVec.ofNat 128 (rep 64 (2 ^ (64 - n.toNat) - 1) 1) := by
  rw [← qwords_srl x]
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega_using [hn], ite_false]

theorem psllq_ror (x : BitVec 128) (n : BitVec 8) (hn : 1 ≤ n.toNat ∧ n.toNat ≤ 63) :
    XShiftOp.eval .psllq x n =
      x.rotateRight (128 - n.toNat) &&& BitVec.ofNat 128 (rep 64 ((2 ^ (64 - n.toNat) - 1) <<< n.toNat) 1) := by
  rw [← qwords_sll x hn.1 hn.2]
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega_using [hn], ite_false]

/-! ## Relating abstract and machine states -/

/-- The address of slot `k` (or external word `k`) of the base address `b`. -/
abbrev xAddr (b : BitVec 32) (k : Nat) : Addr := addr b (16 * k)

structure Rel (R : α → BitVec 128 → Prop) (c : Cfg) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.xmm r)
  slot : ∀ k a, k < c.slots → e.slot k = some a → R a (s.mem.readW (xAddr (s.gpr c.base) k) 128)
  ext : ∀ k a, k < c.exts → e.ext.getD k none = some a → R a (s.mem.readW (xAddr (s.gpr c.ext) k) 128)
  gc : ∀ r v, e.gcOf r = some v → s.gpr r = v

/-- What the machine needs for the memory areas: they are accessible, the
slots do not wrap around the (32-bit) address space, and the external words
do not overlap the slots. -/
structure Ok (c : Cfg) (s : State) : Prop where
  slotIn : ∀ k < c.slots, InRegions s.wr (xAddr (s.gpr c.base) k) 16
  extIn : ∀ k < c.exts, InRegions (s.rd ++ s.wr) (xAddr (s.gpr c.ext) k) 16
  fit : (s.gpr c.base).toNat + 16 * c.slots ≤ 2 ^ 32
  sep : ∀ k < c.slots, ∀ j < c.exts,
    Mem.Sep (xAddr (s.gpr c.base) k) 16 (xAddr (s.gpr c.ext) j) 16

def slotRegion (c : Cfg) (s : State) : Region := ⟨(s.gpr c.base).setWidth 64, 16 * c.slots⟩

theorem Ok.congr {c : Cfg} {s s' : State} (h : Ok c s) (hb : s'.gpr c.base = s.gpr c.base)
    (he : s'.gpr c.ext = s.gpr c.ext) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ok c s' where
  slotIn k hk := by rw [hb, hwr]; exact h.slotIn k hk
  extIn k hk := by rw [he, hrd, hwr]; exact h.extIn k hk
  fit := by rw [hb]; exact h.fit
  sep k hk j hj := by rw [hb, he]; exact h.sep k hk j hj

theorem slot_sep (b : BitVec 32) {j k : Nat} (hj : b.toNat + 16 * j + 16 ≤ 2 ^ 32)
    (hk : b.toNat + 16 * k + 16 ≤ 2 ^ 32) (h : j ≠ k) : Mem.Sep (xAddr b j) 16 (xAddr b k) 16 := by
  intro x h₁ h₂
  rw [xAddr, addr_eq (by omega_using [hj])] at h₁
  rw [xAddr, addr_eq (by omega_using [hk])] at h₂
  have e := Straight.toNat_setWidth32 b
  generalize b.setWidth 64 = B at *
  rcases Nat.lt_or_gt_of_ne h with h | h <;> bv_omega

theorem slot_contains (b : BitVec 32) {n k : Nat} (hk : k < n) (hn : b.toNat + 16 * n ≤ 2 ^ 32) :
    (⟨b.setWidth 64, 16 * n⟩ : Region).Contains (xAddr b k) (128 / 8) := by
  simp only [Region.Contains]
  rw [xAddr, Straight.addr_sub_toNat b (by omega_using [hk, hn])]
  omega_using [hk]

theorem loc_slot {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.slot k)) :
    m.base = c.base ∧ m.disp = 16 * k ∧ k < c.slots := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      cases h
      exact ⟨h2.1, by omega_using [h1], h2.2⟩
    · split at h <;> cases h
  · cases h

theorem loc_ext {c : Cfg} {m : MemOp} {k : Nat} (h : c.loc m = some (.ext k)) :
    m.base = c.ext ∧ m.disp = 16 * k ∧ k < c.exts := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    split at h
    · cases h
    · split at h
      · rename_i h2
        cases h
        exact ⟨h2.1, by omega_using [h1], h2.2⟩
      · cases h
  · cases h

theorem ea_of {s : State} {m : MemOp} {b : Reg} {k : Nat} (hb : m.base = b) (hd : m.disp = 16 * k) :
    s.ea m = xAddr (s.gpr b) k := by
  simp only [State.ea, hb, hd, xAddr, addr]

section
variable {D : Dom α 128} {R : α → BitVec 128 → Prop} {c : Cfg}

theorem perm_ok (hD : D.Sound R) {s n : Nat} {sel : Nat → Bool} {o : Nat → Nat} {a : α} {x : BitVec 128}
    (hx : R a x) : ∀ {rs : List Nat} {b : α}, permD D s n sel o a rs = some b → R b (permV s n sel o x rs)
  | [], b, h => hD.const h
  | r :: rs, b, h => by
    simp only [permD] at h
    simp only [permV]
    split at h
    · rename_i h0
      rw [h0, show BitVec.ofNat 128 0 = 0#128 from rfl, BitVec.and_zero, BitVec.zero_xor]
      exact perm_ok hD hx h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, v, hv, u, hu, w, hw, h⟩ := h
      exact hD.xor (hD.and (hD.ror hx ht) (hD.const hv) hu) (perm_ok hD hx hw) h

/-- The register an instruction the evaluator accepts writes, if any. -/
structure Post (R : α → BitVec 128 → Prop) (c : Cfg) (e' : Env α) (s s' : State)
    (writes : Reg → Prop) : Prop where
  rel : Rel R c e' s'
  ok : Ok c s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  base : s'.gpr c.base = s.gpr c.base
  ext : s'.gpr c.ext = s.gpr c.ext
  other : ∀ r, ¬ writes r → s'.gpr r = s.gpr r
  frame : Frame [slotRegion c s] s.mem s'.mem

/-- An instruction that writes an XMM register with a value the result relates. -/
theorem post_setXmm {e : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c e s) {d : XReg} {a : α}
    {v : BitVec 128} (hv : R a v) {W : Reg → Prop} : Post R c (e.setReg d a) s (s.setXmm d v) W where
  rel := {
    reg := fun r b h => by
      rcases getD_set h with ⟨hi, rfl⟩ | ⟨hi, h'⟩
      · have : r = d := (xidx_inj hi).symm
        subst this
        simp only [State.setXmm, ite_true]; exact hv
      · have : ¬ r = d := fun e => hi (by rw [e])
        simp only [State.setXmm, this, ite_false]; exact hrel.reg r b h'
    slot := fun k b hk h => hrel.slot k b hk h
    ext := fun k b hk h => hrel.ext k b hk h
    gc := fun r v h => hrel.gc r v h }
  ok := hok.congr rfl rfl rfl rfl
  rd := rfl
  wr := rfl
  base := rfl
  ext := rfl
  other _ _ := rfl
  frame := Frame.refl _ _

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) {i : Instr} (h : step D c e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c e' s s' (fun r => i.dst = some r) := by
  cases i with
  | xop o =>
    cases o with
    | bin op d r =>
      cases op with
      | movdqa =>
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨_, rfl, post_setXmm hok hrel (hrel.reg r a ha)⟩
      | pxor =>
        simp only [step] at h
        split at h
        · rename_i x y hx hy
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨_, rfl, post_setXmm hok hrel (hD.xor (hrel.reg d x hx) (hrel.reg r y hy) ht)⟩
        · cases h
      | pand =>
        simp only [step] at h
        split at h
        · rename_i x y hx hy
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨_, rfl, post_setXmm hok hrel (hD.and (hrel.reg d x hx) (hrel.reg r y hy) ht)⟩
        · cases h
      | por =>
        simp only [step] at h
        split at h
        · rename_i x y hx hy
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨_, rfl, post_setXmm hok hrel (hD.or (hrel.reg d x hx) (hrel.reg r y hy) ht)⟩
        · cases h
      | punpcklqdq =>
        simp only [step] at h
        split at h
        · rename_i x y hx hy
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨u, hu, v, hv, h⟩ := h
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
          rw [punpcklqdq_permV]
          exact hD.xor (perm_ok hD (hrel.reg d x hx) hu) (perm_ok hD (hrel.reg r y hy) hv) ht
        · cases h
      | _ => cases h
    | shift op d n =>
      simp only [step] at h
      split at h
      · rename_i hn
        split at h
        · rename_i a ha
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨t, ht, m, hm, h⟩ := h
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
          rw [psrlq_ror _ _ hn]
          exact hD.and (hD.ror (hrel.reg d a ha) ht) (hD.const hm) hu
        · rename_i a ha
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨t, ht, m, hm, h⟩ := h
          obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
          rw [psllq_ror _ _ hn]
          exact hD.and (hD.ror (hrel.reg d a ha) ht) (hD.const hm) hu
        · cases h
      · cases h
    | pshufd d r o =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
      rw [shufDwords_permV]; exact perm_ok hD (hrel.reg r a ha) hb
    | pshuflw d r o =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
      rw [shufLowWords_permV]; exact perm_ok hD (hrel.reg r a ha) hb
    | pshufhw d r o =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
      rw [shufHighWords_permV]; exact perm_ok hD (hrel.reg r a ha) hb
    | movd d r =>
      simp only [step, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, rfl, post_setXmm hok hrel ?_⟩
      rw [hrel.gc r v hv]; exact hD.const hb
    | _ => cases h
  | movdquLoad d m =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_slot hk
      obtain ⟨rg, hr, hcn⟩ := hok.slotIn k hlt
      have hin : InRegions (s.rd ++ s.wr) (xAddr (s.gpr c.base) k) 16 := ⟨rg, List.mem_append_right _ hr, hcn⟩
      exact ⟨_, by simp only [reduceExec, State.load128, ea_of hb hd, hin, ite_true, Option.map_some],
        post_setXmm hok hrel (hrel.slot k a hlt ha)⟩
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_ext hk
      have hin := hok.extIn k hlt
      exact ⟨_, by simp only [reduceExec, State.load128, ea_of hb hd, hin, ite_true, Option.map_some],
        post_setXmm hok hrel (hrel.ext k a hlt ha)⟩
    · cases h
  | movdquStore m r =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hd, hlt⟩ := loc_slot hk
      have hea := ea_of (s := s) hb hd
      have hin := hok.slotIn k hlt
      simp only [reduceExec, State.store128, hea, hin, ite_true, Option.some.injEq, exists_eq_left']
      have hsep : ∀ j < c.slots, j ≠ k → Mem.Sep (xAddr (s.gpr c.base) j) (128 / 8)
          (xAddr (s.gpr c.base) k) (128 / 8) := fun j hj hjk =>
        slot_sep _ (by have := hok.fit; omega_using [hj, this]) (by have := hok.fit; omega_using [hlt, this]) hjk
      refine ⟨⟨fun r' b hr' => hrel.reg r' b hr', fun j b hj hjb => ?_, fun j b hj hjb => ?_,
        fun r v h => hrel.gc r v h⟩, hok.congr rfl rfl rfl rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
      · rcases getD_set hjb with ⟨rfl, rfl⟩ | ⟨hjk, hjb'⟩
        · rw [Mem.readW_writeW_self (n := 16) _ _ _ (by decide)]; exact hrel.reg r a ha
        · rw [Mem.readW_writeW_sep (hsep j hj (Ne.symm hjk)) (by decide)]
          exact hrel.slot j b hj hjb'
      · have hs : Mem.Sep (xAddr (s.gpr c.ext) j) (128 / 8) (xAddr (s.gpr c.base) k) (128 / 8) :=
          fun x h₁ h₂ => hok.sep k hlt j hj x h₂ h₁
        rw [Mem.readW_writeW_sep hs (by decide)]
        exact hrel.ext j b hj hjb
      · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ hlt hok.fit)
    · cases h
  | mov d src =>
    cases src with
    | imm v =>
      simp only [step] at h
      split at h
      · cases h
      · rename_i hd
        simp only [not_or] at hd
        cases h
        have hb : (s.setReg d v).gpr c.base = s.gpr c.base := by simp [State.setReg, Ne.symm hd.1]
        have he : (s.setReg d v).gpr c.ext = s.gpr c.ext := by simp [State.setReg, Ne.symm hd.2]
        refine ⟨s.setReg d v, rfl, ⟨fun r b h => hrel.reg r b h, fun k b hk h => ?_, fun k b hk h => ?_,
          fun r w h => ?_⟩, hok.congr hb he rfl rfl, rfl, rfl, hb, he, fun r hr => ?_, Frame.refl _ _⟩
        · rw [hb]; exact hrel.slot k b hk h
        · rw [he]; exact hrel.ext k b hk h
        · rcases getD_set h with ⟨hi, rfl⟩ | ⟨hi, h'⟩
          · have : r = d := (ridx_inj hi).symm
            subst this; simp [State.setReg]
          · have : ¬ r = d := fun e => hi (by rw [e])
            simp only [State.setReg, this, ite_false]; exact hrel.gc r w h'
        · have : ¬ r = d := fun e => hr (by rw [e]; rfl)
          simp [State.setReg, this]
    | _ => cases h
  | _ => cases h

/-- Running a block that the abstract evaluator accepts: it does not fault,
and the machine state is related to the abstract result. -/
theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State} (hok : Ok c s)
    (hrel : Rel R c e s) (h : eval D c is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c e' s s' (fun r => (is.all fun i => i.dst != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, hok, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.ok p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, p.ok,
      p.rd.trans p₁.rd, p.wr.trans p₁.wr, p.base.trans p₁.base, p.ext.trans p₁.ext,
      fun r hr => ?_, ?_⟩
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)
    · refine p₁.frame.trans ?_
      have := p.frame
      simp only [slotRegion, p₁.base] at this
      exact this

end

theorem run_unique {s s₁ s₂ : State} {is : List Instr} (h₁ : runBlock isa is s = some s₁)
    (h₂ : runBlock isa is s = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- Two slots at offsets `a` and `a'` of `B` that do not overlap. -/
theorem sep_off (B : Addr) {a a' : Nat} (h₁ : B.toNat + a + 16 ≤ 2 ^ 32)
    (h₂ : B.toNat + a' + 16 ≤ 2 ^ 32) (h : a + 16 ≤ a' ∨ a' + 16 ≤ a) :
    Mem.Sep (B + BitVec.ofNat 64 a) 16 (B + BitVec.ofNat 64 a') 16 := by
  intro x hx hy
  rcases h with h | h <;> bv_omega

theorem contains_word {r : Region} {b : BitVec 32} {off k n : Nat}
    (hb : r.base = b.setWidth 64) (hfit : b.toNat + n ≤ 2 ^ 32) (hk : off + 16 * k + 16 ≤ n)
    (hn : n ≤ r.len) :
    r.Contains (xAddr (b + BitVec.ofNat 32 off) k) 16 := by
  simp only [Region.Contains, xAddr, hb]
  rw [Straight.addr_add_ofNat, Straight.addr_sub_toNat b (by omega_using [hfit, hk])]
  omega_using [hk, hn]

/-- `Ok` for slots at offset `off` of a writable region at `b` (of `n ≤ len`
bytes that do not wrap), and external words at offset `off'` of a readable
one at `b'`, apart from the slots: in another region, or in the same one
(`b = b'`) at other offsets. -/
theorem Ok.of_off {c : Cfg} {s : State} {r r' : Region} {b b' : BitVec 32} {off off' n n' : Nat}
    (hr : r ∈ s.wr) (hrb : r.base = b.setWidth 64) (hfit : b.toNat + n ≤ 2 ^ 32) (hn : n ≤ r.len)
    (hb : s.gpr c.base = b + BitVec.ofNat 32 off) (hlen : off + 16 * c.slots ≤ n) (hlt : off < n)
    (hr' : r' ∈ s.rd ++ s.wr) (hrb' : r'.base = b'.setWidth 64) (hfit' : b'.toNat + n' ≤ 2 ^ 32)
    (hn' : n' ≤ r'.len) (hb' : s.gpr c.ext = b' + BitVec.ofNat 32 off')
    (hlen' : off' + 16 * c.exts ≤ n')
    (hsep : c.exts = 0 ∨ r.Disjoint r' ∨
      (b = b' ∧ (off + 16 * c.slots ≤ off' ∨ off' + 16 * c.exts ≤ off))) : Ok c s where
  slotIn k hk := ⟨r, hr, by rw [hb]; exact contains_word hrb hfit (by omega_using [hlen, hk]) hn⟩
  extIn k hk := ⟨r', hr', by rw [hb']; exact contains_word hrb' hfit' (by omega_using [hlen', hk]) hn'⟩
  fit := by
    rw [hb, Straight.toNat_add_off (by omega_using [hfit, hlt])]; omega_using [hfit, hlen]
  sep k hk j hj := by
    rcases hsep with h | h | ⟨rfl, h⟩
    · omega_using [hj, h]
    · intro x h₁ h₂
      have c₁ := contains_word (b := b) (off := off) (k := k) hrb hfit (by omega_using [hlen, hk]) hn
      have c₂ := contains_word (b := b') (off := off') (k := j) hrb' hfit' (by omega_using [hlen', hj]) hn'
      rw [hb] at h₁; rw [hb'] at h₂
      exact h x (c₁.byte h₁) (c₂.byte h₂)
    · intro x h₁ h₂
      have e₁ : xAddr (s.gpr c.base) k = b.setWidth 64 + BitVec.ofNat 64 (off + 16 * k) := by
        rw [hb, xAddr, Straight.addr_add_ofNat]; exact addr_eq (by omega_using [hfit, hlen, hk])
      have e₂ : xAddr (s.gpr c.ext) j = b.setWidth 64 + BitVec.ofNat 64 (off' + 16 * j) := by
        rw [hb', xAddr, Straight.addr_add_ofNat]; exact addr_eq (by omega_using [hlen', hj, hfit'])
      rw [e₁] at h₁; rw [e₂] at h₂
      exact sep_off (b.setWidth 64) (by rw [Straight.toNat_setWidth32]; omega_using [hfit, hlen, hk])
        (by rw [Straight.toNat_setWidth32]; omega_using [hfit', hlen', hj]) (by omega_using [h, hk, hj]) x h₁ h₂

/-! ## Linear layers -/

/-- The slots `j` hold the input words `ins j`, and the external words the
input words from `xb` on. -/
def linEnv (slots exts xb : Nat) (ins : Nat → Option Nat) : Env (Nat × Nat) :=
  { slots := (List.range slots).map fun j => (ins j).map (inWordW 128)
    ext := (List.range exts).map fun j => some (inWordW 128 (xb + j)) }

/-- Each output slot `j` holds the word whose bit `p` is bit `p` of the
constant XOR the atoms `g p`. -/
def linPost (n k : Nat) (outs : List (Nat × Nat × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => decide (o.1 < n) && (match e.slot o.1 with
    | some v => v.1 == o.2.1 && (v.2 == mk 128 o.2.2 128 && decide (v.2 < 2 ^ (128 * 2 ^ k)))
    | none => false)

theorem getD_map_range {β : Type} {f : Nat → Option β} {n j : Nat} {a : β}
    (h : ((List.range n).map f).getD j none = some a) : j < n ∧ f j = some a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at h
  by_cases hj : j < n
  · rw [List.getElem?_range hj] at h; exact ⟨hj, h⟩
  · rw [List.getElem?_eq_none (by simpa using hj)] at h; cases h

/-- A linear block that the evaluator accepts, on the machine. -/
theorem linear_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : Nat → Option Nat}
    {outs : List (Nat × Nat × (Nat → List Nat))}
    (hchk : check (lanes 128 k) c is (linEnv c.slots c.exts xb ins) (linPost c.slots k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 128)
    (hin : ∀ j i, ins j = some i → j < c.slots → 128 * i + 128 ≤ 2 ^ k ∧
      W i = s.mem.readW (xAddr (s.gpr c.base) j) 128)
    (hext : ∀ j < c.exts,
      128 * (xb + j) + 128 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (xAddr (s.gpr c.ext) j) 128) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j cst g, (j, cst, g) ∈ outs → ∀ p < 128,
        (s'.mem.readW (xAddr (s.gpr c.base) j) 128).getLsbD p = (cst.testBit p ^^ xorBits W (g p))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linEnv c.slots c.exts xb ins) s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun j a hj h => ?_, fun r v h => ?_⟩
    · revert h; cases r <;> intro h <;> cases h
    · obtain ⟨hj', h'⟩ := getD_map_range h
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h'
      obtain ⟨h1, h2⟩ := hin j i hi hj'
      rw [← h2]; exact inWordW_rel W h1
    · obtain ⟨hj', h'⟩ := getD_map_range h
      cases h'
      obtain ⟨h1, h2⟩ := hext j hj'
      rw [← h2]; exact inWordW_rel W h1
    · revert h; cases r <;> intro h <;> cases h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j cst g hjg q hq => ?_, p.rd, p.wr, fun r hr => p.other r (by simp [hr]), p.frame⟩
  have h := List.all_eq_true.mp hpost (j, cst, g) hjg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hjn, h⟩ := h
  split at h
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hc, hm, hlt⟩ := h
    have := p.rel.slot j _ hjn hv
    rw [p.base] at this
    have hq' := this.2 q hq
    have h0 : LaneRel k (assign W (2 ^ k)) (outWordW 128 g)
        (s'.mem.readW (xAddr (s.gpr c.base) j) 128 ^^^ BitVec.ofNat 128 cst) := by
      refine ⟨Nat.two_pow_pos _, fun q hq => ?_⟩
      rw [BitVec.getLsbD_xor, this.2 q hq, BitVec.getLsbD_ofNat, decide_eq_true hq, Bool.true_and, hc, hm, outWordW]
      simp only [Nat.zero_testBit, Bool.false_xor]
      cases cst.testBit q <;> simp
    have hb := outWordW_rel_of_lt (by rw [← hm]; exact hlt) h0 q hq
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, decide_eq_true hq, Bool.true_and] at hb
    rw [← hb]
    cases cst.testBit q <;> simp
  · cases h

end VG.X86.StraightX
