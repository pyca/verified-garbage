module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Gcm.RISCV64.PrepLaw
public import VerifiedGarbage.Proof.Gcm.Slots
public import VerifiedGarbage.Proof.Gcm.Spread
public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH with integer multiplications on RISC-V

Untrusted: everything here is checked by Lean. The blocks but for the loads of
`H`, `Y` and the data are run on an abstract machine, the registers and 36
doublewords at a register `b` (`A`, `evalA`), which the machine follows
(`sound`): the key's words, which `prep` stores and the loop reads.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64
open VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghashOperand ghashClass)
open VG.Proof.Gcm.Spread (m4 mul4 mul64 meet4 lo32 hi32 up dn redW mulW keyW0 keyW1)
open VG.Proof.Gcm.Clmul (vdword vdword_xor)

/-! ## The abstract machine -/

structure A where
  g : Reg → BitVec 64
  m : Nat → BitVec 64

namespace A

def set (a : A) (d : Reg) (v : BitVec 64) : A := ⟨fun r => if r = d then v else a.g r, a.m⟩
def put (a : A) (k : Nat) (v : BitVec 64) : A := ⟨a.g, fun j => if j = k then v else a.m j⟩

theorem g_set (a : A) (d : Reg) (v : BitVec 64) (r : Reg) : (a.set d v).g r = if r = d then v else a.g r := rfl
theorem m_set (a : A) (d : Reg) (v : BitVec 64) : (a.set d v).m = a.m := rfl
theorem g_put (a : A) (k : Nat) (v : BitVec 64) : (a.put k v).g = a.g := rfl
theorem m_put (a : A) (k : Nat) (v : BitVec 64) (j : Nat) : (a.put k v).m j = if j = k then v else a.m j := rfl

end A

def logicV (op : LogicOp) (x y : BitVec 64) : BitVec 64 :=
  match op with | .and => x &&& y | .or => x ||| y | .xor => x ^^^ y

/-- A step, `b` the base of the words, which it may store if `w`. -/
def stepA (b : Reg) (w : Bool) : Instr → A → Option A
  | .mul d n m, a => if d = b then none else some (a.set d (a.g n * a.g m))
  | .logic op d n m, a => if d = b then none else some (a.set d (logicV op (a.g n) (a.g m)))
  | .shift .sll .d d n k, a => if d = b ∨ ¬ k < 64 then none else some (a.set d (a.g n <<< k))
  | .shift .srl .d d n k, a => if d = b ∨ ¬ k < 64 then none else some (a.set d (a.g n >>> k))
  | .addi d n imm, a => if d = b ∨ imm ≠ 0 then none else some (a.set d (a.g n))
  | .li d imm, a => if d = b ∨ imm ≠ 0 then none else some (a.set d 0#64)
  | .load .d d n off, a =>
    if d = b ∨ n ≠ b ∨ off % 8 ≠ 0 ∨ ¬ off < 288 then none else some (a.set d (a.m (off / 8)))
  | .store .d t n off, a =>
    if w = false ∨ n ≠ b ∨ off % 8 ≠ 0 ∨ ¬ off < 288 then none else some (a.put (off / 8) (a.g t))
  | _, _ => none

def evalA (b : Reg) (w : Bool) : List Instr → A → Option A
  | [], a => some a
  | i :: is, a => (stepA b w i a).bind (evalA b w is)

theorem evalA_append (b : Reg) (w : Bool) (l₁ l₂ : List Instr) (a : A) :
    evalA b w (l₁ ++ l₂) a = (evalA b w l₁ a).bind (evalA b w l₂) := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, evalA, Option.bind_assoc]
    exact congrArg _ (funext fun a' => ih a')

/-- The machine's state `s` and the abstract one's, from the state `s₀`. -/
structure Rel (b : Reg) (w : Bool) (s₀ s : State) (a : A) : Prop where
  g : s.gpr = a.g
  m : Slots s₀.mem s.mem (s₀.gpr b) 36 a.m
  base : a.g b = s₀.gpr b
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ro : w = false → s.mem = s₀.mem

/-- The words are where the machine may access them. -/
structure Words (b : Reg) (w : Bool) (s₀ : State) : Prop where
  al : ∀ k < 36, (s₀.gpr b + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0
  rd : ∀ k < 36, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 (8 * k)) 8
  wr : w = true → ∀ k < 36, InRegions s₀.wr (s₀.gpr b + BitVec.ofNat 64 (8 * k)) 8

variable {b : Reg} {w : Bool} {s₀ s : State} {a a' : A}

theorem Rel.set (h : Rel b w s₀ s a) {d : Reg} (hd : d ≠ b) (v : BitVec 64) : Rel b w s₀ (s.write d v) (a.set d v) :=
  ⟨by funext r; show (if r = d then v else s.gpr r) = _; rw [h.g]; rfl, h.m,
    by rw [A.g_set, ite_eq_right (Ne.symm hd)]; exact h.base, h.rd, h.wr, h.sp, h.ro⟩

theorem load_sound (hw : Words b w s₀) (h : Rel b w s₀ s a) {d n : Reg} {off : Nat}
    (hd : ¬ (d = b ∨ n ≠ b ∨ off % 8 ≠ 0 ∨ ¬ off < 288)) :
    ∃ s', exec (.load .d d n off) s = some s' ∧ Rel b w s₀ s' (a.set d (a.m (off / 8))) := by
  simp only [not_or, Classical.not_not] at hd
  obtain ⟨hd, hn, ho, hl⟩ := hd
  have he : off = 8 * (off / 8) := by omega
  have hk : off / 8 < 36 := by omega
  have hb : s.gpr n + BitVec.ofNat 64 off = s₀.gpr b + BitVec.ofNat 64 (8 * (off / 8)) := by
    rw [hn, h.g, h.base, ← he]
  have hx := exec_load_d (s := s) (t := d) (n := n) (off := off) (by omega) (by rw [hb]; exact hw.al _ hk)
    (by rw [hb, h.rd, h.wr]; exact hw.rd _ hk)
  rw [hb, h.m.get _ hk] at hx
  exact ⟨_, hx, h.set hd _⟩

theorem store_sound (hw : Words b w s₀) (h : Rel b w s₀ s a) {t n : Reg} {off : Nat}
    (hd : ¬ (w = false ∨ n ≠ b ∨ off % 8 ≠ 0 ∨ ¬ off < 288)) :
    ∃ s', exec (.store .d t n off) s = some s' ∧ Rel b w s₀ s' (a.put (off / 8) (a.g t)) := by
  simp only [not_or, Classical.not_not] at hd
  obtain ⟨hd, hn, ho, hl⟩ := hd
  have he : off = 8 * (off / 8) := by omega
  have hk : off / 8 < 36 := by omega
  have hb : s.gpr n + BitVec.ofNat 64 off = s₀.gpr b + BitVec.ofNat 64 (8 * (off / 8)) := by
    rw [hn, h.g, h.base, ← he]
  have hx := exec_store_d (s := s) (t := t) (n := n) (off := off) (by omega) (by rw [hb]; exact hw.al _ hk)
    (by rw [hb, h.wr]; exact hw.wr (by simpa using hd) _ hk)
  rw [hb, h.g] at hx
  refine ⟨_, hx, ⟨?_, ?_, h.base, h.rd, h.wr, h.sp, fun e => absurd e hd⟩⟩
  · rfl
  · exact h.m.store hk (by decide) (a.g t)

theorem step_sound (hw : Words b w s₀) (h : Rel b w s₀ s a) (i : Instr) (hi : stepA b w i a = some a') :
    ∃ s', exec i s = some s' ∧ Rel b w s₀ s' a' := by
  unfold stepA at hi
  split at hi
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    cases e; exact ⟨_, rfl, by rw [h.g]; exact h.set hd _⟩
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    cases e; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    obtain ⟨hd1, hk⟩ := not_or.mp hd
    cases e; refine ⟨_, ite_eq_left (Classical.not_not.mp hk), ?_⟩; rw [h.g]; exact h.set hd1 _
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    obtain ⟨hd1, hk⟩ := not_or.mp hd
    cases e; refine ⟨_, ite_eq_left (Classical.not_not.mp hk), ?_⟩; rw [h.g]; exact h.set hd1 _
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    obtain ⟨hd1, hk⟩ := not_or.mp hd
    have hk := Classical.not_not.mp hk
    subst hk
    cases e
    refine ⟨_, ite_eq_left (by decide), ?_⟩
    rw [h.g, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact h.set hd1 _
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    obtain ⟨hd1, hk⟩ := not_or.mp hd
    have hk := Classical.not_not.mp hk
    subst hk
    cases e
    exact ⟨_, ite_eq_left (by decide), h.set hd1 _⟩
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    cases e; exact load_sound hw h hd
  · obtain ⟨hd, e⟩ := Option.ite_none_left_eq_some.mp hi
    cases e; exact store_sound hw h hd
  · cases hi

/-- The machine runs what the abstract machine runs. -/
theorem sound (hw : Words b w s₀) {is : List Instr} (h : Rel b w s₀ s a) (he : evalA b w is a = some a') :
    WP isa (.block is) s fun s' => Rel b w s₀ s' a' := by
  induction is generalizing s a with
  | nil => cases he; exact WP.block_nil h
  | cons i is ih =>
    simp only [evalA, Option.bind_eq_some_iff] at he
    obtain ⟨a₁, h₁, h₂⟩ := he
    obtain ⟨s₁, e, r⟩ := step_sound hw h i h₁
    exact WP.block_cons_iff.mpr ⟨s₁, e, ih r h₂⟩

/-! ## Running blocks -/

def WA (b : Reg) (w : Bool) (is : List Instr) (a : A) (Q : A → Prop) : Prop := ∃ a', evalA b w is a = some a' ∧ Q a'

theorem WA.append {l₁ l₂ : List Instr} {Q : A → Prop} (h : WA b w l₁ a fun a' => WA b w l₂ a' Q) :
    WA b w (l₁ ++ l₂) a Q := by
  obtain ⟨a₁, e₁, a₂, e₂, q⟩ := h
  exact ⟨a₂, by rw [evalA_append, e₁]; exact e₂, q⟩

theorem WA.mono {l : List Instr} {Q R : A → Prop} (h : WA b w l a Q) (hq : ∀ a', Q a' → R a') : WA b w l a R := by
  obtain ⟨a', e, q⟩ := h; exact ⟨a', e, hq a' q⟩

theorem WA.sound (hw : Words b w s₀) (h : Rel b w s₀ s a) {is : List Instr} {Q : A → Prop} (hq : WA b w is a Q) :
    WP isa (.block is) s fun s' => ∃ a', Rel b w s₀ s' a' ∧ Q a' := by
  obtain ⟨a', e, q⟩ := hq
  exact WP.mono (RISCV64.sound hw h e) fun s' r => ⟨a', r, q⟩

/-- Registers other than `rs` are unchanged. -/
def Keeps (rs : List Reg) (a a' : A) : Prop := ∀ r, r ∉ rs → a'.g r = a.g r

theorem Keeps.trans {rs : List Reg} {a b c : A} (h₁ : Keeps rs a b) (h₂ : Keeps rs b c) : Keeps rs a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem Keeps.mono {rs rs' : List Reg} {a b : A} (h : Keeps rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' a b :=
  fun r hr => h r fun h' => hr (hs r h')

/-- The masks are in their registers. -/
def Masks (a : A) : Prop := ∀ j < 4, a.g (maskReg j) = m4 j

theorem Masks.keep {rs : List Reg} {a a' : A} (h : Masks a) (k : Keeps rs a a')
    (hr : ∀ j < 4, maskReg j ∉ rs := by decide) : Masks a' := fun j hj => by rw [k _ (hr j hj), h j hj]

/-! ### Folds -/

theorem xor_rev (d a b c : BitVec 64) : d ^^^ a ^^^ b ^^^ c = d ^^^ (a ^^^ b ^^^ c) := by ac_rfl

theorem foldDn_ok (b : Reg) (w : Bool) (d q t : Reg) (hd : d ≠ b) (ht : t ≠ b) (hdq : q ≠ d) (hdt : d ≠ t) (hqt : q ≠ t) (a : A) :
    WA b w (foldDn d q t) a fun a' => a'.g d = a.g d ^^^ dn (a.g q) ∧ Keeps [d, t] a a' ∧ a'.m = a.m := by
  simp (config := {decide := true}) only [WA, foldDn, sll, xorI, evalA, stepA, logicV, Option.bind_some, A.g_set, hd, ht,
    hdq, hdt, hqt, ite_false, ite_true, or_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, by first | exact trivial | rfl⟩
  · rw [dn, xor_rev]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem foldUp_ok (b : Reg) (w : Bool) (d q t : Reg) (hd : d ≠ b) (ht : t ≠ b) (hdq : q ≠ d) (hdt : d ≠ t) (hqt : q ≠ t) (a : A) :
    WA b w (foldUp d q t) a fun a' => a'.g d = a.g d ^^^ up (a.g q) ∧ Keeps [d, t] a a' ∧ a'.m = a.m := by
  simp (config := {decide := true}) only [WA, foldUp, srl, xorI, evalA, stepA, logicV, Option.bind_some, A.g_set, hd, ht,
    hdq, hdt, hqt, ite_false, ite_true, or_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, by first | exact trivial | rfl⟩
  · rw [up, xor_rev]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

/-! ### The product of 32-bit words -/

/-- The key's words at `a0`: word `i` of 32 bits is `kx i`. -/
def Key (kx : Nat → BitVec 64) (a : A) : Prop := ∀ i < 9, ∀ j < 4, a.m (4 * i + j) = kx i &&& m4 j

abbrev cmRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a5, .a6, .a7]

theorem slot_ok {i j : Nat} (hi : i < 9) (hj : j < 4) :
    8 * (4 * i + j) % 8 = 0 ∧ 8 * (4 * i + j) < 288 ∧ 8 * (4 * i + j) / 8 = 4 * i + j := by omega

theorem classes_ok (x : Reg) (i : Nat) (hi : i < 9) (hx : x ∉ cmRegs) {kx : Nat → BitVec 64} {a : A} (hM : Masks a)
    (hK : Key kx a) :
    WA .a0 false (classes x i) a fun a' => (∀ j < 4, a'.g (wc j) = a.g x &&& m4 j) ∧
      (∀ j < 4, a'.g (kc j) = kx i &&& m4 j) ∧ Keeps cmRegs a a' ∧ a'.m = a.m := by
  simp only [cmRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  have h0 := slot_ok hi (show 0 < 4 by decide)
  have h1 := slot_ok hi (show 1 < 4 by decide)
  have h2 := slot_ok hi (show 2 < 4 by decide)
  have h3 := slot_ok hi (show 3 < 4 by decide)
  have e0 : a.g .s0 = m4 0 := hM 0 (by decide)
  have e1 : a.g .s1 = m4 1 := hM 1 (by decide)
  have e2 : a.g .s2 = m4 2 := hM 2 (by decide)
  have e3 : a.g .s3 = m4 3 := hM 3 (by decide)
  simp only [WA, classes, andI, evalA, stepA, logicV, Option.bind_some, A.g_set, A.m_set, reduceCtorEq, hx, h0, h1, h2, h3,
    ite_false, ne_eq, not_true_eq_false, or_self, Option.some.injEq, exists_eq_left', e0, e1, e2, e3]
  refine ⟨?_, ?_, fun r hr => ?_, by first | exact trivial | rfl⟩
  · have h : ∀ j, j < 4 → j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    intro j hj
    rcases h j hj with rfl | rfl | rfl | rfl <;> simp only [wc, reduceCtorEq, ite_false, ite_true]
  · have h : ∀ j, j < 4 → j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    intro j hj
    rw [← hK i hi j hj]
    rcases h j hj with rfl | rfl | rfl | rfl <;> simp only [kc, reduceCtorEq, ite_false, ite_true]
  · simp only [cmRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem classSum_ok (d : Reg) (r : Nat) (hr : r < 4) (hd : d ∉ cmRegs) (hd0 : d ≠ .a0) {x k : BitVec 64} {a : A}
    (hM : Masks a) (hC : ∀ j < 4, a.g (wc j) = x &&& m4 j) (hK : ∀ j < 4, a.g (kc j) = k &&& m4 j) :
    WA .a0 false (classSum d r) a fun a' => a'.g d = a.g d ^^^ (meet4 x k r &&& m4 r) ∧
      Keeps [d, .a6, .a7] a a' ∧ a'.m = a.m := by
  have hw : ∀ j < 4, wc j ≠ .a6 ∧ wc j ≠ .a7 := by decide
  have hk : ∀ j < 4, kc j ≠ .a6 ∧ kc j ≠ .a7 := by decide
  have hm : ∀ j < 4, maskReg j ≠ .a6 ∧ maskReg j ≠ .a7 := by decide
  have l0 : r % 4 < 4 := Nat.mod_lt _ (by decide)
  have l3 : (r + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  have l2 : (r + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  have l1 : (r + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [cmRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  simp only [WA, classSum, xorI, andI, evalA, stepA, logicV, Option.bind_some, A.g_set, reduceCtorEq, hd, hd0,
    hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hk _ l1, hk _ l2, hk _ l3,
    hm r hr, ite_false, ite_true, Option.some.injEq, exists_eq_left', hC 0 (by decide), hC 1 (by decide),
    hC 2 (by decide), hC 3 (by decide), hK _ l0, hK _ l1, hK _ l2, hK _ l3, hM r hr]
  refine ⟨?_, fun q hq => ?_, by first | exact trivial | rfl⟩
  · rw [meet4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]

theorem clmul_ok (d x : Reg) (i : Nat) (hi : i < 9) (hx : x ∉ cmRegs) (hd : d ∉ cmRegs) (hd0 : d ≠ .a0)
    (hdm : ∀ j < 4, maskReg j ∉ [d, Reg.a6, .a7]) {kx : Nat → BitVec 64} {a : A}
    (hM : Masks a) (hK : Key kx a) :
    WA .a0 false (clmul d x i) a fun a' => a'.g d = mul4 (a.g x) (kx i) ∧ Keeps (d :: cmRegs) a a' ∧ a'.m = a.m := by
  have hw : ∀ j < 4, wc j ∉ [Reg.a6, .a7] := by decide
  have hk : ∀ j < 4, kc j ∉ [Reg.a6, .a7] := by decide
  have hwd : ∀ j < 4, wc j ∉ [d, Reg.a6, .a7] := fun j hj => by
    have hcm : ∀ j < 4, wc j ∈ cmRegs := by decide
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hd (h ▸ hcm j hj)
    · exact hw j hj h
  have hkd : ∀ j < 4, kc j ∉ [d, Reg.a6, .a7] := fun j hj => by
    have hcm : ∀ j < 4, kc j ∈ cmRegs := by decide
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hd (h ▸ hcm j hj)
    · exact hk j hj h
  rw [clmul, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((classes_ok x i hi hx hM hK).mono fun a₀ ⟨c₀, q₀, k₀, m₀⟩ => ?_)
  have hz : WA .a0 false [.li d 0] a₀ fun a' => a'.g d = 0#64 ∧ Keeps [d, .a6, .a7] a₀ a' ∧ a'.m = a₀.m := by
    simp only [WA, evalA, stepA, hd0, ne_eq, not_true_eq_false, or_self, ite_false, Option.bind_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨by rw [A.g_set, ite_eq_left rfl], fun r hr => ?_, rfl⟩
    rw [A.g_set, ite_eq_right fun e => hr (by simp [e])]
  have hM₀ : Masks a₀ := hM.keep k₀
  have hS : ∀ r < 4, ∀ c : A, Keeps [d, .a6, .a7] a₀ c → c.m = a₀.m →
      WA .a0 false (classSum d r) c fun c' => c'.g d = c.g d ^^^ (meet4 (a.g x) (kx i) r &&& m4 r) ∧
        Keeps [d, .a6, .a7] a₀ c' ∧ c'.m = a₀.m := by
    intro r hr c hkc hmc
    exact (classSum_ok d r hr hd hd0 (hM₀.keep hkc hdm) (fun j hj => by rw [hkc _ (hwd j hj), c₀ j hj])
      (fun j hj => by rw [hkc _ (hkd j hj), q₀ j hj])).mono fun c' ⟨e, k', m'⟩ => ⟨e, hkc.trans k', m'.trans hmc⟩
  refine WA.append (hz.mono fun a₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WA.append ((hS 0 (by decide) a₁ k₁ m₁).mono fun a₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine WA.append ((hS 1 (by decide) a₂ k₂ m₂).mono fun a₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine WA.append ((hS 2 (by decide) a₃ k₃ m₃).mono fun a₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine (hS 3 (by decide) a₄ k₄ m₄).mono fun a₅ ⟨e₅, k₅, m₅⟩ => ⟨?_, ?_, m₅.trans m₀⟩
  · rw [e₅, e₄, e₃, e₂, e₁, BitVec.zero_xor, mul4]
  · refine (k₀.mono fun r hr => List.mem_cons_of_mem _ hr).trans (k₅.mono fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (by decide)
    · exact List.mem_cons_of_mem _ (by decide)

/-- The key's doubleword `t` from its 32-bit words. -/
structure KeyOf (kx : Nat → BitVec 64) (kd : Nat → BitVec 64) : Prop where
  lo : ∀ t < 3, kx (3 * t) = lo32 (kd t)
  hi : ∀ t < 3, kx (3 * t + 1) = hi32 (kd t)
  sum : ∀ t < 3, kx (3 * t + 2) = lo32 (kd t) ^^^ hi32 (kd t)

abbrev mulRegs : List Reg := [.s6, .s7, .s8, .s10, .s11] ++ cmRegs

theorem mul_ok (r : Reg) (t : Nat) (ht : t < 3) (hr : r ∉ mulRegs) {kx kd : Nat → BitVec 64} (hk : KeyOf kx kd) {a : A}
    (hM : Masks a) (hK : Key kx a) :
    WA .a0 false (mul r t) a fun a' => a'.g .s6 = vdword (VectorCrypto.polyMul (a.g r) (kd t)) 0 ∧
      a'.g .s7 = vdword (VectorCrypto.polyMul (a.g r) (kd t)) 1 ∧ Keeps mulRegs a a' ∧ a'.m = a.m := by
  have hr' := hr
  simp only [mulRegs, cmRegs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  rw [mul, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append (WA.mono (Q := fun a' => a'.g .s10 = lo32 (a.g r) ∧ Keeps mulRegs a a' ∧ a'.m = a.m) ?_ ?_)
  · simp (config := {decide := true}) only [WA, sll, srl, evalA, stepA, Option.bind_some, A.g_set, ite_false, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun q hq => ?_, by first | exact trivial | rfl⟩
    simp only [mulRegs, List.cons_append, List.mem_cons, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  · intro a₁ ⟨e₁, k₁, m₁⟩
    refine WA.append ((clmul_ok .s6 .s10 (3 * t) (kx := kx) (by omega) (by decide) (by decide) (by decide) (by decide) (hM.keep k₁)
      (fun i hi j hj => by rw [m₁]; exact hK i hi j hj)).mono fun a₂ ⟨e₂, k₂, m₂⟩ => ?_)
    have K₂ : Keeps mulRegs a a₂ := k₁.trans (k₂.mono (by decide))
    refine WA.append (WA.mono (Q := fun a' => a'.g .s11 = hi32 (a.g r) ∧ Keeps [.s11] a₂ a' ∧ a'.m = a₂.m) ?_ ?_)
    · simp (config := {decide := true}) only [WA, srl, evalA, stepA, Option.bind_some, A.g_set, ite_false, ite_true,
        Option.some.injEq, exists_eq_left']
      refine ⟨by rw [K₂ r hr]; rfl, fun q hq => ?_, by first | exact trivial | rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      simp only [A.g_set, hq, ite_false]
    · intro a₃ ⟨e₃, k₃, m₃⟩
      have K₃ : Keeps mulRegs a a₃ := K₂.trans (k₃.mono (by decide))
      refine WA.append ((clmul_ok .s7 .s11 (3 * t + 1) (kx := kx) (by omega) (by decide) (by decide) (by decide) (by decide)
        (hM.keep K₃) (fun i hi j hj => by rw [m₃, m₂, m₁]; exact hK i hi j hj)).mono fun a₄ ⟨e₄, k₄, m₄⟩ => ?_)
      have K₄ : Keeps mulRegs a a₄ := K₃.trans (k₄.mono (by decide))
      refine WA.append (WA.mono (Q := fun a' => a'.g .s10 = lo32 (a.g r) ^^^ hi32 (a.g r) ∧ Keeps [.s10] a₄ a' ∧
        a'.m = a₄.m) ?_ ?_)
      · simp (config := {decide := true}) only [WA, xorI, evalA, stepA, logicV, Option.bind_some, A.g_set, ite_false,
          ite_true, Option.some.injEq, exists_eq_left']
        refine ⟨by rw [k₄ .s10 (by decide), k₃ .s10 (by decide), k₂ .s10 (by decide), e₁, k₄ .s11 (by decide), e₃],
          fun q hq => ?_, by first | exact trivial | rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [A.g_set, hq, ite_false]
      · intro a₅ ⟨e₅, k₅, m₅⟩
        have K₅ : Keeps mulRegs a a₅ := K₄.trans (k₅.mono (by decide))
        refine WA.append ((clmul_ok .s8 .s10 (3 * t + 2) (kx := kx) (by omega) (by decide) (by decide) (by decide) (by decide)
          (hM.keep K₅) (fun i hi j hj => by rw [m₅, m₄, m₃, m₂, m₁]; exact hK i hi j hj)).mono
            fun a₆ ⟨e₆, k₆, m₆⟩ => ?_)
        have K₆ : Keeps mulRegs a a₆ := K₅.trans (k₆.mono (by decide))
        have p0 : a₆.g .s6 = mul4 (lo32 (a.g r)) (lo32 (kd t)) := by
          rw [k₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), e₂, e₁, hk.lo t ht]
        have p1 : a₆.g .s7 = mul4 (hi32 (a.g r)) (hi32 (kd t)) := by
          rw [k₆ _ (by decide), k₅ _ (by decide), e₄, e₃, hk.hi t ht]
        have p2 : a₆.g .s8 = mul4 (lo32 (a.g r) ^^^ hi32 (a.g r)) (lo32 (kd t) ^^^ hi32 (kd t)) := by
          rw [e₆, e₅, hk.sum t ht]
        have hres := Spread.mul64_eq (a.g r) (kd t)
        simp (config := {decide := true}) only [WA, xorI, sll, srl, evalA, stepA, logicV, Option.bind_some, A.g_set,
          ite_false, ite_true, Option.some.injEq, exists_eq_left', p0, p1, p2]
        refine ⟨congrArg _root_.Prod.fst hres, congrArg _root_.Prod.snd hres, K₆.trans fun q hq => ?_, ?_⟩
        · simp only [mulRegs, List.cons_append, List.mem_cons, not_or] at hq
          simp only [A.g_set, hq, ite_false]
        · show a₆.m = a.m
          rw [m₆, m₅, m₄, m₃, m₂, m₁]

/-! ### A block -/

/-- The key's doublewords, from `H`'s. -/
def kdOf (h1 h0 : BitVec 64) (t : Nat) : BitVec 64 :=
  match t with
  | 0 => keyW1 h1 h0
  | 1 => keyW0 h1 h0
  | _ => keyW1 h1 h0 ^^^ keyW0 h1 h0

abbrev coreRegs : List Reg := [.s4, .s5, .s9, .a4] ++ mulRegs

theorem xor_u (c0 l0 h0 l1 d : BitVec 64) :
    c0 ^^^ h0 ^^^ l0 ^^^ l1 ^^^ d = c0 ^^^ l0 ^^^ h0 ^^^ l1 ^^^ d := by ac_rfl

theorem xor_mid (c l1 h1 h0 l0 u v : BitVec 64) :
    c ^^^ h1 ^^^ h0 ^^^ l1 ^^^ l0 ^^^ u ^^^ v = h0 ^^^ (c ^^^ l1 ^^^ h1) ^^^ l0 ^^^ u ^^^ v := by ac_rfl

theorem core_ok (h1 h0 : BitVec 64) {kx : Nat → BitVec 64} (hk : KeyOf kx (kdOf h1 h0)) {a : A}
    (hM : Masks a) (hK : Key kx a) :
    WA .a0 false core a fun a' =>
      a'.g .s4 ++ a'.g .s5 = Spec.Gcm.mul (a.g .s4 ++ a.g .s5) (h1 ++ h0) ∧ Keeps coreRegs a a' ∧ a'.m = a.m := by
  have hKm : ∀ {a' : A}, a'.m = a.m → Key kx a' := fun e i hi j hj => by rw [e]; exact hK i hi j hj
  simp only [core, List.append_assoc]
  refine WA.append (WA.mono (Q := fun a' => a'.g .s9 = a.g .s4 ^^^ a.g .s5 ∧ Keeps [.s9] a a' ∧ a'.m = a.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [A.g_set, ite_eq_right hq]
  intro a₁ ⟨e₁, k₁, m₁⟩
  refine WA.append ((mul_ok .s9 2 (by decide) (by decide) hk (hM.keep k₁) (hKm m₁)).mono fun a₂ ⟨c0, c1, k₂, m₂⟩ => ?_)
  rw [e₁] at c0 c1
  refine WA.append (WA.mono (Q := fun a' => a'.g .a4 = a₂.g .s6 ∧ a'.g .s9 = a₂.g .s7 ∧ Keeps [.a4, .s9] a₂ a' ∧
    a'.m = a₂.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  intro a₃ ⟨x₃, y₃, k₃, m₃⟩
  have K₃ : Keeps coreRegs a a₃ := (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))
  have M₃ : a₃.m = a.m := by rw [m₃, m₂, m₁]
  have y1₃ : a₃.g .s4 = a.g .s4 := by rw [k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  have y0₃ : a₃.g .s5 = a.g .s5 := by rw [k₃ _ (by decide), k₂ _ (by decide), k₁ _ (by decide)]
  refine WA.append ((mul_ok .s4 0 (by decide) (by decide) hk (hM.keep K₃) (hKm M₃)).mono fun a₄ ⟨hh0, hh1, k₄, m₄⟩ => ?_)
  rw [y1₃] at hh0 hh1
  refine WA.append (WA.mono (Q := fun a' => a'.g .a4 = a₄.g .a4 ^^^ a₄.g .s6 ∧
    a'.g .s9 = a₄.g .s9 ^^^ a₄.g .s7 ^^^ a₄.g .s6 ∧ a'.g .s4 = a₄.g .s7 ∧ Keeps [.a4, .s9, .s4] a₄ a' ∧ a'.m = a₄.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  intro a₅ ⟨x₅, y₅, z₅, k₅, m₅⟩
  have K₅ : Keeps coreRegs a a₅ := K₃.trans ((k₄.mono (by decide)).trans (k₅.mono (by decide)))
  have M₅ : a₅.m = a.m := by rw [m₅, m₄, M₃]
  have y0₅ : a₅.g .s5 = a.g .s5 := by rw [k₅ _ (by decide), k₄ _ (by decide), y0₃]
  refine WA.append ((mul_ok .s5 1 (by decide) (by decide) hk (hM.keep K₅) (hKm M₅)).mono fun a₆ ⟨l0, l1, k₆, m₆⟩ => ?_)
  rw [y0₅] at l0 l1
  generalize hc : VectorCrypto.polyMul (a.g .s4 ^^^ a.g .s5) (kdOf h1 h0 2) = c at c0 c1
  generalize hh : VectorCrypto.polyMul (a.g .s4) (kdOf h1 h0 0) = h at hh0 hh1
  generalize hl : VectorCrypto.polyMul (a.g .s5) (kdOf h1 h0 1) = l at l0 l1
  refine WA.append (WA.mono (Q := fun a' => a'.g .a4 = a₆.g .a4 ^^^ a₆.g .s6 ^^^ a₆.g .s7 ∧
    a'.g .s9 = a₆.g .s9 ^^^ a₆.g .s7 ^^^ a₆.g .s6 ∧ Keeps [.a4, .s9] a₆ a' ∧ a'.m = a₆.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  intro a₇ ⟨x₇, y₇, k₇, m₇⟩
  refine WA.append ((foldDn_ok .a0 false .a4 .s6 .t0 (by decide) (by decide) (by decide) (by decide) (by decide) a₇).mono
    fun a₈ ⟨e₈, k₈, m₈⟩ => ?_)
  refine WA.append ((foldUp_ok .a0 false .s9 .s6 .t0 (by decide) (by decide) (by decide) (by decide) (by decide) a₈).mono
    fun a₉ ⟨e₉, k₉, m₉⟩ => ?_)
  refine WA.append (WA.mono (Q := fun a' => a'.g .s4 = a₉.g .s4 ^^^ a₉.g .a4 ∧ Keeps [.s4] a₉ a' ∧ a'.m = a₉.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [A.g_set, ite_eq_right hq]
  intro a₁₀ ⟨e₁₀, k₁₀, m₁₀⟩
  refine WA.append ((foldUp_ok .a0 false .s4 .a4 .t0 (by decide) (by decide) (by decide) (by decide) (by decide) a₁₀).mono
    fun a₁₁ ⟨e₁₁, k₁₁, m₁₁⟩ => ?_)
  refine WA.append ((foldDn_ok .a0 false .s9 .a4 .t0 (by decide) (by decide) (by decide) (by decide) (by decide) a₁₁).mono
    fun a₁₂ ⟨e₁₂, k₁₂, m₁₂⟩ => ?_)
  have hu : a₈.g .a4 = vdword (c ^^^ l ^^^ h) 0 ^^^ vdword l 1 ^^^ dn (vdword l 0) := by
    rw [e₈, x₇, k₇ .s6 (by decide), k₆ .a4 (by decide), x₅, k₄ .a4 (by decide), x₃, c0, hh0, l0, l1, vdword_xor,
      vdword_xor, xor_u]
  have hr1 : a₁₂.g .s4 = (redW l h c).1 := by
    rw [k₁₂ _ (by decide), e₁₁, e₁₀, k₁₀ .a4 (by decide), k₉ .a4 (by decide), hu, k₉ .s4 (by decide),
      k₈ .s4 (by decide), k₇ .s4 (by decide), k₆ .s4 (by decide), z₅, hh1, redW]
  have hr0 : a₁₂.g .s9 = (redW l h c).2 := by
    rw [e₁₂, k₁₁ .s9 (by decide), k₁₁ .a4 (by decide), k₁₀ .s9 (by decide), k₁₀ .a4 (by decide), e₉,
      k₉ .a4 (by decide), hu, k₈ .s9 (by decide), k₈ .s6 (by decide), k₇ .s6 (by decide), y₇, k₆ .s9 (by decide), y₅,
      k₄ .s9 (by decide), y₃, c1, hh0, hh1, l0, l1, redW, vdword_xor _ _ 1, vdword_xor _ _ 1, xor_mid]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · show (a₁₂.g .s4 ++ a₁₂.g .s9 : BitVec 128) = _
    rw [hr1, hr0, ← Spread.mul_words, mulW, ← hl, ← hh, ← hc, BitVec.xor_comm (a.g .s4)]
    simp only [kdOf, BitVec.xor_comm (keyW1 h1 h0)]
  · refine K₅.trans ((k₆.mono (by decide)).trans ((k₇.mono (by decide)).trans ((k₈.mono (by decide)).trans
      ((k₉.mono (by decide)).trans ((k₁₀.mono (by decide)).trans ((k₁₁.mono (by decide)).trans
      ((k₁₂.mono (by decide)).trans fun q hq => ?_)))))))
    rw [A.g_set, ite_eq_right fun e => hq (by rw [e]; decide)]
  · show a₁₂.m = a.m
    rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, M₅]

/-! ## The key -/

theorem hi_w2 (h1 h0 : BitVec 64) : Spec.Gcm.ghashHi (w2 h1 h0) = h1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (((h1 ++ h0 : BitVec (64 + 64)) >>> 64).setWidth 64).getLsbD i = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [hi]

theorem lo_w2 (h1 h0 : BitVec 64) : Spec.Gcm.ghashLo (w2 h1 h0) = h0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((h1 ++ h0 : BitVec (64 + 64)).setWidth 64).getLsbD i = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi]

theorem ghashKey0_eq (h1 h0 : BitVec 64) : Spec.Gcm.ghashKey0 (w2 h1 h0) = keyW1 h1 h0 := by
  have h : ∀ c : Bool, (0#64 - (if c then 1#64 else 0#64)) &&& 0xc200000000000000#64 = dn (if c then 1#64 else 0#64) := by
    decide
  rw [Spec.Gcm.ghashKey0, hi_w2, lo_w2, keyW1, Clmul.ushr63 h1, h]

theorem ghashKey1_eq (h1 h0 : BitVec 64) : Spec.Gcm.ghashKey1 (w2 h1 h0) = keyW0 h1 h0 := by
  have h : ∀ c : Bool, (0#64 - (if c then 1#64 else 0#64)) &&& 1#64 = if c then 1#64 else 0#64 := by decide
  rw [Spec.Gcm.ghashKey1, hi_w2, lo_w2, keyW0, Clmul.ushr63 h1, h]

theorem ghashOperand_of (h1 h0 : BitVec 64) {i : Nat} (hi : i < 9) :
    ghashOperand (w2 h1 h0) i =
      if i % 3 = 0 then lo32 (kdOf h1 h0 (i / 3)) else if i % 3 = 1 then hi32 (kdOf h1 h0 (i / 3))
      else lo32 (kdOf h1 h0 (i / 3)) ^^^ hi32 (kdOf h1 h0 (i / 3)) := by
  have hd : i / 3 = 0 ∨ i / 3 = 1 ∨ i / 3 = 2 := by omega
  rw [ghashOperand, ghashKey0_eq, ghashKey1_eq]
  rcases hd with e | e | e <;> simp only [e, kdOf, reduceCtorEq, ite_true, ite_false, Nat.reduceEqDiff] <;> rfl

theorem keyOf (h1 h0 : BitVec 64) : KeyOf (ghashOperand (w2 h1 h0)) (kdOf h1 h0) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [ghashOperand_of _ _ (by omega), ite_eq_left (by omega), show 3 * t / 3 = t by omega]
  · rw [ghashOperand_of _ _ (by omega), ite_eq_right (by omega), ite_eq_left (by omega), show (3 * t + 1) / 3 = t by omega]
  · rw [ghashOperand_of _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      show (3 * t + 2) / 3 = t by omega]

theorem classStore_ok (i : Nat) (r : Reg) (j : Nat) (hi : i < 9) (hj : j < 4) {a : A} (hM : Masks a) :
    WA .s9 true (classStore i r j) a fun a' => a'.m (4 * i + j) = a.g r &&& m4 j ∧
      (∀ k, k ≠ 4 * i + j → a'.m k = a.m k) ∧ Keeps [.a7] a a' := by
  have hs := slot_ok hi hj
  have hm : ∀ j < 4, maskReg j ≠ .a7 := by decide
  simp only [WA, classStore, andI, evalA, stepA, logicV, Option.bind_some, A.g_set, A.m_set, A.m_put, reduceCtorEq, hs,
    ite_false, ite_true, ne_eq, not_true_eq_false, or_self, Option.some.injEq, exists_eq_left', hM j hj]
  refine ⟨trivial, fun k hk => by simp only [hk, ite_false], fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [A.g_put, A.g_set, hq, ite_false]

theorem operand_ok (i : Nat) (r : Reg) (hi : i < 9) (hr : r ≠ .a7) {a : A} (hM : Masks a) :
    WA .s9 true (operand i r) a fun a' => (∀ j < 4, a'.m (4 * i + j) = a.g r &&& m4 j) ∧
      (∀ k, k < 4 * i ∨ 4 * i + 4 ≤ k → a'.m k = a.m k) ∧ Keeps [.a7] a a' := by
  have hr' : r ∉ [Reg.a7] := by simp [hr]
  have h : ∀ n ≤ 4, WA .s9 true ((List.range n).flatMap (classStore i r)) a fun a' =>
      (∀ j < n, a'.m (4 * i + j) = a.g r &&& m4 j) ∧
      (∀ k, k < 4 * i ∨ 4 * i + 4 ≤ k → a'.m k = a.m k) ∧ Keeps [.a7] a a' := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨a, rfl, fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ => rfl⟩
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine WA.append ((ih (by omega)).mono fun b ⟨h1, h2, h3⟩ => ?_)
      refine (classStore_ok i r n hi (by omega) (hM.keep h3)).mono
        fun c ⟨g1, g2, g3⟩ => ⟨fun j hj => ?_, fun k hk => ?_, h3.trans g3⟩
      · by_cases e : j = n
        · subst e; rw [g1, h3 r hr']
        · rw [g2 _ (by omega), h1 j (by omega)]
      · rw [g2 k (by omega), h2 k hk]
  exact h 4 (Nat.le_refl 4)

abbrev opRegs : List Reg := [.t0, .t5, .t6, .a7]

theorem operands_ok (t : Nat) (r : Reg) (ht : t < 3) (hr : r ∉ opRegs) {a : A} (hM : Masks a) :
    WA .s9 true (operands t r) a fun a' => (∀ j < 4, a'.m (4 * (3 * t) + j) = lo32 (a.g r) &&& m4 j) ∧
      (∀ j < 4, a'.m (4 * (3 * t + 1) + j) = hi32 (a.g r) &&& m4 j) ∧
      (∀ j < 4, a'.m (4 * (3 * t + 2) + j) = (lo32 (a.g r) ^^^ hi32 (a.g r)) &&& m4 j) ∧
      (∀ k, k < 12 * t ∨ 12 * t + 12 ≤ k → a'.m k = a.m k) ∧ Keeps opRegs a a' := by
  have hr' := hr
  simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  rw [operands, List.append_assoc, List.append_assoc]
  refine WA.append (WA.mono (Q := fun a' => a'.g .t5 = lo32 (a.g r) ∧ a'.g .t6 = hi32 (a.g r) ∧
    a'.g .t0 = lo32 (a.g r) ^^^ hi32 (a.g r) ∧ Keeps opRegs a a' ∧ a'.m = a.m) ?_ ?_)
  · simp (config := {decide := true}) only [WA, sll, srl, xorI, evalA, stepA, logicV, Option.bind_some, A.g_set, hr',
      ite_false, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, rfl, fun q hq => ?_, by first | exact trivial | rfl⟩
    simp only [opRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  intro a₁ ⟨x, y, z, k₁, m₁⟩
  refine WA.append ((operand_ok (3 * t) .t5 (by omega) (by decide) (hM.keep k₁)).mono fun a₂ ⟨e₂, m₂, k₂⟩ => ?_)
  have K₂ : Keeps opRegs a a₂ := k₁.trans (k₂.mono (by decide))
  refine WA.append ((operand_ok (3 * t + 1) .t6 (by omega) (by decide) (hM.keep K₂)).mono fun a₃ ⟨e₃, m₃, k₃⟩ => ?_)
  have K₃ : Keeps opRegs a a₃ := K₂.trans (k₃.mono (by decide))
  refine (operand_ok (3 * t + 2) .t0 (by omega) (by decide) (hM.keep K₃)).mono fun a₄ ⟨e₄, m₄, k₄⟩ =>
    ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, K₃.trans (k₄.mono (by decide))⟩
  · rw [m₄ _ (by omega), m₃ _ (by omega), e₂ j hj, x]
  · rw [m₄ _ (by omega), e₃ j hj, k₂ _ (by decide), y]
  · rw [e₄ j hj, k₃ _ (by decide), k₂ _ (by decide), z]
  · rw [m₄ _ (by omega), m₃ _ (by omega), m₂ _ (by omega), m₁]

theorem adjust_ok (a : A) :
    WA .s9 true adjust a fun a' => a'.g .t4 = keyW1 (a.g .t1) (a.g .t2) ∧ a'.g .t2 = keyW0 (a.g .t1) (a.g .t2) ∧
      a'.g .t3 = a'.g .t4 ^^^ a'.g .t2 ∧ Keeps [.t2, .t3, .t4, .t5, .t6] a a' ∧ a'.m = a.m := by
  rw [adjust, List.append_assoc]
  refine WA.append (WA.mono (Q := fun a' => a'.g .t4 = a.g .t1 <<< 1 ^^^ a.g .t2 >>> 63 ∧
    a'.g .t2 = keyW0 (a.g .t1) (a.g .t2) ∧ a'.g .t5 = a.g .t1 >>> 63 ∧ Keeps [.t2, .t3, .t4, .t5, .t6] a a' ∧
    a'.m = a.m) ?_ ?_)
  · refine ⟨_, rfl, rfl, rfl, rfl, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]
  intro a₁ ⟨x, y, z, k₁, m₁⟩
  refine WA.append ((foldDn_ok .s9 true .t4 .t5 .t6 (by decide) (by decide) (by decide) (by decide) (by decide) a₁).mono
    fun a₂ ⟨e₂, k₂, m₂⟩ => ?_)
  refine ⟨_, rfl, ?_, ?_, rfl, fun q hq => ?_, ?_⟩
  · show a₂.g .t4 = _
    rw [e₂, x, z, keyW1]
  · show a₂.g .t2 = _
    rw [k₂ _ (by decide), y]
  · rw [A.g_set, ite_eq_right fun e => hq (by rw [e]; decide), k₂ q fun h => hq ((by decide : ∀ r ∈ [Reg.t4, .t6], r ∈ [Reg.t2, .t3, .t4, .t5, .t6]) q h),
      k₁ q hq]
  · show a₂.m = a.m
    rw [m₂, m₁]

theorem keyCode_eq : keyCode = maskCode ++ (adjust ++ (operands 0 .t4 ++ (operands 1 .t2 ++ operands 2 .t3))) := by
  simp only [keyCode, List.append_assoc]

abbrev keyRegs : List Reg := [.t0, .t2, .t3, .t4, .t5, .t6, .a7]

theorem key_ok (h1 h0 : BitVec 64) {a : A} (hM : Masks a) (e1 : a.g .t1 = h1) (e2 : a.g .t2 = h0) :
    WA .s9 true (adjust ++ (operands 0 .t4 ++ (operands 1 .t2 ++ operands 2 .t3))) a fun a' =>
      Key (ghashOperand (w2 h1 h0)) a' ∧ Keeps keyRegs a a' := by
  refine WA.append ((adjust_ok a).mono fun a₁ ⟨x, y, z, k₁, m₁⟩ => ?_)
  rw [e1, e2] at x y
  have hM₁ := hM.keep k₁
  refine WA.append ((operands_ok 0 .t4 (by decide) (by decide) hM₁).mono fun a₂ ⟨l₂, h₂, s₂, m₂, k₂⟩ => ?_)
  have hM₂ := hM₁.keep k₂
  refine WA.append ((operands_ok 1 .t2 (by decide) (by decide) hM₂).mono fun a₃ ⟨l₃, h₃, s₃, m₃, k₃⟩ => ?_)
  refine (operands_ok 2 .t3 (by decide) (by decide) (hM₂.keep k₃)).mono fun a₄ ⟨l₄, h₄, s₄, m₄, k₄⟩ => ⟨?_, ?_⟩
  · have d0 : a₁.g .t4 = kdOf h1 h0 0 := x
    have d1 : a₂.g .t2 = kdOf h1 h0 1 := by rw [k₂ _ (by decide), y]; rfl
    have d2 : a₃.g .t3 = kdOf h1 h0 2 := by rw [k₃ _ (by decide), k₂ _ (by decide), z, x, y]; rfl
    rw [d0] at l₂ h₂ s₂
    rw [d1] at l₃ h₃ s₃
    rw [d2] at l₄ h₄ s₄
    have ko := keyOf h1 h0
    intro i hi j hj
    have hc : ∃ t r, t < 3 ∧ r < 3 ∧ i = 3 * t + r := ⟨i / 3, i % 3, by omega, by omega, by omega⟩
    obtain ⟨t, r, ht, hr, rfl⟩ := hc
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr' with rfl | rfl | rfl
    · rw [Nat.add_zero, ko.lo t ht]
      rcases ht' with rfl | rfl | rfl
      · rw [m₄ _ (by omega), m₃ _ (by omega)]; exact l₂ j hj
      · rw [m₄ _ (by omega)]; exact l₃ j hj
      · exact l₄ j hj
    · rw [ko.hi t ht]
      rcases ht' with rfl | rfl | rfl
      · rw [m₄ _ (by omega), m₃ _ (by omega)]; exact h₂ j hj
      · rw [m₄ _ (by omega)]; exact h₃ j hj
      · exact h₄ j hj
    · rw [ko.sum t ht]
      rcases ht' with rfl | rfl | rfl
      · rw [m₄ _ (by omega), m₃ _ (by omega)]; exact s₂ j hj
      · rw [m₄ _ (by omega)]; exact s₃ j hj
      · exact s₄ j hj
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide))))

/-! ## On the machine -/

theorem maskCode_ok (h : Rel b w s₀ s a) (hb : b ∉ [Reg.t0, .s0, .s1, .s2, .s3]) :
    WP isa (.block maskCode) s fun s' => ∃ a', Rel b w s₀ s' a' ∧ Masks a' ∧ Keeps [.t0, .s0, .s1, .s2, .s3] a a' ∧
      a'.m = a.m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  rw [maskCode, WP.block_append_iff]
  refine WP.mono (ByteLoad.li64_ok (by decide) _) fun s₁ e₁ => ?_
  subst e₁
  have r₁ := (h.set (d := .t0) (Ne.symm hb.1) (sext32 ((mask 0).setWidth 32))).set (d := .s0) (Ne.symm hb.2.1) (mask 0)
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_cons_iff.mpr ⟨_, rfl,
    WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨_, ((r₁.set (d := .s1) (Ne.symm hb.2.2.1) _).set
      (d := .s2) (Ne.symm hb.2.2.2.1) _).set (d := .s3) (Ne.symm hb.2.2.2.2) _, ?_, fun q hq => ?_, rfl⟩⟩⟩⟩
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]

theorem prep_ok (s : State) (hH : InRegions (s.rd ++ s.wr) (s.gpr HP) 16)
    (hW : ∀ k < 36, (s.gpr FP + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 ∧
      InRegions s.wr (s.gpr FP + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block prep) s fun t =>
      (∀ i < 9, ∀ j < 4, t.mem.readW (s.gpr FP + BitVec.ofNat 64 (8 * (4 * i + j))) 64 =
        ghashOperand (blockAt s.mem (s.gpr HP)) i &&& ghashClass j) ∧
      (∀ j < 4, t.gpr (maskReg j) = m4 j) ∧
      (∀ r, r ∉ prepWrites → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr FP, 288⟩] s.mem t.mem := by
  have hw : Words .s9 true s := ⟨fun k hk => (hW k hk).1,
    fun k hk => by
      obtain ⟨R, hR, hc⟩ := (hW k hk).2
      exact ⟨R, List.mem_append_right _ hR, hc⟩, fun _ k hk => (hW k hk).2⟩
  have hin : ∀ o, o + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr HP + BitVec.ofNat 64 o) 8 := fun o ho => by
    obtain ⟨R, hR, hc⟩ := hH
    refine ⟨R, hR, ?_⟩
    have := hc
    simp only [Region.Contains] at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (s.gpr HP - R.base).isLt
    omega
  have r₀ : Rel .s9 true s s ⟨s.gpr, fun k => s.mem.readW (s.gpr .s9 + BitVec.ofNat 64 (8 * k)) 64⟩ :=
    ⟨rfl, Slots.init _ _ _, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  rw [prep, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide) (hin 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  have r₁ := (r₀.set (d := .t0) (by decide) ((s.mem (s.gpr HP + BitVec.ofNat 64 (0 + 7))).setWidth 64)).set (d := .t1)
    (by decide) (ByteLoad.be64 s.mem (s.gpr HP) 0)
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide) (hin 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  have r₂ := (r₁.set (d := .t0) (by decide) ((s.mem (s.gpr HP + BitVec.ofNat 64 (8 + 7))).setWidth 64)).set (d := .t2)
    (by decide) (ByteLoad.be64 s.mem (s.gpr HP) 8)
  rw [keyCode_eq, WP.block_append_iff]
  refine WP.mono (maskCode_ok r₂ (by decide)) fun s₃ ⟨a₃, r₃, hM, k₃, m₃⟩ => ?_
  refine WP.mono (WA.sound hw r₃ (key_ok (ByteLoad.be64 s.mem (s.gpr HP) 0) (ByteLoad.be64 s.mem (s.gpr HP) 8) hM
    (by rw [k₃ _ (by decide)]; rfl) (by rw [k₃ _ (by decide)]; rfl))) fun s₄ ⟨a₄, r₄, hK, k₄⟩ => ?_
  refine ⟨fun i hi j hj => ?_, fun j hj => by rw [r₄.g]; exact (hM.keep k₄) j hj, fun q hq => ?_, r₄.rd, r₄.wr, r₄.sp, r₄.m.frame⟩
  · rw [blockAt_hOf, hOf]
    exact (r₄.m.get (4 * i + j) (by omega)).trans (hK i hi j hj)
  · rw [r₄.g, k₄ q fun h => hq ((by decide : ∀ r ∈ keyRegs, r ∈ prepWrites) q h),
      k₃ q fun h => hq ((by decide : ∀ r ∈ [Reg.t0, .s0, .s1, .s2, .s3], r ∈ prepWrites) q h)]
    simp only [prepWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]

instance instPrepLaw : PrepLaw where
  ok s hH hW := WP.mono (prep_ok s hH hW) fun _ ⟨h1, _, h2⟩ => ⟨h1, h2⟩

/-! ### The loop -/

/-- What holds in the loop, from its entry's state `s₁`: `i` of the blocks at
`D` are absorbed. -/
structure InvL (s₁ : State) (h1 h0 : BitVec 64) (Y : Block) (D : Addr) (n i : Nat) (s : State) : Prop where
  le : i ≤ n
  ex : ∃ a, Rel .a0 false s₁ s a ∧ Masks a ∧ Key (ghashOperand (w2 h1 h0)) a ∧
    a.g .s4 ++ a.g .s5 = ghashFrom (w2 h1 h0) Y (blocksAt s₁.mem D i) ∧ a.g .a2 = D + BitVec.ofNat 64 (16 * i) ∧
    a.g .a3 = BitVec.ofNat 64 (n - i) ∧ a.g .a1 = s₁.gpr .a1 ∧ a.g .ra = s₁.gpr .ra

theorem next_ok (h : Rel .a0 false s₀ s a) :
    WP isa (.block [.addi .a2 .a2 16, .addi .a3 .a3 (-1)]) s fun s' =>
      Rel .a0 false s₀ s' ((a.set .a2 (a.g .a2 + BitVec.ofNat 64 16)).set .a3 (a.g .a3 - BitVec.ofNat 64 1)) := by
  have r := (h.set (d := .a2) (by decide) (a.g .a2 + BitVec.ofNat 64 16)).set (d := .a3) (by decide)
    (a.g .a3 - BitVec.ofNat 64 1)
  have x₁ : exec (.addi .a2 .a2 16) s = some (s.write .a2 (a.g .a2 + BitVec.ofNat 64 16)) := by
    rw [← h.g]; exact exec_addi_nat (n := .a2) (m := 16) (by decide)
  have x₂ : exec (.addi .a3 .a3 (-1)) (s.write .a2 (a.g .a2 + BitVec.ofNat 64 16)) =
      some ((s.write .a2 (a.g .a2 + BitVec.ofNat 64 16)).write .a3 (a.g .a3 - BitVec.ofNat 64 1)) := by
    rw [← h.g]; exact exec_addi_neg_nat (n := .a3) (m := 1) (by decide)
  exact WP.block_cons_iff.mpr ⟨_, x₁, WP.block_cons_iff.mpr ⟨_, x₂, WP.block_nil r⟩⟩

variable {s₁ : State} {h1 h0 : BitVec 64} {Y : Block} {D : Addr} {n : Nat}

theorem body_ok (hw : Words .a0 false s₁)
    (hD : ∀ i < n, InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 (16 * i)) 16) {i : Nat} (hi : i < n) {s : State}
    (hI : InvL s₁ h1 h0 Y D n i s) : WP isa (.block body) s (InvL s₁ h1 h0 Y D n (i + 1)) := by
  obtain ⟨-, a, r, hM, hK, hy, h2, h3, h1a, hra⟩ := hI
  have hin : ∀ (t : State), t.rd = s₁.rd → t.wr = s₁.wr → t.gpr .a2 = D + BitVec.ofNat 64 (16 * i) →
      ∀ o, o + 8 ≤ 16 → InRegions (t.rd ++ t.wr) (t.gpr .a2 + BitVec.ofNat 64 o) 8 := by
    intro t e1 e2 e3 o ho
    rw [e1, e2, e3]
    obtain ⟨R, hR, hc⟩ := hD i hi
    refine ⟨R, hR, ?_⟩
    simp only [Region.Contains] at hc ⊢
    rw [BitVec.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (D + BitVec.ofNat 64 (16 * i) - R.base).isLt
    omega
  have ha2 : s.gpr .a2 = D + BitVec.ofNat 64 (16 * i) := by rw [r.g, h2]
  have hmem : s.mem = s₁.mem := r.ro rfl
  simp only [body, loadX, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide)
    (hin s r.rd r.wr ha2 0 (by decide))) fun s₂ e₂ => ?_
  subst e₂
  have r₂ := (r.set (d := .t0) (by decide) ((s.mem (s.gpr .a2 + BitVec.ofNat 64 (0 + 7))).setWidth 64)).set (d := .s6)
    (by decide) (ByteLoad.be64 s.mem (s.gpr .a2) 0)
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide)
    (hin _ r₂.rd r₂.wr ha2 8 (by decide))) fun s₃ e₃ => ?_
  subst e₃
  have r₃ := (r₂.set (d := .t0) (by decide) ((s.mem (s.gpr .a2 + BitVec.ofNat 64 (8 + 7))).setWidth 64)).set (d := .s7)
    (by decide) (ByteLoad.be64 s.mem (s.gpr .a2) 8)
  rw [WP.block_append_iff]
  refine WP.mono (RISCV64.sound hw r₃ (a' := (A.set _ .s4 _).set .s5 _) rfl) fun s₄ r₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hw r₄ (core_ok h1 h0 (keyOf h1 h0) (fun j hj => by
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases hj' with rfl | rfl | rfl | rfl
      · exact hM 0 (by decide)
      · exact hM 1 (by decide)
      · exact hM 2 (by decide)
      · exact hM 3 (by decide)) hK)) fun s₅ ⟨a₅, r₅, y₅, k₅, m₅⟩ => ?_
  refine WP.mono (next_ok r₅) fun s₆ r₆ => ⟨hi, _, r₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl
    · exact (k₅ .s0 (by decide)).trans (hM 0 (by decide))
    · exact (k₅ .s1 (by decide)).trans (hM 1 (by decide))
    · exact (k₅ .s2 (by decide)).trans (hM 2 (by decide))
    · exact (k₅ .s3 (by decide)).trans (hM 3 (by decide))
  · intro i hi j hj
    show a₅.m _ = _
    rw [m₅]; exact hK i hi j hj
  · refine Eq.trans y₅ ?_
    have hX : blockAt s₁.mem (D + BitVec.ofNat 64 (16 * i)) = w2 (ByteLoad.be64 s.mem (s.gpr .a2) 0)
        (ByteLoad.be64 s.mem (s.gpr .a2) 8) := by rw [blockAt_hOf, hOf, hmem, ha2]
    rw [ghashFrom_blocksAt_succ, ← hy, hX, w2, BitVec.xor_append]
    rfl
  · show a₅.g .a2 + BitVec.ofNat 64 16 = _
    rw [k₅ _ (by decide)]
    show a.g .a2 + _ = _
    rw [h2]
    exact Offset.add_add_eq _ (by omega)
  · show a₅.g .a3 - BitVec.ofNat 64 1 = _
    rw [k₅ _ (by decide)]
    show a.g .a3 - _ = _
    rw [h3]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact (k₅ _ (by decide)).trans h1a
  · exact (k₅ _ (by decide)).trans hra

theorem loop_ok (hw : Words .a0 false s₁) (hn : 16 * n < 2 ^ 64)
    (hD : ∀ i < n, InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 (16 * i)) 16) {s : State}
    (hI : InvL s₁ h1 h0 Y D n 0 s) : WP isa loopCode s (InvL s₁ h1 h0 Y D n n) := by
  have hz : ∀ {i : Nat} {s : State}, InvL s₁ h1 h0 Y D n i s → (s.gpr .a3 == 0) = decide (n - i = 0) := by
    intro i s ⟨_, a, r, _, _, _, _, h3, _, _⟩
    rw [r.g, h3]
    by_cases h : n - i = 0
    · rw [h]; rfl
    · rw [decide_eq_false h, beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h this
  refine WP.ite (decide (n - 0 = 0)) (by simp only [eval, hz hI]) (fun h => ?_) (fun h => ?_)
  · have h0 : n = 0 := by simpa using h
    exact WP.block_nil (h0 ▸ hI)
  · have hn0 : 0 < n := Nat.pos_of_ne_zero (by simpa using h)
    let I : Nat → State → Prop := fun m s => ∃ i, m = n - i ∧ i < n ∧ InvL s₁ h1 h0 Y D n i s
    have hstep : ∀ m s, I m s → WP isa (.block body) s (fun s' =>
        (eval (.nonzero .a3) s' = some false ∧ InvL s₁ h1 h0 Y D n n s') ∨
        (eval (.nonzero .a3) s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hw hD hi hI) fun s' hI' => ?_
      have hz' := hz hI'
      by_cases hl : n - (i + 1) = 0
      · have : i + 1 = n := by omega
        rw [decide_eq_true hl] at hz'
        exact .inl ⟨by simp only [eval, bne, hz', Bool.not_true], this ▸ hI'⟩
      · rw [decide_eq_false hl] at hz'
        exact .inr ⟨by simp only [eval, bne, hz', Bool.not_false], n - (i + 1), by omega, i + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep n s ⟨0, rfl, hn0, hI⟩

/-! ### The frames -/

/-- The loop and the end, in a frame of `F` bytes at `B` that holds `s₀`'s
registers at `o`. -/
theorem rest_ok {s₀ : State} (hw : Words .a0 false s₁) (hn : 16 * n < 2 ^ 64)
    (hD : ∀ i < n, InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 (16 * i)) 16) {B : Addr} {F o : Nat}
    (hB : B.toNat % 16 = 0) (hsp : s₁.sp = B) (hF : F ≤ 2048) (ho : o = 0 ∨ o = 1952) (hoF : o + 96 ≤ F)
    (hfr : (⟨B, F⟩ : Region) ∈ s₁.wr)
    (hsv : Spill.Saved B s₀.gpr (savedAt o) s₁.mem) {s : State} (hI : InvL s₁ h1 h0 Y D n 0 s) :
    WP isa (.seq loopCode (.block (finish o))) s fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.gpr .ra = s₁.gpr .ra ∧ t.gpr .a1 = s₁.gpr .a1 ∧ t.sp = B ∧
      t.wr = s₁.wr ∧ t.rd = s₁.rd ∧
      t.gpr .t1 ++ t.gpr .t2 = ghashFrom (w2 h1 h0) Y (blocksAt s₁.mem D n) := by
  refine WP.seq (WP.mono (loop_ok hw hn hD hI) fun s₂ ⟨_, a, r, _, _, hy₂, _, _, ha1, hra⟩ => ?_)
  have hst : ∀ p ∈ savedAt o, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ p.2 + 8 ≤ F := by
    have h1 : ∀ p ∈ savedAt 0, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ p.2 + 8 ≤ 96 := by decide
    have h2 : ∀ p ∈ savedAt 1952, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ p.2 + 8 ≤ 1952 + 96 := by decide
    intro p hp
    rcases ho with rfl | rfl
    · have := h1 p hp; omega
    · have := h2 p hp; omega
  have hre : Spill.Restorable .t0 (savedAt o) := by rcases ho with rfl | rfl <;> decide
  have hfst : (savedAt o).map Prod.fst = saved := by rcases ho with rfl | rfl <;> decide
  have hfin : finish o = ([mv .t1 .s4, mv .t2 .s5] : List Instr) ++ (([.addSp .t0 0] : List Instr) ++
      Spill.restoreCode .t0 (savedAt o)) := by
    simp only [finish, List.cons_append, List.nil_append]; rfl
  rw [hfin, WP.block_append_iff]
  refine WP.mono (RISCV64.sound hw r (a' := (a.set .t1 (a.g .s4)).set .t2 (a.g .s5)) rfl) fun s₃ r₃ => ?_
  rw [WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨s₃.write .t0 (s₃.sp + BitVec.ofNat 64 0), rfl, WP.block_nil ?_⟩
  have hB₃ : s₃.sp + BitVec.ofNat 64 0 = B := by rw [r₃.sp, hsp]; exact BitVec.add_zero B
  rw [hB₃]
  have r₄ := r₃.set (d := .t0) (by decide) B
  have hm₃ : s₃.mem = s₁.mem := r₃.ro rfl
  refine WP.mono (Spill.restore_wp (B := B) (g := s₀.gpr) (by omega) (by rw [r₄.g]; rfl)
    (fun p hp => ⟨(hst p hp).1, (hst p hp).2.1⟩) hre
    (fun p hp => ⟨⟨B, F⟩, List.mem_append_right _ (by rw [r₄.wr]; exact hfr),
      Offset.contains_base B (by have := hst p hp; omega) (by have := hst p hp; omega)⟩)
    (by show Spill.Saved B s₀.gpr (savedAt o) s₃.mem; rw [hm₃]; exact hsv)) fun s₅ hR => ?_
  have g₅ : ∀ q, q ∉ saved → s₅.gpr q = (A.set (A.set (A.set a .t1 (a.g .s4)) .t2 (a.g .s5)) .t0 B).g q := fun q hq => by
    rw [hR.other q (by rw [hfst]; exact hq), r₄.g]
  refine ⟨fun q hq => ?_, ?_, ?_, ?_, hR.wr.trans r₄.wr, hR.rd.trans r₄.rd, ?_⟩
  · have hp : ∀ q ∈ preserved, q ∈ saved := by decide
    have hq' := hp q hq
    rw [← hfst] at hq'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact hR.gpr p hp
  · rw [g₅ _ (by decide)]; exact hra
  · rw [g₅ _ (by decide)]; exact ha1
  · rw [hR.sp]; exact r₃.sp.trans hsp
  · have e1 : s₅.gpr .t1 = a.g .s4 := g₅ .t1 (by decide)
    have e2 : s₅.gpr .t2 = a.g .s5 := g₅ .t2 (by decide)
    rw [e1, e2, hy₂]

/-- The frame released, and `Y` stored. -/
theorem frame_ok {s₀ : State} {F : Nat} {body : Prog isa} (hF : 0 < F ∧ F ≤ 4064 ∧ F % 16 = 0) (hsp : F ≤ s₀.sp.toNat)
    {v : Block} (hy : (⟨s₀.gpr .a1, 16⟩ : Region) ∈ s₀.wr)
    (h : WP isa body (allocd F s₀) fun t => (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.gpr .ra = s₀.gpr .ra ∧
      t.gpr .a1 = s₀.gpr .a1 ∧ t.sp = s₀.sp - BitVec.ofNat 64 F ∧ t.wr = (allocd F s₀).wr ∧ t.rd = s₀.rd ∧
      t.gpr .t1 ++ t.gpr .t2 = v) :
    ∃ t s', Exec isa (.seq (.frame (.alloc F) body (.free F)) (.block storeY)) s₀ t s' ∧ abiPreserved s₀ s' ∧
      blockAt s'.mem (s₀.gpr .a1) = v := by
  change WP isa _ s₀ fun s' => abiPreserved s₀ s' ∧ blockAt s'.mem (s₀.gpr .a1) = v
  refine WP.seq (WP.allocLe hF hsp (WP.mono h ?_))
  intro t ⟨hg, hra, ha1, htsp, hwr, _, hv⟩ m u _
  have hout : ∀ (t' : State), t'.wr = s₀.wr → t'.gpr .a1 = s₀.gpr .a1 → ∀ k, k + 8 ≤ 16 →
      InRegions t'.wr (t'.gpr .a1 + BitVec.ofNat 64 k) 8 := fun t' e1 e2 k hk =>
    ⟨⟨s₀.gpr .a1, 16⟩, by rw [e1]; exact hy, by rw [e2]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hwr' : (freed F t).wr = s₀.wr := by show t.wr.tail = _; rw [hwr]; rfl
  generalize hf : ({ freed F t with mem := m, unknowns := u } : State) = f
  have fg : f.gpr = t.gpr := by rw [← hf]; rfl
  have fsp : f.sp = s₀.sp := by rw [← hf]; show t.sp + _ = _; rw [htsp, BitVec.sub_add_cancel]
  have fwr : f.wr = s₀.wr := by rw [← hf]; exact hwr'
  have fa : f.gpr .a1 = s₀.gpr .a1 := by rw [fg, ha1]
  refine BE64.wp_storeBE8 (by decide) (by decide) (by decide) rfl (hout f fwr fa 0 (by decide)) fun s₆ s₇ m₆ u₇ => ?_
  have a1₇ : s₇.gpr .a1 = s₀.gpr .a1 := by rw [u₇.other _ (by decide), m₆.gpr, fa]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, m₆.wr, fwr]
  refine BE64.wp_storeBE8 (by decide) (by decide) (by decide) rfl (hout s₇ wr₇ a1₇ 8 (by decide)) fun s₈ s₉ m₈ u₉ => ?_
  have g₉ : ∀ q, q ≠ .t3 → s₉.gpr q = t.gpr q := fun q hq => by
    rw [u₉.other q hq, m₈.gpr, u₇.other q hq, m₆.gpr, fg]
  refine WP.block_nil ⟨⟨fun q hq => ?_, ?_, ?_⟩, ?_⟩
  · have hp : ∀ q ∈ preserved, q ≠ .t3 := by decide
    rw [g₉ q (hp q hq), hg q hq]
  · rw [u₉.sp, m₈.sp, u₇.sp, m₆.sp, fsp]
  · rw [g₉ _ (by decide), hra]
  · have t1 : f.gpr .t1 = t.gpr .t1 := by rw [fg]
    have t2 : s₇.gpr .t2 = t.gpr .t2 := by rw [u₇.other _ (by decide), m₆.gpr, fg]
    rw [← hv, u₉.mem, m₈.mem, u₇.mem, m₆.mem, a1₇, fa, t1, t2, ← BE64.writeBytes_beBytes, ← BE64.writeBytes_beBytes,
      blockAt_store]

/-- `Y` loaded. -/
theorem loadY_ok {s₀ s : State} {a : A} {b : Reg} {w : Bool} (r : Rel b w s₀ s a) (hb : b ∉ [Reg.t0, .s4, .s5])
    (hy : (⟨s.gpr .a1, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block loadY) s fun s' => ∃ a', Rel b w s₀ s' a' ∧
      a'.g .s4 ++ a'.g .s5 = blockAt s.mem (s.gpr .a1) ∧ Keeps [.t0, .s4, .s5] a a' ∧ a'.m = a.m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  have hin : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → t.gpr .a1 = s.gpr .a1 → ∀ o, o + 8 ≤ 16 →
      InRegions (t.rd ++ t.wr) (t.gpr .a1 + BitVec.ofNat 64 o) 8 := fun t e1 e2 e3 o ho =>
    ⟨⟨s.gpr .a1, 16⟩, List.mem_append_right _ (by rw [e2]; exact hy),
      by rw [e3]; exact Offset.contains_base _ (by omega) (by omega)⟩
  rw [loadY, WP.block_append_iff]
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide)
    (hin s rfl rfl rfl 0 (by decide))) fun s₂ e₂ => ?_
  subst e₂
  have r₂ := (r.set (d := .t0) (Ne.symm hb.1) ((s.mem (s.gpr .a1 + BitVec.ofNat 64 (0 + 7))).setWidth 64)).set (d := .s4)
    (Ne.symm hb.2.1) (ByteLoad.be64 s.mem (s.gpr .a1) 0)
  refine WP.mono (ByteLoad.loadBE64_ok (by decide) (by decide) (by decide) (by decide)
    (hin _ rfl rfl rfl 8 (by decide))) fun s₃ e₃ => ?_
  subst e₃
  have r₃ := (r₂.set (d := .t0) (Ne.symm hb.1) ((s.mem (s.gpr .a1 + BitVec.ofNat 64 (8 + 7))).setWidth 64)).set (d := .s5)
    (Ne.symm hb.2.2) (ByteLoad.be64 s.mem (s.gpr .a1) 8)
  refine ⟨_, r₃, ?_, fun q hq => ?_, rfl⟩
  · rw [blockAt_hOf]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_set, hq, ite_false]

/-- The registers saved, at `t0`. -/
theorem saveAt_ok {s : State} {B : Addr} {F o : Nat} (hB : B.toNat % 16 = 0) (hsp : s.sp = B) (hF : F ≤ 2048)
    (ho : o = 0 ∨ o = 1952) (hoF : o + 96 ≤ F) (hfr : (⟨B, F⟩ : Region) ∈ s.wr) :
    WP isa (.block (([.addSp .t0 0] : List Instr) ++ saveAt o)) s fun t => t.gpr .t0 = B ∧
      (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨B + BitVec.ofNat 64 o, 96⟩] s.mem t.mem ∧ Spill.Saved B s.gpr (savedAt o) t.mem := by
  have hst : ∀ p ∈ savedAt o, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ o ≤ p.2 ∧ p.2 + 8 ≤ o + 96 := by
    have h1 : ∀ p ∈ savedAt 0, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 96 := by decide
    have h2 : ∀ p ∈ savedAt 1952, p.2 % 8 = 0 ∧ p.2 < 2048 ∧ 1952 ≤ p.2 ∧ p.2 + 8 ≤ 1952 + 96 := by decide
    rcases ho with rfl | rfl
    · exact h1
    · exact h2
  have hfit : Spill.Fits (savedAt o) := by rcases ho with rfl | rfl <;> decide
  have hnt : ∀ p ∈ savedAt o, p.1 ≠ .t0 := by rcases ho with rfl | rfl <;> decide
  have hB₀ : s.sp + BitVec.ofNat 64 0 = B := by rw [hsp]; exact BitVec.add_zero B
  refine WP.block_cons_iff.mpr ⟨s.write .t0 (s.sp + BitVec.ofNat 64 0), rfl, ?_⟩
  rw [hB₀]
  have ht : (s.write .t0 B).gpr .t0 = B := rfl
  refine WP.mono (Spill.save_wp (b := .t0) (l := savedAt o) (by rw [ht]; omega)
    (fun p hp => ⟨(hst p hp).1, (hst p hp).2.1⟩)
    (fun p hp => ⟨⟨B, F⟩, hfr, by rw [ht]; exact Offset.contains_base B (by have := hst p hp; omega) (by have := hst p hp; omega)⟩))
    fun t h => ⟨by rw [h.gpr]; rfl, fun q hq => by rw [h.gpr]; exact ite_eq_right hq, h.rd, h.wr, h.sp, ?_, ?_⟩
  · rw [h.mem]
    exact Spill.saveMem_frame (fun p hp => (hst p hp).2.2) (by omega) _ _ _
  · rw [h.mem]
    intro p hp
    refine (Spill.saveMem_saved hfit _ _ _ p hp).trans ?_
    exact ite_eq_right (hnt p hp)

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat} (hn : 16 * n < 2 ^ 64)
    (hd : ∀ r ∈ rs, (⟨D, 16 * n⟩ : Region).Disjoint r) : blocksAt m' D n = blocksAt m D n := by
  refine List.map_congr_left fun i hi => blockAt_congr fun j hj => ?_
  have hi' := List.mem_range.mp hi
  rw [Offset.add_add]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by show 16 * n ≤ 2 ^ 64; omega) (by show _ < 16 * n; omega)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p :=
  blockAt_congr fun _ hj => hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; decide) hj

theorem nb_lt {y D : Addr} {n : Nat} (h : (⟨y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩) : 16 * n < 2 ^ 64 := by
  by_contra hc
  refine h y (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (y - D).isLt
  omega

theorem al_frame {B : Addr} (hB : B.toNat % 16 = 0) (k : Nat) : (B + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 :=
  Spill.al8 (by omega) (by omega)

/-- The loop's start, from the masks, the key's words at `a0` and `Y` loaded. -/
theorem inv_start {s t : State} {h1 h0 : BitVec 64} {Y : Block} {D : Addr} {n : Nat} {a : A}
    (r : Rel .a0 false s t a) (hM : Masks a) (hK : Key (ghashOperand (w2 h1 h0)) a) (hy : a.g .s4 ++ a.g .s5 = Y)
    (h2 : a.g .a2 = D) (h3 : a.g .a3 = BitVec.ofNat 64 n) (h1a : a.g .a1 = s.gpr .a1) (hra : a.g .ra = s.gpr .ra) :
    InvL s h1 h0 Y D n 0 t :=
  ⟨Nat.zero_le _, a, r, hM, hK, by rw [hy, ghashFrom_blocksAt_zero], by rw [h2]; exact (BitVec.add_zero D).symm, h3, h1a, hra⟩

instance instGhashLaw : GhashLaw where
  ok s₀ hs := by
    obtain ⟨hrd, hwr, hyd, hfh, hfy, hfd, hyf, hdf, hsa, hsp⟩ := hs
    have hnlt := nb_lt hyd
    generalize hBd : s₀.sp - BitVec.ofNat 64 2048 = B at hfh hfy hfd
    have hBt : B.toNat = s₀.sp.toNat - 2048 := by rw [← hBd]; exact toNat_sub_ofNat' hsp
    have hB : B.toNat % 16 = 0 := by omega
    have hfr : (⟨B, 2048⟩ : Region) ∈ (allocd 2048 s₀).wr := by rw [← hBd]; exact List.mem_cons_self ..
    generalize hCd : B + BitVec.ofNat 64 1664 = C
    have hC : C.toNat % 16 = 0 := by
      rw [← hCd, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hcon : ∀ k < 36, (⟨B, 2048⟩ : Region).Contains (C + BitVec.ofNat 64 (8 * k)) 8 := fun k hk => by
      rw [← hCd, Offset.add_add]
      exact Offset.contains_base B (by omega) (by omega)
    refine frame_ok (F := 2048) (by decide) hsp (by rw [hwr]; exact List.mem_cons_self ..) ?_
    rw [hBd]
    refine WP.seq (WP.mono (Q := fun t => ∃ s₁, InvL s₁ (ByteLoad.be64 s₀.mem (s₀.gpr .a0) 0)
        (ByteLoad.be64 s₀.mem (s₀.gpr .a0) 8) (blockAt s₀.mem (s₀.gpr .a1)) (s₀.gpr .a2) (s₀.gpr .a3).toNat 0 t ∧
      s₁.gpr .a0 = C ∧ s₁.gpr .a1 = s₀.gpr .a1 ∧ s₁.gpr .ra = s₀.gpr .ra ∧ s₁.sp = B ∧ s₁.rd = s₀.rd ∧
      s₁.wr = (allocd 2048 s₀).wr ∧ Frame [⟨B, 2048⟩] s₀.mem s₁.mem ∧ Spill.Saved B s₀.gpr (savedAt 1952) s₁.mem)
      ?_ ?_)
    · have hst : start = ([.addSp .t0 0] ++ saveAt 1952 : List Instr) ++ (([.addSp .s9 1664] : List Instr) ++ (prep ++
          (([mv .a0 .s9] : List Instr) ++ loadY))) := by simp only [start, List.append_assoc]
      rw [hst, WP.block_append_iff]
      refine WP.mono (saveAt_ok (B := B) (F := 2048) (o := 1952) hB hBd (by decide) (.inr rfl) (by decide) hfr)
        fun s₁ ⟨_, g₁, rd₁, wr₁, sp₁, f₁, sv₁⟩ => ?_
      rw [WP.block_append_iff]
      refine WP.block_cons_iff.mpr ⟨s₁.write .s9 (s₁.sp + BitVec.ofNat 64 1664), rfl, WP.block_nil ?_⟩
      have e0 : s₁.sp + BitVec.ofNat 64 1664 = C := by rw [sp₁]; show s₀.sp - BitVec.ofNat 64 2048 + _ = C; rw [hBd, hCd]
      rw [e0, WP.block_append_iff]
      have a0₁ : s₁.gpr .a0 = s₀.gpr .a0 := g₁ .a0 (by decide)
      refine WP.mono (prep_ok (s₁.write .s9 C) ⟨⟨s₀.gpr .a0, 16⟩, ?_, ?_⟩ fun k hk => ⟨al_frame hC k, ⟨B, 2048⟩, ?_,
        hcon k hk⟩) fun s₂ ⟨tab, ms, g₂, rd₂, wr₂, sp₂, f₂⟩ => ?_
      · show _ ∈ s₁.rd ++ s₁.wr
        rw [rd₁]; show _ ∈ s₀.rd ++ _
        rw [hrd]; exact List.mem_cons_self ..
      · show Region.Contains _ (s₁.gpr .a0) 16
        rw [a0₁]; exact Region.contains_self _ _
      · show _ ∈ s₁.wr
        rw [wr₁]; exact hfr
      rw [WP.block_append_iff]
      refine WP.block_cons_iff.mpr ⟨s₂.write .a0 (s₂.gpr .s9 + BitVec.ofInt 64 0), rfl, WP.block_nil ?_⟩
      have e1 : s₂.gpr .s9 + BitVec.ofInt 64 0 = C := by rw [g₂ .s9 (by decide)]; exact BitVec.add_zero C
      rw [e1]
      have gg : ∀ q, q ∉ prepWrites → q ≠ .s9 → q ≠ .a0 → (s₂.write .a0 C).gpr q = s₀.gpr q := by
        intro q h1 h2 h3
        show (if q = .a0 then C else s₂.gpr q) = _
        rw [ite_eq_right h3, g₂ q h1]
        show (if q = .s9 then C else s₁.gpr q) = _
        rw [ite_eq_right h2]
        exact g₁ q fun e => h1 (by rw [e]; decide)
      have F₂ : Frame [⟨B, 2048⟩] s₀.mem s₂.mem := by
        refine (f₁.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, ?_⟩).trans
          (f₂.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, ?_⟩)
        · rw [List.mem_singleton] at hr; subst hr; exact Offset.sub_base B (by decide)
        · rw [List.mem_singleton] at hr; subst hr; show Region.Sub ⟨C, 288⟩ _; rw [← hCd]; exact Offset.sub_base B (by decide)
      have hwr₂ : s₂.wr = (allocd 2048 s₀).wr := wr₂.trans wr₁
      have hbH : blockAt s₁.mem (s₁.gpr .a0) = blockAt s₀.mem (s₀.gpr .a0) := by
        rw [a0₁]
        refine blockAt_frame f₁ fun r hr => ?_
        rw [List.mem_singleton] at hr; subst hr
        exact hfh.symm.sub_right (Offset.sub_base B (by decide))
      have r₀ : Rel .a0 false (s₂.write .a0 C) (s₂.write .a0 C) ⟨(s₂.write .a0 C).gpr, fun k =>
          s₂.mem.readW (C + BitVec.ofNat 64 (8 * k)) 64⟩ :=
        ⟨rfl, Slots.init _ _ _, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      have hya : (s₂.write .a0 C).gpr .a1 = s₀.gpr .a1 := gg .a1 (by decide) (by decide) (by decide)
      refine WP.mono (loadY_ok r₀ (by decide) (by rw [hya]; show _ ∈ s₂.wr; rw [hwr₂]; show _ ∈ _ :: s₀.wr; rw [hwr]; simp))
        fun t ⟨a, ra, hY, k, hm⟩ => ⟨s₂.write .a0 C, ?_, rfl, hya, gg .ra (by decide) (by decide) (by decide), ?_, ?_, hwr₂, F₂, ?_⟩
      · refine inv_start ra ?_ ?_ ?_ ?_ ?_ (k _ (by decide)) (k _ (by decide))
        · intro j hj
          have hj' : ∀ j < 4, maskReg j ∉ [Reg.t0, .s4, .s5] ∧ maskReg j ≠ .a0 := by decide
          rw [k _ (hj' j hj).1]
          exact (ite_eq_right (hj' j hj).2).trans (ms j hj)
        · intro i hi j hj
          rw [hm]
          refine (tab i hi j hj).trans ?_
          show ghashOperand (blockAt s₁.mem (s₁.gpr .a0)) i &&& _ = _
          rw [hbH, blockAt_hOf]; rfl
        · rw [hY, hya]
          refine blockAt_frame F₂ fun r hr => ?_
          rw [List.mem_singleton] at hr; subst hr; exact hfy.symm
        · rw [k _ (by decide)]; exact gg .a2 (by decide) (by decide) (by decide)
        · rw [k _ (by decide)]
          show (s₂.write .a0 C).gpr .a3 = _
          rw [gg .a3 (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · show s₂.sp = B
        rw [sp₂]; show s₁.sp = B
        rw [sp₁]; exact hBd
      · show s₂.rd = s₀.rd
        rw [rd₂]; exact rd₁
      · intro p hp
        show s₂.mem.readW _ _ = _
        rw [f₂.readW (r := ⟨B + BitVec.ofNat 64 1952, 96⟩) ?_ ?_ (by decide)]
        · refine (sv₁ p hp)
        · have h2 : ∀ p ∈ savedAt 1952, 1952 ≤ p.2 ∧ p.2 + 8 ≤ 1952 + 96 := by decide
          exact Offset.contains B (h2 p hp).1 (h2 p hp).2 (by decide)
        · intro r hr
          rw [List.mem_singleton] at hr; subst hr
          show Region.Disjoint _ ⟨C, 288⟩; rw [← hCd]; exact Offset.disjoint B (by decide) (by decide) (by decide)
    · intro t ⟨s₁, hI, h0, h1, hra, hsp₁, hrd₁, hwr₁, F₁, sv⟩
      have hw : Words .a0 false s₁ := ⟨fun k _ => by rw [h0]; exact al_frame hC k,
        fun k hk => ⟨⟨B, 2048⟩, List.mem_append_right _ (by rw [hwr₁]; exact hfr), by rw [h0]; exact hcon k hk⟩,
        fun h => absurd h (by decide)⟩
      refine WP.mono (rest_ok (F := 2048) (o := 1952) hw hnlt ?_ hB hsp₁ (by decide) (.inr rfl) (by decide) (by rw [hwr₁]; exact hfr)
        sv hI) fun u ⟨g, ra, a1, sp, wr, rd, hb⟩ =>
          ⟨g, ra.trans hra, a1.trans h1, sp, wr.trans hwr₁, rd.trans hrd₁, ?_⟩
      · intro i hi
        refine ⟨⟨s₀.gpr .a2, 16 * (s₀.gpr .a3).toNat⟩, List.mem_append_left _ (by rw [hrd₁, hrd]; simp), ?_⟩
        exact Offset.contains_base _ (by omega) (by omega)
      · rw [hb, blocksAt_frame F₁ hnlt, blockAt_hOf s₀.mem (s₀.gpr .a0), hOf]
        intro r hr
        rw [List.mem_singleton] at hr; subst hr; exact hfd.symm

end VG.Proof.Gcm.RISCV64
