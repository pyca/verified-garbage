module

public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Vmx4
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.Mem

/-! # A chunk of the four-block ChaCha20 on PPC64LE

The input of the four blocks (`setup_ok`), the rounds (each operation acts
on word `j` of its registers as on the state of block `j`, `Holds`; the
column and diagonal rounds in their order are `innerBlock`,
`innerBlock_eq`), the input added again (`feed_ok`), and each row
transposed, XORed with the source and stored (`finish_ok`): `chunk_ok`, the
256 bytes of the destination. -/

@[expose] public section

namespace VG.Proof.ChaCha20.PPC64LE.Vmx4

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE.Vmx4
open VG.Spec.ChaCha20 (stateAt serialize block innerBlock)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-! ## The words of vectors

What the code needs of the vector instructions, word by word (`vword`, most
significant first): the word-wise additions and rotations, a `vperm` whose
control selects whole words, and the order of a row's words after `lxvd2x`
and before `stxvd2x`. -/

theorem vword_pack4 (f : Nat → BitVec 32) {i : Nat} (hi : i < 4) :
    vword ((List.range 4).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (32 * (3 - i)))) 0) i =
      f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.ofNat_eq_ofNat,
    BitVec.getLsbD_zero, Bool.false_or]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals simp (disch := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
    Bool.false_or, Bool.or_false]
  all_goals exact congrArg _ (by omega)


theorem vword_xor (x y : BitVec 128) (i : Nat) : vword (x ^^^ y) i = vword x i ^^^ vword y i := by
  simp only [vword, BitVec.extractLsb'_xor]

/-- Equal words from equal bytes. -/
theorem ext_bytes32 {x y : BitVec 32} (h : ∀ t < 4, x.extractLsb' (8 * t) 8 = y.extractLsb' (8 * t) 8) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have e := congrArg (BitVec.getLsbD · (b % 8)) (h (b / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true, Bool.true_and] at e
  rwa [show 8 * (b / 8) + b % 8 = b by omega] at e

theorem vword_byte (x : BitVec 128) (p t : Nat) (ht : t < 4) :
    (vword x p).extractLsb' (8 * t) 8 = x.extractLsb' (8 * (4 * (3 - p) + t)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * t + b < 32 by omega]
  exact congrArg x.getLsbD (by omega)

theorem swap_byte (y : BitVec 128) {k : Nat} (hk : k < 16) :
    (swapDwords y).extractLsb' (8 * k) 8 = y.extractLsb' (8 * (if k < 8 then k + 8 else k - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [getLsbD_swapDwords _ (by omega)]
  exact congrArg y.getLsbD (by split <;> split <;> omega)

/-- `lxvd2x` puts the words of a row of memory in the order 1, 0, 3, 2. -/
theorem vword_row (m : Mem) (a : Addr) {p : Nat} (hp : p < 4) :
    vword (swapDwords (m.read a 16)) p = m.readW (a + BitVec.ofNat 64 (4 * (p ^^^ 1))) 32 := by
  apply ext_bytes32
  intro t ht
  rw [vword_byte _ _ _ ht, swap_byte _ (by omega), Mem.extractLsb'_read _ _ (by split <;> omega),
    ← Mem.readW_byte _ _ ht, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceXor] <;> omega

/-- Byte `k` of what `stxvd2x` stores of a vector of words `w₁, w₀, w₃, w₂`
(most significant first): byte `k % 4` of word `k / 4`. -/
theorem store_byte (x : BitVec 128) {k : Nat} (hk : k < 16) :
    (swapDwords x).extractLsb' (8 * k) 8 =
      (vword x ((k / 4) ^^^ 1)).extractLsb' (8 * (k % 4)) 8 := by
  rw [swap_byte _ hk, vword_byte _ _ _ (by omega)]
  congr 2
  rcases (by omega : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3) with h | h | h | h <;>
    simp (disch := omega) only [h, ↓ite_eq_left, ↓ite_eq_right, Nat.reduceXor] <;> omega

/-- A word of a vector as its bytes, most significant first. -/
theorem vword_bytes (x : BitVec 128) {p : Nat} (hp : p < 4) :
    vword x p = vbyte x (4 * p) ++ vbyte x (4 * p + 1) ++ vbyte x (4 * p + 2) ++ vbyte x (4 * p + 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true,
    Bool.true_and]
  by_cases h1 : b < 8
  · simp only [h1, ite_true, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h2 : b - 8 < 8
  · simp only [h1, h2, ite_true, ite_false, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  by_cases h3 : b - 8 - 8 < 8
  · simp only [h1, h2, h3, ite_true, ite_false, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [h1, h2, h3, ite_false, show b - 8 - 8 - 8 < 8 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

/-- The result of `vperm` on `n` and `m` with the control `c`. -/
def perm (n m c : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let j := (vbyte c i).toNat % 32
    if j < 16 then vbyte n j else vbyte m (j - 16)

theorem exec_perm (d n m c : VReg) (s : State) :
    exec (.vop (.perm d n m c)) s = some (s.writeV d (perm (s.vpr n) (s.vpr m) (s.vpr c))) := rfl

/-- A `vperm` whose control selects word `q` of the concatenation of its
operands for word `p`. -/
theorem vword_perm (n m c : BitVec 128) {p q : Nat} (hp : p < 4) (hq : q < 8)
    (hc : ∀ t < 4, (vbyte c (4 * p + t)).toNat % 32 = 4 * q + t) :
    vword (perm n m c) p = if q < 4 then vword n q else vword m (q - 4) := by
  rw [vword_bytes _ hp, perm, vbyte_packed _ (by omega), vbyte_packed _ (by omega),
    vbyte_packed _ (by omega), vbyte_packed _ (by omega)]
  have h0 := hc 0 (by decide); have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide); have h3 := hc 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [h0, h1, h2, h3]
  by_cases hq4 : q < 4
  · rw [ite_eq_left hq4, vword_bytes _ hq4]
    simp only [show 4 * q < 16 by omega, show 4 * q + 1 < 16 by omega,
      show 4 * q + 2 < 16 by omega, show 4 * q + 3 < 16 by omega, ite_true]
  · rw [ite_eq_right hq4, vword_bytes _ (by omega)]
    simp only [show ¬ 4 * q < 16 by omega, show ¬ 4 * q + 1 < 16 by omega,
      show ¬ 4 * q + 2 < 16 by omega, show ¬ 4 * q + 3 < 16 by omega, ite_false,
      show 4 * q - 16 = 4 * (q - 4) by omega, show 4 * q + 1 - 16 = 4 * (q - 4) + 1 by omega,
      show 4 * q + 2 - 16 = 4 * (q - 4) + 2 by omega, show 4 * q + 3 - 16 = 4 * (q - 4) + 3 by omega]

/-- The words of four concatenated words. -/
theorem vword_append4 (a b c d : BitVec 32) {j : Nat} (hj : j < 4) :
    vword (a ++ b ++ c ++ d : BitVec 128) j = [a, b, c, d].getD j 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [vword, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and, BitVec.getLsbD_append]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceSub, Nat.reduceMul] <;> exact congrArg _ (by omega)

theorem ext_vword {x y : BitVec 128} (h : ∀ p < 4, vword x p = vword y p) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (BitVec.getLsbD · (i % 32)) (h (3 - i / 32) (by omega))
  simp only [vword, BitVec.getLsbD_extractLsb', show i % 32 < 32 by omega, decide_true,
    Bool.true_and] at e
  rwa [show 32 * (3 - (3 - i / 32)) + i % 32 = i by omega] at e

theorem swapDwords_xor (a b : BitVec 128) : swapDwords (a ^^^ b) = swapDwords a ^^^ swapDwords b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_swapDwords _ hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor, getLsbD_swapDwords _ hi,
    getLsbD_swapDwords _ hi]

/-! ## The rounds -/

theorem vreg_inj (a b : Fin 16) : vreg a = vreg b ↔ a = b :=
  (show ∀ a b : Fin 16, vreg a = vreg b ↔ a = b by decide) a b

theorem vreg_ne16 (a : Fin 16) : vreg a ≠ .v16 := (show ∀ a : Fin 16, vreg a ≠ .v16 by decide) a
theorem vreg_ne17 (a : Fin 16) : vreg a ≠ .v17 := (show ∀ a : Fin 16, vreg a ≠ .v17 by decide) a
theorem vreg_ne18 (a : Fin 16) : vreg a ≠ .v18 := (show ∀ a : Fin 16, vreg a ≠ .v18 by decide) a
theorem vreg_ne19 (a : Fin 16) : vreg a ≠ .v19 := (show ∀ a : Fin 16, vreg a ≠ .v19 by decide) a

/-- Word `j` of `vreg k` is word `k` of block `j`'s state. -/
def Holds (vs : Nat → CState) (s : State) : Prop :=
  ∀ k : Fin 16, ∀ j, j < 4 → vword (s.vpr (vreg k)) j = (vs j)[k]

/-- Only vector registers changed. -/
structure VSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  syms : s'.syms = s.syms

theorem VSame.refl (s : State) : VSame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem VSame.trans {s₀ s₁ s₂ : State} (h : VSame s₀ s₁) (h' : VSame s₁ s₂) : VSame s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.sp.trans h.sp, h'.lr.trans h.lr, h'.syms.trans h.syms⟩

theorem syms_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).syms = s.syms := rfl
theorem syms_write (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).syms = s.syms := rfl

theorem VSame.writeV (s : State) (d : VReg) (x : BitVec 128) : VSame s (s.writeV d x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rotation counts. -/
def rotVec (n : Nat) : BitVec 128 :=
  (BitVec.ofNat 32 n ++ BitVec.ofNat 32 n ++ BitVec.ofNat 32 n ++ BitVec.ofNat 32 n : BitVec 128)

/-- The rotation counts in their registers. -/
def Rot (s : State) : Prop :=
  s.vpr .v16 = rotVec 16 ∧ s.vpr .v17 = rotVec 12 ∧ s.vpr .v18 = rotVec 8 ∧ s.vpr .v19 = rotVec 7

structure RoundSame (s s' : State) : Prop extends VSame s s' where
  rot : ∀ r, r = .v16 ∨ r = .v17 ∨ r = .v18 ∨ r = .v19 → s'.vpr r = s.vpr r

theorem RoundSame.trans {s₀ s₁ s₂ : State} (h : RoundSame s₀ s₁) (h' : RoundSame s₁ s₂) :
    RoundSame s₀ s₂ := ⟨h.toVSame.trans h'.toVSame, fun r hr => (h'.rot r hr).trans (h.rot r hr)⟩

theorem RoundSame.refl (s : State) : RoundSame s s := ⟨VSame.refl s, fun _ _ => rfl⟩

theorem Rot.of_same {s s' : State} (h : Rot s) (h' : RoundSame s s') : Rot s' := by
  obtain ⟨h6, h7, h8, h9⟩ := h
  exact ⟨(h'.rot _ (.inl rfl)).trans h6, (h'.rot _ (.inr (.inl rfl))).trans h7,
    (h'.rot _ (.inr (.inr (.inl rfl)))).trans h8, (h'.rot _ (.inr (.inr (.inr rfl)))).trans h9⟩

def step (v : CState) : Op → CState
  | .add d a b => v.set d (v[a] + v[b])
  | .xorRol d a b n => v.set d ((v[a] ^^^ v[b]).rotateLeft n)

theorem get_set (v : CState) (d k : Fin 16) (x : Word) :
    (v.set d x)[k] = if k = d then x else v[k] := by
  simp only [Vector.getElem_set, Fin.getElem_fin, Fin.ext_iff, eq_comm]

/-- The count of a rotation the rounds use, in its register. -/
theorem rot_count {s : State} (h : Rot s) {n : Nat} (hn : n = 16 ∨ n = 12 ∨ n = 8 ∨ n = 7)
    {j : Nat} (hj : j < 4) : (vword (s.vpr (rotReg n)) j).toNat % 32 = n := by
  obtain ⟨h6, h7, h8, h9⟩ := h
  have hv : ∀ m, m < 32 → (vword (rotVec m) j).toNat % 32 = m := by
    intro m hm
    have e : vword (rotVec m) j = BitVec.ofNat 32 m := by
      rw [rotVec, vword_append4 _ _ _ _ hj]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt hm]
  rcases hn with rfl | rfl | rfl | rfl
  · rw [show rotReg 16 = .v16 from rfl, h6]; exact hv 16 (by decide)
  · rw [show rotReg 12 = .v17 from rfl, h7]; exact hv 12 (by decide)
  · rw [show rotReg 8 = .v18 from rfl, h8]; exact hv 8 (by decide)
  · rw [show rotReg 7 = .v19 from rfl, h9]; exact hv 7 (by decide)

theorem rotReg_cases (n : Nat) : rotReg n = .v16 ∨ rotReg n = .v17 ∨ rotReg n = .v18 ∨ rotReg n = .v19 := by
  unfold rotReg; split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · split
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr rfl))

theorem vreg_ne_rot (a : Fin 16) (n : Nat) : vreg a ≠ rotReg n := by
  rcases rotReg_cases n with h | h | h | h <;> rw [h]
  exacts [vreg_ne16 a, vreg_ne17 a, vreg_ne18 a, vreg_ne19 a]

/-- An operation whose rotation is one of the four counts. -/
def opOk : Op → Bool
  | .add .. => true
  | .xorRol _ _ _ n => decide (n = 16 ∨ n = 12 ∨ n = 8 ∨ n = 7)

theorem rotReg_ne_vreg {r : VReg} (hr : r = .v16 ∨ r = .v17 ∨ r = .v18 ∨ r = .v19) (d : Fin 16) :
    r ≠ vreg d := by
  rcases hr with rfl | rfl | rfl | rfl
  exacts [Ne.symm (vreg_ne16 d), Ne.symm (vreg_ne17 d), Ne.symm (vreg_ne18 d), Ne.symm (vreg_ne19 d)]

theorem op_ok (op : Op) (hop : opOk op = true) {vs : Nat → CState} {s : State} (h : Holds vs s) (hr : Rot s) :
    WP isa (.block op.code) s fun s' => Holds (fun j => step (vs j) op) s' ∧ RoundSame s s' := by
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, reduceExec, reduceVOpEval, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left', Bool.false_eq_true, ite_false]
    refine ⟨fun k j hj => ?_, ⟨VSame.writeV _ _ _, fun r hr' => ?_⟩⟩
    · simp only [vpr_writeV, step, get_set, vreg_inj]
      split
      · rw [vword_pack4 _ hj, h a j hj, h b j hj]
      · exact h k j hj
    · simp only [vpr_writeV, rotReg_ne_vreg hr' d, ite_false]
  | xorRol d a b n =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, reduceExec, reduceVOpEval, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨(VSame.writeV _ _ _).trans (VSame.writeV _ _ _), fun r hr' => ?_⟩⟩
    · simp only [vpr_writeV, step, get_set, vreg_inj, Ne.symm (vreg_ne_rot d n), ite_true, ite_false]
      split
      · rw [vword_pack4 _ hj, vword_xor, h a j hj, h b j hj, rot_count hr (of_decide_eq_true hop) hj]
      · exact h k j hj
    · simp only [vpr_writeV, rotReg_ne_vreg hr' d, ite_false]

theorem ops_ok : ∀ (ops : List Op), ops.all opOk = true → ∀ {vs : Nat → CState} {s : State},
    Holds vs s → Rot s →
    WP isa (.block (ops.flatMap Op.code)) s fun s' =>
      Holds (fun j => ops.foldl step (vs j)) s' ∧ RoundSame s s'
  | [], _, _, _, h, _ => WP.block_nil ⟨h, RoundSame.refl _⟩
  | op :: ops, hok, _, _, h, hr => by
    rw [List.all_cons, Bool.and_eq_true] at hok
    exact WP.block_append ((op_ok op hok.1 h hr).mono fun _ ⟨h', hs⟩ =>
      (ops_ok ops hok.2 h' (hr.of_same hs)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

/-- A term in the words `var k` of a state. -/
inductive E
  | var (k : Nat) | add (a b : E) | xor (a b : E) | rol (a : E) (n : Nat)
  deriving DecidableEq

def E.eval (v : CState) : E → Word
  | .var k => if h : k < 16 then v[k] else 0
  | .add a b => a.eval v + b.eval v
  | .xor a b => a.eval v ^^^ b.eval v
  | .rol a n => (a.eval v).rotateLeft n

/-- A state of terms. -/
abbrev ES := Nat → E

def ES.set (f : ES) (i : Nat) (x : E) : ES := fun k => if k = i then x else f k

/-- The operations on symbolic words. -/
def stepE (f : ES) : Op → ES
  | .add d a b => f.set d (.add (f a) (f b))
  | .xorRol d a b n => f.set d (.rol (.xor (f a) (f b)) n)

/-- `qround` on terms. -/
def qroundE (f : ES) (x y z w : Fin 16) : ES :=
  let a := E.add (f x) (f y); let d := E.rol (.xor (f w) a) 16
  let c := E.add (f z) d; let b := E.rol (.xor (f y) c) 12
  let a := E.add a b; let d := E.rol (.xor d a) 8
  let c := E.add c d; let b := E.rol (.xor b c) 7
  (((f.set x a).set y b).set z c).set w d

/-- The terms `f` evaluate to `v`, in the words of `v₀`. -/
def Rel (v₀ : CState) (f : ES) (v : CState) : Prop := ∀ k (hk : k < 16), (f k).eval v₀ = v[k]

theorem Rel.set {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) {i : Nat} (hi : i < 16) {x : E}
    {y : Word} (hx : x.eval v₀ = y) : Rel v₀ (f.set i x) (v.set i y hi) := by
  intro k hk
  simp only [ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem Rel.step {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (i : Op) :
    Rel v₀ (stepE f i) (step v i) := by
  cases i with
  | add d a b => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])
  | xorRol d a b n => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])

theorem Rel.foldl {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) :
    ∀ is : List Op, Rel v₀ (is.foldl stepE f) (is.foldl Vmx4.step v)
  | [] => h
  | i :: is => (h.step i).foldl is

theorem Rel.qround {v₀ : CState} {f : ES} {v : CState} (h : Rel v₀ f v) (x y z w : Fin 16) :
    Rel v₀ (qroundE f x y z w) (qround v x y z w) := by
  simp only [qroundE]
  refine (((h.set x.2 ?_).set y.2 ?_).set z.2 ?_).set w.2 ?_ <;>
    simp only [E.eval, h _ x.2, h _ y.2, h _ z.2, h _ w.2, Fin.getElem_fin]

/-- The words of a state, as terms. -/
def vars : ES := .var

theorem rel_vars (v : CState) : Rel v vars v := fun k hk => by simp [vars, E.eval, hk]

theorem Rel.eq {v₀ : CState} {f : ES} {v v' : CState} (h : Rel v₀ f v) (h' : Rel v₀ f v') : v = v' :=
  Vector.ext fun k hk => (h k hk).symm.trans (h' k hk)

/-- Two states of terms agree on the words of a state. -/
def ES.eq16 (f g : ES) : Bool := (List.range 16).all fun k => f k == g k

theorem Rel.of_eq16 {v₀ : CState} {f g : ES} {v : CState} (h : Rel v₀ f v) (e : ES.eq16 f g = true) :
    Rel v₀ g v := by
  intro k hk
  simp only [ES.eq16, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e k hk]; exact h k hk

theorem cols_eq (v : CState) :
    (quarters cols).foldl step v =
      qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 := by
  have e : ES.eq16 ((quarters cols).foldl stepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 4 8 12).qround 1 5 9 13 |>.qround 2 6 10 14).qround 3 7 11 15)

theorem diags_eq (v : CState) :
    (quarters diags).foldl step v =
      qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := by
  have e : ES.eq16 ((quarters diags).foldl stepE vars)
      (qroundE (qroundE (qroundE (qroundE vars 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) = true := by
    decide +kernel
  exact (((rel_vars v).foldl _).of_eq16 e).eq
    ((((rel_vars v).qround 0 5 10 15).qround 1 6 11 12 |>.qround 2 7 8 13).qround 3 4 9 14)

theorem innerBlock_eq (v : CState) : (quarters cols ++ quarters diags).foldl step v = innerBlock v := by
  rw [List.foldl_append, cols_eq, diags_eq]; rfl

theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : Holds vs s) (hr : Rot s) :
    WP isa (.block doubleRound) s fun s' =>
      Holds (fun j => innerBlock (vs j)) s' ∧ RoundSame s s' := by
  have e : (fun j => (quarters cols ++ quarters diags).foldl step (vs j)) =
      fun j => innerBlock (vs j) := funext fun j => innerBlock_eq (vs j)
  exact (ops_ok _ (by decide) h hr).mono fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

/-- Only `r8`, `r12` and vector registers changed, and memory only as
stated. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  syms : s'.syms = s.syms

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s₀ s₁ s₂ : State} (h : Keep s₀ s₁) (h' : Keep s₁ s₂) : Keep s₀ s₂ :=
  ⟨fun r h8 h12 => (h'.gpr r h8 h12).trans (h.gpr r h8 h12), h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.sp.trans h.sp, h'.lr.trans h.lr, h'.syms.trans h.syms⟩

theorem VSame.keep {s s' : State} (h : VSame s s') : Keep s s' :=
  ⟨fun r _ _ => congrFun h.gpr r, h.rd, h.wr, h.sp, h.lr, h.syms⟩

theorem Keep.write (s : State) {d : Reg} (h : d = .r8 ∨ d = .r12) (v : BitVec 64) : Keep s (s.write d v) := by
  refine ⟨fun r h8 h12 => RegUpd.gpr_write_of_ne _ _ ?_, rfl, rfl, rfl, rfl, rfl⟩
  rcases h with rfl | rfl <;> with_reducible assumption

theorem roundLoop_ok {vs : Nat → CState} {s : State} (h : Holds vs s) (hr : Rot s) :
    WP isa roundLoop s fun u =>
      Holds (fun j => Nat.repeat innerBlock 10 (vs j)) u ∧ Keep s u ∧ u.mem = s.mem := by
  apply WP.seq
  have h0 : WP isa (.block [.li .r12 10]) s fun a => a = s.write .r12 (BitVec.ofNat 64 10) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec_li (show 10 < 2 ^ 15 by decide), runStep_some,
      Option.some.injEq, exists_eq_left']
  refine h0.mono fun a ha => ?_
  subst ha
  let Inv : Nat → State → Prop := fun n u =>
    0 < n ∧ n ≤ 10 ∧ u.gpr .r12 = BitVec.ofNat 64 n ∧
    Holds (fun j => Nat.repeat innerBlock (10 - n) (vs j)) u ∧ Rot u ∧
    Keep s u ∧ u.mem = s.mem
  refine WP.loop (M := isa) Inv ?_ 10 _ ⟨by decide, by decide, RegUpd.gpr_write_self .., ?_, ?_,
    Keep.write _ (.inr rfl) _, rfl⟩
  · intro n u ⟨hn, hle, hc, hu, hru, hk, hm⟩
    apply WP.block_append
    refine (doubleRound_ok hu hru).mono fun b ⟨hb, hub⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, exec_subi (show Reg.r12 ≠ .r0 by decide)
      (show 1 ≤ 2 ^ 15 by decide), runStep_some, Option.some.injEq, exists_eq_left']
    have hcb : b.gpr .r12 = BitVec.ofNat 64 n := by rw [hub.gpr]; exact hc
    have hcc : (b.write .r12 (b.gpr .r12 - BitVec.ofNat 64 1)).gpr .r12 = BitVec.ofNat 64 (n - 1) := by
      rw [RegUpd.gpr_write_self, hcb]; exact Offset.ofNat_sub_ofNat (by omega)
    have hk' : Keep s (b.write .r12 (b.gpr .r12 - BitVec.ofNat 64 1)) :=
      (hk.trans hub.toVSame.keep).trans (Keep.write _ (.inr rfl) _)
    have hcH : Holds (fun j => Nat.repeat innerBlock (10 - (n - 1)) (vs j))
        (b.write .r12 (b.gpr .r12 - BitVec.ofNat 64 1)) := by
      have he : 10 - (n - 1) = (10 - n) + 1 := by omega
      rw [he]
      simpa only [Holds, vpr_write, Nat.repeat] using hb
    have hrc : Rot (b.write .r12 (b.gpr .r12 - BitVec.ofNat 64 1)) := by
      simpa only [Rot, vpr_write] using hru.of_same hub
    have hmc : (b.write .r12 (b.gpr .r12 - BitVec.ofNat 64 1)).mem = s.mem := by
      rw [RegUpd.mem_write, hub.mem, hm]
    have heval := Xor.eval_nonzero_ofNat _ .r12 (by omega : n - 1 < 2 ^ 64) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hk', hmc⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using heval
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hcH
    · right
      refine ⟨?_, n - 1, by omega, by omega, by omega, hcc, hcH, hrc, hk', hmc⟩
      simpa only [decide_eq_true (by omega : n - 1 ≠ 0)] using heval
  · simpa only [Holds, vpr_write, Nat.sub_self, Nat.repeat] using h
  · simpa only [Rot, vpr_write] using hr


/-! ## The table -/

theorem tblWords_length : tblWords.length = 26 := by decide

theorem tbl_eq : ∀ i < 13, tblWords.getD (2 * i) 0 ++ tblWords.getD (2 * i + 1) 0 = tblVecs.getD i 0 := by
  decide

theorem exec_tbl (s : State) (d : VReg) {i : Nat} (hi : i < 13) (h10 : s.gpr .r10 = s.syms tblName)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 (16 * i)) :
    exec (.lxvd2xTbl d .r10 .r8 tblName tblWords) s = some (s.writeV d (tblVecs.getD i 0)) := by
  have ho : (s.gpr .r8).toNat = 16 * i := by
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [reduceExec, ho, h10, tblWords_length, show 16 * i % 8 = 0 by omega,
    show 16 * i / 8 = 2 * i by omega, show 2 * i + 2 ≤ 26 by omega, ne_eq, reduceCtorEq,
    not_false_eq_true, and_self, ite_true, tbl_eq i hi]

/-- Vector `i` of the table into `d`. -/
theorem ldc_ok (s : State) (d : VReg) {i : Nat} (hi : i < 13) (h10 : s.gpr .r10 = s.syms tblName) :
    WP isa (.block (ldc d i)) s fun u =>
      u = (s.write .r8 (BitVec.ofNat 64 (16 * i))).writeV d (tblVecs.getD i 0) := by
  apply WP.of_runBlock
  simp only [ldc, runBlock_cons, runBlock_nil, exec_li (show 16 * i < 2 ^ 15 by omega),
    runStep_some, exec_tbl _ d hi (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h10)
      (RegUpd.gpr_write_self ..), Option.some.injEq, exists_eq_left']

/-! ## Splatting a word of the state -/

theorem splat_ctl : ∀ p < 4, ∀ j < 4, ∀ t < 4,
    (vbyte (tblVecs.getD p 0) (4 * j + t)).toNat % 32 = 4 * p + t := by decide

theorem pos_lt (k : Fin 16) : pos k < 4 := (show ∀ k : Fin 16, pos k < 4 by decide) k

theorem pos_xor (k : Fin 16) : pos k ^^^ 1 = k.val % 4 := (show ∀ k : Fin 16, pos k ^^^ 1 = k.val % 4 by decide) k

theorem stateAt_get (m : Mem) (p : Addr) (k : Fin 16) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (4 * k.val)) 32 := by
  simp only [stateAt, Fin.getElem_fin, Vector.getElem_ofFn]

/-- The registers other than `r8` and `r12`, with the pointers. -/
theorem splat_ok (s : State) (k : Fin 16) (d : VReg)
    (h10 : s.gpr .r10 = s.syms tblName)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (16 * (k.val / 4))) 16) :
    WP isa (.block (splat k d)) s fun u =>
      (∀ j < 4, vword (u.vpr d) j = (stateAt s.mem (s.gpr .r3))[k]) ∧ Keep s u ∧ u.mem = s.mem ∧
      (∀ r, r ≠ d → r ≠ .v16 → r ≠ .v17 → u.vpr r = s.vpr r) := by
  have hr0 : Reg.r3 ≠ .r0 := by decide
  apply WP.block_append
  apply WP.block_append
  have h1 : WP isa (.block [.li .r8 (16 * (k.val / 4)), .lxvd2x .v16 .r3 .r8]) s fun u =>
      u = (s.write .r8 (BitVec.ofNat 64 (16 * (k.val / 4)))).writeV .v16
        (swapDwords (s.mem.read (s.gpr .r3 + BitVec.ofNat 64 (16 * (k.val / 4))) 16)) := by
    apply WP.of_runBlock
    have hin' : InRegions ((s.write .r8 (BitVec.ofNat 64 (16 * (k.val / 4)))).rd ++
        (s.write .r8 (BitVec.ofNat 64 (16 * (k.val / 4)))).wr)
        ((s.write .r8 (BitVec.ofNat 64 (16 * (k.val / 4)))).gpr .r3 +
          (s.write .r8 (BitVec.ofNat 64 (16 * (k.val / 4)))).gpr .r8) 16 := by
      rw [RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write_self,
        RegUpd.gpr_write_of_ne _ _ (by decide)]
      exact hin
    simp only [runBlock_cons, runBlock_nil, exec_li (show 16 * (k.val / 4) < 2 ^ 15 by omega),
      runStep_some, exec_lxvd2x _ _ _ _ hr0 hin', RegUpd.gpr_write_self,
      RegUpd.gpr_write_of_ne _ _ (show Reg.r3 ≠ .r8 by decide), RegUpd.mem_write,
      Option.some.injEq, exists_eq_left']
  refine h1.mono fun u₁ hu₁ => ?_
  subst hu₁
  refine (ldc_ok _ .v17 (Nat.lt_of_lt_of_le (pos_lt k) (by decide))
    (by rw [gpr_writeV, RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h10)).mono fun u₂ hu₂ => ?_
  subst hu₂
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec_perm, runStep_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun j hj => ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩
  · simp only [vpr_writeV, ite_true, show VReg.v16 ≠ .v17 by decide, ite_false, vpr_write]
    rw [vword_perm _ _ _ hj (Nat.lt_trans (pos_lt k) (by decide)) (splat_ctl _ (pos_lt k) j hj),
      ite_eq_left (pos_lt k), vword_row _ _ (pos_lt k), pos_xor, stateAt_get, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 16 * (k.val / 4) + 4 * (k.val % 4) = 4 * k.val by omega]
  · exact (((((Keep.write _ (.inl rfl) _).trans (VSame.writeV _ _ _).keep).trans
      (Keep.write _ (.inl rfl) _)).trans (VSame.writeV _ _ _).keep).trans (VSame.writeV _ _ _).keep)
  · simp only [mem_writeV, RegUpd.mem_write]
  · simp only [vpr_writeV, h1, h2, h3, ite_false, vpr_write]

/-! ## The input -/

/-- The input of the chunk: the state at `r3`, the table's address in `r10`,
and the rows of the state readable. -/
structure CPre (s₀ : State) : Prop where
  r10 : s₀.gpr .r10 = s₀.syms tblName
  rows : ∀ r < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r3 + BitVec.ofNat 64 (16 * r)) 16

/-- The state at `r3` on entry. -/
abbrev S₀ (s₀ : State) : CState := stateAt s₀.mem (s₀.gpr .r3)

def Loaded (s₀ : State) (ks : List (Fin 16)) (s : State) : Prop :=
  ∀ k ∈ ks, ∀ j < 4, vword (s.vpr (vreg k)) j = (S₀ s₀)[k]

theorem Keep.r3 {s₀ s : State} (h : Keep s₀ s) : s.gpr .r3 = s₀.gpr .r3 := h.gpr _ (by decide) (by decide)
theorem Keep.r10 {s₀ s : State} (h : Keep s₀ s) : s.gpr .r10 = s₀.gpr .r10 := h.gpr _ (by decide) (by decide)

theorem CPre.of_keep {s₀ s : State} (hp : CPre s₀) (h : Keep s₀ s) : CPre s := by
  refine ⟨by rw [h.r10, h.syms, hp.r10], fun r hr => ?_⟩
  rw [h.rd, h.wr, h.r3]; exact hp.rows r hr

theorem splats_ok {s₀ : State} (hp : CPre s₀) : ∀ (ks done : List (Fin 16)) {s : State},
    Keep s₀ s → s.mem = s₀.mem → Loaded s₀ done s →
    WP isa (.block (ks.flatMap fun k => splat k (vreg k))) s fun u =>
      Keep s₀ u ∧ u.mem = s₀.mem ∧ Loaded s₀ (ks ++ done) u
  | [], _, _, hk, hm, hl => WP.block_nil ⟨hk, hm, hl⟩
  | k :: ks, done, s, hk, hm, hl => by
    have hp' := hp.of_keep hk
    rw [List.flatMap_cons]
    apply WP.block_append
    refine (splat_ok s k (vreg k) hp'.r10 (hp'.rows _ (by omega))).mono fun u ⟨hv, hku, hmu, hfr⟩ => ?_
    refine (splats_ok hp ks (k :: done) (hk.trans hku) (hmu.trans hm) ?_).mono fun w ⟨h1, h2, h3⟩ =>
      ⟨h1, h2, fun i hi => h3 i (by simpa only [List.mem_append, List.mem_cons, or_comm, or_left_comm,
        or_assoc] using hi)⟩
    intro i hi j hj
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hv j hj, hk.r3, hm]
    · by_cases e : i = k
      · subst e; rw [hv j hj, hk.r3, hm]
      · rw [hfr _ (fun h => e ((vreg_inj _ _).mp h)) (vreg_ne16 i) (vreg_ne17 i)]
        exact hl i hi j hj

theorem ctr_vec : ∀ j < 4, vword (tblVecs.getD 4 0) j = BitVec.ofNat 32 j := by decide

theorem rot_vecs : tblVecs.getD 5 0 = rotVec 16 ∧ tblVecs.getD 6 0 = rotVec 12 ∧
    tblVecs.getD 7 0 = rotVec 8 ∧ tblVecs.getD 8 0 = rotVec 7 := by decide

theorem ctr_get (S : CState) (j : Nat) (k : Fin 16) :
    (ctr S j)[k] = if k.val = 12 then S[k] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Fin.getElem_fin, Vector.getElem_set]
  by_cases h : k.val = 12
  · simp only [h, ite_true]
  · simp only [h, ite_false, Ne.symm h]

/-- The four blocks' states, and the rotation counts. -/
theorem setup_ok {s₀ : State} (hp : CPre s₀) :
    WP isa (.block setup) s₀ fun u =>
      Holds (fun j => ctr (S₀ s₀) j) u ∧ Rot u ∧ Keep s₀ u ∧ u.mem = s₀.mem := by
  simp only [setup]
  apply WP.block_append; apply WP.block_append; apply WP.block_append
  apply WP.block_append; apply WP.block_append; apply WP.block_append
  refine (splats_ok hp _ [] (Keep.refl _) rfl (fun _ h => absurd h List.not_mem_nil)).mono
    fun a ⟨hka, hma, hla⟩ => ?_
  have hpa := hp.of_keep hka
  refine (ldc_ok a .v16 (by decide) hpa.r10).mono fun b hb => ?_
  subst hb
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, reduceExec, reduceVOpEval, runStep_some, Option.map_some,
    Option.some.injEq, exists_eq_left', Bool.false_eq_true, ite_false]
  refine (ldc_ok _ .v16 (by decide) ?_).mono fun c hc => ?_
  · simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ (show Reg.r10 ≠ .r8 by decide), hpa.r10]; rfl
  subst hc
  refine (ldc_ok _ .v17 (by decide) ?_).mono fun c hc => ?_
  · simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ (show Reg.r10 ≠ .r8 by decide), hpa.r10]; rfl
  subst hc
  refine (ldc_ok _ .v18 (by decide) ?_).mono fun c hc => ?_
  · simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ (show Reg.r10 ≠ .r8 by decide), hpa.r10]; rfl
  subst hc
  refine (ldc_ok _ .v19 (by decide) ?_).mono fun c hc => ?_
  · simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ (show Reg.r10 ≠ .r8 by decide), hpa.r10]; rfl
  subst hc
  obtain ⟨r5, r6, r7, r8⟩ := rot_vecs
  refine ⟨fun k j hj => ?_, ?_, ?_, ?_⟩
  · simp only [vpr_writeV, vpr_write, vreg_ne16, vreg_ne17, vreg_ne18, vreg_ne19, ite_false, vreg_inj]
    rw [ctr_get]
    by_cases hk : k = 12
    · subst hk
      simp only [ite_true, vword_pack4 _ hj, hla 12 (by simp) j hj, ctr_vec j hj]
      rfl
    · rw [ite_eq_right hk, ite_eq_right (fun h : k.val = 12 => hk (Fin.ext h))]
      exact hla k (by simp) j hj
  · simp only [Rot, vpr_writeV, vpr_write, reduceCtorEq, ite_true, ite_false, r5, r6, r7, r8]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · exact (((((((((hka.trans (Keep.write _ (.inl rfl) _)).trans (VSame.writeV _ _ _).keep).trans
      (VSame.writeV _ _ _).keep).trans (Keep.write _ (.inl rfl) _)).trans (VSame.writeV _ _ _).keep).trans
      (Keep.write _ (.inl rfl) _)).trans (VSame.writeV _ _ _).keep).trans
      ((Keep.write _ (.inl rfl) _).trans (VSame.writeV _ _ _).keep)).trans
      ((Keep.write _ (.inl rfl) _).trans (VSame.writeV _ _ _).keep))
  · simp only [mem_writeV, RegUpd.mem_write, hma]

/-! ## Adding the input -/

def Fed (s₀ : State) (vs : Nat → CState) (done : List (Fin 16)) (s : State) : Prop :=
  ∀ k : Fin 16, ∀ j < 4, vword (s.vpr (vreg k)) j =
    if k ∈ done then (vs j)[k] + (ctr (S₀ s₀) j)[k] else (vs j)[k]

theorem feedWord_ok {s₀ : State} (hp : CPre s₀) {vs : Nat → CState} {done : List (Fin 16)}
    (k : Fin 16) (hk : k ∉ done) {s : State} (hks : Keep s₀ s) (hm : s.mem = s₀.mem)
    (h : Fed s₀ vs done s) :
    WP isa (.block (feedWord k)) s fun u => Keep s₀ u ∧ u.mem = s₀.mem ∧ Fed s₀ vs (k :: done) u := by
  have hp' := hp.of_keep hks
  have hS : stateAt s.mem (s.gpr .r3) = S₀ s₀ := by rw [hm, hks.r3]
  simp only [feedWord]
  apply WP.block_append; apply WP.block_append
  refine (splat_ok s k .v18 hp'.r10 (hp'.rows _ (by omega))).mono fun a ⟨hva, hka, hma, hfa⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, reduceExec, reduceVOpEval, runStep_some, Option.map_some,
    Option.some.injEq, exists_eq_left', Bool.false_eq_true, ite_false]
  have hk' : ∀ x, Keep s₀ (a.writeV (vreg k) x) := fun x => (hks.trans hka).trans (VSame.writeV _ _ x).keep
  have hfed' : ∀ i : Fin 16, ∀ j < 4, vword (a.vpr (vreg i)) j =
      if i ∈ done then (vs j)[i] + (ctr (S₀ s₀) j)[i] else (vs j)[i] := by
    intro i j hj
    rw [hfa _ (vreg_ne18 i) (vreg_ne16 i) (vreg_ne17 i)]
    exact h i j hj
  have hfed : ∀ i : Fin 16, i ≠ k → ∀ j < 4, vword (a.vpr (vreg i)) j =
      if i ∈ done then (vs j)[i] + (ctr (S₀ s₀) j)[i] else (vs j)[i] := fun i _ => hfed' i
  have hkk : ∀ j < 4, vword (a.vpr (vreg k)) j = (vs j)[k] := by
    intro j hj
    rw [hfed' k j hj, ite_eq_right hk]
  by_cases h12 : k = 12
  · subst h12
    simp only [ite_true]
    apply WP.block_append
    refine (ldc_ok _ .v17 (i := 4) (by decide) ?_).mono fun c hc => ?_
    · exact (hp.of_keep (hk' _)).r10
    subst hc
    apply WP.of_runBlock
    simp only [runBlock_cons, runBlock_nil, reduceExec, reduceVOpEval, runStep_some, Option.map_some,
      Option.some.injEq, exists_eq_left', Bool.false_eq_true, ite_false]
    refine ⟨((hk' _ |>.trans (Keep.write _ (.inl rfl) _)).trans (VSame.writeV _ _ _).keep).trans
      (VSame.writeV _ _ _).keep, by simp only [mem_writeV, RegUpd.mem_write, hma, hm], ?_⟩
    intro i j hj
    simp only [vpr_writeV, vpr_write, vreg_ne17, ite_false, vreg_inj, List.mem_cons]
    by_cases hi : i = 12
    · subst hi
      simp only [ite_true, true_or, vword_pack4 _ hj,
        hkk j hj, hva j hj, hS, ctr_vec j hj, ctr_get, BitVec.add_assoc]
      rfl
    · simp only [hi, ite_false, false_or]
      exact hfed i hi j hj
  · simp only [h12, ite_false]
    apply WP.block_nil
    refine ⟨hk' _, by simp only [mem_writeV, hma, hm], ?_⟩
    intro i j hj
    simp only [vpr_writeV, vreg_inj, List.mem_cons]
    by_cases hi : i = k
    · subst hi
      simp only [ite_true, true_or, vword_pack4 _ hj, hkk j hj, hva j hj, hS, ctr_get,
        show ¬ i.val = 12 from fun e => h12 (Fin.ext e), ite_false]
    · simp only [hi, ite_false, false_or]
      exact hfed i hi j hj

theorem feeds_ok {s₀ : State} (hp : CPre s₀) {vs : Nat → CState} : ∀ (ks done : List (Fin 16)),
    ks.Nodup → (∀ k ∈ ks, k ∉ done) → ∀ {s : State}, Keep s₀ s → s.mem = s₀.mem → Fed s₀ vs done s →
    WP isa (.block (ks.flatMap feedWord)) s fun u => Keep s₀ u ∧ u.mem = s₀.mem ∧ Fed s₀ vs (ks ++ done) u
  | [], _, _, _, _, hk, hm, h => WP.block_nil ⟨hk, hm, h⟩
  | k :: ks, done, hn, hf, s, hk, hm, h => by
    rw [List.flatMap_cons]
    apply WP.block_append
    refine (feedWord_ok hp k (hf k (List.mem_cons_self ..)) hk hm h).mono fun u ⟨hku, hmu, hu⟩ => ?_
    have hn' := List.nodup_cons.mp hn
    refine (feeds_ok hp ks (k :: done) hn'.2 (fun i hi => ?_) hku hmu hu).mono
      fun w ⟨h1, h2, h3⟩ => ⟨h1, h2, fun i j hj => ?_⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨fun e => hn'.1 (e ▸ hi), hf i (List.mem_cons_of_mem _ hi)⟩
    · rw [h3 i j hj]
      simp only [List.mem_append, List.mem_cons, List.cons_append, or_left_comm]

/-- The blocks of the four states: the rounds' result plus the input. -/
theorem feed_ok {s₀ : State} (hp : CPre s₀) {s : State} (hk : Keep s₀ s) (hm : s.mem = s₀.mem)
    (h : Holds (fun j => Nat.repeat innerBlock 10 (ctr (S₀ s₀) j)) s) :
    WP isa (.block feed) s fun u =>
      Holds (fun j => block (ctr (S₀ s₀) j)) u ∧ Keep s₀ u ∧ u.mem = s₀.mem := by
  refine (feeds_ok hp (vs := fun j => Nat.repeat innerBlock 10 (ctr (S₀ s₀) j)) (List.finRange 16) [] (List.nodup_finRange 16) (fun _ _ h => absurd h List.not_mem_nil)
    hk hm (fun k j hj => by rw [h k j hj]; rfl)).mono fun u ⟨hku, hmu, hu⟩ => ⟨fun k j hj => ?_, hku, hmu⟩
  rw [hu k j hj, ite_eq_left (by simp)]
  simp only [block, Fin.getElem_fin, Vector.getElem_zipWith]

/-! ## Transposing a row -/

/-- Word `p` of the `vperm` with control `c` (9 to 12) of the table: this
word of the concatenation of its operands. -/
def qmap (c p : Nat) : Nat :=
  ([[4, 0, 5, 1], [6, 2, 7, 3], [0, 1, 4, 5], [2, 3, 6, 7]].getD (c - 9) []).getD p 0

theorem ctl_words : ∀ c < 4, ∀ p < 4, qmap (c + 9) p < 8 ∧ ∀ t < 4,
    (vbyte (tblVecs.getD (c + 9) 0) (4 * p + t)).toNat % 32 = 4 * qmap (c + 9) p + t := by decide

/-- Word `q` of the concatenation of `n` and `m`. -/
def sel (n m : BitVec 128) (q : Nat) : BitVec 32 := if q < 4 then vword n q else vword m (q - 4)

theorem vword_ctl (n m : BitVec 128) {c p : Nat} (hc : c < 4) (hp : p < 4) :
    vword (perm n m (tblVecs.getD (c + 9) 0)) p = sel n m (qmap (c + 9) p) :=
  vword_perm n m _ hp (ctl_words c hc p hp).1 (ctl_words c hc p hp).2

theorem rowReg_inj : ∀ r i i' : Fin 4, rowReg r i = rowReg r i' ↔ i = i' := by decide
theorem rowReg_ne : ∀ r i : Fin 4, rowReg r i ≠ .v16 ∧ rowReg r i ≠ .v17 ∧ rowReg r i ≠ .v18 ∧
    rowReg r i ≠ .v19 := by decide

theorem qmap_vals :
    qmap 9 0 = 4 ∧
    qmap 9 1 = 0 ∧
    qmap 9 2 = 5 ∧
    qmap 9 3 = 1 ∧
    qmap 10 0 = 6 ∧
    qmap 10 1 = 2 ∧
    qmap 10 2 = 7 ∧
    qmap 10 3 = 3 ∧
    qmap 11 0 = 0 ∧
    qmap 11 1 = 1 ∧
    qmap 11 2 = 4 ∧
    qmap 11 3 = 5 ∧
    qmap 12 0 = 2 ∧
    qmap 12 1 = 3 ∧
    qmap 12 2 = 6 ∧
    qmap 12 3 = 7 := by decide

theorem vword_P (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (perm n m (tblVecs.getD 9 0)) p = sel n m (qmap 9 p) := vword_ctl n m (c := 0) (by decide) hp
theorem vword_Q (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (perm n m (tblVecs.getD 10 0)) p = sel n m (qmap 10 p) := vword_ctl n m (c := 1) (by decide) hp
theorem vword_U (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (perm n m (tblVecs.getD 11 0)) p = sel n m (qmap 11 p) := vword_ctl n m (c := 2) (by decide) hp
theorem vword_V (n m : BitVec 128) {p : Nat} (hp : p < 4) :
    vword (perm n m (tblVecs.getD 12 0)) p = sel n m (qmap 12 p) := vword_ctl n m (c := 3) (by decide) hp

/-- The words of block `j`'s row: `b, a, d, c` of block `j` of `A`, `B`, `C`, `D`. -/
theorem transpose4_words (A B C D : BitVec 128) {j p : Nat} (hj : j < 4) (hp : p < 4) :
    vword ([perm (perm A B (tblVecs.getD 9 0)) (perm C D (tblVecs.getD 9 0)) (tblVecs.getD 11 0),
      perm (perm A B (tblVecs.getD 9 0)) (perm C D (tblVecs.getD 9 0)) (tblVecs.getD 12 0),
      perm (perm A B (tblVecs.getD 10 0)) (perm C D (tblVecs.getD 10 0)) (tblVecs.getD 11 0),
      perm (perm A B (tblVecs.getD 10 0)) (perm C D (tblVecs.getD 10 0)) (tblVecs.getD 12 0)].getD j 0) p =
      vword ([A, B, C, D].getD (p ^^^ 1) 0) j := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ := qmap_vals
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3) with rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [List.getD_cons_zero, List.getD_cons_succ, vword_P, vword_Q, vword_U, vword_V,
    sel, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, Nat.reduceXor,
    Nat.reduceLT, Nat.reduceSub, ↓reduceIte] <;> rfl

theorem perms_ok (s : State) (d₁ n₁ m₁ d₂ n₂ m₂ : VReg) :
    WP isa (.block [.vop (.perm d₁ n₁ m₁ .v19), .vop (.perm d₂ n₂ m₂ .v19)]) s fun u =>
      u = (s.writeV d₁ (perm (s.vpr n₁) (s.vpr m₁) (s.vpr .v19))).writeV d₂
        (perm ((s.writeV d₁ (perm (s.vpr n₁) (s.vpr m₁) (s.vpr .v19))).vpr n₂)
          ((s.writeV d₁ (perm (s.vpr n₁) (s.vpr m₁) (s.vpr .v19))).vpr m₂)
          ((s.writeV d₁ (perm (s.vpr n₁) (s.vpr m₁) (s.vpr .v19))).vpr .v19)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec_perm, runStep_some, Option.some.injEq, exists_eq_left']

theorem transpose4_ok (s : State) (a b c d : VReg) (h10 : s.gpr .r10 = s.syms tblName)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hr : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d → x ≠ .v16 ∧ x ≠ .v17 ∧ x ≠ .v18 ∧ x ≠ .v19) :
    WP isa (.block (transpose4 a b c d)) s fun u =>
      let P := tblVecs.getD 9 0; let Q := tblVecs.getD 10 0
      let U := tblVecs.getD 11 0; let V := tblVecs.getD 12 0
      let A := s.vpr a; let B := s.vpr b; let C := s.vpr c; let D := s.vpr d
      u.vpr b = perm (perm A B P) (perm C D P) U ∧ u.vpr d = perm (perm A B P) (perm C D P) V ∧
      u.vpr c = perm (perm A B Q) (perm C D Q) U ∧ u.vpr .v16 = perm (perm A B Q) (perm C D Q) V ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ .v16 → r ≠ .v17 → r ≠ .v18 → r ≠ .v19 →
        u.vpr r = s.vpr r) ∧ Keep s u ∧ u.mem = s.mem := by
  obtain ⟨ha6, ha7, ha8, ha9⟩ := hr a (.inl rfl)
  obtain ⟨hb6, hb7, hb8, hb9⟩ := hr b (.inr (.inl rfl))
  obtain ⟨hc6, hc7, hc8, hc9⟩ := hr c (.inr (.inr (.inl rfl)))
  obtain ⟨hd6, hd7, hd8, hd9⟩ := hr d (.inr (.inr (.inr rfl)))
  have k10 : ∀ u : State, Keep s u → u.gpr .r10 = u.syms tblName := fun u hu => by
    rw [hu.r10, hu.syms, h10]
  simp only [transpose4]
  apply WP.block_append; apply WP.block_append; apply WP.block_append; apply WP.block_append
  apply WP.block_append; apply WP.block_append; apply WP.block_append
  refine (ldc_ok s .v19 (i := 9) (by decide) h10).mono fun u₁ hu₁ => ?_
  subst hu₁
  refine (perms_ok _ _ _ _ _ _ _).mono fun u₂ hu₂ => ?_
  subst hu₂
  refine (ldc_ok _ .v19 (i := 10) (by decide) (k10 _ ?_)).mono fun u₃ hu₃ => ?_
  · exact ⟨fun r h8 _ => by simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ h8],
      by simp only [rd_writeV, RegUpd.rd_write], by simp only [wr_writeV, RegUpd.wr_write],
      by simp only [sp_writeV, RegUpd.sp_write], by simp only [lr_writeV, RegUpd.lr_write],
      by simp only [syms_writeV, syms_write]⟩
  subst hu₃
  refine (perms_ok _ _ _ _ _ _ _).mono fun u₄ hu₄ => ?_
  subst hu₄
  refine (ldc_ok _ .v19 (i := 11) (by decide) (k10 _ ?_)).mono fun u₅ hu₅ => ?_
  · exact ⟨fun r h8 _ => by simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ h8],
      by simp only [rd_writeV, RegUpd.rd_write], by simp only [wr_writeV, RegUpd.wr_write],
      by simp only [sp_writeV, RegUpd.sp_write], by simp only [lr_writeV, RegUpd.lr_write],
      by simp only [syms_writeV, syms_write]⟩
  subst hu₅
  refine (perms_ok _ _ _ _ _ _ _).mono fun u₆ hu₆ => ?_
  subst hu₆
  refine (ldc_ok _ .v19 (i := 12) (by decide) (k10 _ ?_)).mono fun u₇ hu₇ => ?_
  · exact ⟨fun r h8 _ => by simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ h8],
      by simp only [rd_writeV, RegUpd.rd_write], by simp only [wr_writeV, RegUpd.wr_write],
      by simp only [sp_writeV, RegUpd.sp_write], by simp only [lr_writeV, RegUpd.lr_write],
      by simp only [syms_writeV, syms_write]⟩
  subst hu₇
  refine (perms_ok _ _ _ _ _ _ _).mono fun u₈ hu₈ => ?_
  subst hu₈
  simp only [vpr_writeV, vpr_write, ite_true, ite_false, reduceCtorEq, hab, hac, had, ha6, ha7, ha8, ha9,
    hbc, hbd, hb6, hb7, hb8, hb9, hcd, hc6, hc7, hc8, hc9, hd6, hd7, hd8, hd9,
    Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm ha6, Ne.symm ha7, Ne.symm ha8, Ne.symm ha9,
    Ne.symm hbc, Ne.symm hbd, Ne.symm hb6, Ne.symm hb7, Ne.symm hb8, Ne.symm hb9, Ne.symm hcd,
    Ne.symm hc6, Ne.symm hc7, Ne.symm hc8, Ne.symm hc9, Ne.symm hd6, Ne.symm hd8,
    Ne.symm hd9]
  refine ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, ⟨fun r h8 _ => by simp only [gpr_writeV, RegUpd.gpr_write_of_ne _ _ h8],
    by simp only [rd_writeV, RegUpd.rd_write], by simp only [wr_writeV, RegUpd.wr_write],
    by simp only [sp_writeV, RegUpd.sp_write], by simp only [lr_writeV, RegUpd.lr_write],
    by simp only [syms_writeV, syms_write]⟩,
    by simp only [mem_writeV, RegUpd.mem_write]⟩
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false]

/-! ## The stores -/

theorem exec_vxor (d n m : VReg) (s : State) :
    exec (.vop (.logic .xor d n m)) s = some (s.writeV d (s.vpr n ^^^ s.vpr m)) := rfl

/-- Row `r` of block `j` of the source XORed with the keystream into the
destination. -/
theorem xorRow_ok (s : State) (r j : Fin 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hy : outReg r j ≠ .v19) :
    WP isa (.block (xorRow r j)) s fun u =>
      u.mem = s.mem.write (s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r)) 16
        (s.mem.read (s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 ^^^
          swapDwords (s.vpr (outReg r j))) ∧
      Keep s u ∧ (∀ v, v ≠ .v19 → u.vpr v = s.vpr v) := by
  have ho : 64 * j.val + 16 * r.val < 2 ^ 15 := by omega
  let s₁ := s.write .r8 (BitVec.ofNat 64 (64 * j + 16 * r))
  have h4 : s₁.gpr .r4 + s₁.gpr .r8 = s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r) := by
    simp only [s₁, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ .r8 by decide)]
  have hin' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r4 + s₁.gpr .r8) 16 := by rw [h4]; exact hin
  let s₂ := s₁.writeV .v19 (swapDwords (s₁.mem.read (s₁.gpr .r4 + s₁.gpr .r8) 16))
  let s₃ := s₂.writeV .v19 (s₂.vpr .v19 ^^^ s₂.vpr (outReg r j))
  have h7 : s₃.gpr .r7 + s₃.gpr .r8 = s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r) := by
    simp only [s₃, s₂, s₁, gpr_writeV, RegUpd.gpr_write_self,
      RegUpd.gpr_write_of_ne _ _ (show Reg.r7 ≠ .r8 by decide)]
  have hout' : InRegions s₃.wr (s₃.gpr .r7 + s₃.gpr .r8) 16 := by rw [h7]; exact hout
  apply WP.of_runBlock
  simp only [xorRow, runBlock_cons, exec_li ho, runStep_some]
  rw [exec_lxvd2x _ _ _ _ (by decide) hin']
  simp only [runStep_some, runBlock_cons]
  rw [exec_vxor]
  simp only [runStep_some, runBlock_cons]
  rw [exec_stxvd2x _ _ _ _ (by decide) hout']
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' h8 _ => ?_, rfl, rfl, rfl, rfl, rfl⟩, fun v hv => ?_⟩
  · simp only [s₃, s₂, s₁, vpr_writeV, ite_true, hy, ite_false, vpr_write, RegUpd.mem_write,
      mem_writeV, gpr_writeV, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (show Reg.r7 ≠ .r8 by decide),
      RegUpd.gpr_write_of_ne _ _ (show Reg.r4 ≠ .r8 by decide),
      swapDwords_xor, swapDwords_involutive]
  · simp only [s₃, s₂, s₁, gpr_writeV, RegUpd.gpr_write_of_ne _ _ h8]
  · simp only [s₃, s₂, s₁, vpr_writeV, hv, ite_false, vpr_write]

/-- A 16-byte store of `w ^^^ v` at `p`, a byte at a time. -/
theorem xor_write_apply' (m : Mem) (p : Addr) (w v : BitVec 128) (x : Addr) :
    (m.write p 16 (w ^^^ v)) x =
      if (x - p).toNat < 16 then
        w.extractLsb' (8 * (x - p).toNat) 8 ^^^ v.extractLsb' (8 * (x - p).toNat) 8
      else m x := by
  by_cases h : (x - p).toNat < 16
  · simp only [Mem.write, h, ite_true, BitVec.extractLsb'_xor]
  · rw [ite_eq_right h]; exact Mem.write_apply h

/-- `Data` from a source: distinct, aligned 16-byte stores to the first `N`
bytes at `p` of the bytes of `m₀` at `q` XORed with `out`, tracked by their
slot. -/
def DataTo (m₀ m : Mem) (q p : Addr) (N : Nat) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < N
    then m₀ (q + (x - p)) ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem DataTo.nil (m : Mem) (q p : Addr) (N : Nat) (out : Nat → BitVec 128) :
    DataTo m m q p N out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem DataTo.frame {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) : Frame [⟨p, N⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < N := by
    have hh := hx ⟨p, N⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x, ite_eq_right (fun h => hn h.2)]

/-- Slot `n` of the source is as in `m₀`, if it is not written yet: in
place, or apart from the destination. -/
theorem DataTo.src {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) (halias : q = p ∨ (⟨q, N⟩ : Region).Disjoint ⟨p, N⟩)
    {n : Nat} (hn : 16 * n + 16 ≤ N) (hN : N ≤ 2 ^ 64) (hfresh : n ∉ done) :
    m.read (q + BitVec.ofNat 64 (16 * n)) 16 = m₀.read (q + BitVec.ofNat 64 (16 * n)) 16 := by
  refine Mem.read_congr fun i hi => ?_
  rw [Offset.add_add, h]
  refine ite_eq_right fun ⟨hs, hlt⟩ => ?_
  rcases halias with rfl | hd
  · rw [Mem.sub_ofNat_toNat _ (by omega)] at hs
    exact hfresh (by rwa [show (16 * n + i) / 16 = n by omega] at hs)
  · have hx : (⟨q, N⟩ : Region).Contains (q + BitVec.ofNat 64 (16 * n + i)) 1 := by
      show (q + BitVec.ofNat 64 (16 * n + i) - q).toNat + 1 ≤ N
      rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
    exact hd _ hx (show (q + BitVec.ofNat 64 (16 * n + i) - p).toNat + 1 ≤ N by omega)

theorem DataTo.store {m₀ m : Mem} {q p : Addr} {N : Nat} {out : Nat → BitVec 128} {done : List Nat}
    (h : DataTo m₀ m q p N out done) {n : Nat} (hn : 16 * n + 16 ≤ N) (hN : N ≤ 2 ^ 64)
    (hsrc : m.read (q + BitVec.ofNat 64 (16 * n)) 16 = m₀.read (q + BitVec.ofNat 64 (16 * n)) 16) :
    DataTo m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (q + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) q p N out (n :: done) := by
  intro x
  rw [xor_write_apply']
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < N
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hq : q + BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 ((x - p).toNat % 16) = q + (x - p) := by
      rw [Offset.add_add, show 16 * n + (x - p).toNat % 16 = (x - p).toNat by omega,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [hd, and_self, ite_true, he, hb, List.mem_cons_self, hs, hsrc,
      Mem.extractLsb'_read _ _ (Nat.mod_lt _ (by decide) : (x - p).toNat % 16 < 16), hq]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd, h x]
    by_cases hb : (x - p).toNat < N
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]


/-! ## The rows -/

/-- The 16-byte slot of row `r` of block `j`. -/
def slot (r j : Fin 4) : Nat := 4 * j.val + r.val

theorem slot_lt (r j : Fin 4) : slot r j < 16 := by unfold slot; omega

theorem slot_inj (r i j : Fin 4) : slot r i = slot r j ↔ i = j := by
  simp only [slot, Fin.ext_iff]; omega

theorem slot_ne {r t : Fin 4} (hne : r ≠ t) (i j : Fin 4) : slot r i ≠ slot t j := by
  intro e; apply hne; apply Fin.ext; unfold slot at e; omega

/-- The keystream of slot `n` (row `n % 4` of block `n / 4`), as a store
writes it. -/
def output (vs : Nat → CState) (n : Nat) : BitVec 128 :=
  swapDwords ((vs (n / 4))[4 * (n % 4) + 1]'(by omega) ++ (vs (n / 4))[4 * (n % 4)]'(by omega) ++
    (vs (n / 4))[4 * (n % 4) + 3]'(by omega) ++ (vs (n / 4))[4 * (n % 4) + 2]'(by omega) : BitVec 128)

theorem xor_one_lt {x : Nat} (h : x < 4) : x ^^^ 1 < 4 := by
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) with rfl | rfl | rfl | rfl <;> decide

theorem output_byte (vs : Nat → CState) (k : Nat) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 = (serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [output, store_byte _ (by omega), vword_append4 _ _ _ _ (xor_one_lt (by omega)),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  have e1 : k / 16 / 4 = k / 64 := by omega
  have e2 : k % 16 % 4 = k % 64 % 4 := by omega
  rw [e2]
  congr 1
  simp only [e1]
  rcases (by omega : k % 16 / 4 = 0 ∨ k % 16 / 4 = 1 ∨ k % 16 / 4 = 2 ∨ k % 16 / 4 = 3) with h | h | h | h <;>
    simp only [h, Nat.reduceXor, List.getD_cons_zero, List.getD_cons_succ] <;>
    exact getElem_congr_idx (by omega)

theorem outReg_ne (r j : Fin 4) : outReg r j ≠ .v19 :=
  (show ∀ r j : Fin 4, outReg r j ≠ .v19 by decide) r j

/-- The rows of blocks `js` of row `r` XORed and stored. -/
theorem xorRows_ok (r : Fin 4) (js : List (Fin 4)) (hn : js.Nodup)
    {m₀ : Mem} {q p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : DataTo m₀ s.mem q p 256 out done) (hq : s.gpr .r4 = q) (hp : s.gpr .r7 = p)
    (halias : q = p ∨ (⟨q, 256⟩ : Region).Disjoint ⟨p, 256⟩)
    (hv : ∀ j : Fin 4, swapDwords (s.vpr (outReg r j)) = out (slot r j))
    (hfresh : ∀ j ∈ js, slot r j ∉ done)
    (hin : ∀ j : Fin 4, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (js.flatMap (xorRow r))) s fun s' =>
      DataTo m₀ s'.mem q p 256 out (js.map (slot r) ++ done) ∧ Keep s s' ∧
      (∀ v, v ≠ .v19 → s'.vpr v = s.vpr v) := by
  induction js generalizing s done with
  | nil => exact WP.block_nil ⟨hd, Keep.refl _, fun _ _ => rfl⟩
  | cons j js ih =>
    have he : 64 * j.val + 16 * r.val = 16 * slot r j := by unfold slot; omega
    apply WP.block_append
    refine (xorRow_ok s r j (by rw [hq]; exact hin j) (by rw [hp]; exact hout j) (outReg_ne r j)).mono
      fun s' ⟨hm, hk, hvk⟩ => ?_
    have hd' : DataTo m₀ s'.mem q p 256 out (slot r j :: done) := by
      rw [hm, hp, hq, hv j, he]
      exact hd.store (by have := slot_lt r j; omega) (by decide)
        (hd.src halias (by have := slot_lt r j; omega) (by decide) (hfresh j (List.mem_cons_self ..)))
    have hfresh' : ∀ i ∈ js, slot r i ∉ slot r j :: done := by
      intro i hi
      simp only [List.mem_cons, slot_inj, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 (e ▸ hi), hfresh i (List.mem_cons_of_mem _ hi)⟩
    refine (ih (List.nodup_cons.mp hn).2 hd' (by rw [hk.gpr _ (by decide) (by decide), hq])
      (by rw [hk.gpr _ (by decide) (by decide), hp])
      (fun i => by rw [hvk _ (outReg_ne r i), hv i]) hfresh'
      (fun i => by rw [hk.rd, hk.wr]; exact hin i) (fun i => by rw [hk.wr]; exact hout i)).mono
      fun s'' ⟨hd'', ht, hvt⟩ => ⟨?_, hk.trans ht, fun v hv' => (hvt v hv').trans (hvk v hv')⟩
    intro x
    simpa only [DataTo, List.map_cons, List.mem_append, List.mem_cons, or_assoc,
      or_left_comm] using hd'' x

theorem rowReg_vreg (r i : Fin 4) : rowReg r i = vreg ⟨4 * r.val + i.val, by omega⟩ := rfl

theorem outReg_cases (r j : Fin 4) : outReg r j =
    [rowReg r 1, rowReg r 3, rowReg r 2, .v16].getD j.val .v0 := by
  unfold outReg
  rcases j with ⟨_ | _ | _ | _ | j, hj⟩
  all_goals first | rfl | omega

/-- Row `r` of the four blocks transposed and XORed with the source (at
`r4`, `q`) into the destination (at `r7`, `p`). -/
theorem finishRow_ok (r : Fin 4) {s : State} {m₀ : Mem} {q p : Addr} {vs : Nat → CState}
    {done : List Nat} (h10 : s.gpr .r10 = s.syms tblName)
    (hd : DataTo m₀ s.mem q p 256 (output vs) done) (hq : s.gpr .r4 = q) (hp : s.gpr .r7 = p)
    (halias : q = p ∨ (⟨q, 256⟩ : Region).Disjoint ⟨p, 256⟩)
    (hv : ∀ i : Fin 4, ∀ j < 4, vword (s.vpr (rowReg r i)) j = (vs j)[4 * r.val + i.val]'(by omega))
    (hfresh : ∀ j : Fin 4, slot r j ∉ done)
    (hin : ∀ j : Fin 4, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRow r)) s fun u =>
      DataTo m₀ u.mem q p 256 (output vs) ((List.finRange 4).map (slot r) ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → u.vpr (vreg k) = s.vpr (vreg k)) ∧ Keep s u := by
  have hri : ∀ i i' : Fin 4, i ≠ i' → rowReg r i ≠ rowReg r i' := fun i i' h e => h ((rowReg_inj r i i').mp e)
  apply WP.block_append
  refine (transpose4_ok s _ _ _ _ h10 (hri 0 1 (by decide)) (hri 0 2 (by decide)) (hri 0 3 (by decide))
    (hri 1 2 (by decide)) (hri 1 3 (by decide)) (hri 2 3 (by decide)) ?_).mono
    fun t ⟨hb, hdd, hc, h16, hfr, hkt, hmt⟩ => ?_
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact rowReg_ne r _
  have hY : ∀ j : Fin 4, swapDwords (t.vpr (outReg r j)) = output vs (slot r j) := by
    intro j
    have hsl : slot r j / 4 = j.val := by unfold slot; omega
    have hsm : slot r j % 4 = r.val := by unfold slot; omega
    rw [output]
    refine congrArg swapDwords (ext_vword fun e he => ?_)
    rw [vword_append4 _ _ _ _ he]
    have ht := transpose4_words (s.vpr (rowReg r 0)) (s.vpr (rowReg r 1)) (s.vpr (rowReg r 2))
      (s.vpr (rowReg r 3)) j.isLt he
    have hreg : t.vpr (outReg r j) = [perm (perm (s.vpr (rowReg r 0)) (s.vpr (rowReg r 1)) (tblVecs.getD 9 0))
        (perm (s.vpr (rowReg r 2)) (s.vpr (rowReg r 3)) (tblVecs.getD 9 0)) (tblVecs.getD 11 0),
      perm (perm (s.vpr (rowReg r 0)) (s.vpr (rowReg r 1)) (tblVecs.getD 9 0))
        (perm (s.vpr (rowReg r 2)) (s.vpr (rowReg r 3)) (tblVecs.getD 9 0)) (tblVecs.getD 12 0),
      perm (perm (s.vpr (rowReg r 0)) (s.vpr (rowReg r 1)) (tblVecs.getD 10 0))
        (perm (s.vpr (rowReg r 2)) (s.vpr (rowReg r 3)) (tblVecs.getD 10 0)) (tblVecs.getD 11 0),
      perm (perm (s.vpr (rowReg r 0)) (s.vpr (rowReg r 1)) (tblVecs.getD 10 0))
        (perm (s.vpr (rowReg r 2)) (s.vpr (rowReg r 3)) (tblVecs.getD 10 0)) (tblVecs.getD 12 0)].getD j 0 := by
      rw [outReg_cases]
      rcases j with ⟨_ | _ | _ | _ | j, hj⟩
      · exact hb
      · exact hdd
      · exact hc
      · exact h16
      · omega
    rw [hreg, ht]
    have hA : ∀ i : Fin 4, [s.vpr (rowReg r 0), s.vpr (rowReg r 1), s.vpr (rowReg r 2),
        s.vpr (rowReg r 3)].getD i.val 0 = s.vpr (rowReg r i) := by
      intro i; rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> first | rfl | omega
    rw [show (e ^^^ 1) = (⟨e ^^^ 1, xor_one_lt he⟩ : Fin 4).val from rfl, hA, hv _ _ j.isLt]
    simp only [hsl, hsm]
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceXor, List.getD_cons_zero, List.getD_cons_succ] <;> rfl
  have hq' : t.gpr .r4 = q := by rw [hkt.gpr _ (by decide) (by decide), hq]
  have hp' : t.gpr .r7 = p := by rw [hkt.gpr _ (by decide) (by decide), hp]
  refine (xorRows_ok r (List.finRange 4) (List.nodup_finRange 4) (hmt ▸ hd) hq' hp' halias hY
    (fun j _ => hfresh j) (fun j => by rw [hkt.rd, hkt.wr]; exact hin j)
    (fun j => by rw [hkt.wr]; exact hout j)).mono fun u ⟨hu, hku, hvu⟩ => ⟨hu, fun k hk => ?_, hkt.trans hku⟩
  have hk' : ∀ i : Fin 4, vreg k ≠ rowReg r i := by
    intro i e
    rw [rowReg_vreg, vreg_inj] at e
    subst e; simp at hk; omega
  rw [hvu _ (vreg_ne19 k), hfr _ (hk' 0) (hk' 1) (hk' 2) (hk' 3) (vreg_ne16 k) (vreg_ne17 k)
    (vreg_ne18 k) (vreg_ne19 k)]

theorem finishRows_ok (rs : List (Fin 4)) (hn : rs.Nodup) {s : State} {m₀ : Mem} {q p : Addr}
    {vs : Nat → CState} {done : List Nat} (h10 : s.gpr .r10 = s.syms tblName)
    (hd : DataTo m₀ s.mem q p 256 (output vs) done) (hq : s.gpr .r4 = q) (hp : s.gpr .r7 = p)
    (halias : q = p ∨ (⟨q, 256⟩ : Region).Disjoint ⟨p, 256⟩)
    (hv : ∀ r ∈ rs, ∀ i : Fin 4, ∀ j < 4,
      vword (s.vpr (rowReg r i)) j = (vs j)[4 * r.val + i.val]'(by omega))
    (hfresh : ∀ r ∈ rs, ∀ j : Fin 4, slot r j ∉ done)
    (hin : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap finishRow)) s fun s' =>
      DataTo m₀ s'.mem q p 256 (output vs) (rs.flatMap (fun r => (List.finRange 4).map (slot r)) ++ done) ∧
        Keep s s' := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd, Keep.refl _⟩
  | cons r rs ih =>
    have hr := (List.nodup_cons.mp hn).1
    apply WP.block_append
    refine (finishRow_ok r h10 hd hq hp halias (hv r (List.mem_cons_self ..))
      (hfresh r (List.mem_cons_self ..)) (hin r) (hout r)).mono fun t ⟨ht, hvkeep, hs⟩ => ?_
    have hv' : ∀ x ∈ rs, ∀ i : Fin 4, ∀ j < 4,
        vword (t.vpr (rowReg x i)) j = (vs j)[4 * x.val + i.val]'(by omega) := by
      intro x hx i j hj
      have hxr : (⟨4 * x.val + i.val, by omega⟩ : Fin 16).val / 4 ≠ r.val := by
        have hxr : x ≠ r := fun e => hr (e ▸ hx)
        have : x.val ≠ r.val := fun e => hxr (Fin.ext e)
        simp only; omega
      rw [rowReg_vreg, hvkeep _ hxr, ← rowReg_vreg]; exact hv x (List.mem_cons_of_mem _ hx) i j hj
    have hfresh' : ∀ x ∈ rs, ∀ j : Fin 4, slot x j ∉ (List.finRange 4).map (slot r) ++ done := by
      intro x hx j
      simp only [List.mem_append, not_or]
      refine ⟨?_, hfresh x (List.mem_cons_of_mem _ hx) j⟩
      intro hm
      obtain ⟨i, _, he⟩ := List.mem_map.mp hm
      exact slot_ne (fun (e : x = r) => hr (e ▸ hx)) j i he.symm
    refine (ih (List.nodup_cons.mp hn).2 (by rw [hs.r10, hs.syms, h10]) ht
      (by rw [hs.gpr _ (by decide) (by decide), hq]) (by rw [hs.gpr _ (by decide) (by decide), hp])
      hv' hfresh' (fun x j => by rw [hs.rd, hs.wr]; exact hin x j)
      (fun x j => by rw [hs.wr]; exact hout x j)).mono fun u ⟨hu, hk⟩ => ⟨?_, hs.trans hk⟩
    intro x
    simpa only [DataTo, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hu x

theorem all_slots (n : Fin 16) : n.val ∈ (List.finRange 4).flatMap (fun r => (List.finRange 4).map (slot r)) :=
  (show ∀ n : Fin 16, n.val ∈ (List.finRange 4).flatMap (fun r => (List.finRange 4).map (slot r)) by decide) n

/-- The four blocks' keystream XORed with the 256 bytes of the source (at
`r4`) into the destination (at `r7`), which is the source or apart from it. -/
theorem finish_ok {s : State} {vs : Nat → CState} (h : Holds vs s) (h10 : s.gpr .r10 = s.syms tblName)
    (halias : s.gpr .r4 = s.gpr .r7 ∨ (⟨s.gpr .r4, 256⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩)
    (hin : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r j : Fin 4, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap finishRow)) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r7 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .r4 + BitVec.ofNat 64 k) ^^^ (serialize (vs (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .r7, 256⟩] s.mem s'.mem ∧ Keep s s' := by
  refine (finishRows_ok (List.finRange 4) (List.nodup_finRange 4) h10
    (DataTo.nil s.mem (s.gpr .r4) (s.gpr .r7) 256 (output vs)) rfl rfl halias
    (fun r _ i j hj => by rw [rowReg_vreg, h _ j hj]; rfl) (fun _ _ _ => List.not_mem_nil)
    hin hout).mono fun s' ⟨hd, hs⟩ => ⟨?_, hd.frame, hs⟩
  intro k hk
  rw [hd _, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    ite_eq_left ⟨List.mem_append_left _ (all_slots ⟨k / 16, by omega⟩), hk⟩, output_byte vs k]

/-! ## The chunk -/

/-- A chunk: the keystream of four blocks XORed with the 256 bytes of the
source (at `r4`) into the destination (at `r7`), which is the source or apart
from it. -/
theorem chunk_ok (s : State) (hp : CPre s)
    (halias : s.gpr .r4 = s.gpr .r7 ∨ (⟨s.gpr .r4, 256⟩ : Region).Disjoint ⟨s.gpr .r7, 256⟩)
    (hin : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r j : Fin 4, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa chunk s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r7 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .r4 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (S₀ s) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .r7, 256⟩] s.mem s'.mem ∧ Keep s s' := by
  apply WP.seq
  refine (setup_ok hp).mono fun a ⟨ha, hra, hka, hma⟩ => ?_
  apply WP.seq
  refine (roundLoop_ok ha hra).mono fun b ⟨hb, hkb, hmb⟩ => ?_
  apply WP.block_append
  refine (feed_ok hp (hka.trans hkb) (hmb.trans hma) hb).mono fun c ⟨hc, hkc, hmc⟩ => ?_
  have h4 : c.gpr .r4 = s.gpr .r4 := hkc.gpr _ (by decide) (by decide)
  have h7 : c.gpr .r7 = s.gpr .r7 := hkc.gpr _ (by decide) (by decide)
  refine (finish_ok hc (hp.of_keep hkc).r10 (by rw [h4, h7]; exact halias)
    (fun r j => by rw [hkc.rd, hkc.wr, h4]; exact hin r j)
    (fun r j => by rw [hkc.wr, h7]; exact hout r j)).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, hkc.trans hs⟩
  · simpa only [h4, h7, hmc] using hd
  · simpa only [h7, hmc] using hf

end VG.Proof.ChaCha20.PPC64LE.Vmx4
