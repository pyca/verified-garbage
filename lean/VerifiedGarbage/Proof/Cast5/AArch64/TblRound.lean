module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblSbox
public import VerifiedGarbage.Proof.Blowfish.AArch64.Round
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# CAST5 on AArch64: one round on sixteen blocks

`round_ok`: `round t up`, with `x5` at `Kmᵢ` in the subkeys, for a round `i`
of Type `t`, leaves `R` in `A` and `L ^ f(R, Kmᵢ, Krᵢ)` in `B`, word by
word, and moves `x5` to the next subkey (`up`) or the previous one.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planeOff
  planes words wordReg)
open VG.AArch64.Tbl (VOnly)
open VG.Spec.Cast5 (Word)

/-! ## Words -/

def opEval (o : Op) (a b : Word) : Word :=
  match o with
  | .add => a + b
  | .eor => a ^^^ b
  | .sub => a - b

/-- `f`'s accumulation through S-box `j`, for a round of Type `t` on `I = i`. -/
def fAcc (t : Nat) (i : Word) : Nat → Word
  | 0 => sbox 0 (Spec.Cast5.byte i 0)
  | j + 1 => opEval (op t (j + 1)) (fAcc t i j) (sbox (j + 1) (Spec.Cast5.byte i (j + 1)))

/-- §2.2's `f` of round `i`, of Type `t`. -/
theorem f_eq_fAcc {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hi : i % 3 = t % 3) (d km kr : Word) :
    Spec.Cast5.f i d km kr = fAcc t ((opEval (op t 0) km d).rotateLeft (kr.toNat % 32)) 3 := by
  rcases ht with rfl | rfl | rfl
  · have : i % 3 = 1 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 2 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 0 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]

theorem byte_eq (i : Word) (j : Nat) : Spec.Cast5.byte i j = i.extractLsb' (8 * (3 - j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [Spec.Cast5.byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hk,
    decide_true, Bool.true_and]

/-- The rotation, as the halves of a 64-bit product by a power of two. -/
theorem one_rot : ∀ r < 32, ((1 : Word).rotateLeft r).setWidth 64 = BitVec.twoPow 64 r := by decide
theorem rot_mul (x : Word) {r : Nat} (hr : r < 32) :
    (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 0 32 |||
      (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 32 32 = x.rotateLeft r := by
  rw [one_rot r hr, BitVec.mul_twoPow_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [Proof.Cast5.getLsbD_rotateLeft_lt _ hr hk, BitVec.getLsbD_or, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth]
  have h2 : 32 + k < 64 := by omega
  simp only [hk, h2, decide_true, Bool.true_and, Nat.zero_add]
  by_cases hkr : k < r
  · have e : 32 + k - r = 32 - r + k := by omega
    have h3 : ¬ 32 + k < r := by omega
    have h4 : 32 - r + k < 64 := by omega
    simp [show k < 64 by omega, hkr, h3, e, h4]
  · have h3 : ¬ 32 + k < r := by omega
    have h5 : k - r < 64 := by omega
    have h6 : x.getLsbD (32 + k - r) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [show k < 64 by omega, hkr, h3, h5, h6]
theorem vword_ofVDwords (a b : BitVec 64) {k : Nat} (hk : k < 4) :
    vword (ofVDwords a b) k = (if k < 2 then a else b).extractLsb' (32 * (k % 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [vword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and] <;>
    simp <;> (try split) <;> first | omega | rfl | (congr 1; omega)

theorem vword_or (x y : BitVec 128) (e : Nat) : vword (x ||| y) e = vword x e ||| vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

/-! ## What a step keeps -/

/-- Only the general-purpose registers `gs` and the vector registers `vs`
(and the flags) change. -/
structure RFrame (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem RFrame.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : RFrame gs vs a b)
    (h₂ : RFrame gs vs b c) : RFrame gs vs a c :=
  ⟨fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr),
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.syms.trans h₁.syms⟩

theorem RFrame.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : RFrame gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : RFrame gs' vs' a b :=
  ⟨fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h'), h.mem, h.rd, h.wr,
    h.sp, h.syms⟩

theorem RFrame.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : RFrame [] vs a b := by
  refine ⟨fun r _ => ?_, h.2, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h.1]

/-! ## Four registers, one instruction each -/

/-- Four instructions, instruction `k` writing `D k` with a value `g k` that
reads, of the registers `D`, at most `D k`. -/
theorem map4_run (s : State) (ins : Nat → Instr) (D : Nat → VReg)
    (g : Nat → (VReg → BitVec 128) → BitVec 128)
    (he : ∀ k < 4, ∀ u : State, exec (ins k) u = some (u.setV (D k) (g k u.v)))
    (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → D k ≠ D k')
    (hg : ∀ k < 4, ∀ v v' : VReg → BitVec 128, (∀ r, (∀ k' < 4, k' ≠ k → r ≠ D k') → v' r = v r) →
      g k v' = g k v) :
    ∃ s', runBlock isa ((List.range 4).map ins) s = some s' ∧ (∀ k < 4, s'.v (D k) = g k s.v) ∧
      VOnly [D 0, D 1, D 2, D 3] s s' := by
  let s₁ := s.setV (D 0) (g 0 s.v)
  let s₂ := s₁.setV (D 1) (g 1 s₁.v)
  let s₃ := s₂.setV (D 2) (g 2 s₂.v)
  let s₄ := s₃.setV (D 3) (g 3 s₃.v)
  have hl : (List.range 4).map ins = [ins 0, ins 1, ins 2, ins 3] := rfl
  have ne := fun k hk k' hk' (h : k ≠ k') => hinj k hk k' hk' h
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, he 0 (by decide), runStep_some, runBlock_cons, he 1 (by decide), runStep_some,
      runBlock_cons, he 2 (by decide), runStep_some, runBlock_cons, he 3 (by decide), runStep_some,
      runBlock_nil]
  · intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 1 (by decide) (by decide))]
      exact v_setV_self _ _ _
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 1 (by decide) _ _ fun r hr => v_setV_of_ne _ _ (hr 0 (by decide) (by decide))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 2 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 2 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide)))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 3 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 2 (by decide) (by decide))).trans
          ((v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide))))
  · exact (((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-! ## The operations -/

/-- An operation on the four words of two vectors. -/
def opV (o : Op) (x y : BitVec 128) : BitVec 128 :=
  match o with
  | .add => VArr.s4.map2 (fun _ a b => a + b) x y
  | .eor => x ^^^ y
  | .sub => VArr.s4.map2 (fun _ a b => a - b) x y

theorem exec_op (o : Op) (s : State) (d n m : VReg) :
    exec (o.instr d n m) s = some (s.setV d (opV o (s.v n) (s.v m))) := by
  cases o
  · exact (rfl : exec (.vop (.add .s4 d n m)) s = _)
  · exact (rfl : exec (veor d n m) s = _)
  · exact (rfl : exec (.vop (.sub .s4 d n m)) s = _)

theorem vword_opV (o : Op) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (opV o x y) l = opEval o (vword x l) (vword y l) := by
  cases o
  · show vword (VArr.s4.map2 (fun _ a b => a + b) x y) l = vword x l + vword y l
    rw [vword_map2 _ x y hl]
  · exact Proof.Blowfish.AArch64.vword_xor x y l
  · show vword (VArr.s4.map2 (fun _ a b => a - b) x y) l = vword x l - vword y l
    rw [vword_map2 _ x y hl]

end VG.Proof.Cast5.AArch64.Tbl
