module

import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Impl.Sha1.X86_64.AvxBmi
public import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Impl.Sha1.X86_64.AvxBmi
meta import VerifiedGarbage.Proof.Sha1.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha1.X86_64.AvxBmi.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SHA-1 with AVX and BMI on x86-64: the message schedule of a register

`schedule` computes the next four words of the message schedule from the
previous sixteen (`xupd_quad`).
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64.AvxBmi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.AvxBmi
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1.X86_64.ShaNi (W_ge')

/-- The message words `W₄ᵢ … W₄ᵢ₊₃` (`W₄ᵢ` in the low doubleword). -/
def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofDwords (W M (4 * i)) (W M (4 * i + 1)) (W M (4 * i + 2)) (W M (4 * i + 3))

/-! ## The instructions, on doublewords -/

theorem pxor_ofDwords (a b c d a' b' c' d' : Word) :
    XBinOp.eval .pxor (ofDwords a b c d) (ofDwords a' b' c' d') =
      ofDwords (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  apply ext_dword <;> simp only [dword_pxor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem por_ofDwords (a b c d a' b' c' d' : Word) :
    XBinOp.eval .por (ofDwords a b c d) (ofDwords a' b' c' d') =
      ofDwords (a ||| a') (b ||| b') (c ||| c') (d ||| d') := by
  apply ext_dword <;> simp only [dword_por, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem pslld_ofDwords (a b c d : Word) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .pslld (ofDwords a b c d) n =
      ofDwords (a <<< n.toNat) (b <<< n.toNat) (c <<< n.toNat) (d <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega_arith, ite_false, dword_ofDwords_0,
    dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem psrld_ofDwords (a b c d : Word) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrld (ofDwords a b c d) n =
      ofDwords (a >>> n.toNat) (b >>> n.toNat) (c >>> n.toNat) (d >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega_arith, ite_false, dword_ofDwords_0,
    dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem alignRight_8 (a b c d a' b' c' d' : Word) :
    alignRight (ofDwords a' b' c' d') (ofDwords a b c d) 8 = ofDwords c d a' b' := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : (8 : BitVec 8).toNat * 8 = 64 := rfl
  simp only [alignRight, e, getLsbD_ofDwords, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, decide_eq_true hi, Bool.true_and,
    Nat.zero_add]
  rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h
  all_goals simp (disch := omega_arith) only [ite_eq_left, ite_eq_right]
  all_goals exact congrArg _ (by omega_arith)

theorem getLsbD_zero32 (i : Nat) : (0 : Word).getLsbD i = false := by simp

theorem psrldq_4 (a b c d : Word) :
    XShiftOp.eval .psrldq (ofDwords a b c d) 4 = ofDwords b c d 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : min (4 : BitVec 8).toNat 16 * 8 = 32 := rfl
  simp only [XShiftOp.eval, e, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords, getLsbD_zero32]
  rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega_arith) only [ite_eq_left, ite_eq_right]
  · exact congrArg _ (by omega_arith)
  · exact congrArg _ (by omega_arith)
  · exact congrArg _ (by omega_arith)
  · exact BitVec.getLsbD_of_ge d _ (by omega_arith)

theorem pslldq_12 (a b c d : Word) :
    XShiftOp.eval .pslldq (ofDwords a b c d) 12 = ofDwords 0 0 0 a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : min (12 : BitVec 8).toNat 16 * 8 = 96 := rfl
  simp only [XShiftOp.eval, e, BitVec.getLsbD_shiftLeft, getLsbD_ofDwords, getLsbD_zero32]
  rcases (by omega_arith : i < 96 ∨ 96 ≤ i) with h | h
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96)) with h' | h' | h' <;>
    simp (disch := omega_arith) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega_arith) only [hi, show ¬ i < 96 by omega_arith, show ¬ i < 32 by omega_arith,
      show ¬ i - 32 < 32 by omega_arith, show ¬ i - 32 - 32 < 32 by omega_arith,
      show i - 32 - 32 - 32 = i - 96 by omega_arith, show i - 96 < 32 by omega_arith, decide_true,
      decide_false, Bool.not_false, Bool.true_and, ite_false, ite_true]

/-! ## Rotations -/

theorem rotl1_or (x : Word) : x <<< 1 ||| x >>> 31 = x.rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_rotateLeft, decide_eq_true hi, Bool.true_and]
  rcases (by omega_arith : i < 1 ∨ 1 ≤ i) with h | h
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.false_or, ite_true]
  · simp only [show ¬ i < 1 by omega, decide_false, Bool.not_false, Bool.true_and, ite_false,
      BitVec.getLsbD_of_ge x (31 + i) (by omega_arith), Bool.or_false]

theorem xor_rotl1 (x y : Word) : x ^^^ y >>> 31 ^^^ y <<< 1 = x ^^^ y.rotateLeft 1 := by
  rw [← rotl1_or, BitVec.xor_assoc]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    decide_eq_true hi, Bool.true_and]
  rcases (by omega_arith : i < 1 ∨ 1 ≤ i) with h | h
  · simp [h]
  · simp [show ¬ i < 1 by omega, BitVec.getLsbD_of_ge y (31 + i) (by omega_arith)]

theorem rotl1_xor (x y : Word) : (x ^^^ y).rotateLeft 1 = x.rotateLeft 1 ^^^ y.rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  split <;> simp [hi]

theorem xor_zero32 (x : Word) : x ^^^ 0 = x := by simp

theorem zero_shr (n : Nat) : (0 : Word) >>> n = 0 := by simp
theorem zero_shl (n : Nat) : (0 : Word) <<< n = 0 := by simp

/-! ## One register of `schedule` -/

/-- What `schedule` computes from the four message registers `x₀ … x₃`
(oldest first), as its instructions do. -/
def xupd (x₀ x₁ x₂ x₃ : BitVec 128) : BitVec 128 :=
  let t₀ := alignRight x₁ x₀ 8
  let t₁ := XShiftOp.eval .psrldq x₃ 4
  let y := XBinOp.eval .pxor x₀ x₂
  let t₀ := XBinOp.eval .pxor t₀ t₁
  let y := XBinOp.eval .pxor y t₀
  let t₁ := XShiftOp.eval .psrld y 31
  let y := XShiftOp.eval .pslld y 1
  let y := XBinOp.eval .por y t₁
  let t₀ := XShiftOp.eval .pslldq y 12
  let t₁ := XShiftOp.eval .psrld t₀ 31
  let t₀ := XShiftOp.eval .pslld t₀ 1
  let y := XBinOp.eval .pxor y t₁
  XBinOp.eval .pxor y t₀

theorem xupd_eq (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ w₁₄ w₁₅ : Word) :
    xupd (ofDwords w₀ w₁ w₂ w₃) (ofDwords w₄ w₅ w₆ w₇) (ofDwords w₈ w₉ w₁₀ w₁₁)
      (ofDwords w₁₂ w₁₃ w₁₄ w₁₅) =
      ofDwords ((w₀ ^^^ w₈ ^^^ (w₂ ^^^ w₁₃)).rotateLeft 1) ((w₁ ^^^ w₉ ^^^ (w₃ ^^^ w₁₄)).rotateLeft 1)
        ((w₂ ^^^ w₁₀ ^^^ (w₄ ^^^ w₁₅)).rotateLeft 1)
        ((w₃ ^^^ w₁₁ ^^^ (w₅ ^^^ 0)).rotateLeft 1 ^^^ ((w₀ ^^^ w₈ ^^^ (w₂ ^^^ w₁₃)).rotateLeft 1).rotateLeft 1) := by
  simp only [xupd, alignRight_8, psrldq_4, pxor_ofDwords]
  simp only [psrld_ofDwords _ _ _ _ _ (by decide : (31 : BitVec 8).toNat < 32),
    pslld_ofDwords _ _ _ _ _ (by decide : (1 : BitVec 8).toNat < 32), por_ofDwords, BitVec.reduceToNat,
    rotl1_or]
  simp only [pslldq_12, psrld_ofDwords _ _ _ _ _ (by decide : (31 : BitVec 8).toNat < 32),
    pslld_ofDwords _ _ _ _ _ (by decide : (1 : BitVec 8).toNat < 32), pxor_ofDwords, BitVec.reduceToNat,
    zero_shr, zero_shl, xor_zero32, xor_rotl1]

/-- `schedule` computes the next four words of a block's schedule. -/
theorem xupd_quad (M : Block) (i : Nat) :
    xupd (quad M i) (quad M (i + 1)) (quad M (i + 2)) (quad M (i + 3)) = quad M (i + 4) := by
  simp only [quad]
  rw [xupd_eq]
  have w0 := W_ge' M (4 * i)
  have w1 := W_ge' M (4 * i + 1)
  have w2 := W_ge' M (4 * i + 2)
  have w3 := W_ge' M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega_arith, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega_arith,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega_arith, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega_arith,
    show 4 * i + 13 = 4 * (i + 3) + 1 by omega_arith, show 4 * i + 1 + 13 = 4 * (i + 3) + 2 by omega_arith,
    show 4 * i + 2 + 13 = 4 * (i + 3) + 3 by omega_arith,
    show 4 * i + 8 = 4 * (i + 2) by omega_arith, show 4 * i + 1 + 8 = 4 * (i + 2) + 1 by omega_arith,
    show 4 * i + 2 + 8 = 4 * (i + 2) + 2 by omega_arith, show 4 * i + 3 + 8 = 4 * (i + 2) + 3 by omega_arith,
    show 4 * i + 2 + 2 = 4 * (i + 1) by omega_arith, show 4 * i + 3 + 2 = 4 * (i + 1) + 1 by omega_arith,
    show 4 * i + 1 + 2 = 4 * i + 3 by omega_arith] at w0 w1 w2 w3 ⊢
  rw [w3, w0, w1, w2, xor_zero32, ← rotl1_xor]
  generalize W M = g
  congr 1 <;> ac_rfl

end VG.Proof.Sha1.X86_64.AvxBmi

/-!
# SHA-1 with AVX and BMI on x86-64: one round

`round t` adds `Wₜ + Kₜ`, `fₜ(b, c, d)` (`Ch` and `Maj` as sums of two masks
with no bit in common) and `ROTL⁵(a)` to `e`, in that order.
-/

namespace VG.Proof.Sha1.X86_64.AvxBmi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.AvxBmi
open VG.Impl.Sha1.X86_64 (var Fn fn slot T1)
open VG.Proof.Sha1.X86_64 (Vars pubRegs var_succ var_succ_zero fval f_eq rotl5 rotl30)
open VG.Spec.Sha1 (HashValue Word Block K W f)
open VG.Proof.Sha1 (roundKW rounds_succ round_eq)

/-- `e + fₜ(b, c, d)`, as the round adds it. -/
def fadd : Fn → Word → Word → Word → Word → Word
  | .ch, b, c, d, e => e + (~~~b &&& d) + (c &&& b)
  | .parity, b, c, d, e => e + (b ^^^ c ^^^ d)
  | .maj, b, c, d, e => e + (b &&& c) + ((b ^^^ c) &&& d)

theorem fadd_eq (g : Fn) (b c d e : Word) : fadd g b c d e = e + fval g b c d := by
  cases g
  · rw [fadd, BitVec.add_assoc, BitVec.add_eq_or_of_and_eq_zero (~~~b &&& d) (c &&& b)]
    · congr 1
      ext i hi
      simp only [fval, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
      cases b[i] <;> cases c[i] <;> cases d[i] <;> rfl
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
      cases b[i] <;> cases c[i] <;> cases d[i] <;> rfl
  · rfl
  · rw [fadd, BitVec.add_assoc, BitVec.add_eq_or_of_and_eq_zero (b &&& c) ((b ^^^ c) &&& d)]
    · congr 1
      ext i hi
      simp only [fval, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and]
      cases b[i] <;> cases c[i] <;> cases d[i] <;> rfl
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_zero]
      cases b[i] <;> cases c[i] <;> cases d[i] <;> rfl

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, T1, .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  simp only [var, Impl.Sha1.X86_64.work, T1]
  have h5 := Nat.mod_lt t (show 5 > 0 by omega_arith)
  generalize t % 5 = c at *
  revert h5; revert c; decide

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- What round `t` computes, as it computes it. -/
def roundV (g : Fn) (v : HashValue) (wk : Word) : HashValue :=
  #v[fadd g v[1] v[2] v[3] (v[4] + wk) + v[0].rotateRight 27, v[0], v[1].rotateRight 2, v[2], v[3]]

/-- The round is symbolically executed once per function `f`, for any
registers `a … e` (which `round_nodup` says are different from each other
and the others). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (wk : Word)
    (hv : Vars t s v) (hin : InRegions (s.rd ++ s.wr) (s.ea (slot t)) 4)
    (hw : s.mem.readW (s.ea (slot t)) 32 = wk) :
    WP isa (.block (round t)) s fun s' => Vars (t + 1) s' (roundV (fn t) v wk) ∧ Keeps s s' := by
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 4 by omega_arith),
    var_succ t _ (show 1 < 4 by omega_arith), var_succ t _ (show 2 < 4 by omega_arith),
    var_succ t _ (show 3 < 4 by omega_arith)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha1.X86_64.AvxBmi.round]
  generalize fn t = g
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  simp only [T1, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' ⊢
  cases g <;>
  simp only [fcode, T1, roundV, fadd, Keeps, List.cons_append, List.nil_append, ↓reduceIte, Nat.reduceLeDiff,
    runBlock_cons, runStep_some,
    runBlock_nil, reduceExec, execAlu32, execRorx32, execAndn32, readSrc32,
    isa, State.load32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags,
    RegUpd.ymmHi_setFlags,
    hd, hd', h0, h1, h2, h3, h4, hin, hw, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, and_self, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] <;>
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩ <;>
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hd']

/-- `roundV` is a round of the specification, given `Wₜ + Kₜ`. -/
theorem roundV_eq (M : Block) (v : HashValue) {t : Nat} :
    roundV (fn t) v (W M t + K t) = Spec.Sha1.round M v t := by
  rw [round_eq]
  simp only [roundV, roundKW, fadd_eq, ← f_eq, rotl5, rotl30]
  refine congrArg (fun x => #v[x, v[0], v[1].rotateRight 2, v[2], v[3]]) ?_
  ac_rfl

end VG.Proof.Sha1.X86_64.AvxBmi

/-!
# SHA-1 with AVX and BMI on x86-64: running the message schedule

`schedule i` and `loadW i` leave `W₄ᵢ … W₄ᵢ₊₃` in `msg i` and store them
with `K` in their slots.
-/

namespace VG.Proof.Sha1.X86_64.AvxBmi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.AvxBmi
open VG.Impl.Sha1.X86_64 (at_)
open VG.Spec.Sha1 (HashValue Word Block K W)
open VG.Proof.Sha1.X86_64 (ofInt_natCast)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem kreg_cases (g : Nat) : kreg g = .xmm8 ∨ kreg g = .xmm9 ∨ kreg g = .xmm10 ∨ kreg g = .xmm11 := by
  match g with
  | 0 => exact .inl rfl
  | 1 => exact .inr (.inl rfl)
  | 2 => exact .inr (.inr (.inl rfl))
  | 3 => exact .inr (.inr (.inr rfl))
  | _ + 4 => exact .inl rfl

/-- The vector registers of `schedule i` are all different. -/
theorem msg_nodup (n g : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), t0, t1, mBswap, tmp, kreg g].Nodup := by
  have key : ∀ c < 4, ∀ k ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm11],
      [msg c, msg (c + 1), msg (c + 2), msg (c + 3), t0, t1, mBswap, tmp, k].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega_arith]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide)) _ (by rcases kreg_cases g with h | h | h | h <;> simp [h])

/-- The schedule of words `4i … 4i+3`, from `a, b, c, d` in `msg i … msg (i+3)`. -/
theorem schedule_ok (i : Nat) (s : State) (a b c d kv : BitVec 128)
    (ha : s.xmm (msg i) = a) (hb : s.xmm (msg (i + 1)) = b) (hc : s.xmm (msg (i + 2)) = c)
    (hd : s.xmm (msg (i + 3)) = d) (hk : s.xmm (kreg (i / 5)) = kv)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((16 * (i % 4) : Nat) : Int)) 16) :
    WP isa (.block (schedule i)) s fun s' =>
      s'.xmm (msg i) = xupd a b c d ∧
      (∀ r, r ≠ msg i → r ≠ t0 → r ≠ t1 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((16 * (i % 4) : Nat) : Int))
        (XBinOp.eval .paddd (xupd a b c d) kv) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup i (i / 5)
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [schedule, storeWK, vb, vs, at_, List.cons_append, List.nil_append]
  generalize msg i = x₀ at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 2) = x₂ at *
  generalize msg (i + 3) = x₃ at *
  generalize kreg (i / 5) = kr at *
  simp only [t0, t1, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' ⊢
  simp only [reduceCtorEq, ↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, reduceVOpExec, isa, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.store128, State.ea, hout, hn, hn',
    ha, hb, hc, hd, hk, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r h0 h1 h2 => by simp [h0, h1, h2], trivial, rfl, trivial⟩

/-- Words `4i … 4i+3` loaded from the block at `rsi`. -/
theorem loadW_ok (i : Nat) (s : State) (kv : BitVec 128)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hm : s.xmm mBswap = bswapMask) (hk : s.xmm (kreg (i / 5)) = kv)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((16 * (i % 4) : Nat) : Int)) 16) :
    WP isa (.block (loadW i)) s fun s' =>
      s'.xmm (msg i) =
        XBinOp.eval .pshufb (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 128) bswapMask ∧
      (∀ r, r ≠ msg i → r ≠ t0 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((16 * (i % 4) : Nat) : Int))
        (XBinOp.eval .paddd (XBinOp.eval .pshufb
          (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 128) bswapMask) kv) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup i (i / 5)
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [loadW, storeWK, vb, at_, List.cons_append, List.nil_append]
  generalize msg i = x₀ at *
  generalize kreg (i / 5) = kr at *
  simp only [t0, t1, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' hm ⊢
  simp only [reduceCtorEq, ↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, reduceVOpExec, isa, RegUpd.xmm_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.store128, State.load128, State.ea, hin, hout, hn, hn',
    hm, hk, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r h0 h1 => by simp [h0, h1], trivial, rfl, trivial⟩

end VG.Proof.Sha1.X86_64.AvxBmi

/-!
# SHA-1 with AVX and BMI on x86-64: the rounds of a block

Group `n` runs rounds `4n … 4n+3`, which read `Wₜ + Kₜ` from the window in
the scratch space, then computes words `4n+16 … 4n+19` and stores them with
`K` in the slots the group read.
-/

namespace VG.Proof.Sha1.X86_64.AvxBmi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.AvxBmi
open VG.Impl.Sha1.X86_64 (at_ slot)
open VG.Spec.Sha1 (HashValue Word Block K W)
open VG.Proof.Sha1.X86_64 (Vars pubRegs ofInt_natCast contains_offset' winRegion)
open VG.Proof.Sha1.X86_64.ShaNi (K_eq)

/-- `W₄ₖ + K₄ₖ … W₄ₖ₊₃ + K₄ₖ₊₃`, as `storeWK` stores them. -/
def wkq (M : Block) (k : Nat) : BitVec 128 := XBinOp.eval .paddd (quad M k) (kvec (k / 5))

/-- Where `storeWK k` stores them. -/
abbrev wkAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofInt 64 ((16 * (k % 4) : Nat) : Int)

/-- Words `4k … 4k+3`, with `K`, are in their slots. -/
def WKMem (m : Mem) (scr : Addr) (M : Block) (k : Nat) : Prop := m.readW (wkAddr scr k) 128 = wkq M k

/-- The constants in the vector registers. -/
def Consts (s : State) : Prop :=
  s.xmm mBswap = bswapMask ∧ s.xmm (kreg 0) = kvec 0 ∧ s.xmm (kreg 1) = kvec 1 ∧
    s.xmm (kreg 2) = kvec 2 ∧ s.xmm (kreg 3) = kvec 3

theorem Consts.k {s : State} (h : Consts s) {g : Nat} (hg : g < 4) : s.xmm (kreg g) = kvec g := by
  obtain ⟨-, h0, h1, h2, h3⟩ := h
  rcases (by omega_arith : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3) with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The constants' registers are not those the schedule writes. -/
theorem consts_ne (n : Nat) : ∀ r ∈ [mBswap, kreg 0, kreg 1, kreg 2, kreg 3],
    r ≠ msg n ∧ r ≠ t0 ∧ r ≠ t1 := by
  have key : ∀ c < 4, ∀ r ∈ [mBswap, kreg 0, kreg 1, kreg 2, kreg 3], r ≠ msg c ∧ r ≠ t0 ∧ r ≠ t1 := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide))

theorem Consts.of_eq {s s' : State} (h : Consts s) (n : Nat)
    (he : ∀ r, r ≠ msg n → r ≠ t0 → r ≠ t1 → s'.xmm r = s.xmm r) : Consts s' := by
  have o := fun r hr => he r (consts_ne n r hr).1 (consts_ne n r hr).2.1 (consts_ne n r hr).2.2
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨(o _ (by simp)).trans h0, (o _ (by simp)).trans h1, (o _ (by simp)).trans h2,
    (o _ (by simp)).trans h3, (o _ (by simp)).trans h4⟩

theorem dword_quad (M : Block) (k : Nat) {q : Nat} (hq : q < 4) : dword (quad M k) q = W M (4 * k + q) := by
  rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp [quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem dword_kvec (g : Nat) {q : Nat} (hq : q < 4) : dword (kvec g) q = K (20 * g) := by
  have e : kvec g = ofDwords (K (20 * g)) (K (20 * g)) (K (20 * g)) (K (20 * g)) := rfl
  rw [e]
  rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem K_group {t : Nat} (ht : t < 80) : K (20 * (t / 4 / 5)) = K t := by
  rw [K_eq ht, K_eq (by omega_arith), Nat.div_div_eq_div_mul]
  congr 1
  omega_arith

/-- Round `t` reads `Wₜ + Kₜ`. -/
theorem wk_read {m : Mem} {scr : Addr} {M : Block} {t : Nat} (ht : t < 80) (h : WKMem m scr M (t / 4)) :
    m.readW (scr + BitVec.ofInt 64 ((4 * (t % 16) : Nat) : Int)) 32 = W M t + K t := by
  have hq : t % 4 < 4 := Nat.mod_lt _ (by decide)
  have e : scr + BitVec.ofInt 64 ((4 * (t % 16) : Nat) : Int) =
      wkAddr scr (t / 4) + BitVec.ofNat 64 (4 * (t % 4)) := by
    simp only [wkAddr, ofInt_natCast]
    rw [Offset.add_ofNat_add_ofNat, show 16 * (t / 4 % 4) + 4 * (t % 4) = 4 * (t % 16) by omega_arith]
  rw [e, ← dword_readW _ _ hq, h, wkq, dword_paddd _ _ hq, dword_quad _ _ hq, dword_kvec _ hq, K_group ht,
    show 4 * (t / 4) + t % 4 = t by omega_arith]

theorem wkAddr_contains (scr : Addr) (k : Nat) : (winRegion scr).Contains (wkAddr scr k) (128 / 8) :=
  contains_offset' (by omega_arith) (by omega_arith)

theorem wkmem_write {m : Mem} {scr : Addr} {M : Block} {k k' : Nat} (hne : k % 4 ≠ k' % 4)
    (v : BitVec 128) (h : WKMem m scr M k) : WKMem (m.writeW (wkAddr scr k') v) scr M k := by
  simp only [WKMem, wkAddr, ofInt_natCast] at h ⊢
  exact (readW_writeW_off m scr v (d := 16 * (k % 4)) (e := 16 * (k' % 4)) (n := 16) (by omega_arith)
    (by omega_arith) (by omega_arith)).trans h

theorem wkmem_self (m : Mem) (scr : Addr) (M : Block) (k : Nat) :
    WKMem (m.writeW (wkAddr scr k) (wkq M k)) scr M k :=
  Mem.readW_writeW_self m _ 16 _ (by omega_arith)

theorem in_scr {s : State} {scr : Addr} (hR : (⟨scr, 112⟩ : Region) ∈ s.wr) {d n : Nat} (hd : d + n ≤ 112) :
    InRegions s.wr (scr + BitVec.ofInt 64 (d : Int)) n :=
  ⟨_, hR, contains_offset' hd (by omega_arith)⟩

theorem round_step (t : Nat) (ht : t < 80) (H : HashValue) (M : Block) (scr : Addr) (s : State)
    (hv : Vars t s (Spec.Sha1.rounds H M t)) (hrcx : s.gpr .rcx = scr) (hR : (⟨scr, 112⟩ : Region) ∈ s.wr)
    (hw : WKMem s.mem scr M (t / 4)) :
    WP isa (.block (round t)) s fun s' => Vars (t + 1) s' (Spec.Sha1.rounds H M (t + 1)) ∧ Keeps s s' := by
  have ea : s.ea (slot t) = scr + BitVec.ofInt 64 ((4 * (t % 16) : Nat) : Int) := by
    simp only [slot, ea_at, hrcx]
  obtain ⟨r, hr, hc⟩ := in_scr hR (d := 4 * (t % 16)) (n := 4) (by omega_arith)
  refine WP.mono (round_ok t s _ (W M t + K t) hv (by rw [ea]; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [ea]; exact wk_read ht hw)) fun s' ⟨hv', hk⟩ => ⟨?_, hk⟩
  rw [rounds_succ, ← roundV_eq]; exact hv'

/-- What holds of the schedule after `n` groups, relative to the state `sB`
at their start. -/
structure Sched (M : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop where
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  consts : Consts s
  frame : Frame [winRegion scr] sB.mem s.mem
  wk : ∀ k, n ≤ k → k < n + 4 → k < 20 → WKMem s.mem scr M k
  msgs : ∀ k, n ≤ k → k < n + 4 → k < 20 → s.xmm (msg k) = quad M k

theorem Sched.keeps {M : Block} {scr : Addr} {sB : State} {n : Nat} {s s' : State}
    (h : Sched M scr sB n s) (hk : Keeps s s') : Sched M scr sB n s' := by
  obtain ⟨hm, hrd, hwr, hpub, hx, -⟩ := hk
  refine ⟨fun r hr => (hpub r hr).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_, hm ▸ h.frame,
    fun k h₁ h₂ h₃ => hm ▸ h.wk k h₁ h₂ h₃, fun k h₁ h₂ h₃ => hx ▸ h.msgs k h₁ h₂ h₃⟩
  rw [Consts, hx]; exact h.consts

theorem msg_ne (n k : Nat) (h₁ : n < k) (h₂ : k ≤ n + 3) : msg k ≠ msg n ∧ msg k ≠ t0 ∧ msg k ≠ t1 := by
  have key : ∀ c < 4, ∀ d < 4, 0 < d → msg (c + d) ≠ msg c ∧ msg (c + d) ≠ t0 ∧ msg (c + d) ≠ t1 := by
    decide
  rw [show msg k = msg (n % 4 + (k - n)) by simp only [msg]; rw [show (n % 4 + (k - n)) % 4 = k % 4 by omega_arith],
    show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) _ (by omega_arith) (by omega_arith)

theorem sched_step {M : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 112⟩ : Region) ∈ sB.wr) {n : Nat} (hn : n < 20) {s : State} (h : Sched M scr sB n s) :
    WP isa (.block (if n < 16 then schedule (n + 4) else [])) s fun s' =>
      Sched M scr sB (n + 1) s' ∧ s'.gpr = s.gpr := by
  by_cases h16 : n < 16
  · simp only [h16, ↓reduceIte]
    have hrcx' : s.gpr .rcx = scr := (h.pub .rcx (by decide)).trans hrcx
    have m : ∀ q < 4, s.xmm (msg (n + 4 + q)) = quad M (n + q) := fun q hq => by
      rw [show n + 4 + q = n + q + 4 by omega_arith, msg_add4]
      exact h.msgs (n + q) (by omega_arith) (by omega_arith) (by omega_arith)
    have ma := m 0 (by omega_arith)
    simp only [Nat.add_zero] at ma
    refine WP.mono (schedule_ok (n + 4) s _ _ _ _ _ ma (m 1 (by omega_arith)) (m 2 (by omega_arith))
      (m 3 (by omega_arith)) (h.consts.k (by omega_arith))
      (by rw [hrcx', h.wr]; exact in_scr hR (by omega_arith)))
      fun s' ⟨ex, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hg⟩
    rw [xupd_quad] at ex hm
    rw [hrcx'] at hm
    refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr,
      h.consts.of_eq (n + 4) hx, ?_, ?_, ?_⟩
    · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (wkAddr_contains scr _)
    · intro k h₁ h₂ h₃
      rw [hm]
      by_cases hkn : k = n + 4
      · subst hkn; exact wkmem_self _ _ _ _
      · exact wkmem_write (by omega_arith) _ (h.wk k (by omega_arith) (by omega_arith) h₃)
    · intro k h₁ h₂ h₃
      by_cases hkn : k = n + 4
      · subst hkn; exact ex
      · have o := msg_ne (n + 4) (k + 4) (by omega_arith) (by omega_arith)
        rw [msg_add4] at o
        rw [hx _ o.1 o.2.1 o.2.2]
        exact h.msgs k (by omega_arith) (by omega_arith) h₃
  · simp only [h16, ↓reduceIte]
    exact WP.block_nil ⟨⟨h.pub, h.rd, h.wr, h.consts, h.frame,
      fun k h₁ _ h₃ => h.wk k (by omega_arith) (by omega_arith) h₃,
      fun k h₁ _ h₃ => h.msgs k (by omega_arith) (by omega_arith) h₃⟩, rfl⟩

/-- After `n` groups. -/
def GInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop :=
  Vars (4 * n) s (Spec.Sha1.rounds H M (4 * n)) ∧ Sched M scr sB n s

theorem rounds4_ok {H : HashValue} {M : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 112⟩ : Region) ∈ sB.wr) {n : Nat} (hn : n < 20) {s : State} (hv : Vars (4 * n) s (Spec.Sha1.rounds H M (4 * n)))
    (hs : Sched M scr sB n s) :
    WP isa (.block (round (4 * n) ++ round (4 * n + 1) ++ round (4 * n + 2) ++ round (4 * n + 3))) s
      fun s' => Vars (4 * (n + 1)) s' (Spec.Sha1.rounds H M (4 * (n + 1))) ∧ Sched M scr sB n s' := by
  have hw : ∀ q < 4, WKMem s.mem scr M ((4 * n + q) / 4) := fun q hq => by
    rw [show (4 * n + q) / 4 = n by omega_arith]; exact hs.wk n (by omega_arith) (by omega_arith) hn
  have st : ∀ q < 4, ∀ {s₁ : State}, Keeps s s₁ → Vars (4 * n + q) s₁ (Spec.Sha1.rounds H M (4 * n + q)) →
      WP isa (.block (round (4 * n + q))) s₁ fun s' =>
        Vars (4 * n + q + 1) s' (Spec.Sha1.rounds H M (4 * n + q + 1)) ∧ Keeps s s' := by
    intro q hq s₁ hk hv₁
    have hs₁ := hs.keeps hk
    refine WP.mono (round_step _ (by omega_arith) H M scr s₁ hv₁ ((hs₁.pub .rcx (by decide)).trans hrcx)
      (hs₁.wr ▸ hR) (hk.1 ▸ hw q hq)) fun s' ⟨hv', hk'⟩ => ⟨hv', hk.trans hk'⟩
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (st 0 (by omega_arith) (Keeps.refl s) hv) fun s₁ ⟨hv₁, hk₁⟩ => ?_
  refine WP.mono (st 1 (by omega_arith) hk₁ hv₁) fun s₂ ⟨hv₂, hk₂⟩ => ?_
  refine WP.mono (st 2 (by omega_arith) hk₂ hv₂) fun s₃ ⟨hv₃, hk₃⟩ => ?_
  refine WP.mono (st 3 (by omega_arith) hk₃ hv₃) fun s₄ ⟨hv₄, hk₄⟩ => ?_
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega_arith]
  exact ⟨hv₄, hs.keeps hk₄⟩

theorem groups_ok (H : HashValue) (M : Block) (scr : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 112⟩ : Region) ∈ sB.wr) (h₀ : GInv H M scr sB 0 sB) :
    ∀ n ≤ 20, WP isa (groups n) sB (GInv H M scr sB n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s ⟨hv, hs⟩ => ?_)
    rw [group, WP.block_append_iff]
    refine WP.mono (rounds4_ok hrcx hR (by omega_arith) hv hs) fun s₁ ⟨hv₁, hs₁⟩ => ?_
    refine WP.mono (sched_step hrcx hR (by omega_arith) hs₁) fun s₂ ⟨hs₂, hg₂⟩ => ?_
    exact ⟨by simp only [Vars, hg₂]; exact hv₁, hs₂⟩

end VG.Proof.Sha1.X86_64.AvxBmi

/-!
# SHA-1 compression function on x86-64 with AVX and BMI

`compress_verified` proves `Impl.Sha1.X86_64.AvxBmi.compress` against the same
contract as the scalar `vg_sha1_compress`, reusing its precondition (`Pre`),
its block lemmas and its prologue and epilogue, which save and restore the
same registers in the same place.
-/

namespace VG.Proof.Sha1.X86_64.AvxBmi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.AvxBmi
open VG.Impl.Sha1.X86_64 (at_ save restore load update advance saved)
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha1.X86_64 (Vars pubRegs Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' ofInt_natCast stateAt_get stateAt_eq writeState
  stateAt_writeState frame_writeState winRegion win_sub Saved saveMem saveMem_saved saveMem_frame restore_ok
  saved_frame saved_bound vars0 load_eq update_eq Common LInv)

/-! ## Loading the block -/

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (p : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap32 (m.readW (p + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (p + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) bswapMask = quad M n := by
  rw [show bswapMask = 0x0c0d0e0f08090a0b0405060700010203#128 from rfl, pshufb_bswap]
  have e : ∀ j, j < 4 → bswap32 (dword (m.readW (p + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) j) =
      W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega_arith)]
    refine congrArg (fun a => bswap32 (m.readW a 32)) ?_
    simp only [ofInt_natCast]
    exact Offset.add_add_eq _ (by omega_arith)
  rw [e 0 (by omega_arith), e 1 (by omega_arith), e 2 (by omega_arith), e 3 (by omega_arith)]
  rfl

/-- After loading words `0 … 4n-1`, from the state `sL`. -/
structure LdInv (M : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = sL.gpr
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  consts : Consts s
  frame : Frame [winRegion scr] sL.mem s.mem
  wk : ∀ k < n, WKMem s.mem scr M k
  msgs : ∀ k < n, s.xmm (msg k) = quad M k

theorem load_step {M : Block} {p scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p) (hrcx : sL.gpr .rcx = scr) (hR : (⟨scr, 112⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 4 → InRegions (sL.rd ++ sL.wr) (p + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [winRegion scr] sL.mem m →
      ∀ t : Nat, t < 16 → bswap32 (m.readW (p + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t)
    {n : Nat} (hn : n < 4) {s : State} (h : LdInv M scr sL n s) :
    WP isa (.block (loadW n)) s (LdInv M scr sL (n + 1)) := by
  have hq := load_quad M s.mem p hn (hblk _ h.frame)
  refine WP.mono (loadW_ok n s (kvec 0) (by rw [h.gpr, h.rd, h.wr, hrsi]; exact hin n hn) h.consts.1
    (by rw [show n / 5 = 0 by omega_arith]; exact h.consts.k (by omega_arith))
    (by rw [h.gpr, h.wr, hrcx]; exact in_scr hR (by omega_arith)))
    fun s' ⟨ex, hx, hg, hm, hrd, hwr⟩ => ⟨hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
  · exact h.consts.of_eq n fun r h₁ h₂ _ => hx r h₁ h₂
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [h.gpr, hrcx]; exact wkAddr_contains scr n)
  · have hw : s'.mem = s.mem.writeW (wkAddr scr n) (wkq M n) := by
      rw [hm, h.gpr, hrsi, hrcx, hq, wkq, show n / 5 = 0 by omega_arith]
    intro k hk
    rw [hw]
    by_cases hkn : k = n
    · subst hkn; exact wkmem_self _ _ _ _
    · exact wkmem_write (by omega_arith) _ (h.wk k (by omega_arith))
  · intro k hk
    by_cases hkn : k = n
    · subst hkn; rw [ex, h.gpr, hrsi]; exact hq
    · have o₁ := (msg_ne k n (by omega_arith) (by omega_arith))
      rw [hx _ (Ne.symm o₁.1) (by
        have := (msg_ne k (k + 1) (by omega_arith) (by omega_arith)).2.1
        have key : ∀ c < 4, msg c ≠ t0 := by decide
        rw [show msg k = msg (k % 4) by simp only [msg, Nat.mod_mod]]
        exact key _ (Nat.mod_lt _ (by decide)))]
      exact h.msgs k (by omega_arith)

/-! ## The hash value -/

theorem loadH_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem ∧ s₁.xmm = s.xmm := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  simp only [reduceCtorEq, ↓reduceIte, vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, hrdi, h0, h1, h2, h3, h4,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 5 by decide), stateAt_get _ _ (show 1 < 5 by decide),
    stateAt_get _ _ (show 2 < 5 by decide), stateAt_get _ _ (show 3 < 5 by decide),
    stateAt_get _ _ (show 4 < 5 by decide)]
  simp [pubRegs]

theorem updateH_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, ea_at, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.xmm_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, RegUpd.cf_arithFlags, RegUpd.xmm_arithFlags,
    hrdi, i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4,
    Nat.reduceLeDiff, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], by simp only [and_self]⟩
  simp only [writeState, Vector.getElem_zipWith]

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them: the scalar function's, and
the constants. -/
structure Common' (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  consts : Consts s

/-- The loop invariant, at the start of block `i`. -/
structure LInv' (s₀ : State) (i : Nat) (s : State) : Prop extends LInv s₀ i s where
  consts : Consts s

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv' s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common' s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv' s₀ (i + 1) s') := by
  have hR : scrR s₀ ∈ s.wr := by rw [hL.wr, hp.wr]; simp
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have stw : ∀ {m m' : Mem}, Frame [winRegion (scr s₀)] m m' → ∀ k : Nat, k < 5 →
      m'.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 =
        m.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 :=
    fun hf k hk => hf.readW (contains_offset' (by omega_arith) (by omega_arith)) hst (by decide)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s.mem m → ∀ t : Nat, t < 16 →
      bswap32 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide),
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hin : ∀ n : Nat, n < 4 →
      InRegions (s.rd ++ s.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 :=
    fun n hn => by rw [hL.rd, hL.wr]; exact Proof.Sha1.X86_64.ShaNi.Pre.in_blk16 hp hi hn
  have hrsi : s.gpr .rsi = blkAddr s₀ i := hL.rsi
  have hrcx : s.gpr .rcx = scr s₀ := hL.rcx
  -- Load the block and the hash value.
  have hld : WP isa (.block (loadW 0 ++ loadW 1 ++ loadW 2 ++ loadW 3 ++ load)) s fun s₅ =>
      Vars 0 s₅ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₅.gpr r = s.gpr r) ∧ s₅.rd = s.rd ∧
      s₅.wr = s.wr ∧ Consts s₅ ∧ Frame [winRegion (scr s₀)] s.mem s₅.mem ∧
      (∀ k < 4, WKMem s₅.mem (scr s₀) (blk s₀ i) k) ∧ (∀ k < 4, s₅.xmm (msg k) = quad (blk s₀ i) k) := by
    rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
    have l0 : LdInv (blk s₀ i) (scr s₀) s 0 s :=
      ⟨rfl, rfl, rfl, hL.consts, Frame.refl _ _, fun k hk => absurd hk (by omega_arith),
        fun k hk => absurd hk (by omega_arith)⟩
    refine WP.mono (load_step hrsi hrcx hR hin hblk (n := 0) (by decide) l0) fun s₁ l1 => ?_
    refine WP.mono (load_step hrsi hrcx hR hin hblk (n := 1) (by decide) l1) fun s₂ l2 => ?_
    refine WP.mono (load_step hrsi hrcx hR hin hblk (n := 2) (by decide) l2) fun s₃ l3 => ?_
    refine WP.mono (load_step hrsi hrcx hR hin hblk (n := 3) (by decide) l3) fun s₄ l4 => ?_
    refine WP.mono (loadH_ok hp (by rw [l4.gpr]; exact hL.rdi) (by rw [l4.rd, hL.rd]) (by rw [l4.wr, hL.wr]))
      fun s₅ ⟨hv₅, hpub₅, hrd₅, hwr₅, hm₅, hx₅⟩ => ?_
    have e : stateAt s₄.mem (st s₀) = stateAt s.mem (st s₀) :=
      stateAt_eq fun k hk => by rw [stw l4.frame k hk, ← stateAt_get _ _ hk]
    rw [e] at hv₅
    exact ⟨hv₅, fun r hr => (hpub₅ r hr).trans (by rw [l4.gpr]), hrd₅.trans l4.rd, hwr₅.trans l4.wr,
      by rw [Consts, hx₅]; exact l4.consts, hm₅ ▸ l4.frame, fun k hk => hm₅ ▸ l4.wk k hk,
      fun k hk => hx₅ ▸ l4.msgs k hk⟩
  refine WP.seq (WP.mono hld fun s₅ ⟨hv₅, hpub₅, hrd₅, hwr₅, hc₅, hf₅, hw₅, hx₅⟩ => ?_)
  -- The rounds.
  have hrcx₅ : s₅.gpr .rcx = scr s₀ := (hpub₅ .rcx (by decide)).trans hrcx
  have hR₅ : scrR s₀ ∈ s₅.wr := hwr₅ ▸ hR
  have g₀ : GInv (stateAt s.mem (st s₀)) (blk s₀ i) (scr s₀) s₅ 0 s₅ :=
    ⟨hv₅, ⟨fun _ _ => rfl, rfl, rfl, hc₅, Frame.refl _ _, fun k _ h₂ _ => hw₅ k h₂,
      fun k _ h₂ _ => hx₅ k h₂⟩⟩
  refine WP.seq (WP.mono (groups_ok _ (blk s₀ i) (scr s₀) s₅ hrcx₅ hR₅ g₀ 20 (Nat.le_refl _))
    fun s₆ ⟨hv₆, hs₆⟩ => ?_)
  have pub₆ : ∀ r ∈ pubRegs, s₆.gpr r = s.gpr r := fun r hr => by rw [hs₆.pub r hr, hpub₅ r hr]
  have hrdi₆ : s₆.gpr .rdi = st s₀ := (pub₆ .rdi (by decide)).trans hL.rdi
  refine WP.mono (updateH_ok hp _ (stateAt s.mem (st s₀)) hv₆ hrdi₆
    (by rw [hs₆.rd, hrd₅, hL.rd]) (by rw [hs₆.wr, hwr₅, hL.wr]) fun k hk => ?_) fun s₇ h₇ => ?_
  · rw [stw hs₆.frame k hk, stw hf₅ k hk, stateAt_get _ _ hk]
  obtain ⟨hm₇, hrsi₇, hrdx₇, hzf₇, hrdi₇, hrcx₇, hrsp₇, hrd₇, hwr₇, hx₇⟩ := h₇
  have hrdx : s₆.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₆ .rdx (by decide), hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  have winsub : ∀ r ∈ [winRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₇.mem := by
    refine hL.frame.trans ((hf₅.sub winsub).trans ((hs₆.frame.sub winsub).trans ?_))
    rw [hm₇]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : Common' s₀ (i + 1) s₇ := by
    refine ⟨⟨by rw [hrdi₇, hrdi₆], by rw [hrcx₇, pub₆ .rcx (by decide), hL.rcx],
      by rw [hrsp₇, pub₆ .rsp (by decide), hL.rsp], by rw [hrd₇, hs₆.rd, hrd₅, hL.rd],
      by rw [hwr₇, hs₆.wr, hwr₅, hL.wr], hframe, ?_, ?_⟩, ?_⟩
    · rw [hm₇, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₇]
      refine saved_frame hp ?_ (.inr (frame_writeState (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hs₆.frame)
      exact saved_frame hp hL.saved (.inl hf₅)
    · rw [Consts, hx₇]; exact hs₆.consts
  have hev : eval .ne s₇ = some (!(s₆.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₇]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_arith
    refine ⟨?_, by omega_arith, ⟨{ hcommon.toCommon with rsi := ?_, rdx := ?_ }, hcommon.consts⟩⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₇, pub₆ .rsi (by decide), hL.rsi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hrdx₇, hrdx]

/-! ## The prologue -/

theorem kreg_0 : kreg 0 = .xmm8 := rfl
theorem kreg_1 : kreg 1 = .xmm9 := rfl
theorem kreg_2 : kreg 2 = .xmm10 := rfl
theorem kreg_3 : kreg 3 = .xmm11 := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ consts ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ Consts s₁ := by
  simp only [List.append_assoc]
  refine Spill.save_then .rcx saved (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.of_runBlock
  simp only [consts, const, vb, kreg_0, kreg_1, kreg_2, kreg_3, mBswap, tmp, List.cons_append,
    List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, VOp.exec, State.setV, State.lane,
    State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], trivial, trivial, trivial, trivial, ?_⟩
  simp only [reduceCtorEq, ↓reduceIte, Consts, kreg_0, kreg_1, kreg_2, kreg_3, mBswap, VBinOp.sse, movq_const, and_self]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha1.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common' s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc.toCommon)
  have hc₀ : Common' s₀ 0 s₁ := by
    refine ⟨⟨by rw [hg _ (by decide)], by rw [hg _ (by decide)], by rw [hg _ (by decide)], hrd, hwr, ?_, ?_,
      by rw [hm]; exact saveMem_saved⟩, hc⟩
    · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
    · rw [hm]
      apply stateAt_eq
      intro k hk
      rw [saveMem_frame.readW (contains_offset' (off := 4 * k) (len := 20) (by omega_arith) (by omega_arith))
        (by simpa using hp.st_scr)
        (by decide), ← stateAt_get _ _ hk]
      rfl
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv' s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common' s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega_arith, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv' s₀ 0 s₁ :=
      ⟨{ hc₀.toCommon with
        rsi := by rw [hg _ (by decide)]; simp [blkAddr]
        rdx := by rw [hg _ (by decide)]; simp [nb] }, hc⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem compress_verified :
    Verified X86_64.target Impl.Sha1.X86_64.AvxBmi.compress Proof.Sha1.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, (Proof.Sha1.X86_64.compress_verified).2.2⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Sha1.X86_64.AvxBmi
