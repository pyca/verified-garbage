module

public import VerifiedGarbage.Proof.Sha1.X86.Compress
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Const
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
public import VerifiedGarbage.Impl.Sha1.X86.ShaNi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha1.X86.Compress
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Const
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sha1.X86.ShaNi.Lit
meta import VerifiedGarbage.Impl.Sha1.X86.ShaNi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Reduce
public import VerifiedGarbage.Proof.Sha1.Spec
public import VerifiedGarbage.TCB.X86.Sse
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Sha1.Spec
meta import VerifiedGarbage.TCB.X86.Sse
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Sha1.X86.ShaNi.Rounds`, which this module and modules that import it used -/

section

/-! ### `Sha1.X86.ShaNi.Spec`, which this module and modules that import it used -/

section

/-!
# SHA-1 with the SHA extensions on x86: the values in the SSE registers

How the working variables, the message schedule and the constants are laid out
in SSE registers, and that `sha1rnds4`, `sha1nexte` and `sha1msg1`/`sha1msg2`
compute rounds and schedule words of `Spec/Sha1.lean`: the lemmas of x86-64
(`Proof/Sha1/X86_64/ShaNi/Compress.lean`), for x86's model of the
instructions.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.ShaNi

open VG VG.X86
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `A, B, C, D`, as `sha1rnds4` takes and returns them
(`A` in bits 127:96). -/
def abcd (v : HashValue) : BitVec 128 := ofDwords v[3] v[2] v[1] v[0]

/-- The working variable `E` in bits 127:96, and zeros. -/
def eReg (v : HashValue) : BitVec 128 := ofDwords 0 0 0 v[4]

/-- The message schedule words `W₄ᵢ … W₄ᵢ₊₃` (`W₄ᵢ` in bits 127:96). -/
def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofDwords (W M (4 * i + 3)) (W M (4 * i + 2)) (W M (4 * i + 1)) (W M (4 * i))

/-! ## Rounds -/

/-- One round in group `g` of 20 rounds, as `sha1rnds4` computes it. -/
def hw (g : Nat) (v : HashValue) (w : Word) : HashValue :=
  #v[sha1F g v[1] v[2] v[3] + v[0].rotateLeft 5 + w + v[4] + sha1K g, v[0], v[1].rotateLeft 30, v[2],
    v[3]]

theorem f_eq {t : Nat} (ht : t < 80) : f t = sha1F (t / 20) := by
  funext x y z
  simp only [f, Spec.Sha1.ch, Spec.Sha1.parity, Spec.Sha1.maj]
  rcases (by omega_using [] : t < 20 ∨ (20 ≤ t ∧ t < 40) ∨ (40 ≤ t ∧ t < 60) ∨ 60 ≤ t) with h | h | h | h
  · simp only [h, ite_true, Nat.div_eq_of_lt h]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], h.2, ite_false, ite_true, show t / 20 = 1 by omega_using [h]]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], show ¬ t < 40 by omega_using [h], h.2, ite_false, ite_true,
      show t / 20 = 2 by omega_using [h]]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], show ¬ t < 40 by omega_using [h], show ¬ t < 60 by omega_using [h], ite_false,
      show t / 20 = 3 by omega_using [ht, h]]; rfl

theorem K_eq {t : Nat} (ht : t < 80) : K t = sha1K (t / 20) := by
  simp only [K]
  rcases (by omega_using [] : t < 20 ∨ (20 ≤ t ∧ t < 40) ∨ (40 ≤ t ∧ t < 60) ∨ 60 ≤ t) with h | h | h | h
  · simp only [h, ite_true, Nat.div_eq_of_lt h]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], h.2, ite_false, ite_true, show t / 20 = 1 by omega_using [h]]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], show ¬ t < 40 by omega_using [h], h.2, ite_false, ite_true,
      show t / 20 = 2 by omega_using [h]]; rfl
  · simp only [show ¬ t < 20 by omega_using [h], show ¬ t < 40 by omega_using [h], show ¬ t < 60 by omega_using [h], ite_false,
      show t / 20 = 3 by omega_using [ht, h]]; rfl

/-- A round of the specification is `hw` of its group. -/
theorem round_hw (M : Block) (v : HashValue) {t : Nat} (ht : t < 80) :
    Spec.Sha1.round M v t = hw (t / 20) v (W M t) := by
  rw [round_eq, f_eq ht, K_eq ht]
  simp only [roundKW, hw]
  refine congrArg (fun x => #v[x, v[0], v[1].rotateLeft 30, v[2], v[3]]) ?_
  ac_rfl

/-- Four rounds in group `g`. -/
def hw4 (g : Nat) (v : HashValue) (w0 w1 w2 w3 : Word) : HashValue :=
  hw g (hw g (hw g (hw g v w0) w1) w2) w3

theorem hw4_e (g : Nat) (v : HashValue) (w0 w1 w2 w3 : Word) :
    (hw4 g v w0 w1 w2 w3)[4] = v[0].rotateLeft 30 := rfl

section
variable (g : Nat) (v : HashValue) (w : Word)
theorem hw_0 : (hw g v w)[0] = sha1F g v[1] v[2] v[3] + v[0].rotateLeft 5 + w + v[4] + sha1K g := rfl
theorem hw_1 : (hw g v w)[1] = v[0] := rfl
theorem hw_2 : (hw g v w)[2] = v[1].rotateLeft 30 := rfl
theorem hw_3 : (hw g v w)[3] = v[2] := rfl
theorem hw_4 : (hw g v w)[4] = v[3] := rfl
end

theorem imm_eq {g : Nat} (hg : g < 4) : ((BitVec.ofNat 8 g).extractLsb' 0 2).toNat = g := by
  rcases (by omega_using [hg] : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `sha1rnds4` does four rounds of group `g`, given `W₀ + E` in bits 127:96 of
its source and `W₁ … W₃` below. -/
theorem rnds4_eq (v : HashValue) {g : Nat} (hg : g < 4) (w0 w1 w2 w3 : Word) :
    sha1Rnds4 (abcd v) (ofDwords w3 w2 w1 (w0 + v[4])) (BitVec.ofNat 8 g) =
      abcd (hw4 g v w0 w1 w2 w3) := by
  simp only [sha1Rnds4, imm_eq hg, abcd, hw4, hw_0, hw_1, hw_2, hw_3, hw_4, dword_ofDwords_0,
    dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, ← BitVec.add_assoc]

/-! ## The value added to the first message word -/

theorem zero_add32 (x : Word) : (0 : Word) + x = x := by simp

/-- In the first four rounds, `E` is added by `paddd`. -/
theorem paddd_e (v : HashValue) (M : Block) :
    XBinOp.eval .paddd (eReg v) (quad M 0) =
      ofDwords (W M (4 * 0 + 3)) (W M (4 * 0 + 2)) (W M (4 * 0 + 1)) (W M (4 * 0) + v[4]) := by
  simp only [XBinOp.eval, eReg, quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, BitVec.add_comm v[4], zero_add32]

/-- After that, `E` is `A` of four rounds before, rotated left by 30, which
`sha1nexte` adds. -/
theorem nexte_e (x : BitVec 128) (M : Block) (i : Nat) :
    XBinOp.eval .sha1nexte x (quad M i) =
      ofDwords (W M (4 * i + 3)) (W M (4 * i + 2)) (W M (4 * i + 1))
        (W M (4 * i) + (dword x 3).rotateLeft 30) := by
  simp only [XBinOp.eval, quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## The message schedule -/

theorem dword_xor (x y : BitVec 128) (k : Nat) : dword (x ^^^ y) k = dword x k ^^^ dword y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, decide_eq_true hi, Bool.true_and]

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = (W M (t + 13) ^^^ W M (t + 8) ^^^ W M (t + 2) ^^^ W M t).rotateLeft 1 := by
  rw [W_ge M (by omega_using []), show t + 16 - 3 = t + 13 by omega_using [], show t + 16 - 8 = t + 8 by omega_using [],
    show t + 16 - 14 = t + 2 by omega_using [], Nat.add_sub_cancel]

/-- `sha1msg1`, `pxor` and `sha1msg2` compute the next four schedule words
from the previous sixteen. -/
theorem schedule_eq (M : Block) (i : Nat) :
    sha1Msg2 (XBinOp.eval .pxor (XBinOp.eval .sha1msg1 (quad M i) (quad M (i + 1))) (quad M (i + 2)))
      (quad M (i + 3)) = quad M (i + 4) := by
  simp only [sha1Msg2, XBinOp.eval, quad, dword_xor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]
  have w0 := W_ge' M (4 * i)
  have w1 := W_ge' M (4 * i + 1)
  have w2 := W_ge' M (4 * i + 2)
  have w3 := W_ge' M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega_using [], show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega_using [],
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega_using [], show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega_using [],
    show 4 * i + 13 = 4 * (i + 3) + 1 by omega_using [], show 4 * i + 1 + 13 = 4 * (i + 3) + 2 by omega_using [],
    show 4 * i + 2 + 13 = 4 * (i + 3) + 3 by omega_using [],
    show 4 * i + 8 = 4 * (i + 2) by omega_using [], show 4 * i + 1 + 8 = 4 * (i + 2) + 1 by omega_using [],
    show 4 * i + 2 + 8 = 4 * (i + 2) + 2 by omega_using [], show 4 * i + 3 + 8 = 4 * (i + 2) + 3 by omega_using [],
    show 4 * i + 2 + 2 = 4 * (i + 1) by omega_using [], show 4 * i + 3 + 2 = 4 * (i + 1) + 1 by omega_using [],
    show 4 * i + 1 + 2 = 4 * i + 3 by omega_using []] at w0 w1 w2 w3 ⊢
  rw [w3, w0, w1, w2]
  generalize W M = f
  ac_rfl

/-! ## Adding the working variables into the hash value -/

theorem paddd_abcd (v H : HashValue) :
    XBinOp.eval .paddd (abcd v) (abcd H) = abcd (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, abcd, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

theorem nexte_eReg (x : BitVec 128) (v H : HashValue) (hx : (dword x 3).rotateLeft 30 = v[4]) :
    XBinOp.eval .sha1nexte x (eReg H) = eReg (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, eReg, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith, hx, BitVec.add_comm H[4]]

end VG.Proof.Sha1.X86.ShaNi

end

end

/-!
# SHA-1 with the SHA extensions on x86: the 80 rounds of a block

The rounds of `Impl.Sha1.X86.ShaNi`, which are those of x86-64
(`Proof/Sha1/X86_64/ShaNi/Compress.lean`) but for the registers holding the
block pointer: rounds `0 … 4n-1` from `ABCD` in `xmm0` and `E` in `xmm1`
compute the specification's rounds, keeping the last sixteen schedule words.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.ShaNi

open VG VG.X86 VG.Impl.Sha1.X86.ShaNi
open VG.Spec.Sha1 (HashValue Word Block W)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The registers of a group of four rounds are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega_using []]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem msg_other (n : Nat) (r : XReg)
    (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

/-- `msg k` for the three registers other than `msg n` that hold schedule words. -/
theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega_using [h₁, h₂] : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

/-! ## Four rounds -/

theorem rounds4_ok (n : Nat) (s : State) (a x q : BitVec 128)
    (h0 : s.xmm .xmm0 = a) (h1 : s.xmm .xmm1 = x) (hq : s.xmm (msg n) = q) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = sha1Rnds4 a (XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x q)
        (BitVec.ofNat 8 (n / 5)) ∧
      s'.xmm .xmm1 = a ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4]
  generalize msg n = y at *
  generalize (if n = 0 then XBinOp.paddd else XBinOp.sha1nexte) = op
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, reduceCtorEq, hd, h0, h1, hq,
    eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, not_false_eq_true]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 2)) = c)
    (hd' : s.xmm (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = sha1Msg2 (XBinOp.eval .pxor (XBinOp.eval .sha1msg1 a b) c) d ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 4 by omega_using [hn], ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, hd'', ha, hb, hc, hd',
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r h0 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, not_false_eq_true]

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * n)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (addr (s.gpr .ecx) (16 * n)) 128) (s.xmm .xmm7) ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h7 := (msg_other n .xmm7 (.inr (.inr (.inr rfl)))).symm
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, State.load128, ea_at, hin,
    h7, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h0 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, not_false_eq_true]

/-- What `xmm1` holds before rounds `4n …`: for `n = 0`, `E` and zeros; after
that, `ABCD` of four rounds before, whose `A` rotated left by 30 is `E`. -/
def ECarry (n : Nat) (v : HashValue) (x : BitVec 128) : Prop :=
  if n = 0 then x = eReg v else (dword x 3).rotateLeft 30 = v[4]

/-- The value added to rounds `4n … 4n+3`: `W₄ₙ + E`, then `W₄ₙ₊₁ … W₄ₙ₊₃`. -/
theorem wk_eq (M : Block) (n : Nat) (v : HashValue) (x : BitVec 128) (hx : ECarry n v x) :
    XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x (quad M n) =
      ofDwords (W M (4 * n + 3)) (W M (4 * n + 2)) (W M (4 * n + 1)) (W M (4 * n) + v[4]) := by
  by_cases h : n = 0
  · subst h
    simp only [ECarry, ite_true] at hx
    simp only [ite_true, hx, paddd_e]
  · simp only [ECarry, h, ite_false] at hx
    simp only [h, ite_false, nexte_e, hx]

theorem rounds_four (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) :
    Spec.Sha1.rounds H M (4 * (n + 1)) =
      hw4 (n / 5) (Spec.Sha1.rounds H M (4 * n)) (W M (4 * n)) (W M (4 * n + 1)) (W M (4 * n + 2))
        (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega_using [], rounds_succ, rounds_succ, rounds_succ, rounds_succ,
    round_hw _ _ (by omega_using [hn]), round_hw _ _ (by omega_using [hn]), round_hw _ _ (by omega_using [hn]), round_hw _ _ (by omega_using [hn]),
    show (4 * n) / 20 = n / 5 by omega_using [], show (4 * n + 1) / 20 = n / 5 by omega_using [],
    show (4 * n + 2) / 20 = n / 5 by omega_using [], show (4 * n + 3) / 20 = n / 5 by omega_using []]
  rfl

theorem rounds4_step (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) (s : State)
    (h0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n)))
    (h1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)) (hq : s.xmm (msg n) = quad M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * (n + 1))) ∧
      ECarry (n + 1) (Spec.Sha1.rounds H M (4 * (n + 1))) (s'.xmm .xmm1) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ _ h0 rfl hq) fun s' ⟨e0, e1, hx, hg, hm, hrd, hwr⟩ => ?_
  rw [wk_eq M n _ _ h1, rnds4_eq _ (by omega_using [hn])] at e0
  refine ⟨by rw [e0, rounds_four H M hn], ?_, hx, hg, hm, hrd, hwr⟩
  simp only [ECarry, Nat.add_one_ne_zero, ite_false, e1, abcd, dword_ofDwords_3]
  rw [rounds_four H M hn, hw4_e]

/-! ## Loading the message words -/

theorem getLsbD_bswap_block' (x : BitVec 32) {j r : Nat} (hj : j < 4) (hr : r < 8) :
    (bswap x).getLsbD (8 * j + r) = x.getLsbD (8 * (3 - j) + r) := by
  rw [getLsbD_bswap_block x hj hr]
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
  simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, Nat.zero_add] <;>
  exact congrArg _ (by omega)

/-- Reversing the bytes of a register reverses the order of its doublewords
and the bytes of each. -/
theorem pshufb_rev (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask =
      ofDwords (bswap (dword a 3)) (bswap (dword a 2)) (bswap (dword a 1)) (bswap (dword a 0)) := by
  have hb : XBinOp.eval .pshufb a bswapMask = ofBytes fun j => byte a (15 - j) := by
    simp only [XBinOp.eval, ofBytes, bswapMask]
    rfl
  rw [hb]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega_using [hi], by omega_using [], by omega_using []⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega_using [],
    getLsbD_ofDwords_block _ _ _ _ (by omega_using [hk]) (by omega_using [hr])]
  have hm := Nat.mod_lt k (by decide : 4 > 0)
  rcases (by omega_using [hk] : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3) with h | h | h | h <;>
  simp only [h, ↓reduceIte, Nat.reduceEqDiff] <;>
  rw [getLsbD_bswap_block' _ hm hr] <;>
  simp only [byte, dword, BitVec.getLsbD_extractLsb', decide_eq_true hr,
    decide_eq_true (show 8 * (3 - k % 4) + r < 32 by omega_using [hr]), Bool.true_and] <;>
  exact congrArg a.getLsbD (by omega_using [h])

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (bp : BitVec 32) (hfit : bp.toNat + 64 ≤ 2 ^ 32)
    {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap (m.readW (addr bp (4 * t)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (addr bp (16 * n)) 128) bswapMask = quad M n := by
  rw [pshufb_rev]
  have e : ∀ j, j < 4 → bswap (dword (m.readW (addr bp (16 * n)) 128) j) = W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega_using [hn, hj])]
    refine congrArg (fun a => bswap (m.readW a 32)) ?_
    rw [addr_eq (by omega_using [hfit, hn]), addr_eq (by omega_using [hfit, hn, hj]), Offset.add_ofNat_add_ofNat,
      show 16 * n + 4 * j = 4 * (4 * n + j) by omega_using []]
  rw [e 0 (by omega_using []), e 1 (by omega_using []), e 2 (by omega_using []), e 3 (by omega_using [])]
  rfl

/-! ## The rounds -/

/-- What holds after rounds `0 … 4n-1` of a block `M`, from the state `sB` at its start. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n))
  x1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad M k
  x7 : s.xmm .xmm7 = sB.xmm .xmm7
  gpr : s.gpr = sB.gpr
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_ok (H : HashValue) (M : Block) (bp : BitVec 32) (sB : State)
    (hecx : sB.gpr .ecx = bp) (hfit : bp.toNat + 64 ≤ 2 ^ 32) (hmask : sB.xmm .xmm7 = bswapMask)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (addr bp (16 * n)) 16)
    (hblk : ∀ t : Nat, t < 16 → bswap (sB.mem.readW (addr bp (4 * t)) 32) = W M t)
    (h0 : sB.xmm .xmm0 = abcd H) (h1 : sB.xmm .xmm1 = eReg H) :
    ∀ n ≤ 20, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h0, by simp only [ECarry, ite_true]; exact h1,
      fun _ h => absurd h (by omega_using []), rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_using [hn])) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_ecx : s.gpr .ecx = bp := by rw [hs.gpr, hecx]
    -- The schedule: `msg n` gets `quad M n`; nothing else changes.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad M n ∧ (∀ r, r ≠ msg n → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_ecx]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        rw [e, hs_ecx, hs.mem, hs.x7, hmask]
        exact load_quad M sB.mem bp hfit hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega_using [hlo]⟩
        refine WP.mono (schedule_hi (i + 4) (by omega_using []) s (quad M i) (quad M (i + 1)) (quad M (i + 2))
          (quad M (i + 3)) ?_ ?_ ?_ ?_) fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [msg_add4]; exact hs.msgs i (by omega_using []) (by omega_using [])
        · rw [show i + 4 + 1 = i + 1 + 4 by omega_using [], msg_add4]; exact hs.msgs (i + 1) (by omega_using []) (by omega_using [])
        · rw [show i + 4 + 2 = i + 2 + 4 by omega_using [], msg_add4]; exact hs.msgs (i + 2) (by omega_using []) (by omega_using [])
        · rw [show i + 4 + 3 = i + 3 + 4 by omega_using [], msg_add4]; exact hs.msgs (i + 3) (by omega_using []) (by omega_using [])
        · rw [e]; exact schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o0 := msg_other n .xmm0 (.inl rfl)
    have o1 := msg_other n .xmm1 (.inr (.inl rfl))
    have o7 := msg_other n .xmm7 (.inr (.inr (.inr rfl)))
    refine WP.mono (rounds4_step H M (n := n) (by omega_using [hn]) s₁ (by rw [hx₁ _ (Ne.symm o0)]; exact hs.x0)
      (by rw [hx₁ _ (Ne.symm o1)]; exact hs.x1) hq)
      fun s₂ ⟨e0, e1, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e0, e1, fun k hk hk' => ?_, ?_, by rw [hg₂, hg₁, hs.gpr], by rw [hm₂, hm₁, hs.mem],
      by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · rw [hx₂ _ (msg_other k _ (.inl rfl)) (msg_other k _ (.inr (.inl rfl)))
        (msg_other k _ (.inr (.inr (.inl rfl))))]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega_using [hk, hkn]) (by omega_using [hk']))]
        exact hs.msgs k (by omega_using [hk, hkn]) (by omega_using [hk'])
    · rw [hx₂ _ (by decide) (by decide) (by decide), hx₁ _ (Ne.symm o7)]
      exact hs.x7

end VG.Proof.Sha1.X86.ShaNi

end

end

/-!
# SHA-1 compression function on x86 with the SHA extensions

`compress_verified` proves `Impl.Sha1.X86.ShaNi.compress` against the same
contract as the scalar `vg_sha1_compress` (`Proof.Sha1.compressX86`),
reusing its precondition (`Pre`), its block lemmas and its initial taint: the
rounds are those of `Rounds.lean`; around them, the hash value is loaded and
stored, and the working variables at the start of each block are kept in
`scratch[0..32)` and added back at its end.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.ShaNi

open VG VG.X86 VG.Impl.Sha1.X86.ShaNi
open VG.Proof.Sha1.X86 (Pre pre_of st bp nb scr esp₀ stR blR scrR retR H₀ blkAddr blk
  blk_word compressBlocks_succ contains_sub st_eq harg_of)
open VG.Proof.Sha256.X86.ShaNi (movd_value shift_last_value or_last_value)
open VG.Spec.Sha1 (HashValue Word Block W stateAt compressBlocks compress)

/-! ## Loading and storing the hash value -/

theorem const_ok (c : BitVec 128) (s : State) :
    WP isa (.block (const c)) s fun s' =>
      s'.xmm .xmm7 = c ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ldq : ∀ a b, XBinOp.eval .punpckldq a b =
      ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := fun _ _ => rfl
  apply WP.of_runBlock
  simp only [Nat.reduceAdd, and_self, const, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, XOp.exec, isa, movd_value, ldq,
    dword_ofDwords_0, dword_ofDwords_1, punpcklqdq_eq,
    shift_last_value,
    RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h7 h2 => ?_, fun r hr => ?_, trivial⟩
  · exact (or_last_value _ _ _ _).trans (ofDwords_dword c)
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_of_ne, h7, h2, not_false_eq_true]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem loadState_ok (s : State) (p : BitVec 32)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p)
    (h0 : InRegions (s.rd ++ s.wr) (addr p 0) 16) (h4 : InRegions (s.rd ++ s.wr) (addr p 4) 16) :
    WP isa (.block loadState) s fun s' =>
      s'.xmm .xmm0 = shufDwords (s.mem.readW (addr p 0) 128) 0x1b ∧
      s'.xmm .xmm1 = XShiftOp.eval .pslldq (XShiftOp.eval .psrldq (s.mem.readW (addr p 4) 128) 12) 12 ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [loadState, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, XOp.exec, isa,
    State.load32, State.load128, ea_at, harg, hv, ite_true, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, h0, h4,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem loadArgs_ok (s : State)
    (h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (h16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) :
    WP isa (.block loadArgs) s fun s' =>
      s'.gpr .ecx = s.mem.readW (addr (s.gpr .esp) 8) 32 ∧
      s'.gpr .edx = s.mem.readW (addr (s.gpr .esp) 16) 32 ∧
      s'.gpr .eax = s.mem.readW (addr (s.gpr .esp) 12) 32 ∧
      s'.zf = some (s.mem.readW (addr (s.gpr .esp) 12) 32 &&& s.mem.readW (addr (s.gpr .esp) 12) 32 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.xmm = s.xmm ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [loadArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, isa,
    State.load32, ea_at, RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, h8, h12, h16,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.xmm_setReg,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r ha hc hd => ?_, trivial, trivial, trivial, trivial⟩
  simp only [ha, hc, hd, ↓reduceIte]

theorem stateAt_lo (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) {j : Nat} (hj : j < 4) :
    dword (m.readW (addr p 0) 128) j = (stateAt m (p.setWidth 64))[j] := by
  rw [addr_eq (by omega_arith), dword_readW _ _ hj]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [Offset.add_ofNat_add_ofNat, Nat.zero_add]

theorem stateAt_e (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) :
    dword (m.readW (addr p 4) 128) 3 = (stateAt m (p.setWidth 64))[4] := by
  rw [addr_eq (by omega_arith), dword_readW _ _ (by decide)]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [Offset.add_ofNat_add_ofNat]

theorem getLsbD_zero32 (i : Nat) : (0 : Word).getLsbD i = false := by simp

theorem shift_e (x : BitVec 128) :
    XShiftOp.eval .pslldq (XShiftOp.eval .psrldq x 12) 12 = ofDwords 0 0 0 (dword x 3) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : min (12 : BitVec 8).toNat 16 * 8 = 96 := rfl
  simp only [XShiftOp.eval, e, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_dword]
  rcases (by omega_arith : i < 96 ∨ 96 ≤ i) with h | h
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, getLsbD_zero32]
    rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96)) with h' | h' | h' <;>
    simp (disch := omega_arith) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega_arith) only [hi, show ¬ i < 96 by omega_arith, show ¬ i < 32 by omega_arith,
      show ¬ i - 32 < 32 by omega_arith, show ¬ i - 32 - 32 < 32 by omega_arith, show i - 32 - 32 - 32 = i - 96 by omega_arith,
      show i - 96 < 32 by omega_arith, decide_true, decide_false, Bool.not_false, Bool.true_and, ite_false]

/-- `B, C, D, E` from `A, B, C, D` and `E`. -/
theorem por_e (a b c d e : Word) :
    XBinOp.eval .por (XShiftOp.eval .psrldq (ofDwords a b c d) 4) (ofDwords 0 0 0 e) = ofDwords b c d e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e32 : min (4 : BitVec 8).toNat 16 * 8 = 32 := rfl
  simp only [XBinOp.eval, XShiftOp.eval, e32, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_zero32]
  rcases (by omega_arith : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega_arith) only [ite_eq_left, ite_eq_right, Bool.or_false]
  · exact congrArg _ (by omega_arith)
  · exact congrArg _ (by omega_arith)
  · exact congrArg _ (by omega_arith)
  · rw [BitVec.getLsbD_of_ge d _ (by omega_arith), Bool.false_or]

theorem shufDwords_1b (a : BitVec 128) :
    shufDwords a 0x1b = ofDwords (dword a 3) (dword a 2) (dword a 1) (dword a 0) := rfl

/-- The hash value as the loaded registers hold it. -/
theorem loaded_eq (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) :
    shufDwords (m.readW (addr p 0) 128) 0x1b = abcd (stateAt m (p.setWidth 64)) ∧
    XShiftOp.eval .pslldq (XShiftOp.eval .psrldq (m.readW (addr p 4) 128) 12) 12 =
      eReg (stateAt m (p.setWidth 64)) := by
  refine ⟨?_, ?_⟩
  · rw [shufDwords_1b, stateAt_lo _ hfit (show 0 < 4 by decide), stateAt_lo _ hfit (show 1 < 4 by decide),
      stateAt_lo _ hfit (show 2 < 4 by decide), stateAt_lo _ hfit (show 3 < 4 by decide)]
    rfl
  · rw [shift_e, stateAt_e _ hfit]; rfl

/-- The hash value after storing `x` at `p + 4` and `y` at `p`. -/
theorem stateAt_store (m : Mem) {p : BitVec 32} (hfit : p.toNat + 20 ≤ 2 ^ 32) (x y : BitVec 128) :
    stateAt ((m.writeW (addr p 4) x).writeW (addr p 0) y) (p.setWidth 64) =
      #v[dword y 0, dword y 1, dword y 2, dword y 3, dword x 3] := by
  rw [addr_eq (k := 4) (by omega_arith), addr_eq (k := 0) (by omega_arith)]
  generalize p.setWidth 64 = P
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  by_cases hlo : j < 4
  · rw [show P + BitVec.ofNat 64 (4 * j) = P + BitVec.ofNat 64 0 + BitVec.ofNat 64 (4 * j) by
      rw [Offset.add_ofNat_add_ofNat, Nat.zero_add],
      readW_writeW128 _ _ _ hlo]
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · obtain rfl : j = 4 := by omega_arith
    rw [Mem.readW_writeW_sep (Offset.sep P (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      show P + BitVec.ofNat 64 (4 * 4) = P + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * 3) by
        rw [Offset.add_ofNat_add_ofNat],
      readW_writeW128 _ _ _ (by omega_arith)]
    rfl

/-- `ABCD` and `E`, stored back as the hash value. -/
theorem store_ok (s : State) (p : BitVec 32) (v : HashValue)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p) (hfit : p.toNat + 20 ≤ 2 ^ 32)
    (h0 : InRegions s.wr (addr p 0) 16) (h4 : InRegions s.wr (addr p 4) 16)
    (x0 : s.xmm .xmm0 = abcd v) (x1 : s.xmm .xmm1 = eReg v) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW (addr p 4) x).writeW (addr p 0) y) ∧
      stateAt s'.mem (p.setWidth 64) = v ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [store, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, XOp.exec, isa,
    State.load32, State.store128, ea_at, harg, hv, ite_true, RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg, h0, h4,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, x0, x1, eval_movdqa,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, fun r hr => ?_, trivial, trivial⟩
  · rw [stateAt_store _ hfit]
    simp only [shufDwords_1b, abcd, eReg, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, por_e]
    apply Vector.ext
    intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

/-! ## A block -/

theorem save_ok (s : State)
    (h0 : InRegions s.wr (addr (s.gpr .edx) 0) 16) (h16 : InRegions s.wr (addr (s.gpr .edx) 16) 16) :
    WP isa (.block save) s fun s' =>
      s'.mem = (s.mem.writeW (addr (s.gpr .edx) 0) (s.xmm .xmm0)).writeW
        (addr (s.gpr .edx) 16) (s.xmm .xmm1) ∧
      s'.xmm = s.xmm ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128,
    ea_at, h0, h16, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem finish_ok (s : State) (H : HashValue) (M : Block)
    (h0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * 20)))
    (h1 : (dword (s.xmm .xmm1) 3).rotateLeft 30 = (Spec.Sha1.rounds H M (4 * 20))[4])
    (i0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) 0) 16)
    (i16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) 16) 16)
    (v0 : s.mem.readW (addr (s.gpr .edx) 0) 128 = abcd H)
    (v16 : s.mem.readW (addr (s.gpr .edx) 16) 128 = eReg H) :
    WP isa (.block finish) s fun s' =>
      s'.xmm .xmm0 = abcd (compress H M) ∧ s'.xmm .xmm1 = eReg (compress H M) ∧
      s'.xmm .xmm7 = s.xmm .xmm7 ∧
      s'.gpr .ecx = s.gpr .ecx + 64 ∧ s'.gpr .eax = s.gpr .eax - 1 ∧
      (∀ r, r ≠ .ecx → r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [finish, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, execAlu, readSrc, isa, State.load128, ea_at, i0, i16, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, h0, v0, v16, paddd_abcd, nexte_eReg _ _ _ h1,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, trivial, trivial, trivial, fun r hc ha => ?_, trivial, trivial, trivial, trivial⟩
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne, hc, ha, not_false_eq_true,
    RegUpd.gpr_setXmm]

/-! ## The loop over the blocks -/

theorem Pre.blk_fit {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have hb := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 64 * i < 2 ^ 32 by omega_arith),
    Nat.mod_eq_of_lt (show (bp s₀).toNat + 64 * i < 2 ^ 32 by omega_arith)]
  omega_arith

theorem Pre.blk_vec {s₀ : State} (hp : Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (16 * n)) 16 := by
  have he : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    simpa only [blkAddr, addr] using addr_eq (x := bp s₀) (k := 64 * i)
      (by have := hp.blk_fits; omega_arith)
  refine ⟨blR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], ?_⟩
  rw [addr_eq (by have := Pre.blk_fit hp hi; omega_arith), he, Offset.add_add]
  exact Offset.contains_base _ (by omega_arith) (by have := hp.blk_fits; omega_arith)

theorem Pre.scr_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 112) :
    InRegions s₀.wr (addr (scr s₀) d) 16 :=
  ⟨scrR s₀, by simp [hp.wr], contains_sub hd (by omega_arith) (hp.scr_eq (by omega_arith))⟩

theorem Pre.st_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 20) :
    InRegions s₀.wr (addr (st s₀) d) 16 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega_arith) (st_eq hp (by omega_arith))⟩

theorem in_read_of_write {rd wr : List Region} {p : Addr} {n : Nat}
    (h : InRegions wr p n) : InRegions (rd ++ wr) p n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append.mpr (.inr hr), hc⟩

/-- Writing 16 bytes at `scratch + d`. -/
theorem scr_write {s₀ : State} (hp : Pre s₀) (m : Mem) (v : BitVec 128) {d : Nat} (hd : d + 16 ≤ 112) :
    Frame [scrR s₀] m (m.writeW (addr (scr s₀) d) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v
    (contains_sub hd (by omega_arith) (hp.scr_eq (by omega_arith)))

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  x1 : s.xmm .xmm1 = eReg (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  edx : s.gpr .edx = scr s₀
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x7 : s.xmm .xmm7 = bswapMask
  ecx : s.gpr .ecx = blkAddr s₀ i
  eax : s.gpr .eax = BitVec.ofNat 32 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have vecwr : ∀ d : Nat, d + 16 ≤ 112 → InRegions s.wr (addr (s.gpr .edx) d) 16 := by
    intro d hd; rw [hL.wr, hL.edx]; exact Pre.scr_vec hp hd
  refine WP.seq (WP.mono (save_ok s (vecwr 0 (by decide)) (vecwr 16 (by decide)))
    fun s₁ ⟨hm₁, hx₁, hg₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [scrR s₀] s₀.mem s₁.mem := by
    rw [hm₁, hL.edx]
    exact (hL.frame.trans (scr_write hp _ _ (by decide))).trans (scr_write hp _ _ (by decide))
  have v0 : s₁.mem.readW (addr (scr s₀) 0) 128 = abcd (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) := by
    rw [hm₁, hL.edx, hp.scr_eq (by decide), hp.scr_eq (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      Mem.readW_writeW_self _ _ 16 _ (by decide), hL.x0]
  have v16 : s₁.mem.readW (addr (scr s₀) 16) 128 = eReg (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) := by
    rw [hm₁, hL.edx, Mem.readW_writeW_self _ _ 16 _ (by decide), hL.x1]
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.ecx])
    (Pre.blk_fit hp hi) (by rw [hx₁, hL.x7])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.blk_vec hp hi hn)
    (fun t ht => by
      rw [hf₁.readW (hp.blk_contains hi ht) (by simpa using hp.blk_scr) (by decide)]
      exact blk_word hp hi ht)
    (by rw [hx₁, hL.x0]) (by rw [hx₁, hL.x1]) 20 (Nat.le_refl _)) fun s₂ hR => ?_)
  have hedx₂ : s₂.gpr .edx = scr s₀ := by rw [hR.gpr, hg₁, hL.edx]
  have hx1 : (dword (s₂.xmm .xmm1) 3).rotateLeft 30 =
      (Spec.Sha1.rounds (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i) (blk s₀ i) (4 * 20))[4] := by
    have := hR.x1; simpa only [ECarry, Nat.reduceMul, Nat.reduceEqDiff, ite_false] using this
  have rw₂ : ∀ d : Nat, d + 16 ≤ 112 → InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .edx) d) 16 := by
    intro d hd
    rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hedx₂]
    exact in_read_of_write (Pre.scr_vec hp hd)
  refine WP.mono (finish_ok s₂ _ _ hR.x0 hx1 (rw₂ 0 (by decide)) (rw₂ 16 (by decide))
    (by rw [hedx₂, hR.mem, v0]) (by rw [hedx₂, hR.mem, v16]))
    fun s₃ ⟨f0, f1, f7, fecx, feax, fg, fzf, fm, frd, fwr⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [hR.gpr, hg₁]
  have heax : s₂.gpr .eax - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [g₂, hL.eax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      Nat.sub_sub]
  have hcommon : Common s₀ (i + 1) s₃ :=
    ⟨by rw [f0, compressBlocks_succ], by rw [f1, compressBlocks_succ],
      by rw [fg _ (by decide) (by decide), hedx₂],
      fun r ha hc hd => by rw [fg r hc ha, g₂, hL.gpr r ha hc hd],
      by rw [frd, hR.rd, hrd₁, hL.rd], by rw [fwr, hR.wr, hwr₁, hL.wr], by rw [fm, hR.mem]; exact hf₁⟩
  have hev : eval .ne s₃ = some (!(s₂.gpr .eax - 1 == 0)) := by
    simp only [eval, fzf, Option.map_some]
  rw [heax] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega_arith
    refine ⟨?_, by omega_arith, { hcommon with x7 := ?_, ecx := ?_, eax := ?_ }⟩
    · rw [hev]
      have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        have hn : nb s₀ < 2 ^ 32 := (VG.X86.arg s₀ 2).isLt
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)] at h'
        exact hne h'
      simpa using h0
    · rw [f7, hR.x7, hx₁, hL.x7]
    · rw [fecx, g₂, hL.ecx, blkAddr, blkAddr, BitVec.add_assoc]
      rw [show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
      exact congrArg (fun n => bp s₀ + BitVec.ofNat 32 n) (by omega_arith)
    · rw [feax, heax]

theorem loop_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State}
    (hL : LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (Common s₀ (nb s₀)) := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
  have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hL⟩
    refine WP.mono (body_ok hp hi hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega_arith, i + 1, rfl, hi', hL'⟩
  exact WP.loop (M := isa) Inv hstep (nb s₀) s ⟨0, rfl, hpos, hL⟩

/-! ## The whole function -/

theorem load_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block load) s₀ fun s' => LInv s₀ 0 s' ∧ s'.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have shape : load = loadState ++ (const bswapMask ++ loadArgs) := by
    simp only [load, List.append_assoc]
  rw [shape, WP.block_append_iff]
  have hst := hp.st_fits
  refine WP.mono (loadState_ok s₀ (st s₀) (hp.in_arg (by decide) (by decide)) rfl
    (in_read_of_write (Pre.st_vec hp (by decide))) (in_read_of_write (Pre.st_vec hp (by decide))))
    fun s₁ ⟨x0, x1, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok bswapMask s₁) fun s₂ ⟨x7, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
  have esp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [hg₂ _ (by decide), hg₁ _ (by decide)]
  have rd₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [hrd₂, hwr₂, hrd₁, hwr₁]
  refine WP.mono (loadArgs_ok s₂ (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide))
    (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide))
    (by rw [esp₂, rd₂]; exact hp.in_arg (by decide) (by decide)))
    fun s₃ ⟨ecx, edx, eax, zf, hg₃, hx₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have m₂ : s₂.mem = s₀.mem := by rw [hm₂, hm₁]
  have a1 : s₂.mem.readW (addr (s₂.gpr .esp) 8) 32 = bp s₀ := by rw [esp₂, m₂]; rfl
  have a2 : s₂.mem.readW (addr (s₂.gpr .esp) 12) 32 = arg s₀ 2 := by rw [esp₂, m₂]; rfl
  have a3 : s₂.mem.readW (addr (s₂.gpr .esp) 16) 32 = scr s₀ := by rw [esp₂, m₂]; rfl
  have lv := loaded_eq s₀.mem hst
  have hc : Common s₀ 0 s₃ :=
    ⟨by rw [hx₃, hx₂ _ (by decide) (by decide), x0, lv.1]; rfl,
      by rw [hx₃, hx₂ _ (by decide) (by decide), x1, lv.2]; rfl,
      by rw [edx, a3],
      fun r ha hc hd => by rw [hg₃ r ha hc hd, hg₂ r ha, hg₁ r hd],
      by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], by rw [hm₃, m₂]; exact Frame.refl _ _⟩
  refine ⟨{ hc with x7 := ?_, ecx := ?_, eax := ?_ }, ?_⟩
  · rw [hx₃, x7]
  · rw [ecx, a1]; simp [blkAddr]
  · rw [eax, a2]; simp [nb]
  · rw [zf, a2]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (load_ok hp) fun s₁ ⟨hL₀, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp only [eval, hzf]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hL₀.toCommon)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      exact loop_ok hp hpos hL₀
  · have hst := hp.st_fits
    have hesp : s₂.gpr .esp = esp₀ s₀ := hc.gpr .esp (by decide) (by decide) (by decide)
    have hf : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
      hc.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
    refine WP.mono (store_ok s₂ (st s₀) _
      (by rw [hesp, hc.rd, hc.wr]; exact hp.in_arg (by decide) (by decide))
      (by rw [hesp]; exact harg_of hp hf) hst
      (by rw [hc.wr]; exact Pre.st_vec hp (by decide)) (by rw [hc.wr]; exact Pre.st_vec hp (by decide))
      hc.x0 hc.x1)
      fun s' ⟨⟨x, y, hm'⟩, hstate, hg', _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hstate⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hne : r ≠ .edx ∧ r ≠ .eax ∧ r ≠ .ecx := by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hg' r hne.1, hc.gpr r hne.2.1 hne.2.2 hne.1]
    · have c : ∀ d : Nat, d + 16 ≤ 20 → (stR s₀).Contains (addr (st s₀) d) (128 / 8) :=
        fun d hd => contains_sub hd (by omega_arith) (st_eq hp (by omega_arith))
      have m := List.mem_cons_self (a := stR s₀) (l := [scrR s₀])
      have hf' : Frame [stR s₀, scrR s₀] s₀.mem s'.mem := by
        rw [hm']; exact (hf.writeW m x (c 4 (by decide))).writeW m y (c 0 (by decide))
      exact hf'.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)

theorem compress_verified :
    Verified X86.target Impl.Sha1.X86.ShaNi.compress Proof.Sha1.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) Proof.Sha1.X86.τ₀
      (fun _ _ h₁ h₂ hpub => Proof.Sha1.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨Proof.Sha1.X86.satState, Proof.Sha1.X86.sat_pre⟩⟩

theorem compress_nosp : NoSp Impl.Sha1.X86.ShaNi.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Sha1.X86.ShaNi.compress = 0 := by lit_decide

end VG.Proof.Sha1.X86.ShaNi
