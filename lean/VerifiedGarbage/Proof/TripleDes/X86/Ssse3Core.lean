module

public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Round
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.TripleDes.X86.WordStore

/-!
# Triple DES's core by `pshufb` on x86 (32-bit): what the code does

`ssse3CoreSpec`: the core of `Impl/TripleDes/X86/Ssse3.lean` meets what the
modes need of a core (`Proof.Modes.X86.CoreSpec`), with the key a schedule,
read through the first stack argument, and its cipher
`Spec.TripleDes.cipher`; and it fits Triple DES's functions (`ssse3Fits`,
`Mode.Fits`), whose lemmas (`Proof/TripleDes/X86/FbVerified.lean`,
`CbcVerified.lean`, `FbFinalVerified.lean`) then hold of the modes over it.

* A round (`round_wp`), run an instruction at a time in four pieces (the
  expansion and the key, the look-ups, the masks and the fold, P), from a
  state given by its XMM registers, leaves in `xmm7` what
  `Ssse3Round.lean` says of it (`roundX`), and the input half in its slot;
  so with the rounds' keys in the buffer (`Keys`) it is a round of DES on
  the halves rotated right by one (`round_step`, by `round_ok`).
* Two rounds and the count (`double_wp`), eight times a pass (`pass_wp`:
  DES's sixteen rounds under a key's schedule, the second key's in reverse,
  `pass_eq`), three passes with the halves exchanged between them
  (`rounds_wp`).
* The block's two ends (`head_wp`, `tail_wp`): the initial and the final
  permutation in the general registers (`ip_wp`, `fp_wp`), and the halves to
  and from their rotated form; `crypt_wp`: the block of the buffer is
  enciphered in place, as `Spec.TripleDes.encryptBlock` does.
* The keys (`key_wp`: a round key of the schedule to the two words the
  rounds read; `prepBody_wp`: a round's keys of the three passes), and
  `prepare_wp`: the table's address to the buffer's first slot, taken with
  `symPush` in the four bytes below `esp`, and the 48 rounds' keys in the
  order of use (`Ready`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Ssse3

open VG VG.X86
open VG.Impl.TripleDes.X86.Ssse3
open VG.Impl.Modes.X86 (sb at_ argOp)

/-! ## Straight-line XMM code -/

variable {s : State}

/-- An instruction that writes an XMM register, from a state given by its XMM registers. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i { s with xmm := f } = some (State.setXmm { s with xmm := f } d v))
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then v else f r } Q) :
    WP isa (.block (i :: is)) { s with xmm := f } Q := Wp.cons h k

/-- A constant of the table. -/
theorem wp_tb {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {off : Nat}
    (hb : s.gpr tbr = s.syms tableName) (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ table.length)
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then cst off else f r } Q) :
    WP isa (.block (tb d off :: is)) { s with xmm := f } Q :=
  Wp.cons (show (if s.gpr tbr = s.syms tableName ∧ off % 8 = 0 ∧ off / 8 + 2 ≤ table.length then some _ else none) = _ by
    rw [ite_eq_left (show _ ∧ _ ∧ _ from ⟨hb, ho.1, ho.2⟩)]; rfl) k

/-- A 16-byte load. -/
theorem wp_ld {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then s.mem.readW a 128 else f r } Q) :
    WP isa (.block (.movdquLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load128 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load128, ite_eq_left hin]; rfl) k

/-- A 16-byte store. -/
theorem wp_st {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {r : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions s.wr a 16)
    (k : WP isa (.block is) { ({ s with mem := s.mem.writeW a (f r) } : State) with xmm := f } Q) :
    WP isa (.block (.movdquStore m r :: is)) { s with xmm := f } Q :=
  Wp.cons (show State.store128 { s with xmm := f } (s.ea m) (f r) = _ by
    rw [ha, State.store128, ite_eq_left hin]) k

/-- An 8-byte load. -/
theorem wp_lq {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : WP isa (.block is)
      { s with xmm := fun r => if r = d then (0 : BitVec 64) ++ s.mem.readW a 64 else f r } Q) :
    WP isa (.block (.movqLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load64 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load64, ite_eq_left hin]; rfl) k

/-! ## A round, in four pieces -/

/-- The input half to its slot, its expansion, the key and the index step. -/
def pE (sin koff : Nat) : List Instr :=
  [stx sb sin .xmm7, .xop (.pshufd .xmm0 .xmm7 0), sh .psrld .xmm7 2,
   sh .psrlq .xmm0 30, x .punpckldq .xmm7 .xmm0, tb .xmm6 (oM),
   x .pand .xmm7 .xmm6, .movqLoad .xmm6 (at_ kr koff), x .pxor .xmm7 .xmm6,
   tb .xmm6 (oStep)]

/-- The sixteen look-ups. -/
def pL : List Instr :=
  [tb .xmm2 (oT 0 0), x .pshufb .xmm2 .xmm7, tb .xmm3 (oT 1 0),
   x .pshufb .xmm3 .xmm7, tb .xmm1 (oT 2 0), x .pshufb .xmm1 .xmm7,
   tb .xmm4 (oT 3 0), x .pshufb .xmm4 .xmm7, x .paddd .xmm7 .xmm6,
   tb .xmm5 (oT 0 1), x .pshufb .xmm5 .xmm7, x .pxor .xmm5 .xmm2,
   tb .xmm0 (oT 1 1), x .pshufb .xmm0 .xmm7, x .pxor .xmm0 .xmm3,
   tb .xmm2 (oT 2 1), x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm1,
   tb .xmm1 (oT 3 1), x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm4,
   x .paddd .xmm7 .xmm6, tb .xmm3 (oT 0 2), x .pshufb .xmm3 .xmm7,
   x .pxor .xmm5 .xmm3, tb .xmm4 (oT 1 2), x .pshufb .xmm4 .xmm7,
   x .pxor .xmm0 .xmm4, tb .xmm3 (oT 2 2), x .pshufb .xmm3 .xmm7,
   x .pxor .xmm3 .xmm2, tb .xmm4 (oT 3 2), x .pshufb .xmm4 .xmm7,
   x .pxor .xmm4 .xmm1, x .paddd .xmm7 .xmm6, tb .xmm1 (oT 0 3),
   x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm5, tb .xmm2 (oT 1 3),
   x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm0, tb .xmm0 (oT 2 3),
   x .pshufb .xmm0 .xmm7, x .pxor .xmm3 .xmm0, tb .xmm5 (oT 3 3),
   x .pshufb .xmm5 .xmm7, x .pxor .xmm4 .xmm5]

/-- The pairs' masks, the sum and its fold. -/
def pF : List Instr :=
  [tb .xmm6 (oMask 0), x .pand .xmm1 .xmm6, tb .xmm6 (oMask 1),
   x .pand .xmm2 .xmm6, tb .xmm6 (oMask 2), x .pand .xmm3 .xmm6,
   tb .xmm6 (oMask 3), x .pand .xmm4 .xmm6, x .pxor .xmm1 .xmm2,
   x .pxor .xmm3 .xmm4, x .pxor .xmm1 .xmm3, .xop (.pshufd .xmm0 .xmm1 0xe1),
   x .pxor .xmm0 .xmm1]

/-- P, and the target. -/
def pP (stgt : Nat) : List Instr :=
  [x .movdqa .xmm5 .xmm0, sh .psrlq .xmm5 7, tb .xmm6 (oP 0),
   x .pand .xmm5 .xmm6, x .movdqa .xmm2 .xmm0, sh .psrlq .xmm2 15,
   tb .xmm6 (oP 1), x .pand .xmm2 .xmm6, x .pxor .xmm5 .xmm2,
   x .movdqa .xmm4 .xmm0, sh .psrlq .xmm4 16, tb .xmm6 (oP 2),
   x .pand .xmm4 .xmm6, x .movdqa .xmm3 .xmm0, sh .psrlq .xmm3 23,
   tb .xmm6 (oP 3), x .pand .xmm3 .xmm6, x .pxor .xmm4 .xmm3,
   x .pxor .xmm5 .xmm4, x .movdqa .xmm1 .xmm0, sh .psrlq .xmm1 27,
   tb .xmm6 (oP 4), x .pand .xmm1 .xmm6, sh .psrlq .xmm0 30,
   tb .xmm6 (oP 5), x .pand .xmm0 .xmm6, x .pxor .xmm1 .xmm0,
   ld .xmm7 sb stgt, x .pxor .xmm7 .xmm1, x .pxor .xmm7 .xmm5]

theorem round_eq (sin stgt koff : Nat) : round sin stgt koff = pE sin koff ++ (pL ++ (pF ++ pP stgt)) := rfl

theorem pE_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {sin koff : Nat} {sa ka : Addr}
    (hsa : s.ea (at_ sb sin) = sa) (hka : s.ea (at_ kr koff) = ka) (hb : s.gpr tbr = s.syms tableName)
    (hws : InRegions s.wr sa 16) (hrk : InRegions (s.rd ++ s.wr) ka 8)
    (k : ∀ g : XReg → BitVec 128,
      g .xmm7 = idxX (f .xmm7) ((0 : BitVec 64) ++ (s.mem.writeW sa (f .xmm7)).readW ka 64) → g .xmm6 = cst oStep →
      WP isa (.block is) { ({ s with mem := s.mem.writeW sa (f .xmm7) } : State) with xmm := g } Q) :
    WP isa (.block (pE sin koff ++ is)) { s with xmm := f } Q := by
  refine wp_st hsa hws (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_lq hka hrk (
    wp_xs rfl (wp_tb hb (by decide) (k _ rfl rfl))))))))))
/-- The look-ups of the index as it is. -/
def pL0 : List Instr :=
  [tb .xmm2 (oT 0 0), x .pshufb .xmm2 .xmm7, tb .xmm3 (oT 1 0),
   x .pshufb .xmm3 .xmm7, tb .xmm1 (oT 2 0), x .pshufb .xmm1 .xmm7,
   tb .xmm4 (oT 3 0), x .pshufb .xmm4 .xmm7, x .paddd .xmm7 .xmm6]

/-- The look-ups of the index a step on. -/
def pL1 : List Instr :=
  [tb .xmm5 (oT 0 1), x .pshufb .xmm5 .xmm7, x .pxor .xmm5 .xmm2,
   tb .xmm0 (oT 1 1), x .pshufb .xmm0 .xmm7, x .pxor .xmm0 .xmm3,
   tb .xmm2 (oT 2 1), x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm1,
   tb .xmm1 (oT 3 1), x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm4,
   x .paddd .xmm7 .xmm6]

/-- The look-ups of the index two steps on. -/
def pL2 : List Instr :=
  [tb .xmm3 (oT 0 2), x .pshufb .xmm3 .xmm7, x .pxor .xmm5 .xmm3,
   tb .xmm4 (oT 1 2), x .pshufb .xmm4 .xmm7, x .pxor .xmm0 .xmm4,
   tb .xmm3 (oT 2 2), x .pshufb .xmm3 .xmm7, x .pxor .xmm3 .xmm2,
   tb .xmm4 (oT 3 2), x .pshufb .xmm4 .xmm7, x .pxor .xmm4 .xmm1,
   x .paddd .xmm7 .xmm6]

/-- The look-ups of the index three steps on. -/
def pL3 : List Instr :=
  [tb .xmm1 (oT 0 3), x .pshufb .xmm1 .xmm7, x .pxor .xmm1 .xmm5,
   tb .xmm2 (oT 1 3), x .pshufb .xmm2 .xmm7, x .pxor .xmm2 .xmm0,
   tb .xmm0 (oT 2 3), x .pshufb .xmm0 .xmm7, x .pxor .xmm3 .xmm0,
   tb .xmm5 (oT 3 3), x .pshufb .xmm5 .xmm7, x .pxor .xmm4 .xmm5]

theorem pL_eq : pL = pL0 ++ (pL1 ++ (pL2 ++ pL3)) := rfl

theorem pL0_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128, g .xmm2 = lkX 0 0 (f .xmm7) →
      g .xmm3 = lkX 1 0 (f .xmm7) →
      g .xmm1 = lkX 2 0 (f .xmm7) →
      g .xmm4 = lkX 3 0 (f .xmm7) →
      g .xmm7 = stepC (f .xmm6) (f .xmm7) →
      g .xmm6 = f .xmm6 →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pL0 ++ is)) { s with xmm := f } Q := by
  refine wp_tb hb (by decide) (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (k _ rfl rfl rfl rfl rfl rfl)))))))))

theorem pL1_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128, g .xmm5 = lkX 0 1 (f .xmm7) ^^^ f .xmm2 →
      g .xmm0 = lkX 1 1 (f .xmm7) ^^^ f .xmm3 →
      g .xmm2 = lkX 2 1 (f .xmm7) ^^^ f .xmm1 →
      g .xmm1 = lkX 3 1 (f .xmm7) ^^^ f .xmm4 →
      g .xmm7 = stepC (f .xmm6) (f .xmm7) →
      g .xmm6 = f .xmm6 →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pL1 ++ is)) { s with xmm := f } Q := by
  refine wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ rfl rfl rfl rfl rfl rfl)))))))))))))

theorem pL2_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128, g .xmm5 = f .xmm5 ^^^ lkX 0 2 (f .xmm7) →
      g .xmm0 = f .xmm0 ^^^ lkX 1 2 (f .xmm7) →
      g .xmm3 = lkX 2 2 (f .xmm7) ^^^ f .xmm2 →
      g .xmm4 = lkX 3 2 (f .xmm7) ^^^ f .xmm1 →
      g .xmm7 = stepC (f .xmm6) (f .xmm7) →
      g .xmm6 = f .xmm6 →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pL2 ++ is)) { s with xmm := f } Q := by
  refine wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ rfl rfl rfl rfl rfl rfl)))))))))))))

theorem pL3_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128, g .xmm1 = lkX 0 3 (f .xmm7) ^^^ f .xmm5 →
      g .xmm2 = lkX 1 3 (f .xmm7) ^^^ f .xmm0 →
      g .xmm3 = f .xmm3 ^^^ lkX 2 3 (f .xmm7) →
      g .xmm4 = f .xmm4 ^^^ lkX 3 3 (f .xmm7) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pL3 ++ is)) { s with xmm := f } Q := by
  refine wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (k _ rfl rfl rfl rfl))))))))))))

theorem pL_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128, g .xmm1 = yA 0 (f .xmm6) (f .xmm7) → g .xmm2 = yA 1 (f .xmm6) (f .xmm7) →
      g .xmm3 = yB 2 (f .xmm6) (f .xmm7) → g .xmm4 = yB 3 (f .xmm6) (f .xmm7) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pL ++ is)) { s with xmm := f } Q := by
  rw [pL_eq, List.append_assoc, List.append_assoc, List.append_assoc]
  refine pL0_wp hb fun g₀ a2 a3 a1 a4 a7 a6 => ?_
  refine pL1_wp hb fun g₁ b5 b0 b2 b1 b7 b6 => ?_
  refine pL2_wp hb fun g₂ c5 c0 c3 c4 c7 c6 => ?_
  refine pL3_wp hb fun g₃ d1 d2 d3 d4 => k g₃ ?_ ?_ ?_ ?_
  · rw [d1, c5, c7, b5, b7, b6, a2, a7, a6, yA]
  · rw [d2, c0, c7, b0, b7, b6, a3, a7, a6, yA]
  · rw [d3, c3, c7, b2, b7, b6, a1, a7, a6, yB]
  · rw [d4, c4, c7, b1, b7, b6, a4, a7, a6, yB]

theorem pF_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hb : s.gpr tbr = s.syms tableName)
    (k : ∀ g : XReg → BitVec 128,
      g .xmm0 = shufDwords (((f .xmm1 &&& cst (oMask 0)) ^^^ (f .xmm2 &&& cst (oMask 1))) ^^^
          ((f .xmm3 &&& cst (oMask 2)) ^^^ (f .xmm4 &&& cst (oMask 3)))) 0xe1 ^^^
        (((f .xmm1 &&& cst (oMask 0)) ^^^ (f .xmm2 &&& cst (oMask 1))) ^^^
          ((f .xmm3 &&& cst (oMask 2)) ^^^ (f .xmm4 &&& cst (oMask 3)))) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pF ++ is)) { s with xmm := f } Q := by
  refine wp_tb hb (by decide) (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ rfl)))))))))))))
/-- P's term, of the folded sum `D`. -/
abbrev termD (D : BitVec 128) (i n : Nat) : BitVec 128 := XShiftOp.eval .psrlq D (BitVec.ofNat 8 n) &&& cst (oP i)

theorem pP_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {stgt : Nat} {ta : Addr}
    (hta : s.ea (at_ sb stgt) = ta) (hb : s.gpr tbr = s.syms tableName) (hrt : InRegions (s.rd ++ s.wr) ta 16)
    (k : ∀ g : XReg → BitVec 128,
      g .xmm7 = (s.mem.readW ta 128 ^^^ (termD (f .xmm0) 4 27 ^^^ termD (f .xmm0) 5 30)) ^^^
        ((termD (f .xmm0) 0 7 ^^^ termD (f .xmm0) 1 15) ^^^ (termD (f .xmm0) 2 16 ^^^ termD (f .xmm0) 3 23)) →
      WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (pP stgt ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (
    wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (
    wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (
    wp_xs rfl (wp_tb hb (by decide) (wp_xs rfl (wp_xs rfl (wp_ld hta hrt (wp_xs rfl (wp_xs rfl (k _ rfl))))))))))))))))))))))))))))))
/-- A round: the input half, in `xmm7`, goes to its slot at `sa`, and
`xmm7` becomes `roundX` of it, of the eight bytes of keys at `ka` and of
the sixteen bytes at `ta`, the target's slot. -/
theorem round_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {sin stgt koff : Nat} {sa ta ka : Addr}
    (hsa : s.ea (at_ sb sin) = sa) (hta : s.ea (at_ sb stgt) = ta) (hka : s.ea (at_ kr koff) = ka)
    (hb : s.gpr tbr = s.syms tableName) (hws : InRegions s.wr sa 16) (hrt : InRegions (s.rd ++ s.wr) ta 16)
    (hrk : InRegions (s.rd ++ s.wr) ka 8)
    (k : ∀ g : XReg → BitVec 128,
      g .xmm7 = roundX (f .xmm7) ((0 : BitVec 64) ++ (s.mem.writeW sa (f .xmm7)).readW ka 64)
        ((s.mem.writeW sa (f .xmm7)).readW ta 128) →
      WP isa (.block is) { ({ s with mem := s.mem.writeW sa (f .xmm7) } : State) with xmm := g } Q) :
    WP isa (.block (round sin stgt koff ++ is)) { s with xmm := f } Q := by
  rw [round_eq, List.append_assoc, List.append_assoc, List.append_assoc]
  refine pE_wp hsa hka hb hws hrk fun g₁ e7 e6 => ?_
  refine pL_wp hb fun g₂ y1 y2 y3 y4 => ?_
  refine pF_wp hb fun g₃ h0 => ?_
  refine pP_wp hta hb hrt fun g₄ h7 => k g₄ ?_
  rw [h7, h0, y1, y2, y3, y4, e7, e6]
  rfl

/-! ## The scratch buffer, and a round of DES -/

open VG.Spec.TripleDes (Schedule roundFunction)

/-- Byte `o` of the scratch buffer at `B`. -/
abbrev sa (B : BitVec 32) (o : Nat) : Addr := B.setWidth 64 + BitVec.ofNat 64 o

/-- The schedule's round key that the rounds use `i`-th: the second key's
in reverse order. -/
def ord (i : Nat) : Nat := if 16 ≤ i ∧ i < 32 then 47 - i else i

/-- The rounds' keys in the scratch buffer at `B`: for each round in the
order of use, the two words of its round key. -/
def Keys (m : Mem) (B : BitVec 32) (k : Schedule) : Prop :=
  ∀ i < 48, m.readW (sa B (keyOff + 8 * i)) 64 = kw1 (k.getD (ord i) 0) ++ kw0 (k.getD (ord i) 0)

theorem dword_key (v : BitVec 64) :
    dword ((0 : BitVec 64) ++ v) 0 = v.setWidth 32 ∧ dword ((0 : BitVec 64) ++ v) 1 = (v >>> 32).setWidth 32 := by
  refine ⟨?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [VG.X86.getLsbD_dword, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
      decide_true, Bool.true_and, Nat.mul_zero, Nat.mul_one, Nat.zero_add, show j < 64 by omega_arith,
      show 32 + j < 64 by omega_arith, ite_true]

theorem ea_sb {B : BitVec 32} (hB : s.gpr sb = B) {o : Nat} (h : B.toNat + o < 2 ^ 32) : s.ea (at_ sb o) = sa B o := by
  show (s.gpr sb + BitVec.ofNat 32 o).setWidth 64 = _
  rw [hB]; exact addr_eq h

/-- A round of DES in the scratch buffer at `B`: with the right half `r`
in `xmm7` and the left half `l` in the target's slot (both rotated right
by one), and the keys of the round `j` at `[kr + koff]`, the input half
goes to its slot and `xmm7` holds `l` with the round function of `r`. -/
theorem round_step {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {sin stgt koff j : Nat}
    {B : BitVec 32} {k : Schedule} {l r : BitVec 32}
    (hB : s.gpr sb = B) (hb : s.gpr tbr = s.syms tableName) (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) (hsl : (sin = sA ∧ stgt = sB) ∨ (sin = sB ∧ stgt = sA)) (hj : j < 48)
    (hka : s.ea (at_ kr koff) = sa B (keyOff + 8 * j)) (hK : Keys s.mem B k)
    (hX : dword (f .xmm7) 0 = r.rotateRight 1) (hT : dword (s.mem.readW (sa B stgt) 128) 0 = l.rotateRight 1)
    (k' : ∀ g : XReg → BitVec 128,
      dword (g .xmm7) 0 = (l ^^^ roundFunction r ((k.getD (ord j) 0).setWidth 48)).rotateRight 1 →
      WP isa (.block is) { ({ s with mem := s.mem.writeW (sa B sin) (f .xmm7) } : State) with xmm := g } Q) :
    WP isa (.block (round sin stgt koff ++ is)) { s with xmm := f } Q := by
  have hin : ∀ o n, o + n ≤ 944 → InRegions s.wr (sa B o) n := fun o n h =>
    ⟨_, hw, VG.Offset.contains_base _ h (by omega_arith)⟩
  have hsin : sin + 16 ≤ 48 ∧ 16 ≤ sin := by rcases hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [sA, sB]
  have hstgt : stgt + 16 ≤ 48 ∧ 16 ≤ stgt := by rcases hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [sA, sB]
  have hne : sin + 16 ≤ stgt ∨ stgt + 16 ≤ sin := by rcases hsl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [sA, sB]
  refine round_wp (ea_sb hB (by omega_arith)) (ea_sb hB (by omega_arith)) hka hb (hin _ _ (by omega_arith))
    ⟨_, List.mem_append_right _ hw, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    ⟨_, List.mem_append_right _ hw,
      VG.Offset.contains_base _ (show keyOff + 8 * j + 8 ≤ 944 by simp only [keyOff]; omega_arith)
        (by simp only [keyOff]; omega_arith)⟩ fun g hg => k' g ?_
  have eK : (s.mem.writeW (sa B sin) (f .xmm7)).readW (sa B (keyOff + 8 * j)) 64 =
      kw1 (k.getD (ord j) 0) ++ kw0 (k.getD (ord j) 0) := by
    rw [Mem.readW_writeW_sep (VG.Offset.sep _ (.inr (by simp only [keyOff]; omega_arith))
      (by simp only [keyOff]; omega_arith) (by omega_arith)) (by decide)]
    exact hK j hj
  have eT : (s.mem.writeW (sa B sin) (f .xmm7)).readW (sa B stgt) 128 = s.mem.readW (sa B stgt) 128 :=
    Mem.readW_writeW_sep (VG.Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  obtain ⟨d0, d1⟩ := dword_key (kw1 (k.getD (ord j) 0) ++ kw0 (k.getD (ord j) 0))
  rw [hg, eK, eT, round_ok _ _ _ r (k.getD (ord j) 0) hX (by rw [d0, VG.Proof.TripleDes.appended_right])
    (by rw [d1, VG.Proof.TripleDes.appended_left]), hT, rotateRight_xor]

/-! ## The initial and the final permutation -/

open VG.X86.Wp
open VG.Spec.TripleDes (permute)
open VG.Proof.TripleDes (appended_left appended_right)

theorem stepL_app (a b : BitVec 32) (n : Nat) (m : BitVec 32) : stepL n m (a ++ b) = swA a b n m ++ swB a b n m := by
  rw [stepL, show hi (a ++ b) = a from appended_left a b, show lo (a ++ b) = b from appended_right a b]

theorem stepR_app (a b : BitVec 32) (n : Nat) (m : BitVec 32) : stepR n m (a ++ b) = swB b a n m ++ swA b a n m := by
  rw [stepR, show hi (a ++ b) = a from appended_left a b, show lo (a ++ b) = b from appended_right a b]

/-- An exchange of bits between two registers, through `eax`. -/
theorem swap_wp {a b : Reg} {n : Nat} {m : BitVec 32} {is : List Instr} {Q : State → Prop} (hab : a ≠ b)
    (ha : a ≠ .eax) (hb : b ≠ .eax) (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', s'.gpr a = swA (s.gpr a) (s.gpr b) n m → s'.gpr b = swB (s.gpr a) (s.gpr b) n m →
      (∀ r, r ≠ a → r ≠ b → r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (swap a b n m ++ is)) s Q := by
  show WP isa (.block (.mov .eax (.reg a) :: .shift .shr .eax n :: .alu .xor .eax (.reg b) :: .alu .and .eax (.imm m) ::
    .alu .xor b (.reg .eax) :: .shift .ror .eax (32 - n) :: .alu .xor a (.reg .eax) :: is)) s Q
  refine wp_mov fun s₁ u₁ => wp_shr hn fun s₂ u₂ _ => wp_xor fun s₃ u₃ => wp_andi fun s₄ u₄ => wp_xor fun s₅ u₅ =>
    wp_ror ⟨by omega_arith, by omega_arith⟩ fun s₆ u₆ => wp_xor fun s₇ u₇ => k s₇ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ ?_ ?_ ?_
  · rw [u₇.gpr, u₆.gpr, u₆.other a ha, u₅.other .eax hb.symm, u₅.other a hab, u₄.gpr, u₄.other a ha, u₃.gpr,
      u₃.other a ha, u₂.gpr, u₂.other a ha, u₂.other b hb, u₁.gpr, u₁.other a ha, u₁.other b hb]
    rfl
  · rw [u₇.other b hab.symm, u₆.other b hb, u₅.gpr, u₄.gpr, u₄.other b hb, u₃.gpr, u₃.other b hb, u₂.gpr,
      u₂.other b hb, u₁.gpr, u₁.other b hb]
    rfl
  · rw [u₇.other r h1, u₆.other r h3, u₅.other r h2, u₄.other r h3, u₃.other r h3, u₂.other r h3, u₁.other r h3]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

theorem rotr_rotr (x : BitVec 32) : (x.rotateRight 1).rotateRight 31 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateRight]
  by_cases h : j = 0
  · subst h; simp
  · simp [show j < 32 by omega_arith, show ¬ j < 1 by omega_arith, show j - 1 < 31 by omega_arith,
      show 1 + (j - 1) = j by omega_arith]

/-- The initial permutation of the block's two words in `esi` and `ecx`,
each half then rotated right by one. -/
theorem ip_wp {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .esi = (hi (permute Spec.TripleDes.ip (s.gpr .esi ++ s.gpr .ecx))).rotateRight 1 →
      s'.gpr .ecx = (lo (permute Spec.TripleDes.ip (s.gpr .esi ++ s.gpr .ecx))).rotateRight 1 →
      (∀ r, r ≠ .esi → r ≠ .ecx → r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (ip ++ is)) s Q := by
  simp only [ip, List.append_assoc]
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₁ a₁ b₁ o₁ m₁ r₁ w₁ y₁ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₂ a₂ b₂ o₂ m₂ r₂ w₂ y₂ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₃ a₃ b₃ o₃ m₃ r₃ w₃ y₃ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₄ a₄ b₄ o₄ m₄ r₄ w₄ y₄ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₅ a₅ b₅ o₅ m₅ r₅ w₅ y₅ => ?_
  refine wp_ror (by decide) fun s₆ u₆ => wp_ror (by decide) fun s₇ u₇ => k s₇ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ ?_ ?_ ?_
  all_goals
    have e : s₅.gpr .esi ++ s₅.gpr .ecx = permute Spec.TripleDes.ip (s.gpr .esi ++ s.gpr .ecx) := by
      rw [← ipS_eq, ipS, stepL_app, stepL_app, stepR_app, stepR_app, stepL_app, ← a₁, ← b₁, ← a₂, ← b₂, ← a₃, ← b₃,
        ← a₄, ← b₄, ← a₅, ← b₅]
  · rw [u₇.other _ (by decide), u₆.gpr, ← e, show hi (s₅.gpr .esi ++ s₅.gpr .ecx) = _ from appended_left _ _]
  · rw [u₇.gpr, u₆.other _ (by decide), ← e, show lo (s₅.gpr .esi ++ s₅.gpr .ecx) = _ from appended_right _ _]
  · rw [u₇.other r h2, u₆.other r h1, o₅ r h1 h2 h3, o₄ r h2 h1 h3, o₃ r h2 h1 h3, o₂ r h1 h2 h3, o₁ r h1 h2 h3]
  · rw [u₇.mem, u₆.mem, m₅, m₄, m₃, m₂, m₁]
  · rw [u₇.rd, u₆.rd, r₅, r₄, r₃, r₂, r₁]
  · rw [u₇.wr, u₆.wr, w₅, w₄, w₃, w₂, w₁]
  · rw [u₇.syms, u₆.syms, y₅, y₄, y₃, y₂, y₁]

/-- The halves in `esi` and `ecx`, rotated right by one, rotated back, and
the final permutation of the two words. -/
theorem fp_wp {is : List Instr} {Q : State → Prop} {l r : BitVec 32} (hl : s.gpr .esi = l.rotateRight 1)
    (hr : s.gpr .ecx = r.rotateRight 1)
    (k : ∀ s', s'.gpr .esi = hi (permute Spec.TripleDes.fp (l ++ r)) → s'.gpr .ecx = lo (permute Spec.TripleDes.fp (l ++ r)) →
      (∀ r, r ≠ .esi → r ≠ .ecx → r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (fp ++ is)) s Q := by
  simp only [fp, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ror (by decide) fun s₆ u₆ => wp_ror (by decide) fun s₇ u₇ => ?_
  have e6 : s₇.gpr .esi = l := by rw [u₇.other _ (by decide), u₆.gpr, hl, rotr_rotr]
  have e7 : s₇.gpr .ecx = r := by rw [u₇.gpr, u₆.other _ (by decide), hr, rotr_rotr]
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₁ a₁ b₁ o₁ m₁ r₁ w₁ y₁ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₂ a₂ b₂ o₂ m₂ r₂ w₂ y₂ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₃ a₃ b₃ o₃ m₃ r₃ w₃ y₃ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₄ a₄ b₄ o₄ m₄ r₄ w₄ y₄ => ?_
  refine swap_wp (by decide) (by decide) (by decide) (by decide) fun s₅ a₅ b₅ o₅ m₅ r₅ w₅ y₅ =>
    k s₅ ?_ ?_ (fun q h1 h2 h3 => ?_) ?_ ?_ ?_ ?_
  all_goals
    have e : s₅.gpr .esi ++ s₅.gpr .ecx = permute Spec.TripleDes.fp (l ++ r) := by
      rw [← fpS_eq, fpS, stepL_app, stepR_app, stepR_app, stepL_app, stepL_app, ← e6, ← e7, ← a₁, ← b₁, ← a₂, ← b₂,
        ← a₃, ← b₃, ← a₄, ← b₄, ← a₅, ← b₅]
  · rw [← e, show hi (s₅.gpr .esi ++ s₅.gpr .ecx) = _ from appended_left _ _]
  · rw [← e, show lo (s₅.gpr .esi ++ s₅.gpr .ecx) = _ from appended_right _ _]
  · rw [o₅ q h1 h2 h3, o₄ q h1 h2 h3, o₃ q h2 h1 h3, o₂ q h2 h1 h3, o₁ q h1 h2 h3, u₇.other q h2, u₆.other q h1]
  · rw [m₅, m₄, m₃, m₂, m₁, u₇.mem, u₆.mem]
  · rw [r₅, r₄, r₃, r₂, r₁, u₇.rd, u₆.rd]
  · rw [w₅, w₄, w₃, w₂, w₁, u₇.wr, u₆.wr]
  · rw [y₅, y₄, y₃, y₂, y₁, u₇.syms, u₆.syms]

/-! ## General registers between the rounds, and the loops -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside), the XMM
registers kept. -/
structure Xupd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  upd : Upd s s' d v
  xmm : s'.xmm = s.xmm

theorem xmovi {d : Reg} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Xupd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨Upd.setReg _ _ _, rfl⟩)

theorem xmov {d r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Xupd s s' d (s.gpr r) → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨Upd.setReg _ _ _, rfl⟩)

theorem xaddi {d : Reg} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Xupd s s' d (s.gpr d + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨Upd.flags _ _ _ _ _ _, rfl⟩)

theorem xsubi {d : Reg} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Xupd s s' d (s.gpr d - v) → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨Upd.flags _ _ _ _ _ _, rfl⟩ rfl)

/-- A loop that runs its body `n` times: the body takes `I t` to `I (t + 1)`
and leaves ZF clear but after the last. -/
theorem count_loop {I : Nat → State → Prop} {n : Nat} {body : Prog isa} (hn : 0 < n) (hs : I 0 s)
    (step : ∀ t u, t < n → I t u → WP isa body u fun u' => I (t + 1) u' ∧ eval .ne u' = some (decide (t + 1 < n))) :
    WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m u => ∃ t, m = n - t ∧ t < n ∧ I t u) (fun m u ⟨t, hm, ht, hI⟩ => ?_) (n - 0) s
    ⟨0, rfl, hn, hs⟩
  refine WP.mono (step t u ht hI) fun u' ⟨hI', hc⟩ => ?_
  by_cases h : t + 1 < n
  · exact .inr ⟨hc.trans (by simp [h]), n - (t + 1), by omega_arith, t + 1, rfl, h, hI'⟩
  · obtain rfl : t + 1 = n := by omega_arith
    exact .inl ⟨hc.trans (by simp), hI'⟩

/-! ## Two rounds -/

open VG.Proof.TripleDes (feistelStep)

theorem Keys.write {m : Mem} {B : BitVec 32} {k : Schedule} (h : Keys m B k) {o w : Nat} (ho : o + w / 8 ≤ keyOff)
    (v : BitVec w) : Keys (m.writeW (sa B o) v) B k := fun i hi => by
  rw [Mem.readW_writeW_sep (VG.Offset.sep _ (.inr (by omega_arith)) (by simp only [keyOff]; omega_arith)
    (by simp only [keyOff] at ho; omega_arith)) (by decide)]
  exact h i hi

theorem ea_kr {B : BitVec 32} {x koff : Nat} (h : s.gpr kr = B + BitVec.ofNat 32 x) (hb : B.toNat + (x + koff) < 2 ^ 32) :
    s.ea (at_ kr koff) = sa B (x + koff) := by
  show (s.gpr kr + BitVec.ofNat 32 koff).setWidth 64 = _
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]; exact addr_eq hb

theorem readW_self128 (m : Mem) (a : Addr) (v : BitVec 128) : (m.writeW a v).readW a 128 = v :=
  Mem.readW_writeW_self m a 16 v (by decide)

theorem keyOff_eq : keyOff = 48 := rfl

/-- What the rounds keep, from the state `s₀` at the block's start, with
the scratch buffer at `B`: its base and the table's in their registers, the
keys, and all of memory but the block's bytes and the two slots. -/
structure Base (s₀ : State) (B : BitVec 32) (k : Schedule) (s : State) : Prop where
  sb : s.gpr sb = B
  tb : s.gpr tbr = s.syms tableName
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  keys : Keys s.mem B k
  frame : Frame [⟨sa B blkOff, 40⟩] s₀.mem s.mem

/-- Before double round `t` of the pass `p`, with the halves `st` (left,
right): the right half is in `xmm7` and the left in the slot `sB`, both
rotated right by one; the keys' pointer and the counts. -/
structure PInv (s₀ : State) (B : BitVec 32) (k : Schedule) (p t : Nat) (st : BitVec 32 × BitVec 32) (s : State) :
    Prop where
  base : Base s₀ B k s
  kr : s.gpr kr = B + BitVec.ofNat 32 (keyOff + 8 * (16 * p + 2 * t))
  ecx : s.gpr .ecx = BitVec.ofNat 32 (8 - t)
  edx : s.gpr .edx = BitVec.ofNat 32 (3 - p)
  x7 : dword (s.xmm .xmm7) 0 = st.2.rotateRight 1
  sl : dword (s.mem.readW (sa B sB) 128) 0 = st.1.rotateRight 1

/-- The round key the rounds use `i`-th. -/
abbrev rk (k : Schedule) (i : Nat) : BitVec 48 := (k.getD (ord i) 0).setWidth 48

/-- Two rounds, and the count. -/
theorem double_wp {s₀ : State} {B : BitVec 32} {k : Schedule} (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₀.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) {p t : Nat} (hp : p < 3) (ht : t < 8) {st : BitVec 32 × BitVec 32}
    (h : PInv s₀ B k p t st s) :
    WP isa (.block double) s fun s' =>
      PInv s₀ B k p (t + 1) (feistelStep (rk k (16 * p + 2 * t + 1)) (feistelStep (rk k (16 * p + 2 * t)) st)) s' ∧
        eval .ne s' = some (decide (t + 1 < 8)) := by
  have hw' : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr := by rw [h.base.wr]; exact hw
  show WP isa (.block (round sA sB 0 ++ (round sB sA 8 ++ [.alu .add kr (.imm 16), .alu .sub .ecx (.imm 1)])))
    { s with xmm := s.xmm } _
  refine round_step (j := 16 * p + 2 * t) (l := st.1) (r := st.2) h.base.sb h.base.tb hw' hfit (.inl ⟨rfl, rfl⟩)
    (by omega_arith)
    (ea_kr h.kr (by show B.toNat + (keyOff + 8 * (16 * p + 2 * t) + 0) < 2 ^ 32; have := keyOff_eq; omega_arith))
    h.base.keys h.x7 h.sl fun g₁ h₁ => ?_
  refine round_step (j := 16 * p + 2 * t + 1) (l := st.2) (r := st.1 ^^^ roundFunction st.2 (rk k (16 * p + 2 * t)))
    h.base.sb h.base.tb hw' hfit (.inr ⟨rfl, rfl⟩) (by omega_arith)
    ((ea_kr (s := s) h.kr
        (by show B.toNat + (keyOff + 8 * (16 * p + 2 * t) + 8) < 2 ^ 32; have := keyOff_eq; omega_arith)).trans
      (congrArg (sa B) (show keyOff + 8 * (16 * p + 2 * t) + 8 = keyOff + 8 * (16 * p + 2 * t + 1) by omega_arith)))
    (h.base.keys.write (by decide) _) h₁
    ((congrArg (dword · 0) (readW_self128 _ _ _)).trans h.x7)
    fun g₂ h₂ => ?_
  refine xaddi fun s₃ u₃ => xsubi fun s₄ u₄ z₄ => WP.block_nil ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₄.upd.other _ (by decide), u₃.upd.other _ (by decide)]; exact h.base.sb
  · rw [u₄.upd.other _ (by decide), u₃.upd.other _ (by decide), u₄.upd.syms, u₃.upd.syms]; exact h.base.tb
  · rw [u₄.upd.other _ (by decide), u₃.upd.other _ (by decide)]; exact h.base.esp
  · rw [u₄.upd.rd, u₃.upd.rd]; exact h.base.rd
  · rw [u₄.upd.wr, u₃.upd.wr]; exact h.base.wr
  · rw [u₄.upd.syms, u₃.upd.syms]; exact h.base.syms
  · rw [u₄.upd.mem, u₃.upd.mem]; exact (h.base.keys.write (by decide) _).write (by decide) _
  · rw [u₄.upd.mem, u₃.upd.mem]
    exact (h.base.frame.writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))
  · rw [u₄.upd.other _ (by decide), u₃.upd.gpr]
    show s.gpr kr + 16 = _
    rw [h.kr, BitVec.add_assoc]
    exact congrArg (B + ·) (by
      rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 32) (by omega_arith))
  · rw [u₄.upd.gpr, u₃.upd.other _ (by decide)]
    show s.gpr .ecx - 1 = _
    rw [h.ecx, ofNat_pred (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by omega_arith)
  · rw [u₄.upd.other _ (by decide), u₃.upd.other _ (by decide)]; exact h.edx
  · rw [u₄.xmm, u₃.xmm]; exact h₂
  · rw [u₄.upd.mem, u₃.upd.mem]
    exact (congrArg (dword · 0) (readW_self128 _ _ _)).trans h₁
  · show s₄.zf.map (!·) = _
    rw [z₄, u₃.upd.other _ (by decide)]
    show Option.map (!·) (some (s.gpr .ecx - 1 == 0)) = _
    rw [h.ecx, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h7 : t + 1 < 8 <;> simp [h7] <;> omega_arith

/-! ## A pass, and the three passes -/

open VG.Spec.TripleDes (Direction componentSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix desCore)

/-- The direction of the pass `p`: the second decrypts. -/
def dirOf (p : Nat) : Direction := if p = 1 then .decrypt else .encrypt

/-- The first `n` rounds of the pass `p`, with the keys in the order the
code reads them. -/
def pk (k : Schedule) (p : Nat) (v : BitVec 32 × BitVec 32) (n : Nat) : BitVec 32 × BitVec 32 :=
  (List.range n).foldl (fun st j => feistelStep (rk k (16 * p + j)) st) v

theorem pk_succ (k : Schedule) (p : Nat) (v : BitVec 32 × BitVec 32) (n : Nat) :
    pk k p v (n + 1) = feistelStep (rk k (16 * p + n)) (pk k p v n) := by
  unfold pk
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The keys in the order of use are each pass's round keys. -/
theorem rk_eq (k : Schedule) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    rk k (16 * p + j) = roundKey (componentSchedule k p) (dirOf p) j := by
  obtain rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 := by omega_arith
  · have e : roundKey (componentSchedule k 0) (dirOf 0) j = (componentSchedule k 0).getD j 0 := by
      simp [roundKey, dirOf]
    rw [e, componentSchedule, VG.Proof.TripleDes.vector_getD _ _ hj, Vector.getElem_ofFn, rk, ord,
      ite_eq_right (by omega_arith)]
  · have e : roundKey (componentSchedule k 1) (dirOf 1) j = (componentSchedule k 1).getD (15 - j) 0 := by
      simp [roundKey, dirOf]
    rw [e, componentSchedule, VG.Proof.TripleDes.vector_getD _ _ (show 15 - j < 16 by omega_arith),
      Vector.getElem_ofFn, rk, ord, ite_eq_left (by omega_arith)]
    exact congrArg (fun i => (k.getD i 0).setWidth 48) (show 47 - (16 * 1 + j) = 16 * 1 + (15 - j) by omega_arith)
  · have e : roundKey (componentSchedule k 2) (dirOf 2) j = (componentSchedule k 2).getD j 0 := by
      simp [roundKey, dirOf]
    rw [e, componentSchedule, VG.Proof.TripleDes.vector_getD _ _ hj, Vector.getElem_ofFn, rk, ord,
      ite_eq_right (by omega_arith)]

theorem pk_eq (k : Schedule) {p : Nat} (hp : p < 3) (v : BitVec 32 × BitVec 32) (n : Nat) (hn : n ≤ 16) :
    pk k p v n = roundPrefix (componentSchedule k p) (dirOf p) n v := by
  induction n with
  | zero => simp [pk, roundPrefix]
  | succ n ih =>
    rw [pk_succ, VG.Proof.TripleDes.roundPrefix_succ, ih (by omega_arith), rk_eq k hp (by omega_arith)]

/-- A pass of DES on the two words `v`. -/
theorem pass_eq (k : Schedule) {p : Nat} (hp : p < 3) (v : BitVec 64) :
    desCore (componentSchedule k p) (dirOf p) v = (pk k p (hi v, lo v) 16).2 ++ (pk k p (hi v, lo v) 16).1 := by
  rw [pk_eq k hp _ 16 (Nat.le_refl 16)]; rfl

/-- Before the pass `p`, with the two words `v` (the left half the high
one): the right half in `xmm7`, the left in the slot `sB`. -/
structure OInv (s₀ : State) (B : BitVec 32) (k : Schedule) (p : Nat) (v : BitVec 64) (s : State) : Prop where
  base : Base s₀ B k s
  kr : s.gpr kr = B + BitVec.ofNat 32 (keyOff + 8 * (16 * p))
  edx : s.gpr .edx = BitVec.ofNat 32 (3 - p)
  x7 : dword (s.xmm .xmm7) 0 = (lo v).rotateRight 1
  sl : dword (s.mem.readW (sa B sB) 128) 0 = (hi v).rotateRight 1

/-- A pass: eight double rounds, and the exchange of the halves. -/
theorem pass_wp {s₀ : State} {B : BitVec 32} {k : Schedule} (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₀.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) {p : Nat} (hp : p < 3) {v : BitVec 64} (h : OInv s₀ B k p v s) :
    WP isa (.seq (.block [.mov .ecx (.imm 8)]) (.seq (.loop (.block double) .ne) (.block exchange))) s fun s' =>
      OInv s₀ B k (p + 1) (desCore (componentSchedule k p) (dirOf p) v) s' ∧
        eval .ne s' = some (decide (p + 1 < 3)) := by
  refine WP.seq (xmovi fun s₁ u₁ => WP.block_nil ?_)
  have h₁ : PInv s₀ B k p 0 (pk k p (hi v, lo v) (2 * 0)) s₁ :=
    ⟨⟨by rw [u₁.upd.other _ (by decide)]; exact h.base.sb,
        by rw [u₁.upd.other _ (by decide), u₁.upd.syms]; exact h.base.tb,
        by rw [u₁.upd.other _ (by decide)]; exact h.base.esp, by rw [u₁.upd.rd]; exact h.base.rd,
        by rw [u₁.upd.wr]; exact h.base.wr, by rw [u₁.upd.syms]; exact h.base.syms,
        by rw [u₁.upd.mem]; exact h.base.keys, by rw [u₁.upd.mem]; exact h.base.frame⟩,
      by rw [u₁.upd.other _ (by decide)]; exact h.kr, u₁.upd.gpr,
      by rw [u₁.upd.other _ (by decide)]; exact h.edx, by rw [u₁.xmm]; exact h.x7,
      by rw [u₁.upd.mem]; exact h.sl⟩
  refine WP.seq (WP.mono (count_loop (I := fun t u => PInv s₀ B k p t (pk k p (hi v, lo v) (2 * t)) u) (by decide) h₁
    fun t u ht hI => WP.mono (double_wp hw hfit hp ht hI) fun u' ⟨a, b⟩ => ⟨?_, b⟩) fun s₂ h₂ => ?_)
  · rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega_arith, pk_succ, pk_succ]; exact a
  have hw' : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₂.wr := by rw [h₂.base.wr]; exact hw
  have ea : s₂.ea (at_ sb sB) = sa B sB := ea_sb h₂.base.sb (by simp only [sB]; omega_arith)
  have hin : InRegions s₂.wr (sa B sB) 16 := ⟨_, hw', VG.Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (ld .xmm0 sb sB :: stx sb sB .xmm7 :: x .movdqa .xmm7 .xmm0 :: [.alu .sub .edx (.imm 1)]))
    { s₂ with xmm := s₂.xmm } _
  refine wp_ld ea ⟨_, List.mem_append_right _ hw', VG.Offset.contains_base _ (by decide) (by decide)⟩
    (wp_st ea hin (wp_xs rfl (xsubi fun s₃ u₃ z₃ => WP.block_nil ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩)))
  · rw [u₃.upd.other _ (by decide)]; exact h₂.base.sb
  · rw [u₃.upd.other _ (by decide), u₃.upd.syms]; exact h₂.base.tb
  · rw [u₃.upd.other _ (by decide)]; exact h₂.base.esp
  · rw [u₃.upd.rd]; exact h₂.base.rd
  · rw [u₃.upd.wr]; exact h₂.base.wr
  · rw [u₃.upd.syms]; exact h₂.base.syms
  · rw [u₃.upd.mem]; exact h₂.base.keys.write (by decide) _
  · rw [u₃.upd.mem]
    exact h₂.base.frame.writeW (List.mem_singleton_self _) _ (VG.Offset.contains _ (by decide) (by decide) (by decide))
  · rw [u₃.upd.other _ (by decide)]
    exact h₂.kr.trans (congrArg (fun i => B + BitVec.ofNat 32 i) (by omega_arith))
  · rw [u₃.upd.gpr]
    show s₂.gpr .edx - 1 = _
    rw [h₂.edx, ofNat_pred (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by omega_arith)
  · rw [u₃.xmm, pass_eq k hp, show lo (_ ++ _) = _ from appended_right _ _]
    exact h₂.sl
  · rw [u₃.upd.mem, pass_eq k hp, show hi (_ ++ _) = _ from appended_left _ _]
    exact (congrArg (dword · 0) (readW_self128 _ _ _)).trans h₂.x7
  · show s₃.zf.map (!·) = _
    rw [z₃]
    show Option.map (!·) (some (s₂.gpr .edx - 1 == 0)) = _
    rw [h₂.edx, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h3 : p + 1 < 3 <;> simp [h3] <;> omega_arith

/-- The words after the first `p` passes. -/
def passes (k : Schedule) (v : BitVec 64) : Nat → BitVec 64
  | 0 => v
  | p + 1 => desCore (componentSchedule k p) (dirOf p) (passes k v p)

/-- The 48 rounds. -/
theorem rounds_wp {s₀ : State} {B : BitVec 32} {k : Schedule} (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₀.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) {v : BitVec 64} (h : OInv s₀ B k 0 v s) :
    WP isa rounds s (OInv s₀ B k 3 (passes k v 3)) :=
  count_loop (I := fun p u => OInv s₀ B k p (passes k v p) u) (by decide) h fun _ _ hp hI => pass_wp hw hfit hp hI

/-! ## The block's two ends -/

open VG.Spec.TripleDes (decodeBlock encodeBlock blockAt)

theorem dword_movd (x : BitVec 32) : dword ((0 : BitVec 96) ++ x) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.X86.getLsbD_dword, BitVec.getLsbD_append, hj, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add,
    ite_true]

theorem sa_add4 (B : BitVec 32) (o : Nat) : sa B o + 4 = sa B (o + 4) := by
  rw [sa, BitVec.add_assoc, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]

/-- The block to the first round's halves. -/
theorem head_wp {B : BitVec 32} {k : Schedule} (hB : s.gpr sb = B) (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) (htb : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : Keys s.mem B k) :
    WP isa (.block cryptHead) s
      (OInv s B k 0 (permute Spec.TripleDes.ip (decodeBlock (blockAt s.mem (sa B blkOff))))) := by
  have ha : ∀ o, o + 4 ≤ 944 → addr B o = sa B o := fun o h => addr_eq (by omega_arith)
  have hin : ∀ o, o + 4 ≤ 944 → InRegions (s.rd ++ s.wr) (addr B o) 4 := fun o h => by
    rw [ha o h]; exact ⟨_, List.mem_append_right _ hw, VG.Offset.contains_base _ h (by omega_arith)⟩
  show WP isa (.block (.mov tbr (.mem ⟨sb, 0⟩) :: .mov .esi (.mem ⟨sb, blkOff⟩) :: .mov .ecx (.mem ⟨sb, blkOff + 4⟩) ::
    .bswap .esi :: .bswap .ecx :: (ip ++ [.xop (.movd .xmm0 .esi), stx sb sB .xmm0, .xop (.movd .xmm7 .ecx),
      .mov kr (.reg sb), .alu .add kr (.imm (BitVec.ofNat 32 keyOff)), .mov .edx (.imm 3)]))) s _
  refine wp_ldm hB (hin 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_ldm (B := B) (by rw [u₁.other _ (by decide)]; exact hB) (by rw [u₁.rd, u₁.wr]; exact hin _ (by decide))
    fun s₂ u₂ => ?_
  refine wp_ldm (B := B) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by decide)) fun s₃ u₃ => ?_
  refine wp_bswap fun s₄ u₄ => wp_bswap fun s₅ u₅ => ip_wp fun s₆ a₆ b₆ o₆ m₆ r₆ w₆ y₆ => ?_
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e_esi : s₅.gpr .esi = bswap (s.mem.readW (sa B blkOff) 32) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem, ha _ (by decide)]
  have e_ecx : s₅.gpr .ecx = bswap (s.mem.readW (sa B (blkOff + 4)) 32) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, ha _ (by decide)]
  have hv : s₅.gpr .esi ++ s₅.gpr .ecx = decodeBlock (blockAt s.mem (sa B blkOff)) := by
    rw [VG.Proof.TripleDes.X86.decodeBlock_readW, e_esi, e_ecx, sa_add4]
  rw [hv] at a₆ b₆
  have mem₆ : s₆.mem = s.mem := m₆.trans mem₅
  have g₆ : ∀ r, r ≠ .esi → r ≠ .ecx → r ≠ .eax → r ≠ .ebx → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₆ r h1 h2 h3, u₅.other r h2, u₄.other r h1, u₃.other r h2, u₂.other r h1, u₁.other r h4]
  have wr₆ : s₆.wr = s.wr := by rw [w₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₆ : s₆.rd = s.rd := by rw [r₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have sy₆ : s₆.syms = s.syms := by rw [y₆, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have sb₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  have tb₆ : s₆.gpr tbr = s.syms tableName := by
    rw [o₆ _ (by decide) (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ha 0 (by decide)]
    exact (congrArg (s.mem.readW · 32) (BitVec.add_zero _)).trans htb
  show WP isa (.block (.xop (.movd .xmm0 .esi) :: stx sb sB .xmm0 :: .xop (.movd .xmm7 .ecx) ::
    .mov kr (.reg sb) :: .alu .add kr (.imm (BitVec.ofNat 32 keyOff)) :: [.mov .edx (.imm 3)])) { s₆ with xmm := s₆.xmm } _
  refine wp_xs rfl (wp_st (ea_sb sb₆ (by simp only [sB]; omega_arith))
    ⟨_, by rw [wr₆]; exact hw, VG.Offset.contains_base _ (by decide) (by decide)⟩ (wp_xs rfl (xmov fun s₇ u₇ =>
      xaddi fun s₈ u₈ => xmovi fun s₉ u₉ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩)))
  · rw [u₉.upd.other _ (by decide), u₈.upd.other _ (by decide), u₇.upd.other _ (by decide)]; exact sb₆
  · rw [u₉.upd.other _ (by decide), u₈.upd.other _ (by decide), u₇.upd.other _ (by decide), u₉.upd.syms, u₈.upd.syms,
      u₇.upd.syms]
    exact tb₆.trans (congrFun sy₆ tableName).symm
  · rw [u₉.upd.other _ (by decide), u₈.upd.other _ (by decide), u₇.upd.other _ (by decide)]
    exact g₆ _ (by decide) (by decide) (by decide) (by decide)
  · rw [u₉.upd.rd, u₈.upd.rd, u₇.upd.rd]; exact rd₆
  · rw [u₉.upd.wr, u₈.upd.wr, u₇.upd.wr]; exact wr₆
  · rw [u₉.upd.syms, u₈.upd.syms, u₇.upd.syms]; exact sy₆
  · rw [u₉.upd.mem, u₈.upd.mem, u₇.upd.mem]
    show Keys (s₆.mem.writeW (sa B sB) _) B k
    rw [mem₆]; exact hk.write (by decide) _
  · rw [u₉.upd.mem, u₈.upd.mem, u₇.upd.mem]
    show Frame _ s.mem (s₆.mem.writeW (sa B sB) _)
    rw [mem₆]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains _ (by decide) (by decide) (by decide))
  · rw [u₉.upd.other _ (by decide), u₈.upd.gpr, u₇.upd.gpr]
    show s₆.gpr sb + BitVec.ofNat 32 keyOff = _
    rw [sb₆]; rfl
  · exact u₉.upd.gpr
  · rw [u₉.xmm, u₈.xmm, u₇.xmm]
    show dword ((0 : BitVec 96) ++ s₆.gpr .ecx) 0 = _
    rw [dword_movd, b₆]
  · rw [u₉.upd.mem, u₈.upd.mem, u₇.upd.mem]
    show dword ((s₆.mem.writeW (sa B sB) ((0 : BitVec 96) ++ s₆.gpr .esi)).readW (sa B sB) 128) 0 = _
    rw [readW_self128, dword_movd, a₆]

theorem readW_dword0 (m : Mem) (a : Addr) : m.readW a 32 = dword (m.readW a 128) 0 := by
  have h := VG.X86.dword_readW m a (j := 0) (by decide)
  rw [Nat.mul_zero, BitVec.add_zero] at h
  exact h.symm

/-- The halves after the last exchange to the block. -/
theorem tail_wp {s₀ : State} {B : BitVec 32} {k : Schedule} (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₀.wr)
    (hfit : B.toNat + 944 ≤ 2 ^ 32) {V : BitVec 64} (h : OInv s₀ B k 3 V s) :
    WP isa (.block cryptTail) s fun s' =>
      s'.gpr sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
        Keys s'.mem B k ∧ Frame [⟨sa B blkOff, 40⟩] s₀.mem s'.mem ∧
        blockAt s'.mem (sa B blkOff) = encodeBlock (permute Spec.TripleDes.fp V) := by
  have hw' : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr := by rw [h.base.wr]; exact hw
  have ha : ∀ o, o + 4 ≤ 944 → addr B o = sa B o := fun o h => addr_eq (by omega_arith)
  have hin : ∀ o, o + 4 ≤ 944 → InRegions s.wr (addr B o) 4 := fun o h => by
    rw [ha o h]; exact ⟨_, hw', VG.Offset.contains_base _ h (by omega_arith)⟩
  have hin' : ∀ o, o + 4 ≤ 944 → InRegions (s.rd ++ s.wr) (addr B o) 4 := fun o h =>
    let ⟨r, hr, c⟩ := hin o h; ⟨r, List.mem_append_right _ hr, c⟩
  show WP isa (.block (stx sb sA .xmm7 :: .mov .esi (.mem ⟨sb, sB⟩) :: .mov .ecx (.mem ⟨sb, sA⟩) ::
    (fp ++ [.bswap .esi, .bswap .ecx, .store ⟨sb, blkOff⟩ .esi, .store ⟨sb, blkOff + 4⟩ .ecx]))) { s with xmm := s.xmm } _
  refine wp_st (ea_sb h.base.sb (by simp only [sA]; omega_arith))
    ⟨_, hw', VG.Offset.contains_base _ (by decide) (by decide)⟩ ?_
  refine wp_ldm (B := B) h.base.sb (hin' _ (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (B := B) (by rw [u₂.other _ (by decide)]; exact h.base.sb)
    (by rw [u₂.rd, u₂.wr]; exact hin' _ (by decide)) fun s₃ u₃ => ?_
  have e_l : s₃.gpr .esi = (hi V).rotateRight 1 := by
    rw [u₃.other _ (by decide), u₂.gpr]
    show (s.mem.writeW (sa B sA) (s.xmm .xmm7)).readW (addr B sB) 32 = _
    rw [ha _ (by decide), Mem.readW_writeW_sep (VG.Offset.sep _ (.inr (by decide)) (by decide) (by decide)) (by decide),
      readW_dword0]
    exact h.sl
  have e_r : s₃.gpr .ecx = (lo V).rotateRight 1 := by
    rw [u₃.gpr, u₂.mem]
    show (s.mem.writeW (sa B sA) (s.xmm .xmm7)).readW (addr B sA) 32 = _
    rw [ha _ (by decide), readW_dword0, readW_self128]
    exact h.x7
  refine fp_wp e_l e_r fun s₄ a₄ b₄ o₄ m₄ r₄ w₄ y₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => ?_
  have sb₆ : s₆.gpr sb = B := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), o₄ _ (by decide) (by decide) (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide)]
    exact h.base.sb
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, w₄, u₃.wr, u₂.wr]
  refine wp_stm (b := sb) (B := B) (o := blkOff) sb₆ (by rw [wr₆]; exact hin _ (by decide)) fun s₇ u₇ => ?_
  refine wp_stm (b := sb) (B := B) (o := blkOff + 4) ((congrFun u₇.gpr _).trans sb₆)
    (by rw [u₇.wr, wr₆]; exact hin _ (by decide)) fun s₈ u₈ => WP.block_nil ?_
  rw [show hi V ++ lo V = V from VG.Proof.TripleDes.halves_append V] at a₄ b₄
  have e₆ : s₆.gpr .esi = bswap (hi (permute Spec.TripleDes.fp V)) := by rw [u₆.other _ (by decide), u₅.gpr, a₄]
  have c₆ : s₆.gpr .ecx = bswap (lo (permute Spec.TripleDes.fp V)) := by rw [u₆.gpr, u₅.other _ (by decide), b₄]
  have mem₈ : s₈.mem = (s.mem.writeW (sa B sA) (s.xmm .xmm7)).writeW (sa B blkOff)
      (VG.byteRev64 (permute Spec.TripleDes.fp V)) := by
    rw [u₈.mem, u₇.mem, u₇.gpr, e₆, c₆, u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, ha _ (by decide), ha _ (by decide),
      ← sa_add4, VG.Proof.TripleDes.X86.writeW_pair, VG.Proof.TripleDes.X86.bswapPair,
      VG.Proof.TripleDes.halves_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₈.gpr, u₇.gpr]; exact sb₆
  · rw [u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), o₄ _ (by decide) (by decide) (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide)]
    exact h.base.esp
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, r₄, u₃.rd, u₂.rd]; exact h.base.rd
  · rw [u₈.wr, u₇.wr, wr₆]; exact h.base.wr
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, y₄, u₃.syms, u₂.syms]; exact h.base.syms
  · rw [mem₈]; exact (h.base.keys.write (by decide) _).write (by decide) _
  · rw [mem₈]
    exact (h.base.frame.writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (VG.Offset.contains _ (by decide) (by decide) (by decide))
  · rw [mem₈, VG.Proof.TripleDes.X86.blockAt_writeW]

/-! ## The core's block function -/

open VG.Proof.Modes.X86 (ScrIn coreRegion blkAddr blkRegion slotA stkRegion)
open VG.Proof.TripleDes (dirCipher bytesAt_eq)
open VG.Spec.Aes (bytesAt)

/-- The key is ready: the table's address in the scratch buffer's first
slot, and the rounds' keys. -/
def Ready (s : State) (B : BitVec 32) (k : Schedule) : Prop :=
  s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ Keys s.mem B k ∧ B.toNat + 944 ≤ 2 ^ 32

theorem ready_frame {s s' : State} {B : BitVec 32} {k : Schedule} {rs : List Region} (h : Ready s B k)
    (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) : Ready s' B k := by
  obtain ⟨htb, hk, hfit⟩ := h
  refine ⟨?_, fun i hi => ?_, hfit⟩
  · rw [hsy, ← htb]
    refine hf.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hd r hr with h' | h'
    · exact h'.sub_left (Region.sub_prefix (by decide))
    · exact (VG.Offset.disjoint_base _ (by decide) (by decide)).symm.sub_right h'
  · rw [← hk i hi]
    refine hf.readW (r := ⟨sa B (keyOff + 8 * i), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hd r hr with h' | h'
    · exact h'.sub_left (VG.Offset.sub_base _ (by have := keyOff_eq; simp only [core, slots]; omega_arith))
    · exact (VG.Offset.disjoint _ (.inr (by have := keyOff_eq; simp only [core]; omega_arith))
        (by have := keyOff_eq; omega_arith) (by decide)).sub_right h'

theorem passes3 (k : Schedule) (v : BitVec 64) :
    passes k v 3 = desCore (componentSchedule k 2) .encrypt (desCore (componentSchedule k 1) .decrypt
      (desCore (componentSchedule k 0) .encrypt v)) := rfl

/-- The block of the core's buffer, enciphered in place. -/
theorem crypt_wp {s : State} {B : BitVec 32} {k : Schedule} (hB : s.gpr sb = B) (hs : ScrIn s B core.total)
    (hr : Ready s B k) :
    WP isa core.crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧
      (∀ j < core.G, bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        dirCipher .encrypt k (bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨htb, hk, hfit⟩ := hr
  have hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr := hs.wr
  show WP isa (.seq (.block cryptHead) (.seq rounds (.block cryptTail))) s _
  refine WP.seq (WP.mono (head_wp hB hw hfit htb hk) fun s₁ h₁ => WP.seq (WP.mono (rounds_wp hw hfit h₁) fun s₂ h₂ =>
    WP.mono (tail_wp hw hfit h₂) fun s₃ ⟨a, b, c, d, e, f, g, hblk⟩ => ?_))
  refine ⟨a, b, ⟨?_, f, hfit⟩, ?_, fun j hj => ?_, c, d⟩
  · rw [e, ← htb]
    exact g.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (VG.Offset.disjoint_base _ (by decide) (by decide)).symm) (by decide)
  · refine g.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.sub_base _ (by decide)
  · obtain rfl : j = 0 := by have : j < 1 := hj; omega_arith
    have eB : blkAddr core B 0 = sa B blkOff := by simp [blkAddr, slotA, core, blkOff]
    rw [show 4 * core.bw = 8 from rfl, eB, bytesAt_eq, hblk, VG.Proof.TripleDes.X86.Mode.dirCipher_bytes, passes3]
    show _ = (Spec.TripleDes.encryptBlock k _).toList
    rw [VG.Proof.TripleDes.encryptBlock_eq_cores]

/-! ## The keys -/

/-- A field of a round key's word: a shift or a rotation, and a mask. -/
def fv (x : BitVec 32) (rot : Bool) (n : Nat) (m : BitVec 32) : BitVec 32 :=
  (if rot then x.rotateRight n else x >>> n) &&& m

theorem wp_ori {d : Reg} {v : BitVec 32} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- A field, to `ebp`. -/
theorem field_wp {src : Reg} {off n : Nat} {rot : Bool} {m P : BitVec 32} {is : List Instr} {Q : State → Prop}
    (hsrc : s.gpr src = P) (hin : InRegions (s.rd ++ s.wr) (addr P off) 4) (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' .ebp (fv (s.mem.readW (addr P off) 32) rot n m) → WP isa (.block is) s' Q) :
    WP isa (.block (field src off rot n m ++ is)) s Q := by
  cases rot
  · show WP isa (.block (.mov .ebp (.mem ⟨src, off⟩) :: .shift .shr .ebp n :: .alu .and .ebp (.imm m) :: is)) s Q
    refine wp_ldm hsrc hin fun s₁ u₁ => wp_shr hn fun s₂ u₂ _ => wp_andi fun s₃ u₃ =>
      k s₃ ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl, fun r hr => by rw [u₃.other r hr, u₂.other r hr, u₁.other r hr],
        by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
        by rw [u₃.syms, u₂.syms, u₁.syms]⟩
  · show WP isa (.block (.mov .ebp (.mem ⟨src, off⟩) :: .shift .ror .ebp n :: .alu .and .ebp (.imm m) :: is)) s Q
    refine wp_ldm hsrc hin fun s₁ u₁ => wp_ror hn fun s₂ u₂ => wp_andi fun s₃ u₃ =>
      k s₃ ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl, fun r hr => by rw [u₃.other r hr, u₂.other r hr, u₁.other r hr],
        by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
        by rw [u₃.syms, u₂.syms, u₁.syms]⟩

/-- What a step of a word's accumulation keeps. -/
structure Kupd (s s' : State) (v : BitVec 32) : Prop where
  ebx : s'.gpr .ebx = v
  other : ∀ r, r ≠ .ebx → r ≠ .ebp → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

/-- A word's first field, to `ebx`. -/
theorem movf_wp {src : Reg} {off n : Nat} {rot : Bool} {m P : BitVec 32} {is : List Instr} {Q : State → Prop}
    (hsrc : s.gpr src = P) (hin : InRegions (s.rd ++ s.wr) (addr P off) 4) (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Kupd s s' (fv (s.mem.readW (addr P off) 32) rot n m) → WP isa (.block is) s' Q) :
    WP isa (.block (field src off rot n m ++ (.mov .ebx (.reg .ebp) :: is))) s Q :=
  field_wp hsrc hin hn fun s₁ u₁ => wp_mov fun s₂ u₂ =>
    k s₂ ⟨by rw [u₂.gpr, u₁.gpr], fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.syms, u₁.syms]⟩

/-- A further field, into `ebx`. -/
theorem orf_wp {src : Reg} {off n : Nat} {rot : Bool} {m P : BitVec 32} {is : List Instr} {Q : State → Prop}
    (hsrc : s.gpr src = P) (hin : InRegions (s.rd ++ s.wr) (addr P off) 4) (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Kupd s s' (s.gpr .ebx ||| fv (s.mem.readW (addr P off) 32) rot n m) → WP isa (.block is) s' Q) :
    WP isa (.block (field src off rot n m ++ (.alu .or .ebx (.reg .ebp) :: is))) s Q :=
  field_wp hsrc hin hn fun s₁ u₁ => wp_or fun s₂ u₂ =>
    k s₂ ⟨by rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide)], fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.syms, u₁.syms]⟩

theorem kw0_eq (lo hi : BitVec 32) :
    fv lo false 6 0x3f#32 ||| fv lo false 10 0x3f00#32 ||| fv lo false 14 0x30000#32 ||| fv hi true 14 0x3c0000#32 |||
      fv hi true 18 0x3f000000#32 ||| 0x40404040#32 = kw0 (hi ++ lo) := by
  simp only [kw0, fv, appended_left, appended_right, Bool.false_eq_true, ↓reduceIte]

theorem kw1_eq (lo hi : BitVec 32) :
    fv lo false 4 0x3f00#32 ||| (lo &&& 0x3f#32) ||| fv lo false 8 0x3f0000#32 ||| fv hi true 12 0x3f000000#32 |||
      0x40404040#32 = kw1 (hi ++ lo) := by
  simp only [kw1, fv, appended_left, appended_right, Bool.false_eq_true, ↓reduceIte]

/-- A round's two words, from the round key at `[src + off]` to
`[esi + dst]`, through `ebx` and `ebp`. -/
theorem key_wp {src : Reg} {off dst : Nat} {P D : BitVec 32} {is : List Instr} {Q : State → Prop}
    (hsrc : s.gpr src = P) (hD : s.gpr .esi = D) (h1 : src ≠ .ebp) (h2 : src ≠ .ebx)
    (hlo : InRegions (s.rd ++ s.wr) (addr P off) 4) (hhi : InRegions (s.rd ++ s.wr) (addr P (off + 4)) 4)
    (hw0 : InRegions s.wr (addr D dst) 4) (hw1 : InRegions s.wr (addr D (dst + 4)) 4)
    (sep0 : Mem.Sep (addr P off) 4 (addr D dst) 4) (sep1 : Mem.Sep (addr P (off + 4)) 4 (addr D dst) 4)
    (k : ∀ s', s'.mem = (s.mem.writeW (addr D dst)
            (kw0 (s.mem.readW (addr P (off + 4)) 32 ++ s.mem.readW (addr P off) 32))).writeW (addr D (dst + 4))
          (kw1 (s.mem.readW (addr P (off + 4)) 32 ++ s.mem.readW (addr P off) 32)) →
      (∀ r, r ≠ .ebx → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (key src off dst ++ is)) s Q := by
  simp only [key, List.append_assoc, List.cons_append, List.nil_append]
  refine movf_wp hsrc hlo (by decide) fun s₁ a₁ => ?_
  have p₁ : s₁.gpr src = P := by rw [a₁.other _ h2 h1]; exact hsrc
  have rw₁ : s₁.rd ++ s₁.wr = s.rd ++ s.wr := by rw [a₁.rd, a₁.wr]
  refine orf_wp p₁ (by rw [rw₁]; exact hlo) (by decide) fun s₂ a₂ => ?_
  have p₂ : s₂.gpr src = P := by rw [a₂.other _ h2 h1]; exact p₁
  have rw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [a₂.rd, a₂.wr]; exact rw₁
  refine orf_wp p₂ (by rw [rw₂]; exact hlo) (by decide) fun s₃ a₃ => ?_
  have p₃ : s₃.gpr src = P := by rw [a₃.other _ h2 h1]; exact p₂
  have rw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [a₃.rd, a₃.wr]; exact rw₂
  refine orf_wp p₃ (by rw [rw₃]; exact hhi) (by decide) fun s₄ a₄ => ?_
  have p₄ : s₄.gpr src = P := by rw [a₄.other _ h2 h1]; exact p₃
  have rw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [a₄.rd, a₄.wr]; exact rw₃
  refine orf_wp p₄ (by rw [rw₄]; exact hhi) (by decide) fun s₅ a₅ => ?_
  refine wp_ori fun s₆ u₆ => ?_
  have m₁ : s₁.mem = s.mem := a₁.mem
  have m₂ : s₂.mem = s.mem := a₂.mem.trans m₁
  have m₃ : s₃.mem = s.mem := a₃.mem.trans m₂
  have m₄ : s₄.mem = s.mem := a₄.mem.trans m₃
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, a₅.mem]; exact m₄
  have e₆ : s₆.gpr .ebx = kw0 (s.mem.readW (addr P (off + 4)) 32 ++ s.mem.readW (addr P off) 32) := by
    rw [u₆.gpr, a₅.ebx, m₄, a₄.ebx, m₃, a₃.ebx, m₂, a₂.ebx, m₁, a₁.ebx]; exact kw0_eq _ _
  have g₆ : ∀ r, r ≠ .ebx → r ≠ .ebp → s₆.gpr r = s.gpr r := fun r hx hp => by
    rw [u₆.other r hx, a₅.other r hx hp, a₄.other r hx hp, a₃.other r hx hp, a₂.other r hx hp, a₁.other r hx hp]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, a₅.wr, a₄.wr, a₃.wr, a₂.wr, a₁.wr]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, a₅.rd, a₄.rd, a₃.rd, a₂.rd, a₁.rd]
  have sy₆ : s₆.syms = s.syms := by rw [u₆.syms, a₅.syms, a₄.syms, a₃.syms, a₂.syms, a₁.syms]
  refine wp_stm (b := .esi) (B := D) (o := dst) ((g₆ _ (by decide) (by decide)).trans hD) (by rw [wr₆]; exact hw0)
    fun s₇ u₇ => ?_
  have p₇ : s₇.gpr src = P := by rw [u₇.gpr, g₆ _ h2 h1]; exact hsrc
  have rw₇ : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by rw [u₇.rd, u₇.wr, rd₆, wr₆]
  have lo₇ : s₇.mem.readW (addr P off) 32 = s.mem.readW (addr P off) 32 := by
    rw [u₇.mem, Mem.readW_writeW_sep sep0 (by decide), m₆]
  have hi₇ : s₇.mem.readW (addr P (off + 4)) 32 = s.mem.readW (addr P (off + 4)) 32 := by
    rw [u₇.mem, Mem.readW_writeW_sep sep1 (by decide), m₆]
  refine movf_wp p₇ (by rw [rw₇]; exact hlo) (by decide) fun s₈ a₈ => ?_
  have p₈ : s₈.gpr src = P := by rw [a₈.other _ h2 h1]; exact p₇
  have rw₈ : s₈.rd ++ s₈.wr = s.rd ++ s.wr := by rw [a₈.rd, a₈.wr]; exact rw₇
  refine wp_ldm p₈ (by rw [rw₈]; exact hlo) fun s₉ u₉ => wp_andi fun s₁₀ u₁₀ => wp_or fun s₁₁ u₁₁ => ?_
  have p₁₁ : s₁₁.gpr src = P := by rw [u₁₁.other _ h2, u₁₀.other _ h1, u₉.other _ h1]; exact p₈
  have rw₁₁ : s₁₁.rd ++ s₁₁.wr = s.rd ++ s.wr := by rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr]; exact rw₈
  have m₁₁ : s₁₁.mem = s₇.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, a₈.mem]
  refine orf_wp p₁₁ (by rw [rw₁₁]; exact hlo) (by decide) fun s₁₂ a₁₂ => ?_
  have p₁₂ : s₁₂.gpr src = P := by rw [a₁₂.other _ h2 h1]; exact p₁₁
  have rw₁₂ : s₁₂.rd ++ s₁₂.wr = s.rd ++ s.wr := by rw [a₁₂.rd, a₁₂.wr]; exact rw₁₁
  refine orf_wp p₁₂ (by rw [rw₁₂]; exact hhi) (by decide) fun s₁₃ a₁₃ => wp_ori fun s₁₄ u₁₄ => ?_
  have m₁₄ : s₁₄.mem = s₇.mem := by rw [u₁₄.mem, a₁₃.mem, a₁₂.mem]; exact m₁₁
  have e₁₄ : s₁₄.gpr .ebx = kw1 (s.mem.readW (addr P (off + 4)) 32 ++ s.mem.readW (addr P off) 32) := by
    rw [u₁₄.gpr, a₁₃.ebx, a₁₂.mem, m₁₁, hi₇, a₁₂.ebx, m₁₁, lo₇, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr,
      u₉.other _ (by decide), a₈.mem, lo₇, a₈.ebx, lo₇]
    exact kw1_eq _ _
  have g₁₄ : ∀ r, r ≠ .ebx → r ≠ .ebp → s₁₄.gpr r = s.gpr r := fun r hx hp => by
    rw [u₁₄.other r hx, a₁₃.other r hx hp, a₁₂.other r hx hp, u₁₁.other r hx, u₁₀.other r hp, u₉.other r hp,
      a₈.other r hx hp, u₇.gpr, g₆ r hx hp]
  have wr₁₄ : s₁₄.wr = s.wr := by
    rw [u₁₄.wr, a₁₃.wr, a₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, a₈.wr, u₇.wr, wr₆]
  refine wp_stm (b := .esi) (B := D) (o := dst + 4) ((g₁₄ _ (by decide) (by decide)).trans hD)
    (by rw [wr₁₄]; exact hw1) fun s₁₅ u₁₅ => k s₁₅ ?_ (fun r hx hp => by rw [u₁₅.gpr, g₁₄ r hx hp]) ?_ ?_ ?_
  · rw [u₁₅.mem, m₁₄, u₇.mem, m₆, e₆, e₁₄]
  · rw [u₁₅.rd, u₁₄.rd, a₁₃.rd, a₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, a₈.rd, u₇.rd, rd₆]
  · rw [u₁₅.wr, wr₁₄]
  · rw [u₁₅.syms, u₁₄.syms, a₁₃.syms, a₁₂.syms, u₁₁.syms, u₁₀.syms, u₉.syms, a₈.syms, u₇.syms, sy₆]

/-- The two words of a round key, as the rounds read them. -/
abbrev kq (S : BitVec 64) : BitVec 64 := kw1 S ++ kw0 S

theorem add4 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + 4 = p + BitVec.ofNat 64 (d + 4) := by
  rw [BitVec.add_assoc, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]

/-- The round key at slot `i` of the schedule at `P` to the keys of the
round `i'`. -/
theorem keyAt_wp {src : Reg} {off dst i i' : Nat} {X Dv B P : BitVec 32} {S : BitVec 64} {is : List Instr}
    {Q : State → Prop} (hsrc : s.gpr src = X) (hD : s.gpr .esi = Dv) (h1 : src ≠ .ebp) (h2 : src ≠ .ebx)
    (eS : addr X off = P.setWidth 64 + BitVec.ofNat 64 (8 * i))
    (eS4 : addr X (off + 4) = P.setWidth 64 + BitVec.ofNat 64 (8 * i) + 4)
    (eD : addr Dv dst = sa B (keyOff + 8 * i')) (eD4 : addr Dv (dst + 4) = sa B (keyOff + 8 * i') + 4)
    (hi : i < 48) (hi' : i' < 48) (hrs : (⟨P.setWidth 64, 384⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr)
    (hdis : Region.Disjoint ⟨P.setWidth 64, 384⟩ ⟨B.setWidth 64, 944⟩)
    (hS : s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = S)
    (k' : ∀ s', s'.mem = s.mem.writeW (sa B (keyOff + 8 * i')) (kq S) →
      (∀ r, r ≠ .ebx → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (key src off dst ++ is)) s Q := by
  have cS : (⟨P.setWidth 64, 384⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 4 :=
    VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have cS4 : (⟨P.setWidth 64, 384⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 (8 * i) + 4) 4 := by
    rw [add4]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have cD : (⟨B.setWidth 64, 944⟩ : Region).Contains (sa B (keyOff + 8 * i')) 4 :=
    VG.Offset.contains_base _ (by have := keyOff_eq; omega_arith) (by have := keyOff_eq; omega_arith)
  have cD4 : (⟨B.setWidth 64, 944⟩ : Region).Contains (sa B (keyOff + 8 * i') + 4) 4 := by
    rw [add4]; exact VG.Offset.contains_base _ (by have := keyOff_eq; omega_arith) (by have := keyOff_eq; omega_arith)
  refine key_wp hsrc hD h1 h2 (by rw [eS]; exact ⟨_, hrs, cS⟩) (by rw [eS4]; exact ⟨_, hrs, cS4⟩)
    (by rw [eD]; exact ⟨_, hw, cD⟩) (by rw [eD4]; exact ⟨_, hw, cD4⟩) (by rw [eS, eD]; exact hdis.sep cS cD)
    (by rw [eS4, eD]; exact hdis.sep cS4 cD) fun s' hm g r w y => k' s' ?_ g r w y
  rw [hm, eS, eS4, eD, eD4, VG.Proof.TripleDes.X86.readW_pair, hS, VG.Proof.TripleDes.X86.writeW_pair]

theorem rdw_same (m : Mem) (B : BitVec 32) (a : Nat) (v : BitVec 64) :
    (m.writeW (sa B (keyOff + 8 * a)) v).readW (sa B (keyOff + 8 * a)) 64 = v := Mem.readW_writeW_self64 _ _ _

theorem rdw_ne (m : Mem) (B : BitVec 32) {a b : Nat} (h : a ≠ b) (ha : a < 48) (hb : b < 48) (v : BitVec 64) :
    (m.writeW (sa B (keyOff + 8 * a)) v).readW (sa B (keyOff + 8 * b)) 64 = m.readW (sa B (keyOff + 8 * b)) 64 :=
  Mem.readW_writeW_sep (VG.Offset.sep _ (by omega_arith) (by have := keyOff_eq; omega_arith)
    (by have := keyOff_eq; omega_arith)) (by decide)

theorem ord_lo {t : Nat} (ht : t < 16) : ord t = t := by rw [ord, ite_eq_right (by omega_arith)]
theorem ord_mid {t : Nat} (ht : t < 16) : ord (16 + t) = 31 - t := by
  rw [ord, ite_eq_left (by omega_arith)]; omega_arith
theorem ord_hi {t : Nat} (ht : t < 16) : ord (32 + t) = 32 + t := by
  rw [ord, ite_eq_right (by omega_arith)]

theorem addr_add {P : BitVec 32} {a b c : Nat} (hc : a + b = c) (h : P.toNat + c < 2 ^ 32) :
    addr (P + BitVec.ofNat 32 a) b = P.setWidth 64 + BitVec.ofNat 64 c := by
  rw [← addr_eq h]
  simp only [addr]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hc]

theorem addr_add4 {P : BitVec 32} {a b c : Nat} (hc : a + b = c + 4) (h : P.toNat + (c + 4) < 2 ^ 32) :
    addr (P + BitVec.ofNat 32 a) b = P.setWidth 64 + BitVec.ofNat 64 c + 4 := (addr_add hc h).trans (add4 _ _).symm

/-- The schedule's words are apart from the keys the loop writes. -/
theorem sched_read {m₁ m : Mem} {B P : BitVec 32} (hf : Frame [⟨sa B keyOff, 384⟩] m₁ m)
    (hdis : Region.Disjoint ⟨P.setWidth 64, 384⟩ ⟨B.setWidth 64, 944⟩) {i : Nat} (hi : i < 48) :
    m.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = m₁.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 :=
  hf.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact (hdis.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right
      (VG.Offset.sub_base _ (by have := keyOff_eq; omega_arith))) (by decide)

theorem keys_contains (B : BitVec 32) {i : Nat} (hi : i < 48) :
    (⟨sa B keyOff, 384⟩ : Region).Contains (sa B (keyOff + 8 * i)) (64 / 8) :=
  VG.Offset.contains _ (by omega_arith) (by omega_arith) (by have := keyOff_eq; omega_arith)

/-- The keys' conversion, before the round `t` of each of the three passes. -/
structure KInv (s₁ : State) (B P : BitVec 32) (k : Schedule) (t : Nat) (s : State) : Prop where
  sb : s.gpr sb = B
  eax : s.gpr .eax = P + BitVec.ofNat 32 (8 * t)
  edx : s.gpr .edx = P + BitVec.ofNat 32 (248 - 8 * t)
  esi : s.gpr .esi = B + BitVec.ofNat 32 (keyOff + 8 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (16 - t)
  esp : s.gpr .esp = s₁.gpr .esp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  syms : s.syms = s₁.syms
  frame : Frame [⟨sa B keyOff, 384⟩] s₁.mem s.mem
  done : ∀ i < 48, i % 16 < t → s.mem.readW (sa B (keyOff + 8 * i)) 64 = kq (k.getD (ord i) 0)

theorem prepBody_eq : prepBody = key .eax 0 0 ++ (key .edx 0 128 ++ (key .eax 256 256 ++
    ([.alu .add .eax (.imm 8), .alu .sub .edx (.imm 8), .alu .add .esi (.imm 8), .alu .sub .ecx (.imm 1)] :
      List Instr))) := by
  rw [prepBody, List.append_assoc, List.append_assoc]

/-- A round's keys of the three passes, and the count. -/
theorem prepBody_wp {s₁ : State} {B P : BitVec 32} {k : Schedule} {t : Nat}
    (hrs : (⟨P.setWidth 64, 384⟩ : Region) ∈ s₁.rd ++ s₁.wr) (hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s₁.wr)
    (hdis : Region.Disjoint ⟨P.setWidth 64, 384⟩ ⟨B.setWidth 64, 944⟩)
    (hP : P.toNat + 384 ≤ 2 ^ 32) (hfit : B.toNat + 944 ≤ 2 ^ 32)
    (hS : ∀ i < 48, s₁.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = k.getD i 0)
    (ht : t < 16) (h : KInv s₁ B P k t s) :
    WP isa (.block prepBody) s fun s' => KInv s₁ B P k (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 16)) := by
  have hrs' : (⟨P.setWidth 64, 384⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd, h.wr]; exact hrs
  have hw' : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr := by rw [h.wr]; exact hw
  have hko := keyOff_eq
  rw [prepBody_eq]
  refine keyAt_wp (i := t) (i' := t) h.eax h.esi (by decide) (by decide)
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (by omega_arith) (by omega_arith) hrs' hw' hdis
    ((sched_read h.frame hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₂ m₂ g₂ rd₂ wr₂ sy₂ => ?_
  obtain f₂ : Frame [⟨sa B keyOff, 384⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  refine keyAt_wp (i := 31 - t) (i' := 16 + t) ((g₂ .edx (by decide) (by decide)).trans h.edx)
    ((g₂ .esi (by decide) (by decide)).trans h.esi) (by decide) (by decide)
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (by omega_arith) (by omega_arith) (by rw [rd₂, wr₂]; exact hrs') (by rw [wr₂]; exact hw') hdis
    ((sched_read f₂ hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₃ m₃ g₃ rd₃ wr₃ sy₃ => ?_
  obtain f₃ : Frame [⟨sa B keyOff, 384⟩] s₁.mem s₃.mem := by
    rw [m₃]; exact f₂.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  refine keyAt_wp (i := 32 + t) (i' := 32 + t)
    ((g₃ .eax (by decide) (by decide)).trans ((g₂ .eax (by decide) (by decide)).trans h.eax))
    ((g₃ .esi (by decide) (by decide)).trans ((g₂ .esi (by decide) (by decide)).trans h.esi)) (by decide) (by decide)
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (addr_add (by omega_arith) (by omega_arith)) (addr_add4 (by omega_arith) (by omega_arith))
    (by omega_arith) (by omega_arith) (by rw [rd₃, wr₃, rd₂, wr₂]; exact hrs') (by rw [wr₃, wr₂]; exact hw') hdis
    ((sched_read f₃ hdis (by omega_arith)).trans (hS _ (by omega_arith))) fun s₄ m₄ g₄ rd₄ wr₄ sy₄ => ?_
  obtain f₄ : Frame [⟨sa B keyOff, 384⟩] s₁.mem s₄.mem := by
    rw [m₄]; exact f₃.writeW (List.mem_singleton_self _) _ (keys_contains B (by omega_arith))
  obtain G : ∀ r, r ≠ .ebx → r ≠ .ebp → s₄.gpr r = s.gpr r := fun r a b =>
    ((g₄ r a b).trans (g₃ r a b)).trans (g₂ r a b)
  refine wp_addi fun s₅ u₅ => wp_subi fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => wp_subi fun s₈ u₈ _ z₈ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      G _ (by decide) (by decide)]
    exact h.sb
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, G _ (by decide) (by decide),
      h.eax, BitVec.add_assoc]
    exact congrArg (P + ·) (by
      rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 32) (by omega_arith))
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), G _ (by decide) (by decide),
      h.edx, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
    exact congrArg (P + ·) ((sub_ofNat (b := 8) (by omega_arith)).trans
      (congrArg (BitVec.ofNat 32) (by omega_arith)))
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), G _ (by decide) (by decide),
      h.esi, BitVec.add_assoc]
    exact congrArg (B + ·) (by
      rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 32) (by omega_arith))
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), G _ (by decide) (by decide),
      h.ecx, ofNat_pred (by omega_arith)]
    exact congrArg (BitVec.ofNat 32) (by omega_arith)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      G _ (by decide) (by decide)]
    exact h.esp
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄, rd₃, rd₂]; exact h.rd
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, wr₃, wr₂]; exact h.wr
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, sy₄, sy₃, sy₂]; exact h.syms
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact f₄
  · intro i hi hlt
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄, m₃, m₂]
    by_cases e2 : i = 32 + t
    · subst e2; rw [rdw_same, ord_hi ht]
    rw [rdw_ne _ _ (Ne.symm e2) (by omega_arith) hi]
    by_cases e1 : i = 16 + t
    · subst e1; rw [rdw_same, ord_mid ht]
    rw [rdw_ne _ _ (Ne.symm e1) (by omega_arith) hi]
    by_cases e0 : i = t
    · subst e0; rw [rdw_same, ord_lo ht]
    rw [rdw_ne _ _ (Ne.symm e0) (by omega_arith) hi]
    exact h.done i hi (by omega_arith)
  · show s₈.zf.map (!·) = _
    rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), G _ (by decide) (by decide),
      h.ecx, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h7 : t + 1 < 16 <;> simp [h7] <;> omega_arith

theorem addr_zero (B : BitVec 32) : addr B 0 = B.setWidth 64 := by simp [addr]

/-- The table's address and the keys of the 48 rounds, in the core's
slots. -/
theorem prepare_wp {s : State} {B : BitVec 32} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B core.total) (hR : (⟨B.setWidth 64, 4 * core.total⟩ : Region) ∈ rs)
    (hk : Mode.KeyArgs s rs k) (hsp : core.stack ≤ (s.gpr .esp).toNat) :
    WP isa core.prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfitP, hdis, hadis, -, hsk, hsa⟩ := hk
  have hfB : B.toNat + 944 ≤ 2 ^ 32 := hs.fit
  have hw : (⟨B.setWidth 64, 944⟩ : Region) ∈ s.wr := hs.wr
  have hsp' : 16 ≤ (s.gpr .esp).toNat := hsp
  have hko := keyOff_eq
  obtain dPB : Region.Disjoint ⟨p.setWidth 64, 384⟩ ⟨B.setWidth 64, 944⟩ := hdis _ hR
  obtain dAB : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 944⟩ := hadis _ hR
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1))
    (.seq (.block prepHead) (.loop (.block prepBody) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s (by omega_arith)) fun s₀ h₀ => WP.seq ?_)
  obtain sb₀ : s₀.gpr sb = B := (h₀.gpr _ (by decide)).trans hB
  obtain esp₀ : s₀.gpr .esp = s.gpr .esp := h₀.gpr _ (by decide)
  -- what the function has written is in the core's slots or the core's stack
  obtain f₀ : Frame [coreRegion core B, stkRegion (s.gpr .esp) 16] s.mem s₀.mem :=
    h₀.frame.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
      obtain rfl := List.mem_singleton.mp hr
      exact below_sub (by decide) hsp'⟩
  refine wp_stm sb₀ (by rw [h₀.wr, addr_zero]; exact ⟨_, hw, by simp [Region.Contains]⟩) fun s₁ u₁ => ?_
  obtain f₁ : Frame [coreRegion core B, stkRegion (s.gpr .esp) 16] s.mem s₁.mem := by
    rw [u₁.mem, addr_zero]
    exact f₀.writeW List.mem_cons_self _
      (show (⟨B.setWidth 64, 904⟩ : Region).Contains _ 4 by simp [Region.Contains])
  obtain hval : s₁.mem.readW (s.ea (argOp 0)) 32 = p :=
    (f₁.readW (r := ⟨s.ea (argOp 0), 4⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact dAB.sub_right (Region.sub_prefix (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact hsa.symm) (by decide)).trans hp
  refine wp_ldm (B := s.gpr .esp) (by rw [u₁.gpr]; exact esp₀)
    (by rw [u₁.rd, u₁.wr, h₀.rd, h₀.wr]; exact hin) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_movi fun s₇ u₇ =>
    WP.block_nil ?_
  obtain G : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .ecx → s₇.gpr r = s₀.gpr r := fun r a b c d => by
    rw [u₇.other r d, u₆.other r c, u₅.other r c, u₄.other r b, u₃.other r b, u₂.other r a, u₁.gpr]
  obtain M : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain RD : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₀.rd]
  obtain WR : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₀.wr]
  obtain SY : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms, h₀.syms]
  obtain eax₂ : s₂.gpr .eax = p := u₂.gpr.trans hval
  refine WP.mono (count_loop (I := KInv s₇ B p (Spec.TripleDes.scheduleAt s.mem (p.setWidth 64))) (n := 16)
    (by decide) ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, Frame.refl _ _, fun i _ h => absurd h (Nat.not_lt_zero _)⟩
    fun t u ht hI => prepBody_wp (by rw [RD, WR]; exact hsch) (by rw [WR]; exact hw) dPB hfitP hfB (fun i hi => ?_)
      ht hI) fun s₈ h₈ => ?_
  · exact (G _ (by decide) (by decide) (by decide) (by decide)).trans sb₀
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), eax₂]
    exact (BitVec.add_zero p).symm
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, eax₂]
    rfl
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, sb₀]
    rfl
  · rw [u₇.gpr]; rfl
  · rw [VG.Proof.TripleDes.vector_getD _ i hi, VG.Proof.TripleDes.scheduleAt_readW _ _ i hi, M]
    exact f₁.readW (r := ⟨_, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (dPB.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
      · obtain rfl := List.mem_singleton.mp hr
        exact hsk.symm.sub_left (VG.Offset.sub_base _ (by omega_arith))) (by decide)
  refine ⟨⟨?_, fun i hi => h₈.done i hi (by omega_arith), hfB⟩, h₈.sb,
    h₈.esp.trans ((G _ (by decide) (by decide) (by decide) (by decide)).trans esp₀), ?_, h₈.rd.trans RD,
    h₈.wr.trans WR⟩
  · rw [h₈.syms, SY, ← h₀.addr]
    refine (h₈.frame.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact VG.Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by decide)).trans ?_
    rw [M, u₁.mem, addr_zero]
    exact Mem.readW_writeW_self _ _ 4 _ (by decide)
  · refine Frame.trans (by rw [M]; exact f₁) (h₈.frame.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩)
    obtain rfl := List.mem_singleton.mp hr
    exact VG.Offset.sub_base _ (by decide)

/-- The core's contract: Triple DES's encryption of a block, with the
schedule in the first stack argument. -/
def ssse3CoreSpec : VG.Proof.Modes.X86.CoreSpec core where
  Key := Schedule
  cipher := dirCipher .encrypt
  KeyArgs := Mode.KeyArgs
  Ready := Ready
  cipher_len k b := by simp [dirCipher, Spec.TripleDes.cipher, core]
  layout := ⟨by decide, .inl rfl, by decide, by decide⟩
  keyArgs_congr h e r w _ f := Mode.keyArgs_congr h e r w f
  ready_frame h _ _ _ hsy hf _ hd := ready_frame h hsy hf hd
  prepare_wp := prepare_wp
  crypt_wp hB hs hr _ := crypt_wp hB hs hr

/-- The core fits Triple DES's functions, with 118 words. -/
def ssse3Fits : Mode.Fits ssse3CoreSpec 118 := ⟨id, id, rfl, rfl, rfl, rfl⟩

end VG.Proof.TripleDes.X86.Ssse3
