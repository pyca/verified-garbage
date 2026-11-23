module

public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Round
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Triple DES's core by `pshufb` on x86 (32-bit): what the code does

* A round (`round_wp`), run an instruction at a time in four pieces (the
  expansion and the key, the look-ups, the masks and the fold, P), from a
  state given by its XMM registers, leaves in `xmm7` what
  `Ssse3Round.lean` says of it (`roundX`), and the input half in its slot.
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

end VG.Proof.TripleDes.X86.Ssse3
