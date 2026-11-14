module

public import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Impl.Blake2.Arm.CompressS
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Blake2.Arm.CompressS.Rounds`, which only this module used -/

section

@[expose] public section

section

/-!
# BLAKE2s on ARMv7: instructions and rotations

Weakest-precondition rules for the instructions the compression function uses
that `Proof/MdStream/Arm` lacks, and the facts about rotations its rotated
registers need.
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd)

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [reduceExec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl (k _ (Upd.setReg _ _ _))

theorem op2_ror {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

end

/-! ## Rotations -/

theorem rotl_rotr (x : BitVec 32) {k : Nat} (hk : k < 32) : (x.rotateRight k).rotateLeft k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega_arith | (congr 1; omega_arith)

theorem rotr_rotl (x : BitVec 32) {k : Nat} (hk : k < 32) : (x.rotateLeft k).rotateRight k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega_arith | (congr 1; omega_arith)

theorem rotr_eq_rotl (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateRight k = x.rotateLeft (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk',
    Nat.mod_eq_of_lt (show 32 - k < 32 by omega_arith)]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega_arith | (congr 1; omega_arith)

theorem rotl_xor (x y : BitVec 32) (k : Nat) : (x ^^^ y).rotateLeft k = x.rotateLeft k ^^^ y.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  split <;> simp_all

theorem rotl8_rotr1 (x : BitVec 32) : (x.rotateLeft 8).rotateRight 1 = x.rotateLeft 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, show 8 % 32 = 8 from rfl,
    show 1 % 32 = 1 from rfl, show 7 % 32 = 7 from rfl]
  by_cases h1 : i < 32 - 1
  · by_cases h2 : 1 + i < 8 <;> by_cases h3 : i < 7 <;>
      simp [h1, h2, h3, hi, show 1 + i < 32 by omega_arith] <;> first | omega_arith | (congr 1; omega_arith)
  · by_cases h2 : i - (32 - 1) < 8 <;> by_cases h3 : i < 7 <;> simp [h1, h2, h3, hi] <;>
      first | omega_arith | (congr 1; omega_arith)

/-- `G`'s words for BLAKE2s, in the order the code computes them: with `b` and
`d` given rotated left by 7 and 8, the code's additions and exclusive ors
before their rotations. -/
theorem mix_s (va B' vc D' X Y : BitVec 32) :
    Proof.Blake2.mix Spec.Blake2.s va (B'.rotateRight 7) vc (D'.rotateRight 8) X Y =
      let a1 := va + B'.rotateRight 7 + X
      let e1 := a1 ^^^ D'.rotateRight 8
      let c1 := vc + e1.rotateRight 16
      let f1 := c1 ^^^ B'.rotateRight 7
      let a2 := a1 + Y + f1.rotateRight 12
      let e2 := a2 ^^^ e1.rotateRight 16
      let c2 := c1 + e2.rotateRight 8
      let f2 := c2 ^^^ f1.rotateRight 12
      (a2, f2.rotateRight 7, c2, e2.rotateRight 8) := by
  simp only [Proof.Blake2.mix, show Spec.Blake2.s.R1 = 16 from rfl, show Spec.Blake2.s.R2 = 12 from rfl,
    show Spec.Blake2.s.R3 = 8 from rfl, show Spec.Blake2.s.R4 = 7 from rfl]
  simp only [BitVec.xor_comm (D'.rotateRight 8), BitVec.xor_comm (B'.rotateRight 7), BitVec.add_assoc,
    BitVec.add_comm Y]
  simp only [BitVec.xor_comm _ (_ + _)]

end VG.Proof.Blake2.ArmS

end

/-!
# BLAKE2s on ARMv7: the rounds

`G`, executed once for any of its registers and offsets (`wp_g`), and the
rounds on the work vector: words 0–3 in `r0`–`r3`, words 4–7 rotated left by 7
in `r4`–`r7`, words 8–11 in `scratch[64, 80)` and words 12–15 rotated left by
8 in `r8`–`r11` (`RI`).
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Blake2.Arm.S (wreg cOff g gAt round rounds)
open VG.Proof.Sha512.Arm (Only A A_eq)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_ldr wp_str op2_reg)
open VG.Spec.Blake2 (Work Block)

/-! ## One `G` -/

/-- What `G` leaves, from `s`, with the words `r` (`mix`'s order). -/
structure GOut (a b d : Reg) (V : BitVec 32) (c : Nat) (s s' : State)
    (r : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) : Prop where
  ra : s'.gpr a = r.1
  rb : s'.gpr b = r.2.1.rotateLeft 7
  rdd : s'.gpr d = r.2.2.2.rotateLeft 8
  other : ∀ q, q ≠ a → q ≠ b → q ≠ d → q ≠ .lr → s'.gpr q = s.gpr q
  mem : s'.mem = s.mem.writeW (A V (cOff c)) r.2.2.1
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_g {a b d : Reg} {c x y : Nat} {V : BitVec 32}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (haS : a ≠ .r12) (hbS : b ≠ .r12) (hdS : d ≠ .r12) (haT : a ≠ .lr) (hbT : b ≠ .lr) (hdT : d ≠ .lr)
    (hc : cOff c < 4096) (hx : 4 * x < 4096) (hy : 4 * y < 4096) (hV : s.gpr .r12 = V)
    (iX : InRegions (s.rd ++ s.wr) (A V (4 * x)) 4) (iY : InRegions (s.rd ++ s.wr) (A V (4 * y)) 4)
    (oC : InRegions s.wr (A V (cOff c)) 4)
    (K : ∀ s', GOut a b d V c s s' (Proof.Blake2.mix Spec.Blake2.s (s.gpr a) ((s.gpr b).rotateRight 7)
      (s.mem.readW (A V (cOff c)) 32) ((s.gpr d).rotateRight 8) (s.mem.readW (A V (4 * x)) 32)
      (s.mem.readW (A V (4 * y)) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (g a b d c x y ++ rest)) s Q := by
  have iC : InRegions (s.rd ++ s.wr) (A V (cOff c)) 4 :=
    let ⟨r, hr, h⟩ := oC; ⟨r, List.mem_append_right _ hr, h⟩
  simp only [g, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine wp_ldr hx (by rw [hV]) iX fun s₁ u₁ => ?_
  refine wp_add (op2_ror (by decide)) fun s₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₄ u₄ => ?_
  have hS : ∀ q : Reg, q ≠ .lr → q ≠ a → q ≠ d → s₄.gpr q = s.gpr q := fun q h1 h2 h3 => by
    rw [u₄.other q h3, u₃.other q h2, u₂.other q h2, u₁.other q h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldr hy (by rw [hS _ (by decide) (Ne.symm haS) (Ne.symm hdS), hV])
    (by rw [rd₄, wr₄]; exact iY) fun s₅ u₅ => ?_
  refine wp_add (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_ldr hc (by rw [u₆.other _ (Ne.symm haS), u₅.other _ (by decide),
      hS _ (by decide) (Ne.symm haS) (Ne.symm hdS), hV])
    (by rw [u₆.rd, u₅.rd, rd₄, u₆.wr, u₅.wr, wr₄]; exact iC) fun s₇ u₇ => ?_
  refine wp_add (op2_ror (by decide)) fun s₈ u₈ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₉ u₉ => ?_
  refine wp_add (op2_ror (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_add (op2_ror (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_eor (op2_ror (by decide)) fun s₁₃ u₁₃ => ?_
  have hS' : ∀ q : Reg, q ≠ .lr → q ≠ a → q ≠ b → q ≠ d → s₁₃.gpr q = s.gpr q := fun q h1 h2 h3 h4 => by
    rw [u₁₃.other q h3, u₁₂.other q h1, u₁₁.other q h4, u₁₀.other q h2, u₉.other q h3, u₈.other q h1,
      u₇.other q h1, u₆.other q h2, u₅.other q h1, hS q h1 h2 h4]
  have m₁₃ : s₁₃.mem = s.mem := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  refine wp_str hc (by rw [hS' _ (by decide) (Ne.symm haS) (Ne.symm hbS) (Ne.symm hdS), hV])
    (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]; exact oC)
    fun s₁₄ m₁₄ => K s₁₄ ?_
  -- The registers, step by step.
  have v2 : s₂.gpr a = s.gpr a + (s.gpr b).rotateRight 7 := by rw [u₂.gpr, u₁.other a haT, u₁.other b hbT]
  have a3 : s₃.gpr a = s.gpr a + (s.gpr b).rotateRight 7 + s.mem.readW (A V (4 * x)) 32 := by
    rw [u₃.gpr, v2, u₂.other .lr (Ne.symm haT), u₁.gpr]
  have b3 : s₃.gpr b = s.gpr b := by rw [u₃.other b (Ne.symm hab), u₂.other b (Ne.symm hab), u₁.other b hbT]
  have d3 : s₃.gpr d = s.gpr d := by rw [u₃.other d (Ne.symm had), u₂.other d (Ne.symm had), u₁.other d hdT]
  have e4 : s₄.gpr d = s₃.gpr a ^^^ (s.gpr d).rotateRight 8 := by rw [u₄.gpr, d3]
  have a4 : s₄.gpr a = s₃.gpr a := u₄.other a had
  have b4 : s₄.gpr b = s.gpr b := by rw [u₄.other b hbd, b3]
  have a6 : s₆.gpr a = s₃.gpr a + s.mem.readW (A V (4 * y)) 32 := by
    rw [u₆.gpr, u₅.other a haT, a4, u₅.gpr, m₄]
  have c7 : s₇.gpr .lr = s.mem.readW (A V (cOff c)) 32 := by rw [u₇.gpr, u₆.mem, u₅.mem, m₄]
  have d7 : s₇.gpr d = s₄.gpr d := by rw [u₇.other d hdT, u₆.other d (Ne.symm had), u₅.other d hdT]
  have b7 : s₇.gpr b = s.gpr b := by rw [u₇.other b hbT, u₆.other b (Ne.symm hab), u₅.other b hbT, b4]
  have a7 : s₇.gpr a = s₆.gpr a := u₇.other a haT
  have c8 : s₈.gpr .lr = s.mem.readW (A V (cOff c)) 32 + (s₄.gpr d).rotateRight 16 := by
    rw [u₈.gpr, c7, d7]
  have f9 : s₉.gpr b = s₈.gpr .lr ^^^ (s.gpr b).rotateRight 7 := by rw [u₉.gpr, u₈.other b hbT, b7]
  have a9 : s₉.gpr a = s₆.gpr a := by rw [u₉.other a hab, u₈.other a haT, a7]
  have d9 : s₉.gpr d = s₄.gpr d := by rw [u₉.other d (Ne.symm hbd), u₈.other d hdT, d7]
  have c9 : s₉.gpr .lr = s₈.gpr .lr := u₉.other .lr (Ne.symm hbT)
  have a10 : s₁₀.gpr a = s₆.gpr a + (s₉.gpr b).rotateRight 12 := by rw [u₁₀.gpr, a9]
  have d10 : s₁₀.gpr d = s₄.gpr d := by rw [u₁₀.other d (Ne.symm had), d9]
  have b10 : s₁₀.gpr b = s₉.gpr b := u₁₀.other b (Ne.symm hab)
  have c10 : s₁₀.gpr .lr = s₈.gpr .lr := by rw [u₁₀.other .lr (Ne.symm haT), c9]
  have e11 : s₁₁.gpr d = s₁₀.gpr a ^^^ (s₄.gpr d).rotateRight 16 := by rw [u₁₁.gpr, d10]
  have a11 : s₁₁.gpr a = s₁₀.gpr a := u₁₁.other a had
  have b11 : s₁₁.gpr b = s₉.gpr b := by rw [u₁₁.other b hbd, b10]
  have c11 : s₁₁.gpr .lr = s₈.gpr .lr := by rw [u₁₁.other .lr (Ne.symm hdT), c10]
  have c12 : s₁₂.gpr .lr = s₈.gpr .lr + (s₁₁.gpr d).rotateRight 8 := by rw [u₁₂.gpr, c11]
  have a12 : s₁₂.gpr a = s₁₀.gpr a := by rw [u₁₂.other a haT, a11]
  have b12 : s₁₂.gpr b = s₉.gpr b := by rw [u₁₂.other b hbT, b11]
  have d12 : s₁₂.gpr d = s₁₁.gpr d := u₁₂.other d hdT
  have f13 : s₁₃.gpr b = s₁₂.gpr .lr ^^^ (s₉.gpr b).rotateRight 12 := by rw [u₁₃.gpr, b12]
  have a13 : s₁₃.gpr a = s₁₀.gpr a := by rw [u₁₃.other a hab, a12]
  have d13 : s₁₃.gpr d = s₁₁.gpr d := by rw [u₁₃.other d (Ne.symm hbd), d12]
  have c13 : s₁₃.gpr .lr = s₁₂.gpr .lr := u₁₃.other .lr (Ne.symm hbT)
  rw [mix_s]
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₄.gpr, a13, a10, a6, f9, c8, e4, a3]
  · rw [m₁₄.gpr, f13, c12, f9, c8, e11, a10, a6, f9, c8, e4, a3, rotl_rotr _ (by decide)]
  · rw [m₁₄.gpr, d13, e11, a10, a6, f9, c8, e4, a3, rotl_rotr _ (by decide)]
  · rw [m₁₄.gpr, hS' q h4 h1 h2 h3]
  · rw [m₁₄.mem, m₁₃, c13, c12, e11, a10, a6, f9, c8, e4, a3]
  · rw [m₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄]
  · rw [m₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]
  · rw [m₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp,
      u₁.sp]

end

/-! ## The work vector -/

/-- Word `k` of the work vector is `x`: in its register (rotated for words
4–7 and 12–15) or, for words 8–11, in `scratch`. -/
def Holds (V : BitVec 32) (s : State) (k : Nat) (x : BitVec 32) : Prop :=
  if k < 4 then s.gpr (wreg k) = x
  else if k < 8 then s.gpr (wreg k) = x.rotateLeft 7
  else if k < 12 then s.mem.readW (A V (cOff k)) 32 = x
  else s.gpr (wreg k) = x.rotateLeft 8

theorem holds_lo {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h : k < 4) :
    Holds V s k x ↔ s.gpr (wreg k) = x := by simp only [Holds, h, ↓reduceIte]

theorem holds_mid {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 4 ≤ k) (h₂ : k < 8) :
    Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 7 := by
  simp only [Holds, show ¬ k < 4 by omega_arith, h₂, ↓reduceIte]

theorem holds_c {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 8 ≤ k) (h₂ : k < 12) :
    Holds V s k x ↔ s.mem.readW (A V (cOff k)) 32 = x := by
  simp only [Holds, show ¬ k < 4 by omega_arith, show ¬ k < 8 by omega_arith, h₂, ↓reduceIte]

theorem holds_hi {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 12 ≤ k) :
    Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 8 := by
  simp only [Holds, show ¬ k < 4 by omega_arith, show ¬ k < 8 by omega_arith, show ¬ k < 12 by omega_arith, ↓reduceIte]

/-- Words 8–11 of the work vector, in `scratch[64, 80)`. -/
abbrev cR (V : BitVec 32) : Region := ⟨State.addr V + BitVec.ofNat 64 64, 16⟩

/-- What the rounds need of the state `s₀` at their start: the scratch space
at `V` (in `r12`), holding the message block `M` in its first 64 bytes. -/
structure RCtx (V : BitVec 32) (M : Block 32) (s₀ : State) : Prop where
  r12 : s₀.gpr .r12 = V
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wV : ∀ o, o + 4 ≤ 512 → InRegions s₀.wr (A V o) 4
  msg : ∀ j (hj : j < 16), s₀.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩

/-- The rounds invariant, relative to the state `s₀` at their start: the work
vector is `v`, and nothing else has changed but `lr`, `r0`–`r11` and
`scratch[64, 80)`. -/
structure RI (V : BitVec 32) (s₀ : State) (v : Work 32) (s : State) : Prop where
  vars : ∀ k (hk : k < 16), Holds V s k v[k]
  r12 : s.gpr .r12 = s₀.gpr .r12
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [cR V] s₀.mem s.mem

theorem wreg_ne : ∀ k < 16, wreg k ≠ .r12 ∧ wreg k ≠ .lr := by decide

theorem wreg_inj' : ∀ k < 16, ∀ j < 16, wreg k = wreg j → k = j ∨ (8 ≤ k ∧ k < 12) ∨ (8 ≤ j ∧ j < 12) := by
  decide

theorem wreg_inj (k : Nat) (hk : k < 16) (j : Nat) (hj : j < 16) (h₁ : ¬ (8 ≤ k ∧ k < 12))
    (h₂ : ¬ (8 ≤ j ∧ j < 12)) (e : wreg k = wreg j) : k = j := by
  rcases wreg_inj' k hk j hj e with h | h | h
  · exact h
  · exact absurd h h₁
  · exact absurd h h₂

theorem cOff_A {V : BitVec 32} (fit : V.toNat + 512 ≤ 2 ^ 32) {o : Nat} (ho : o < 512) :
    A V o = State.addr V + BitVec.ofNat 64 o := A_eq (by omega_arith)

theorem gAt_ok {x y z u : Nat} (hx : x < 4) (hy₁ : 4 ≤ y) (hy : y < 8) (hz₁ : 8 ≤ z) (hz : z < 12)
    (hu₁ : 12 ≤ u) (hu : u < 16) (r i : Nat) {V : BitVec 32} {M : Block 32} {s₀ s : State}
    {v : Work 32} (c : RCtx V M s₀) (h : RI V s₀ v s) :
    WP isa (gAt r i x y z u) s (RI V s₀ (Spec.Blake2.G Spec.Blake2.s v ⟨x, by omega_arith⟩ ⟨y, by omega_arith⟩
      ⟨z, by omega_arith⟩ ⟨u, hu⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have fitV := c.fitV
  have nx := wreg_ne x (by omega_arith)
  have ny := wreg_ne y (by omega_arith)
  have nu := wreg_ne u (by omega_arith)
  have ixy : wreg x ≠ wreg y := fun e => absurd (wreg_inj x (by omega_arith) y (by omega_arith) (by omega_arith) (by omega_arith) e)
    (by omega_arith)
  have ixu : wreg x ≠ wreg u := fun e => absurd (wreg_inj x (by omega_arith) u (by omega_arith) (by omega_arith) (by omega_arith) e)
    (by omega_arith)
  have iyu : wreg y ≠ wreg u := fun e => absurd (wreg_inj y (by omega_arith) u (by omega_arith) (by omega_arith) (by omega_arith) e)
    (by omega_arith)
  have hcz : cOff z < 4096 := by unfold cOff; omega_arith
  have hV : s.gpr .r12 = V := by rw [h.r12, c.r12]
  -- The message words are unchanged.
  have hm : ∀ j (hj : j < 16), s.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩ := fun j hj => by
    rw [← c.msg j hj, cOff_A fitV (by omega_arith)]
    refine h.frame.readW (r := ⟨State.addr V, 64⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact (Offset.disjoint_base _ (by omega_arith) (by omega_arith)).symm
  have iV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := c.wV o ho; ⟨r, List.mem_append_right _ (by rw [h.wr]; exact hr), hc⟩
  unfold gAt
  rw [← List.append_nil (g _ _ _ _ _ _)]
  refine wp_g ixy ixu iyu nx.1 ny.1 nu.1 nx.2 ny.2 nu.2 hcz (by omega_arith) (by omega_arith) hV
    (iV _ (by omega_arith)) (iV _ (by omega_arith)) (by rw [h.wr]; exact c.wV _ (by unfold cOff; omega_arith))
    fun s' w => WP.block_nil ?_
  have va : s.gpr (wreg x) = v[x]'(by omega_arith) := (holds_lo hx).mp (h.vars x (by omega_arith))
  have vb : (s.gpr (wreg y)).rotateRight 7 = v[y]'(by omega_arith) := by
    rw [(holds_mid hy₁ hy).mp (h.vars y (by omega_arith)), rotr_rotl _ (by decide)]
  have vc : s.mem.readW (A V (cOff z)) 32 = v[z]'(by omega_arith) := (holds_c hz₁ hz).mp (h.vars z (by omega_arith))
  have vd : (s.gpr (wreg u)).rotateRight 8 = v[u]'hu := by
    rw [(holds_hi hu₁).mp (h.vars u hu), rotr_rotl _ (by decide)]
  rw [va, vb, vc, vd, hm _ sj, hm _ sk] at w
  have hwm : ∀ k, 8 ≤ k → k < 12 → k ≠ z →
      s'.mem.readW (A V (cOff k)) 32 = s.mem.readW (A V (cOff k)) 32 := fun k h1 h2 hk => by
    rw [w.mem, cOff_A fitV (by unfold cOff; omega_arith), cOff_A fitV (by unfold cOff; omega_arith)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by unfold cOff; omega_arith) (by unfold cOff; omega_arith)
      (by unfold cOff; omega_arith)) (by decide)
  refine ⟨fun k hk => ?_, by rw [w.other _ (Ne.symm nx.1) (Ne.symm ny.1) (Ne.symm nu.1) (by decide), h.r12],
    by rw [w.rd, h.rd], by rw [w.wr, h.wr], by rw [w.sp, h.sp], ?_⟩
  · rw [Proof.Blake2.G_get _ v (a := ⟨x, by omega_arith⟩) (b := ⟨y, by omega_arith⟩) (c := ⟨z, by omega_arith⟩) (d := ⟨u, hu⟩)
      (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by dsimp only; omega_arith) (by dsimp only; omega_arith)
      (by dsimp only; omega_arith) (by dsimp only; omega_arith) _ _ k hk]
    simp only [Fin.getElem_fin]
    by_cases ey : y = k
    · subst ey; simp only [↓reduceIte]; exact (holds_mid hy₁ hy).mpr w.rb
    by_cases ez : z = k
    · subst ez; simp only [ey, ↓reduceIte]
      exact (holds_c hz₁ hz).mpr (by rw [w.mem]; exact Mem.readW_writeW_self32 _ _ _)
    by_cases eu : u = k
    · subst eu; simp only [ey, ez, ↓reduceIte]; exact (holds_hi hu₁).mpr w.rdd
    by_cases ex : x = k
    · subst ex; simp only [ey, ez, eu, ↓reduceIte]; exact (holds_lo hx).mpr w.ra
    simp only [ey, ez, eu, ex, ↓reduceIte]
    have hv := h.vars k hk
    by_cases hc8 : 8 ≤ k ∧ k < 12
    · rw [holds_c hc8.1 hc8.2] at hv ⊢; rw [hwm k hc8.1 hc8.2 (Ne.symm ez), hv]
    · have hn : ∀ j < 16, ¬ (8 ≤ j ∧ j < 12) → j ≠ k → wreg k ≠ wreg j := fun j hj hj' hjk e =>
        hjk (wreg_inj k hk j hj hc8 hj' e).symm
      have ho : s'.gpr (wreg k) = s.gpr (wreg k) :=
        w.other _ (hn x (by omega_arith) (by omega_arith) ex) (hn y (by omega_arith) (by omega_arith) ey) (hn u hu (by omega_arith) eu)
          (wreg_ne k hk).2
      unfold Holds at hv ⊢
      split <;> [rw [ho]; skip] <;> rename_i h4 <;> simp only [h4, ↓reduceIte] at hv
      · exact hv
      split <;> [rw [ho]; skip] <;> rename_i h8 <;> simp only [h8, ↓reduceIte] at hv
      · exact hv
      simp only [show ¬ k < 12 by omega_arith, ↓reduceIte] at hv ⊢; rw [ho]; exact hv
  · rw [w.mem]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [cOff_A fitV (by unfold cOff; omega_arith)]
    exact Offset.contains _ (by unfold cOff; omega_arith) (by unfold cOff; omega_arith) (by omega_arith)

section
open VG.Spec.Blake2 (G sigmaAt s)

/-- A round, as the eight `G`s `round` runs. -/
theorem round_eq (M : Block 32) (v : Work 32) (r : Nat) :
    Spec.Blake2.round s M v r =
      G s (G s (G s (G s (G s (G s (G s (G s v
        ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨8, by decide⟩ ⟨12, by decide⟩ (M (sigmaAt r (2 * 0)))
          (M (sigmaAt r (2 * 0 + 1))))
        ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨9, by decide⟩ ⟨13, by decide⟩ (M (sigmaAt r (2 * 1)))
          (M (sigmaAt r (2 * 1 + 1))))
        ⟨2, by decide⟩ ⟨6, by decide⟩ ⟨10, by decide⟩ ⟨14, by decide⟩ (M (sigmaAt r (2 * 2)))
          (M (sigmaAt r (2 * 2 + 1))))
        ⟨3, by decide⟩ ⟨7, by decide⟩ ⟨11, by decide⟩ ⟨15, by decide⟩ (M (sigmaAt r (2 * 3)))
          (M (sigmaAt r (2 * 3 + 1))))
        ⟨0, by decide⟩ ⟨5, by decide⟩ ⟨10, by decide⟩ ⟨15, by decide⟩ (M (sigmaAt r (2 * 4)))
          (M (sigmaAt r (2 * 4 + 1))))
        ⟨1, by decide⟩ ⟨6, by decide⟩ ⟨11, by decide⟩ ⟨12, by decide⟩ (M (sigmaAt r (2 * 5)))
          (M (sigmaAt r (2 * 5 + 1))))
        ⟨2, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨13, by decide⟩ (M (sigmaAt r (2 * 6)))
          (M (sigmaAt r (2 * 6 + 1))))
        ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨9, by decide⟩ ⟨14, by decide⟩ (M (sigmaAt r (2 * 7)))
          (M (sigmaAt r (2 * 7 + 1))) := rfl

end

theorem round_ok (r : Nat) {V : BitVec 32} {M : Block 32} {s₀ s : State} {v : Work 32}
    (c : RCtx V M s₀) (h : RI V s₀ v s) :
    WP isa (round r) s (RI V s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  unfold round
  rw [round_eq]
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 4) (z := 8) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 0 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 5) (z := 9) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 1 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 6) (z := 10) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 2 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 3) (y := 7) (z := 11) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 3 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 0) (y := 5) (z := 10) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 4 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 1) (y := 6) (z := 11) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 5 c h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok (x := 2) (y := 7) (z := 8) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 6 c h) fun s h => ?_)
  exact WP.mono (gAt_ok (x := 3) (y := 4) (z := 9) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 7 c h) fun s h => h

theorem rounds_ok {V : BitVec 32} {M : Block 32} {s₀ : State} {v : Work 32} (c : RCtx V M s₀)
    (hv : ∀ k (hk : k < 16), Holds V s₀ k v[k]) (n : Nat) :
    WP isa (rounds n) s₀ (RI V s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil ⟨hv, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok n c hs

end VG.Proof.Blake2.ArmS

end

end


/-!
# BLAKE2s on ARMv7: one block

Setting up the work vector (`init_ok`): copying the block to `scratch`,
loading the state into registers and the IV words; and XORing the work vector
into the state (`fin_ok`).
-/

@[expose] public section

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Blake2.Arm.S (wreg cOff xOff stOff blkOff movImm ld lds ivC ivD ivCs ivDs copyMsg finX finHi finLo)
open VG.Proof.Sha512.Arm (A A_eq)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_ldr wp_str wp_mov op2_reg op2_imm)
open VG.Spec.Blake2 (Work Block HashValue)

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm d v ++ rest)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

end

/-! ## Copying the block -/

structure CInv (V B : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr V, 64⟩] s.mem s'.mem
  msg : ∀ j < n, s'.mem.readW (A V (4 * j)) 32 = s.mem.readW (A B (4 * j)) 32

theorem copyMsg_ok {V B : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (hB : s.gpr .r0 = B)
    (fitV : V.toNat + 512 ≤ 2 ^ 32) (fitB : B.toNat + 64 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4)
    (rB : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr) (A B o) 4)
    (hd : Region.Disjoint ⟨State.addr B, 64⟩ ⟨State.addr V, 64⟩) :
    ∀ n ≤ 16, WP isa (copyMsg n) s (CInv V B s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s₁ h₁ => ?_)
    simp only [Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
    refine wp_ldr (by omega_arith) (by rw [h₁.gpr _ (by decide), hB]) (by rw [h₁.rd, h₁.wr]; exact rB _ (by omega_arith))
      fun s₂ u₂ => ?_
    refine wp_str (by omega_arith) (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by omega_arith)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _
        (by rw [addr_add (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
    · have eB : State.addr (B + BitVec.ofNat 32 (4 * n)) = State.addr B + BitVec.ofNat 64 (4 * n) :=
        addr_add (by omega_arith)
      have eV : ∀ i, i < 16 → State.addr (V + BitVec.ofNat 32 (4 * i)) = State.addr V + BitVec.ofNat 64 (4 * i) :=
        fun i hi => addr_add (by omega_arith)
      show (s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (4 * j))) 32 =
        s.mem.readW (State.addr (B + BitVec.ofNat 32 (4 * j))) 32)
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e
        rw [Mem.readW_writeW_self32, eB]
        exact h₁.frame.readW (r := ⟨State.addr B, 64⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
      · rw [Mem.readW_writeW_sep (by
          rw [eV j (by omega_arith), eV n (by omega_arith)]
          exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact h₁.msg j (by omega_arith)

/-! ## Loading the state -/

/-- Word `k` (0–7) of the state `H` as `init` loads it: words 4–7 rotated left
by 7. -/
def ldv (H : Nat → BitVec 32) (k : Nat) : BitVec 32 := if k < 4 then H k else (H k).rotateLeft 7

theorem wreg_ne8 {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) : wreg j ≠ wreg k :=
  fun e => h (wreg_inj j (by omega_arith) k (by omega_arith) (by omega_arith) (by omega_arith) e)

structure LdInv (st : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, (∀ k < 8, r ≠ wreg k) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, s'.gpr (wreg k) = ldv (fun k => s.mem.readW (A st (4 * k)) 32) k

theorem lds_ok {st : BitVec 32} {s : State} (h11 : s.gpr .r11 = st)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4) :
    ∀ n ≤ 8, WP isa (lds n) s (LdInv st s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s₁ h₁ => ?_)
    have h11' : s₁.gpr .r11 = st := by rw [h₁.gpr _ (by decide), h11]
    have hfin : ∀ s₃ : State, Upd s₁ s₃ (wreg n)
        (ldv (fun k => s.mem.readW (A st (4 * k)) 32) n) → LdInv st s (n + 1) s₃ := fun s₃ u₃ =>
      ⟨fun r hr => by rw [u₃.other r (hr n (by omega_arith)), h₁.gpr r hr], by rw [u₃.mem, h₁.mem],
        by rw [u₃.rd, h₁.rd], by rw [u₃.wr, h₁.wr], by rw [u₃.sp, h₁.sp], fun k hk => by
          by_cases e : k = n
          · subst e; exact u₃.gpr
          · rw [u₃.other _ (wreg_ne8 (by omega_arith) (by omega_arith) e)]; exact h₁.vars k (by omega_arith)⟩
    simp only [ld]
    refine wp_ldr (by omega_arith) (by rw [h11']) (by rw [h₁.rd, h₁.wr]; exact rS _ (by omega_arith)) fun s₂ u₂ => ?_
    by_cases h4 : n < 4
    · simp only [h4, ↓reduceIte]
      exact WP.block_nil (hfin s₂ (by simpa only [ldv, h4, ↓reduceIte, h₁.mem] using u₂))
    · simp only [h4, ↓reduceIte]
      refine wp_mov (op2_ror (by decide)) fun s₃ u₃ => WP.block_nil (hfin s₃ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩)
      · rw [u₃.gpr, u₂.gpr, h₁.mem, rotr_eq_rotl _ (by decide) (by decide)]
        simp only [ldv, h4, ↓reduceIte]
      · rw [u₃.other r hr, u₂.other r hr]
      · rw [u₃.mem, u₂.mem]
      · rw [u₃.rd, u₂.rd]
      · rw [u₃.wr, u₂.wr]
      · rw [u₃.sp, u₂.sp]

/-! ## The IV words -/

structure CvInv (V : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [cR V] s.mem s'.mem
  c : ∀ j < n, s'.mem.readW (A V (cOff (j + 8))) 32 = Spec.Blake2.s.IV.toList.getD j 0

theorem ivCs_ok {V : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4) :
    ∀ n ≤ 4, WP isa (ivCs n) s (CvInv V s n) := by
  intro n hn
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega_arith)
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s₁ h₁ => ?_)
    simp only [ivC, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 8 - 8 = n by omega_arith]
    refine wp_movImm fun s₂ u₂ => wp_str (by unfold cOff; omega_arith)
      (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by unfold cOff; omega_arith)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · have hc : (cR V).Contains (State.addr (V + BitVec.ofNat 32 (cOff (n + 8)))) (32 / 8) := by
        rw [eV _ (by unfold cOff; omega_arith)]
        exact Offset.contains _ (by unfold cOff; omega_arith) (by unfold cOff; omega_arith) (by omega_arith)
      rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ hc
    · show s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (cOff (j + 8)))) 32 = _
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
          rw [eV _ (by unfold cOff; omega_arith), eV _ (by unfold cOff; omega_arith)]
          exact Offset.sep _ (by unfold cOff; omega_arith) (by unfold cOff; omega_arith) (by unfold cOff; omega_arith))
          (by decide)]
        exact h₁.c j (by omega_arith)

theorem wreg_hi_ne : ∀ j < 4, ∀ i < 4, wreg (j + 12) = wreg (i + 12) → j = i := by decide
theorem wreg_hi_ne' : ∀ j < 4, wreg (j + 12) ≠ .lr ∧ wreg (j + 12) ≠ .r12 := by decide

structure DvInv (V : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .lr → (∀ j < 4, r ≠ wreg (j + 12)) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ j < n, s'.gpr (wreg (j + 12)) =
    (Spec.Blake2.s.IV.toList.getD (j + 4) 0 ^^^ s.mem.readW (A V (xOff (j + 12))) 32).rotateLeft 8

theorem ivDs_ok {V : BitVec 32} {s : State} (hV : s.gpr .r12 = V)
    (rV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4) :
    ∀ n ≤ 4, WP isa (ivDs n) s (DvInv V s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_arith)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_arith)) fun s₁ h₁ => ?_)
    have hw := wreg_hi_ne' n (by omega_arith)
    simp only [ivD, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 12 - 8 = n + 4 by omega_arith]
    refine wp_movImm fun s₂ u₂ => ?_
    refine wp_ldr (by unfold xOff; omega_arith) (by
        rw [u₂.other _ (Ne.symm hw.2), h₁.gpr _ (by decide) (by decide), hV])
      (by rw [u₂.rd, u₂.wr, h₁.rd, h₁.wr]; exact rV _ (by unfold xOff; omega_arith)) fun s₃ u₃ => ?_
    refine wp_eor (op2_ror (by decide)) fun s₄ u₄ => WP.block_nil ?_
    refine ⟨fun r h1 h2 => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, h₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp], fun j hj => ?_⟩
    · rw [u₄.other r (h2 n (by omega_arith)), u₃.other r h1, u₂.other r (h2 n (by omega_arith)), h₁.gpr r h1 h2]
    · by_cases e : j = n
      · subst e
        rw [u₄.gpr, u₃.other _ hw.1, u₂.gpr, u₃.gpr, u₂.mem, h₁.mem, rotr_eq_rotl _ (by decide) (by decide),
          rotl_xor]
      · have hne : wreg (j + 12) ≠ wreg (n + 12) := fun h => e (wreg_hi_ne j (by omega_arith) n (by omega_arith) h)
        rw [u₄.other _ hne, u₃.other _ (wreg_hi_ne' j (by omega_arith)).1, u₂.other _ hne]
        exact h₁.vars j (by omega_arith)

/-! ## Setting up the work vector -/

/-- A word of `scratch` outside the regions a frame allows to change. -/
theorem scr_word {V : BitVec 32} (fitV : V.toNat + 512 ≤ 2 ^ 32) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hd : d + 4 ≤ 512)
    (hdis : ∀ r ∈ rs, Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r) :
    m'.readW (A V d) 32 = m.readW (A V d) 32 := by
  rw [cOff_A fitV (by omega_arith)]; exact hf.readW (Region.contains_self _ _) hdis (by decide)

/-- The words `init` sets up, from the state words `H` and the words `X` of
`scratch` XORed into words 12–15. -/
def initW (H X : Nat → BitVec 32) (k : Nat) : BitVec 32 :=
  if k < 8 then H k else if k < 12 then Spec.Blake2.s.IV.toList.getD (k - 8) 0
  else Spec.Blake2.s.IV.toList.getD (k - 8) 0 ^^^ X k

/-- The regions of `scratch` that `init` writes. -/
abbrev initR (V : BitVec 32) : List Region :=
  [⟨State.addr V, 80⟩, ⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩]

structure IOut (V st B : BitVec 32) (s s' : State) : Prop where
  r12 : s'.gpr .r12 = V
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (initR V) s.mem s'.mem
  blk : s'.mem.readW (A V blkOff) 32 = B + 64
  msg : ∀ j < 16, s'.mem.readW (A V (4 * j)) 32 = s.mem.readW (A B (4 * j)) 32
  vars : ∀ k < 16, Holds V s' k (initW (fun k => s.mem.readW (A st (4 * k)) 32)
    (fun k => s.mem.readW (A V (xOff k)) 32) k)

theorem init_ok {V st B : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (fitS : st.toNat + 32 ≤ 2 ^ 32) (fitB : B.toNat + 64 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4)
    (rB : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr) (A B o) 4)
    (hst : s.mem.readW (A V stOff) 32 = st) (hblk : s.mem.readW (A V blkOff) 32 = B)
    (hdB : Region.Disjoint ⟨State.addr B, 64⟩ ⟨State.addr V, 64⟩)
    (hdS : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr V, 512⟩) :
    WP isa Impl.Blake2.Arm.S.init s (IOut V st B s) := by
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega_arith)
  have rV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := wV o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  -- The regions `init` writes, and what lies outside them.
  have sub64 : ∀ r ∈ [(⟨State.addr V, 64⟩ : Region)], ∃ r' ∈ initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
  have subC : ∀ r ∈ [cR V], ∃ r' ∈ initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
  have hBlk : (⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ : Region).Contains
      (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
    rw [eV _ (by decide)]; exact Region.contains_self _ _
  have outR : ∀ d, 88 ≤ d → d + 4 ≤ 512 → ∀ r ∈ initR V,
      Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r := fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by simp only [blkOff]; omega_arith) (by omega_arith) (by simp only [blkOff]; omega_arith)
  have stR : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr V, 512⟩) → ∀ {m m' : Mem},
      Frame rs m m' → ∀ k < 8, m'.readW (A st (4 * k)) 32 = m.readW (A st (4 * k)) 32 :=
    fun hs m m' hf k hk => by
      rw [A_eq (by omega_arith)]
      exact hf.readW (r := ⟨State.addr st, 32⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
        (fun r hr => hdS.sub_right (hs r hr)) (by decide)
  unfold Impl.Blake2.Arm.S.init
  simp only [Impl.Blake2.Arm.S.S]
  refine WP.seq (wp_ldr (by decide) (by rw [hV]) (rV _ (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have hB₁ : s₁.gpr .r0 = B := by rw [u₁.gpr]; exact hblk
  have V₁ : s₁.gpr .r12 = V := by rw [u₁.other _ (by decide), hV]
  refine WP.seq (WP.mono (copyMsg_ok V₁ hB₁ fitV fitB (by rw [u₁.wr]; exact wV) (by rw [u₁.rd, u₁.wr]; exact rB)
    hdB 16 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have V₂ : s₂.gpr .r12 = V := by rw [h₂.gpr _ (by decide), V₁]
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_str (by decide)
    (by rw [u₃.other _ (by decide), V₂]) (by rw [u₃.wr, h₂.wr, u₁.wr]; exact wV _ (by decide))
    fun s₄ m₄ => wp_ldr (by decide) (by rw [m₄.gpr, u₃.other _ (by decide), V₂])
    (by rw [m₄.rd, m₄.wr, u₃.rd, u₃.wr, h₂.rd, h₂.wr, u₁.rd, u₁.wr]; exact rV _ (by decide))
    fun s₅ u₅ => WP.block_nil ?_)
  have f₄ : Frame (initR V) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, ← u₁.mem]
    exact (h₂.frame.sub sub64).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ hBlk
  have h11 : s₅.gpr .r11 = st := by
    rw [u₅.gpr, ← hst]
    exact scr_word fitV f₄ (d := stOff) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, m₄.rd, u₃.rd, h₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, m₄.wr, u₃.wr, h₂.wr, u₁.wr]
  have V₅ : s₅.gpr .r12 = V := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), V₂]
  refine WP.seq (WP.mono (lds_ok h11 (by rw [rd₅, wr₅]; exact rS) 8 (Nat.le_refl _)) fun s₆ h₆ => ?_)
  have V₆ : s₆.gpr .r12 = V := by rw [h₆.gpr _ (by decide), V₅]
  refine WP.seq (WP.mono (ivCs_ok V₆ fitV (by rw [h₆.wr, wr₅]; exact wV) 4 (Nat.le_refl _)) fun s₇ h₇ => ?_)
  have V₇ : s₇.gpr .r12 = V := by rw [h₇.gpr _ (by decide), V₆]
  refine WP.mono (ivDs_ok V₇ (by rw [h₇.rd, h₇.wr, h₆.rd, h₆.wr, rd₅, wr₅]; exact rV) 4 (Nat.le_refl _))
    fun s₈ h₈ => ?_
  have f₈ : Frame (initR V) s.mem s₈.mem := by
    rw [h₈.mem]; exact (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
  refine ⟨by rw [h₈.gpr _ (by decide) (by decide), V₇], by rw [h₈.rd, h₇.rd, h₆.rd, rd₅],
    by rw [h₈.wr, h₇.wr, h₆.wr, wr₅], ?_, f₈, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · rw [h₈.sp, h₇.sp, h₆.sp, u₅.sp, m₄.sp, u₃.sp, h₂.sp, u₁.sp]
  · -- The block pointer.
    have hd : ∀ r ∈ [cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    rw [h₈.mem, scr_word fitV h₇.frame (by decide) hd, h₆.mem, m₅]
    show s₄.mem.readW (State.addr (V + BitVec.ofNat 32 blkOff)) 32 = _
    rw [m₄.mem, Mem.readW_writeW_self32, u₃.gpr, h₂.gpr _ (by decide), hB₁]
  · -- The message words.
    have hd : ∀ r ∈ [cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 (4 * j), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    have hsep : Mem.Sep (State.addr V + BitVec.ofNat 64 (4 * j)) (32 / 8)
        (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
      rw [eV _ (by decide)]
      exact Offset.sep _ (by simp only [blkOff]; omega_arith) (by omega_arith) (by simp only [blkOff]; omega_arith)
    rw [h₈.mem, scr_word fitV h₇.frame (by omega_arith) hd, h₆.mem, m₅, m₄.mem,
      show (A V (4 * j)) = State.addr V + BitVec.ofNat 64 (4 * j) from eV _ (by omega_arith),
      Mem.readW_writeW_sep hsep (by decide), u₃.mem, ← eV _ (by omega_arith), h₂.msg j hj, u₁.mem]
  · -- The work vector.
    have hS₅ : ∀ i < 8, s₅.mem.readW (A st (4 * i)) 32 = s.mem.readW (A st (4 * i)) 32 := fun i hi =>
      stR (rs := initR V) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by omega_arith)
        · exact Offset.sub_base _ (by simp only [blkOff]; omega_arith)) (by rw [m₅]; exact f₄) i hi
    have hX : ∀ i, 88 ≤ xOff i → xOff i + 4 ≤ 512 →
        s₇.mem.readW (A V (xOff i)) 32 = s.mem.readW (A V (xOff i)) 32 := fun i h1 h2 => by
      have f₇ : Frame (initR V) s.mem s₇.mem :=
        (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
      exact scr_word fitV f₇ h2 (outR _ h1 h2)
    have hr : ∀ i < 8, s₈.gpr (wreg i) = s₆.gpr (wreg i) := fun i hi => by
      rw [h₈.gpr _ (wreg_ne i (by omega_arith)).2 (fun j hj e => absurd
        (wreg_inj i (by omega_arith) (j + 12) (by omega_arith) (by omega_arith) (by omega_arith) e) (by omega_arith)),
        h₇.gpr _ (wreg_ne i (by omega_arith)).2]
    unfold Holds initW
    by_cases h4 : k < 4
    · simp only [h4, ↓reduceIte, show k < 8 by omega_arith]
      rw [hr k (by omega_arith), h₆.vars k (by omega_arith)]
      simp only [ldv, h4, ↓reduceIte]; exact hS₅ k (by omega_arith)
    by_cases h8 : k < 8
    · simp only [h4, h8, ↓reduceIte]
      rw [hr k h8, h₆.vars k h8]
      simp only [ldv, h4, ↓reduceIte]; rw [hS₅ k h8]
    by_cases h12 : k < 12
    · simp only [h4, h8, h12, ↓reduceIte]
      rw [h₈.mem]
      have := h₇.c (k - 8) (by omega_arith)
      rwa [show k - 8 + 8 = k by omega_arith] at this
    · simp only [h4, h8, h12, ↓reduceIte]
      have := h₈.vars (k - 12) (by omega_arith)
      rw [show k - 12 + 12 = k by omega_arith, show k - 12 + 4 = k - 8 by omega_arith] at this
      rw [this, hX k (by unfold xOff; omega_arith) (by unfold xOff; omega_arith)]

/-! ## XORing the work vector into the state -/

/-- What `fin` needs of the state `s₀` at its start: the state at `st` and
the scratch space at `V`, holding words 8–11 of the work vector `v`. -/
structure FCtx (V st : BitVec 32) (v : Work 32) (s₀ : State) : Prop where
  fitS : st.toNat + 32 ≤ 2 ^ 32
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wS : ∀ o, o + 4 ≤ 32 → InRegions s₀.wr (A st o) 4
  rV : ∀ o, o + 4 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (A V o) 4
  c : ∀ k (hk : k < 4), s₀.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8]'(by omega_arith)
  disj : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr V, 512⟩

/-- The invariant of `fin`, from `s₀`, with the words `D` of the state done. -/
structure FI (V st : BitVec 32) (H : Nat → BitVec 32) (v : Work 32) (s₀ : State) (D : List Nat)
    (s : State) : Prop where
  r8 : s.gpr .r8 = st
  r12 : s.gpr .r12 = V
  r9 : s.gpr .r9 = s₀.mem.readW (A V blkOff) 32
  r10 : s.gpr .r10 = s₀.mem.readW (A V Impl.Blake2.Arm.S.nOff) 32
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr st, 32⟩] s₀.mem s.mem
  lo : ∀ k (hk : k < 4), k ∉ D → s.gpr (wreg k) = v[k]'(by omega_arith)
  mid : ∀ k (hk : k < 4), s.gpr (wreg (k + 4)) = (v[k + 4]'(by omega_arith) ^^^ v[k + 4 + 8]'(by omega_arith)).rotateLeft 7
  words : ∀ k (hk : k < 8), s.mem.readW (A st (4 * k)) 32 =
    if k ∈ D then H k ^^^ (v[k]'(by omega_arith) ^^^ v[k + 8]'(by omega_arith)) else H k

theorem wreg_lo_ne : ∀ k < 8, wreg k ≠ .lr ∧ wreg k ≠ .r8 ∧ wreg k ≠ .r12 := by decide
theorem wreg_lo_ne' : ∀ k < 4, wreg k ≠ .r9 ∧ wreg k ≠ .r10 := by decide

theorem FI.st_addr {V st : BitVec 32} {v : Work 32} {s₀ : State} (c : FCtx V st v s₀) {k : Nat} (hk : k < 8) :
    State.addr (st + BitVec.ofNat 32 (4 * k)) = State.addr st + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := c.fitS; omega_arith)

theorem FI.words_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) (h : FI V st H v s₀ D s) {j : Nat} (hj : j < 8) {m : Mem}
    (hm : m = s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) (H j ^^^ (v[j]'(by omega_arith) ^^^ v[j + 8]'(by omega_arith)))) :
    ∀ k (hk : k < 8), m.readW (A st (4 * k)) 32 =
      if k ∈ j :: D then H k ^^^ (v[k]'(by omega_arith) ^^^ v[k + 8]'(by omega_arith)) else H k := fun k hk => by
  subst hm
  show (s.mem.writeW _ _).readW (State.addr (st + BitVec.ofNat 32 (4 * k))) 32 = _
  by_cases e : k = j
  · subst e; simp only [List.mem_cons_self, ↓reduceIte]; exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (by
      rw [FI.st_addr c hk, FI.st_addr c hj]; exact Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    simp only [List.mem_cons, e, false_or]; exact h.words k hk

theorem FI.frame_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) (h : FI V st H v s₀ D s) {j : Nat} (hj : j < 8) (x : BitVec 32) :
    Frame [⟨State.addr st, 32⟩] s₀.mem (s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) x) :=
  h.frame.writeW (List.mem_singleton_self _) _ (by
    rw [FI.st_addr c hj]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem finHi_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k + 4 ∉ D) (h : FI V st H v s₀ D s) :
    WP isa (.block (finHi (k + 4))) s (FI V st H v s₀ ((k + 4) :: D)) := by
  have nw := wreg_lo_ne (k + 4) (by omega_arith)
  simp only [finHi, Impl.Blake2.Arm.S.T]
  refine wp_ldr (by omega_arith) (by rw [h.r8]) (by
      rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega_arith); ⟨r, List.mem_append_right _ hr, hc⟩)
    fun s₁ u₁ => wp_eor (op2_ror (by decide)) fun s₂ u₂ => wp_str (by omega_arith)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
      (by rw [u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega_arith)) fun s₃ m₃ => WP.block_nil ?_
  have hv : s₂.gpr .lr = H (k + 4) ^^^ (v[k + 4]'(by omega_arith) ^^^ v[k + 4 + 8]'(by omega_arith)) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ nw.1, h.mid k hk, rotr_rotl _ (by decide)]
    have := h.words (k + 4) (by omega_arith)
    simp only [hD, ↓reduceIte] at this
    rw [← this]
  refine ⟨by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r8],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r12],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r9],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r10],
    by rw [m₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₃.wr, u₂.wr, u₁.wr, h.wr], by rw [m₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega_arith) _, fun j hj hjD => ?_, fun j hj => ?_,
    h.words_upd c (j := k + 4) (by omega_arith) (by rw [m₃.mem, hv, u₂.mem, u₁.mem])⟩
  · have := wreg_lo_ne j (by omega_arith)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have := wreg_lo_ne (j + 4) (by omega_arith)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.mid j hj]

theorem finLo_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k ∉ D) (h : FI V st H v s₀ D s) :
    WP isa (.block (finLo k)) s (FI V st H v s₀ (k :: D)) := by
  have nw := wreg_lo_ne k (by omega_arith)
  have iS : InRegions (s.rd ++ s.wr) (A st (4 * k)) 4 := by
    rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega_arith); ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [finLo, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
  refine wp_ldr (by unfold cOff; omega_arith) (by rw [h.r12]) (by rw [h.rd, h.wr]; exact c.rV _ (by unfold cOff; omega_arith))
    fun s₁ u₁ => wp_eor (op2_reg _ _) fun s₂ u₂ => wp_ldr (by omega_arith)
      (by rw [u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide), h.r8]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact iS)
      fun s₃ u₃ => wp_eor (op2_reg _ _) fun s₄ u₄ => wp_str (by omega_arith)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
        h.r8])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega_arith)) fun s₅ m₅ => WP.block_nil ?_
  have hc : s.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8]'(by omega_arith) := by
    rw [← c.c k hk, cOff_A c.fitV (by unfold cOff; omega_arith)]
    exact h.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (c.disj.sub_right (Offset.sub_base _ (by unfold cOff; omega_arith))).symm) (by decide)
  have hw : s₃.gpr (wreg k) = v[k]'(by omega_arith) ^^^ v[k + 8]'(by omega_arith) := by
    rw [u₃.other _ nw.1, u₂.gpr, u₁.other _ nw.1, h.lo k hk hD, u₁.gpr]
    exact congrArg _ hc
  have hv : s₄.gpr .lr = H k ^^^ (v[k]'(by omega_arith) ^^^ v[k + 8]'(by omega_arith)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₁.mem, hw]
    have := h.words k (by omega_arith)
    simp only [hD, ↓reduceIte] at this
    exact congrArg (· ^^^ _) this
  have n9 := wreg_lo_ne' k hk
  refine ⟨?_, ?_, by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.1),
      u₁.other _ (by decide), h.r9],
    by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.2),
      u₁.other _ (by decide), h.r10], by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega_arith) _, fun j hj hjD => ?_,
    fun j hj => ?_, h.words_upd c (j := k) (by omega_arith) (by rw [m₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem])⟩
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
      h.r8]
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.2), u₁.other _ (by decide),
      h.r12]
  · have nj := wreg_lo_ne j (by omega_arith)
    have ne : wreg j ≠ wreg k := wreg_ne8 (by omega_arith) (by omega_arith) fun e => hjD (e ▸ List.mem_cons_self)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1,
      h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have nj := wreg_lo_ne (j + 4) (by omega_arith)
    have ne : wreg (j + 4) ≠ wreg k := wreg_ne8 (by omega_arith) (by omega_arith) (by omega_arith)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1, h.mid j hj]

theorem finPre_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : FCtx V st v s)
    (hv : ∀ k (hk : k < 16), Holds V s k (v[k]'(by omega_arith))) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa (.block (finX 4 ++ finX 5 ++ finX 6 ++ finX 7 ++ ([.ldr .r8 Impl.Blake2.Arm.S.S stOff,
      .ldr .r9 Impl.Blake2.Arm.S.S blkOff, .ldr .r10 Impl.Blake2.Arm.S.S Impl.Blake2.Arm.S.nOff] : List Instr))) s
      (FI V st (fun k => s.mem.readW (A st (4 * k)) 32) v s []) := by
  simp only [finX, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine wp_eor (op2_ror (by decide)) fun s₁ u₁ => wp_eor (op2_ror (by decide)) fun s₂ u₂ =>
    wp_eor (op2_ror (by decide)) fun s₃ u₃ => wp_eor (op2_ror (by decide)) fun s₄ u₄ => ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have V₄ : s₄.gpr .r12 = V := by simp (disch := decide) only [u₄.other, u₃.other, u₂.other, u₁.other, hV]
  refine wp_ldr (a := A V stOff) (by decide) (by rw [V₄]) (by rw [rd₄, wr₄]; exact c.rV _ (by decide))
    fun s₅ u₅ => wp_ldr (a := A V blkOff) (by decide) (by rw [u₅.other _ (by decide), V₄])
    (by rw [u₅.rd, u₅.wr, rd₄, wr₄]; exact c.rV _ (by decide))
    fun s₆ u₆ => wp_ldr (a := A V Impl.Blake2.Arm.S.nOff) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), V₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, rd₄, wr₄]; exact c.rV _ (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, m₄]
  have mid : ∀ k (hk : k < 4), s.gpr (wreg (k + 4)) ^^^ (s.gpr (wreg (k + 4 + 8))).rotateRight 1 =
      (v[k + 4]'(by omega_arith) ^^^ v[k + 4 + 8]'(by omega_arith)).rotateLeft 7 := fun k hk => by
    rw [(holds_mid (by omega_arith) (by omega_arith)).mp (hv (k + 4) (by omega_arith)),
      (holds_hi (by omega_arith)).mp (hv (k + 4 + 8) (by omega_arith)), rotl8_rotr1, rotl_xor]
  refine ⟨by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, m₄]; exact hst,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), V₄],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, m₄],
    by rw [u₇.gpr, u₆.mem, u₅.mem, m₄],
    by rw [u₇.rd, u₆.rd, u₅.rd, rd₄], by rw [u₇.wr, u₆.wr, u₅.wr, wr₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [m₇]; exact Frame.refl _ _,
    fun k hk _ => ?_, fun k hk => ?_, fun k hk => by rw [m₇]; rfl⟩
  · have e := (holds_lo hk).mp (hv k (by omega_arith))
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
      exact e
  · have e := mid k hk
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other]
      exact e

theorem fin_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : FCtx V st v s)
    (hv : ∀ k (hk : k < 16), Holds V s k (v[k]'(by omega_arith))) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa Impl.Blake2.Arm.S.fin s fun s' =>
      s'.gpr .r12 = V ∧ s'.gpr .r8 = st ∧ s'.gpr .r9 = s.mem.readW (A V blkOff) 32 ∧
      s'.gpr .r10 = s.mem.readW (A V Impl.Blake2.Arm.S.nOff) 32 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr st, 32⟩] s.mem s'.mem ∧
      ∀ k (hk : k < 8), s'.mem.readW (A st (4 * k)) 32 =
        s.mem.readW (A st (4 * k)) 32 ^^^ (v[k]'(by omega_arith) ^^^ v[k + 8]'(by omega_arith)) := by
  unfold Impl.Blake2.Arm.S.fin
  refine WP.seq (WP.mono (finPre_ok c hv hV hst) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 0) c (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 1) c (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 2) c (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (finHi_ok (k := 3) c (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 0) c (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 1) c (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (finLo_ok (k := 2) c (by decide) (by decide) h₇) fun s₈ h₈ => ?_)
  refine WP.mono (finLo_ok (k := 3) c (by decide) (by decide) h₈) fun s₉ h₉ => ?_
  refine ⟨h₉.r12, h₉.r8, h₉.r9, h₉.r10, h₉.rd, h₉.wr, h₉.sp, h₉.frame, fun k hk => ?_⟩
  rw [h₉.words k hk]
  have : k ∈ [3, 2, 1, 0, 0 + 4 + 3 - 3 + 3, 2 + 4, 1 + 4, 0 + 4] := by
    rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [this, ↓reduceIte]

end VG.Proof.Blake2.ArmS
