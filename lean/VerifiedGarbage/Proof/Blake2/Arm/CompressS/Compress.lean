import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Blake2.Arm.CompressS
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Arm.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.CompressS.Rounds`. -/
section

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
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

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
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

theorem rotr_rotl (x : BitVec 32) {k : Nat} (hk : k < 32) : (x.rotateLeft k).rotateRight k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

theorem rotr_eq_rotl (x : BitVec 32) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateRight k = x.rotateLeft (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk',
    Nat.mod_eq_of_lt (show 32 - k < 32 by omega)]
  split <;> (try split) <;> (try simp_all) <;> first | rfl | omega | (congr 1; omega)

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
      simp [h1, h2, h3, hi, show 1 + i < 32 by omega] <;> first | omega | (congr 1; omega)
  · by_cases h2 : i - (32 - 1) < 8 <;> by_cases h3 : i < 7 <;> simp [h1, h2, h3, hi] <;>
      first | omega | (congr 1; omega)

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
    (K : ∀ s', VG.Proof.Blake2.ArmS.GOut a b d V c s s' (Proof.Blake2.mix Spec.Blake2.s (s.gpr a) ((s.gpr b).rotateRight 7)
      (s.mem.readW (A V (cOff c)) 32) ((s.gpr d).rotateRight 8) (s.mem.readW (A V (4 * x)) 32)
      (s.mem.readW (A V (4 * y)) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (g a b d c x y ++ rest)) s Q := by
  have iC : InRegions (s.rd ++ s.wr) (A V (cOff c)) 4 :=
    let ⟨r, hr, h⟩ := oC; ⟨r, List.mem_append_right _ hr, h⟩
  simp only [g, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine wp_ldr hx (by rw [hV]) iX fun s₁ u₁ => ?_
  refine wp_add (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₄ u₄ => ?_
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
  refine wp_add (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₈ u₈ => ?_
  refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₉ u₉ => ?_
  refine wp_add (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₁₀ u₁₀ => ?_
  refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_add (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₁₂ u₁₂ => ?_
  refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₁₃ u₁₃ => ?_
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
  rw [VG.Proof.Blake2.ArmS.mix_s]
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₁₄.gpr, a13, a10, a6, f9, c8, e4, a3]
  · rw [m₁₄.gpr, f13, c12, f9, c8, e11, a10, a6, f9, c8, e4, a3, VG.Proof.Blake2.ArmS.rotl_rotr _ (by decide)]
  · rw [m₁₄.gpr, d13, e11, a10, a6, f9, c8, e4, a3, VG.Proof.Blake2.ArmS.rotl_rotr _ (by decide)]
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
    VG.Proof.Blake2.ArmS.Holds V s k x ↔ s.gpr (wreg k) = x := by simp only [VG.Proof.Blake2.ArmS.Holds, h, ↓reduceIte]

theorem holds_mid {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 4 ≤ k) (h₂ : k < 8) :
    VG.Proof.Blake2.ArmS.Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 7 := by
  simp only [VG.Proof.Blake2.ArmS.Holds, show ¬ k < 4 by omega, h₂, ↓reduceIte]

theorem holds_c {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 8 ≤ k) (h₂ : k < 12) :
    VG.Proof.Blake2.ArmS.Holds V s k x ↔ s.mem.readW (A V (cOff k)) 32 = x := by
  simp only [VG.Proof.Blake2.ArmS.Holds, show ¬ k < 4 by omega, show ¬ k < 8 by omega, h₂, ↓reduceIte]

theorem holds_hi {V : BitVec 32} {s : State} {k : Nat} {x : BitVec 32} (h₁ : 12 ≤ k) :
    VG.Proof.Blake2.ArmS.Holds V s k x ↔ s.gpr (wreg k) = x.rotateLeft 8 := by
  simp only [VG.Proof.Blake2.ArmS.Holds, show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ↓reduceIte]

/-- Words 8–11 of the work vector, in `scratch[64, 80)`. -/
abbrev cR (V : BitVec 32) : Region := ⟨State.addr V + BitVec.ofNat 64 64, 16⟩

/-- What the rounds need of the state `s₀` at their start: the scratch space
at `V` (in `r12`), holding the message block `M` in its first 64 bytes. -/
structure RCtx (V : BitVec 32) (M : VG.Spec.Blake2.Block 32) (s₀ : State) : Prop where
  r12 : s₀.gpr .r12 = V
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wV : ∀ o, o + 4 ≤ 512 → InRegions s₀.wr (A V o) 4
  msg : ∀ j (hj : j < 16), s₀.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩

/-- The rounds invariant, relative to the state `s₀` at their start: the work
vector is `v`, and nothing else has changed but `lr`, `r0`–`r11` and
`scratch[64, 80)`. -/
structure RI (V : BitVec 32) (s₀ : State) (v : Work 32) (s : State) : Prop where
  vars : ∀ k (hk : k < 16), VG.Proof.Blake2.ArmS.Holds V s k v[k]
  r12 : s.gpr .r12 = s₀.gpr .r12
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Blake2.ArmS.cR V] s₀.mem s.mem

theorem wreg_ne : ∀ k < 16, wreg k ≠ .r12 ∧ wreg k ≠ .lr := by decide

theorem wreg_inj' : ∀ k < 16, ∀ j < 16, wreg k = wreg j → k = j ∨ (8 ≤ k ∧ k < 12) ∨ (8 ≤ j ∧ j < 12) := by
  decide

theorem wreg_inj (k : Nat) (hk : k < 16) (j : Nat) (hj : j < 16) (h₁ : ¬ (8 ≤ k ∧ k < 12))
    (h₂ : ¬ (8 ≤ j ∧ j < 12)) (e : wreg k = wreg j) : k = j := by
  rcases VG.Proof.Blake2.ArmS.wreg_inj' k hk j hj e with h | h | h
  · exact h
  · exact absurd h h₁
  · exact absurd h h₂

theorem cOff_A {V : BitVec 32} (fit : V.toNat + 512 ≤ 2 ^ 32) {o : Nat} (ho : o < 512) :
    A V o = State.addr V + BitVec.ofNat 64 o := A_eq (by omega)

theorem gAt_ok {x y z u : Nat} (hx : x < 4) (hy₁ : 4 ≤ y) (hy : y < 8) (hz₁ : 8 ≤ z) (hz : z < 12)
    (hu₁ : 12 ≤ u) (hu : u < 16) (r i : Nat) {V : BitVec 32} {M : VG.Spec.Blake2.Block 32} {s₀ s : State}
    {v : Work 32} (c : VG.Proof.Blake2.ArmS.RCtx V M s₀) (h : VG.Proof.Blake2.ArmS.RI V s₀ v s) :
    WP isa (gAt r i x y z u) s (VG.Proof.Blake2.ArmS.RI V s₀ (Spec.Blake2.G Spec.Blake2.s v ⟨x, by omega⟩ ⟨y, by omega⟩
      ⟨z, by omega⟩ ⟨u, hu⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  have fitV := c.fitV
  have nx := VG.Proof.Blake2.ArmS.wreg_ne x (by omega)
  have ny := VG.Proof.Blake2.ArmS.wreg_ne y (by omega)
  have nu := VG.Proof.Blake2.ArmS.wreg_ne u (by omega)
  have ixy : wreg x ≠ wreg y := fun e => absurd (VG.Proof.Blake2.ArmS.wreg_inj x (by omega) y (by omega) (by omega) (by omega) e)
    (by omega)
  have ixu : wreg x ≠ wreg u := fun e => absurd (VG.Proof.Blake2.ArmS.wreg_inj x (by omega) u (by omega) (by omega) (by omega) e)
    (by omega)
  have iyu : wreg y ≠ wreg u := fun e => absurd (VG.Proof.Blake2.ArmS.wreg_inj y (by omega) u (by omega) (by omega) (by omega) e)
    (by omega)
  have hcz : cOff z < 4096 := by unfold cOff; omega
  have hV : s.gpr .r12 = V := by rw [h.r12, c.r12]
  -- The message words are unchanged.
  have hm : ∀ j (hj : j < 16), s.mem.readW (A V (4 * j)) 32 = M ⟨j, hj⟩ := fun j hj => by
    rw [← c.msg j hj, VG.Proof.Blake2.ArmS.cOff_A fitV (by omega)]
    refine h.frame.readW (r := ⟨State.addr V, 64⟩) (Offset.contains_base _ (by omega) (by omega)) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have iV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := c.wV o ho; ⟨r, List.mem_append_right _ (by rw [h.wr]; exact hr), hc⟩
  unfold gAt
  rw [← List.append_nil (g _ _ _ _ _ _)]
  refine VG.Proof.Blake2.ArmS.wp_g ixy ixu iyu nx.1 ny.1 nu.1 nx.2 ny.2 nu.2 hcz (by omega) (by omega) hV
    (iV _ (by omega)) (iV _ (by omega)) (by rw [h.wr]; exact c.wV _ (by unfold cOff; omega))
    fun s' w => WP.block_nil ?_
  have va : s.gpr (wreg x) = v[x]'(by omega) := (VG.Proof.Blake2.ArmS.holds_lo hx).mp (h.vars x (by omega))
  have vb : (s.gpr (wreg y)).rotateRight 7 = v[y]'(by omega) := by
    rw [(VG.Proof.Blake2.ArmS.holds_mid hy₁ hy).mp (h.vars y (by omega)), VG.Proof.Blake2.ArmS.rotr_rotl _ (by decide)]
  have vc : s.mem.readW (A V (cOff z)) 32 = v[z]'(by omega) := (VG.Proof.Blake2.ArmS.holds_c hz₁ hz).mp (h.vars z (by omega))
  have vd : (s.gpr (wreg u)).rotateRight 8 = v[u]'hu := by
    rw [(VG.Proof.Blake2.ArmS.holds_hi hu₁).mp (h.vars u hu), VG.Proof.Blake2.ArmS.rotr_rotl _ (by decide)]
  rw [va, vb, vc, vd, hm _ sj, hm _ sk] at w
  have hwm : ∀ k, 8 ≤ k → k < 12 → k ≠ z →
      s'.mem.readW (A V (cOff k)) 32 = s.mem.readW (A V (cOff k)) 32 := fun k h1 h2 hk => by
    rw [w.mem, VG.Proof.Blake2.ArmS.cOff_A fitV (by unfold cOff; omega), VG.Proof.Blake2.ArmS.cOff_A fitV (by unfold cOff; omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by unfold cOff; omega) (by unfold cOff; omega)
      (by unfold cOff; omega)) (by decide)
  refine ⟨fun k hk => ?_, by rw [w.other _ (Ne.symm nx.1) (Ne.symm ny.1) (Ne.symm nu.1) (by decide), h.r12],
    by rw [w.rd, h.rd], by rw [w.wr, h.wr], by rw [w.sp, h.sp], ?_⟩
  · rw [Proof.Blake2.G_get _ v (a := ⟨x, by omega⟩) (b := ⟨y, by omega⟩) (c := ⟨z, by omega⟩) (d := ⟨u, hu⟩)
      (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega) (by dsimp only; omega) _ _ k hk]
    simp only [Fin.getElem_fin]
    by_cases ey : y = k
    · subst ey; simp only [↓reduceIte]; exact (VG.Proof.Blake2.ArmS.holds_mid hy₁ hy).mpr w.rb
    by_cases ez : z = k
    · subst ez; simp only [ey, ↓reduceIte]
      exact (VG.Proof.Blake2.ArmS.holds_c hz₁ hz).mpr (by rw [w.mem]; exact Mem.readW_writeW_self32 _ _ _)
    by_cases eu : u = k
    · subst eu; simp only [ey, ez, ↓reduceIte]; exact (VG.Proof.Blake2.ArmS.holds_hi hu₁).mpr w.rdd
    by_cases ex : x = k
    · subst ex; simp only [ey, ez, eu, ↓reduceIte]; exact (VG.Proof.Blake2.ArmS.holds_lo hx).mpr w.ra
    simp only [ey, ez, eu, ex, ↓reduceIte]
    have hv := h.vars k hk
    by_cases hc8 : 8 ≤ k ∧ k < 12
    · rw [VG.Proof.Blake2.ArmS.holds_c hc8.1 hc8.2] at hv ⊢; rw [hwm k hc8.1 hc8.2 (Ne.symm ez), hv]
    · have hn : ∀ j < 16, ¬ (8 ≤ j ∧ j < 12) → j ≠ k → wreg k ≠ wreg j := fun j hj hj' hjk e =>
        hjk (VG.Proof.Blake2.ArmS.wreg_inj k hk j hj hc8 hj' e).symm
      have ho : s'.gpr (wreg k) = s.gpr (wreg k) :=
        w.other _ (hn x (by omega) (by omega) ex) (hn y (by omega) (by omega) ey) (hn u hu (by omega) eu)
          (VG.Proof.Blake2.ArmS.wreg_ne k hk).2
      unfold VG.Proof.Blake2.ArmS.Holds at hv ⊢
      split <;> [rw [ho]; skip] <;> rename_i h4 <;> simp only [h4, ↓reduceIte] at hv
      · exact hv
      split <;> [rw [ho]; skip] <;> rename_i h8 <;> simp only [h8, ↓reduceIte] at hv
      · exact hv
      simp only [show ¬ k < 12 by omega, ↓reduceIte] at hv ⊢; rw [ho]; exact hv
  · rw [w.mem]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    rw [VG.Proof.Blake2.ArmS.cOff_A fitV (by unfold cOff; omega)]
    exact Offset.contains _ (by unfold cOff; omega) (by unfold cOff; omega) (by omega)

section
open VG.Spec.Blake2 (G sigmaAt s)

/-- A round, as the eight `G`s `round` runs. -/
theorem round_eq (M : VG.Spec.Blake2.Block 32) (v : Work 32) (r : Nat) :
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

theorem round_ok (r : Nat) {V : BitVec 32} {M : VG.Spec.Blake2.Block 32} {s₀ s : State} {v : Work 32}
    (c : VG.Proof.Blake2.ArmS.RCtx V M s₀) (h : VG.Proof.Blake2.ArmS.RI V s₀ v s) :
    WP isa (round r) s (VG.Proof.Blake2.ArmS.RI V s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  unfold round
  rw [VG.Proof.Blake2.ArmS.round_eq]
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 0) (y := 4) (z := 8) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 0 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 1) (y := 5) (z := 9) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 1 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 2) (y := 6) (z := 10) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 2 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 3) (y := 7) (z := 11) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 3 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 0) (y := 5) (z := 10) (u := 15) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 4 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 1) (y := 6) (z := 11) (u := 12) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 5 c h) fun s h => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 2) (y := 7) (z := 8) (u := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 6 c h) fun s h => ?_)
  exact WP.mono (VG.Proof.Blake2.ArmS.gAt_ok (x := 3) (y := 4) (z := 9) (u := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r 7 c h) fun s h => h

theorem rounds_ok {V : BitVec 32} {M : VG.Spec.Blake2.Block 32} {s₀ : State} {v : Work 32} (c : VG.Proof.Blake2.ArmS.RCtx V M s₀)
    (hv : ∀ k (hk : k < 16), VG.Proof.Blake2.ArmS.Holds V s₀ k v[k]) (n : Nat) :
    WP isa (rounds n) s₀ (VG.Proof.Blake2.ArmS.RI V s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil ⟨hv, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact VG.Proof.Blake2.ArmS.round_ok n c hs

end VG.Proof.Blake2.ArmS

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.CompressS.Block`. -/
section

/-!
# BLAKE2s on ARMv7: one block

Setting up the work vector (`init_ok`): copying the block to `scratch`,
loading the state into registers and the IV words; and XORing the work vector
into the state (`fin_ok`).
-/

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
  refine VG.Proof.Blake2.ArmS.wp_movw fun s₁ u₁ => VG.Proof.Blake2.ArmS.wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

end

theorem iv_getD {k : Nat} (hk : k < 8) : Spec.Blake2.s.IV.toList.getD k 0 = Spec.Blake2.s.IV[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

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
    ∀ n ≤ 16, WP isa (copyMsg n) s (VG.Proof.Blake2.ArmS.CInv V B s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    simp only [Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
    refine wp_ldr (by omega) (by rw [h₁.gpr _ (by decide), hB]) (by rw [h₁.rd, h₁.wr]; exact rB _ (by omega))
      fun s₂ u₂ => ?_
    refine wp_str (by omega) (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by omega)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _
        (by rw [addr_add (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
    · have eB : State.addr (B + BitVec.ofNat 32 (4 * n)) = State.addr B + BitVec.ofNat 64 (4 * n) :=
        addr_add (by omega)
      have eV : ∀ i, i < 16 → State.addr (V + BitVec.ofNat 32 (4 * i)) = State.addr V + BitVec.ofNat 64 (4 * i) :=
        fun i hi => addr_add (by omega)
      show (s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (4 * j))) 32 =
        s.mem.readW (State.addr (B + BitVec.ofNat 32 (4 * j))) 32)
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e
        rw [Mem.readW_writeW_self32, eB]
        exact h₁.frame.readW (r := ⟨State.addr B, 64⟩) (Offset.contains_base _ (by omega) (by omega))
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)
      · rw [Mem.readW_writeW_sep (by
          rw [eV j (by omega), eV n (by omega)]
          exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.msg j (by omega)

/-! ## Loading the state -/

/-- Word `k` (0–7) of the state `H` as `init` loads it: words 4–7 rotated left
by 7. -/
def ldv (H : Nat → BitVec 32) (k : Nat) : BitVec 32 := if k < 4 then H k else (H k).rotateLeft 7

theorem wreg_ne8 {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) : wreg j ≠ wreg k :=
  fun e => h (VG.Proof.Blake2.ArmS.wreg_inj j (by omega) k (by omega) (by omega) (by omega) e)

structure LdInv (st : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, (∀ k < 8, r ≠ wreg k) → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, s'.gpr (wreg k) = VG.Proof.Blake2.ArmS.ldv (fun k => s.mem.readW (A st (4 * k)) 32) k

theorem lds_ok {st : BitVec 32} {s : State} (h11 : s.gpr .r11 = st)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4) :
    ∀ n ≤ 8, WP isa (lds n) s (VG.Proof.Blake2.ArmS.LdInv st s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    have h11' : s₁.gpr .r11 = st := by rw [h₁.gpr _ (by decide), h11]
    have hfin : ∀ s₃ : State, Upd s₁ s₃ (wreg n)
        (VG.Proof.Blake2.ArmS.ldv (fun k => s.mem.readW (A st (4 * k)) 32) n) → VG.Proof.Blake2.ArmS.LdInv st s (n + 1) s₃ := fun s₃ u₃ =>
      ⟨fun r hr => by rw [u₃.other r (hr n (by omega)), h₁.gpr r hr], by rw [u₃.mem, h₁.mem],
        by rw [u₃.rd, h₁.rd], by rw [u₃.wr, h₁.wr], by rw [u₃.sp, h₁.sp], fun k hk => by
          by_cases e : k = n
          · subst e; exact u₃.gpr
          · rw [u₃.other _ (VG.Proof.Blake2.ArmS.wreg_ne8 (by omega) (by omega) e)]; exact h₁.vars k (by omega)⟩
    simp only [ld]
    refine wp_ldr (by omega) (by rw [h11']) (by rw [h₁.rd, h₁.wr]; exact rS _ (by omega)) fun s₂ u₂ => ?_
    by_cases h4 : n < 4
    · simp only [h4, ↓reduceIte]
      exact WP.block_nil (hfin s₂ (by simpa only [VG.Proof.Blake2.ArmS.ldv, h4, ↓reduceIte, h₁.mem] using u₂))
    · simp only [h4, ↓reduceIte]
      refine wp_mov (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₃ u₃ => WP.block_nil (hfin s₃ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩)
      · rw [u₃.gpr, u₂.gpr, h₁.mem, VG.Proof.Blake2.ArmS.rotr_eq_rotl _ (by decide) (by decide)]
        simp only [VG.Proof.Blake2.ArmS.ldv, h4, ↓reduceIte]
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
  frame : Frame [VG.Proof.Blake2.ArmS.cR V] s.mem s'.mem
  c : ∀ j < n, s'.mem.readW (A V (cOff (j + 8))) 32 = Spec.Blake2.s.IV.toList.getD j 0

theorem ivCs_ok {V : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4) :
    ∀ n ≤ 4, WP isa (ivCs n) s (VG.Proof.Blake2.ArmS.CvInv V s n) := by
  intro n hn
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega)
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    simp only [ivC, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 8 - 8 = n by omega]
    refine VG.Proof.Blake2.ArmS.wp_movImm fun s₂ u₂ => wp_str (by unfold cOff; omega)
      (by rw [u₂.other _ (by decide), h₁.gpr _ (by decide), hV])
      (by rw [u₂.wr, h₁.wr]; exact wV _ (by unfold cOff; omega)) fun s₃ m₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [m₃.gpr, u₂.other r hr, h₁.gpr r hr], by rw [m₃.rd, u₂.rd, h₁.rd],
      by rw [m₃.wr, u₂.wr, h₁.wr], by rw [m₃.sp, u₂.sp, h₁.sp], ?_, fun j hj => ?_⟩
    · have hc : (VG.Proof.Blake2.ArmS.cR V).Contains (State.addr (V + BitVec.ofNat 32 (cOff (n + 8)))) (32 / 8) := by
        rw [eV _ (by unfold cOff; omega)]
        exact Offset.contains _ (by unfold cOff; omega) (by unfold cOff; omega) (by omega)
      rw [m₃.mem, u₂.mem]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ hc
    · show s₃.mem.readW (State.addr (V + BitVec.ofNat 32 (cOff (j + 8)))) 32 = _
      rw [m₃.mem, u₂.gpr, u₂.mem]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
          rw [eV _ (by unfold cOff; omega), eV _ (by unfold cOff; omega)]
          exact Offset.sep _ (by unfold cOff; omega) (by unfold cOff; omega) (by unfold cOff; omega))
          (by decide)]
        exact h₁.c j (by omega)

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
    ∀ n ≤ 4, WP isa (ivDs n) s (VG.Proof.Blake2.ArmS.DvInv V s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    have hw := VG.Proof.Blake2.ArmS.wreg_hi_ne' n (by omega)
    simp only [ivD, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S, show n + 12 - 8 = n + 4 by omega]
    refine VG.Proof.Blake2.ArmS.wp_movImm fun s₂ u₂ => ?_
    refine wp_ldr (by unfold xOff; omega) (by
        rw [u₂.other _ (Ne.symm hw.2), h₁.gpr _ (by decide) (by decide), hV])
      (by rw [u₂.rd, u₂.wr, h₁.rd, h₁.wr]; exact rV _ (by unfold xOff; omega)) fun s₃ u₃ => ?_
    refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₄ u₄ => WP.block_nil ?_
    refine ⟨fun r h1 h2 => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, h₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd],
      by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp], fun j hj => ?_⟩
    · rw [u₄.other r (h2 n (by omega)), u₃.other r h1, u₂.other r (h2 n (by omega)), h₁.gpr r h1 h2]
    · by_cases e : j = n
      · subst e
        rw [u₄.gpr, u₃.other _ hw.1, u₂.gpr, u₃.gpr, u₂.mem, h₁.mem, VG.Proof.Blake2.ArmS.rotr_eq_rotl _ (by decide) (by decide),
          VG.Proof.Blake2.ArmS.rotl_xor]
      · have hne : wreg (j + 12) ≠ wreg (n + 12) := fun h => e (VG.Proof.Blake2.ArmS.wreg_hi_ne j (by omega) n (by omega) h)
        rw [u₄.other _ hne, u₃.other _ (VG.Proof.Blake2.ArmS.wreg_hi_ne' j (by omega)).1, u₂.other _ hne]
        exact h₁.vars j (by omega)

/-! ## Setting up the work vector -/

/-- A word of `scratch` outside the regions a frame allows to change. -/
theorem scr_word {V : BitVec 32} (fitV : V.toNat + 512 ≤ 2 ^ 32) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hd : d + 4 ≤ 512)
    (hdis : ∀ r ∈ rs, Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r) :
    m'.readW (A V d) 32 = m.readW (A V d) 32 := by
  rw [VG.Proof.Blake2.ArmS.cOff_A fitV (by omega)]; exact hf.readW (Region.contains_self _ _) hdis (by decide)

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
  frame : Frame (VG.Proof.Blake2.ArmS.initR V) s.mem s'.mem
  blk : s'.mem.readW (A V blkOff) 32 = B + 64
  msg : ∀ j < 16, s'.mem.readW (A V (4 * j)) 32 = s.mem.readW (A B (4 * j)) 32
  vars : ∀ k < 16, VG.Proof.Blake2.ArmS.Holds V s' k (VG.Proof.Blake2.ArmS.initW (fun k => s.mem.readW (A st (4 * k)) 32)
    (fun k => s.mem.readW (A V (xOff k)) 32) k)

theorem init_ok {V st B : BitVec 32} {s : State} (hV : s.gpr .r12 = V) (fitV : V.toNat + 512 ≤ 2 ^ 32)
    (fitS : st.toNat + 32 ≤ 2 ^ 32) (fitB : B.toNat + 64 ≤ 2 ^ 32)
    (wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A V o) 4)
    (rS : ∀ o, o + 4 ≤ 32 → InRegions (s.rd ++ s.wr) (A st o) 4)
    (rB : ∀ o, o + 4 ≤ 64 → InRegions (s.rd ++ s.wr) (A B o) 4)
    (hst : s.mem.readW (A V stOff) 32 = st) (hblk : s.mem.readW (A V blkOff) 32 = B)
    (hdB : Region.Disjoint ⟨State.addr B, 64⟩ ⟨State.addr V, 64⟩)
    (hdS : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr V, 512⟩) :
    WP isa Impl.Blake2.Arm.S.init s (VG.Proof.Blake2.ArmS.IOut V st B s) := by
  have eV : ∀ i, i < 512 → State.addr (V + BitVec.ofNat 32 i) = State.addr V + BitVec.ofNat 64 i :=
    fun i hi => addr_add (by omega)
  have rV : ∀ o, o + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A V o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := wV o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  -- The regions `init` writes, and what lies outside them.
  have sub64 : ∀ r ∈ [(⟨State.addr V, 64⟩ : Region)], ∃ r' ∈ VG.Proof.Blake2.ArmS.initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
  have subC : ∀ r ∈ [VG.Proof.Blake2.ArmS.cR V], ∃ r' ∈ VG.Proof.Blake2.ArmS.initR V, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega)⟩
  have hBlk : (⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ : Region).Contains
      (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
    rw [eV _ (by decide)]; exact Region.contains_self _ _
  have outR : ∀ d, 88 ≤ d → d + 4 ≤ 512 → ∀ r ∈ VG.Proof.Blake2.ArmS.initR V,
      Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 d, 4⟩ r := fun d h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
  have stR : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr V, 512⟩) → ∀ {m m' : Mem},
      Frame rs m m' → ∀ k < 8, m'.readW (A st (4 * k)) 32 = m.readW (A st (4 * k)) 32 :=
    fun hs m m' hf k hk => by
      rw [A_eq (by omega)]
      exact hf.readW (r := ⟨State.addr st, 32⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => hdS.sub_right (hs r hr)) (by decide)
  unfold Impl.Blake2.Arm.S.init
  simp only [Impl.Blake2.Arm.S.S]
  refine WP.seq (wp_ldr (by decide) (by rw [hV]) (rV _ (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have hB₁ : s₁.gpr .r0 = B := by rw [u₁.gpr]; exact hblk
  have V₁ : s₁.gpr .r12 = V := by rw [u₁.other _ (by decide), hV]
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.copyMsg_ok V₁ hB₁ fitV fitB (by rw [u₁.wr]; exact wV) (by rw [u₁.rd, u₁.wr]; exact rB)
    hdB 16 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have V₂ : s₂.gpr .r12 = V := by rw [h₂.gpr _ (by decide), V₁]
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_str (by decide)
    (by rw [u₃.other _ (by decide), V₂]) (by rw [u₃.wr, h₂.wr, u₁.wr]; exact wV _ (by decide))
    fun s₄ m₄ => wp_ldr (by decide) (by rw [m₄.gpr, u₃.other _ (by decide), V₂])
    (by rw [m₄.rd, m₄.wr, u₃.rd, u₃.wr, h₂.rd, h₂.wr, u₁.rd, u₁.wr]; exact rV _ (by decide))
    fun s₅ u₅ => WP.block_nil ?_)
  have f₄ : Frame (VG.Proof.Blake2.ArmS.initR V) s.mem s₄.mem := by
    rw [m₄.mem, u₃.mem, ← u₁.mem]
    exact (h₂.frame.sub sub64).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ hBlk
  have h11 : s₅.gpr .r11 = st := by
    rw [u₅.gpr, ← hst]
    exact VG.Proof.Blake2.ArmS.scr_word fitV f₄ (d := stOff) (by decide) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      · exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, m₄.rd, u₃.rd, h₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, m₄.wr, u₃.wr, h₂.wr, u₁.wr]
  have V₅ : s₅.gpr .r12 = V := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), V₂]
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.lds_ok h11 (by rw [rd₅, wr₅]; exact rS) 8 (Nat.le_refl _)) fun s₆ h₆ => ?_)
  have V₆ : s₆.gpr .r12 = V := by rw [h₆.gpr _ (by decide), V₅]
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.ivCs_ok V₆ fitV (by rw [h₆.wr, wr₅]; exact wV) 4 (Nat.le_refl _)) fun s₇ h₇ => ?_)
  have V₇ : s₇.gpr .r12 = V := by rw [h₇.gpr _ (by decide), V₆]
  refine WP.mono (VG.Proof.Blake2.ArmS.ivDs_ok V₇ (by rw [h₇.rd, h₇.wr, h₆.rd, h₆.wr, rd₅, wr₅]; exact rV) 4 (Nat.le_refl _))
    fun s₈ h₈ => ?_
  have f₈ : Frame (VG.Proof.Blake2.ArmS.initR V) s.mem s₈.mem := by
    rw [h₈.mem]; exact (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
  refine ⟨by rw [h₈.gpr _ (by decide) (by decide), V₇], by rw [h₈.rd, h₇.rd, h₆.rd, rd₅],
    by rw [h₈.wr, h₇.wr, h₆.wr, wr₅], ?_, f₈, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · rw [h₈.sp, h₇.sp, h₆.sp, u₅.sp, m₄.sp, u₃.sp, h₂.sp, u₁.sp]
  · -- The block pointer.
    have hd : ∀ r ∈ [VG.Proof.Blake2.ArmS.cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 blkOff, 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by decide) (by decide) (by decide)
    rw [h₈.mem, VG.Proof.Blake2.ArmS.scr_word fitV h₇.frame (by decide) hd, h₆.mem, m₅]
    show s₄.mem.readW (State.addr (V + BitVec.ofNat 32 blkOff)) 32 = _
    rw [m₄.mem, Mem.readW_writeW_self32, u₃.gpr, h₂.gpr _ (by decide), hB₁]
  · -- The message words.
    have hd : ∀ r ∈ [VG.Proof.Blake2.ArmS.cR V], Region.Disjoint ⟨State.addr V + BitVec.ofNat 64 (4 * j), 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    have hsep : Mem.Sep (State.addr V + BitVec.ofNat 64 (4 * j)) (32 / 8)
        (State.addr (V + BitVec.ofNat 32 blkOff)) (32 / 8) := by
      rw [eV _ (by decide)]
      exact Offset.sep _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
    rw [h₈.mem, VG.Proof.Blake2.ArmS.scr_word fitV h₇.frame (by omega) hd, h₆.mem, m₅, m₄.mem,
      show (A V (4 * j)) = State.addr V + BitVec.ofNat 64 (4 * j) from eV _ (by omega),
      Mem.readW_writeW_sep hsep (by decide), u₃.mem, ← eV _ (by omega), h₂.msg j hj, u₁.mem]
  · -- The work vector.
    have hS₅ : ∀ i < 8, s₅.mem.readW (A st (4 * i)) 32 = s.mem.readW (A st (4 * i)) 32 := fun i hi =>
      stR (rs := VG.Proof.Blake2.ArmS.initR V) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · exact Offset.sub_base _ (by simp only [blkOff]; omega)) (by rw [m₅]; exact f₄) i hi
    have hX : ∀ i, 88 ≤ xOff i → xOff i + 4 ≤ 512 →
        s₇.mem.readW (A V (xOff i)) 32 = s.mem.readW (A V (xOff i)) 32 := fun i h1 h2 => by
      have f₇ : Frame (VG.Proof.Blake2.ArmS.initR V) s.mem s₇.mem :=
        (f₄.trans (by rw [h₆.mem, m₅]; exact Frame.refl _ _)).trans (h₇.frame.sub subC)
      exact VG.Proof.Blake2.ArmS.scr_word fitV f₇ h2 (outR _ h1 h2)
    have hr : ∀ i < 8, s₈.gpr (wreg i) = s₆.gpr (wreg i) := fun i hi => by
      rw [h₈.gpr _ (VG.Proof.Blake2.ArmS.wreg_ne i (by omega)).2 (fun j hj e => absurd
        (VG.Proof.Blake2.ArmS.wreg_inj i (by omega) (j + 12) (by omega) (by omega) (by omega) e) (by omega)),
        h₇.gpr _ (VG.Proof.Blake2.ArmS.wreg_ne i (by omega)).2]
    unfold VG.Proof.Blake2.ArmS.Holds VG.Proof.Blake2.ArmS.initW
    by_cases h4 : k < 4
    · simp only [h4, ↓reduceIte, show k < 8 by omega]
      rw [hr k (by omega), h₆.vars k (by omega)]
      simp only [VG.Proof.Blake2.ArmS.ldv, h4, ↓reduceIte]; exact hS₅ k (by omega)
    by_cases h8 : k < 8
    · simp only [h4, h8, ↓reduceIte]
      rw [hr k h8, h₆.vars k h8]
      simp only [VG.Proof.Blake2.ArmS.ldv, h4, ↓reduceIte]; rw [hS₅ k h8]
    by_cases h12 : k < 12
    · simp only [h4, h8, h12, ↓reduceIte]
      rw [h₈.mem]
      have := h₇.c (k - 8) (by omega)
      rwa [show k - 8 + 8 = k by omega] at this
    · simp only [h4, h8, h12, ↓reduceIte]
      have := h₈.vars (k - 12) (by omega)
      rw [show k - 12 + 12 = k by omega, show k - 12 + 4 = k - 8 by omega] at this
      rw [this, hX k (by unfold xOff; omega) (by unfold xOff; omega)]

/-! ## XORing the work vector into the state -/

/-- What `fin` needs of the state `s₀` at its start: the state at `st` and
the scratch space at `V`, holding words 8–11 of the work vector `v`. -/
structure FCtx (V st : BitVec 32) (v : Work 32) (s₀ : State) : Prop where
  fitS : st.toNat + 32 ≤ 2 ^ 32
  fitV : V.toNat + 512 ≤ 2 ^ 32
  wS : ∀ o, o + 4 ≤ 32 → InRegions s₀.wr (A st o) 4
  rV : ∀ o, o + 4 ≤ 512 → InRegions (s₀.rd ++ s₀.wr) (A V o) 4
  c : ∀ k (hk : k < 4), s₀.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8]'(by omega)
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
  lo : ∀ k (hk : k < 4), k ∉ D → s.gpr (wreg k) = v[k]'(by omega)
  mid : ∀ k (hk : k < 4), s.gpr (wreg (k + 4)) = (v[k + 4]'(by omega) ^^^ v[k + 4 + 8]'(by omega)).rotateLeft 7
  words : ∀ k (hk : k < 8), s.mem.readW (A st (4 * k)) 32 =
    if k ∈ D then H k ^^^ (v[k]'(by omega) ^^^ v[k + 8]'(by omega)) else H k

theorem wreg_lo_ne : ∀ k < 8, wreg k ≠ .lr ∧ wreg k ≠ .r8 ∧ wreg k ≠ .r12 := by decide
theorem wreg_lo_ne' : ∀ k < 4, wreg k ≠ .r9 ∧ wreg k ≠ .r10 := by decide

theorem FI.st_addr {V st : BitVec 32} {v : Work 32} {s₀ : State} (c : VG.Proof.Blake2.ArmS.FCtx V st v s₀) {k : Nat} (hk : k < 8) :
    State.addr (st + BitVec.ofNat 32 (4 * k)) = State.addr st + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := c.fitS; omega)

theorem FI.words_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : VG.Proof.Blake2.ArmS.FCtx V st v s₀) (h : VG.Proof.Blake2.ArmS.FI V st H v s₀ D s) {j : Nat} (hj : j < 8) {m : Mem}
    (hm : m = s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) (H j ^^^ (v[j]'(by omega) ^^^ v[j + 8]'(by omega)))) :
    ∀ k (hk : k < 8), m.readW (A st (4 * k)) 32 =
      if k ∈ j :: D then H k ^^^ (v[k]'(by omega) ^^^ v[k + 8]'(by omega)) else H k := fun k hk => by
  subst hm
  show (s.mem.writeW _ _).readW (State.addr (st + BitVec.ofNat 32 (4 * k))) 32 = _
  by_cases e : k = j
  · subst e; simp only [List.mem_cons_self, ↓reduceIte]; exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (by
      rw [FI.st_addr c hk, FI.st_addr c hj]; exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    simp only [List.mem_cons, e, false_or]; exact h.words k hk

theorem FI.frame_upd {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : VG.Proof.Blake2.ArmS.FCtx V st v s₀) (h : VG.Proof.Blake2.ArmS.FI V st H v s₀ D s) {j : Nat} (hj : j < 8) (x : BitVec 32) :
    Frame [⟨State.addr st, 32⟩] s₀.mem (s.mem.writeW (State.addr (st + BitVec.ofNat 32 (4 * j))) x) :=
  h.frame.writeW (List.mem_singleton_self _) _ (by
    rw [FI.st_addr c hj]; exact Offset.contains_base _ (by omega) (by omega))

theorem finHi_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : VG.Proof.Blake2.ArmS.FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k + 4 ∉ D) (h : VG.Proof.Blake2.ArmS.FI V st H v s₀ D s) :
    WP isa (.block (finHi (k + 4))) s (VG.Proof.Blake2.ArmS.FI V st H v s₀ ((k + 4) :: D)) := by
  have nw := VG.Proof.Blake2.ArmS.wreg_lo_ne (k + 4) (by omega)
  simp only [finHi, Impl.Blake2.Arm.S.T]
  refine wp_ldr (by omega) (by rw [h.r8]) (by
      rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega); ⟨r, List.mem_append_right _ hr, hc⟩)
    fun s₁ u₁ => VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₂ u₂ => wp_str (by omega)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
      (by rw [u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega)) fun s₃ m₃ => WP.block_nil ?_
  have hv : s₂.gpr .lr = H (k + 4) ^^^ (v[k + 4]'(by omega) ^^^ v[k + 4 + 8]'(by omega)) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ nw.1, h.mid k hk, VG.Proof.Blake2.ArmS.rotr_rotl _ (by decide)]
    have := h.words (k + 4) (by omega)
    simp only [hD, ↓reduceIte] at this
    rw [← this]
  refine ⟨by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r8],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r12],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r9],
    by rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r10],
    by rw [m₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₃.wr, u₂.wr, u₁.wr, h.wr], by rw [m₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega) _, fun j hj hjD => ?_, fun j hj => ?_,
    h.words_upd c (j := k + 4) (by omega) (by rw [m₃.mem, hv, u₂.mem, u₁.mem])⟩
  · have := VG.Proof.Blake2.ArmS.wreg_lo_ne j (by omega)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have := VG.Proof.Blake2.ArmS.wreg_lo_ne (j + 4) (by omega)
    rw [m₃.gpr, u₂.other _ this.1, u₁.other _ this.1, h.mid j hj]

theorem finLo_ok {V st : BitVec 32} {H : Nat → BitVec 32} {v : Work 32} {s₀ s : State} {D : List Nat}
    (c : VG.Proof.Blake2.ArmS.FCtx V st v s₀) {k : Nat} (hk : k < 4) (hD : k ∉ D) (h : VG.Proof.Blake2.ArmS.FI V st H v s₀ D s) :
    WP isa (.block (finLo k)) s (VG.Proof.Blake2.ArmS.FI V st H v s₀ (k :: D)) := by
  have nw := VG.Proof.Blake2.ArmS.wreg_lo_ne k (by omega)
  have iS : InRegions (s.rd ++ s.wr) (A st (4 * k)) 4 := by
    rw [h.rd, h.wr]; exact let ⟨r, hr, hc⟩ := c.wS _ (by omega); ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [finLo, Impl.Blake2.Arm.S.T, Impl.Blake2.Arm.S.S]
  refine wp_ldr (by unfold cOff; omega) (by rw [h.r12]) (by rw [h.rd, h.wr]; exact c.rV _ (by unfold cOff; omega))
    fun s₁ u₁ => VG.Proof.Blake2.ArmS.wp_eor (op2_reg _ _) fun s₂ u₂ => wp_ldr (by omega)
      (by rw [u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide), h.r8]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact iS)
      fun s₃ u₃ => VG.Proof.Blake2.ArmS.wp_eor (op2_reg _ _) fun s₄ u₄ => wp_str (by omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
        h.r8])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact c.wS _ (by omega)) fun s₅ m₅ => WP.block_nil ?_
  have hc : s.mem.readW (A V (cOff (k + 8))) 32 = v[k + 8]'(by omega) := by
    rw [← c.c k hk, VG.Proof.Blake2.ArmS.cOff_A c.fitV (by unfold cOff; omega)]
    exact h.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (c.disj.sub_right (Offset.sub_base _ (by unfold cOff; omega))).symm) (by decide)
  have hw : s₃.gpr (wreg k) = v[k]'(by omega) ^^^ v[k + 8]'(by omega) := by
    rw [u₃.other _ nw.1, u₂.gpr, u₁.other _ nw.1, h.lo k hk hD, u₁.gpr]
    exact congrArg _ hc
  have hv : s₄.gpr .lr = H k ^^^ (v[k]'(by omega) ^^^ v[k + 8]'(by omega)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₁.mem, hw]
    have := h.words k (by omega)
    simp only [hD, ↓reduceIte] at this
    exact congrArg (· ^^^ _) this
  have n9 := VG.Proof.Blake2.ArmS.wreg_lo_ne' k hk
  refine ⟨?_, ?_, by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.1),
      u₁.other _ (by decide), h.r9],
    by rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm n9.2),
      u₁.other _ (by decide), h.r10], by rw [m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    by rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.frame_upd c (by omega) _, fun j hj hjD => ?_,
    fun j hj => ?_, h.words_upd c (j := k) (by omega) (by rw [m₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem])⟩
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.1), u₁.other _ (by decide),
      h.r8]
  · rw [m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (Ne.symm nw.2.2), u₁.other _ (by decide),
      h.r12]
  · have nj := VG.Proof.Blake2.ArmS.wreg_lo_ne j (by omega)
    have ne : wreg j ≠ wreg k := VG.Proof.Blake2.ArmS.wreg_ne8 (by omega) (by omega) fun e => hjD (e ▸ List.mem_cons_self)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1,
      h.lo j hj fun hm => hjD (List.mem_cons_of_mem _ hm)]
  · have nj := VG.Proof.Blake2.ArmS.wreg_lo_ne (j + 4) (by omega)
    have ne : wreg (j + 4) ≠ wreg k := VG.Proof.Blake2.ArmS.wreg_ne8 (by omega) (by omega) (by omega)
    rw [m₅.gpr, u₄.other _ nj.1, u₃.other _ nj.1, u₂.other _ ne, u₁.other _ nj.1, h.mid j hj]

theorem finPre_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : VG.Proof.Blake2.ArmS.FCtx V st v s)
    (hv : ∀ k (hk : k < 16), VG.Proof.Blake2.ArmS.Holds V s k (v[k]'(by omega))) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa (.block (finX 4 ++ finX 5 ++ finX 6 ++ finX 7 ++ ([.ldr .r8 Impl.Blake2.Arm.S.S stOff,
      .ldr .r9 Impl.Blake2.Arm.S.S blkOff, .ldr .r10 Impl.Blake2.Arm.S.S Impl.Blake2.Arm.S.nOff] : List Instr))) s
      (VG.Proof.Blake2.ArmS.FI V st (fun k => s.mem.readW (A st (4 * k)) 32) v s []) := by
  simp only [finX, Impl.Blake2.Arm.S.S, List.cons_append, List.nil_append]
  refine VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₁ u₁ => VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₂ u₂ =>
    VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₃ u₃ => VG.Proof.Blake2.ArmS.wp_eor (VG.Proof.Blake2.ArmS.op2_ror (by decide)) fun s₄ u₄ => ?_
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
      (v[k + 4]'(by omega) ^^^ v[k + 4 + 8]'(by omega)).rotateLeft 7 := fun k hk => by
    rw [(VG.Proof.Blake2.ArmS.holds_mid (by omega) (by omega)).mp (hv (k + 4) (by omega)),
      (VG.Proof.Blake2.ArmS.holds_hi (by omega)).mp (hv (k + 4 + 8) (by omega)), VG.Proof.Blake2.ArmS.rotl8_rotr1, VG.Proof.Blake2.ArmS.rotl_xor]
  refine ⟨by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, m₄]; exact hst,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), V₄],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, m₄],
    by rw [u₇.gpr, u₆.mem, u₅.mem, m₄],
    by rw [u₇.rd, u₆.rd, u₅.rd, rd₄], by rw [u₇.wr, u₆.wr, u₅.wr, wr₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [m₇]; exact Frame.refl _ _,
    fun k hk _ => ?_, fun k hk => ?_, fun k hk => by rw [m₇]; rfl⟩
  · have e := (VG.Proof.Blake2.ArmS.holds_lo hk).mp (hv k (by omega))
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.other]
      exact e
  · have e := mid k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, u₁.gpr]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, u₁.other]
      exact e
    · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, u₁.other]
      exact e

theorem fin_ok {V st : BitVec 32} {v : Work 32} {s : State} (c : VG.Proof.Blake2.ArmS.FCtx V st v s)
    (hv : ∀ k (hk : k < 16), VG.Proof.Blake2.ArmS.Holds V s k (v[k]'(by omega))) (hV : s.gpr .r12 = V)
    (hst : s.mem.readW (A V stOff) 32 = st) :
    WP isa Impl.Blake2.Arm.S.fin s fun s' =>
      s'.gpr .r12 = V ∧ s'.gpr .r8 = st ∧ s'.gpr .r9 = s.mem.readW (A V blkOff) 32 ∧
      s'.gpr .r10 = s.mem.readW (A V Impl.Blake2.Arm.S.nOff) 32 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr st, 32⟩] s.mem s'.mem ∧
      ∀ k (hk : k < 8), s'.mem.readW (A st (4 * k)) 32 =
        s.mem.readW (A st (4 * k)) 32 ^^^ (v[k]'(by omega) ^^^ v[k + 8]'(by omega)) := by
  unfold Impl.Blake2.Arm.S.fin
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finPre_ok c hv hV hst) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finHi_ok (k := 0) c (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finHi_ok (k := 1) c (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finHi_ok (k := 2) c (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finHi_ok (k := 3) c (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finLo_ok (k := 0) c (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finLo_ok (k := 1) c (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.finLo_ok (k := 2) c (by decide) (by decide) h₇) fun s₈ h₈ => ?_)
  refine WP.mono (VG.Proof.Blake2.ArmS.finLo_ok (k := 3) c (by decide) (by decide) h₈) fun s₉ h₉ => ?_
  refine ⟨h₉.r12, h₉.r8, h₉.r9, h₉.r10, h₉.rd, h₉.wr, h₉.sp, h₉.frame, fun k hk => ?_⟩
  rw [h₉.words k hk]
  have : k ∈ [3, 2, 1, 0, 0 + 4 + 3 - 3 + 3, 2 + 4, 1 + 4, 0 + 4] := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [this, ↓reduceIte]

end VG.Proof.Blake2.ArmS

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress`. -/
section

section

/-!
# BLAKE2s on ARMv7: the code as a literal

The code of the compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.Blake2.Arm.S.compress

end VG

end

/-!
# BLAKE2s compression function on ARMv7: the whole function

The prologue, which keeps the arguments, the counter, the flag word and our
caller's registers in `scratch` (`setup_ok`); one block (`body_ok`: `init_ok`,
`rounds_ok`, `fin_ok` and `advance_ok`), whose loop invariant is all in
`scratch`; and the epilogue (`restore_ok`). The loop is proven against
`Proof.Blake2.compressArm Spec.Blake2.s` (`compress_verified'`), which the
streaming functions use for their calls; `compress_verified` moves it to the
shared contract of `Spec/Blake2/Contract.lean`. Constant time is the taint
analysis on the literal code (`LitS.lean`).
-/

namespace VG.Proof.Blake2.ArmS

open VG VG.Arm
open VG.Impl.Sha512.Arm (lo hi)
open VG.Impl.Blake2.Arm.S (wreg cOff xOff stOff blkOff nOff tOff fOff saved advance body save restore setup)
open VG.Proof.Sha512.Arm (A A_eq lo_add hi_add lo_toNat hi_toNat)
open VG.Proof.MdStream.Arm (eval_ne contains_offset sub_offset)
open VG.Spec.Blake2 (Work Block HashValue Params)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := stackArg s₀ 3
abbrev t₀ : Nat := (tArm s₀).toNat
abbrev fl : Bool := stackArg s₀ 2 != 0
abbrev blR : Region := ⟨State.addr (VG.Proof.Blake2.ArmS.bp s₀), 64 * VG.Proof.Blake2.ArmS.nb s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev stR : Region := ⟨State.addr (VG.Proof.Blake2.ArmS.stp s₀), 32⟩
abbrev scrR : Region := ⟨State.addr (VG.Proof.Blake2.ArmS.scp s₀), 512⟩
abbrev H₀ : HashValue 32 := Spec.Blake2.stateAt 32 s₀.mem (State.addr (VG.Proof.Blake2.ArmS.stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Blake2.ArmS.bp s₀ + BitVec.ofNat 32 (64 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.ArmS.blR s₀, VG.Proof.Blake2.ArmS.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.ArmS.stR s₀, VG.Proof.Blake2.ArmS.scrR s₀]
  st_scr : (VG.Proof.Blake2.ArmS.stR s₀).Disjoint (VG.Proof.Blake2.ArmS.scrR s₀)
  blk_st : (VG.Proof.Blake2.ArmS.blR s₀).Disjoint (VG.Proof.Blake2.ArmS.stR s₀)
  blk_scr : (VG.Proof.Blake2.ArmS.blR s₀).Disjoint (VG.Proof.Blake2.ArmS.scrR s₀)
  a_st : (VG.Proof.Blake2.ArmS.argR s₀).Disjoint (VG.Proof.Blake2.ArmS.stR s₀)
  a_scr : (VG.Proof.Blake2.ArmS.argR s₀).Disjoint (VG.Proof.Blake2.ArmS.scrR s₀)
  st_fits : (VG.Proof.Blake2.ArmS.stp s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Blake2.ArmS.bp s₀).toNat + 64 * VG.Proof.Blake2.ArmS.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Blake2.ArmS.scp s₀).toNat + 512 ≤ 2 ^ 32
  sp_fits : s₀.sp.toNat + 16 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (VG.Proof.Blake2.compressArm Spec.Blake2.s).pre s₀) : VG.Proof.Blake2.ArmS.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Blake2.ArmS.Pre s₀)
include h

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) : (VG.Proof.Blake2.ArmS.blkAddr s₀ i).toNat = (VG.Proof.Blake2.ArmS.bp s₀).toNat + 64 * i := by
  have := h.blk_fits
  simp only [VG.Proof.Blake2.ArmS.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) : (VG.Proof.Blake2.ArmS.blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) :
    State.addr (VG.Proof.Blake2.ArmS.blkAddr s₀ i) = State.addr (VG.Proof.Blake2.ArmS.bp s₀) + BitVec.ofNat 64 (64 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) : Region.Sub ⟨State.addr (VG.Proof.Blake2.ArmS.blkAddr s₀ i), 64⟩ (VG.Proof.Blake2.ArmS.blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) :
    ∀ o, o + 4 ≤ 64 → InRegions (s₀.rd ++ s₀.wr) (A (VG.Proof.Blake2.ArmS.blkAddr s₀ i) o) 4 := fun o ho => by
  have := h.blk_fit hi
  have := h.blk_fits
  refine ⟨VG.Proof.Blake2.ArmS.blR s₀, by simp [h.rd], ?_⟩
  rw [A_eq (by omega), h.blk_addr hi, Offset.add_ofNat_add_ofNat]
  exact contains_offset (by omega) (by omega)

/-- The address of a word of `scratch`. -/
theorem scr_addr {d : Nat} (hd : d < 512) :
    A (VG.Proof.Blake2.ArmS.scp s₀) d = State.addr (VG.Proof.Blake2.ArmS.scp s₀) + BitVec.ofNat 64 d := A_eq (by have := h.scr_fits; omega)

theorem out_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (VG.Proof.Blake2.ArmS.scp s₀) d) 4 := by
  rw [h.scr_addr (by omega)]
  exact ⟨VG.Proof.Blake2.ArmS.scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem in_scr {d : Nat} (hd : d + 4 ≤ 512) : InRegions (s₀.rd ++ s₀.wr) (A (VG.Proof.Blake2.ArmS.scp s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := h.out_scr hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem out_st {d : Nat} (hd : d + 4 ≤ 32) : InRegions s₀.wr (A (VG.Proof.Blake2.ArmS.stp s₀) d) 4 := by
  rw [A_eq (by have := h.st_fits; omega)]
  exact ⟨VG.Proof.Blake2.ArmS.stR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem in_st {d : Nat} (hd : d + 4 ≤ 32) : InRegions (s₀.rd ++ s₀.wr) (A (VG.Proof.Blake2.ArmS.stp s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := h.out_st hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of `scratch` outside the regions a frame allows to change. -/
theorem scr_frame {d : Nat} (hd' : d + 4 ≤ 512) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr (VG.Proof.Blake2.ArmS.scp s₀) + BitVec.ofNat 64 d, 4⟩ r) :
    m'.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = m.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := by
  rw [h.scr_addr (by omega)]
  exact hf.readW (Region.contains_self _ _) hd (by decide)

/-- A state word outside the scratch space. -/
theorem st_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.ArmS.scrR s₀] m m') {k : Nat} (hk : k < 8) :
    m'.readW (A (VG.Proof.Blake2.ArmS.stp s₀) (4 * k)) 32 = m.readW (A (VG.Proof.Blake2.ArmS.stp s₀) (4 * k)) 32 := by
  rw [A_eq (by have := h.st_fits; omega)]
  exact hf.readW (r := VG.Proof.Blake2.ArmS.stR s₀) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.st_scr) (by decide)

/-- A block word outside the state and the scratch space. -/
theorem blk_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.ArmS.stR s₀, VG.Proof.Blake2.ArmS.scrR s₀] m m') {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) {o : Nat}
    (ho : o + 4 ≤ 64) : m'.readW (A (VG.Proof.Blake2.ArmS.blkAddr s₀ i) o) 32 = m.readW (A (VG.Proof.Blake2.ArmS.blkAddr s₀ i) o) 32 := by
  have := h.blk_fit hi
  rw [A_eq (by omega)]
  exact hf.readW (r := ⟨State.addr (VG.Proof.Blake2.ArmS.blkAddr s₀ i), 64⟩) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.blk_st.sub_left (h.blk_sub hi)
    · exact h.blk_scr.sub_left (h.blk_sub hi)) (by decide)

end Pre

/-! ## The prologue -/

/-- The flag word of `last`. -/
def flag32 (l : BitVec 32) : BitVec 32 := 0 - ((0 - l ||| l) >>> 31)

/-- The flag word: all ones for the final block. -/
def flagW (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

theorem flag_eq (l : BitVec 32) : VG.Proof.Blake2.ArmS.flag32 l = VG.Proof.Blake2.ArmS.flagW (l != 0) := by
  by_cases h : l = 0
  · subst h; decide
  · have hm : (0 - l ||| l).msb = true := by
      rw [BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide, BitVec.toNat_sub]
      have := l.isLt
      have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Bool.or_eq_true,
        decide_eq_true_eq]
      omega
    have e1 : (0 - l ||| l) >>> 31 = 1 := by
      rw [BitVec.msb_eq_decide] at hm
      simp only [decide_eq_true_eq] at hm
      apply BitVec.eq_of_toNat_eq
      have := (0 - l ||| l).isLt
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
      omega
    have ht : (l != 0) = true := by simpa using h
    simp only [VG.Proof.Blake2.ArmS.flag32, e1, VG.Proof.Blake2.ArmS.flagW, ht, ite_true]
    decide

/-- The words the prologue stores in `scratch`, in order. -/
def setupWrites (s₀ : State) : List (Nat × BitVec 32) :=
  [(92, stackArg s₀ 0), (96, stackArg s₀ 1), (108, s₀.gpr .r4), (112, s₀.gpr .r5), (116, s₀.gpr .r6),
   (120, s₀.gpr .r7), (124, s₀.gpr .r8), (128, s₀.gpr .r9), (132, s₀.gpr .r10), (136, s₀.gpr .r11),
   (140, s₀.gpr .lr), (80, s₀.gpr .r0), (84, s₀.gpr .r1), (88, s₀.gpr .r2), (100, VG.Proof.Blake2.ArmS.flag32 (stackArg s₀ 2)),
   (104, 0)]

/-- The memory after the prologue. -/
def setupMem (s₀ : State) : Mem :=
  (VG.Proof.Blake2.ArmS.setupWrites s₀).foldl (fun m p => m.writeW (A (VG.Proof.Blake2.ArmS.scp s₀) p.1) p.2) s₀.mem

theorem readW_writeW_scr {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A (VG.Proof.Blake2.ArmS.scp s₀) e) v).readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = m.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rw [hp.scr_addr (by omega), hp.scr_addr (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

/-- A stack argument is unchanged by a write to `scratch`. -/
theorem readW_writeW_arg {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) (m : Mem) (v : BitVec 32) {i e : Nat} (hi : i < 4)
    (he : e + 4 ≤ 512) :
    (m.writeW (A (VG.Proof.Blake2.ArmS.scp s₀) e) v).readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 =
      m.readW (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 32 := by
  have := hp.sp_fits
  refine Mem.readW_writeW_sep (hp.a_scr.sep ?_ ?_) (by decide)
  · show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
    rw [addr_add (by omega), addr_add (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  · rw [hp.scr_addr (by omega)]; exact contains_offset he (by omega)

set_option simprocs false in
theorem setup_ok {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ =>
      s₁.mem = VG.Proof.Blake2.ArmS.setupMem s₀ ∧ s₁.gpr .r12 = VG.Proof.Blake2.ArmS.scp s₀ ∧ s₁.z = (s₀.gpr .r2 - 0 == 0) ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr ∧ s₁.sp = s₀.sp := by
  have hs := hp.sp_fits
  have ia : ∀ i, i < 4 → InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => ⟨VG.Proof.Blake2.ArmS.argR s₀, by simp [hp.rd], by
      show (⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 16⟩ : Region).Contains _ 4
      rw [addr_add (by omega), addr_add (by omega)]
      exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have a0 := ia 0 (by decide); have a1 := ia 1 (by decide); have a2 := ia 2 (by decide)
  have a3 := ia 3 (by decide)
  simp only [show 4 * 0 = 0 from rfl, show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl] at a0 a1 a2 a3
  have e3 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 12)) 32 = stackArg s₀ 3 := rfl
  have e0 : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 0)) 32 = stackArg s₀ 0 := rfl
  have e1 : ∀ v, (s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 92)) v).readW
      (State.addr (s₀.sp + BitVec.ofNat 32 4)) 32 = stackArg s₀ 1 := fun v =>
    VG.Proof.Blake2.ArmS.readW_writeW_arg hp _ v (i := 1) (by decide) (by decide)
  have e2 : ∀ v v', ((s₀.mem.writeW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 92)) v).writeW
      (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 96)) v').readW
      (State.addr (s₀.sp + BitVec.ofNat 32 8)) 32 = stackArg s₀ 2 := fun v v' => by
    rw [VG.Proof.Blake2.ArmS.readW_writeW_arg hp _ v' (i := 2) (by decide) (by decide),
      VG.Proof.Blake2.ArmS.readW_writeW_arg hp _ v (i := 2) (by decide) (by decide)]; rfl
  have w : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => hp.out_scr hd
  have w92 := w 92 (by decide); have w96 := w 96 (by decide); have w108 := w 108 (by decide)
  have w112 := w 112 (by decide); have w116 := w 116 (by decide); have w120 := w 120 (by decide)
  have w124 := w 124 (by decide); have w128 := w 128 (by decide); have w132 := w 132 (by decide)
  have w136 := w 136 (by decide); have w140 := w 140 (by decide); have w80 := w 80 (by decide)
  have w84 := w 84 (by decide); have w88 := w 88 (by decide); have w100 := w 100 (by decide)
  have w104 := w 104 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [setup, save, saved, Impl.Blake2.Arm.S.S, Impl.Blake2.Arm.S.T,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, tOff, stOff, blkOff, nOff, fOff,
    show 92 + 4 = 96 from rfl, show 100 + 4 = 104 from rfl, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, Op2.eval, State.load32, State.store32, subFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.sp_setReg, a0, a1, a2, a3, e3, e0, e1, e2, w92, w96, w108, w112, w116, w120, w124, w128,
    w132, w136, w140, w80, w84, w88, w100, w104,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

/-! ## Advancing the counter -/

/-- `scratch` after `advance`: the counter's two words advanced by 64, the
pointers `P8` and `P9` stored again and the count `n` decremented. -/
def ctrMem (m : Mem) (scr : BitVec 32) (N : Nat) (P8 P9 n : BitVec 32) : Mem :=
  ((((m.writeW (A scr tOff) (lo (BitVec.ofNat 64 (N + 64)))).writeW (A scr (tOff + 4))
    (hi (BitVec.ofNat 64 (N + 64)))).writeW (A scr stOff) P8).writeW (A scr blkOff) P9).writeW (A scr nOff) (n - 1)

theorem carry_lo (N : Nat) : lo (BitVec.ofNat 64 N) + 64 = lo (BitVec.ofNat 64 (N + 64)) := by
  rw [← BitVec.ofNat_add_ofNat, lo_add]; rfl

theorem carry_hi (N : Nat) :
    hi (BitVec.ofNat 64 N) + 0 + (if 2 ^ 32 ≤ (lo (BitVec.ofNat 64 N)).toNat + 64 then 1 else 0) =
      hi (BitVec.ofNat 64 (N + 64)) := by
  rw [← BitVec.ofNat_add_ofNat, hi_add]
  simp only [show lo (BitVec.ofNat 64 64) = 64 from rfl, show hi (BitVec.ofNat 64 64) = 0 from rfl,
    show (64 : BitVec 32).toNat = 64 from rfl]

set_option simprocs false in
theorem advance_ok {s : State} {scr : BitVec 32} {N : Nat} {P8 P9 n : BitVec 32}
    (h12 : s.gpr .r12 = scr) (h8 : s.gpr .r8 = P8) (h9 : s.gpr .r9 = P9) (h10 : s.gpr .r10 = n)
    (hw : ∀ d, d + 4 ≤ 512 → InRegions s.wr (A scr d) 4)
    (hlo : s.mem.readW (A scr tOff) 32 = lo (BitVec.ofNat 64 N))
    (hhi : s.mem.readW (A scr (tOff + 4)) 32 = hi (BitVec.ofNat 64 N)) :
    WP isa (.block advance) s fun s' =>
      s'.z = (n - 1 == 0) ∧ s'.gpr .r12 = scr ∧ (∀ r, r ∉ [Reg.r0, .r1, .r10] → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.Proof.Blake2.ArmS.ctrMem s.mem scr N P8 P9 n ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have ir : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (A scr d) 4 := fun d hd =>
    let ⟨r, hr, hc⟩ := hw d hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have o92 := hw 92 (by decide); have o96 := hw 96 (by decide); have o80 := hw 80 (by decide)
  have o84 := hw 84 (by decide); have o88 := hw 88 (by decide)
  have i92 := ir 92 (by decide); have i96 := ir 96 (by decide)
  simp only [A, tOff, show 92 + 4 = 96 from rfl] at o92 o96 o80 o84 o88 i92 i96 hlo hhi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, Impl.Blake2.Arm.S.S, tOff, nOff, stOff, blkOff,
    show 92 + 4 = 96 from rfl, runBlock_cons, runStep_some, runBlock_nil, exec, isa, Op2.eval, State.load32,
    State.store32, addFlags, subFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.c_setReg, RegUpd.z_setReg, RegUpd.sp_setReg, h12, h8, h9, h10, o92, o96, o80, o84, o88, i92, i96, hlo,
    hhi, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2⟩ := hr
    simp only [h0, h1, h2, ite_false]
  · simp only [decide_eq_true_eq, show (64 : BitVec 32).toNat = 64 from rfl, VG.Proof.Blake2.ArmS.carry_lo, VG.Proof.Blake2.ArmS.carry_hi]
    rfl

/-! ## The work vector of `F` -/

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : Spec.Blake2.HashValue 32) (t : Nat) (f : Bool) : Spec.Blake2.Work 32 :=
  let v : Spec.Blake2.Work 32 := h ++ Spec.Blake2.s.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem initW_eq (h : Spec.Blake2.HashValue 32) (N : Nat) (f : Bool) {H X : Nat → BitVec 32}
    (hH : ∀ k (hk : k < 8), H k = (h[k]'(by omega))) (h12 : X 12 = BitVec.ofNat 32 N)
    (h13 : X 13 = BitVec.ofNat 32 (N / 2 ^ 32)) (h14 : X 14 = VG.Proof.Blake2.ArmS.flagW f) (h15 : X 15 = 0) (k : Nat)
    (hk : k < 16) : VG.Proof.Blake2.ArmS.initW H X k = (VG.Proof.Blake2.ArmS.initV h N f)[k] := by
  have ha : ∀ j (hj : j < 16), (h ++ Spec.Blake2.s.IV)[j] =
      if h8 : j < 8 then (h[j]'(by omega)) else Spec.Blake2.s.IV[j - 8] := fun j hj => Vector.getElem_append hj
  have hg : ∀ j (hj : j < 8), Spec.Blake2.s.IV.toList.getD j 0 = Spec.Blake2.s.IV[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, hj]
  unfold VG.Proof.Blake2.ArmS.initW VG.Proof.Blake2.ArmS.initV
  rcases (by omega : k < 8 ∨ (8 ≤ k ∧ k < 12) ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    h8 | h8 | rfl | rfl | rfl | rfl
  · have : 12 ≠ k ∧ 13 ≠ k ∧ 14 ≠ k := by omega
    cases f <;> simp [h8, this, ha k hk, hH k h8]
  · have : 12 ≠ k ∧ 13 ≠ k ∧ 14 ≠ k := by omega
    simp only [show ¬ k < 8 by omega, h8.2, ↓reduceIte]
    rw [hg (k - 8) (by omega)]
    cases f <;> simp [show ¬ k < 8 by omega, this, ha k hk]
  · cases f <;> simp [ha, h12]
  · cases f <;> simp [ha, h13]
  · cases f <;> simp [ha, h14, VG.Proof.Blake2.ArmS.flagW]
  · cases f <;> simp [ha, h15]

theorem F_eq (h : HashValue 32) (m : VG.Spec.Blake2.Block 32) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.s h m t f =
      Vector.ofFn fun i => (h[i]'(by omega)) ^^^ ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (VG.Proof.Blake2.ArmS.initV h t f))[i] ^^^
        ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (VG.Proof.Blake2.ArmS.initV h t f))[i.val + 8] := rfl

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 32 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt 32 m (State.addr st))[k] = m.readW (A st (4 * k)) 32 := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn]
  rw [A_eq (by omega)]

theorem blockAt_get {bk : BitVec 32} (hfit : bk.toNat + 64 ≤ 2 ^ 32) (m : Mem) {j : Nat} (hj : j < 16) :
    Spec.Blake2.blockAt 32 m (State.addr bk) ⟨j, hj⟩ = m.readW (A bk (4 * j)) 32 := by
  rw [Proof.Blake2.blockAt_word, A_eq (by omega)]

theorem lo_ofNat (N : Nat) : lo (BitVec.ofNat 64 N) = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem hi_ofNat (N : Nat) : hi (BitVec.ofNat 64 N) = BitVec.ofNat 32 (N / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch space. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (VG.Proof.Blake2.ArmS.scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_off : ∀ p ∈ saved, 108 ≤ p.2 ∧ p.2 + 4 ≤ 144 := by decide

/-- What holds between blocks, after `i` of them: everything is in `scratch`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = VG.Proof.Blake2.ArmS.scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Blake2.ArmS.stR s₀, VG.Proof.Blake2.ArmS.scrR s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 32 s.mem (State.addr (VG.Proof.Blake2.ArmS.stp s₀)) =
    Spec.Blake2.compressBlocks Spec.Blake2.s (VG.Proof.Blake2.ArmS.H₀ s₀) s₀.mem (State.addr (VG.Proof.Blake2.ArmS.bp s₀)) i (VG.Proof.Blake2.ArmS.t₀ s₀) (VG.Proof.Blake2.ArmS.fl s₀)
  saved : VG.Proof.Blake2.ArmS.Saved s₀ s.mem
  st : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) stOff) 32 = VG.Proof.Blake2.ArmS.stp s₀
  blk : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) blkOff) 32 = VG.Proof.Blake2.ArmS.blkAddr s₀ i
  n : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) nOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - i)
  tlo : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) tOff) 32 = lo (BitVec.ofNat 64 (VG.Proof.Blake2.ArmS.t₀ s₀ + i * 64))
  thi : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) (tOff + 4)) 32 = hi (BitVec.ofNat 64 (VG.Proof.Blake2.ArmS.t₀ s₀ + i * 64))
  f : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) fOff) 32 = VG.Proof.Blake2.ArmS.flagW (VG.Proof.Blake2.ArmS.fl s₀)
  z : s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) (fOff + 4)) 32 = 0

theorem compressBlocks_succ' (H : HashValue 32) (m : Mem) (p : Addr) (i t : Nat) (f : Bool) :
    Spec.Blake2.compressBlocks Spec.Blake2.s H m p (i + 1) t f =
      Spec.Blake2.F Spec.Blake2.s (Spec.Blake2.compressBlocks Spec.Blake2.s H m p i t f)
        (Spec.Blake2.blockAt 32 m (p + BitVec.ofNat 64 (64 * i))) (t + i * 64) f :=
  Proof.Blake2.compressBlocks_succ _ _ _ _ _ _ _

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.ArmS.nb s₀) {s : State} (hL : VG.Proof.Blake2.ArmS.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Blake2.ArmS.LInv s₀ (VG.Proof.Blake2.ArmS.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Blake2.ArmS.nb s₀ ∧ VG.Proof.Blake2.ArmS.LInv s₀ (i + 1) s') := by
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set N := VG.Proof.Blake2.ArmS.t₀ s₀ + i * 64 with hN
  set H := Spec.Blake2.compressBlocks Spec.Blake2.s (VG.Proof.Blake2.ArmS.H₀ s₀) s₀.mem (State.addr (VG.Proof.Blake2.ArmS.bp s₀)) i (VG.Proof.Blake2.ArmS.t₀ s₀) (VG.Proof.Blake2.ArmS.fl s₀)
    with hH
  set M := Spec.Blake2.blockAt 32 s₀.mem (State.addr (VG.Proof.Blake2.ArmS.blkAddr s₀ i)) with hM
  have hHk : ∀ k (hk : k < 8), s.mem.readW (A (VG.Proof.Blake2.ArmS.stp s₀) (4 * k)) 32 = (H[k]'(by omega)) := fun k hk => by
    rw [← VG.Proof.Blake2.ArmS.stateAt_get fitS _ hk, hL.state]
  have wV : ∀ o, o + 4 ≤ 512 → InRegions s.wr (A (VG.Proof.Blake2.ArmS.scp s₀) o) 4 := by rw [hL.wr]; exact fun o ho => hp.out_scr ho
  have dScr : ∀ d, d + 4 ≤ 512 → Region.Disjoint ⟨State.addr (VG.Proof.Blake2.ArmS.scp s₀) + BitVec.ofNat 64 d, 4⟩ (VG.Proof.Blake2.ArmS.stR s₀) :=
    fun d hd => (hp.st_scr.sub_right (Offset.sub_base _ (by omega))).symm
  -- Initialize the work vector.
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.init_ok (V := VG.Proof.Blake2.ArmS.scp s₀) (st := VG.Proof.Blake2.ArmS.stp s₀) (B := VG.Proof.Blake2.ArmS.blkAddr s₀ i) hL.r12 fitV fitS fitB wV
    (by rw [hL.rd, hL.wr]; exact fun o ho => hp.in_st ho) (by rw [hL.rd, hL.wr]; exact hp.blk_rd hi)
    hL.st hL.blk ((hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)))
    hp.st_scr) fun s₁ h₁ => ?_)
  have hv : ∀ k (hk : k < 16), VG.Proof.Blake2.ArmS.Holds (VG.Proof.Blake2.ArmS.scp s₀) s₁ k (VG.Proof.Blake2.ArmS.initV H N (VG.Proof.Blake2.ArmS.fl s₀))[k] := fun k hk => by
    rw [← VG.Proof.Blake2.ArmS.initW_eq H N (VG.Proof.Blake2.ArmS.fl s₀) hHk ?_ ?_ ?_ ?_ k hk]
    · exact h₁.vars k hk
    · show s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) tOff) 32 = _; rw [hL.tlo, VG.Proof.Blake2.ArmS.lo_ofNat]
    · show s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) (tOff + 4)) 32 = _; rw [hL.thi, VG.Proof.Blake2.ArmS.hi_ofNat]
    · exact hL.f
    · exact hL.z
  -- The rounds.
  have rc : VG.Proof.Blake2.ArmS.RCtx (VG.Proof.Blake2.ArmS.scp s₀) M s₁ :=
    ⟨h₁.r12, fitV, by rw [h₁.wr]; exact wV, fun j hj => by
      rw [h₁.msg j hj, hp.blk_frame hL.frame hi (by omega), hM, VG.Proof.Blake2.ArmS.blockAt_get fitB _ hj]⟩
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.rounds_ok rc hv 10) fun s₂ h₂ => ?_)
  -- XOR into the state.
  set v := (List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s M) (VG.Proof.Blake2.ArmS.initV H N (VG.Proof.Blake2.ArmS.fl s₀)) with hv'
  have hst₁ : ∀ d, (d = 80 ∨ 88 ≤ d) → d + 4 ≤ 512 →
      s₁.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := fun d h1 h2 =>
    hp.scr_frame h2 h₁.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by simp only [blkOff]; omega) (by omega) (by simp only [blkOff]; omega)
  have hst₂ : ∀ d, 80 ≤ d → d + 4 ≤ 512 →
      s₂.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = s₁.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := fun d h1 h2 =>
    hp.scr_frame h2 h₂.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have fc : VG.Proof.Blake2.ArmS.FCtx (VG.Proof.Blake2.ArmS.scp s₀) (VG.Proof.Blake2.ArmS.stp s₀) v s₂ :=
    ⟨fitS, fitV, by rw [h₂.wr, h₁.wr, hL.wr]; exact fun o ho => hp.out_st ho,
      by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hL.rd, hL.wr]; exact fun o ho => hp.in_scr ho,
      fun k hk => (VG.Proof.Blake2.ArmS.holds_c (by omega) (by omega)).mp (h₂.vars (k + 8) (by omega)), hp.st_scr⟩
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.fin_ok fc h₂.vars (by rw [h₂.r12, h₁.r12])
    (by rw [hst₂ stOff (by decide) (by decide), hst₁ stOff (.inl rfl) (by decide)]; exact hL.st))
    fun s₃ ⟨r12₃, r8₃, r9₃, r10₃, rd₃, wr₃, sp₃, f₃, w₃⟩ => ?_)
  have hst₃ : ∀ d, d + 4 ≤ 512 → s₃.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = s₂.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 :=
    fun d h2 => hp.scr_frame h2 f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dScr d h2
  have hs : ∀ d, (d = 80 ∨ 88 ≤ d) → d + 4 ≤ 512 →
      s₃.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = s.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := fun d h1 h2 => by
    rw [hst₃ d h2, hst₂ d (by omega) h2, hst₁ d h1 h2]
  -- Advance the counter.
  have wV₃ : ∀ d, d + 4 ≤ 512 → InRegions s₃.wr (A (VG.Proof.Blake2.ArmS.scp s₀) d) 4 := by
    rw [wr₃, h₂.wr, h₁.wr]; exact wV
  refine WP.mono (VG.Proof.Blake2.ArmS.advance_ok (N := N) r12₃ r8₃ r9₃ r10₃ wV₃
    (by rw [hs tOff (by decide) (by decide)]; exact hL.tlo)
    (by rw [hs (tOff + 4) (by decide) (by decide)]; exact hL.thi))
    fun s₄ ⟨z₄, r12₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  have hs₄ : ∀ d, d + 4 ≤ 512 → (d + 4 ≤ 80 ∨ 100 ≤ d) →
      s₄.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 = s₃.mem.readW (A (VG.Proof.Blake2.ArmS.scp s₀) d) 32 := fun d h2 h3 => by
    rw [m₄, VG.Proof.Blake2.ArmS.ctrMem, VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ h2 (by decide) (by simp only [nOff]; omega),
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ h2 (by decide) (by simp only [blkOff]; omega),
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ h2 (by decide) (by simp only [stOff]; omega),
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ h2 (by decide) (by simp only [tOff]; omega),
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ h2 (by decide) (by simp only [tOff]; omega)]
  have hc : Frame [VG.Proof.Blake2.ArmS.scrR s₀] s₃.mem s₄.mem := by
    have c : ∀ d, d + 4 ≤ 512 → (VG.Proof.Blake2.ArmS.scrR s₀).Contains (A (VG.Proof.Blake2.ArmS.scp s₀) d) (32 / 8) := fun d hd => by
      rw [hp.scr_addr (by omega)]; exact contains_offset hd (by omega)
    have m := List.mem_singleton_self (VG.Proof.Blake2.ArmS.scrR s₀)
    rw [m₄]
    exact ((((((Frame.refl _ _).writeW m _ (c _ (by decide))).writeW m _ (c _ (by decide))).writeW m _
      (c _ (by decide))).writeW m _ (c _ (by decide))).writeW m _ (c _ (by decide)))
  -- The state.
  have hstate : Spec.Blake2.stateAt 32 s₄.mem (State.addr (VG.Proof.Blake2.ArmS.stp s₀)) = Spec.Blake2.F Spec.Blake2.s H M N (VG.Proof.Blake2.ArmS.fl s₀) := by
    refine Vector.ext fun k hk => ?_
    have hk8 : k < 8 := hk
    have hw : Frame [VG.Proof.Blake2.ArmS.scrR s₀] s.mem s₂.mem :=
      (h₁.frame.sub fun r hr => ⟨VG.Proof.Blake2.ArmS.scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Region.sub_prefix (by omega)
        · exact Offset.sub_base _ (by simp only [blkOff]; omega)⟩).trans
      (h₂.frame.sub fun r hr => ⟨VG.Proof.Blake2.ArmS.scrR s₀, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)
    rw [VG.Proof.Blake2.ArmS.stateAt_get fitS _ hk8, hp.st_frame hc hk8, w₃ k hk8, hp.st_frame hw hk8, hHk k hk8, VG.Proof.Blake2.ArmS.F_eq,
      Vector.getElem_ofFn, BitVec.xor_assoc]
    rfl
  have hsub : ∀ r ∈ VG.Proof.Blake2.ArmS.initR (VG.Proof.Blake2.ArmS.scp s₀), ∃ r' ∈ [VG.Proof.Blake2.ArmS.stR s₀, VG.Proof.Blake2.ArmS.scrR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨VG.Proof.Blake2.ArmS.scrR s₀, by simp, ?_⟩
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega)
    · exact Offset.sub_base _ (by simp only [blkOff]; omega)
  have hframe : Frame [VG.Proof.Blake2.ArmS.stR s₀, VG.Proof.Blake2.ArmS.scrR s₀] s₀.mem s₄.mem :=
    (((hL.frame.trans (h₁.frame.sub hsub)).trans (h₂.frame.sub fun r hr => ⟨VG.Proof.Blake2.ArmS.scrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega)⟩)).trans
      (f₃.mono (by simp))).trans (hc.mono (by simp))
  have hnb : VG.Proof.Blake2.ArmS.nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hn : s₃.gpr .r10 = BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - i) := by
    rw [r10₃, hst₂ nOff (by decide) (by decide), hst₁ nOff (by decide) (by decide)]; exact hL.n
  have hn1 : BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - i) - 1 = BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - (i + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hN1 : N + 64 = VG.Proof.Blake2.ArmS.t₀ s₀ + (i + 1) * 64 := by rw [hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have hL' : VG.Proof.Blake2.ArmS.LInv s₀ (i + 1) s₄ := by
    refine ⟨r12₄, by rw [rd₄, rd₃, h₂.rd, h₁.rd, hL.rd],
      by rw [wr₄, wr₃, h₂.wr, h₁.wr, hL.wr], by rw [sp₄, sp₃, h₂.sp, h₁.sp, hL.sp], hframe, ?_,
      fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstate, VG.Proof.Blake2.ArmS.compressBlocks_succ', ← hH, hM, hp.blk_addr hi]
    · have := VG.Proof.Blake2.ArmS.saved_off p hp'
      rw [hs₄ p.2 (by omega) (by omega), hs p.2 (by omega) (by omega)]; exact hL.saved p hp'
    · rw [m₄, VG.Proof.Blake2.ArmS.ctrMem, VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [m₄, VG.Proof.Blake2.ArmS.ctrMem, VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
        hst₂ blkOff (by decide) (by decide), h₁.blk]
      simp only [VG.Proof.Blake2.ArmS.blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [m₄, VG.Proof.Blake2.ArmS.ctrMem]
      show (_ : Mem).readW (A (VG.Proof.Blake2.ArmS.scp s₀) nOff) 32 = _
      rw [Mem.readW_writeW_self32, ← r10₃, hn, hn1]
    · rw [m₄, VG.Proof.Blake2.ArmS.ctrMem, VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hN1]
    · rw [m₄, VG.Proof.Blake2.ArmS.ctrMem, VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide),
        VG.Proof.Blake2.ArmS.readW_writeW_scr hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hN1]
    · rw [hs₄ fOff (by decide) (by decide), hs fOff (by decide) (by decide)]; exact hL.f
    · rw [hs₄ (fOff + 4) (by decide) (by decide), hs (fOff + 4) (by decide) (by decide)]; exact hL.z
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, ← r10₃, hn, hn1]
  by_cases hlast : i + 1 = VG.Proof.Blake2.ArmS.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hL'⟩
  · right
    have hne : VG.Proof.Blake2.ArmS.nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Blake2.ArmS.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    exact ⟨by rw [hev]; simpa using h0, by omega, hL'⟩

/-! ## The prologue's memory -/

theorem setupMem_frame {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) : Frame [VG.Proof.Blake2.ArmS.scrR s₀] s₀.mem (VG.Proof.Blake2.ArmS.setupMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (VG.Proof.Blake2.ArmS.scrR s₀).Contains (A (VG.Proof.Blake2.ArmS.scp s₀) d) (32 / 8) :=
    fun d hd => by rw [hp.scr_addr (by omega)]; exact contains_offset hd (by have := hp.scr_fits; omega)
  have m := List.mem_singleton_self (VG.Proof.Blake2.ArmS.scrR s₀)
  have key : ∀ (l : List (Nat × BitVec 32)), (∀ p ∈ l, p.1 + 4 ≤ 512) → ∀ m₀ : Mem,
      Frame [VG.Proof.Blake2.ArmS.scrR s₀] s₀.mem m₀ →
      Frame [VG.Proof.Blake2.ArmS.scrR s₀] s₀.mem (l.foldl (fun m p => m.writeW (A (VG.Proof.Blake2.ArmS.scp s₀) p.1) p.2) m₀) := by
    intro l
    induction l with
    | nil => intro _ m₀ h; exact h
    | cons p ps ih =>
      intro hl m₀ h
      exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
        (h.writeW m _ (c p.1 (hl p List.mem_cons_self)))
  have hl : ∀ p ∈ VG.Proof.Blake2.ArmS.setupWrites s₀, p.1 + 4 ≤ 512 := by
    intro p hp
    simp only [VG.Proof.Blake2.ArmS.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> exact Nat.le_of_ble_eq_true rfl
  exact key _ hl _ (Frame.refl _ _)

theorem linv_zero {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) {s₁ : State} (hm : s₁.mem = VG.Proof.Blake2.ArmS.setupMem s₀)
    (h12 : s₁.gpr .r12 = VG.Proof.Blake2.ArmS.scp s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) :
    VG.Proof.Blake2.ArmS.LInv s₀ 0 s₁ := by
  have hf := VG.Proof.Blake2.ArmS.setupMem_frame hp
  refine ⟨h12, hrd, hwr, hsp, by rw [hm]; exact hf.mono (by simp), ?_, fun p hp' => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · refine Vector.ext fun k hk => ?_
    rw [hm, VG.Proof.Blake2.ArmS.stateAt_get hp.st_fits _ hk, hp.st_frame hf hk, ← VG.Proof.Blake2.ArmS.stateAt_get hp.st_fits _ hk]
    rfl
  all_goals simp only [hm, A, stOff, blkOff, nOff, tOff, fOff]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
    simp [VG.Proof.Blake2.ArmS.blkAddr]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
    simp [VG.Proof.Blake2.ArmS.nb]
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
    rw [Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (Proof.Sha512.Arm.lo_append _ _).symm
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
    rw [Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (Proof.Sha512.Arm.hi_append _ _).symm
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32,
      VG.Proof.Blake2.ArmS.readW_writeW_scr hp]
    exact VG.Proof.Blake2.ArmS.flag_eq _
  · simp (config := {decide := true}) only [VG.Proof.Blake2.ArmS.setupMem, VG.Proof.Blake2.ArmS.setupWrites, List.foldl, A, Mem.readW_writeW_self32]

/-! ## The epilogue -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) {s : State} (hc : VG.Proof.Blake2.ArmS.LInv s₀ (VG.Proof.Blake2.ArmS.nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (VG.Proof.Blake2.compressArm Spec.Blake2.s).post s₀ s' := by
  have i : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 d)) 4 :=
    fun d hd => by rw [hc.rd, hc.wr]; exact hp.in_scr hd
  have i0 := i 108 (by decide); have i1 := i 112 (by decide); have i2 := i 116 (by decide)
  have i3 := i 120 (by decide); have i4 := i 124 (by decide); have i5 := i 128 (by decide)
  have i6 := i 132 (by decide); have i7 := i 136 (by decide); have i8 := i 140 (by decide)
  have g : ∀ p ∈ saved, s.mem.readW (State.addr (stackArg s₀ 3 + BitVec.ofNat 32 p.2)) 32 = s₀.gpr p.1 :=
    hc.saved
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := g
  have hstate := hc.state
  have hr12 := hc.r12
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, saved, Impl.Blake2.Arm.S.S, List.map_cons, List.map_nil,
    runBlock_cons, runStep_some, runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hr12, i0, i1, i2, i3, i4, i5, i6, i7, i8, ite_true,
    ite_false, g0, g1, g2, g3, g4, g5, g6, g7, g8, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Blake2.ArmS.Pre s₀) :
    WP isa Impl.Blake2.Arm.S.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (VG.Proof.Blake2.compressArm Spec.Blake2.s).post s₀ s' := by
  unfold Impl.Blake2.Arm.S.compress
  refine WP.seq (WP.mono (VG.Proof.Blake2.ArmS.setup_ok hp) fun s₁ ⟨m₁, r12₁, z₁, rd₁, wr₁, sp₁⟩ => ?_)
  have hL₀ := VG.Proof.Blake2.ArmS.linv_zero hp m₁ r12₁ rd₁ wr₁ sp₁
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.ArmS.LInv s₀ (VG.Proof.Blake2.ArmS.nb s₀)) ?_ fun s₂ hc => VG.Proof.Blake2.ArmS.restore_ok hp hc)
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by rw [← z₁]; rfl) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Blake2.ArmS.nb s₀ = 0 := by simp at h; simp [VG.Proof.Blake2.ArmS.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀)
  · have hpos : 0 < VG.Proof.Blake2.ArmS.nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Blake2.ArmS.nb s₀ - i ∧ i < VG.Proof.Blake2.ArmS.nb s₀ ∧ VG.Proof.Blake2.ArmS.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Blake2.ArmS.LInv s₀ (VG.Proof.Blake2.ArmS.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Blake2.ArmS.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Blake2.ArmS.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Blake2.ArmS.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-! ## Verified -/

/-- The initial taint: `r0`–`r2` are public, and so are the 16 bytes of stack
arguments. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [32, 512], argLen := 16, argBases := [(12, 1)] }

theorem argByte_eq {s : State} (hsp : s.sp.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem wf₀ {s : State} (hp : VG.Proof.Blake2.ArmS.Pre s) : VG.Arm.Taint.Wf VG.Proof.Blake2.ArmS.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.ArmS.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hp.sp_fits, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [VG.Proof.Blake2.ArmS.addr_toNat] <;> omega
  · have e : (⟨State.addr s.sp, 16⟩ : Region) = VG.Proof.Blake2.ArmS.argR s := by simp [stackArgAddr]
    simp only [VG.Proof.Blake2.ArmS.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [VG.Proof.Blake2.ArmS.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (VG.Proof.Blake2.compressArm Spec.Blake2.s).pre s₁)
    (h₂ : (VG.Proof.Blake2.compressArm Spec.Blake2.s).pre s₂) (hpub : (VG.Proof.Blake2.compressArm Spec.Blake2.s).pub s₁ s₂) :
    VG.Arm.Taint.Agree VG.Proof.Blake2.ArmS.τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, a0, a1, a2, a3⟩ := hpub
  have hp₁ := VG.Proof.Blake2.ArmS.pre_of _ h₁; have hp₂ := VG.Proof.Blake2.ArmS.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.ArmS.wf₀ hp₁, VG.Proof.Blake2.ArmS.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [VG.Proof.Blake2.ArmS.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Blake2.ArmS.stR, VG.Proof.Blake2.ArmS.scrR, VG.Proof.Blake2.ArmS.stp, VG.Proof.Blake2.ArmS.scp, p0, a3]
  · simp only [VG.Proof.Blake2.ArmS.τ₀] at hk
    rw [VG.Proof.Blake2.ArmS.argByte_eq hp₁.sp_fits hk, VG.Proof.Blake2.ArmS.argByte_eq hp₂.sp_fits hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

/-- A state satisfying the precondition (with no blocks, and the scratch space at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩, ⟨0x4000, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0, 512⟩]

/-- The proof, against the ARMv7 contract the streaming functions use. -/
theorem compress_verified' :
    Verified Arm.target Impl.Blake2.Arm.S.compress (VG.Proof.Blake2.compressArm Spec.Blake2.s) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Blake2.ArmS.correct (VG.Proof.Blake2.ArmS.pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := taint) VG.Proof.Blake2.ArmS.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Blake2.ArmS.agree₀ h₁ h₂ hpub)
      (by taint_decide)
  · refine ⟨VG.Proof.Blake2.ArmS.sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem compress_noCalls : Impl.Blake2.Arm.S.compress.noCalls = true := by
  lit_decide

theorem compress_implies :
    (VG.Proof.Blake2.compressArm Spec.Blake2.s).Implies (Spec.Blake2.compressSContract Arm.abi) := by
  sig_implies [Spec.Blake2.compressSContract, Spec.Blake2.compressSSig, VG.Proof.Blake2.compressArm, tArm, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Blake2.blockBytes]
    [sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.ArmS.sat

/-- The proof, against the shared contract of `Spec/Blake2/Contract.lean`. -/
theorem compress_verified :
    Verified Arm.target Impl.Blake2.Arm.S.compress (Spec.Blake2.compressSContract Arm.abi) :=
  compress_verified'.of_implies VG.Proof.Blake2.ArmS.compress_implies

end VG.Proof.Blake2.ArmS

end
