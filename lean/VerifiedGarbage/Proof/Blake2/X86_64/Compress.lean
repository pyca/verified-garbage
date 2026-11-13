module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Proof.Blake2.X86_64.Contract
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.X86_64.Lit
public import VerifiedGarbage.Impl.Blake2.X86_64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Blake2.Spec
meta import VerifiedGarbage.Proof.Blake2.X86_64.Contract
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Blake2.X86_64.Lit
meta import VerifiedGarbage.Impl.Blake2.X86_64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# BLAKE2 compression function on x86-64

The proof, for BLAKE2b and BLAKE2s at once (words of `w = 64` or `32` bits),
that `Impl.Blake2.X86_64.compress P` meets `compressX86_64 P`
(`Proof/Blake2/X86_64/Contract.lean`): `compress_correct` and `compressB_ct`,
`compressS_ct`; and from them `compressB_verified` and `compressS_verified`
against the shared contracts of `Spec/Blake2/Contract.lean`.

Each half of a `G` (`halfG`) is executed symbolically once per word size
(`halfOk`) and composed by `round_ok`; `Holds` says where each word of the
work vector is. The code runs a half-round's four `G`s a half at a time,
which `cols_halves` and `diags_halves` show is the spec's order of them.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64

open VG VG.X86_64 VG.Impl.Blake2.X86_64
open VG.Spec.Blake2 (Params Work Block G)
open VG.Proof.Blake2 (mix G_get)

variable {w : Nat}

/-- What the proofs need of the parameters: the words are 64 or 32 bits, and
the rotation counts are ones the rotate instructions take. -/
structure Ok (P : Params w) : Prop where
  hw : w = 64 ∨ w = 32
  r1 : 1 ≤ P.R1 ∧ P.R1 < w
  r2 : 1 ≤ P.R2 ∧ P.R2 < w
  r3 : 1 ≤ P.R3 ∧ P.R3 < w
  r4 : 1 ≤ P.R4 ∧ P.R4 < w

theorem ok_b : Ok Spec.Blake2.b := ⟨.inl rfl, by decide, by decide, by decide, by decide⟩
theorem ok_s : Ok Spec.Blake2.s := ⟨.inr rfl, by decide, by decide, by decide, by decide⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The address of `scr + d` as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

/-! ## Addresses in `scratch` -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  rw [off, ofInt_natCast]

theorem off_sep (p : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32)
    (he : e + k < 2 ^ 32) : Mem.Sep (off p d) n (off p e) k := by
  rw [off_eq, off_eq]; exact Offset.sep p h (by omega_using [hd]) (by omega_using [he])

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 32) :
    (⟨base, len⟩ : Region).Contains (off base d) n := by
  rw [off_eq]; exact Offset.contains_base base h (by omega_using [hd])

/-- A `w`-bit word written and read back. -/
theorem readW_writeW_self' (hw : w = 64 ∨ w = 32) (m : Mem) (a : Addr) (v : BitVec w) :
    (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

/-- Reading after a write elsewhere in `scratch`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hd : d + w / 8 < 2 ^ 32) (he : e + w' / 8 < 2 ^ 32) (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hw : w / 8 ≤ 8) :
    (m.writeW (off p e) v).readW (off p d) w = m.readW (off p d) w :=
  Mem.readW_writeW_sep (off_sep p h hd he) (by omega_using [hw])

/-! ## Half a `G` -/

/-- Half of `G` (RFC 7693 §3.1) on the words `a, b, c, d` of `v`, with the
message word `x` and the rotations `n1` and `n2`: `G` is two of them
(`G_halves`). -/
def halfG (n1 n2 : Nat) (v : Work w) (a b c d : Fin 16) (x : BitVec w) : Work w :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d ((v[d] ^^^ v[a]).rotateRight n1)
  let v := v.set c (v[c] + v[d])
  v.set b ((v[b] ^^^ v[c]).rotateRight n2)

theorem G_halves (P : Params w) (v : Work w) (a b c d : Fin 16) (x y : BitVec w) :
    G P v a b c d x y = halfG P.R3 P.R4 (halfG P.R1 P.R2 v a b c d x) a b c d y := rfl

/-- `halfG` on the four words: the new `a`, `b`, `c` and `d`. -/
def hmix (n1 n2 : Nat) (va vb vc vd x : BitVec w) : BitVec w × BitVec w × BitVec w × BitVec w :=
  let a := va + vb + x
  let d := (vd ^^^ a).rotateRight n1
  let c := vc + d
  (a, (vb ^^^ c).rotateRight n2, c, d)

/-- Word `k` after `halfG` on four distinct words. -/
theorem halfG_get (n1 n2 : Nat) (v : Work w) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1) (x : BitVec w)
    (k : Nat) (hk : k < 16) :
    (halfG n1 n2 v a b c d x)[k]'hk =
      if b.1 = k then (hmix n1 n2 (v[a]'a.2) (v[b]'b.2) (v[c]'c.2) (v[d]'d.2) x).2.1
      else if c.1 = k then (hmix n1 n2 (v[a]'a.2) (v[b]'b.2) (v[c]'c.2) (v[d]'d.2) x).2.2.1
      else if d.1 = k then (hmix n1 n2 (v[a]'a.2) (v[b]'b.2) (v[c]'c.2) (v[d]'d.2) x).2.2.2
      else if a.1 = k then (hmix n1 n2 (v[a]'a.2) (v[b]'b.2) (v[c]'c.2) (v[d]'d.2) x).1
      else v[k]'hk := by
  simp only [halfG, Proof.Blake2.set_get, Proof.Blake2.set_get_fin, hab, hac, had,
    Ne.symm hbc, Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  by_cases eb : b.1 = k
  · subst eb; simp only [ite_true, hab, hbc.symm, hbd.symm, ite_false, hmix]
  by_cases ec : c.1 = k
  · subst ec; simp only [ite_true, eb, hac, hcd.symm, ite_false, hmix]
  by_cases ed : d.1 = k
  · subst ed; simp only [ite_true, eb, ec, had, ite_false, hmix]
  by_cases ea : a.1 = k
  · subst ea; simp only [ite_true, eb, ec, ed, ite_false, hmix]
  simp only [eb, ec, ed, ea, ite_false]

theorem halfG_getP (n1 n2 : Nat) (v : Work w) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1) (x : BitVec w)
    (k : Nat) (hk : k < 16) :
    (halfG n1 n2 v a b c d x)[k]'hk =
      if b.1 = k then (hmix n1 n2 (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2) x).2.1
      else if c.1 = k then (hmix n1 n2 (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2) x).2.2.1
      else if d.1 = k then (hmix n1 n2 (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2) x).2.2.2
      else if a.1 = k then (hmix n1 n2 (v[a.1]'a.2) (v[b.1]'b.2) (v[c.1]'c.2) (v[d.1]'d.2) x).1
      else v[k]'hk :=
  halfG_get n1 n2 v hab hac had hbc hbd hcd x k hk

theorem cases16 {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega

/-- The value of a literal index. -/
theorem val_lit (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

/-- Four `G`s on the words `q 0`, …, `q 3` (the columns or the diagonals),
as the code runs them: their first halves, then their second halves. -/
def quadH (P : Params w) (q : Nat → Fin 16 × Fin 16 × Fin 16 × Fin 16) (x y : Nat → BitVec w)
    (v : Work w) : Work w :=
  let H (n1 n2 : Nat) (k : Nat) (z : Nat → BitVec w) (v : Work w) :=
    halfG n1 n2 v (q k).1 (q k).2.1 (q k).2.2.1 (q k).2.2.2 (z k)
  H P.R3 P.R4 3 y <| H P.R3 P.R4 2 y <| H P.R3 P.R4 1 y <| H P.R3 P.R4 0 y <|
  H P.R1 P.R2 3 x <| H P.R1 P.R2 2 x <| H P.R1 P.R2 1 x <| H P.R1 P.R2 0 x v

def colsF : Nat → Fin 16 × Fin 16 × Fin 16 × Fin 16
  | 0 => (0, 4, 8, 12) | 1 => (1, 5, 9, 13) | 2 => (2, 6, 10, 14) | _ => (3, 7, 11, 15)
def diagsF : Nat → Fin 16 × Fin 16 × Fin 16 × Fin 16
  | 0 => (0, 5, 10, 15) | 1 => (1, 6, 11, 12) | 2 => (2, 7, 8, 13) | _ => (3, 4, 9, 14)

theorem cols_halves (P : Params w) (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = quadH P colsF x y v := by
  simp only [G_halves, quadH, colsF]
  apply Vector.ext
  intro j hj
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [halfG_getP, val_lit, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]

theorem diags_halves (P : Params w) (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) = quadH P diagsF x y v := by
  simp only [G_halves, quadH, diagsF]
  apply Vector.ext
  intro j hj
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [halfG_getP, val_lit, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte]

/-- Round `r` as the code runs it. -/
theorem round_halves (P : Params w) (m : Block w) (v : Work w) (r : Nat) :
    Spec.Blake2.round P m v r =
      quadH P diagsF (fun k => m (Spec.Blake2.sigmaAt r (2 * (4 + k)))) (fun k => m (Spec.Blake2.sigmaAt r (2 * (4 + k) + 1)))
        (quadH P colsF (fun k => m (Spec.Blake2.sigmaAt r (2 * k))) (fun k => m (Spec.Blake2.sigmaAt r (2 * k + 1))) v) := by
  rw [← cols_halves, ← diags_halves]
  rfl

/-! ## Where the words are during the rounds -/

/-- The slot of word `k` of the work vector. -/
abbrev slot (scr : Addr) (k : Nat) : Addr := off scr (vOff k)

/-- Word `k` is in the third row, whose words are in their slots during the
rounds. -/
abbrev third (k : Nat) : Prop := 8 ≤ k ∧ k ≤ 11

theorem halfOk (hw : w = 64 ∨ w = 32) {n1 n2 : Nat} (r1 : 1 ≤ n1 ∧ n1 < w) (r2 : 1 ≤ n2 ∧ n2 < w)
    {a b d : Reg} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha9 : a ≠ .r9) (hb9 : b ≠ .r9)
    (hd9 : d ≠ .r9) (hai : a ≠ .rsi) (hbi : b ≠ .rsi) (hdi : d ≠ .rsi) {s : State} {scr : Addr}
    (h9 : s.gpr .r9 = scr) {c j : Nat}
    (hij : InRegions (s.rd ++ s.wr) (off scr (msgOff w j)) (w / 8))
    (hic : InRegions (s.rd ++ s.wr) (slot scr c) (w / 8)) (hoc : InRegions s.wr (slot scr c) (w / 8))
    (va vb vc vd x : BitVec w)
    (ha : s.gpr a = va.setWidth 64) (hb : s.gpr b = vb.setWidth 64) (hd : s.gpr d = vd.setWidth 64)
    (hc : s.mem.readW (slot scr c) w = vc) (hx : s.mem.readW (off scr (msgOff w j)) w = x) :
    WP isa (.block (half (w := w) a b c d j n1 n2)) s fun s' =>
      s'.gpr a = (hmix n1 n2 va vb vc vd x).1.setWidth 64 ∧
      s'.gpr b = (hmix n1 n2 va vb vc vd x).2.1.setWidth 64 ∧
      s'.gpr d = (hmix n1 n2 va vb vc vd x).2.2.2.setWidth 64 ∧
      s'.mem = s.mem.writeW (slot scr c) (hmix n1 n2 va vb vc vd x).2.2.1 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ d → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨r1, r1'⟩ := r1; obtain ⟨r2, r2'⟩ := r2
  have e : va + x + vb = va + vb + x := by rw [BitVec.add_assoc, BitVec.add_comm x, ← BitVec.add_assoc]
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] at hij hic hoc
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, half, ld, st, Impl.Blake2.X86_64.add, Impl.Blake2.X86_64.xor, ror,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
      State.load64, State.store64, ea_at, isa,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
      ha, hb, hc, hd, hx, h9, hij, hic, hoc,
      hab, had, hbd, hab.symm, had.symm, hbd.symm, ha9.symm, hb9.symm, hd9.symm,
      hai, hbi, hdi, hai.symm, hbi.symm, hdi.symm, r1, r2, Nat.le_of_lt_succ r1', Nat.le_of_lt_succ r2',
      and_self, BitVec.setWidth_eq, e, hmix,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], by trivial⟩
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, Nat.reducePow, half, ld, st, Impl.Blake2.X86_64.add,
      Impl.Blake2.X86_64.xor, ror,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, execShift32, readSrc32,
      State.load32, State.store32, ea_at, isa, State.setReg32,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
      ha, hb, hc, hd, hx, h9, hij, hic, hoc,
      hab, had, hbd, hab.symm, had.symm, hbd.symm, ha9.symm, hb9.symm, hd9.symm,
      hai, hbi, hdi, hai.symm, hbi.symm, hdi.symm, r1, r2, Nat.le_of_lt_succ r1', Nat.le_of_lt_succ r2',
      and_self, RegUpd.setWidth_setWidth_32, e, hmix,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], by trivial⟩

/-- The work vector `v` is in the registers and the third row's slots. -/
def Holds (scr : Addr) (v : Work w) (s : State) : Prop :=
  ∀ k (hk : k < 16), if third k then s.mem.readW (slot scr k) w = (v[k]'hk)
    else s.gpr (wreg k) = (v[k]'hk).setWidth 64

theorem wreg_ne (k : Nat) : wreg k ≠ .r9 ∧ wreg k ≠ .rdi ∧ wreg k ≠ .rsp ∧ wreg k ≠ .rsi := by
  unfold wreg; split <;> decide

/-- The registers of the words outside the third row are distinct. -/
theorem wreg_inj16' : ∀ j < 16, ∀ k < 16, (8 ≤ j ∧ j ≤ 11) ∨ (8 ≤ k ∧ k ≤ 11) ∨ wreg j ≠ wreg k ∨
    j = k := by
  decide

theorem wreg_inj16 (j : Nat) (hj : j < 16) (k : Nat) (hk : k < 16) (tj : ¬third j) (tk : ¬third k)
    (e : wreg j = wreg k) : j = k := by
  rcases wreg_inj16' j hj k hk with h | h | h | h
  exacts [absurd h tj, absurd h tk, absurd e h, h]

/-- The words of a half `G` as the code runs it: `c` in the third row, the
others not, all four distinct. -/
abbrev HSide (a b c d : Nat) : Prop :=
  ¬third a ∧ ¬third b ∧ third c ∧ ¬third d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- The slots of the work vector. -/
abbrev slotsR (scr : Addr) : Region := ⟨off scr 128, 128⟩

/-- `scratch`. -/
abbrev scR (scr : Addr) : Region := ⟨scr, 512⟩

theorem in_sc {rs ws : List Region} {scr : Addr} (hw : scR scr ∈ ws) {d n : Nat} (h : d + n ≤ 512) :
    InRegions (rs ++ ws) (off scr d) n :=
  ⟨scR scr, List.mem_append_right _ hw, contains_off h (by omega_using [h])⟩

theorem out_sc {ws : List Region} {scr : Addr} (hw : scR scr ∈ ws) {d n : Nat} (h : d + n ≤ 512) :
    InRegions ws (off scr d) n :=
  ⟨scR scr, hw, contains_off h (by omega_using [h])⟩

/-- What the rounds need of the state `s₀` at their start: `scratch` may be
written, and the copy of the block read, and it is apart from the third
row's slots. -/
structure Env (w : Nat) (scr : Addr) (s₀ : State) : Prop where
  sc : scR scr ∈ s₀.wr
  msg : ∀ j : Fin 16, InRegions (s₀.rd ++ s₀.wr) (off scr (msgOff w j)) (w / 8)
  sep : ∀ j : Fin 16, ∀ k, third k → Mem.Sep (off scr (msgOff w j)) (w / 8) (slot scr k) (w / 8)

/-- The rounds invariant, relative to the state `s₀` at the start of the
rounds, on the block `m` (its copy in `scratch`). -/
structure RI (scr : Addr) (m : Block w) (v : Work w) (s₀ s : State) : Prop where
  holds : Holds scr v s
  frame : Frame [slotsR scr] s₀.mem s.mem
  msg : ∀ j : Fin 16, s.mem.readW (off scr (msgOff w j)) w = m j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r9 : s.gpr .r9 = scr
  rdi : s.gpr .rdi = s₀.gpr .rdi
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem half_stepR' {n1 n2 : Nat} (hw : w = 64 ∨ w = 32) (r1 : 1 ≤ n1 ∧ n1 < w)
    (r2 : 1 ≤ n2 ∧ n2 < w) {a b c d : Fin 16} (hq : HSide a b c d) (j : Fin 16) {scr : Addr}
    {m : Block w} {v : Work w} {s₀ s : State} (he : Env w scr s₀) (hR : RI scr m v s₀ s) :
    WP isa (.block (half (w := w) (wreg a) (wreg b) c (wreg d) j n1 n2)) s
      (RI scr m (halfG n1 n2 v a b c d (m j)) s₀) := by
  obtain ⟨ta, tb, tc, td, nab, nac, nad, nbc, nbd, ncd⟩ := hq
  have hw8 : w / 8 ≤ 8 := by rcases hw with rfl | rfl <;> decide
  have ga := hR.holds a a.2; rw [ite_eq_right ta] at ga
  have gb := hR.holds b b.2; rw [ite_eq_right tb] at gb
  have gc := hR.holds c c.2; rw [ite_eq_left tc] at gc
  have gd := hR.holds d d.2; rw [ite_eq_right td] at gd
  have rab : wreg a ≠ wreg b := fun e => nab (wreg_inj16 a a.2 b b.2 ta tb e)
  have rad : wreg a ≠ wreg d := fun e => nad (wreg_inj16 a a.2 d d.2 ta td e)
  have rbd : wreg b ≠ wreg d := fun e => nbd (wreg_inj16 b b.2 d d.2 tb td e)
  have hsc : scR scr ∈ s.wr := hR.wr ▸ he.sc
  have hsl : vOff c + w / 8 ≤ 512 := by simp only [vOff]; omega_using [tc.2, hw8]
  refine WP.mono (halfOk hw r1 r2 rab rad rbd (wreg_ne a).1 (wreg_ne b).1 (wreg_ne d).1
    (wreg_ne a).2.2.2 (wreg_ne b).2.2.2 (wreg_ne d).2.2.2 hR.r9
    (by rw [hR.rd, hR.wr]; exact he.msg j) (in_sc hsc hsl) (out_sc hsc hsl) _ _ _ _ _ ga gb gd gc
    (hR.msg j)) fun s' ⟨ha, hb, hd, hm, hr, hrd, hwr⟩ => ?_
  have keep : ∀ q : Reg, q = .r9 ∨ q = .rdi ∨ q = .rsp → s'.gpr q = s.gpr q := by
    intro q hq
    have h : ∀ k, wreg k ≠ q := fun k => by
      rcases hq with rfl | rfl | rfl
      exacts [(wreg_ne k).1, (wreg_ne k).2.1, (wreg_ne k).2.2.1]
    exact hr q (h a).symm (h b).symm (h d).symm (by rcases hq with rfl | rfl | rfl <;> decide)
  refine ⟨fun k hk => ?_, ?_, fun q => ?_, hrd.trans hR.rd, hwr.trans hR.wr,
    (keep _ (.inl rfl)).trans hR.r9, (keep _ (.inr (.inl rfl))).trans hR.rdi,
    (keep _ (.inr (.inr rfl))).trans hR.rsp⟩
  · rw [halfG_getP _ _ v nab nac nad nbc nbd ncd _ k hk]
    by_cases eb : b.1 = k
    · subst eb; rw [ite_eq_left rfl, ite_eq_right tb]; exact hb
    rw [ite_eq_right eb]
    by_cases ec : c.1 = k
    · subst ec; rw [ite_eq_left rfl, ite_eq_left tc, hm, readW_writeW_self' hw]
    rw [ite_eq_right ec]
    by_cases ed : d.1 = k
    · subst ed; rw [ite_eq_left rfl, ite_eq_right td]; exact hd
    rw [ite_eq_right ed]
    by_cases ea : a.1 = k
    · subst ea; rw [ite_eq_left rfl, ite_eq_right ta]; exact ha
    rw [ite_eq_right ea]
    have hk' := hR.holds k hk
    by_cases tk : third k
    · rw [ite_eq_left tk] at hk' ⊢
      rw [hm, readW_writeW_off _ _ _ (by simp only [vOff]; omega_using [tk.2, hw8])
        (by simp only [vOff]; omega_using [tc.2, hw8]) (by simp only [vOff]; omega_using [ec, hw8]) hw8]
      exact hk'
    · rw [ite_eq_right tk] at hk' ⊢
      rw [hr _ (fun e => ea (wreg_inj16 a a.2 k hk ta tk e.symm))
        (fun e => eb (wreg_inj16 b b.2 k hk tb tk e.symm))
        (fun e => ed (wreg_inj16 d d.2 k hk td tk e.symm)) (wreg_ne k).2.2.2]
      exact hk'
  · rw [hm]
    exact hR.frame.writeW (List.mem_singleton_self _) _ (by
      simp only [slotsR, slot, off_eq]
      exact Offset.contains _ (by simp only [vOff]; omega_using []) (by simp only [vOff]; omega_using [tc.2, hw8])
        (by omega_using []))
  · rw [hm, Mem.readW_writeW_sep (he.sep q c tc) (by omega_using [hw8])]
    exact hR.msg q

theorem half_stepR {P : Params w} (hP : Ok P) {a b c d : Fin 16} (hq : HSide a b c d)
    (second : Bool) (r i : Nat) {scr : Addr} {m : Block w} {v : Work w} {s₀ s : State}
    (he : Env w scr s₀) (hR : RI scr m v s₀ s) :
    WP isa (halfAt P r i a b c d second) s
      (RI scr m (halfG (if second then P.R3 else P.R1) (if second then P.R4 else P.R2) v a b c d
        (m (Spec.Blake2.sigmaAt r (2 * i + if second then 1 else 0)))) s₀) := by
  cases second
  · exact half_stepR' hP.hw hP.r1 hP.r2 hq _ he hR
  · exact half_stepR' hP.hw hP.r3 hP.r4 hq _ he hR

/-! ## Rounds -/

theorem cols_ok {P : Params w} (hP : Ok P) {scr : Addr} {m : Block w} {v : Work w}
    {s₀ s : State} (he : Env w scr s₀) (hR : RI scr m v s₀ s) (r : Nat) :
    WP isa (quad P r 0 cols) s (RI scr m (quadH P colsF (fun k => m (Spec.Blake2.sigmaAt r (2 * k)))
      (fun k => m (Spec.Blake2.sigmaAt r (2 * k + 1))) v) s₀) := by
  unfold quad
  refine WP.seq (WP.mono (half_stepR hP (a := 0) (b := 4) (c := 8) (d := 12) (by decide) false r 0 he hR) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 1) (b := 5) (c := 9) (d := 13) (by decide) false r 1 he h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 2) (b := 6) (c := 10) (d := 14) (by decide) false r 2 he h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 3) (b := 7) (c := 11) (d := 15) (by decide) false r 3 he h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 0) (b := 4) (c := 8) (d := 12) (by decide) true r 0 he h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 1) (b := 5) (c := 9) (d := 13) (by decide) true r 1 he h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 2) (b := 6) (c := 10) (d := 14) (by decide) true r 2 he h₆) fun s₇ h₇ => ?_)
  exact WP.mono (half_stepR hP (a := 3) (b := 7) (c := 11) (d := 15) (by decide) true r 3 he h₇) fun _ h => h

theorem diags_ok {P : Params w} (hP : Ok P) {scr : Addr} {m : Block w} {v : Work w}
    {s₀ s : State} (he : Env w scr s₀) (hR : RI scr m v s₀ s) (r : Nat) :
    WP isa (quad P r 4 diags) s (RI scr m (quadH P diagsF (fun k => m (Spec.Blake2.sigmaAt r (2 * (4 + k))))
      (fun k => m (Spec.Blake2.sigmaAt r (2 * (4 + k) + 1))) v) s₀) := by
  unfold quad
  refine WP.seq (WP.mono (half_stepR hP (a := 0) (b := 5) (c := 10) (d := 15) (by decide) false r 4 he hR) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 1) (b := 6) (c := 11) (d := 12) (by decide) false r 5 he h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 2) (b := 7) (c := 8) (d := 13) (by decide) false r 6 he h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 3) (b := 4) (c := 9) (d := 14) (by decide) false r 7 he h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 0) (b := 5) (c := 10) (d := 15) (by decide) true r 4 he h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 1) (b := 6) (c := 11) (d := 12) (by decide) true r 5 he h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (half_stepR hP (a := 2) (b := 7) (c := 8) (d := 13) (by decide) true r 6 he h₆) fun s₇ h₇ => ?_)
  exact WP.mono (half_stepR hP (a := 3) (b := 4) (c := 9) (d := 14) (by decide) true r 7 he h₇) fun _ h => h

theorem round_ok {P : Params w} (hP : Ok P) {scr : Addr} {m : Block w} {v : Work w}
    {s₀ s : State} (he : Env w scr s₀) (hR : RI scr m v s₀ s) (r : Nat) :
    WP isa (Impl.Blake2.X86_64.round P r) s (RI scr m (Spec.Blake2.round P m v r) s₀) := by
  rw [round_halves]
  exact WP.seq (WP.mono (cols_ok hP he hR r) fun _ h => diags_ok hP he h r)

theorem rounds_ok {P : Params w} (hP : Ok P) {scr : Addr} {m : Block w} {v : Work w}
    {s₀ : State} (he : Env w scr s₀) (h₀ : RI scr m v s₀ s₀) :
    ∀ n, WP isa (rounds P n) s₀ (RI scr m ((List.range n).foldl (Spec.Blake2.round P m) v) s₀)
  | 0 => WP.block_nil h₀
  | n + 1 => by
    refine WP.seq (WP.mono (rounds_ok hP he h₀ n) fun s h => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok hP he h n

/-! ## Words in memory -/

theorem readW32_of_bytes {m : Mem} {a : Addr} {V : BitVec 32}
    (h : ∀ i < 4, m (a + BitVec.ofNat 64 i) = V.extractLsb' (8 * i) 8) : m.readW a 32 = V := by
  have e := Mem.read_eq_of_bytes (n := 4) (v := V) h
  show (m.read a 4).setWidth 32 = V
  rw [e]; exact BitVec.setWidth_eq V

/-- The low half of a 64-bit word. -/
theorem readW_lo32 (m : Mem) (a : Addr) : m.readW a 32 = (m.readW a 64).setWidth 32 := by
  apply readW32_of_bytes; intro i hi
  rw [BitVec.extractLsb'_setWidth_of_le (by omega_using [hi])]
  show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * i) 8
  rw [BitVec.extractLsb'_setWidth_of_le (by omega_using [hi]), Mem.extractLsb'_read m a (by omega_using [hi] : i < 8)]

/-- The high half of a 64-bit word. -/
theorem readW_hi32 (m : Mem) (a : Addr) :
    m.readW (a + 4) 32 = (m.readW a 64).extractLsb' 32 32 := by
  apply readW32_of_bytes; intro i hi
  have e : ((m.readW a 64).extractLsb' 32 32).extractLsb' (8 * i) 8 =
      (m.readW a 64).extractLsb' (8 * (4 + i)) 8 := by
    ext k hk; simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
    simp only [show 8 * i + k < 32 by omega_using [hi, hk], decide_true, Bool.true_and]; congr 1; omega_using []
  rw [e]
  show _ = ((m.read a 8).setWidth 64).extractLsb' (8 * (4 + i)) 8
  rw [BitVec.extractLsb'_setWidth_of_le (by omega_using [hi]), Mem.extractLsb'_read m a (by omega_using [hi] : 4 + i < 8),
    show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]

theorem read_leBytes (m : Mem) : ∀ (n : Nat) (a : Addr),
    m.read a n = Spec.Blake2.leBytes n (fun i => m (a + BitVec.ofNat 64 i))
  | 0, _ => rfl
  | n + 1, a => by
    rw [Mem.read, Spec.Blake2.leBytes, read_leBytes m n (a + 1)]
    have e : (fun i => m (a + 1 + BitVec.ofNat 64 i)) = fun i => m (a + BitVec.ofNat 64 (i + 1)) :=
      funext fun i => by rw [Offset.add_ofNat_succ]
    rw [e, show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a]

/-- Word `j` of the block at `p`, as the code reads it. -/
theorem blockAt_get (m : Mem) (p : Addr) (j : Fin 16) :
    Spec.Blake2.blockAt w m p j = m.readW (off p (ws w * j)) w := by
  simp only [Spec.Blake2.blockAt, Spec.Blake2.parseBlock, Spec.Blake2.leWord, Mem.readW, off_eq,
    read_leBytes, ws, Offset.add_ofNat_add_ofNat]

/-- Word `j` of the state at `p`, as the code reads it. -/
theorem stateAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < 8) :
    (Spec.Blake2.stateAt w m p)[j] = m.readW (off p (ws w * j)) w := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, off_eq, ws]

/-! ## The compression function, in the order of the code -/

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (P : Params w) (h : Spec.Blake2.HashValue w) (t : Nat) (f : Bool) : Work w :=
  let v : Work w := h ++ P.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v

theorem F_eq (P : Params w) (h : Spec.Blake2.HashValue w) (m : Block w) (t : Nat) (f : Bool) :
    Spec.Blake2.F P h m t f = Vector.ofFn fun i : Fin 8 =>
      (h[i]'(by omega_using [])) ^^^ ((List.range P.r).foldl (Spec.Blake2.round P m) (V0 P h t f))[i] ^^^
        ((List.range P.r).foldl (Spec.Blake2.round P m) (V0 P h t f))[i.val + 8] := rfl

/-- The final block flag as a word. -/
def flagW (w : Nat) (f : Bool) : BitVec w := if f then BitVec.allOnes w else 0

theorem V0_get (P : Params w) (h : Spec.Blake2.HashValue w) (t : Nat) (f : Bool) (k : Nat)
    (hk : k < 16) : (V0 P h t f)[k] =
      if hk8 : k < 8 then (h[k]'(by omega_using [hk8])) else if k = 12 then P.IV[4] ^^^ BitVec.ofNat w t
      else if k = 13 then P.IV[5] ^^^ BitVec.ofNat w (t / 2 ^ w)
      else if k = 14 then P.IV[6] ^^^ flagW w f else P.IV[k - 8]'(by omega_using [hk]) := by
  have base : ((h ++ P.IV : Work w))[k] = if hk8 : k < 8 then (h[k]'(by omega_using [hk8])) else P.IV[k - 8]'(by omega_using [hk]) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ P.IV : Work w)[12] = P.IV[4] := by simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ P.IV : Work w)[13] = P.IV[5] := by simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ P.IV : Work w)[14] = P.IV[6] := by simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [V0, flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev stA : Addr := s₀.gpr .rdi
abbrev bpA : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev t₀ : Nat := (s₀.gpr .rcx).toNat
abbrev fl : Bool := (s₀.gpr .r8).setWidth 32 != 0
abbrev scA : Addr := s₀.gpr .r9
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

abbrev stR (w : Nat) (s₀ : State) : Region := ⟨stA s₀, 8 * (w / 8)⟩
abbrev blR (w : Nat) (s₀ : State) : Region := ⟨bpA s₀, Spec.Blake2.blockBytes w * nb s₀⟩
abbrev H₀ (w : Nat) (s₀ : State) : Spec.Blake2.HashValue w := Spec.Blake2.stateAt w s₀.mem (stA s₀)
abbrev blkAddr (w : Nat) (s₀ : State) (i : Nat) : Addr := bpA s₀ + BitVec.ofNat 64 (Spec.Blake2.blockBytes w * i)
abbrev blk (w : Nat) (s₀ : State) (i : Nat) : Block w := Spec.Blake2.blockAt w s₀.mem (blkAddr w s₀ i)

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [blR w s₀]
  wr : s₀.wr = [stR w s₀, scR (scA s₀)]
  st_sc : (stR w s₀).Disjoint (scR (scA s₀))
  bl_st : (blR w s₀).Disjoint (stR w s₀)
  bl_sc : (blR w s₀).Disjoint (scR (scA s₀))
  ret_st : (retR s₀).Disjoint (stR w s₀)
  ret_sc : (retR s₀).Disjoint (scR (scA s₀))

theorem pre_of {P : Params w} {s₀ : State} (h : (compressX86_64 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem hsc : scR (scA s₀) ∈ s₀.wr := by simp [hp.wr]

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt (hw : w = 64 ∨ w = 32) : Spec.Blake2.blockBytes w * nb s₀ < 2 ^ 64 := by
  apply Classical.byContradiction; intro hn
  refine hp.bl_st (stA s₀) ?_ (by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
    rcases hw with rfl | rfl <;> decide)
  simp only [Region.Contains]
  have := (stA s₀ - bpA s₀).isLt
  omega_using [hn]

theorem st_contains (hw : w = 64 ∨ w = 32) {k : Nat} (hk : k < 8) :
    (stR w s₀).Contains (off (stA s₀) (ws w * k)) (w / 8) :=
  contains_off (by simp only [ws]; rcases hw with rfl | rfl <;> omega_using [hk])
    (by simp only [ws]; rcases hw with rfl | rfl <;> omega_using [hk])

theorem in_st (hw : w = 64 ∨ w = 32) {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (off (stA s₀) (ws w * k)) (w / 8) :=
  ⟨stR w s₀, by simp [hp.wr], hp.st_contains hw hk⟩

theorem out_st (hw : w = 64 ∨ w = 32) {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (off (stA s₀) (ws w * k)) (w / 8) :=
  ⟨stR w s₀, by simp [hp.wr], hp.st_contains hw hk⟩

theorem blk_contains (hw : w = 64 ∨ w = 32) {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    (blR w s₀).Contains (off (blkAddr w s₀ i) (ws w * j)) (w / 8) := by
  have := hp.nb_lt hw
  rw [off_eq, Offset.add_ofNat_add_ofNat]
  refine Offset.contains_base _ ?_ ?_ <;>
  simp only [Spec.Blake2.blockBytes, ws] at this ⊢ <;> rcases hw with rfl | rfl <;>
  simp only [Nat.reduceDiv, Nat.reduceMul] at this ⊢ <;> omega_using [hi, hj, this]

theorem in_blk (hw : w = 64 ∨ w = 32) {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    InRegions (s₀.rd ++ s₀.wr) (off (blkAddr w s₀ i) (ws w * j)) (w / 8) :=
  ⟨blR w s₀, by simp [hp.rd], hp.blk_contains hw hi hj⟩

end Pre

theorem msg_lt (hw : w = 64 ∨ w = 32) (j : Fin 16) : msgOff w j + w / 8 ≤ 128 := by
  have := j.2; simp only [msgOff, ws]; rcases hw with rfl | rfl <;> omega_using []

/-! ## Copying the block -/

theorem copyWord_ok (hw : w = 64 ∨ w = 32) {j : Nat} {s : State} {p scr : Addr}
    (hsi : s.gpr .rsi = p) (h9 : s.gpr .r9 = scr)
    (hin : InRegions (s.rd ++ s.wr) (off p (ws w * j)) (w / 8))
    (hout : InRegions s.wr (off scr (msgOff w j)) (w / 8)) :
    WP isa (.block [ld w .rax (at_ .rsi (ws w * j)), st w (at_ .r9 (msgOff w j)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off scr (msgOff w j)) (s.mem.readW (off p (ws w * j)) w) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] at hin hout
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, and_self, st, ld, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, State.load64, State.store64, ea_at, isa,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      hsi, h9, hin, hout, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial⟩
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, and_self, st, ld, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc32, State.load32, State.store32, ea_at, isa,
      State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      hsi, h9, hin, hout, RegUpd.setWidth_setWidth_32, Option.map_some, Option.some.injEq,
      exists_eq_left']
    exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial⟩

/-- The copy of the block. -/
abbrev msgR (scr : Addr) : Region := ⟨scr, 128⟩

/-- The copy invariant after `n` words, relative to the state `s₁` after
loading the block's address. -/
structure CI (w : Nat) (s₀ : State) (i : Nat) (s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [msgR (scA s₀)] s₁.mem s.mem
  msg : ∀ j (hj : j < 16), j < n → s.mem.readW (off (scA s₀) (msgOff w j)) w = blk w s₀ i ⟨j, hj⟩

theorem msg_sep (hw : w = 64 ∨ w = 32) {j k : Nat} (h : j ≠ k) :
    msgOff w j + w / 8 ≤ msgOff w k ∨ msgOff w k + w / 8 ≤ msgOff w j := by
  simp only [msgOff, ws]; rcases hw with rfl | rfl <;> omega_using [h]

theorem copy_step (hw : w = 64 ∨ w = 32) {s₀ s₁ : State} (hp : Pre w s₀) {i : Nat}
    (hi : i < nb s₀) (hsi : s₁.gpr .rsi = blkAddr w s₀ i) (h9 : s₁.gpr .r9 = scA s₀)
    (hf : Frame [stR w s₀, scR (scA s₀)] s₀.mem s₁.mem) {n : Nat} (hn : n < 16) {s : State}
    (hc : CI w s₀ i s₁ n s) :
    WP isa (.block [ld w .rax (at_ .rsi (ws w * n)), st w (at_ .r9 (msgOff w n)) .rax]) s
      (CI w s₀ i s₁ (n + 1)) := by
  have hw8 : w / 8 ≤ 8 := by rcases hw with rfl | rfl <;> decide
  have hml : msgOff w n + w / 8 ≤ 128 := msg_lt hw ⟨n, hn⟩
  have hsc : scR (scA s₀) ∈ s.wr := hc.wr ▸ hp.hsc
  refine WP.mono (copyWord_ok hw (hc.gpr .rsi (by decide) ▸ hsi) (hc.gpr .r9 (by decide) ▸ h9)
    (by rw [hc.rd, hc.wr]; exact hp.in_blk hw hi hn) (out_sc hsc (by omega_using [hml])))
    fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  -- The word read is the block's.
  have hx : s.mem.readW (off (blkAddr w s₀ i) (ws w * n)) w = blk w s₀ i ⟨n, hn⟩ := by
    have hd : ∀ r ∈ [msgR (scA s₀)], (blR w s₀).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hp.bl_sc.sub_right (Region.sub_prefix (by omega_using []))
    rw [hc.frame.readW (hp.blk_contains hw hi hn) hd (by omega_using [hw8]),
      hf.readW (hp.blk_contains hw hi hn) (by simpa using ⟨hp.bl_st, hp.bl_sc⟩) (by omega_using [hw8])]
    exact (blockAt_get _ _ ⟨n, hn⟩).symm
  refine ⟨fun r hr => (hg r hr).trans (hc.gpr r hr), hrd.trans hc.rd, hwr.trans hc.wr, ?_,
    fun j hj hjn => ?_⟩
  · rw [hm]
    exact hc.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_using [hml]) (by omega_using [hml]))
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have : msgOff w j + w / 8 ≤ 128 := msg_lt hw ⟨j, hj⟩
      rw [readW_writeW_off _ _ _ (by omega_using [this]) (by omega_using [hml])
        (msg_sep hw (Nat.ne_of_lt hjn)) hw8]
      exact hc.msg j hj hjn
    · rw [readW_writeW_self' hw, hx]

theorem copy_eq : copy (w := w) = ld 64 .rsi (at_ .r9 blOff) :: (List.range 16).flatMap fun j =>
    [ld w .rax (at_ .rsi (ws w * j)), st w (at_ .r9 (msgOff w j)) .rax] := rfl

theorem copy_ok (hw : w = 64 ∨ w = 32) {s₀ : State} (hp : Pre w s₀) {i : Nat} (hi : i < nb s₀)
    {s : State} (h9 : s.gpr .r9 = scA s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [stR w s₀, scR (scA s₀)] s₀.mem s.mem)
    (hbl : s.mem.readW (off (scA s₀) blOff) 64 = blkAddr w s₀ i) :
    WP isa (.block (copy (w := w))) s fun s' =>
      (∀ r, r ≠ .rax → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [msgR (scA s₀)] s.mem s'.mem ∧
      ∀ j : Fin 16, s'.mem.readW (off (scA s₀) (msgOff w j)) w = blk w s₀ i j := by
  rw [copy_eq, show ∀ (a : Instr) l, a :: l = [a] ++ l from fun _ _ => rfl, WP.block_append_iff]
  have hin : InRegions (s.rd ++ s.wr) (off (scA s₀) blOff) 8 :=
    in_sc (hwr ▸ hp.hsc) (by decide)
  refine WP.mono (Q := fun s₁ : State => s₁.gpr .rsi = blkAddr w s₀ i ∧ (∀ r, r ≠ .rsi → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) ?_ fun s₁ ⟨hsi, hg, hm, hrd₁, hwr₁⟩ => ?_
  · apply WP.of_runBlock
    simp only [↓reduceIte, and_self, ld, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, State.load64, ea_at, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, h9, hin, hbl, Option.map_some, Option.some.injEq,
      exists_eq_left']
    exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial⟩
  have hc₀ : CI w s₀ i s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁.trans hrd, hwr₁.trans hwr, Frame.refl _ _,
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.mono (wp_range_flatMap (CI w s₀ i s₁) (fun k s hk hc => copy_step hw hp hi hsi
    ((hg .r9 (by decide)).trans h9) (hm ▸ hf) hk hc) 16 (Nat.le_refl _) s₁ hc₀) fun s' hc => ?_
  refine ⟨fun r h1 h2 => (hc.gpr r h1).trans (hg r h2), hc.rd, hc.wr, hm ▸ hc.frame,
    fun j => hc.msg j j.2 j.2⟩

/-! ## Initializing the work vector -/

/-- Where the code reads the high word of the offset counter. -/
def hiOff (w : Nat) : Nat := if w = 64 then thiOff else tloOff + 4

theorem init_eq (P : Params w) : init P = [imm w .rax P.IV[0], st w (at_ .r9 (vOff 8)) .rax,
    imm w .rax P.IV[1], st w (at_ .r9 (vOff 9)) .rax, imm w .rax P.IV[2], st w (at_ .r9 (vOff 10)) .rax, imm w .rax P.IV[3],
    st w (at_ .r9 (vOff 11)) .rax,
    ld w .rax (at_ .rdi (ws w * 0)), ld w .rbx (at_ .rdi (ws w * 1)),
    ld w .rcx (at_ .rdi (ws w * 2)), ld w .rdx (at_ .rdi (ws w * 3)),
    ld w .r14 (at_ .rdi (ws w * 4)), ld w .r15 (at_ .rdi (ws w * 5)),
    ld w .rbp (at_ .rdi (ws w * 6)), ld w .r8 (at_ .rdi (ws w * 7)),
    imm w .r10 P.IV[4], Impl.Blake2.X86_64.xor w .r10 (.mem (at_ .r9 tloOff)),
    imm w .r11 P.IV[5], Impl.Blake2.X86_64.xor w .r11 (.mem (at_ .r9 (hiOff w))),
    imm w .r12 P.IV[6], Impl.Blake2.X86_64.xor w .r12 (.mem (at_ .r9 fOff)),
    imm w .r13 P.IV[7]] := rfl

/-- A statement about the indices below 8, unrolled. -/
theorem forall_lt_eight' {p : (k : Nat) → k < 8 → Prop} :
    (∀ k (hk : k < 8), p k hk) ↔ p 0 (by decide) ∧ p 1 (by decide) ∧ p 2 (by decide) ∧
      p 3 (by decide) ∧ p 4 (by decide) ∧ p 5 (by decide) ∧ p 6 (by decide) ∧ p 7 (by decide) :=
  ⟨fun h => ⟨h 0 _, h 1 _, h 2 _, h 3 _, h 4 _, h 5 _, h 6 _, h 7 _⟩,
    fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ k hk => by
      match k, hk with
      | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
      | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7⟩

theorem forall_lt_eight {p : Nat → Prop} :
    (∀ k, k < 8 → p k) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4 ∧ p 5 ∧ p 6 ∧ p 7 :=
  forall_lt_eight' (p := fun k _ => p k)

theorem init_ok {P : Params w} (hw : w = 64 ∨ w = 32) {s : State} {scr stp : Addr}
    (h9 : s.gpr .r9 = scr) (hdi : s.gpr .rdi = stp)
    (o8 : InRegions s.wr (slot scr 8) (w / 8)) (o9 : InRegions s.wr (slot scr 9) (w / 8))
    (o10 : InRegions s.wr (slot scr 10) (w / 8))
    (o11 : InRegions s.wr (slot scr 11) (w / 8))
    (hst : ∀ k < 8, InRegions (s.rd ++ s.wr) (off stp (ws w * k)) (w / 8))
    (itl : InRegions (s.rd ++ s.wr) (off scr tloOff) (w / 8))
    (ihi : InRegions (s.rd ++ s.wr) (off scr (hiOff w)) (w / 8))
    (ifl : InRegions (s.rd ++ s.wr) (off scr fOff) (w / 8)) :
    WP isa (.block (init P)) s fun s' =>
      s'.mem = (((s.mem.writeW (slot scr 8) P.IV[0]).writeW (slot scr 9) P.IV[1]).writeW
        (slot scr 10) P.IV[2]).writeW (slot scr 11) P.IV[3] ∧
      (∀ k < 8, s'.gpr (wreg k) = (s'.mem.readW (off stp (ws w * k)) w).setWidth 64) ∧
      s'.gpr .r10 = (P.IV[4] ^^^ s'.mem.readW (off scr tloOff) w).setWidth 64 ∧
      s'.gpr .r11 = (P.IV[5] ^^^ s'.mem.readW (off scr (hiOff w)) w).setWidth 64 ∧
      s'.gpr .r12 = (P.IV[6] ^^^ s'.mem.readW (off scr fOff) w).setWidth 64 ∧
      s'.gpr .r13 = P.IV[7].setWidth 64 ∧
      s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := hst 0 (by decide); have h1 := hst 1 (by decide); have h2 := hst 2 (by decide)
  have h3 := hst 3 (by decide); have h4 := hst 4 (by decide); have h5 := hst 5 (by decide)
  have h6 := hst 6 (by decide); have h7 := hst 7 (by decide)
  rw [init_eq]
  rcases hw with rfl | rfl <;>
    simp only [↓reduceIte, Nat.reduceEqDiff, Nat.reduceDiv, hiOff] at o8 o9 o10 o11 h0 h1 h2 h3 h4 h5 h6 h7 itl ihi ifl
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, and_self, st, ld, imm, Impl.Blake2.X86_64.xor, hiOff,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64,
      State.store64, ea_at, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, h9, hdi, o8, o9, o10, o11, h0, h1, h2, h3, h4, h5, h6, h7, itl, ihi, ifl,
      BitVec.setWidth_eq, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left', forall_lt_eight, wreg, off]
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, and_self, st, ld, imm, Impl.Blake2.X86_64.xor, hiOff,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
      State.load32, State.store32, ea_at, isa, State.setReg32, RegUpd.gpr_setReg,
      RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, h9, hdi, o8, o9, o10, o11, h0, h1,
      h2, h3, h4, h5, h6, h7, itl, ihi, ifl, RegUpd.setWidth_setWidth_32, BitVec.setWidth_eq, Option.bind_some,
      Option.map_some, Option.some.injEq, exists_eq_left', forall_lt_eight, wreg, off]

/-! ## After the rounds -/

theorem spill_eq : spill (w := w) = [st w (at_ .r9 (vOff 12)) .r10,
    st w (at_ .r9 (vOff 13)) .r11, st w (at_ .r9 (vOff 14)) .r12,
    st w (at_ .r9 (vOff 15)) .r13] := rfl

theorem spill_ok (hw : w = 64 ∨ w = 32) {s : State} {scr : Addr} (h9 : s.gpr .r9 = scr)
    (o12 : InRegions s.wr (slot scr 12) (w / 8))
    (o13 : InRegions s.wr (slot scr 13) (w / 8)) (o14 : InRegions s.wr (slot scr 14) (w / 8))
    (o15 : InRegions s.wr (slot scr 15) (w / 8)) :
    WP isa (.block (spill (w := w))) s fun s' =>
      s'.mem = (((s.mem.writeW (slot scr 12)
        ((s.gpr .r10).setWidth w)).writeW (slot scr 13) ((s.gpr .r11).setWidth w)).writeW
        (slot scr 14) ((s.gpr .r12).setWidth w)).writeW (slot scr 15) ((s.gpr .r13).setWidth w) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [spill_eq]
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] at o12 o13 o14 o15
  · apply WP.of_runBlock
    simp only [↓reduceIte, and_self, st, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.store64, ea_at, isa, h9, o12, o13, o14, o15,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  · apply WP.of_runBlock
    simp only [↓reduceIte, Nat.reduceEqDiff, and_self, st, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.store32, ea_at, isa, h9, o12, o13, o14, o15,
      Option.some.injEq, exists_eq_left']

theorem xorStore_ok (hw : w = 64 ∨ w = 32) {a : Reg} (hadi : a ≠ .rdi) {d e : Nat}
    {s : State} {scr stp : Addr} (h9 : s.gpr .r9 = scr) (hdi : s.gpr .rdi = stp)
    (hi1 : InRegions (s.rd ++ s.wr) (off scr d) (w / 8))
    (hi2 : InRegions (s.rd ++ s.wr) (off stp e) (w / 8)) (ho : InRegions s.wr (off stp e) (w / 8)) :
    WP isa (.block [Impl.Blake2.X86_64.xor w a (.mem (at_ .r9 d)),
      Impl.Blake2.X86_64.xor w a (.mem (at_ .rdi e)), st w (at_ .rdi e) a]) s fun s' =>
      s'.mem = s.mem.writeW (off stp e) ((s.gpr a).setWidth w ^^^ s.mem.readW (off scr d) w ^^^
        s.mem.readW (off stp e) w) ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases hw with rfl | rfl <;> simp only [Nat.reduceDiv] at hi1 hi2 ho
  · apply WP.of_runBlock
    simp only [↓reduceIte, and_self, st, Impl.Blake2.X86_64.xor, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.store64, ea_at, isa,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      h9, hdi, hi1, hi2, ho, hadi.symm, BitVec.setWidth_eq, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial⟩
  · apply WP.of_runBlock
    simp only [↓reduceIte, Nat.reduceEqDiff, and_self, st, Impl.Blake2.X86_64.xor,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.load32,
      State.store32, ea_at, isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, h9, hdi, hi1, hi2, ho, hadi.symm,
      RegUpd.setWidth_setWidth_32, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r h => by simp only [h, ite_false], trivial⟩

/-- A block's size, as the code adds it. -/
def bbv (w : Nat) : BitVec 64 := BitVec.ofNat 64 (16 * ws w)

/-- The parameter slots after `advance`. -/
def advMem (w : Nat) (scr : Addr) (m : Mem) : Mem :=
  let T := m.readW (off scr tloOff) 64
  let m₁ := (m.writeW (off scr blOff) (m.readW (off scr blOff) 64 + bbv w)).writeW
    (off scr tloOff) (T + bbv w)
  let m₂ := if w = 64 then m₁.writeW (off scr thiOff) (m.readW (off scr thiOff) 64 +
    (BitVec.ofBool (decide (2 ^ 64 ≤ T.toNat + (bbv w).toNat))).setWidth 64) else m₁
  m₂.writeW (off scr nOff) (m.readW (off scr nOff) 64 - 1)

theorem sx_bbv (hw : w = 64 ∨ w = 32) :
    (BitVec.ofNat 32 (16 * ws w)).signExtend 64 = bbv w := by
  rcases hw with rfl | rfl <;> decide

theorem advance_ok (hw : w = 64 ∨ w = 32) {s : State} {scr : Addr} (h9 : s.gpr .r9 = scr)
    (hsc : scR scr ∈ s.wr) :
    WP isa (.block (advance (w := w))) s fun s' =>
      s'.mem = advMem w scr s.mem ∧ s'.zf = some (s.mem.readW (off scr nOff) 64 - 1 == 0) ∧
      s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ib : InRegions (s.rd ++ s.wr) (off scr blOff) 8 := in_sc hsc (by decide)
  have it : InRegions (s.rd ++ s.wr) (off scr tloOff) 8 := in_sc hsc (by decide)
  have ih : InRegions (s.rd ++ s.wr) (off scr thiOff) 8 := in_sc hsc (by decide)
  have i_n : InRegions (s.rd ++ s.wr) (off scr nOff) 8 := in_sc hsc (by decide)
  have ob : InRegions s.wr (off scr blOff) 8 := out_sc hsc (by decide)
  have ot : InRegions s.wr (off scr tloOff) 8 := out_sc hsc (by decide)
  have oh : InRegions s.wr (off scr thiOff) 8 := out_sc hsc (by decide)
  have o_n : InRegions s.wr (off scr nOff) 8 := out_sc hsc (by decide)
  have r1 : ∀ (m : Mem) {d e : Nat} (v : BitVec 64), d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 < 2 ^ 32 →
      e + 8 < 2 ^ 32 → (m.writeW (off scr e) v).readW (off scr d) 64 = m.readW (off scr d) 64 :=
    fun m _ _ v h hd he => readW_writeW_off (w := 64) m scr v hd he h (by decide)
  have rT : ∀ x : BitVec 64, (s.mem.writeW (off scr blOff) x).readW (off scr tloOff) 64 =
      s.mem.readW (off scr tloOff) 64 := fun x => r1 _ x (by decide) (by decide) (by decide)
  have rH : ∀ x y : BitVec 64, ((s.mem.writeW (off scr blOff) x).writeW (off scr tloOff) y).readW
      (off scr thiOff) 64 = s.mem.readW (off scr thiOff) 64 := fun x y => by
    rw [r1 _ y (by decide) (by decide) (by decide), r1 _ x (by decide) (by decide) (by decide)]
  have rN : ∀ x y : BitVec 64, ((s.mem.writeW (off scr blOff) x).writeW (off scr tloOff) y).readW
      (off scr nOff) 64 = s.mem.readW (off scr nOff) 64 := fun x y => by
    rw [r1 _ y (by decide) (by decide) (by decide), r1 _ x (by decide) (by decide) (by decide)]
  have rN' : ∀ x y z : BitVec 64, (((s.mem.writeW (off scr blOff) x).writeW (off scr tloOff) y).writeW
      (off scr thiOff) z).readW (off scr nOff) 64 = s.mem.readW (off scr nOff) 64 := fun x y z => by
    rw [r1 _ z (by decide) (by decide) (by decide), rN]
  have e0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have eb := sx_bbv hw
  rcases hw with rfl | rfl
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, and_self, advance, advMem, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      State.load64, State.store64, ea_at, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      RegUpd.zf_arithFlags, RegUpd.cf_arithFlags, h9, ib, it, ih, i_n, ob, ot, oh, o_n, rT, rH, rN',
      eb, e0, e1, Option.bind_some, Option.map_some, Option.some.injEq,
      exists_eq_left']
    have a0 : ∀ x : BitVec 64, x + (0 : BitVec 64) = x := fun x => BitVec.add_zero x
    exact ⟨by rw [a0], trivial⟩
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, and_self, advance, advMem, List.cons_append,
      List.nil_append, List.append_nil, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.load64, State.store64, ea_at, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, h9,
      ib, it, i_n, ob, ot, o_n, rT, rN, eb, e1, Option.bind_some, Option.map_some,
      Option.some.injEq, exists_eq_left']

/-! ## Frames in `scratch` and the state -/

theorem sub_lo (scr : Addr) {d k n : Nat} (h : d + k ≤ n) :
    Region.Sub ⟨off scr d, k⟩ ⟨scr, n⟩ := by
  rw [off_eq]; exact Offset.sub_base _ h

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem sc_st {d k : Nat} (h : d + k ≤ 512) :
    (⟨off (scA s₀) d, k⟩ : Region).Disjoint (stR w s₀) :=
  (hp.st_sc.sub_right (sub_lo _ h)).symm

theorem st_sc' {n : Nat} (h : n ≤ 512) : (stR w s₀).Disjoint ⟨scA s₀, n⟩ :=
  hp.st_sc.sub_right (Region.sub_prefix h)

/-- A word of `scratch` at `d ≥ n` is kept by writes to the state and `scratch[0, n)`. -/
theorem keep_sc {m m' : Mem} {n : Nat} (hf : Frame [stR w s₀, ⟨scA s₀, n⟩] m m') {d w' : Nat}
    (hd : n ≤ d) (hd' : d + w' / 8 ≤ 512) :
    m'.readW (off (scA s₀) d) w' = m.readW (off (scA s₀) d) w' := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by omega_using [hd'])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sc_st hd'
  · rw [off_eq]; exact Offset.disjoint_base _ hd (by omega_using [hd'])

/-- A word of the state is kept by writes to `scratch[0, n)`. -/
theorem keep_st {m m' : Mem} {n : Nat} (hf : Frame [⟨scA s₀, n⟩] m m') (hn : n ≤ 512)
    (hw : w = 64 ∨ w = 32) {k : Nat} (hk : k < 8) :
    m'.readW (off (stA s₀) (ws w * k)) w = m.readW (off (stA s₀) (ws w * k)) w :=
  hf.readW (hp.st_contains hw hk) (by simpa using hp.st_sc' hn)
    (by rcases hw with rfl | rfl <;> decide)

end Pre

/-! ## Finishing: `(h[i]'(by omega)) ^= (v[i]'(by omega)) ^ (v[i + 8]'(by omega))` -/

theorem finish_eq : finish (w := w) = (List.range 8).flatMap fun i =>
    [Impl.Blake2.X86_64.xor w (wreg i) (.mem (at_ .r9 (vOff (i + 8)))),
      Impl.Blake2.X86_64.xor w (wreg i) (.mem (at_ .rdi (ws w * i))),
      st w (at_ .rdi (ws w * i)) (wreg i)] := rfl

/-- The finishing invariant after `n` words, relative to the state `s₁` before them. -/
structure FI (w : Nat) (s₀ s₁ : State) (vR : Work w) (n : Nat) (s : State) : Prop where
  gpr : ∀ j, n ≤ j → j < 8 → s.gpr (wreg j) = s₁.gpr (wreg j)
  r9 : s.gpr .r9 = s₁.gpr .r9
  rdi : s.gpr .rdi = s₁.gpr .rdi
  rsp : s.gpr .rsp = s₁.gpr .rsp
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [stR w s₀] s₁.mem s.mem
  st : ∀ j (hj : j < 8), s.mem.readW (off (stA s₀) (ws w * j)) w =
    if j < n then (vR[j]'(by omega_using [hj])) ^^^ (vR[j + 8]'(by omega_using [hj])) ^^^ s₁.mem.readW (off (stA s₀) (ws w * j)) w
    else s₁.mem.readW (off (stA s₀) (ws w * j)) w

theorem wreg_inj : ∀ j < 8, ∀ k < 8, wreg j = wreg k → j = k := by decide

theorem setWidth_setWidth' (hw : w = 64 ∨ w = 32) (x : BitVec w) : (x.setWidth 64).setWidth w = x := by
  rcases hw with rfl | rfl
  · simp only [BitVec.setWidth_eq]
  · exact RegUpd.setWidth_setWidth_32 x

theorem finish_step (hw : w = 64 ∨ w = 32) {s₀ : State} (hp : Pre w s₀) {s₁ : State}
    {vR : Work w} (h9 : s₁.gpr .r9 = scA s₀) (hdi : s₁.gpr .rdi = stA s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hv : ∀ j (hj : j < 8), s₁.gpr (wreg j) = (vR[j]'(by omega_using [hj])).setWidth 64)
    (hs : ∀ j (hj : j < 8), s₁.mem.readW (slot (scA s₀) (j + 8)) w = (vR[j + 8]'(by omega_using [hj]))) (n : Nat)
    (hn : n < 8) (s : State) (hf : FI w s₀ s₁ vR n s) :
    WP isa (.block [Impl.Blake2.X86_64.xor w (wreg n) (.mem (at_ .r9 (vOff (n + 8)))),
      Impl.Blake2.X86_64.xor w (wreg n) (.mem (at_ .rdi (ws w * n))),
      st w (at_ .rdi (ws w * n)) (wreg n)]) s (FI w s₀ s₁ vR (n + 1)) := by
  have hw8 : w / 8 ≤ 8 := by rcases hw with rfl | rfl <;> decide
  have hsc : scR (scA s₀) ∈ s.wr := by rw [hf.wr, hwr]; exact hp.hsc
  have hsl : vOff (n + 8) + w / 8 ≤ 512 := by simp only [vOff]; omega_using [hn, hw8]
  refine WP.mono (xorStore_ok hw (wreg_ne n).2.1 (hf.r9.trans h9) (hf.rdi.trans hdi)
    (in_sc hsc hsl) (by rw [hf.rd, hf.wr, hrd, hwr]; exact hp.in_st hw hn)
    (by rw [hf.wr, hwr]; exact hp.out_st hw hn)) fun s' ⟨hm, hg, hrd', hwr'⟩ => ?_
  have ea : (s.gpr (wreg n)).setWidth w = (vR[n]'(by omega_using [hn])) := by
    rw [hf.gpr n (Nat.le_refl _) hn, hv n hn, setWidth_setWidth' hw]
  have eb : s.mem.readW (off (scA s₀) (vOff (n + 8))) w = (vR[n + 8]'(by omega_using [hn])) := by
    rw [hf.frame.readW (Region.contains_self _ _) (by simpa using hp.sc_st hsl) (by omega_using [hw8])]
    exact hs n hn
  have ec := hf.st n hn
  simp only [Nat.lt_irrefl, ite_false] at ec
  rw [ea, eb, ec] at hm
  refine ⟨fun j hj hj8 => ?_, ?_, ?_, ?_, hrd'.trans hf.rd, hwr'.trans hf.wr, ?_, fun j hj => ?_⟩
  · rw [hg _ (fun e => by have := wreg_inj j hj8 n hn e; omega_using [hj, this])]
    exact hf.gpr j (by omega_using [hj]) hj8
  · rw [hg _ (wreg_ne n).1.symm]; exact hf.r9
  · rw [hg _ (wreg_ne n).2.1.symm]; exact hf.rdi
  · rw [hg _ (wreg_ne n).2.2.1.symm]; exact hf.rsp
  · rw [hm]; exact hf.frame.writeW (List.mem_singleton_self _) _ (hp.st_contains hw hn)
  · rw [hm]
    by_cases ejn : j = n
    · subst ejn
      rw [readW_writeW_self' hw]
      simp only [Nat.lt_succ_self, ite_true]
    · have hsep : ws w * j + w / 8 ≤ ws w * n ∨ ws w * n + w / 8 ≤ ws w * j := by
        simp only [ws]; rcases hw with rfl | rfl <;> omega_using [ejn]
      rw [readW_writeW_off _ _ _ (by simp only [ws]; rcases hw with rfl | rfl <;> omega_using [hj])
        (by simp only [ws]; rcases hw with rfl | rfl <;> omega_using [hn]) hsep hw8, hf.st j hj]
      have : (j < n + 1) = (j < n) := propext ⟨fun h => by omega_using [ejn, h], fun h => by omega_using [h]⟩
      simp only [this]

theorem finish_ok (hw : w = 64 ∨ w = 32) {s₀ : State} (hp : Pre w s₀) {s₁ : State}
    {vR : Work w} (h9 : s₁.gpr .r9 = scA s₀) (hdi : s₁.gpr .rdi = stA s₀) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hv : ∀ j (hj : j < 8), s₁.gpr (wreg j) = (vR[j]'(by omega_using [hj])).setWidth 64)
    (hs : ∀ j (hj : j < 8), s₁.mem.readW (slot (scA s₀) (j + 8)) w = (vR[j + 8]'(by omega_using [hj]))) :
    WP isa (.block (finish (w := w))) s₁ (FI w s₀ s₁ vR 8) := by
  rw [finish_eq]
  refine wp_range_flatMap (M := isa) (FI w s₀ s₁ vR) (fun k s hk h => finish_step hw hp h9 hdi hrd hwr hv hs k hk s h)
    8 (Nat.le_refl _) s₁ ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun j _ => ?_⟩
  simp only [Nat.not_lt_zero, ite_false]

/-! ## The counter and the flag, as the code reads them -/

theorem lo32_ofNat (T : Nat) : (BitVec.ofNat 64 T).setWidth 32 = BitVec.ofNat 32 T := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using []

theorem hi32_ofNat (T : Nat) : (BitVec.ofNat 64 T).extractLsb' 32 32 = BitVec.ofNat 32 (T / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega_using []

theorem carry_ofNat (T bb : Nat) (hb : bb < 2 ^ 64) : BitVec.ofNat 64 (T / 2 ^ 64) +
    (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 T).toNat + (BitVec.ofNat 64 bb).toNat))).setWidth 64 =
    BitVec.ofNat 64 ((T + bb) / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  by_cases h : 2 ^ 64 ≤ T % 2 ^ 64 + bb
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_true, Nat.mod_eq_of_lt hb, Bool.toNat_true]
    omega_using [hb, h]
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_false, Nat.mod_eq_of_lt hb, Bool.toNat_false]
    omega_using [h]

theorem readW_lo (hw : w = 64 ∨ w = 32) {m : Mem} {a : Addr} {T : Nat}
    (h : m.readW a 64 = BitVec.ofNat 64 T) : m.readW a w = BitVec.ofNat w T := by
  rcases hw with rfl | rfl
  · exact h
  · rw [readW_lo32, h, lo32_ofNat]

theorem readW_hi (hw : w = 64 ∨ w = 32) {m : Mem} {scr : Addr} {T : Nat}
    (hlo : m.readW (off scr tloOff) 64 = BitVec.ofNat 64 T)
    (hhi : w = 64 → m.readW (off scr thiOff) 64 = BitVec.ofNat 64 (T / 2 ^ 64)) :
    m.readW (off scr (hiOff w)) w = BitVec.ofNat w (T / 2 ^ w) := by
  rcases hw with rfl | rfl
  · exact hhi rfl
  · have e : off scr (hiOff 32) = off scr tloOff + 4 := by
      rw [off_eq, off_eq, BitVec.add_assoc]; rfl
    rw [e, readW_hi32, hlo, hi32_ofNat]

theorem readW_flag (hw : w = 64 ∨ w = 32) {m : Mem} {a : Addr} {f : Bool}
    (h : m.readW a 64 = flagW 64 f) : m.readW a w = flagW w f := by
  rcases hw with rfl | rfl
  · exact h
  · rw [readW_lo32, h]; cases f <;> decide

/-! ## The work vector after `init` -/

theorem holds_init {P : Params w} {s : State} {scr : Addr} {H : Spec.Blake2.HashValue w} {T : Nat}
    {f : Bool} (hst : ∀ k (hk : k < 8), s.gpr (wreg k) = (H[k]'(by omega_using [hk])).setWidth 64)
    (h8 : s.mem.readW (slot scr 8) w = P.IV[0]) (h9 : s.mem.readW (slot scr 9) w = P.IV[1])
    (h10 : s.mem.readW (slot scr 10) w = P.IV[2]) (h11 : s.mem.readW (slot scr 11) w = P.IV[3])
    (h10r : s.gpr .r10 = (P.IV[4] ^^^ BitVec.ofNat w T).setWidth 64)
    (h11r : s.gpr .r11 = (P.IV[5] ^^^ BitVec.ofNat w (T / 2 ^ w)).setWidth 64)
    (h12r : s.gpr .r12 = (P.IV[6] ^^^ flagW w f).setWidth 64)
    (h13r : s.gpr .r13 = P.IV[7].setWidth 64) :
    Holds scr (V0 P H T f) s := by
  intro k hk
  rw [V0_get P H T f k hk]
  by_cases hk8 : k < 8
  · rw [ite_eq_right (show ¬third k by omega_using [hk8])]
    simp only [hk8, dite_true]; exact hst k hk8
  · have : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega_using [hk, hk8]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [third, wreg, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceEqDiff, and_self,
      and_false, ↓reduceIte, ↓reduceDIte, h8, h9, h10, h11, h10r, h11r, h12r, h13r, Nat.reduceSub]

/-! ## The loop invariant -/

/-- The parameter slots before block `i`. -/
structure Slots (w : Nat) (s₀ : State) (i : Nat) (m : Mem) : Prop where
  bl : m.readW (off (scA s₀) blOff) 64 = blkAddr w s₀ i
  n : m.readW (off (scA s₀) nOff) 64 = BitVec.ofNat 64 (nb s₀ - i)
  tlo : m.readW (off (scA s₀) tloOff) 64 = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes w)
  thi : w = 64 → m.readW (off (scA s₀) thiOff) 64 =
    BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes w) / 2 ^ 64)
  f : m.readW (off (scA s₀) fOff) 64 = flagW 64 (fl s₀)

/-- The callee-saved registers are saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (off (scA s₀) p.2) 64 = s₀.gpr p.1

/-- What holds between blocks, after `i` of them. -/
structure Common (P : Params w) (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = stA s₀
  r9 : s.gpr .r9 = scA s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR w s₀, scR (scA s₀)] s₀.mem s.mem
  state : Spec.Blake2.stateAt w s.mem (stA s₀) =
    Spec.Blake2.compressBlocks P (H₀ w s₀) s₀.mem (bpA s₀) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem
  slots : Slots w s₀ i s.mem

/-! ## One block -/

theorem stage1_ok {P : Params w} (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {i : Nat}
    (hi : i < nb s₀) {s : State} (hc : Common P s₀ i s) :
    WP isa (.block (copy (w := w) ++ init P)) s fun s' =>
      RI (scA s₀) (blk w s₀ i) (V0 P (Spec.Blake2.stateAt w s.mem (stA s₀))
        (t₀ s₀ + i * Spec.Blake2.blockBytes w) (fl s₀)) s' s' ∧
      Env w (scA s₀) s' ∧
      Frame [⟨scA s₀, 256⟩] s.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.gpr .rdi = stA s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp := by
  have hw := hP.hw
  have hw8 : w / 8 ≤ 8 := by rcases hw with rfl | rfl <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hw hp hi hc.r9 hc.rd hc.wr hc.frame hc.slots.bl)
    fun sa ⟨ga, rda', wra', fa, ma⟩ => ?_
  have hsc : scR (scA s₀) ∈ sa.wr := wra' ▸ hp.hsc
  have hsl : ∀ k, k < 16 → vOff k + w / 8 ≤ 512 := fun k hk => by simp only [vOff]; omega_using [hw8, hk]
  have hhi : 256 ≤ hiOff w ∧ hiOff w + w / 8 ≤ 512 := by
    simp only [hiOff, thiOff, tloOff]; split <;> omega
  refine WP.mono (init_ok hw (P := P) (s := sa) (scr := scA s₀) (stp := stA s₀)
    ((ga .r9 (by decide) (by decide)).trans hc.r9) ((ga .rdi (by decide) (by decide)).trans hc.rdi)
    (out_sc hsc (hsl 8 (by decide))) (out_sc hsc (hsl 9 (by decide)))
    (out_sc hsc (hsl 10 (by decide))) (out_sc hsc (hsl 11 (by decide)))
    (fun k hk => by rw [rda', wra']; exact hp.in_st hw hk)
    (in_sc hsc (by simp only [tloOff]; omega_using [hw8])) (in_sc hsc hhi.2)
    (in_sc hsc (by simp only [fOff]; omega_using [hw8])))
    fun sb ⟨mb, gk, g10, g11, g12, g13, g9, gdi, gsp, _, rdb, wrb⟩ => ?_
  have c : ∀ k, 8 ≤ k → k < 16 → (⟨scA s₀, 256⟩ : Region).Contains (slot (scA s₀) k) (w / 8) :=
    fun k h1 h2 => contains_off (by simp only [vOff]; omega_using [hw8, h2]) (by simp only [vOff]; omega_using [h2])
  have fb : Frame [⟨scA s₀, 256⟩] s.mem sb.mem := by
    rw [mb]
    refine ((((fa.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 9 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 10 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 11 (by decide) (by decide))
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)
  have fb' : Frame [stR w s₀, ⟨scA s₀, 256⟩] s.mem sb.mem :=
    fb.mono fun r hr => List.mem_cons_of_mem _ hr
  have sep : ∀ {j k : Nat} (m : Mem) (v : BitVec w), j < 16 → k < 16 → j ≠ k →
      (m.writeW (slot (scA s₀) k) v).readW (slot (scA s₀) j) w = m.readW (slot (scA s₀) j) w :=
    fun m v hj hk hjk => readW_writeW_off _ _ _ (by simp only [vOff]; omega_using [hhi, hj])
      (by simp only [vOff]; omega_using [hhi, hk]) (by simp only [vOff]; omega_using [hw8, hjk]) hw8
  have h8 : sb.mem.readW (slot (scA s₀) 8) w = P.IV[0] := by
    rw [mb, sep (j := 8) (k := 11) _ _ (by decide) (by decide) (by decide),
      sep (j := 8) (k := 10) _ _ (by decide) (by decide) (by decide),
      sep (j := 8) (k := 9) _ _ (by decide) (by decide) (by decide), readW_writeW_self' hw]
  have h9 : sb.mem.readW (slot (scA s₀) 9) w = P.IV[1] := by
    rw [mb, sep (j := 9) (k := 11) _ _ (by decide) (by decide) (by decide),
      sep (j := 9) (k := 10) _ _ (by decide) (by decide) (by decide), readW_writeW_self' hw]
  have h10 : sb.mem.readW (slot (scA s₀) 10) w = P.IV[2] := by
    rw [mb, sep (j := 10) (k := 11) _ _ (by decide) (by decide) (by decide), readW_writeW_self' hw]
  have h11 : sb.mem.readW (slot (scA s₀) 11) w = P.IV[3] := by
    rw [mb, readW_writeW_self' hw]
  have hH : ∀ k (hk : k < 8), sb.gpr (wreg k) =
      (Spec.Blake2.stateAt w s.mem (stA s₀))[k].setWidth 64 := fun k hk => by
    rw [gk k hk, hp.keep_st fb (by decide) hw hk, stateAt_get _ _ hk]
  have etl : sb.mem.readW (off (scA s₀) tloOff) w =
      BitVec.ofNat w (t₀ s₀ + i * Spec.Blake2.blockBytes w) := by
    rw [hp.keep_sc fb' (by decide) (by simp only [tloOff]; omega_using [hw8])]
    exact readW_lo hw hc.slots.tlo
  have ehi : sb.mem.readW (off (scA s₀) (hiOff w)) w =
      BitVec.ofNat w ((t₀ s₀ + i * Spec.Blake2.blockBytes w) / 2 ^ w) := by
    rw [hp.keep_sc fb' hhi.1 hhi.2]
    exact readW_hi hw hc.slots.tlo hc.slots.thi
  have efl : sb.mem.readW (off (scA s₀) fOff) w = flagW w (fl s₀) := by
    rw [hp.keep_sc fb' (by decide) (by simp only [fOff]; omega_using [hw8])]
    exact readW_flag hw hc.slots.f
  have hr9 : sb.gpr .r9 = scA s₀ := g9.trans ((ga .r9 (by decide) (by decide)).trans hc.r9)
  have hmsg : ∀ j : Fin 16, sb.mem.readW (off (scA s₀) (msgOff w j)) w = blk w s₀ i j := fun j => by
    have hm := msg_lt hw j
    have sm : ∀ (m : Mem) (v : BitVec w) (k : Nat), 8 ≤ k → k < 16 →
        (m.writeW (slot (scA s₀) k) v).readW (off (scA s₀) (msgOff w j)) w =
          m.readW (off (scA s₀) (msgOff w j)) w :=
      fun m v k h1 h2 => readW_writeW_off _ _ _ (by omega_using [hm]) (by simp only [vOff]; omega_using [hm, h2])
        (by simp only [vOff]; omega_using [hm]) hw8
    rw [mb, sm _ _ 11 (by decide) (by decide), sm _ _ 10 (by decide) (by decide),
      sm _ _ 9 (by decide) (by decide), sm _ _ 8 (by decide) (by decide)]
    exact ma j
  have hsb : scR (scA s₀) ∈ sb.wr := wrb.trans wra' ▸ hp.hsc
  refine ⟨⟨holds_init hH h8 h9 h10 h11 (by rw [g10, etl]) (by rw [g11, ehi]) (by rw [g12, efl])
    g13, Frame.refl _ _, hmsg, rfl, rfl, hr9, rfl, rfl⟩,
    ⟨hsb, fun j => in_sc hsb (by have := msg_lt hw j; omega_using [this]),
      fun j k tk => off_sep _ (by have := msg_lt hw j; simp only [vOff]; omega_using [this, tk.1])
        (by have := msg_lt hw j; omega_using [this]) (by simp only [vOff]; omega_using [tk.2, hw8])⟩,
    fb, rdb.trans rda', wrb.trans wra',
    gdi.trans ((ga .rdi (by decide) (by decide)).trans hc.rdi),
    gsp.trans ((ga .rsp (by decide) (by decide)).trans hc.rsp)⟩

/-! ## The parameter slots after `advance` -/

theorem advMem_frame (scr : Addr) (m : Mem) : Frame [⟨scr, 288⟩] m (advMem w scr m) := by
  have c : ∀ d, d + 8 ≤ 288 → (⟨scr, 288⟩ : Region).Contains (off scr d) (64 / 8) :=
    fun d hd => contains_off hd (by omega_using [hd])
  simp only [advMem]
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (c _ (by decide))
  have f₁ := ((Frame.refl [(⟨scr, 288⟩ : Region)] m).writeW (List.mem_singleton_self _)
    (m.readW (off scr blOff) 64 + bbv w) (c blOff (by decide))).writeW (List.mem_singleton_self _)
    (m.readW (off scr tloOff) 64 + bbv w) (c tloOff (by decide))
  split
  · exact f₁.writeW (List.mem_singleton_self _) _ (c thiOff (by decide))
  · exact f₁

theorem readW_writeW_sc (scr : Addr) (m : Mem) {d e : Nat} (v : BitVec 64)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 < 2 ^ 32) (he : e + 8 < 2 ^ 32) :
    (m.writeW (off scr e) v).readW (off scr d) 64 = m.readW (off scr d) 64 :=
  readW_writeW_off (w := 64) m scr v hd he h (by decide)

theorem advMem_reads (scr : Addr) (m : Mem) :
    (advMem w scr m).readW (off scr blOff) 64 = m.readW (off scr blOff) 64 + bbv w ∧
    (advMem w scr m).readW (off scr tloOff) 64 = m.readW (off scr tloOff) 64 + bbv w ∧
    (advMem w scr m).readW (off scr nOff) 64 = m.readW (off scr nOff) 64 - 1 ∧
    (w = 64 → (advMem w scr m).readW (off scr thiOff) 64 = m.readW (off scr thiOff) 64 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (m.readW (off scr tloOff) 64).toNat + (bbv w).toNat))).setWidth 64) := by
  simp only [advMem]
  split
  · simp (disch := decide) only [readW_writeW_sc, Mem.readW_writeW_self64]
    exact ⟨trivial, trivial, trivial, fun _ => trivial⟩
  · rename_i h
    simp (disch := decide) only [readW_writeW_sc, Mem.readW_writeW_self64]
    exact ⟨trivial, trivial, trivial, fun e => absurd e h⟩

/-! ## Advancing the parameters -/

theorem bb_eq : 16 * ws w = Spec.Blake2.blockBytes w := rfl

theorem blkAddr_succ (s₀ : State) (i : Nat) : blkAddr w s₀ i + bbv w = blkAddr w s₀ (i + 1) := by
  simp only [blkAddr, bbv, bb_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]

theorem n_succ {nb i : Nat} (h : i < nb) :
    BitVec.ofNat 64 (nb - i) - 1 = BitVec.ofNat 64 (nb - (i + 1)) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_using [h]),
    Nat.sub_sub]

theorem t_succ (t i : Nat) : BitVec.ofNat 64 (t + i * Spec.Blake2.blockBytes w) + bbv w =
    BitVec.ofNat 64 (t + (i + 1) * Spec.Blake2.blockBytes w) := by
  rw [bbv, bb_eq, BitVec.ofNat_add_ofNat, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem saved_bounds : ∀ p ∈ saved, 288 ≤ p.2 ∧ p.2 + 8 ≤ 512 := by decide

theorem slotsR_sub (scr : Addr) : Region.Sub (slotsR scr) ⟨scr, 256⟩ := sub_lo scr (by decide)

theorem body_ok {P : Params w} (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {i : Nat}
    (hi : i < nb s₀) {s : State} (hc : Common P s₀ i s) :
    WP isa (body P) s fun s' =>
      Common P s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hw := hP.hw
  have hw8 : w / 8 ≤ 8 := by rcases hw with rfl | rfl <;> decide
  refine WP.seq (WP.mono (stage1_ok hP hp hi hc) fun sb ⟨hR, he, fb, rdb, wrb, dib, spb⟩ => ?_)
  have hscb : scR (scA s₀) ∈ sb.wr := wrb ▸ hp.hsc
  refine WP.seq (WP.mono (rounds_ok hP he hR P.r) fun sc hR' => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  have hscc : scR (scA s₀) ∈ sc.wr := hR'.wr ▸ hscb
  have hsl : ∀ k, k < 16 → vOff k + w / 8 ≤ 512 := fun k hk => by simp only [vOff]; omega_using [hw8, hk]
  refine WP.mono (spill_ok hw hR'.r9 (out_sc hscc (hsl 12 (by decide))) (out_sc hscc (hsl 13 (by decide)))
    (out_sc hscc (hsl 14 (by decide))) (out_sc hscc (hsl 15 (by decide))))
    fun sd ⟨md, gd, rdd, wrd⟩ => ?_
  -- The work vector after the rounds.
  generalize hvR : (List.range P.r).foldl (Spec.Blake2.round P (blk w s₀ i))
    (V0 P (Spec.Blake2.stateAt w s.mem (stA s₀)) (t₀ s₀ + i * Spec.Blake2.blockBytes w)
      (fl s₀)) = vR at hR'
  have hreg : ∀ k (hk : k < 16), ¬third k → sc.gpr (wreg k) = (vR[k]'(by omega_using [hk])).setWidth 64 :=
    fun k hk h => by have := hR'.holds k hk; rwa [ite_eq_right h] at this
  have hmem : ∀ k (hk : k < 16), third k →
      sc.mem.readW (slot (scA s₀) k) w = (vR[k]'(by omega_using [hk])) :=
    fun k hk h => by have := hR'.holds k hk; rwa [ite_eq_left h] at this
  have ssep : ∀ {j k : Nat} (m : Mem) (v : BitVec w), j < 16 → k < 16 → j ≠ k →
      (m.writeW (slot (scA s₀) k) v).readW (slot (scA s₀) j) w = m.readW (slot (scA s₀) j) w :=
    fun m v hj hk hjk => readW_writeW_off _ _ _ (by simp only [vOff]; omega_using [hw8, hj])
      (by simp only [vOff]; omega_using [hw8, hk]) (by simp only [vOff]; omega_using [hw8, hjk]) hw8
  have hv : ∀ j (hj : j < 8), sd.gpr (wreg j) = (vR[j]'(by omega_using [hj])).setWidth 64 := fun j hj => by
    have h3 : ¬(8 ≤ j ∧ j ≤ 11) := by omega_using [hj]
    rw [gd]; exact hreg j (by omega_using [hj]) h3
  have hs : ∀ j (hj : j < 8), sd.mem.readW (slot (scA s₀) (j + 8)) w = (vR[j + 8]'(by omega_using [hj])) := by
    have e : ∀ k (hk : k < 16), ¬third k → (sc.gpr (wreg k)).setWidth w = (vR[k]'(by omega_using [hk])) :=
      fun k hk h => (congrArg (BitVec.setWidth w) (hreg k hk h)).trans (setWidth_setWidth' hw _)
    have e12 : (sc.gpr .r10).setWidth w = vR[12] := e 12 (by decide) (by decide)
    have e13 : (sc.gpr .r11).setWidth w = vR[13] := e 13 (by decide) (by decide)
    have e14 : (sc.gpr .r12).setWidth w = vR[14] := e 14 (by decide) (by decide)
    have e15 : (sc.gpr .r13).setWidth w = vR[15] := e 15 (by decide) (by decide)
    have m8 := hmem 8 (by decide) (by decide)
    have m9 := hmem 9 (by decide) (by decide)
    have m10 := hmem 10 (by decide) (by decide)
    have m11 := hmem 11 (by decide) (by decide)
    rw [md, forall_lt_eight']
    simp (disch := decide) only [ssep, readW_writeW_self' hw, Nat.reduceAdd, e12, e13, e14,
      e15, m8, m9, m10, m11, and_self]
  have hr9d : sd.gpr .r9 = scA s₀ := by rw [gd]; exact hR'.r9
  have hdid : sd.gpr .rdi = stA s₀ := by rw [gd, hR'.rdi, dib]
  have hrdd : sd.rd = s₀.rd := rdd.trans (hR'.rd.trans rdb)
  have hwrd : sd.wr = s₀.wr := wrd.trans (hR'.wr.trans wrb)
  refine WP.mono (finish_ok hw hp hr9d hdid hrdd hwrd hv hs) fun se hF => ?_
  refine WP.mono (advance_ok hw (hF.r9.trans hr9d) (by rw [hF.wr, hwrd]; exact hp.hsc))
    fun sf ⟨mf, zf, r9f, dif, spf, rdf, wrf⟩ => ?_
  -- Frames.
  have cS : ∀ k, 8 ≤ k → k < 16 → (slotsR (scA s₀)).Contains (slot (scA s₀) k) (w / 8) :=
    fun k h1 h2 => by
      simp only [slotsR, slot, off_eq]
      exact Offset.contains _ (by simp only [vOff]; omega_using []) (by simp only [vOff]; omega_using [hw8, h2]) (by omega_using [])
  have Fd : Frame [slotsR (scA s₀)] sc.mem sd.mem := by
    rw [md]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cS 12 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cS 13 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cS 14 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cS 15 (by decide) (by decide))
  have F256 : Frame [⟨scA s₀, 256⟩] s.mem sd.mem :=
    fb.trans ((hR'.frame.trans Fd).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slotsR_sub _⟩)
  have F1 : Frame [stR w s₀, ⟨scA s₀, 256⟩] s.mem se.mem :=
    (F256.mono fun r hr => List.mem_cons_of_mem _ hr).trans
      (hF.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  have BF : Frame [stR w s₀, ⟨scA s₀, 288⟩] s.mem sf.mem := by
    refine (F1.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide)⟩
    · rw [mf]; exact (advMem_frame _ _).mono fun r hr => List.mem_cons_of_mem _ hr
  have sv : ∀ d, 256 ≤ d → d + 8 ≤ 512 →
      se.mem.readW (off (scA s₀) d) 64 = s.mem.readW (off (scA s₀) d) 64 :=
    fun d h1 h2 => hp.keep_sc F1 h1 h2
  obtain ⟨ab, at', an, ah⟩ := advMem_reads (w := w) (scA s₀) se.mem
  rw [← mf] at ab at' an ah
  have hn : se.mem.readW (off (scA s₀) nOff) 64 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [sv _ (by decide) (by decide), hc.slots.n, n_succ hi]
  refine ⟨⟨dif.trans (hF.rdi.trans hdid), r9f.trans (hF.r9.trans hr9d), ?_,
    rdf.trans (hF.rd.trans hrdd), wrf.trans (hF.wr.trans hwrd), ?_, ?_, ?_, ?_⟩, by rw [zf, hn]⟩
  · rw [spf, hF.rsp, gd, hR'.rsp, spb]
  · refine hc.frame.trans (BF.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide)⟩
  · rw [compressBlocks_succ, ← hc.state, F_eq, hvR]
    apply Vector.ext; intro j hj
    rw [stateAt_get _ _ hj, Vector.getElem_ofFn,
      hp.keep_st (m := se.mem) (by rw [mf]; exact advMem_frame _ _) (by decide) hw hj, hF.st j hj]
    simp only [hj, ite_true]
    rw [hp.keep_st F256 (by decide) hw hj, ← stateAt_get _ _ hj]
    exact (BitVec.xor_comm _ _).trans (BitVec.xor_assoc _ _ _).symm
  · intro p hp'
    have := saved_bounds p hp'
    rw [hp.keep_sc BF this.1 this.2]; exact hc.saved p hp'
  · refine ⟨?_, ?_, ?_, fun h64 => ?_, ?_⟩
    · rw [ab, sv _ (by decide) (by decide), hc.slots.bl, blkAddr_succ]
    · rw [an, hn]
    · rw [at', sv _ (by decide) (by decide), hc.slots.tlo, t_succ]
    · subst h64
      rw [ah rfl, sv _ (by decide) (by decide), sv _ (by decide) (by decide), hc.slots.tlo,
        hc.slots.thi rfl, bbv, carry_ofNat _ _ (by decide), bb_eq, Nat.add_mul, Nat.one_mul,
        ← Nat.add_assoc]
    · rw [hp.keep_sc BF (by decide) (by decide)]; exact hc.slots.f

/-! ## The prologue -/

theorem pro_eq : save ++ setup = [
    .store (at_ .r9 296) .rbx, .store (at_ .r9 304) .rbp, .store (at_ .r9 312) .r12,
    .store (at_ .r9 320) .r13, .store (at_ .r9 328) .r14, .store (at_ .r9 336) .r15,
    .mov32 .r8 (.reg .r8), .store (at_ .r9 blOff) .rsi, .store (at_ .r9 nOff) .rdx,
    .store (at_ .r9 tloOff) .rcx, .mov32 .rax (.imm 0), .store (at_ .r9 thiOff) .rax,
    .alu .test .r8 (.reg .r8)] := rfl

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem :=
  (((((((((s₀.mem.writeW (off (scA s₀) 296) (s₀.gpr .rbx)).writeW (off (scA s₀) 304) (s₀.gpr .rbp)).writeW
    (off (scA s₀) 312) (s₀.gpr .r12)).writeW (off (scA s₀) 320) (s₀.gpr .r13)).writeW
    (off (scA s₀) 328) (s₀.gpr .r14)).writeW (off (scA s₀) 336) (s₀.gpr .r15)).writeW
    (off (scA s₀) blOff) (s₀.gpr .rsi)).writeW (off (scA s₀) nOff) (s₀.gpr .rdx)).writeW
    (off (scA s₀) tloOff) (s₀.gpr .rcx)).writeW (off (scA s₀) thiOff) (0 : BitVec 64)

theorem pro_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save ++ setup)) s₀ fun s₁ =>
      s₁.mem = proMem s₀ ∧ s₁.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → r ≠ .r8 → s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&& ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0) ∧
      s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have o : ∀ d, d + 8 ≤ 512 → InRegions s₀.wr (off (scA s₀) d) 8 := fun d hd => out_sc hp.hsc hd
  have o1 := o 296 (by decide); have o2 := o 304 (by decide); have o3 := o 312 (by decide)
  have o4 := o 320 (by decide); have o5 := o 328 (by decide); have o6 := o 336 (by decide)
  have o7 := o blOff (by decide); have o8 := o nOff (by decide); have o9 := o tloOff (by decide)
  have o10 := o thiOff (by decide)
  have e0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := by decide
  rw [pro_eq]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, readSrc32, State.store64, proMem, e0, ea_at, isa, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
    o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], trivial⟩

theorem zf_last (x : BitVec 32) : (x.setWidth 64 &&& x.setWidth 64 == 0) = !(x != 0) := by
  rw [BitVec.and_self, bne, Bool.not_not, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))] at this
    exact BitVec.eq_of_toNat_eq (this.trans rfl)
  · intro h; subst h; rfl

theorem flag_ok {s₀ s₁ : State} (hm : s₁.mem = proMem s₀) (hrax : s₁.gpr .rax = 0)
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₁.gpr r = s₀.gpr r)
    (hzf : s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&&
      ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0))
    (hwr : scR (scA s₀) ∈ s₁.wr) :
    WP isa flag s₁ fun s₂ =>
      s₂.mem = (proMem s₀).writeW (off (scA s₀) fOff) (flagW 64 (fl s₀)) ∧
      s₂.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have h9 : s₁.gpr .r9 = scA s₀ := hg .r9 (by decide) (by decide)
  have hdx : s₁.gpr .rdx = s₀.gpr .rdx := hg .rdx (by decide) (by decide)
  refine WP.seq (WP.mono (Q := fun s : State => s.gpr .rax = flagW 64 (fl s₀) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ ∀ r, r ≠ .rax → s.gpr r = s₁.gpr r) ?_ fun s h => ?_)
  · refine WP.ite (!(fl s₀)) (by simp only [eval, hzf, zf_last]) (fun h => ?_) (fun h => ?_)
    · have hf : fl s₀ = false := by simpa using h
      exact WP.block_nil ⟨by rw [hrax, hf]; rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · have hf : fl s₀ = true := by simpa using h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, RegUpd.gpr_setReg,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true, Option.map_some,
        Option.some.injEq, exists_eq_left', hf]
      exact ⟨by decide, trivial, trivial, trivial, fun r h => by simp only [h, ite_false]⟩
  · obtain ⟨hrax', hm', hrd', hwr', hg'⟩ := h
    have o : InRegions s.wr (off (scA s₀) fOff) 8 := out_sc (hwr' ▸ hwr) (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, ea_at,
      State.store64, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, hg' .r9 (by decide), h9, o, hrax', hm', hm,
      hg' .rdx (by decide), hdx, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, fun r h1 h2 => by rw [hg' r h1, hg r h1 h2], hrd', hwr'⟩

theorem common0 {P : Params w} (hw : w = 64 ∨ w = 32) {s₀ : State} (hp : Pre w s₀) {s₂ : State}
    (hm : s₂.mem = (proMem s₀).writeW (off (scA s₀) fOff) (flagW 64 (fl s₀)))
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r) (hrd : s₂.rd = s₀.rd)
    (hwr : s₂.wr = s₀.wr) : Common P s₀ 0 s₂ := by
  have W : ∀ {m : Mem} (d : Nat) (v : BitVec 64), d + 8 ≤ 512 → Frame [scR (scA s₀)] s₀.mem m →
      Frame [scR (scA s₀)] s₀.mem (m.writeW (off (scA s₀) d) v) :=
    fun d v hd h => h.writeW (List.mem_singleton_self _) v (contains_off hd (by omega_using [hd]))
  have F0 : Frame [scR (scA s₀)] s₀.mem s₂.mem := by
    rw [hm, proMem]
    repeat (first | refine W _ _ (by decide +kernel) ?_ | exact Frame.refl _ _)
  have R : ∀ {d : Nat}, s₂.mem.readW (off (scA s₀) d) 64 =
      ((proMem s₀).writeW (off (scA s₀) fOff) (flagW 64 (fl s₀))).readW (off (scA s₀) d) 64 :=
    by intro d; rw [hm]
  refine ⟨hg _ (by decide +kernel) (by decide +kernel), hg _ (by decide +kernel) (by decide +kernel),
    hg _ (by decide +kernel) (by decide +kernel), hrd, hwr, F0.mono fun r hr => ?_, ?_, fun p hp' => ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; simp [hr]
  · rw [compressBlocks_zero]
    apply Vector.ext; intro j hj
    rw [stateAt_get _ _ hj, stateAt_get _ _ hj]
    exact hp.keep_st F0 (by decide +kernel) hw hj
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide +kernel) only [R, proMem, readW_writeW_sc, Mem.readW_writeW_self64]
  · refine ⟨?_, ?_, ?_, fun _ => ?_, ?_⟩ <;>
      simp (disch := decide +kernel) only [R, proMem, readW_writeW_sc, Mem.readW_writeW_self64]
    · rw [blkAddr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt (s₀.gpr .rcx).isLt]; rfl

/-! ## The epilogue -/

theorem restore_ok {P : Params w} {s₀ : State} (hp : Pre w s₀) {s : State}
    (hc : Common P s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 P).post s₀ s' := by
  have hsc : scR (scA s₀) ∈ s.wr := hc.wr ▸ hp.hsc
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_sc⟩) (by decide)
  refine WP.mono (Spill.restore_ok .r9 saved s₀.gpr s (by decide) (fun p hp' => ?_) fun p hp' => ?_)
    fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := in_sc (rs := s.rd) hsc (d := p.2) (n := 8) (by have := saved_bounds p hp'; omega_using [this])
    rw [off, ofInt_natCast] at this
    rw [hc.r9]; exact this
  · have := hc.saved p hp'
    rw [off, ofInt_natCast] at this
    rw [hc.r9]; exact this
  · exact ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hc.rsp, by rw [hm]; exact hret⟩,
      by show Spec.Blake2.stateAt _ _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {P : Params w} (hP : Ok P) {s₀ : State} (hp : Pre w s₀) :
    WP isa (compress P) s₀ fun s' => gprPreserved s₀ s' ∧ (compressX86_64 P).post s₀ s' := by
  have hw := hP.hw
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨hm, hrax, hg, hzf, hrd, hwr⟩ => ?_)
  refine WP.seq (WP.mono (flag_ok hm hrax hg hzf (hwr ▸ hp.hsc))
    fun s₂ ⟨hm₂, hzf₂, hg₂, hrd₂, hwr₂⟩ => ?_)
  have hc₀ : Common P s₀ 0 s₂ := common0 hw hp hm₂ hg₂ (hrd₂.trans hrd) (hwr₂.trans hwr)
  refine WP.seq (WP.mono (Q := Common P s₀ (nb s₀)) ?_ fun s₃ hc => restore_ok hp hc)
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp only [eval, hzf₂])
    (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [BitVec.and_self, beq_iff_eq] at h; simp only [nb, h]; rfl
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Common P s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa (body P) s (fun s' =>
        (isa.eval .ne s' = some false ∧ Common P s₀ (nb s₀) s') ∨
        (isa.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hc⟩
      refine WP.mono (body_ok hP hp hi hc) fun s' ⟨hc', hz⟩ => ?_
      by_cases hlast : i + 1 = nb s₀
      · left
        refine ⟨?_, hlast ▸ hc'⟩
        simp only [eval, hz, ← hlast, Nat.sub_self, Option.map_some]; rfl
      · right
        have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
        refine ⟨?_, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hne], hc'⟩
        have h0 : (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro h'
          have h'' := congrArg BitVec.toNat h'
          rw [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s₀.gpr .rdx).isLt)] at h''
          exact hne (h''.trans rfl)
        simp only [eval, hz, h0, Option.map_some]; rfl
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hc₀⟩

/-! ## Results -/

/-- The public part of the input: the pointers, `n`, `t`, the low half of
`last`, and the state's and `scratch`'s regions (of `l` and 512 bytes). -/
def τ₀ (l : Nat) : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r9], flags := false, lens := [l, 512],
    bases := [(.rdi, 0, 0), (.r9, 1, 0)], lo := .ofList [.r8] }

theorem agree₀ {P : Params w} (hw : w = 64 ∨ w = 32) {s₁ s₂ : State}
    (h₁ : (compressX86_64 P).pre s₁) (h₂ : (compressX86_64 P).pre s₂)
    (hpub : (compressX86_64 P).pub s₁ s₂) : X86_64.Taint.Agree (τ₀ (8 * (w / 8))) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (compressX86_64 P).pre s → X86_64.Taint.Wf (τ₀ (8 * (w / 8))) s := by
    intro s hs
    obtain ⟨-, hwr, hd, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hwr, τ₀], by simp [hwr, hd], ?_⟩, fun p hp => ?_⟩
    · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> rcases hw with rfl | rfl <;> dsimp only <;> omega_using []
    · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hwr]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    fun r hr => ?_, X86_64.Taint.noXr⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p6]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact p5

theorem compress_correct {P : Params w} (hP : Ok P)
    (hmx : (Impl.Blake2.X86_64.compress P).allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : (compressX86_64 P).pre s) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.compress P) s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 P).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct hP (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec hmx he h.1, h.2⟩

theorem compressB_correct (s : State) (hs : (compressX86_64 Spec.Blake2.b).pre s) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.compress Spec.Blake2.b) s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.b).post s s' :=
  compress_correct ok_b (by lit_decide) s hs

theorem compressS_correct (s : State) (hs : (compressX86_64 Spec.Blake2.s).pre s) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.compress Spec.Blake2.s) s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.s).post s s' :=
  compress_correct ok_s (by lit_decide) s hs

theorem compressB_ct : ConstantTime isa (compressX86_64 Spec.Blake2.b).pre
    (compressX86_64 Spec.Blake2.b).pub (Impl.Blake2.X86_64.compress Spec.Blake2.b) :=
  VG.Taint.constantTime (A := taint) (τ₀ 64) (fun _ _ h₁ h₂ hp => agree₀ (.inl rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compressS_ct : ConstantTime isa (compressX86_64 Spec.Blake2.s).pre
    (compressX86_64 Spec.Blake2.s).pub (Impl.Blake2.X86_64.compress Spec.Blake2.s) :=
  VG.Taint.constantTime (A := taint) (τ₀ 32) (fun _ _ h₁ h₂ hp => agree₀ (.inr rfl) h₁ h₂ hp)
    (by taint_decide)

/-- A state satisfying the precondition (with no blocks), for a state of `len` bytes. -/
def satState (len : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .r9 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, len⟩, ⟨0x3000, 512⟩]

theorem compressB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.compress Spec.Blake2.b)
      (Proof.Blake2.compressBContract X86_64.abi) :=
  Verified.of_correct compressB_correct compressB_ct (by
    sig_implies [Proof.Blake2.compressBContract, Proof.Blake2.compressBSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)

theorem compressS_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.compress Spec.Blake2.s)
      (Proof.Blake2.compressSContract X86_64.abi) :=
  Verified.of_correct compressS_correct compressS_ct (by
    sig_implies [Proof.Blake2.compressSContract, Proof.Blake2.compressSSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 32)

end VG.Proof.Blake2.X86_64
