module

public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
public import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
meta import VerifiedGarbage.Proof.Blake2.X86_64.Avx.Lit
meta import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Blake2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Blake2.X86_64.Lit
meta import VerifiedGarbage.Proof.Blake2.X86_64.Compress
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Blake2.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Blake2.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Blake2.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Blake2.Spec
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Blake2.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Blake2.Contract

/-! ### `Blake2.X86_64.Avx.Compress`, which this module and modules that import it used -/

section

/-! ### `Blake2.X86_64.Avx.Round`, which only this module used -/

section

/-! ### `Blake2.Cols`, which only this module used -/

section

/-!
# A BLAKE2 round on four columns at once, for any word size

As `Lanes.lean` for BLAKE2b: the work vector as four rows of four words
(`4k…4k+3` for `k < 4`); the four column `G`s of a round are `G` on each
column of the rows at once (`mixColsP`), with the message words of column
`q` (`x q`, `y q`); the four diagonal `G`s are the same after rows 0, 2 and
3 are rotated left by three, one and two places (`rotInP`; row 1 stays), so
that column `q` holds diagonal `(q + 3) mod 4`, rotated back after it
(`rotOutP`). This is how code keeping each row in one vector register
computes a round (`round_colsP`).
-/

@[expose] public section

namespace VG.Proof.Blake2

open VG.Spec.Blake2

variable {w : Nat} (P : Params w)

/-- Component `k` of the result of `mix`: `a`, `b`, `c` or `d`. -/
def pick4 (k : Nat) (x : BitVec w × BitVec w × BitVec w × BitVec w) : BitVec w :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- `G` on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once,
with the message words `x q` and `y q`. -/
def mixColsP (x y : Nat → BitVec w) (v : Work w) : Work w :=
  Vector.ofFn fun j => pick4 (j.val / 4)
    (mix P (v[j.val % 4]'(by omega_using [])) (v[4 + j.val % 4]'(by omega_using [])) (v[8 + j.val % 4]'(by omega_using []))
      (v[12 + j.val % 4]'(by omega_using [])) (x (j.val % 4)) (y (j.val % 4)))

/-- Rows 0, 2 and 3 rotated left by three, one and two places. -/
def rotInP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + j.val / 4 + 3) % 4]'(by omega_using [])

/-- Rows 0, 2 and 3 rotated left by one, three and two places (back). -/
def rotOutP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + 3 * (j.val / 4) + 1) % 4]'(by omega_using [])

theorem mixColsP_get (x y : Nat → BitVec w) (v : Work w) (j : Nat) (hj : j < 16) :
    (mixColsP P x y v)[j] = pick4 (j / 4) (mix P (v[j % 4]'(by omega_using [])) (v[4 + j % 4]'(by omega_using []))
      (v[8 + j % 4]'(by omega_using [])) (v[12 + j % 4]'(by omega_using [])) (x (j % 4)) (y (j % 4))) := by
  simp only [mixColsP, Vector.getElem_ofFn]

theorem rotInP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (rotInP v)[j] = v[4 * (j / 4) + (j % 4 + j / 4 + 3) % 4]'(by omega_using [hj]) := by
  simp only [rotInP, Vector.getElem_ofFn]

theorem rotOutP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (rotOutP v)[j] = v[4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4]'(by omega_using [hj]) := by
  simp only [rotOutP, Vector.getElem_ofFn]

theorem cases16' {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega_using [hj]

/-- The value of a literal index. -/
theorem val_lit16 (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

theorem G_getP (v : Work w) {a c d e : Fin 16} (hab : a.1 ≠ c.1) (hac : a.1 ≠ d.1)
    (had : a.1 ≠ e.1) (hcd : c.1 ≠ d.1) (hce : c.1 ≠ e.1) (hde : d.1 ≠ e.1) (x y : BitVec w)
    (k : Nat) (hk : k < 16) :
    (G P v a c d e x y)[k]'hk =
      if c.1 = k then (mix P (v[a.1]'a.2) (v[c.1]'c.2) (v[d.1]'d.2) (v[e.1]'e.2) x y).2.1
      else if d.1 = k then (mix P (v[a.1]'a.2) (v[c.1]'c.2) (v[d.1]'d.2) (v[e.1]'e.2) x y).2.2.1
      else if e.1 = k then (mix P (v[a.1]'a.2) (v[c.1]'c.2) (v[d.1]'d.2) (v[e.1]'e.2) x y).2.2.2
      else if a.1 = k then (mix P (v[a.1]'a.2) (v[c.1]'c.2) (v[d.1]'d.2) (v[e.1]'e.2) x y).1 else (v[k]'hk) :=
  G_get P v hab hac had hcd hce hde x y k hk

/-- The four column `G`s of a round. -/
theorem columns_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = mixColsP P x y v := by
  -- The side conditions of `G_getP` once for each `G`, not at every rewrite of every case.
  obtain g0 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 0) (c := 4) (d := 8) (e := 12) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g1 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 1) (c := 5) (d := 9) (e := 13) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g2 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 2) (c := 6) (d := 10) (e := 14) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g3 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 3) (c := 7) (d := 11) (e := 15) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  apply Vector.ext
  intro j hj
  simp only [mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16' hj
  all_goals
    simp only [g0, g1, g2, g3, val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, pick4]

/-- The four diagonal `G`s of a round, with the message words `x i` and `y i`
of diagonal `i`. -/
theorem diagonals_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) =
      rotOutP (mixColsP P (fun q => x ((q + 3) % 4)) (fun q => y ((q + 3) % 4)) (rotInP v)) := by
  -- The side conditions of `G_getP` once for each `G`, not at every rewrite of every case.
  obtain g0 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 0) (c := 5) (d := 10) (e := 15) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g1 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 1) (c := 6) (d := 11) (e := 12) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g2 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 2) (c := 7) (d := 8) (e := 13) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  obtain g3 := (fun (v : Work w) (x y : BitVec w) (k : Nat) (hk : k < 16) =>
      G_getP P v (a := 3) (c := 4) (d := 9) (e := 14) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) x y k hk)
  apply Vector.ext
  intro j hj
  simp only [rotOutP_get, rotInP_get, mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16' hj
  all_goals
    simp only [g0, g1, g2, g3, val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, pick4]

/-- Round `r` on four columns: the column `G`s, then the diagonal ones. -/
theorem round_colsP (m : Block w) (v : Work w) (r : Nat) :
    round P m v r =
      rotOutP (mixColsP P (fun q => m (sigmaAt r (8 + 2 * ((q + 3) % 4))))
        (fun q => m (sigmaAt r (9 + 2 * ((q + 3) % 4))))
        (rotInP (mixColsP P (fun q => m (sigmaAt r (2 * q))) (fun q => m (sigmaAt r (2 * q + 1))) v))) := by
  rw [← diagonals_eqP P (fun i => m (sigmaAt r (8 + 2 * i))) (fun i => m (sigmaAt r (9 + 2 * i))),
    ← columns_eqP]
  rfl

end VG.Proof.Blake2

end

end


/-!
# BLAKE2s on x86-64 with AVX: a round

The rows of the work vector are in `xmm0`–`xmm3` (`words`). Each message
vector is gathered into `xmm5` (`msg_ok`), each half of `G` runs on the
four doublewords at once (`half_cols`), and the diagonals are rotated into
columns and back (`diag_words`, `undiag_words`); `round_ok` composes them
into `Spec.Blake2.round` through `round_colsP`.

Every instruction is `VEX.128`-encoded: only the low lanes of the vector
registers (`State.xmm`) are followed.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2 (mix pick4 mixColsP rotInP rotOutP mixColsP_get rotInP_get rotOutP_get
  round_colsP)

abbrev W := BitVec 32

/-- Doubleword `q` of `r`. -/
abbrev dw (s : State) (r : XReg) (q : Nat) : W := dword (s.xmm r) q

theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

/-! ## Blocks of vector instructions -/

/-- Run instructions that write only vector registers. -/
def run : List VOp → State → State
  | [], s => s
  | o :: os, s => run os (o.exec s)

theorem runBlock_run (os : List VOp) (s : State) :
    runBlock isa (os.map .vop) s = some (run os s) := by
  induction os generalizing s with
  | nil => exact runBlock_nil
  | cons o os ih =>
    rw [List.map_cons, runBlock_cons]
    exact (runStep_some (s := o.exec s)).trans (ih _)

theorem run_append (a b : List VOp) (s : State) : run (a ++ b) s = run b (run a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

@[simp] theorem run_gpr (os : List VOp) (s : State) : (run os s).gpr = s.gpr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_gpr o s)

@[simp] theorem run_mem (os : List VOp) (s : State) : (run os s).mem = s.mem := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_mem o s)

@[simp] theorem run_rd (os : List VOp) (s : State) : (run os s).rd = s.rd := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_rd o s)

@[simp] theorem run_wr (os : List VOp) (s : State) : (run os s).wr = s.wr := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact (ih _).trans (VOp.exec_wr o s)

theorem block_run_ok (os : List VOp) (s : State) {Q : State → Prop} (h : Q (run os s)) :
    WP isa (.block (os.map .vop)) s Q :=
  WP.of_runBlock ⟨_, runBlock_run os s, h⟩

/-! ## The low lanes after `VEX.128` instructions

These hold by definition, but are proven by `(rfl)`, not `rfl`: `simp` uses a
lemma proven by `rfl` as a definitional rewrite, and the kernel then checks
its result by unfolding `VOp.exec` at every instruction of a block. -/

theorem xmm_vbin (op : VBinOp) (d a b : XReg) (s : State) (r : XReg) :
    ((VOp.vbin op .l128 d a b).exec s).xmm r =
      if r = d then op.sse.eval (s.xmm a) (s.xmm b) else s.xmm r := (rfl)

theorem xmm_vshift (op : XShiftOp) (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vshift op .l128 d a n).exec s).xmm r = if r = d then op.eval (s.xmm a) n else s.xmm r :=
  (rfl)

theorem xmm_vpshufd (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) :
    ((VOp.vpshufd .l128 d a o).exec s).xmm r = if r = d then shufDwords (s.xmm a) o else s.xmm r :=
  (rfl)

theorem xmm_vmovdqa (d a : XReg) (s : State) (r : XReg) :
    ((VOp.vmovdqa .l128 d a).exec s).xmm r = if r = d then s.xmm a else s.xmm r := (rfl)

theorem xmm_vmovq (d : XReg) (g : Reg) (s : State) (r : XReg) :
    ((VOp.vmovq d g).exec s).xmm r = if r = d then (0 : BitVec 64) ++ s.gpr g else s.xmm r :=
  (rfl)

/-- What a block leaves: everything but the low lanes of the vector registers
`rs` (and their upper lanes and the flags, which nothing reads). -/
structure XF (rs : List XReg) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : ∀ r, r ∉ rs → t.xmm r = s.xmm r

theorem XF.refl (rs : List XReg) (s : State) : XF rs s s := ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XF.trans {rs : List XReg} {s t u : State} (h : XF rs s t) (h' : XF rs t u) : XF rs s u :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XF.mono {rs rs' : List XReg} {s t : State} (h : XF rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    XF rs' s t := ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem XF.run {os : List VOp} {rs : List XReg} {s : State}
    (h : ∀ r, r ∉ rs → (run os s).xmm r = s.xmm r) : XF rs s (run os s) :=
  ⟨run_gpr os s, run_mem os s, run_rd os s, run_wr os s, h⟩

theorem dw_of_xf {rs : List XReg} {s t : State} (h : XF rs s t) {r : XReg} (hr : r ∉ rs) (q : Nat) :
    dw t r q = dw s r q := by
  simp only [dw, h.xmm r hr]

/-! ## Doublewords -/

theorem rotr_shifts (x : W) {n : Nat} (hn : n < 32) :
    x <<< (32 - n) ||| x >>> n = x.rotateRight n := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hn]
  exact BitVec.or_comm _ _

theorem rotr16 (x : W) : x.rotateLeft 16 = x.rotateRight 16 := by
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.rotateRight, BitVec.rotateRightAux,
    Nat.reduceMod, Nat.reduceSub]
  exact BitVec.or_comm _ _

/-- The `vpshufb` mask rotating each doubleword right by 8 bits. -/
abbrev rotr8Mask : BitVec 128 := 0x0c0f0e0d080b0a090407060500030201#128

theorem pshufb_rotr8_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a rotr8Mask = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 1) % 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem dword_pshufb_rotr8 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rotr8Mask) i = (dword a i).rotateRight 8 := by
  rw [pshufb_rotr8_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword_ofBytes _ hi hm, BitVec.getLsbD_rotateRight]
  have h8 : m % 8 < 8 := Nat.mod_lt _ (by omega_using [])
  simp only [byte, BitVec.getLsbD_extractLsb', getLsbD_dword, h8, decide_true, Bool.true_and,
    show 8 % 32 = 8 from rfl]
  by_cases h : m < 32 - 8
  · have h' : 8 + m < 32 := by omega_using [h]
    simp only [h, h', ite_true, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [h])
  · have h' : m - (32 - 8) < 32 := by omega_using [hm]
    simp only [h, h', hm, ite_false, decide_true, Bool.true_and]
    exact congrArg _ (by omega_using [hm, h])

theorem dword_pshufb_rotr16 (a : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb a rot16Mask) i = (dword a i).rotateRight 16 := by
  rw [dword_pshufb_rot16 _ hi, rotr16]

/-- A 16-byte load, doubleword by doubleword. -/
theorem dword_readW (m : Mem) (a : Addr) {q : Nat} (hq : q < 4) :
    dword (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (4 * q)) 32 := by
  have h := readW_extract m a (w := 128) (k := 4 * q) (n := 4) (by omega_using [hq])
  simp only [← Nat.mul_assoc, Nat.reduceMul] at h
  rw [dword_eq]; exact h

theorem punpcklqdq_dwords (a b : BitVec 128) :
    XBinOp.eval .punpcklqdq a b = ofDwords (dword a 0) (dword a 1) (dword b 0) (dword b 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, ofDwords, dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 32
  · simp [h1, show i < 64 by omega_using [h1]]
  by_cases h2 : i < 64
  · simp [h1, h2, show i - 32 < 32 by omega_using [h2], show 32 + (i - 32) = i by omega_using [h1]]
  by_cases h3 : i < 96
  · simp [h1, h2, show ¬ i - 32 < 32 by omega_using [h2], show i - 32 - 32 = i - 64 by omega_using [],
      show i - 64 < 64 by omega_using [hi], show i - 64 < 32 by omega_using [h3]]
  · simp [h1, h2, show ¬ i - 32 < 32 by omega_using [h2], show ¬ i - 32 - 32 < 32 by omega_using [h3],
      show i - 32 - 32 - 32 < 32 by omega_using [hi], show 32 + (i - 32 - 32 - 32) = i - 64 by omega_using [h3],
      show i - 64 < 64 by omega_using [hi]]

theorem dword_punpcklqdq (a b : BitVec 128) {q : Nat} (hq : q < 4) :
    dword (XBinOp.eval .punpcklqdq a b) q = if q < 2 then dword a q else dword b (q - 2) := by
  rw [punpcklqdq_dwords]
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
    simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      Nat.reduceLT, ↓reduceIte, Nat.reduceSub]

/-! ## The two halves of `G` -/

/-- Half of `G`: `a += x + b; d = (d ^ a) >>> R; c += d; b = (b ^ c) >>> n`. -/
def H (R n : Nat) (v : W × W × W × W) (x : W) : W × W × W × W :=
  let a := v.1 + x + v.2.1
  let d := (v.2.2.2 ^^^ a).rotateRight R
  let c := v.2.2.1 + d
  let b := (v.2.1 ^^^ c).rotateRight n
  (a, b, c, d)

theorem add_right_comm' (a b c : W) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc]

theorem mix_eq (va vb vc vd x y : W) :
    mix Spec.Blake2.s va vb vc vd x y = H 8 7 (H 16 12 (va, vb, vc, vd) x) y := by
  simp only [mix, H, Spec.Blake2.s, add_right_comm' va vb x]
  rw [add_right_comm' _ _ y]

/-- Doubleword `q` of each of the four rows. -/
def cols (s : State) (q : Nat) : W × W × W × W := (dw s .xmm0 q, dw s .xmm1 q, dw s .xmm2 q, dw s .xmm3 q)

def halfOps (mask : XReg) (n : Nat) : List VOp :=
  [.vbin .vpaddd .l128 .xmm0 .xmm0 .xmm5, .vbin .vpaddd .l128 .xmm0 .xmm0 .xmm1,
    .vbin .vpxor .l128 .xmm3 .xmm3 .xmm0, .vbin .vpshufb .l128 .xmm3 .xmm3 mask,
    .vbin .vpaddd .l128 .xmm2 .xmm2 .xmm3, .vbin .vpxor .l128 .xmm1 .xmm1 .xmm2,
    .vshift .psrld .l128 .xmm4 .xmm1 (BitVec.ofNat 8 n),
    .vshift .pslld .l128 .xmm1 .xmm1 (BitVec.ofNat 8 (32 - n)), .vbin .vpor .l128 .xmm1 .xmm1 .xmm4]

theorem half_eq (mask : XReg) (n : Nat) : half mask n = (halfOps mask n).map .vop := rfl

/-- The registers a half writes. -/
abbrev halfRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4]

theorem half_cols {mask : XReg} {R n : Nat} (hn : 0 < n) (hn' : n < 32) {s : State}
    (h0 : mask ≠ .xmm0) (h3 : mask ≠ .xmm3)
    (hm : ∀ y : BitVec 128, ∀ q < 4, dword (XBinOp.eval .pshufb y (s.xmm mask)) q = (dword y q).rotateRight R)
    {q : Nat} (hq : q < 4) :
    cols (run (halfOps mask n) s) q = H R n (cols s q) (dw s .xmm5 q) := by
  have e1 : (BitVec.ofNat 8 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn'])]
  have e2 : (BitVec.ofNat 8 (32 - n)).toNat = 32 - n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  simp only [halfOps, run, cols, dw, xmm_vbin, xmm_vshift, ↓reduceIte, reduceCtorEq, h0, h3,
    reduceVBinOpSse]
  simp only [dword_paddd _ _ hq, dword_pxor, dword_por, hm _ q hq,
    dword_psrld _ (BitVec.ofNat 8 n) (by rw [e1]; omega_using [hn']) hq,
    dword_pslld _ (BitVec.ofNat 8 (32 - n)) (by rw [e2]; omega_using [hn]) hq, e1, e2, rotr_shifts _ hn', H]

theorem half_keeps {mask : XReg} {n : Nat} (s : State) : XF halfRegs s (run (halfOps mask n) s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4⟩ := hr
  simp only [halfOps, run, xmm_vbin, xmm_vshift, h0, h1, h2, h3, h4, ite_false]

/-! ## Diagonals -/

def diagOps : List VOp :=
  [.vpshufd .l128 .xmm0 .xmm0 0x93, .vpshufd .l128 .xmm2 .xmm2 0x39, .vpshufd .l128 .xmm3 .xmm3 0x4e]
def undiagOps : List VOp :=
  [.vpshufd .l128 .xmm0 .xmm0 0x39, .vpshufd .l128 .xmm2 .xmm2 0x93, .vpshufd .l128 .xmm3 .xmm3 0x4e]

/-- The register of row `k`. -/
def row : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | _ => .xmm3

/-- The work vector in `xmm0`–`xmm3`: word `j` is doubleword `j % 4` of row `j / 4`. -/
def words (s : State) : Spec.Blake2.Work 32 := Vector.ofFn fun j => dw s (row (j.val / 4)) (j.val % 4)

theorem words_get (s : State) (j : Nat) (hj : j < 16) : (words s)[j] = dw s (row (j / 4)) (j % 4) := by
  simp only [words, Vector.getElem_ofFn]

theorem cases_div4 {j : Nat} (hj : j < 16) : j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3 := by
  omega_using [hj]

theorem sel_93 {k : Nat} (hk : k < 4) : ((0x93 : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 3) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel_39 {k : Nat} (hk : k < 4) : ((0x39 : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 1) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem sel_4e {k : Nat} (hk : k < 4) : ((0x4e : BitVec 8).extractLsb' (2 * k) 2).toNat = (k + 2) % 4 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

theorem diag_words (s : State) : words (run diagOps s) = rotInP (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotInP_get _ _ hj, words_get _ _ (by omega_using [hj]),
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) / 4 = j / 4 by omega_using [],
    show (4 * (j / 4) + (j % 4 + j / 4 + 3) % 4) % 4 = (j % 4 + j / 4 + 3) % 4 by omega_using []]
  simp only [diagOps, run, dw]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [row, xmm_vpshufd, ↓reduceIte, reduceCtorEq, dword_shufDwords _ _ hk, sel_93 hk,
      sel_39 hk, sel_4e hk] <;> congr 1 <;> omega_using []

theorem undiag_words (s : State) : words (run undiagOps s) = rotOutP (words s) := by
  apply Vector.ext
  intro j hj
  have hk : j % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [words_get _ _ hj, rotOutP_get _ _ hj, words_get _ _ (by omega_using [hj]),
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) / 4 = j / 4 by omega_using [],
    show (4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4) % 4 = (j % 4 + 3 * (j / 4) + 1) % 4 by omega_using []]
  simp only [undiagOps, run, dw]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
    simp only [row, xmm_vpshufd, ↓reduceIte, reduceCtorEq, dword_shufDwords _ _ hk, sel_93 hk,
      sel_39 hk, sel_4e hk] <;> congr 1 <;> omega_using []

theorem diag_keeps (s : State) : XF halfRegs s (run diagOps s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [diagOps, run, xmm_vpshufd, hr.1, hr.2.2.1, hr.2.2.2.1, ite_false]

theorem undiag_keeps (s : State) : XF halfRegs s (run undiagOps s) := by
  refine XF.run fun r hr => ?_
  simp only [halfRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [undiagOps, run, xmm_vpshufd, hr.1, hr.2.2.1, hr.2.2.2.1, ite_false]

/-- The rows after `G` on each doubleword are `mixColsP` of the rows before. -/
theorem words_of_cols {s t : State} {x y : Nat → W}
    (h : ∀ q < 4, cols t q = H 8 7 (H 16 12 (cols s q) (x q)) (y q)) :
    words t = mixColsP Spec.Blake2.s x y (words s) := by
  apply Vector.ext
  intro j hj
  have g := h (j % 4) (Nat.mod_lt _ (by decide))
  rw [← mix_eq] at g
  simp only [cols] at g
  rw [words_get _ _ hj, mixColsP_get _ _ _ _ _ hj, words_get _ _ (by omega_using []),
    words_get _ _ (by omega_using []), words_get _ _ (by omega_using []), words_get _ _ (by omega_using []),
    show j % 4 / 4 = 0 by omega_using [], show (4 + j % 4) / 4 = 1 by omega_using [], show (8 + j % 4) / 4 = 2 by omega_using [],
    show (12 + j % 4) / 4 = 3 by omega_using [], Nat.mod_mod, show (4 + j % 4) % 4 = j % 4 by omega_using [],
    show (8 + j % 4) % 4 = j % 4 by omega_using [], show (12 + j % 4) % 4 = j % 4 by omega_using []]
  rcases cases_div4 hj with e | e | e | e <;> rw [e] <;> simp only [row, pick4] <;> rw [← g]

/-! ## Gathering the message words -/

/-- Where the block is, and that its 64 bytes may be read. -/
structure Blk (p : Addr) (s : State) : Prop where
  rsi : s.gpr .rsi = p
  rd : ∀ i ≤ 12, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (4 * i)) 16

theorem Blk.of_xf {rs : List XReg} {p : Addr} {s t : State} (h : Blk p s) (hf : XF rs s t) : Blk p t :=
  ⟨by rw [hf.gpr]; exact h.rsi, by rw [hf.rd, hf.wr]; exact h.rd⟩

/-- Word `j` of the block at `p`. -/
abbrev mw (m : Mem) (p : Addr) (j : Nat) : W := m.readW (p + BitVec.ofNat 64 (4 * j)) 32

theorem src_ok : ∀ j < 16, ∀ q < 4, (src j q).1 ≤ 12 ∧
    (if (src j q).2 then (src j q).1 = 4 * (j / 4) else (src j q).1 + q = j) := by decide

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, ofInt_natCast]

theorem mw_load {m : Mem} {p : Addr} {b q : Nat} (hq : q < 4) :
    dword (m.readW (p + BitVec.ofNat 64 (4 * b)) 128) q = mw m p (b + q) := by
  rw [dword_readW _ _ hq, Offset.add_add, mw, Nat.mul_add]

/-- Word `j` into doubleword `p` of `d`. -/
theorem ldw_ok {d : XReg} {j p : Nat} (hj : j < 16) (hp : p < 4) {s : State} {pa : Addr}
    (hb : Blk pa s) :
    WP isa (.block (ldw d j p)) s fun t => dw t d p = mw s.mem pa j ∧ XF [d] s t := by
  obtain ⟨hb12, he⟩ := src_ok j hj p hp
  have hj4 : j % 4 < 4 := Nat.mod_lt _ (by decide)
  unfold ldw
  generalize src j p = sp at hb12 he
  obtain ⟨b, sw⟩ := sp
  simp only at hb12 he
  have ld := hb.rd b hb12
  have hea : s.ea (at_ .rsi (4 * b)) = pa + BitVec.ofNat 64 (4 * b) := by rw [ea_at, hb.rsi]
  cases sw <;> simp only [Bool.false_eq_true, ite_true, ite_false] at he ⊢ <;>
  apply WP.of_runBlock <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.load128, hea, ld, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  · refine ⟨?_, ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩⟩
    · simp only [dw, RegUpd.xmm_setV, ↓reduceIte]
      rw [mw_load hp, he]
    · simp only [List.mem_singleton] at hr
      simp only [RegUpd.xmm_setV, hr, ite_false]
  · refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr => ?_⟩⟩
    · simp only [dw, xmm_vpshufd, RegUpd.xmm_setV, ↓reduceIte]
      rw [dword_shufDwords_bcast _ hj4 hp, mw_load hj4, he]
      exact congrArg (mw s.mem pa) (by omega_using [])
    · simp only [List.mem_singleton] at hr
      simp only [xmm_vpshufd, RegUpd.xmm_setV, hr, ite_false]

theorem pairPos_lt (j j' : Nat) : pairPos j j' < 4 := by
  unfold pairPos; split <;> decide

theorem xmm_unpck (hi : Bool) (d a b : XReg) (s : State) (r : XReg) :
    ((VOp.vbin (if hi then .vpunpckhdq else .vpunpckldq) .l128 d a b).exec s).xmm r =
      if r = d then (if hi then XBinOp.eval .punpckhdq (s.xmm a) (s.xmm b)
        else XBinOp.eval .punpckldq (s.xmm a) (s.xmm b)) else s.xmm r := by
  cases hi <;> rfl

/-- Words `j` and `j'` into doublewords 0 and 1 of `d`. -/
theorem pair_ok {d a b : XReg} (hab : a ≠ b) {j j' : Nat} (hj : j < 16)
    (hj' : j' < 16) {s : State} {pa : Addr} (hb : Blk pa s) :
    WP isa (.block (pair d a b j j')) s fun t =>
      dw t d 0 = mw s.mem pa j ∧ dw t d 1 = mw s.mem pa j' ∧ XF [d, a, b] s t := by
  unfold pair
  rw [List.append_assoc]
  apply WP.block_append
  refine (ldw_ok (d := a) hj (pairPos_lt j j') hb).mono fun t1 ⟨l1, f1⟩ => ?_
  apply WP.block_append
  refine (ldw_ok (d := b) hj' (pairPos_lt j j') (hb.of_xf f1)).mono fun t2 ⟨l2, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Option.some.injEq, exists_eq_left']
  have a2 : dw t2 a (pairPos j j') = mw s.mem pa j := by
    rw [dw_of_xf f2 (by simpa using hab), l1]
  rw [f1.mem] at l2
  refine ⟨?_, ?_, ⟨by simp [f2.gpr, f1.gpr], by simp [f2.mem, f1.mem], by simp [f2.rd, f1.rd],
    by simp [f2.wr, f1.wr], fun r hr => ?_⟩⟩
  · simp only [dw, xmm_unpck, ↓reduceIte]
    unfold pairPos at a2 l2
    cases hh : hiPair j j' <;> simp only [hh, Bool.false_eq_true, ite_false, ite_true] at a2 l2 ⊢ <;>
      simp only [dword_punpckldq, dword_punpckhdq, dword_ofDwords_0] <;> exact a2
  · simp only [dw, xmm_unpck, ↓reduceIte]
    unfold pairPos at a2 l2
    cases hh : hiPair j j' <;> simp only [hh, Bool.false_eq_true, ite_false, ite_true] at a2 l2 ⊢ <;>
      simp only [dword_punpckldq, dword_punpckhdq, dword_ofDwords_1] <;> exact l2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [xmm_unpck, ifn hr.1, f2.xmm r (by simpa using hr.2.2), f1.xmm r (by simpa using hr.2.1)]

/-- The registers `msg` writes. -/
abbrev msgRegs : List XReg := [.xmm5, .xmm6, .xmm7, .xmm8, .xmm9]

theorem msgWord_lt (r k q : Nat) : msgWord r k q < 16 := (Spec.Blake2.sigmaAt _ _).isLt

/-- Message vector `k` of round `r`, in `xmm5`. -/
theorem msg_ok (r k : Nat) {s : State} {pa : Addr} (hb : Blk pa s) :
    WP isa (.block (msg r k)) s fun t =>
      (∀ q < 4, dw t .xmm5 q = mw s.mem pa (msgWord r k q)) ∧ XF msgRegs s t := by
  unfold msg
  rw [List.append_assoc]
  apply WP.block_append
  refine (pair_ok (d := .xmm5) (a := .xmm6) (b := .xmm7) (by decide)
    (msgWord_lt r k 0) (msgWord_lt r k 1) hb).mono fun t1 ⟨p0, p1, f1⟩ => ?_
  apply WP.block_append
  refine (pair_ok (d := .xmm8) (a := .xmm8) (b := .xmm9) (by decide)
    (msgWord_lt r k 2) (msgWord_lt r k 3) (hb.of_xf f1)).mono fun t2 ⟨p2, p3, f2⟩ => ?_
  apply WP.of_runBlock
  simp only [v, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Option.some.injEq, exists_eq_left']
  rw [f1.mem] at p2 p3
  have x50 : dw t2 .xmm5 0 = mw s.mem pa (msgWord r k 0) := by
    rw [dw_of_xf f2 (by decide), p0]
  have x51 : dw t2 .xmm5 1 = mw s.mem pa (msgWord r k 1) := by
    rw [dw_of_xf f2 (by decide), p1]
  refine ⟨fun q hq => ?_, ⟨by simp [f2.gpr, f1.gpr], by simp [f2.mem, f1.mem],
    by simp [f2.rd, f1.rd], by simp [f2.wr, f1.wr], fun r hr => ?_⟩⟩
  · rcases cases4 hq with rfl | rfl | rfl | rfl <;>
      simp only [dw, xmm_vbin, ↓reduceIte, reduceVBinOpSse, dword_punpcklqdq _ _ hq, Nat.reduceLT,
        Nat.reduceSub]
    exacts [x50, x51, p2, p3]
  · simp only [msgRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [xmm_vbin, ifn hr.1, f2.xmm r (by simp [hr.2.2.2.1, hr.2.2.2.2]),
      f1.xmm r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-! ## A round -/

/-- The masks of the rotations, in `xmm14` and `xmm15`. -/
structure Masks (s : State) : Prop where
  m16 : s.xmm .xmm14 = rot16Mask
  m8 : s.xmm .xmm15 = rotr8Mask

/-- The registers a round writes. -/
abbrev roundRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9]

theorem Masks.of_xf {rs : List XReg} {s t : State} (h : Masks s) (hv : XF rs s t)
    (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Masks t :=
  ⟨(hv.xmm _ h14).trans h.m16, (hv.xmm _ h15).trans h.m8⟩

theorem cols_of_xf {rs : List XReg} {s t : State} (hv : XF rs s t) (h0 : .xmm0 ∉ rs)
    (h1 : .xmm1 ∉ rs) (h2 : .xmm2 ∉ rs) (h3 : .xmm3 ∉ rs) (q : Nat) : cols t q = cols s q := by
  simp only [cols, dw_of_xf hv h0, dw_of_xf hv h1, dw_of_xf hv h2, dw_of_xf hv h3]

theorem half1_cols {s : State} (h : Masks s) {q : Nat} (hq : q < 4) :
    cols (run (halfOps .xmm14 12) s) q = H 16 12 (cols s q) (dw s .xmm5 q) :=
  half_cols (by decide) (by decide) (by decide) (by decide)
    (fun y q hq => by rw [h.m16]; exact dword_pshufb_rotr16 y hq) hq

theorem half2_cols {s : State} (h : Masks s) {q : Nat} (hq : q < 4) :
    cols (run (halfOps .xmm15 7) s) q = H 8 7 (cols s q) (dw s .xmm5 q) :=
  half_cols (by decide) (by decide) (by decide) (by decide)
    (fun y q hq => by rw [h.m8]; exact dword_pshufb_rotr8 y hq) hq

theorem half_vf {mask : XReg} {n : Nat} (s : State) : XF roundRegs s (run (halfOps mask n) s) :=
  (half_keeps s).mono (by decide)

/-- The first half of `G` on the four doublewords, with the message vector
`x`, and the message vector `y` loaded for the second half, before `D`. -/
theorem g_ok {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) (r k : Nat) (x y : Nat → W)
    (hx : ∀ q < 4, mw s.mem pa (msgWord r k q) = x q)
    (hy : ∀ q < 4, mw s.mem pa (msgWord r (k + 1) q) = y q)
    {D : Prog isa} {Q : State → Prop}
    (hD : ∀ s3, XF roundRegs s s3 → Masks s3 → (∀ q < 4, cols s3 q = H 16 12 (cols s q) (x q)) →
      (∀ q < 4, dw s3 .xmm5 q = y q) → WP isa D s3 Q) :
    WP isa (.seq (.block (msg r k)) (.seq (.block half1) (.seq (.block (msg r (k + 1))) D))) s Q := by
  refine WP.seq ((msg_ok r k hb).mono fun s1 ⟨m1, f1⟩ => ?_)
  have hm1 := hm.of_xf f1 (by decide) (by decide)
  rw [half1, half_eq]
  refine WP.seq (block_run_ok _ _ ?_)
  generalize hs2 : run (halfOps .xmm14 12) s1 = s2
  have f2 : XF roundRegs s1 s2 := hs2 ▸ half_vf s1
  have c2 : ∀ q < 4, cols s2 q = H 16 12 (cols s1 q) (dw s1 .xmm5 q) := fun q hq =>
    hs2 ▸ half1_cols hm1 hq
  have f12 : XF roundRegs s s2 := (f1.mono (by decide)).trans f2
  refine WP.seq ((msg_ok r (k + 1) (hb.of_xf f12)).mono fun s3 ⟨m3, f3⟩ => ?_)
  refine hD s3 (f12.trans (f3.mono (by decide)))
    ((hm1.of_xf f2 (by decide) (by decide)).of_xf f3 (by decide) (by decide))
    (fun q hq => ?_) (fun q hq => ?_)
  · rw [cols_of_xf f3 (by decide) (by decide) (by decide) (by decide), c2 q hq,
      cols_of_xf f1 (by decide) (by decide) (by decide) (by decide), m1 q hq, hx q hq]
  · rw [m3 q hq, f12.mem, hy q hq]

/-- The second half of `G`, after `g_ok`. -/
theorem h2_words {s s3 : State} {x y : Nat → W} (hm : Masks s3)
    (hc : ∀ q < 4, cols s3 q = H 16 12 (cols s q) (x q)) (hy : ∀ q < 4, dw s3 .xmm5 q = y q) :
    words (run (halfOps .xmm15 7) s3) = mixColsP Spec.Blake2.s x y (words s) :=
  words_of_cols fun q hq => by rw [half2_cols hm hq, hc q hq, hy q hq]

theorem half2_diag_eq : half2 ++ diagonalize = (halfOps .xmm15 7 ++ diagOps).map .vop := by
  rw [List.map_append]; rfl

theorem half2_undiag_eq : half2 ++ undiagonalize = (halfOps .xmm15 7 ++ undiagOps).map .vop := by
  rw [List.map_append]; rfl

/-- Word `j` of the block. -/
theorem mw_block (m : Mem) (pa : Addr) (j : Nat) (hj : j < 16) :
    mw m pa j = Spec.Blake2.blockAt 32 m pa ⟨j, hj⟩ :=
  (Proof.Blake2.blockAt_word m pa j hj).symm

theorem lane_lo {k q : Nat} (hk : k < 2) : lane k q = q := by simp only [lane, hk, ite_true]
theorem lane_hi {k q : Nat} (hk : ¬ k < 2) : lane k q = (q + 3) % 4 := by
  simp only [lane, hk, ite_false]

theorem msg_word (m : Mem) (pa : Addr) (r k q : Nat) :
    mw m pa (msgWord r k q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (8 * (k / 2) + 2 * lane k q + k % 2)) :=
  mw_block m pa _ (Fin.isLt _)

theorem msg_lo (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r 0 q) = Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (2 * q)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega_using []))

theorem msg_lo1 (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r (0 + 1) q) = Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (2 * q + 1)) := by
  rw [msg_word, lane_lo (by decide)]
  exact congrArg _ (congrArg _ (by omega_using []))

theorem msg_hi (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r 2 q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega_using []))

theorem msg_hi1 (m : Mem) (pa : Addr) (r q : Nat) :
    mw m pa (msgWord r (2 + 1) q) =
      Spec.Blake2.blockAt 32 m pa (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))) := by
  rw [msg_word, lane_hi (by decide)]
  exact congrArg _ (congrArg _ (by omega_using []))

theorem diag_vf (s : State) : XF roundRegs s (run diagOps s) := (diag_keeps s).mono (by decide)
theorem undiag_vf (s : State) : XF roundRegs s (run undiagOps s) := (undiag_keeps s).mono (by decide)

/-- Round `r` on the rows in `xmm0`–`xmm3`, with the block at `rsi`. -/
theorem round_ok (r : Nat) {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) :
    WP isa (round r) s fun t =>
      words t = Spec.Blake2.round Spec.Blake2.s (Spec.Blake2.blockAt 32 s.mem pa) (words s) r ∧
      XF roundRegs s t ∧ Masks t := by
  unfold round
  refine g_ok hb hm r 0 _ _ (fun q _ => msg_lo _ _ r q) (fun q _ => msg_lo1 _ _ r q)
    fun s3 f3 hm3 hc3 hy3 => ?_
  rw [half2_diag_eq]
  refine WP.seq (block_run_ok _ _ ?_)
  generalize hs4 : run (halfOps .xmm15 7 ++ diagOps) s3 = s4
  have f4 : XF roundRegs s s4 := by
    rw [← hs4, run_append]; exact (f3.trans (half_vf s3)).trans (diag_vf _)
  have hm4 : Masks s4 := hm.of_xf f4 (by decide) (by decide)
  have w4 : words s4 = rotInP (mixColsP Spec.Blake2.s
      (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (2 * q)))
      (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (2 * q + 1))) (words s)) := by
    rw [← hs4, run_append, diag_words, h2_words hm3 hc3 hy3]
  refine g_ok (hb.of_xf f4) hm4 r 2
    (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (8 + 2 * ((q + 3) % 4))))
    (fun q => Spec.Blake2.blockAt 32 s.mem pa (Spec.Blake2.sigmaAt r (9 + 2 * ((q + 3) % 4))))
    (fun q _ => by rw [f4.mem]; exact msg_hi _ _ r q) (fun q _ => by rw [f4.mem]; exact msg_hi1 _ _ r q)
    fun s7 f7 hm7 hc7 hy7 => ?_
  rw [half2_undiag_eq]
  refine block_run_ok _ _ ⟨?_, ?_, ?_⟩
  · rw [run_append, undiag_words, h2_words hm7 hc7 hy7, w4, round_colsP]
  · rw [run_append]; exact ((f4.trans f7).trans (half_vf s7)).trans (undiag_vf _)
  · rw [run_append]
    exact hm.of_xf (((f4.trans f7).trans (half_vf s7)).trans (undiag_vf _)) (by decide) (by decide)

/-- Rounds `0 … n-1`. -/
theorem rounds_ok (n : Nat) {s : State} {pa : Addr} (hb : Blk pa s) (hm : Masks s) :
    WP isa (rounds n) s fun t =>
      words t = (List.range n).foldl (Spec.Blake2.round Spec.Blake2.s
        (Spec.Blake2.blockAt 32 s.mem pa)) (words s) ∧ XF roundRegs s t ∧ Masks t := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, XF.refl _ _, hm⟩
  | succ n ih =>
    refine WP.seq (ih.mono fun t ⟨wt, ft, mt⟩ => ?_)
    refine (round_ok n (hb.of_xf ft) mt).mono fun u ⟨wu, fu, mu⟩ => ⟨?_, ft.trans fu, mu⟩
    rw [wu, wt, ft.mem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end VG.Proof.Blake2.X86_64.Avx

end

end

/-!
# BLAKE2s compression function on x86-64 with AVX

The proof that `Impl.Blake2.X86_64.Avx.compress` meets `compressX86_64 s`
(`Proof/Blake2/X86_64/Contract.lean`), as the scalar code does
(`Proof/Blake2/X86_64/Compress.lean`, whose description of the precondition
and of the work vector before the rounds, `V0`, this proof shares): the
masks and the IV in registers (`setup_ok`), then for each block the work
vector (`init_ok`), the rounds (`rounds_ok`), the XOR into the state
(`finish_ok`) and the next block (`advance_ok`). Constant time is checked
by evaluation.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64
open VG.Impl.Blake2.X86_64.Avx
open VG.Impl.Blake2.X86_64 (at_)
open VG.Proof.Blake2.X86_64 (Pre pre_of stA bpA nb t₀ fl stR blR H₀ blkAddr V0 V0_get F_eq flagW
  zf_last τ₀ agree₀ satState lo32_ofNat hi32_ofNat)

/-- Word `q` of BLAKE2s's IV. -/
def ivAt (q : Nat) : W := if h : q < 8 then Spec.Blake2.s.IV[q] else 0

/-- The masks and the IV, in their registers. -/
structure Consts (s : State) : Prop where
  masks : Masks s
  iv0 : ∀ q < 4, dword (s.xmm .xmm11) q = ivAt q
  iv1 : ∀ q < 4, dword (s.xmm .xmm12) q = ivAt (4 + q)

theorem Consts.of_xf {rs : List XReg} {s t : State} (h : Consts s) (hv : XF rs s t)
    (h11 : .xmm11 ∉ rs) (h12 : .xmm12 ∉ rs) (h14 : .xmm14 ∉ rs) (h15 : .xmm15 ∉ rs) : Consts t :=
  ⟨h.masks.of_xf hv h14 h15, fun q hq => (dw_of_xf hv h11 q).trans (h.iv0 q hq),
    fun q hq => (dw_of_xf hv h12 q).trans (h.iv1 q hq)⟩

/-! ## Values of 128 bits made of two quadwords -/

theorem qword_app0 (a b : BitVec 64) : qword (a ++ b) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem unpck_app (lo hi : BitVec 64) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ lo) ((0 : BitVec 64) ++ hi) = hi ++ lo := by
  simp only [reduceXBinOpEval, qword_app0]

theorem dword_app (a b : BitVec 64) {q : Nat} (hq : q < 4) :
    dword (a ++ b) q = if q < 2 then b.extractLsb' (32 * q) 32 else a.extractLsb' (32 * (q - 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases cases4 hq with rfl | rfl | rfl | rfl <;>
  · simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMul]
    split <;> first | rfl | omega | (exact congrArg _ (by omega_using []))

/-! ## The set-up -/

/-- `d := (lo, hi)`, through `rax` and `xmm4`. -/
theorem pair64_ok {d : XReg} (hd : d ≠ .xmm4) (lo hi : BitVec 64) (s : State) :
    WP isa (.block (pair64 d lo hi)) s fun u =>
      u.xmm d = hi ++ lo ∧ (∀ r, r ≠ .rax → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr ∧ (∀ r, r ≠ d → r ≠ .xmm4 → u.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [pair64, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
  · simp only [xmm_vbin, xmm_vmovq, ↓reduceIte, hd, RegUpd.xmm_setReg,
      RegUpd.gpr_setReg_self, VBinOp.sse]
    exact unpck_app lo hi
  · simp only [VOp.exec_gpr, RegUpd.gpr_setReg, hr, ite_false]
  · simp only [xmm_vbin, xmm_vmovq, h1, h2, ite_false, RegUpd.xmm_setReg]

theorem mask16_eq : (rot16Hi ++ rot16Lo : BitVec 128) = rot16Mask := by decide
theorem mask8_eq : (rotr8Hi ++ rotr8Lo : BitVec 128) = rotr8Mask := by decide

theorem iv0_eq : ∀ q < 4, dword (ivPair 2 ++ ivPair 0 : BitVec 128) q = ivAt q := by decide
theorem iv1_eq : ∀ q < 4, dword (ivPair 6 ++ ivPair 4 : BitVec 128) q = ivAt (4 + q) := by decide

theorem setup_eq : setup = ([.mov32 .r8 (.reg .r8)] : List Instr) ++
    (pair64 .xmm14 rot16Lo rot16Hi ++ (pair64 .xmm15 rotr8Lo rotr8Hi ++
      (pair64 .xmm11 (ivPair 0) (ivPair 2) ++ (pair64 .xmm12 (ivPair 4) (ivPair 6) ++
        ([.alu .test .r8 (.reg .r8)] : List Instr))))) := by
  simp only [setup, List.append_assoc]

/-- What a block of general-purpose instructions leaves: memory, permissions
and vector registers. -/
structure GF (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : t.xmm = s.xmm

theorem GF.trans {s t u : State} (h : GF s t) (h' : GF t u) : GF s u :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.xmm.trans h.xmm⟩

theorem Consts.of_gf {s t : State} (h : Consts s) (hg : GF s t) : Consts t :=
  ⟨⟨by rw [hg.xmm]; exact h.masks.m16, by rw [hg.xmm]; exact h.masks.m8⟩,
    fun q hq => by rw [hg.xmm]; exact h.iv0 q hq,
    fun q hq => by rw [hg.xmm]; exact h.iv1 q hq⟩

theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧
      t.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (((s.gpr .r8).setWidth 32).setWidth 64 &&& ((s.gpr .r8).setWidth 32).setWidth 64 == 0) := by
  rw [setup_eq]
  apply WP.block_append
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  generalize hs0 : s.setReg .r8 (((s.gpr .r8).setWidth 32).setWidth 64) = s0
  have g0 : ∀ r, r ≠ .r8 → s0.gpr r = s.gpr r := fun r hr => by
    rw [← hs0, RegUpd.gpr_setReg, ifn hr]
  have r80 : s0.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := by
    rw [← hs0, RegUpd.gpr_setReg_self]
  have mem0 : s0.mem = s.mem := by rw [← hs0]; rfl
  have rd0 : s0.rd = s.rd := by rw [← hs0]; rfl
  have wr0 : s0.wr = s.wr := by rw [← hs0]; rfl
  apply WP.block_append
  refine (pair64_ok (d := .xmm14) (by decide) _ _ s0).mono fun u1 ⟨x1, g1, m1, rd1, wr1, k1⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm15) (by decide) _ _ u1).mono fun u2 ⟨x2, g2, m2, rd2, wr2, k2⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm11) (by decide) _ _ u2).mono fun u3 ⟨x3, g3, m3, rd3, wr3, k3⟩ => ?_
  apply WP.block_append
  refine (pair64_ok (d := .xmm12) (by decide) _ _ u3).mono fun u4 ⟨x4, g4, m4, rd4, wr4, k4⟩ => ?_
  have c4 : Consts u4 := by
    refine ⟨⟨?_, ?_⟩, fun q hq => ?_, fun q hq => ?_⟩
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide),
        x1, mask16_eq]
    · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), x2, mask8_eq]
    · rw [k4 _ (by decide) (by decide), x3]; exact iv0_eq q hq
    · rw [x4]; exact iv1_eq q hq
  have g4' : ∀ r, r ≠ .rax → u4.gpr r = s0.gpr r := fun r hr =>
    (g4 r hr).trans ((g3 r hr).trans ((g2 r hr).trans (g1 r hr)))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e8 : u4.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := (g4' _ (by decide)).trans r80
  refine ⟨c4.of_gf ⟨rfl, rfl, rfl, rfl⟩, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, e8]
  · exact (g4' r h1).trans (g0 r h2)
  · rw [m4, m3, m2, m1, mem0]
  · rw [rd4, rd3, rd2, rd1, rd0]
  · rw [wr4, wr3, wr2, wr1, wr0]

theorem flag_ok {s₀ s₁ : State} (h8 : s₁.gpr .r8 = ((s₀.gpr .r8).setWidth 32).setWidth 64)
    (hzf : s₁.zf = some (((s₀.gpr .r8).setWidth 32).setWidth 64 &&&
      ((s₀.gpr .r8).setWidth 32).setWidth 64 == 0)) :
    WP isa flag s₁ fun s₂ => s₂.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64 ∧
      s₂.zf = some (s₁.gpr .rdx &&& s₁.gpr .rdx == 0) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧
      GF s₁ s₂ := by
  refine WP.seq (WP.mono (Q := fun s : State => s.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64 ∧
      (∀ r, r ≠ .r8 → s.gpr r = s₁.gpr r) ∧ GF s₁ s) ?_ fun s h => ?_)
  · refine WP.ite (!(fl s₀)) (by simp only [eval, hzf, zf_last]) (fun h => ?_) (fun h => ?_)
    · have hf : fl s₀ = false := by simpa using h
      refine WP.block_nil ⟨?_, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
      have hx : (s₀.gpr .r8).setWidth 32 = 0 := by simpa [fl] using hf
      rw [h8, hx, hf]; rfl
    · have hf : fl s₀ = true := by simpa using h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
        RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left', hf]
      exact ⟨by decide, fun r h => by simp only [h, ite_false], rfl, rfl, rfl, rfl⟩
  · obtain ⟨h8', hg, hf⟩ := h
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, hg .rdx (by decide), Option.bind_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨h8', trivial, hg, hf.trans ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## The work vector -/

/-- The fourth row's counter and flag words, `(t₀, t₁, f, 0)`. -/
def ctr (T : Nat) (f : Bool) (q : Nat) : W :=
  if q = 0 then BitVec.ofNat 32 T else if q = 1 then BitVec.ofNat 32 (T / 2 ^ 32)
  else if q = 2 then flagW 32 f else 0

theorem ctr_dword (T : Nat) (f : Bool) {q : Nat} (hq : q < 4) :
    dword ((flagW 32 f).setWidth 64 ++ BitVec.ofNat 64 T) q = ctr T f q := by
  rw [dword_app _ _ hq]
  rcases cases4 hq with rfl | rfl | rfl | rfl
  · simp only [Nat.reduceLT, ↓reduceIte, Nat.mul_zero, ctr]
    exact lo32_ofNat T
  · simp only [Nat.reduceLT, ↓reduceIte, Nat.mul_one, ctr, Nat.one_ne_zero]
    exact hi32_ofNat T
  · simp only [Nat.reduceLT, ↓reduceIte, ctr, Nat.reduceSub, Nat.mul_zero, Nat.reduceEqDiff]
    cases f <;> decide
  · simp only [Nat.reduceLT, ↓reduceIte, ctr, Nat.reduceSub, Nat.mul_one, Nat.reduceEqDiff]
    cases f <;> decide

/-- A 16-byte load, word by word. -/
theorem mw_load16 (m : Mem) (st : Addr) {e q : Nat} (hq : q < 4) :
    dword (m.readW (st + BitVec.ofNat 64 e) 128) q = m.readW (st + BitVec.ofNat 64 (e + 4 * q)) 32 := by
  rw [dword_readW _ _ hq, Offset.add_add]

theorem init_ok {s : State} {st : Addr} {T : Nat} {f : Bool} (hdi : s.gpr .rdi = st)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 T) (h8 : s.gpr .r8 = (flagW 32 f).setWidth 64)
    (hc : Consts s)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 16) 16) :
    WP isa (.block init) s fun t =>
      words t = V0 Spec.Blake2.s (Spec.Blake2.stateAt 32 s.mem st) T f ∧
      XF [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm13] s t := by
  apply WP.of_runBlock
  simp only [init, v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at, hdi,
    hin0, hin1, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨by simp, by simp, by simp, by simp, fun r hr => ?_⟩⟩
  · apply Vector.ext; intro j hj
    rw [words_get _ _ hj, V0_get _ _ _ _ _ hj]
    have hq : j % 4 < 4 := Nat.mod_lt _ (by decide)
    rcases cases_div4 hj with e | e | e | e <;> rw [e] <;>
      simp only [row, dw, xmm_vbin, xmm_vmovq, xmm_vmovdqa, RegUpd.xmm_setV, VOp.exec_gpr,
        State.setV_gpr, ↓reduceIte, reduceCtorEq, VBinOp.sse]
    · rw [mw_load16 _ _ hq, dite_eq_left_of_eq_true (eq_true (by omega_using [e])), Spec.Blake2.stateAt,
        Vector.getElem_ofFn]
      exact congrArg (fun x => s.mem.readW (st + BitVec.ofNat 64 x) 32) (by dsimp only; omega_using [e])
    · rw [mw_load16 _ _ hq, dite_eq_left_of_eq_true (eq_true (by omega_using [e])), Spec.Blake2.stateAt,
        Vector.getElem_ofFn]
      exact congrArg (fun x => s.mem.readW (st + BitVec.ofNat 64 x) 32) (by dsimp only; omega_using [e])
    · rw [hc.iv0 _ hq, dite_eq_right_of_eq_false (eq_false (by omega_using [e])), ifn (by omega_using [e]),
        ifn (by omega_using [e]), ifn (by omega_using [e]), ivAt, dite_eq_left_of_eq_true (eq_true (by omega_using []))]
      simp only [show j % 4 = j - 8 by omega_using [e]]
    · rw [dword_pxor, unpck_app, hcx, h8, ctr_dword _ _ hq, hc.iv1 _ hq,
        dite_eq_right_of_eq_false (eq_false (by omega_using [e]))]
      have : j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega_using [e]
      rcases this with rfl | rfl | rfl | rfl <;>
        simp only [ivAt, ctr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, ↓reduceDIte,
          ↓reduceIte, Nat.reduceEqDiff]
      exact BitVec.xor_zero
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h13⟩ := hr
    simp only [xmm_vbin, xmm_vmovq, xmm_vmovdqa, RegUpd.xmm_setV, h0, h1, h2, h3, h4, h13,
      ite_false]

/-! ## The new state -/

/-- A read of a word of the state after a 16-byte store into it. -/
theorem read_write128 (m : Mem) (st : Addr) {d e : Nat} (hd : d + 4 ≤ 32) (he : e + 16 ≤ 32)
    (h4 : d % 4 = 0) (he4 : e % 4 = 0) (v : BitVec 128) :
    (m.writeW (st + BitVec.ofNat 64 e) v).readW (st + BitVec.ofNat 64 d) 32 =
      if e ≤ d ∧ d < e + 16 then dword v ((d - e) / 4) else m.readW (st + BitVec.ofNat 64 d) 32 := by
  split
  · rename_i h
    rw [show st + BitVec.ofNat 64 d = st + BitVec.ofNat 64 e + BitVec.ofNat 64 (4 * ((d - e) / 4)) from
      (Offset.add_add_eq st (by omega_using [h4, he4, h])).symm]
    refine (readW_writeW_inside _ _ v (k := 4 * ((d - e) / 4)) (n := 4) (by omega_using [h]) (by decide)).trans ?_
    rw [dword_eq, show 8 * (4 * ((d - e) / 4)) = 32 * ((d - e) / 4) by omega_using []]
  · exact VG.X86_64.readW_writeW_off m st v (n := 4) (by omega_using [hd]) (by omega_using [he]) (by omega_arith)

theorem finish_ok {s : State} {st : Addr} (hdi : s.gpr .rdi = st)
    (hin0 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 0) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 16) 16)
    (hout0 : InRegions s.wr (st + BitVec.ofNat 64 0) 16)
    (hout1 : InRegions s.wr (st + BitVec.ofNat 64 16) 16) :
    WP isa (.block finish) s fun t =>
      (∀ j (hj : j < 8), t.mem.readW (st + BitVec.ofNat 64 (4 * j)) 32 =
        s.mem.readW (st + BitVec.ofNat 64 (4 * j)) 32 ^^^ (words s)[j]'(Nat.lt_trans hj (by decide)) ^^^
          (words s)[j + 8]'(Nat.add_lt_add_right hj 8)) ∧
      Frame [⟨st, 32⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm4 → t.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [finish, v, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128,
    State.store128_eq, ea_at, hdi, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, VOp.exec_mem,
    xmm_vbin, RegUpd.xmm_setV, State.setMem_xmm, VBinOp.sse, ↓reduceIte, reduceCtorEq,
    State.setV_gpr, State.setV_rd, State.setV_wr, State.setV_mem, State.setMem_gpr,
    State.setMem_rd, State.setMem_wr, State.setMem_mem, hin0, hin1, hout0, hout1,
    Option.map_some, Option.some.injEq, exists_eq_left']
  have sep : (s.mem.writeW (st + 0#64)
      (XBinOp.eval .pxor (XBinOp.eval .pxor (s.xmm .xmm0) (s.xmm .xmm2))
        (s.mem.readW (st + 0#64) 128))).readW (st + 16#64) 128 =
      s.mem.readW (st + 16#64) 128 :=
    VG.X86_64.readW_writeW_off _ st _ (d := 16) (e := 0) (n := 16) (by omega_using []) (by omega_using []) (by omega_using [])
  refine ⟨fun j hj => ?_, ?_, trivial, trivial, trivial, fun r h0 h1 h4 => ?_⟩
  · rw [read_write128 _ st (d := 4 * j) (e := 16) (by omega_using [hj]) (by omega_using []) (by omega_using []) (by omega_using [])]
    by_cases hj4 : j < 4
    · rw [ifn (by omega_using [hj4]), read_write128 _ st (d := 4 * j) (e := 0) (by omega_using [hj]) (by omega_using []) (by omega_using [])
        (by omega_using []), ifp (by omega_using [hj4]), Nat.sub_zero, show 4 * j / 4 = j by omega_using [],
        words_get _ _ (by omega_using [hj]), words_get _ _ (by omega_using [hj]), show j / 4 = 0 by omega_using [hj4],
        show (j + 8) / 4 = 2 by omega_using [hj4], show j % 4 = j by omega_using [hj4], show (j + 8) % 4 = j by omega_using [hj4]]
      simp only [row, dw, dword_pxor]
      rw [mw_load16 _ _ hj4, Nat.zero_add, BitVec.xor_comm _ (s.mem.readW _ 32), BitVec.xor_assoc]
    · rw [ifp (by omega_using [hj, hj4]), show (4 * j - 16) / 4 = j - 4 by omega_using [],
        words_get _ _ (by omega_using [hj]), words_get _ _ (by omega_using [hj]), show j / 4 = 1 by omega_using [hj, hj4],
        show (j + 8) / 4 = 3 by omega_using [hj, hj4], show j % 4 = j - 4 by omega_using [hj, hj4], show (j + 8) % 4 = j - 4 by omega_using [hj, hj4]]
      simp only [row, dw, dword_pxor]
      rw [sep, mw_load16 _ _ (by omega_using [hj]), show 16 + 4 * (j - 4) = 4 * j by omega_using [hj4],
        BitVec.xor_comm _ (s.mem.readW _ 32), BitVec.xor_assoc]
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains_base st (by decide) (by decide))
  · simp only [h0, h1, h4, ite_false]

/-! ## The next block -/

theorem advance_ok {s : State} {T : Nat} (hcx : s.gpr .rcx = BitVec.ofNat 64 T) :
    WP isa (.block advance) s fun t => t.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 64 ∧
      t.gpr .rcx = BitVec.ofNat 64 (T + 64) ∧
      t.gpr .rdx = s.gpr .rdx - 1 ∧ t.zf = some (s.gpr .rdx - 1 == 0) ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ GF s t := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, e64, e1,
    ↓reduceIte, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left', hcx]
  refine ⟨trivial, ?_, trivial, trivial, fun r h1 h2 h3 => ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.ofNat_add_ofNat]
  · simp only [h1, h2, h3, ite_false]

/-! ## One block -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = blkAddr 32 s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes 32)
  r8 : s.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64
  keep : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rax → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR 32 s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt 32 s.mem (stA s₀) =
    Spec.Blake2.compressBlocks Spec.Blake2.s (H₀ 32 s₀) s₀.mem (bpA s₀) i (t₀ s₀) (fl s₀)
  consts : Consts s

namespace PreX
variable {s₀ : State} (hp : Pre 32 s₀)
include hp

theorem st_in {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions (s₀.rd ++ s₀.wr) (stA s₀ + BitVec.ofNat 64 d) 16 :=
  ⟨stR 32 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega_using [hd])⟩

theorem st_out {d : Nat} (hd : d + 16 ≤ 32) : InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 d) 16 :=
  ⟨stR 32 s₀, by simp [hp.wr], Offset.contains_base _ (by simpa using hd) (by omega_using [hd])⟩

theorem blk_in {i : Nat} (hi : i < nb s₀) {k : Nat} (hk : k ≤ 12) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr 32 s₀ i + BitVec.ofNat 64 (4 * k)) 16 := by
  have := hp.nb_lt (.inr rfl)
  refine ⟨blR 32 s₀, by simp [hp.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
  rw [hb] at this ⊢
  exact Offset.contains_base _ (by rw [hb]; omega_using [hi, hk]) (by omega_using [hi, hk, this])

/-- The block is not in the state. -/
theorem blk_frame {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [stR 32 s₀] s₀.mem m) :
    Spec.Blake2.blockAt 32 m (blkAddr 32 s₀ i) = Spec.Blake2.blockAt 32 s₀.mem (blkAddr 32 s₀ i) := by
  have := hp.nb_lt (.inr rfl)
  funext j
  rw [show j = ⟨j.val, j.isLt⟩ from rfl, Proof.Blake2.blockAt_word _ _ _ j.isLt,
    Proof.Blake2.blockAt_word _ _ _ j.isLt]
  refine hf.readW (r := blR 32 s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [blkAddr, Offset.add_add]
    have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
    rw [hb] at this ⊢
    exact Offset.contains_base _ (by rw [hb]; omega_using [hi]) (by omega_using [hi, this])
  · simp only [List.mem_singleton] at hr
    subst hr; exact hp.bl_st

end PreX

theorem body_ok {s₀ : State} (hp : Pre 32 s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hc : Common s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) := by
  have hdi : s.gpr .rdi = stA s₀ := hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hc.rd, hc.wr]
  refine WP.seq ((init_ok hdi hc.rcx hc.r8 hc.consts (hrw ▸ PreX.st_in hp (by decide))
    (hrw ▸ PreX.st_in hp (by decide))).mono fun t1 ⟨w1, f1⟩ => ?_)
  have c1 := hc.consts.of_xf f1 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ((rounds_ok 10 (pa := blkAddr 32 s₀ i)
    ⟨by rw [f1.gpr]; exact hc.rsi, fun k hk => by rw [f1.rd, f1.wr, hrw]; exact PreX.blk_in hp hi hk⟩
    c1.masks).mono fun t2 ⟨w2, f2, m2⟩ => ?_)
  have c2 := c1.of_xf f2 (by decide) (by decide) (by decide) (by decide)
  apply WP.block_append
  refine (finish_ok (st := stA s₀) (by rw [f2.gpr, f1.gpr]; exact hdi)
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreX.st_in hp (by decide))
    (by rw [f2.rd, f2.wr, f1.rd, f1.wr, hrw]; exact PreX.st_in hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreX.st_out hp (by decide))
    (by rw [f2.wr, f1.wr, hc.wr]; exact PreX.st_out hp (by decide))).mono
    fun t3 ⟨x3, fr3, g3, rd3, wr3, l3⟩ => ?_
  have gs : ∀ r, t3.gpr r = s.gpr r := fun r => by rw [g3, f2.gpr, f1.gpr]
  refine (advance_ok (T := t₀ s₀ + i * Spec.Blake2.blockBytes 32) (by rw [gs]; exact hc.rcx)).mono fun t4 ⟨si4, cx4, dx4, zf4, g4, gf4⟩ => ?_
  have hb : Spec.Blake2.blockBytes 32 = 64 := rfl
  have dx : t4.gpr .rdx = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [dx4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]
  have mem2 : t2.mem = s.mem := f2.mem.trans f1.mem
  refine ⟨⟨?_, dx, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [si4, gs, hc.rsi]; exact Proof.Blake2.X86_64.blkAddr_succ (w := 32) s₀ i
  · rw [cx4, hb]; congr 1; omega_using []
  · rw [g4 _ (by decide) (by decide) (by decide), gs]; exact hc.r8
  · rw [g4 _ h1 h2 h4, gs]; exact hc.keep r h1 h2 h3 h4 h5
  · rw [gf4.rd, rd3, f2.rd, f1.rd, hc.rd]
  · rw [gf4.wr, wr3, f2.wr, f1.wr, hc.wr]
  · rw [gf4.mem]
    exact hc.frame.trans (by rw [← mem2]; exact fr3)
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, F_eq]
    apply Vector.ext; intro j hj
    rw [Vector.getElem_ofFn, Spec.Blake2.stateAt, Vector.getElem_ofFn, gf4.mem]
    simp only [Nat.reduceDiv]
    rw [x3 j hj, mem2, w2, w1, f1.mem, PreX.blk_frame hp hi hc.frame,
      show Spec.Blake2.s.r = 10 from rfl, Fin.getElem_fin, Fin.getElem_fin]
    have hst : (Spec.Blake2.stateAt 32 s.mem (stA s₀))[j] =
        s.mem.readW (stA s₀ + BitVec.ofNat 64 (4 * j)) 32 := by
      simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, Nat.reduceDiv]
    rw [hst]
  · refine Consts.of_gf ⟨⟨?_, ?_⟩, fun q hq => ?_, fun q hq => ?_⟩ gf4
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.masks.m16
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.masks.m8
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.iv0 q hq
    · rw [l3 _ (by decide) (by decide) (by decide)]; exact c2.iv1 q hq
  · rw [zf4, gs, hc.rdx, Proof.Blake2.X86_64.n_succ hi]

/-! ## The whole function -/

theorem common0 {s₀ s₂ : State} (h8 : s₂.gpr .r8 = (flagW 32 (fl s₀)).setWidth 64)
    (hg : ∀ r, r ≠ .rax → r ≠ .r8 → s₂.gpr r = s₀.gpr r)
    (hm : s₂.mem = s₀.mem) (hrd : s₂.rd = s₀.rd) (hwr : s₂.wr = s₀.wr) (hc : Consts s₂) :
    Common s₀ 0 s₂ := by
  refine ⟨?_, ?_, ?_, h8, fun r _ _ h3 _ h5 => hg r h3 h5, hrd, hwr, ?_, ?_, hc⟩
  · rw [hg _ (by decide) (by decide), blkAddr, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [hg _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hg _ (by decide) (by decide), Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hm]; exact Frame.refl _ _
  · rw [Proof.Blake2.compressBlocks_zero, hm]

theorem correct {s₀ : State} (hp : Pre 32 s₀) :
    WP isa compress s₀ fun s' =>
      gprPreserved s₀ s' ∧ (compressX86_64 Spec.Blake2.s).post s₀ s' := by
  refine WP.seq ((setup_ok s₀).mono fun s₁ ⟨c1, r81, g1, m1, rd1, wr1, zf1⟩ => ?_)
  refine WP.seq ((flag_ok (s₀ := s₀) r81 zf1).mono fun s₂ ⟨r82, zf2, g2, f2⟩ => ?_)
  have hc₀ : Common s₀ 0 s₂ := common0 r82
    (fun r h1 h2 => (g2 r h2).trans (g1 r h1 h2))
    (f2.mem.trans m1) (f2.rd.trans rd1) (f2.wr.trans wr1) (c1.of_gf f2)
  have hdx : s₁.gpr .rdx = s₀.gpr .rdx := g1 _ (by decide) (by decide)
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_
  · refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp only [eval, zf2, hdx])
      (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp only [nb, h]; rfl
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Common s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
          (isa.eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
          (isa.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hc⟩
        refine WP.mono (body_ok hp hi hc) fun s' ⟨hc', hz⟩ => ?_
        by_cases hlast : i + 1 = nb s₀
        · left
          refine ⟨?_, hlast ▸ hc'⟩
          simp only [eval, hz, ← hlast, Nat.sub_self, Option.map_some]; rfl
        · right
          have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
          refine ⟨?_, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hlast], hc'⟩
          have h0 : (BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0) = false := by
            rw [beq_eq_false_iff_ne]
            intro h'
            have h'' := congrArg BitVec.toNat h'
            rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (s₀.gpr .rdx).isLt)] at h''
            exact hne (h''.trans rfl)
          simp only [eval, hz, h0, Option.map_some]; rfl
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₂ ⟨0, rfl, hpos, hc₀⟩
  · refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hc.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
    · exact hc.state

/-! ## Results -/

theorem compress_correct (s : State) (hs : (compressX86_64 Spec.Blake2.s).pre s) :
    ∃ t s', Exec isa Impl.Blake2.X86_64.Avx.compress s t s' ∧ abiPreserved s s' ∧
      (compressX86_64 Spec.Blake2.s).post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem compress_ct : ConstantTime isa (compressX86_64 Spec.Blake2.s).pre
    (compressX86_64 Spec.Blake2.s).pub Impl.Blake2.X86_64.Avx.compress :=
  VG.Taint.constantTime (A := taint) (τ₀ 32) (fun _ _ h₁ h₂ hp => agree₀ (.inr rfl) h₁ h₂ hp)
    (by taint_decide)

theorem compress_verified :
    Verified X86_64.target Impl.Blake2.X86_64.Avx.compress (Proof.Blake2.compressSContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct (by
    sig_implies [Proof.Blake2.compressSContract, Proof.Blake2.compressSSig, compressX86_64,
      X86_64.abi, X86_64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 32)

end VG.Proof.Blake2.X86_64.Avx

end

end

/-!
# BLAKE2s on x86-64 with AVX: the streaming functions

`update` and `finalize` calling `vg_blake2s_compress_avx` (`avx`): what
their proofs of correctness need of it (`callee`), and their constant time,
by the same taint analysis as with the scalar compression function
(`Proof/Blake2/X86_64/Stream/CT.lean`), of the code with this callee.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86_64.Avx

open VG VG.X86_64 VG.Spec.Blake2
open VG.Proof.Blake2.X86_64.Stream (CalleeOk τUpdate τFinalize update_agree finalize_agree okS)

theorem callee : CalleeOk s Impl.Blake2.X86_64.Avx.compress :=
  CalleeOk.of_verified compress_correct (by lit_decide) (by lit_decide)

theorem update_ct : ConstantTime isa (updateX86_64 s).pre (updateX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.update s avx) :=
  VG.Taint.constantTime (A := taint) (τUpdate 32) (fun _ _ h₁ h₂ hp => update_agree okS h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86_64 s).pre (finalizeX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.finalize s avx) :=
  VG.Taint.constantTime (A := taint) (τFinalize 32)
    (fun _ _ h₁ h₂ hp => finalize_agree okS h₁ h₂ hp) (by taint_decide)

end VG.Proof.Blake2.X86_64.Avx
