import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Tail

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: the rounds

Lane `l` (128 bits) of the registers `zmm0 … zmm7` holds the words of block
`l` of each set: row `r` of the first set's in `zmm r`, of the second's in
`zmm (4 + r)`. As words of the lane, word `4 r + q` is doubleword `q` of
register `r` (`W`), so words `0 … 15` are the first set's state and `16 …
31` the second's. Every instruction of the rounds acts on each lane as a
step on its words (`hstep`): the column round on rows, and the rotations of
the rows that make the diagonals columns. A double round on the words is
proven, once, to be `innerBlock` on each set, by comparing terms; then on
the four lanes of the registers.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Spec.ChaCha20 (Word qround innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (xidx xidx_lt xidx_inj div4_lt mod4_lt sel2 sel2_eq sel2_lt Same
  Same.trans)

/-- The words of a lane: word `4 r + q` in doubleword `q` of register `r`. -/
abbrev W := Nat → Word

/-- The instructions of the rounds. -/
inductive HI
  | add (d a b : XReg) | xor (d a b : XReg) | rol (d a : XReg) (n : BitVec 8)
  | shuf (d a : XReg) (o : BitVec 8)

def HI.instr : HI → Instr
  | .add d a b => z .vpaddd d a b
  | .xor d a b => z .vpxord d a b
  | .rol d a n => .zop (.vprold d a n)
  | .shuf d a o => .zop (.vpshufd d a o)

/-- `w` with row `d` replaced by `f`. -/
def setRow {α : Type} (w : Nat → α) (d : Nat) (f : Nat → α) : Nat → α :=
  fun k => if k / 4 = d then f (k % 4) else w k

/-- An instruction of the rounds, on the words of a lane. -/
def hstep (w : W) : HI → W
  | .add d a b => setRow w (xidx d) fun q => w (4 * xidx a + q) + w (4 * xidx b + q)
  | .xor d a b => setRow w (xidx d) fun q => w (4 * xidx a + q) ^^^ w (4 * xidx b + q)
  | .rol d a n => setRow w (xidx d) fun q => (w (4 * xidx a + q)).rotateLeft (n.toNat % 32)
  | .shuf d a o => setRow w (xidx d) fun q => w (4 * xidx a + sel2 o.toNat q)

/-- The registers hold the words of the four lanes `ws 0 … ws 3`. -/
def HH (ws : Nat → W) (s : State) : Prop :=
  ∀ r l q, l < 4 → q < 4 → dword (s.zlane r l) q = ws l (4 * xidx r + q)

theorem setRow_row {α : Type} (w : Nat → α) (r d : Nat) (f : Nat → α) {q : Nat} (hq : q < 4) :
    setRow w d f (4 * r + q) = if r = d then f q else w (4 * r + q) := by
  simp only [setRow, show (4 * r + q) / 4 = r by omega, show (4 * r + q) % 4 = q by omega]

/-- One instruction of the rounds, on the four lanes. -/
theorem step_ok (i : HI) {ws : Nat → W} {s : State} (h : HH ws s) :
    ∃ s', exec i.instr s = some s' ∧ HH (fun l => hstep (ws l) i) s' ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | add d a b =>
    refine ⟨_, rfl, fun r l q hl hq => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zlane_zbin _ _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
    split
    · simp only [ZBinOp.sse, dword_paddd _ _ hq]; rw [h a l q hl hq, h b l q hl hq]
    · exact h r l q hl hq
  | xor d a b =>
    refine ⟨_, rfl, fun r l q hl hq => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zlane_zbin _ _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
    split
    · simp only [ZBinOp.sse, dword_pxor]; rw [h a l q hl hq, h b l q hl hq]
    · exact h r l q hl hq
  | rol d a n =>
    refine ⟨_, rfl, fun r l q hl hq => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zlane_vprold _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
    split
    · rw [dword_rolDwords _ _ hq, h a l q hl hq]
    · exact h r l q hl hq
  | shuf d a o =>
    refine ⟨_, rfl, fun r l q hl hq => ?_, by simp, by simp, by simp, by simp⟩
    simp only [zlane_vpshufd _ _ _ _ _ hl, hstep, setRow_row _ _ _ _ hq, xidx_inj]
    split
    · rw [dword_shufDwords _ _ hq, sel2_eq, h a l _ hl (sel2_lt _ _)]
    · exact h r l q hl hq

/-- Instructions of the rounds, in sequence, on the four lanes. -/
theorem block_ok : ∀ (is : List HI) {ws : Nat → W} {s : State}, HH ws s →
    WP isa (.block (is.map HI.instr)) s fun s' => HH (fun l => is.foldl hstep (ws l)) s' ∧ Same s s'
  | [], _, _, h => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | i :: is, _, _, h => by
    obtain ⟨s', he, h', g, m, r, w⟩ := step_ok i h
    exact WP.block_cons_iff.2 ⟨s', he, WP.mono (block_ok is h') fun _ ⟨ht, hs⟩ =>
      ⟨ht, hs.gpr.trans g, hs.mem.trans m, hs.rd.trans r, hs.wr.trans w⟩⟩

/-! ## The code as instructions of the rounds -/

def halfH (a b c d : XReg) (r₁ r₂ : BitVec 8) : List HI :=
  [.add a a b, .xor d d a, .rol d d r₁, .add c c d, .xor b b c, .rol b b r₂]

theorem half_eq (a b c d : XReg) (r₁ r₂ : BitVec 8) :
    half a b c d r₁ r₂ = (halfH a b c d r₁ r₂).map HI.instr := rfl

def rotH (b c d : XReg) (o₁ o₂ o₃ : BitVec 8) : List HI := [.shuf b b o₁, .shuf c c o₂, .shuf d d o₃]

theorem rot_eq (b c d : XReg) (o₁ o₂ o₃ : BitVec 8) :
    rot b c d o₁ o₂ o₃ = (rotH b c d o₁ o₂ o₃).map HI.instr := rfl

def half2H (r₁ r₂ : BitVec 8) : List HI :=
  [.add .xmm0 .xmm0 .xmm1, .add .xmm4 .xmm4 .xmm5, .xor .xmm3 .xmm3 .xmm0, .xor .xmm7 .xmm7 .xmm4,
   .rol .xmm3 .xmm3 r₁, .rol .xmm7 .xmm7 r₁, .add .xmm2 .xmm2 .xmm3, .add .xmm6 .xmm6 .xmm7,
   .xor .xmm1 .xmm1 .xmm2, .xor .xmm5 .xmm5 .xmm6, .rol .xmm1 .xmm1 r₂, .rol .xmm5 .xmm5 r₂]

theorem half2_eq (r₁ r₂ : BitVec 8) : half2 r₁ r₂ = (half2H r₁ r₂).map HI.instr := rfl

/-- The column round, and the diagonal round with the rotations around it,
of the first set and of both. -/
def colsH : List HI := halfH .xmm0 .xmm1 .xmm2 .xmm3 16 12 ++ halfH .xmm0 .xmm1 .xmm2 .xmm3 8 7
def diagsH : List HI :=
  rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ colsH ++ rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39
def cols2H : List HI := half2H 16 12 ++ half2H 8 7
def diags2H : List HI :=
  (rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ rotH .xmm5 .xmm6 .xmm7 0x39 0x4e 0x93) ++ cols2H ++
    (rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39 ++ rotH .xmm5 .xmm6 .xmm7 0x93 0x4e 0x39)

theorem doubleRound_eq : doubleRound = (colsH ++ diagsH).map HI.instr := by
  simp only [doubleRound, colsH, diagsH, half_eq, rot_eq, List.map_append, List.append_assoc]

theorem doubleRound2_eq : doubleRound2 = (cols2H ++ diags2H).map HI.instr := by
  simp only [doubleRound2, cols2H, diags2H, half2_eq, rot2, rot_eq, List.map_append, List.append_assoc]

/-! ## The rounds on the words, by terms -/

/-- A term in the words `var k` of a lane. -/
inductive HE
  | var (k : Nat) | add (a b : HE) | xor (a b : HE) | rol (a : HE) (n : Nat)
  deriving DecidableEq

def HE.eval (w : W) : HE → Word
  | .var k => w k
  | .add a b => a.eval w + b.eval w
  | .xor a b => a.eval w ^^^ b.eval w
  | .rol a n => (a.eval w).rotateLeft n

/-- `hstep` on terms. -/
def hstepE (f : Nat → HE) : HI → Nat → HE
  | .add d a b => setRow f (xidx d) fun q => .add (f (4 * xidx a + q)) (f (4 * xidx b + q))
  | .xor d a b => setRow f (xidx d) fun q => .xor (f (4 * xidx a + q)) (f (4 * xidx b + q))
  | .rol d a n => setRow f (xidx d) fun q => .rol (f (4 * xidx a + q)) (n.toNat % 32)
  | .shuf d a o => setRow f (xidx d) fun q => f (4 * xidx a + sel2 o.toNat q)

/-- The terms `f` evaluate to the words `w`, in the words `w₀`. -/
def Rel (w₀ : W) (f : Nat → HE) (w : W) : Prop := ∀ k, (f k).eval w₀ = w k

theorem Rel.step {w₀ : W} {f : Nat → HE} {w : W} (h : Rel w₀ f w) (i : HI) :
    Rel w₀ (hstepE f i) (hstep w i) := by
  intro k
  cases i <;> simp only [hstepE, hstep, setRow] <;> split <;>
    first | exact h _ | (simp only [HE.eval]; rw [h, h]) | (simp only [HE.eval]; rw [h])

theorem Rel.foldl {w₀ : W} {f : Nat → HE} {w : W} (h : Rel w₀ f w) :
    ∀ is : List HI, Rel w₀ (is.foldl hstepE f) (is.foldl hstep w)
  | [] => h
  | i :: is => (h.step i).foldl is

/-- `QUARTERROUND` on terms, at the words `x, y, z, w`. -/
def qroundE (f : Nat → HE) (x y z w : Nat) : Nat → HE :=
  let a := HE.add (f x) (f y); let d := HE.rol (.xor (f w) a) 16
  let c := HE.add (f z) d; let b := HE.rol (.xor (f y) c) 12
  let a := HE.add a b; let d := HE.rol (.xor d a) 8
  let c := HE.add c d; let b := HE.rol (.xor b c) 7
  fun k => if k = w then d else if k = z then c else if k = y then b else if k = x then a else f k

/-- The state of the words `16 k … 16 k + 15` of a lane: set `k`. -/
def blk (w : W) (k : Nat) : CState := Vector.ofFn fun i => w (16 * k + i)

/-- The terms `f` evaluate, at the words of set `k`, to the state `v`. -/
def RelS (w₀ : W) (f : Nat → HE) (k : Nat) (v : CState) : Prop :=
  ∀ i (hi : i < 16), (f (16 * k + i)).eval w₀ = v[i]

theorem RelS.qround {w₀ : W} {f : Nat → HE} {k : Nat} {v : CState} (h : RelS w₀ f k v)
    (x y z w : Fin 16) (hd : x.1 ≠ y.1 ∧ x.1 ≠ z.1 ∧ x.1 ≠ w.1 ∧ y.1 ≠ z.1 ∧ y.1 ≠ w.1 ∧ z.1 ≠ w.1) :
    RelS w₀ (qroundE f (16 * k + x) (16 * k + y) (16 * k + z) (16 * k + w)) k (qround v x y z w) := by
  intro i hi
  have ex := h x x.2; have ey := h y y.2; have ez := h z z.2; have ew := h w w.2
  simp only [qroundE, Spec.ChaCha20.qround, Spec.ChaCha20.quarterRound, Vector.getElem_set,
    Nat.add_left_cancel_iff]
  by_cases iw : i = w.1
  · subst iw; simp [HE.eval, ex, ey, ez, ew]
  · by_cases iz : i = z.1
    · subst iz; simp [HE.eval, ex, ey, ez, ew, Ne.symm iw, hd]
    · by_cases iy : i = y.1
      · subst iy; simp [HE.eval, ex, ey, ez, ew, Ne.symm iw, Ne.symm iz, hd]
      · by_cases ix : i = x.1
        · subst ix; simp [HE.eval, ex, ey, ez, ew, Ne.symm iw, Ne.symm iz, Ne.symm iy, hd]
        · simp only [iw, iz, iy, ix, ite_false, Ne.symm iw, Ne.symm iz, Ne.symm iy, Ne.symm ix]
          exact h i hi

/-- The words, as terms. -/
def vars : Nat → HE := .var

theorem rel_vars (w : W) : Rel w vars w := fun _ => rfl

theorem relS_vars (w : W) (k : Nat) : RelS w vars k (blk w k) := fun i hi => by
  show w (16 * k + i) = _
  simp [blk]

/-- Two term states agree on the words of both sets. -/
def eq32 (f g : Nat → HE) : Bool := (List.range 32).all fun k => f k == g k

theorem RelS.of_rel {w₀ : W} {f g : Nat → HE} {w : W} (h : Rel w₀ f w) (e : eq32 f g = true)
    {k : Nat} (hk : k < 2) {v : CState} (hg : RelS w₀ g k v) : blk w k = v := by
  simp only [eq32, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  apply Vector.ext; intro i hi
  simp only [blk, Vector.getElem_ofFn]
  rw [← h, e _ (by omega)]
  exact hg i hi

/-- The column round on the terms of set `k`. -/
def colsE (f : Nat → HE) (k : Nat) : Nat → HE :=
  qroundE (qroundE (qroundE (qroundE f (16 * k + 0) (16 * k + 4) (16 * k + 8) (16 * k + 12))
    (16 * k + 1) (16 * k + 5) (16 * k + 9) (16 * k + 13)) (16 * k + 2) (16 * k + 6) (16 * k + 10)
    (16 * k + 14)) (16 * k + 3) (16 * k + 7) (16 * k + 11) (16 * k + 15)

/-- The diagonal round on the terms of set `k`. -/
def diagsE (f : Nat → HE) (k : Nat) : Nat → HE :=
  qroundE (qroundE (qroundE (qroundE f (16 * k + 0) (16 * k + 5) (16 * k + 10) (16 * k + 15))
    (16 * k + 1) (16 * k + 6) (16 * k + 11) (16 * k + 12)) (16 * k + 2) (16 * k + 7) (16 * k + 8)
    (16 * k + 13)) (16 * k + 3) (16 * k + 4) (16 * k + 9) (16 * k + 14)

/-- Words of a set other than those of the quarter round are kept, as are
the words of the other set. -/
theorem qroundE_other (f : Nat → HE) {x y z w n : Nat} (h : n ≠ x ∧ n ≠ y ∧ n ≠ z ∧ n ≠ w) :
    qroundE f x y z w n = f n := by
  simp [qroundE, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem RelS.cols {w₀ : W} {f : Nat → HE} {k : Nat} {v : CState} (h : RelS w₀ f k v) :
    RelS w₀ (colsE f k) k (Spec.ChaCha20.qround (Spec.ChaCha20.qround (Spec.ChaCha20.qround
      (Spec.ChaCha20.qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) :=
  (((h.qround 0 4 8 12 (by decide)).qround 1 5 9 13 (by decide)).qround 2 6 10 14 (by decide)).qround
    3 7 11 15 (by decide)

theorem RelS.diags {w₀ : W} {f : Nat → HE} {k : Nat} {v : CState} (h : RelS w₀ f k v) :
    RelS w₀ (diagsE f k) k (Spec.ChaCha20.qround (Spec.ChaCha20.qround (Spec.ChaCha20.qround
      (Spec.ChaCha20.qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) :=
  (((h.qround 0 5 10 15 (by decide)).qround 1 6 11 12 (by decide)).qround 2 7 8 13 (by decide)).qround
    3 4 9 14 (by decide)

/-- The terms of set `k` are those of `f` if they agree there. -/
theorem RelS.congr {w₀ : W} {f g : Nat → HE} {k : Nat} {v : CState} (h : RelS w₀ f k v)
    (e : ∀ i < 16, g (16 * k + i) = f (16 * k + i)) : RelS w₀ g k v := fun i hi => by
  rw [e i hi]; exact h i hi

theorem cols1_check : eq32 (colsH.foldl hstepE vars) (colsE vars 0) = true := by decide +kernel
theorem diags1_check : eq32 (diagsH.foldl hstepE vars) (diagsE vars 0) = true := by decide +kernel
theorem cols2_check : eq32 (cols2H.foldl hstepE vars) (colsE (colsE vars 0) 1) = true := by
  decide +kernel
theorem diags2_check : eq32 (diags2H.foldl hstepE vars) (diagsE (diagsE vars 0) 1) = true := by
  decide +kernel

/-! ## The double rounds on the words of a lane -/

theorem innerBlock_eq (v : CState) : innerBlock v =
    Spec.ChaCha20.qround (Spec.ChaCha20.qround (Spec.ChaCha20.qround (Spec.ChaCha20.qround
      (Spec.ChaCha20.qround (Spec.ChaCha20.qround (Spec.ChaCha20.qround
      (Spec.ChaCha20.qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15)
      0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := rfl

/-- The terms of the other set are unchanged by a round of one. -/
theorem colsE_other (f : Nat → HE) {k n : Nat} (h : n < 16 * k ∨ 16 * k + 16 ≤ n) : colsE f k n = f n := by
  simp only [colsE]
  rw [qroundE_other _ (by omega), qroundE_other _ (by omega), qroundE_other _ (by omega),
    qroundE_other _ (by omega)]

theorem diagsE_other (f : Nat → HE) {k n : Nat} (h : n < 16 * k ∨ 16 * k + 16 ≤ n) : diagsE f k n = f n := by
  simp only [diagsE]
  rw [qroundE_other _ (by omega), qroundE_other _ (by omega), qroundE_other _ (by omega),
    qroundE_other _ (by omega)]

theorem dr1_words (w : W) : blk ((colsH ++ diagsH).foldl hstep w) 0 = innerBlock (blk w 0) := by
  rw [List.foldl_append]
  have h₁ : blk (colsH.foldl hstep w) 0 = _ :=
    RelS.of_rel ((rel_vars w).foldl colsH) cols1_check (by decide) (relS_vars w 0).cols
  have h₂ := RelS.of_rel ((rel_vars (colsH.foldl hstep w)).foldl diagsH) diags1_check (by decide)
    (relS_vars (colsH.foldl hstep w) 0).diags
  rw [h₂, h₁, innerBlock_eq]

theorem dr2_words (w : W) {k : Nat} (hk : k < 2) :
    blk ((cols2H ++ diags2H).foldl hstep w) k = innerBlock (blk w k) := by
  rw [List.foldl_append]
  have c0 : RelS w (colsE (colsE vars 0) 1) 0 _ :=
    (relS_vars w 0).cols.congr fun i hi => colsE_other _ (by omega)
  have c1 : RelS w (colsE (colsE vars 0) 1) 1 _ :=
    ((relS_vars w 1).congr fun i hi => colsE_other _ (by omega)).cols
  let w' := cols2H.foldl hstep w
  have d0 : RelS w' (diagsE (diagsE vars 0) 1) 0 _ :=
    (relS_vars w' 0).diags.congr fun i hi => diagsE_other _ (by omega)
  have d1 : RelS w' (diagsE (diagsE vars 0) 1) 1 _ :=
    ((relS_vars w' 1).congr fun i hi => diagsE_other _ (by omega)).diags
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [RelS.of_rel ((rel_vars w').foldl diags2H) diags2_check (by decide) d0,
      RelS.of_rel ((rel_vars w).foldl cols2H) cols2_check (by decide) c0, innerBlock_eq]
  · rw [RelS.of_rel ((rel_vars w').foldl diags2H) diags2_check (by decide) d1,
      RelS.of_rel ((rel_vars w).foldl cols2H) cols2_check (by decide) c1, innerBlock_eq]

/-! ## The rounds on the registers -/

open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx512 (zreg_xidx xidx_zreg)

/-- The states of `S` sets of four blocks are in the registers: word `i` of
block `l` of set `k` (block `4 k + l`) in doubleword `i % 4` of lane `l` of
`zmm (4 k + i / 4)`. -/
def HB (S : Nat) (vs : Nat → CState) (s : State) : Prop :=
  ∀ k < S, ∀ l < 4, ∀ i (hi : i < 16), dword (s.zlane (zreg (4 * k + i / 4)) l) (i % 4) = (vs (4 * k + l))[i]

/-- The words of the lanes of the registers. -/
def wordsOf (s : State) (l : Nat) : W := fun n => dword (s.zlane (zreg (n / 4)) l) (n % 4)

theorem hh_wordsOf (s : State) : HH (wordsOf s) s := fun r l q hl hq => by
  simp only [wordsOf, show (4 * xidx r + q) / 4 = xidx r by omega,
    show (4 * xidx r + q) % 4 = q by omega, zreg_xidx]

theorem blk_wordsOf {S : Nat} {vs : Nat → CState} {s : State} (h : HB S vs s) {k l : Nat} (hk : k < S)
    (hl : l < 4) : blk (wordsOf s l) k = vs (4 * k + l) := by
  apply Vector.ext; intro i hi
  simp only [blk, Vector.getElem_ofFn, wordsOf]
  rw [show (16 * k + i) / 4 = 4 * k + i / 4 by omega, show (16 * k + i) % 4 = i % 4 by omega]
  exact h k hk l hl i hi

theorem hb_of {S : Nat} {ws : Nat → W} {s : State} (h : HH ws s) {vs : Nat → CState}
    (hv : ∀ k < S, ∀ l < 4, blk (ws l) k = vs (4 * k + l)) (hS : S ≤ 4) : HB S vs s := by
  intro k hk l hl i hi
  rw [h _ l _ hl (Nat.mod_lt _ (by decide)), xidx_zreg _ (by omega), ← hv k hk l hl]
  simp only [blk, Vector.getElem_ofFn]
  congr 1; omega

theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : HB 1 vs s) :
    WP isa (.block doubleRound) s fun s' => HB 1 (fun j => innerBlock (vs j)) s' ∧ Same s s' := by
  rw [doubleRound_eq]
  refine WP.mono (block_ok _ (hh_wordsOf s)) fun s' ⟨h', hs⟩ => ⟨hb_of h' (fun k hk l hl => ?_) (by decide), hs⟩
  obtain rfl : k = 0 := by omega
  rw [dr1_words, blk_wordsOf h hk hl]

theorem doubleRound2_ok {vs : Nat → CState} {s : State} (h : HB 2 vs s) :
    WP isa (.block doubleRound2) s fun s' => HB 2 (fun j => innerBlock (vs j)) s' ∧ Same s s' := by
  rw [doubleRound2_eq]
  refine WP.mono (block_ok _ (hh_wordsOf s)) fun s' ⟨h', hs⟩ => ⟨hb_of h' (fun k hk l hl => ?_) (by decide), hs⟩
  rw [dr2_words _ hk, blk_wordsOf h hk hl]

theorem rounds_ok {vs : Nat → CState} {s₀ : State} (h : HB 1 vs s₀) :
    ∀ n, WP isa (rounds n) s₀ fun s => HB 1 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ Same s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ ⟨h₁, hs⟩ =>
      WP.mono (doubleRound_ok h₁) fun _ ⟨h₂, hs'⟩ => ⟨h₂, hs.trans hs'⟩)

theorem rounds2_ok {vs : Nat → CState} {s₀ : State} (h : HB 2 vs s₀) :
    ∀ n, WP isa (rounds2 n) s₀ fun s => HB 2 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ Same s₀ s
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds2_ok h n) fun _ ⟨h₁, hs⟩ =>
      WP.mono (doubleRound2_ok h₁) fun _ ⟨h₂, hs'⟩ => ⟨h₂, hs.trans hs'⟩)

end VG.Proof.ChaCha20.X86_64.Avx512Tail
