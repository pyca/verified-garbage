module

public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Halves
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
public import VerifiedGarbage.Proof.Framework.Lit
public meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Following coefficients through the code of an NTT

The values an NTT computes are numbered: value `256 l + i` is coefficient `i` after step `l`, and
`R : Nat → BitVec 16` says what each is. `run` follows a block of code, with what each halfword of
each register is (`Val`: one of the numbered values, a constant, or what an instruction makes of
one on the way to the next), and with the numbers of the values in each vector of the polynomial
in memory. The butterflies are recognized by a `Dir`, which says of which numbered value a sum, a
difference or a reduced product is the next (`Dir.Sound`): nothing here depends on the order of the
instructions, or on the registers they use.

`run_sound`: if `run` succeeds, so does the code, and the polynomial is what `run` says.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64

/-! ## Values -/

/-- A lane of `sqrdmulh` (but for the two operands that saturate). -/
def sqr (x y : BitVec 16) : BitVec 16 := BitVec.ofInt 16 ((2 * x.toInt * y.toInt + 2 ^ 15) >>> 16)

/-- A lane of a reduced product: `x z - sqr(x, t) q`. -/
def red (x z t : BitVec 16) : BitVec 16 := x * z - sqr x t * 3329#16

/-- A lane of the floor of a quotient by `q`. -/
def flo (x : BitVec 16) : BitVec 16 := (sqr x 20159#16).sshiftRight 11

/-- What the halfwords of a register are: lists of eight numbers, of values or constants. -/
inductive Val
  /-- The values `ns`. -/
  | coef (ns : List Nat)
  /-- Constants. -/
  | lit (cs : List Nat)
  /-- The low halves of the products of the values `ns` by the constants `zs`. -/
  | low (ns zs : List Nat)
  /-- The `sqrdmulh` of the values `ns` by the constants `zs`. -/
  | quot (ns zs : List Nat)
  /-- Their reduced products. -/
  | prod (ns zs ts : List Nat)
  /-- The floors of the quotients of the values `ns` by `q`. -/
  | floor (ns : List Nat)
  /-- The signs of reduced products, as masks. -/
  | sign (ns zs ts : List Nat)
  /-- `q` where a reduced product is negative. -/
  | fix (ns zs ts : List Nat)
  /-- The sums of the values `ns` and `ms`. -/
  | sum (ns ms : List Nat)
  deriving DecidableEq

/-- Constant `e` of a list. -/
def cst (cs : List Nat) (e : Nat) : BitVec 16 := BitVec.ofNat 16 (cs.getD e 0)

/-- Halfword `e` of a register, where value `n` is `R n`. -/
def Val.lane (R : Nat → BitVec 16) : Val → Nat → BitVec 16
  | .coef ns, e => R (ns.getD e 0)
  | .lit cs, e => cst cs e
  | .low ns zs, e => R (ns.getD e 0) * cst zs e
  | .quot ns zs, e => sqr (R (ns.getD e 0)) (cst zs e)
  | .prod ns zs ts, e => red (R (ns.getD e 0)) (cst zs e) (cst ts e)
  | .floor ns, e => flo (R (ns.getD e 0))
  | .sign ns zs ts, e => (red (R (ns.getD e 0)) (cst zs e) (cst ts e)).sshiftRight 15
  | .fix ns zs ts, e => (red (R (ns.getD e 0)) (cst zs e) (cst ts e)).sshiftRight 15 &&& 3329#16
  | .sum ns ms, e => R (ns.getD e 0) + R (ms.getD e 0)

/-- `x` is what `v` says. -/
def Val.Is (R : Nat → BitVec 16) (v : Val) (x : BitVec 128) : Prop := ∀ e < 8, vhalf x e = v.lane R e

/-- The values that instructions lead to. -/
structure Dir where
  add : Val → Val → Option Val
  sub : Val → Val → Option Val
  prod : List Nat → List Nat → List Nat → Option Val
  canon : List Nat → Option Val

structure Dir.Sound (D : Dir) (R : Nat → BitVec 16) : Prop where
  add : ∀ {a b c}, D.add a b = some c → ∀ e < 8, c.lane R e = a.lane R e + b.lane R e
  sub : ∀ {a b c}, D.sub a b = some c → ∀ e < 8, c.lane R e = a.lane R e - b.lane R e
  prod : ∀ {ns zs ts c}, D.prod ns zs ts = some c → ∀ e < 8, c.lane R e = (Val.prod ns zs ts).lane R e
  canon : ∀ {ns c}, D.canon ns = some c → ∀ e < 8,
    c.lane R e = R (ns.getD e 0) - flo (R (ns.getD e 0)) * 3329#16

/-! ## Instructions -/

/-- `p` of the first `n` elements of three lists. -/
def all3 (p : Nat → Nat → Nat → Bool) : Nat → List Nat → List Nat → List Nat → Bool
  | 0, _, _, _ => true
  | n + 1, a :: as, b :: bs, c :: cs => p a b c && all3 p n as bs cs
  | _ + 1, _, _, _ => false

theorem all3_get {p : Nat → Nat → Nat → Bool} : ∀ {n : Nat} {as bs cs : List Nat},
    all3 p n as bs cs = true → ∀ e < n, p (as.getD e 0) (bs.getD e 0) (cs.getD e 0) = true
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a :: as, b :: bs, c :: cs, h, e, he => by
    simp only [all3, Bool.and_eq_true] at h
    cases e with
    | zero => exact h.1
    | succ e => simpa using all3_get h.2 e (Nat.lt_of_succ_lt_succ he)
  | n + 1, [], _, _, h, _, _ => by simp [all3] at h
  | n + 1, _ :: _, [], _, h, _, _ => by simp [all3] at h
  | n + 1, _ :: _, _ :: _, [], h, _, _ => by simp [all3] at h

/-- The same coefficients after a step: the values `k` further. -/
def next (k : Nat) (l : List Nat) : List Nat := l.map (· + k)

theorem getD_next {k : Nat} {l : List Nat} {e : Nat} (he : e < l.length) : (next k l).getD e 0 = l.getD e 0 + k := by
  simp only [next, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem he, Option.map_some,
    Option.getD_some]

theorem all3_length {p : Nat → Nat → Nat → Bool} : ∀ {n : Nat} {as bs cs : List Nat}, all3 p n as bs cs = true →
    n ≤ as.length ∧ n ≤ bs.length
  | 0, _, _, _, _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | n + 1, a :: as, b :: bs, c :: cs, h => by
    simp only [all3, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := all3_length h.2
    exact ⟨Nat.succ_le_succ h1, Nat.succ_le_succ h2⟩
  | n + 1, [], _, _, h => by simp [all3] at h
  | n + 1, _ :: _, [], _, h => by simp [all3] at h
  | n + 1, _ :: _, _ :: _, [], h => by simp [all3] at h

/-- The first eight elements are `c`. -/
def allAre (c : Nat) (l : List Nat) : Bool := all3 (fun a _ _ => Nat.beq a c) 8 l l l

theorem allAre_get {c : Nat} {l : List Nat} (h : allAre c l = true) {e : Nat} (he : e < 8) : l.getD e 0 = c :=
  Nat.eq_of_beq_eq_true (all3_get h e he)

/-- No element is `2¹⁵`, the one multiplier that could saturate. -/
def noSat (l : List Nat) : Bool := all3 (fun a _ _ => Nat.blt a 32768 || Nat.blt 32768 a && Nat.blt a 65536) 8 l l l

/-- A product of a register by the constants `zs`; `d` is what the destination was. -/
def mulStep (D : Dir) (op : VMulHOp) (d : Option Val) (n : Val) (zs : List Nat) : Option Val :=
  match op, n with
  | .mul, .coef ns => some (.low ns zs)
  | .sqrdmulh, .coef ns => if noSat zs then some (.quot ns zs) else none
  | .mls, .quot ns ts =>
    match d with
    | some (.low ms ws) => if allAre 3329 zs && decide (ms = ns) then D.prod ns ws ts else none
    | _ => none
  | .mls, .floor ns =>
    match d with
    | some (.coef ms) => if allAre 3329 zs && decide (ms = ns) then D.canon ns else none
    | _ => none
  | _, _ => none

/-- The numbers a permutation of words leads to. -/
def permStep (op : VPermOp) (a : VArr) : List Nat → List Nat → Option (List Nat)
  | [a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7] =>
    match a, op with
    | .d2, .trn1 => some [a0, a1, a2, a3, b0, b1, b2, b3]
    | .d2, .trn2 => some [a4, a5, a6, a7, b4, b5, b6, b7]
    | .s4, .trn1 => some [a0, a1, b0, b1, a4, a5, b4, b5]
    | .s4, .trn2 => some [a2, a3, b2, b3, a6, a7, b6, b7]
    | .s4, .zip1 => some [a0, a1, b0, b1, a2, a3, b2, b3]
    | .s4, .zip2 => some [a4, a5, b4, b5, a6, a7, b6, b7]
    | .s4, .uzp1 => some [a0, a1, a4, a5, b0, b1, b4, b5]
    | .s4, .uzp2 => some [a2, a3, a6, a7, b2, b3, b6, b7]
    | _, _ => none
  | _, _ => none

/-- The registers: what `v0, v1, …` are, if known. -/
abbrev Regs := List (Option Val)

def Regs.get (v : Regs) (r : VReg) : Option Val := v.getD r.index none

/-- What an instruction writes. -/
def vstep (D : Dir) (v : Regs) : VOp → Option (VReg × Val)
  | .mulHE op d n m i =>
    match v.get n, v.get m with
    | some x, some (.lit cs) =>
      if decide (i < 8) && decide (m.index < 16) then
        (mulStep D op (v.get d) x (List.replicate 8 (cs.getD i 0))).map fun y => (d, y)
      else none
    | _, _ => none
  | .mulH op d n m =>
    match v.get n, v.get m with
    | some x, some (.lit cs) => (mulStep D op (v.get d) x cs).map fun y => (d, y)
    | _, _ => none
  | .add .h8 d n m =>
    match v.get n, v.get m with
    | some x, some y => (D.add x y).map fun z => (d, z)
    | _, _ => none
  | .sub .h8 d n m =>
    match v.get n, v.get m with
    | some x, some y => (D.sub x y).map fun z => (d, z)
    | _, _ => none
  | .shift .sshr .h8 d n sh =>
    match v.get n with
    | some (.quot ns zs) => if Nat.beq sh 11 && allAre 20159 zs then some (d, .floor ns) else none
    | some (.prod ns zs ts) => if Nat.beq sh 15 then some (d, .sign ns zs ts) else none
    | _ => none
  | .logic .and d n m =>
    match v.get n, v.get m with
    | some (.sign ns zs ts), some (.lit cs) => if allAre 3329 cs then some (d, .fix ns zs ts) else none
    | _, _ => none
  | .perm op a d n m =>
    match v.get n, v.get m with
    | some (.coef xs), some (.coef ys) => (permStep op a xs ys).map fun zs => (d, .coef zs)
    | _, _ => none
  | _ => none

/-- The registers, and the numbers of the values of each vector of the polynomial. -/
structure St where
  v : Regs
  mem : List (List Nat)

/-- A register other than a callee-saved one. -/
def scratchV (d : VReg) : Bool := Nat.blt d.index 8 || Nat.blt 15 d.index

/-- An instruction: the polynomial is at `x0`, and rows of the table `T` at `x2`. -/
def step (D : Dir) (T : List (List Nat)) (a : St) : Instr → Option St
  | .vop op =>
    match vstep D a.v op with
    | some (d, x) => if scratchV d then some ⟨a.v.set d.index (some x), a.mem⟩ else none
    | none => none
  | .ldrq d .x0 off =>
    if Nat.beq (off % 16) 0 && Nat.blt off 512 && scratchV d then
      some ⟨a.v.set d.index (some (.coef (a.mem.getD (off / 16) []))), a.mem⟩ else none
  | .ldrq d .x2 off =>
    if Nat.beq (off % 16) 0 && Nat.blt off 65536 && Nat.blt (off / 16) T.length && scratchV d then
      some ⟨a.v.set d.index (some (.lit (T.getD (off / 16) []))), a.mem⟩ else none
  | .strq d .x0 off =>
    match a.v.get d with
    | some (.coef ns) =>
      if Nat.beq (off % 16) 0 && Nat.blt off 512 then some ⟨a.v, a.mem.set (off / 16) ns⟩ else none
    | _ => none
  | _ => none

/-- A block of instructions. -/
def run (D : Dir) (T : List (List Nat)) : List Instr → St → Option St
  | [], a => some a
  | i :: is, a => (step D T a i).bind fun b => run D T is b

kernel_fn run

theorem run_append {D : Dir} {T : List (List Nat)} : ∀ {is js : List Instr} {a b c : St},
    run D T is a = some b → run D T js b = some c → run D T (is ++ js) a = some c
  | [], _, _, _, _, h, h' => by cases h; exact h'
  | i :: is, js, a, b, c, h, h' => by
    simp only [run, List.cons_append] at h ⊢
    cases hs : step D T a i with
    | none => rw [hs] at h; cases h
    | some x => rw [hs] at h; exact run_append (b := b) h h'

/-! ## Soundness -/

theorem noSat_get {l : List Nat} (h : noSat l = true) {e : Nat} (he : e < 8) : cst l e ≠ 0x8000#16 := by
  have := all3_get h e he
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at this
  intro hc
  have := congrArg BitVec.toNat hc
  simp only [cst, BitVec.toNat_ofNat] at this
  omega_arith

theorem cst_replicate (c : Nat) {e : Nat} (he : e < 8) : cst (List.replicate 8 c) e = BitVec.ofNat 16 c := by
  rw [cst, List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left he, Option.getD_some]

theorem cst_allAre {c : Nat} {l : List Nat} (h : allAre c l = true) {e : Nat} (he : e < 8) :
    cst l e = BitVec.ofNat 16 c := by rw [cst, allAre_get h he]

/-- What `mulStep` says of each lane: the instruction's, which does not saturate. -/
theorem mulStep_sound {D : Dir} {R : Nat → BitVec 16} (hD : D.Sound R) {op : VMulHOp} {d : Option Val} {n y : Val}
    {zs : List Nat} (h : mulStep D op d n zs = some y) {vd : BitVec 128} (hd : ∀ x, d = some x → x.Is R vd)
    {vn : BitVec 128} (hn : n.Is R vn) {e : Nat} (he : e < 8) :
    op.lane (vhalf vd e) (vhalf vn e) (cst zs e) = some (y.lane R e) := by
  unfold mulStep at h
  split at h
  · cases h
    rw [hn e he]; rfl
  · split at h
    · rename_i hs
      cases h
      simp only [VMulHOp.lane, sqdmulhHLane, noSat_get hs he, and_false, ↓reduceIte]
      rw [hn e he]; rfl
    · cases h
  · split at h
    · rename_i ms ws
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨hq, rfl⟩ := hs
        rw [hD.prod h e he]
        simp only [VMulHOp.lane, hd _ rfl e he, hn e he, cst_allAre hq he, Val.lane, red]
      · cases h
    · cases h
  · split at h
    · rename_i ms
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        obtain ⟨hq, rfl⟩ := hs
        rw [hD.canon h e he]
        simp only [VMulHOp.lane, hd _ rfl e he, hn e he, cst_allAre hq he, Val.lane]
      · cases h
    · cases h
  · cases h

/-- The result of a lane-wise operation that does not fault. -/
theorem lanes_result {f : Nat → Option (BitVec 16)} {g : Nat → BitVec 16} (h : ∀ e < 8, f e = some (g e)) :
    ((List.range 8).all fun e => (f e).isSome) = true ∧
      ∀ e < 8, vhalf (ofVHalves fun e => (f e).getD 0) e = g e := by
  refine ⟨List.all_eq_true.2 fun e he => ?_, fun e he => ?_⟩
  · rw [h e (List.mem_range.1 he)]; rfl
  · rw [vhalf_ofVHalves _ he, h e he]; rfl

theorem sw32 (x : BitVec 32) : (x.setWidth 128).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem vword_trn1_s4 (x y : BitVec 128) {k : Nat} (hk : k < 4) :
    vword (VPermOp.eval .trn1 .s4 x y) k = if k % 2 = 0 then vword x k else vword y (k - 1) := by
  simp only [VPermOp.eval]
  rw [VG.Proof.Blowfish.AArch64.s4_ofLanes _ hk, show (VArr.s4.lanes x).length / 2 = 2 by simp [VArr.lanes],
    VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 2 k (by omega_using [hk])]
  split <;> rename_i h <;> rw [VG.Proof.Blowfish.AArch64.s4_lanes_getD _ (by omega_using [hk]), sw32] <;>
    exact congrArg _ (by omega_using [h])

theorem vword_trn2_s4 (x y : BitVec 128) {k : Nat} (hk : k < 4) :
    vword (VPermOp.eval .trn2 .s4 x y) k = if k % 2 = 0 then vword x (k + 1) else vword y k := by
  simp only [VPermOp.eval]
  rw [VG.Proof.Blowfish.AArch64.s4_ofLanes _ hk, show (VArr.s4.lanes x).length / 2 = 2 by simp [VArr.lanes],
    VG.Proof.Blowfish.AArch64.getD_pairs _ _ _ 2 k (by omega_using [hk])]
  split <;> rename_i h <;> rw [VG.Proof.Blowfish.AArch64.s4_lanes_getD _ (by omega_using [hk]), sw32] <;>
    exact congrArg _ (by omega_using [h])

/-- The halfwords of a vector whose words are those of vectors known. -/
theorem is_words {R : Nat → BitVec 16} {z : BitVec 128} {c0 c1 c2 c3 c4 c5 c6 c7 : Nat}
    (h : ∀ k < 4, ∃ (x : BitVec 128) (j : Nat), vword z k = vword x j ∧
      vhalf x (2 * j) = R ([c0, c1, c2, c3, c4, c5, c6, c7].getD (2 * k) 0) ∧
      vhalf x (2 * j + 1) = R ([c0, c1, c2, c3, c4, c5, c6, c7].getD (2 * k + 1) 0)) :
    (Val.coef [c0, c1, c2, c3, c4, c5, c6, c7]).Is R z := by
  intro e he
  obtain ⟨x, j, hw, h0, h1⟩ := h (e / 2) (by omega_using [he])
  rw [vhalf_vword, hw]
  simp only [Val.lane]
  rcases (show e % 2 = 0 ∨ e % 2 = 1 by omega_using []) with h2 | h2
  · rw [show 2 * (e / 2) = e by omega_using [h2]] at h0
    rw [h2, ← h0, vhalf_vword, show 2 * j / 2 = j by omega_using [], show 2 * j % 2 = 0 by omega_using []]
  · rw [show 2 * (e / 2) + 1 = e by omega_using [h2]] at h1
    rw [h2, ← h1, vhalf_vword, show (2 * j + 1) / 2 = j by omega_using [], show (2 * j + 1) % 2 = 1 by omega_using []]

theorem permStep_sound {R : Nat → BitVec 16} {op : VPermOp} {a : VArr} {xs ys zs : List Nat}
    (h : permStep op a xs ys = some zs) {x y : BitVec 128} (hx : (Val.coef xs).Is R x)
    (hy : (Val.coef ys).Is R y) : (Val.coef zs).Is R (op.eval a x y) := by
  unfold permStep at h
  split at h
  · rename_i a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
    have X : ∀ j < 4, vhalf x (2 * j) = R ([a0, a1, a2, a3, a4, a5, a6, a7].getD (2 * j) 0) ∧
        vhalf x (2 * j + 1) = R ([a0, a1, a2, a3, a4, a5, a6, a7].getD (2 * j + 1) 0) := fun j hj =>
      ⟨hx _ (by omega_using [hj]), hx _ (by omega_using [hj])⟩
    have Y : ∀ j < 4, vhalf y (2 * j) = R ([b0, b1, b2, b3, b4, b5, b6, b7].getD (2 * j) 0) ∧
        vhalf y (2 * j + 1) = R ([b0, b1, b2, b3, b4, b5, b6, b7].getD (2 * j + 1) 0) := fun j hj =>
      ⟨hy _ (by omega_using [hj]), hy _ (by omega_using [hj])⟩
    split at h <;> cases h <;> refine is_words fun k hk => ?_ <;>
      rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact ⟨x, 0, vword_trn1_d2 x y (by decide), X 0 (by decide)⟩
    · exact ⟨x, 1, vword_trn1_d2 x y (by decide), X 1 (by decide)⟩
    · exact ⟨y, 0, vword_trn1_d2 x y (by decide), Y 0 (by decide)⟩
    · exact ⟨y, 1, vword_trn1_d2 x y (by decide), Y 1 (by decide)⟩
    · exact ⟨x, 2, vword_trn2_d2 x y (by decide), X 2 (by decide)⟩
    · exact ⟨x, 3, vword_trn2_d2 x y (by decide), X 3 (by decide)⟩
    · exact ⟨y, 2, vword_trn2_d2 x y (by decide), Y 2 (by decide)⟩
    · exact ⟨y, 3, vword_trn2_d2 x y (by decide), Y 3 (by decide)⟩
    · exact ⟨x, 0, vword_trn1_s4 x y (by decide), X 0 (by decide)⟩
    · exact ⟨y, 0, vword_trn1_s4 x y (by decide), Y 0 (by decide)⟩
    · exact ⟨x, 2, vword_trn1_s4 x y (by decide), X 2 (by decide)⟩
    · exact ⟨y, 2, vword_trn1_s4 x y (by decide), Y 2 (by decide)⟩
    · exact ⟨x, 1, vword_trn2_s4 x y (by decide), X 1 (by decide)⟩
    · exact ⟨y, 1, vword_trn2_s4 x y (by decide), Y 1 (by decide)⟩
    · exact ⟨x, 3, vword_trn2_s4 x y (by decide), X 3 (by decide)⟩
    · exact ⟨y, 3, vword_trn2_s4 x y (by decide), Y 3 (by decide)⟩
    · exact ⟨x, 0, vword_zip1_s4' x y (by decide), X 0 (by decide)⟩
    · exact ⟨y, 0, vword_zip1_s4' x y (by decide), Y 0 (by decide)⟩
    · exact ⟨x, 1, vword_zip1_s4' x y (by decide), X 1 (by decide)⟩
    · exact ⟨y, 1, vword_zip1_s4' x y (by decide), Y 1 (by decide)⟩
    · exact ⟨x, 2, vword_zip2_s4 x y (by decide), X 2 (by decide)⟩
    · exact ⟨y, 2, vword_zip2_s4 x y (by decide), Y 2 (by decide)⟩
    · exact ⟨x, 3, vword_zip2_s4 x y (by decide), X 3 (by decide)⟩
    · exact ⟨y, 3, vword_zip2_s4 x y (by decide), Y 3 (by decide)⟩
    · exact ⟨x, 0, vword_uzp1_s4 x y (by decide), X 0 (by decide)⟩
    · exact ⟨x, 2, vword_uzp1_s4 x y (by decide), X 2 (by decide)⟩
    · exact ⟨y, 0, vword_uzp1_s4 x y (by decide), Y 0 (by decide)⟩
    · exact ⟨y, 2, vword_uzp1_s4 x y (by decide), Y 2 (by decide)⟩
    · exact ⟨x, 1, vword_uzp2_s4 x y (by decide), X 1 (by decide)⟩
    · exact ⟨x, 3, vword_uzp2_s4 x y (by decide), X 3 (by decide)⟩
    · exact ⟨y, 1, vword_uzp2_s4 x y (by decide), Y 1 (by decide)⟩
    · exact ⟨y, 3, vword_uzp2_s4 x y (by decide), Y 3 (by decide)⟩
  · cases h

/-- What the registers say of a state. -/
def Regs.Ok (R : Nat → BitVec 16) (v : Regs) (s : State) : Prop := ∀ r x, v.get r = some x → x.Is R (s.v r)

/-- What `vstep` says is what the instruction writes. -/
theorem vstep_sound {D : Dir} {R : Nat → BitVec 16} (hD : D.Sound R) {v : Regs} {s : State} (hv : v.Ok R s)
    {op : VOp} {d : VReg} {y : Val} (h : vstep D v op = some (d, y)) :
    ∃ x, op.eval s = some (d, x) ∧ y.Is R x := by
  unfold vstep at h
  split at h
  · rename_i op d' n m i
    split at h
    · rename_i x cs hn hm
      split at h
      · rename_i hi
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
        obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.1 h
        cases he
        have hl : ∀ e < 8, op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) i) = some (y.lane R e) :=
          fun e he => by
            rw [hv m _ hm i hi.1]
            have := mulStep_sound hD hz (fun x hx => hv d x hx) (hv n _ hn) he
            rwa [cst_replicate _ he] at this
        obtain ⟨ha, hr⟩ := lanes_result hl
        exact ⟨_, by simp only [VOp.eval]; rw [ite_eq_left ⟨hi.1, hi.2, ha⟩], hr⟩
      · cases h
    · cases h
  · rename_i op d' n m
    split at h
    · rename_i x cs hn hm
      obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      have hl : ∀ e < 8, op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) e) = some (y.lane R e) :=
        fun e he => by
          rw [hv m _ hm e he]
          exact mulStep_sound hD hz (fun x hx => hv d x hx) (hv n _ hn) he
      obtain ⟨ha, hr⟩ := lanes_result hl
      exact ⟨_, by simp only [VOp.eval]; rw [ite_eq_left ha], hr⟩
    · cases h
  · rename_i d' n m
    split at h
    · rename_i x z hn hm
      obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      refine ⟨_, rfl, fun e he => ?_⟩
      rw [vhalf_map2 _ _ _ he, hD.add hw e he, hv n _ hn e he, hv m _ hm e he]
    · cases h
  · rename_i d' n m
    split at h
    · rename_i x z hn hm
      obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      refine ⟨_, rfl, fun e he => ?_⟩
      rw [vhalf_map2 _ _ _ he, hD.sub hw e he, hv n _ hn e he, hv m _ hm e he]
    · cases h
  · rename_i d' n sh
    split at h
    · rename_i ns zs hn
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true] at hs
        obtain rfl := Nat.eq_of_beq_eq_true hs.1
        cases h
        refine ⟨_, rfl, fun e he => ?_⟩
        rw [vhalf_map2 _ _ _ he, hv n _ hn e he]
        simp only [VShiftOp.eval, Val.lane, cst_allAre hs.2 he, flo]
      · cases h
    · rename_i ns zs ts hn
      split at h
      · rename_i hs
        obtain rfl := Nat.eq_of_beq_eq_true hs
        cases h
        refine ⟨_, rfl, fun e he => ?_⟩
        rw [vhalf_map2 _ _ _ he, hv n _ hn e he]
        rfl
      · cases h
    · cases h
  · rename_i d' n m
    split at h
    · rename_i ns zs ts cs hn hm
      split at h
      · rename_i hs
        cases h
        refine ⟨_, rfl, fun e he => ?_⟩
        rw [vhalf_and, hv n _ hn e he, hv m _ hm e he]
        simp only [Val.lane, cst_allAre hs he]
      · cases h
    · cases h
  · rename_i op a d' n m
    split at h
    · rename_i xs ys hn hm
      obtain ⟨zs, hz, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact ⟨_, rfl, permStep_sound hz (hv n _ hn) (hv m _ hm)⟩
    · cases h
  · cases h

/-! ## Blocks of instructions -/

/-- What a block starts from: the polynomial at `x0` is writable, and the table `T` at `x2`
readable and apart from it. -/
structure Env (T : List (List Nat)) (f t : Addr) (s : State) : Prop where
  x0 : s.gpr .x0 = f
  x2 : s.gpr .x2 = t
  wr : Covers [⟨f, 512⟩] s.wr
  rd : Covers [⟨t, 16 * T.length⟩] (s.rd ++ s.wr)
  apart : (Region.mk t (16 * T.length)).Disjoint ⟨f, 512⟩
  len : T.length ≤ 4096
  row : ∀ i < T.length, ∀ e < 8, vhalf (s.mem.read (t + BitVec.ofNat 64 (16 * i)) 16) e = cst (T.getD i []) e

/-- What `run` says of a state `s` reached from `s₀`. -/
structure Rel (R : Nat → BitVec 16) (f : Addr) (s₀ : State) (a : St) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  vcs : ∀ r ∈ preservedV, s.v r = s₀.v r
  frame : Frame [⟨f, 512⟩] s₀.mem s.mem
  v : a.v.Ok R s
  vlen : a.v.length = 32
  mlen : a.mem.length = 32
  mem : ∀ i < 32, ∀ e < 8, Proof.MlKem.coeffAtW 16 s.mem f (8 * i + e) = R ((a.mem.getD i []).getD e 0)

theorem index_lt (r : VReg) : r.index < 32 := by cases r <;> decide

theorem index_inj {a b : VReg} (h : a.index = b.index) : a = b := by
  revert h; cases a <;> cases b <;> first | exact fun _ => rfl | exact fun h => absurd h (by decide)

theorem scratchV_pres {d : VReg} (h : scratchV d = true) : d ∉ preservedV := by
  revert h; cases d <;> decide

theorem get_set {v : Regs} (hl : v.length = 32) (d r : VReg) (x : Val) :
    Regs.get (v.set d.index (some x)) r = if r = d then some x else v.get r := by
  simp only [Regs.get, List.getD_eq_getElem?_getD]
  by_cases h : r = d
  · subst h
    rw [ite_eq_left rfl, List.getElem?_set_self (by rw [hl]; exact index_lt _)]; rfl
  · rw [ite_eq_right h, List.getElem?_set_ne (fun hh => h (index_inj hh.symm))]

/-- A state after a write of a register. -/
theorem Rel.setV {R : Nat → BitVec 16} {f : Addr} {s₀ s : State} {a : St} (h : Rel R f s₀ a s) {d : VReg}
    (hd : scratchV d = true) {x : Val} {y : BitVec 128} (hx : x.Is R y) :
    Rel R f s₀ ⟨a.v.set d.index (some x), a.mem⟩ (s.setV d y) where
  gpr := h.gpr
  sp := h.sp
  rd := h.rd
  wr := h.wr
  vcs r hr := by
    rw [RegUpd.v_setV_of_ne _ _ (fun (e : r = d) => scratchV_pres hd (e ▸ hr))]; exact h.vcs r hr
  frame := h.frame
  v r z hz := by
    rw [get_set h.vlen] at hz
    by_cases hr : r = d
    · subst hr
      rw [ite_eq_left rfl] at hz
      cases hz
      rw [RegUpd.v_setV_self]; exact hx
    · rw [ite_eq_right hr] at hz
      rw [RegUpd.v_setV_of_ne _ _ hr]; exact h.v r z hz
  vlen := by rw [List.length_set]; exact h.vlen
  mlen := h.mlen
  mem := h.mem

theorem step_sound {D : Dir} {R : Nat → BitVec 16} (hD : D.Sound R) {T : List (List Nat)} {f t : Addr}
    {s₀ : State} (he : Env T f t s₀) {a b : St} {i : Instr} (h : step D T a i = some b) {s : State}
    (hr : Rel R f s₀ a s) : ∃ s', exec i s = some s' ∧ Rel R f s₀ b s' := by
  unfold step at h
  split at h
  · rename_i op
    split at h
    · rename_i d x hs
      split at h
      · rename_i hd
        cases h
        obtain ⟨y, hy, hx⟩ := vstep_sound hD hr.v hs
        exact ⟨s.setV d y, by simp only [reduceExec, hy, Option.map_some], hr.setV hd hx⟩
      · cases h
    · cases h
  · rename_i d off
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      obtain ⟨⟨h1, h2⟩, hd⟩ := hc
      have h1 := Nat.eq_of_beq_eq_true h1
      have ha : s.gpr .x0 + BitVec.ofNat 64 off = f + BitVec.ofNat 64 off := by rw [hr.gpr, he.x0]
      have hin : InRegions (s.rd ++ s.wr) (f + BitVec.ofNat 64 off) 16 := by
        rw [hr.rd, hr.wr]
        exact Covers.right he.wr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base f (by omega_using [h1, h2]) (by omega_using [h2])⟩
      refine ⟨s.setV d (s.mem.read (f + BitVec.ofNat 64 off) 16), ?_, hr.setV hd fun e he' => ?_⟩
      · simp only [reduceExec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ⟨h1, by omega_using [h2]⟩, and_self, ite_true, ha,
          Option.bind_some, State.load, hin, Option.map_some]
      · apply BitVec.eq_of_toNat_eq
        rw [show off = 2 * (8 * (off / 16)) by omega_using [h1], vhalf_read_coeff _ _ _ he',
          hr.mem _ (by omega_using [h2]) e he', show 2 * (8 * (off / 16)) / 16 = off / 16 by omega_using []]
        rfl
    · cases h
  · rename_i d off
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, hd⟩ := hc
      have h1 := Nat.eq_of_beq_eq_true h1
      have ha : s.gpr .x2 + BitVec.ofNat 64 off = t + BitVec.ofNat 64 off := by rw [hr.gpr, he.x2]
      have hct : (Region.mk t (16 * T.length)).Contains (t + BitVec.ofNat 64 off) 16 :=
        Offset.contains_base t (by omega_using [h1, h3]) (by omega_using [h2])
      have hin : InRegions (s.rd ++ s.wr) (t + BitVec.ofNat 64 off) 16 := by
        rw [hr.rd, hr.wr]
        exact he.rd _ _ ⟨_, List.mem_singleton_self _, hct⟩
      refine ⟨s.setV d (s.mem.read (t + BitVec.ofNat 64 off) 16), ?_, hr.setV hd fun e he' => ?_⟩
      · simp only [reduceExec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ⟨h1, h2⟩, and_self, ite_true, ha,
          Option.bind_some, State.load, hin, Option.map_some]
      · rw [hr.frame.read hct (fun r hr' => by rw [List.mem_singleton.1 hr']; exact he.apart) (by decide)]
        have := he.row (off / 16) h3 e he'
        rw [show 16 * (off / 16) = off by omega_using [h1]] at this
        exact this
    · cases h
  · rename_i d off
    split at h
    · rename_i ns hn
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc
        obtain ⟨h1, h2⟩ := hc
        have h1 := Nat.eq_of_beq_eq_true h1
        have ha : s.gpr .x0 + BitVec.ofNat 64 off = f + BitVec.ofNat 64 off := by rw [hr.gpr, he.x0]
        have hct : (Region.mk f 512).Contains (f + BitVec.ofNat 64 off) 16 :=
          Offset.contains_base f (by omega_using [h1, h2]) (by omega_using [h2])
        have hout : InRegions s.wr (f + BitVec.ofNat 64 off) 16 := by
          rw [hr.wr]
          exact he.wr _ _ ⟨_, List.mem_singleton_self _, hct⟩
        refine ⟨{ s with mem := s.mem.write (f + BitVec.ofNat 64 off) 16 (s.v d) }, ?_, ?_⟩
        · simp only [reduceExec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ⟨h1, by omega_using [h2]⟩, and_self, ite_true, ha,
            Option.bind_some, State.store, hout]
        · refine ⟨hr.gpr, hr.sp, hr.rd, hr.wr, hr.vcs, hr.frame.write (n := 16) (List.mem_singleton_self _) (s.v d) hct,
            hr.v, hr.vlen, by rw [List.length_set]; exact hr.mlen, fun i hi e he' => ?_⟩
          dsimp only
          rw [show off = 2 * (8 * (off / 16)) by omega_using [h1],
            coeffAtW16_write _ _ (by omega_using [h2]) (by omega_using [hi, he']),
            show 2 * (8 * (off / 16)) / 16 = off / 16 by omega_using [], List.getD_eq_getElem?_getD (l := a.mem.set _ _)]
          by_cases hj : i = off / 16
          · rw [ite_eq_left (by omega_using [hj, he']), hj,
              List.getElem?_set_self (by rw [hr.mlen]; omega_using [h2]), Option.getD_some,
              show 8 * (off / 16) + e - 8 * (off / 16) = e by omega_using [], hr.v d _ hn e he']
            rfl
          · rw [ite_eq_right (by omega_using [hj, he']), List.getElem?_set_ne (Ne.symm hj), ← List.getD_eq_getElem?_getD,
              hr.mem i hi e he']
      · cases h
    · cases h
  · cases h

theorem run_sound {D : Dir} {R : Nat → BitVec 16} (hD : D.Sound R) {T : List (List Nat)} {f t : Addr}
    {s₀ : State} (he : Env T f t s₀) : ∀ {is : List Instr} {a b : St}, run D T is a = some b → ∀ {s : State},
      Rel R f s₀ a s → WP isa (.block is) s fun s' => Rel R f s₀ b s'
  | [], _, _, h, s, hr => by cases h; exact WP.block_nil_iff.2 hr
  | i :: is, a, b, h, s, hr => by
    obtain ⟨c, hc, h'⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', hs, hr'⟩ := step_sound hD he hc hr
    exact WP.block_cons_iff.2 ⟨s', hs, run_sound hD he h' hr'⟩

end VG.Proof.MlKem.AArch64.Ntt16
