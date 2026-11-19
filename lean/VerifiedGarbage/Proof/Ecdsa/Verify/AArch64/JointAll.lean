module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.SumAll
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall

/-!
# Joint radix-four ECDSA verification on AArch64: for every curve

`Impl/Ecdsa/Verify/<Curve>/AArch64/Joint.lean` states the same programs for
each curve, with the curve's numbers written out: two tables of the scalars'
bits, a table of the fifteen nonzero digit pairs `[i]G + [j]Q`, then one
chain of doublings with an addition of the entry the two scalars' next
digits select. The table is built in one of two ways: through pointers the
counter selects (`build`: P-192, secp256k1, brainpoolP512r1), or by a choice
among fifteen copies (`buildTable`: brainpoolP256r1, brainpoolP384r1).

This module states those programs once, for a configuration `c` and the
words `m` of a scalar, and proves them for a configuration with a `Kit`
(and, for `buildTable`, a `Compact`): `pointsWith_ok`, for a table's program
that is `BuildOk`; `points_ok` and `pointsCompact_ok`, for the two; and
`verifyWith_ok`, the verification with such points. Each curve's
`Joint/State.lean` gives its kit, and its `Joint/Points.lean` and
`Joint/Main.lean` restate what other modules use, for the curve's own
programs, which are these by definition.

A fact about the layout depends on the configuration only through its word
count, four, six or eight (`Kit.n_mem`): `jd c` decides it at the three, and
`jo c` proves at the three, by `omega`, arithmetic in the word count and the
number of a table's entry.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.JointKit

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V UX UY UZ RM')
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
  (pair pair_curve pair_add pair_zero shift_radix stage at_step at_zero at_top
   pair_generator pair_peer previous previous_lt table_step point_comm)

/-- What the joint multiplication's proof needs of a configuration. A class,
so that the statements are in the configuration itself, as each curve's
module states them for its own. -/
class Kit (c : Cfg) : Prop where
  /-- A field element has four, six or eight words. -/
  n_mem : c.n ∈ [4, 6, 8]
  /-- The complete addition keeps the loop's counter. -/
  sum_counter : ∀ i ∈ instrs (sum c), clobbers i .x19 = false

/-- The words `m` of a scalar: the loop takes `32 * m` rounds, of two bits each. -/
structure Rounds (c : Cfg) (m : Nat) : Prop where
  /-- A scalar is at least a word. -/
  pos : 0 < m
  /-- A scalar is no longer than a field element. -/
  le : m ≤ c.n
  /-- The group's order fits the scalar's words. -/
  order_lt : BaseCfgOk c → c.C.n < 2 ^ (64 * m)

theorem Kit.n_pos (c : Cfg) [Kit c] : 0 < c.n := by
  have h := Kit.n_mem (c := c)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem Kit.n_le (c : Cfg) [Kit c] : c.n ≤ 8 := by
  have h := Kit.n_mem (c := c)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

/-! ## The programs -/

abbrev resultPt (c : Cfg) : Pt := c.pt RX RY RZ
abbrev entry (c : Cfg) : Pt := c.pt UX UY UZ
/-- The table of `u`'s bits, a byte each. -/
abbrev bitsU : Nat := 2944
/-- The table of `v`'s bits. -/
abbrev bitsV (c : Cfg) : Nat := 2944 + 64 * c.n
/-- The fifteen projective triples. -/
abbrev tableAt : Nat := 5280

/-- Digit pair `i + 4j`, numbered from one. There is no stored zero entry. -/
def tablePt (c : Cfg) (d : Nat) : Pt :=
  ⟨tableAt + 24 * c.n * (d-1),tableAt + 24 * c.n * (d-1) + 8 * c.n,tableAt + 24 * c.n * (d-1) + 16 * c.n⟩

def infinity (c : Cfg) : List Instr :=
  setConst c.n (resultPt c).x 0 ++ setConst c.n (resultPt c).y (c.mont 1) ++ setConst c.n (resultPt c).z 0

def affineEntry (c : Cfg) (x y : Nat) : List Instr :=
  copy c.n (entry c).x (c.sl x) ++ copy c.n (entry c).y (c.sl y) ++ copy c.n (entry c).z (c.sl ONEP)

def addPoints (c : Cfg) : Prog isa := sum c

def double (c : Cfg) : Prog isa := .seq (.block (copyPt c.n (entry c) (resultPt c))) (addPoints c)

/-- The digit pair `u[2j:2j+2] + 4 v[2j:2j+2]` in `x2`. -/
def digit (c : Cfg) : List Instr :=
  [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16] ++
  hornerBits bitsU 2 ++ [.addImm .x .x6 .x2 0] ++ hornerBits (bitsV c) 2 ++
  [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]

/-- Copy `n` words from the selected entry pointer into a coordinate. -/
def copyFrom : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | n+1, dst, src => [.ldr .x .x4 .x16 src,st .x4 dst] ++ copyFrom n (dst+8) (src+8)

/-- Load a nonzero public digit pair into the addition's three input slots. -/
def fetchHead (c : Cfg) : List Instr :=
  [.subImm .x .x2 .x2 1,.movz .x .x17 (BitVec.ofNat 16 (24 * c.n)) 0,.mul .x .x2 .x2 .x17,
   .movz .x .x16 tableAt 0,.add .x .x16 .x0 .x16,.add .x .x16 .x16 .x2]

def fetch (c : Cfg) : List Instr :=
  fetchHead c ++ copyFrom c.n (entry c).x 0 ++ copyFrom c.n (entry c).y (8 * c.n) ++
    copyFrom c.n (entry c).z (16 * c.n)

def digitTail (c : Cfg) : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block (fetch c)) (addPoints c))

def addDigit (c : Cfg) : Prog isa := .seq (.block (digit c)) (digitTail c)

def step (c : Cfg) : Prog isa :=
  .seq (.block [decCounter]) (.seq (double c) (.seq (double c) (addDigit c)))

/-- `x2 = k - x19`: the number of a table entry, from the build's counter. -/
def indexFrom (k : Nat) : List Instr := [.movz .x .x2 (BitVec.ofNat 16 k) 0,.sub .x .x2 .x2 .x19]

/-- Copy `n` words of a coordinate to the entry the pointer `x16` selects. -/
def copyTo : Nat → Nat → Nat → List Instr
  | 0, _, _ => []
  | n+1, dst, src => [ld .x4 src,.str .x .x4 .x16 dst] ++ copyTo n (dst+8) (src+8)

/-- The entry numbered `k - x19` into the result, or the point at infinity
for number zero. -/
def previousEntry (c : Cfg) (k : Nat) : Prog isa :=
  .seq (.block (indexFrom k)) (.ite (.zero .x .x2) (.block (infinity c))
    (.block (fetchHead c ++ copyFrom c.n (resultPt c).x 0 ++ copyFrom c.n (resultPt c).y (8 * c.n) ++
      copyFrom c.n (resultPt c).z (16 * c.n))))

/-- `x2 = (x19 & 3) ^ 3`: zero exactly when the entry `15 - x19` starts a row. -/
def rowTest : List Instr :=
  [.movz .x .x5 3 0,.logic .and .x .x2 .x19 .x5,.logic .eor .x .x2 .x2 .x5]

/-- The result into the entry numbered `15 - x19`. -/
def storeEntry (c : Cfg) : List Instr :=
  indexFrom 15 ++ fetchHead c ++ copyTo c.n 0 (resultPt c).x ++ copyTo c.n (8 * c.n) (resultPt c).y ++
    copyTo c.n (16 * c.n) (resultPt c).z

/-- Entry `d = 15 - x19`, with `x19` counting down from fifteen: the previous
entry plus `G`, or the previous row's first entry plus `Q` (the point at
infinity for the first entry of the first two rows), through pointers the
counter selects, so that one complete addition serves all fifteen entries. -/
def buildStep (c : Cfg) : Prog isa :=
  .seq (.block (decCounter :: rowTest)) <|
  .seq (.ite (.zero .x .x2)
    (.seq (previousEntry c 11) (.block (affineEntry c PX PY)))
    (.seq (previousEntry c 14) (.block (affineEntry c GX GY)))) <|
  .seq (addPoints c) (.block (storeEntry c))

/-- The table's fifteen entries, in order. -/
def build (c : Cfg) : Prog isa := .seq (.block [.movz .x .x19 15 0]) (.loop (buildStep c) (.nonzero .x .x19))

def prepare (c : Cfg) : Prog isa :=
  .seq (bits (c.sl U) bitsU (8 * c.n)) <|
  .seq (bits (c.sl V) (bitsV c) (8 * c.n))
    (.block (setConst c.n (c.sl EXPP) (c.mont (3 * c.C.b))))

/-- The bit tables, the table of digit pairs by `build`, `R = O`, and the
counter: `32 * m` rounds. -/
def setupWith (c : Cfg) (m : Nat) (build : Prog isa) : Prog isa :=
  .seq (prepare c) <| .seq build (.block (infinity c ++ [.movz .x .x19 (BitVec.ofNat 16 (32 * m)) 0]))

def pointsWith (c : Cfg) (m : Nat) (build : Prog isa) : Prog isa :=
  .seq (setupWith c m build) (.loop (step c) (.nonzero .x .x19))

abbrev setup (c : Cfg) (m : Nat) : Prog isa := setupWith c m (build c)
abbrev points (c : Cfg) (m : Nat) : Prog isa := pointsWith c m (build c)

/-! ## The layout -/

abbrev coordinates (p : Pt) : List Nat := [p.x,p.y,p.z]
abbrev num (c : Cfg) (base : Addr) (s : State) (o : Nat) := wordsVal s.mem base o c.n
abbrev val (c : Cfg) (base : Addr) (s : State) (o : Nat) := tmv c.C c.n base s o
abbrev addWork (c : Cfg) : List (Nat × Nat) := slW c sumW
abbrev entryWork (c : Cfg) : List (Nat × Nat) := (coordinates (entry c)).map (·,8*c.n)
abbrev loopWork (c : Cfg) : List (Nat × Nat) := addWork c ++ entryWork c
abbrev work (c : Cfg) : List (Nat × Nat) :=
  loopWork c ++ [(c.sl EXPP,8*c.n),(bitsU,128*c.n),(tableAt,360*c.n)]
abbrev gSource (c : Cfg) : Pt := c.pt GX GY ONEP
abbrev qSource (c : Cfg) : Pt := c.pt PX PY ONEP
abbrev arithmeticWork (c : Cfg) := loopWork c ++ [(tableAt,360*c.n)]
abbrev resultWork (c : Cfg) : List (Nat × Nat) := (coordinates (resultPt c)).map (·,8*c.n)
abbrev prepWork (c : Cfg) : List (Nat × Nat) := [(bitsU,128*c.n),(c.sl EXPP,8*c.n)]

/-- `decide` for a fact about the layout, which depends on the configuration
only through its word count: at the three word counts (and `decide` itself
for a closed fact beside one). -/
local macro "jd " c:term : tactic => `(tactic| first
  | decide
  | (have hjd := Kit.n_mem (c := $c)
     try simp only [resultPt, entry, bitsV, tablePt, coordinates, addWork, entryWork, loopWork, work, gSource,
       qSource, arithmeticWork, resultWork, prepWork, slW, Cfg.MP', Cfg.pt, Cfg.sl]
     generalize Cfg.n $c = n at hjd ⊢
     revert n
     decide))

/-- `omega` for a goal in the word count and the number of a table's entry: at
the three word counts. -/
local macro "jo " c:term : tactic => `(tactic|
  (have hjo := Kit.n_mem (c := $c)
   simp only [List.mem_cons, List.not_mem_nil, or_false] at hjo
   rcases hjo with hjo | hjo | hjo <;> simp only [hjo] <;> omega))

variable {c : Cfg} [Kit c]

/-- The number `movz` loads. -/
theorem movz_val {k : Nat} (hk : k < 2 ^ 16) : (BitVec.ofNat 16 k).setWidth 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega


def PointAt (c : Cfg) (base : Addr) (s : State) (p : Pt) (P : Point c.C) : Prop :=
  (∀ o ∈ coordinates p,num c base s o < c.C.p) ∧
  Rep c.C (val c base s p.x) (val c base s p.y) (val c base s p.z) P

structure Changes (base : Addr) (W : List (Nat × Nat)) (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x0
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Unch base W s.mem t.mem

theorem Changes.scr {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : Scr s base 8192) : Scr t base 8192 :=
  ⟨h.x0.trans hs.x0,h.wr ▸ hs.wr,hs.nowrap,hs.enc⟩

theorem Changes.trans {base : Addr} {W : List (Nat × Nat)} {s t u : State}
    (h : Changes base W s t) (k : Changes base W t u) : Changes base W s u :=
  ⟨k.x0.trans h.x0,k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp,(h.mem.trans k.mem).mono (fun _ h => (List.mem_append.mp h).elim id id)⟩

theorem Changes.mono {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : ∀ w ∈ W,w ∈ W') : Changes base W' s t :=
  ⟨h.x0,h.rd,h.wr,h.sp,h.mem.mono hs⟩

theorem Changes.point {base : Addr} {W : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t) (hs : Scr s base 8192) {p : Pt} {P : Point c.C}
    (hp : PointAt c base s p P) (hle : ∀ x ∈ coordinates p,x+8*c.n ≤ 8192)
    (hsep : ∀ x ∈ coordinates p,∀ w ∈ W,x+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ x) :
    PointAt c base t p P := by
  have e (x : Nat) (hx : x ∈ coordinates p) : num c base t x = num c base s x :=
    h.mem.wordsVal (hsep x hx) (by have := hs.nowrap; have := hle x hx; have hn8 := (Kit.n_le c); omega_using [this, hn8])
  refine ⟨fun x hx => Nat.lt_of_le_of_lt (Nat.le_of_eq (e x hx)) (hp.1 x hx),?_⟩
  change Rep c.C (toM _ _ (num c base t p.x)) (toM _ _ (num c base t p.y))
    (toM _ _ (num c base t p.z)) P
  rw [e _ (by simp),e _ (by simp),e _ (by simp)]
  exact hp.2

/-- Complete addition in the three live slots, with the same existing field and curve contracts. -/
theorem sum_points {base : Addr} {s : State} (hc : BaseCfgOk c) (hC : Law c.C)
    (hs : Scr s base 8192) (hm : ModOkA c.MP' 8192 c.C.p s.mem base)
    (ha : val c base s (c.sl AP) = Fin.ofNat c.C.p c.C.a)
    (hb : val c base s (c.sl EXPP) = Fin.ofNat c.C.p (3*c.C.b))
    (hal : num c base s (c.sl AP) < c.C.p) (hbl : num c base s (c.sl EXPP) < c.C.p)
    {P Q : Point c.C} (hP : onCurve c.C P = true) (hQ : onCurve c.C Q = true)
    (hp : PointAt c base s (entry c) P) (hq : PointAt c base s (resultPt c) Q) :
    WP isa (sum c) s fun t =>
      Changes base (addWork c) s t ∧ PointAt c base t (resultPt c) (Spec.Weierstrass.add P Q) ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hi : ∀ i ∈ sumR,sv c base s i < c.C.p := by
    intro i hi
    simp only [sumR,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hal
    · exact hbl
    · exact hp.1 _ (by jd c)
    · exact hp.1 _ (by jd c)
    · exact hp.1 _ (by jd c)
    · exact hq.1 _ (by jd c)
    · exact hq.1 _ (by jd c)
    · exact hq.1 _ (by jd c)
  obtain ⟨trace,t,he,ht,rd,wr,unch,_,bounds,result⟩ := sum_full_ok hc hs hm hi
  refine ⟨trace,t,he,⟨ht.x0.trans hs.x0.symm,rd,wr,VG.AArch64.Exec.sp he,unch⟩,⟨?_,?_⟩,Exec.gpr Kit.sum_counter he⟩
  · intro o ho
    simp only [coordinates,resultPt,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact bounds.2.1
    · exact bounds.2.2
    · exact bounds.1
  · change (val c base t (resultPt c).x,val c base t (resultPt c).y,val c base t (resultPt c).z) =
      rcbAdd (val c base s (c.sl AP)) (val c base s (c.sl EXPP))
        (val c base s (entry c).x) (val c base s (entry c).y) (val c base s (entry c).z)
        (val c base s (resultPt c).x) (val c base s (resultPt c).y) (val c base s (resultPt c).z) at result
    rw [ha,hb] at result
    exact Rep.add hC hP hQ hp.2 hq.2 result.symm

structure CopyLayout (c : Cfg) (o a : Pt) : Prop where
  end_le : ∀ x ∈ coordinates o ++ coordinates a,x+8*c.n ≤ 8192
  aligned : ∀ x ∈ coordinates o ++ coordinates a,x % 8 = 0
  apart : ∀ x ∈ coordinates o,∀ y ∈ coordinates o ++ coordinates a,x ≠ y →
    x+8*c.n ≤ y ∨ y+8*c.n ≤ x
  different : ∀ x ∈ coordinates o,x ∉ coordinates a
  nodup : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z

omit [Kit c] in
theorem copy_point {base : Addr} {s : State} (hs : Scr s base 8192) {a o : Pt}
    (hL : CopyLayout c o a) {P : Point c.C} (hp : PointAt c base s a P) :
    WP isa (.block (copyPt c.n o a)) s fun t =>
      Changes base ((coordinates o).map (·,8*c.n)) s t ∧ PointAt c base t o P ∧
      t.gpr .x19 = s.gpr .x19 := by
  have hle : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x+8*c.n ≤ 8192 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.end_le
  have hal : ∀ x ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x % 8 = 0 := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.aligned
  have hap : ∀ x ∈ [o.x,o.y,o.z],∀ y ∈ [o.x,o.y,o.z,a.x,a.y,a.z],x ≠ y →
      x+8*c.n ≤ y ∨ y+8*c.n ≤ x := by
    simpa only [coordinates,List.cons_append,List.nil_append] using hL.apart
  refine WP.mono (copyPt_ok hs hle hal hap hL.different hL.nodup) fun t ⟨x,y,z,k,u⟩ => ?_
  refine ⟨⟨k.gpr _ (by decide),k.rd,k.wr,k.sp,u⟩,⟨?_,?_⟩,k.gpr _ (by decide)⟩
  · intro p hp'
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · rw [show num c base t o.x = num c base s a.x from x]; exact hp.1 _ (by simp)
    · rw [show num c base t o.y = num c base s a.y from y]; exact hp.1 _ (by simp)
    · rw [show num c base t o.z = num c base s a.z from z]; exact hp.1 _ (by simp)
  · have vx : val c base t o.x = val c base s a.x := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) x
    have vy : val c base t o.y = val c base s a.y := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) y
    have vz : val c base t o.z = val c base s a.z := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) z
    rw [vx,vy,vz]; exact hp.2

theorem entry_from_result : CopyLayout c (entry c) (resultPt c) := ⟨by jd c,by jd c,by jd c,by jd c,by jd c⟩

/-- The all-zero scalar pair starts from the standard projective infinity. -/
theorem infinity_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (hc : BaseCfgOk c) (hC : Law c.C) :
    WP isa (.block (infinity c)) s fun t =>
      Changes base ((coordinates (resultPt c)).map (·,8*c.n)) s t ∧
      PointAt c base t (resultPt c) .infinity ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have hn8 := (Kit.n_le c)
  have hex : (resultPt c).x+8*c.n ≤ 8192 := by jd c
  have hey : (resultPt c).y+8*c.n ≤ 8192 := by jd c
  have hm0 : 0 < c.C.p := by change 0 < c.C.p; have := hc.p_ge; omega_using [this]
  have hm1 : c.mont 1 < c.C.p := Nat.mod_lt _ hm0
  have hm1r : c.mont 1 < 2 ^ (64*c.n) := Nat.lt_trans hm1 hc.p_lt
  rw [infinity,WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n:=c.n) (o:=(resultPt c).x) (x:=0) (by jd c) (by jd c) (Nat.pow_pos (by jd c)))
    fun s₁ ⟨x,k₁,u₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (setConst_ok hs₁ (n:=c.n) (o:=(resultPt c).y) (by jd c) (by jd c) hm1r)
    fun s₂ ⟨y,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=c.n) (o:=(resultPt c).z) (x:=0) (by jd c) (by jd c) (Nat.pow_pos (by jd c)))
    fun t ⟨z,k₃,u₃⟩ => ?_
  have kt := (k₁.trans k₂).trans k₃
  have xt : num c base t (resultPt c).x = 0 := by
    unfold num
    rw [u₃.wordsVal (by jd c) (by have := hs.nowrap; omega_using [hn8, hex]),
      u₂.wordsVal (by jd c) (by have := hs.nowrap; omega_using [hn8, hex])]; exact x
  have yt : num c base t (resultPt c).y = c.mont 1 := by
    unfold num
    rw [u₃.wordsVal (by jd c) (by have := hs.nowrap; omega_using [hn8, hey])]; exact y
  have zt : num c base t (resultPt c).z = 0 := z
  have ut : Unch base ((coordinates (resultPt c)).map (·,8*c.n)) s.mem t.mem :=
    (u₁.unch.trans (u₂.unch.trans u₃.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> jd c)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,ut⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro p hp
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [xt]; exact hm0
    · rw [yt]; exact hm1
    · rw [zt]; exact hm0
  · have vx : val c base t (resultPt c).x = 0 :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) xt).trans (toM_zero _ _)
    have vy : val c base t (resultPt c).y = 1 :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) yt).trans (toM_cmont hc 1)
    have vz : val c base t (resultPt c).z = 0 :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) zt).trans (toM_zero _ _)
    rw [vx,vy,vz]; exact rep_infinity' hC

/-! The constants and affine input points remain unchanged during joint multiplication. -/

theorem Changes.cover {base : Addr} {W W' : List (Nat × Nat)} {s t : State}
    (h : Changes base W s t)
    (hs : ∀ w ∈ W,∃ w' ∈ W',w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2) : Changes base W' s t :=
  ⟨h.x0,h.rd,h.wr,h.sp,h.mem.cover hs⟩

structure Inputs (c : Cfg) (base : Addr) (P Q : Point c.C) (s : State) : Prop where
  scr : Scr s base 8192
  mod : ModOkA c.MP' 8192 c.C.p s.mem base
  a_lt : num c base s (c.sl AP) < c.C.p
  b_lt : num c base s (c.sl EXPP) < c.C.p
  a : val c base s (c.sl AP) = Fin.ofNat c.C.p c.C.a
  b : val c base s (c.sl EXPP) = Fin.ofNat c.C.p (3*c.C.b)
  generator : PointAt c base s (gSource c) P
  peer : PointAt c base s (qSource c) Q

theorem Inputs.unch {base : Addr} {P Q : Point c.C} {s t : State} (h : Inputs c base P Q s)
    (k : Changes base (arithmeticWork c) s t) : Inputs c base P Q t := by
  have hn8 := (Kit.n_le c)
  have en (o : Nat) (hl : o+8*c.n ≤ 8192)
      (hap : ∀ w ∈ (arithmeticWork c),o+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ o) : num c base t o = num c base s o :=
    k.mem.wordsVal hap (by have := h.scr.nowrap; omega_using [hn8, hl])
  have ea := en (c.sl AP) (by jd c) (by jd c)
  have eb := en (c.sl EXPP) (by jd c) (by jd c)
  refine ⟨k.scr h.scr,h.mod.unch k.mem (by jd c) h.scr.nowrap,?_,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact h.a_lt
  · rw [eb]; exact h.b_lt
  · exact (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) ea).trans h.a
  · exact (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) eb).trans h.b
  · exact k.point h.scr h.generator (by jd c) (by jd c)
  · exact k.point h.scr h.peer (by jd c) (by jd c)

omit [Kit c] in
theorem entryWork_sub : ∀ w ∈ (entryWork c),w ∈ (loopWork c) := by
  intro w h; exact List.mem_append_right _ h

omit [Kit c] in
theorem addWork_sub : ∀ w ∈ (addWork c),w ∈ (loopWork c) := by
  intro w h; exact List.mem_append_left _ h

omit [Kit c] in
theorem loopWork_sub : ∀ w ∈ (loopWork c),w ∈ (arithmeticWork c) := by
  intro w h; exact List.mem_append_left _ h

theorem double_points {base : Addr} {P Q A : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hI : Inputs c base P Q s)
    (hA : onCurve c.C A = true) (hp : PointAt c base s (resultPt c) A) :
    WP isa (double c) s fun t => Changes base (loopWork c) s t ∧ Inputs c base P Q t ∧
      PointAt c base t (resultPt c) (add A A) ∧ t.gpr .x19 = s.gpr .x19 := by
  rw [double]
  refine WP.seq (WP.mono (copy_point hI.scr entry_from_result hp) fun s₁ ⟨k₁,p₁,c₁⟩ => ?_)
  have W₁ := k₁.mono entryWork_sub
  have I₁ := hI.unch (W₁.mono loopWork_sub)
  have p₁' := k₁.point hI.scr hp (by jd c) (by jd c)
  refine WP.mono (sum_points hc hC I₁.scr I₁.mod I₁.a I₁.b I₁.a_lt I₁.b_lt hA hA p₁ p₁')
    fun t ⟨k₂,p₂,c₂⟩ => ?_
  have W₂ := k₂.mono addWork_sub
  have W := W₁.trans W₂
  exact ⟨W,hI.unch (W.mono loopWork_sub),p₂,c₂.trans c₁⟩

/-! Reading one public pair of unsigned two-bit digits. -/

abbrev Bits (c : Cfg) (base : Addr) (u v : Nat) (s : State) : Prop :=
  (∀ t < 64*c.n,s.mem (off base (bitsU+t)) = if u.testBit t then 1 else 0) ∧
  (∀ t < 64*c.n,s.mem (off base ((bitsV c)+t)) = if v.testBit t then 1 else 0)

def digitPair (u v j : Nat) : Nat := (u >>> (2*j)) % 4 + 4*((v >>> (2*j)) % 4)

theorem digitPair_lt (u v j : Nat) : digitPair u v j < 16 := by
  unfold digitPair; omega_using []

theorem Changes.bits {base : Addr} {u v : Nat} {s t : State}
    (h : Changes base (arithmeticWork c) s t) (hb : Bits c base u v s) : Bits c base u v t := by
  have apart : ∀ b ∈ [bitsU,(bitsV c)],∀ j < 64*c.n,∀ w ∈ (arithmeticWork c),
      b+j+1 ≤ w.1 ∨ w.1+w.2 ≤ b+j := by
    intro b h j hj w hw
    have hd : ∀ b ∈ [bitsU,(bitsV c)],∀ w ∈ (arithmeticWork c),b+64*c.n ≤ w.1 ∨ w.1+w.2 ≤ b := by jd c
    have := hd b h w hw; omega_using [hj, this]
  constructor
  · intro j hj
    rw [h.mem.byte (apart bitsU (by simp) j hj) (by have := (Kit.n_le c); change 2944+j < 2^64; omega_using [hj, this])]
    exact hb.1 j hj
  · intro j hj
    rw [h.mem.byte (apart (bitsV c) (by simp) j hj) (by have := (Kit.n_le c); change (2944+64*c.n)+j < 2^64; omega_using [hj, this])]
    exact hb.2 j hj

theorem index2_ok {s : State} {base : Addr} (hs : Scr s base 8192) {j : Nat}
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.lsl .x .x16 .x19 1,.add .x .x16 .x0 .x16]) s fun t =>
      t.gpr .x16 = off base (2*j) ∧ Keeps [.x16] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 1 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hx,hs.x0,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 64 j * BitVec.ofNat 64 2 = base + BitVec.ofNat 64 (2*j)
    rw [←BitVec.ofNat_mul,Nat.mul_comm j 2]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

omit [Kit c] in
theorem read2_ok {base : Addr} {s : State} (hs : Scr s base 8192) {bits k j : Nat}
    (hbits : bits+64*c.n ≤ 8192) (henc : bits+2 ≤ 4096) (hj : j < 32*c.n)
    (h16 : s.gpr .x16 = off base (2*j))
    (hb : ∀ t < 64*c.n,s.mem (off base (bits+t)) = if k.testBit t then 1 else 0) :
    WP isa (.block (hornerBits bits 2)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 ((k >>> (2*j)) % 4) ∧ Keeps [.x2,.x4] s t := by
  have hv : ∀ i,(k.testBit (2*j+(i-bits))).toNat ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 2 bits (s:=s) (by decide) henc fun i hi => ?_)
    fun t ⟨v,h⟩ => ⟨?_,h⟩
  · have e : s.gpr .x16+BitVec.ofNat 64 (bits+i) = off base (bits+(2*j+i)) := by
      rw [h16,off,off,BitVec.add_assoc,←BitVec.ofNat_add]
      exact congrArg (base+·) (congrArg _ (by omega_using []))
    refine ⟨?_,?_⟩
    · rw [e]; exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hbits, hj, hi]) (by decide)⟩
    · rw [e,hb _ (by omega_using [hj, hi]),show bits+i-bits=i by omega_using []]
      cases k.testBit (2*j+i) <;> rfl
  · have he : hornerVal (fun i => (k.testBit (2*j+(i-bits))).toNat) bits 2 = combWin 2 k j := by
      have hh := hornerVal_eq k 2 j 2 (Nat.le_refl _)
      rw [Nat.sub_self,Nat.add_zero] at hh
      rw [combWin,←hh]
      exact hornerVal_congr fun i _ => by simp only [show bits+i-bits=i by omega_using []]
    rw [v,he,combWin,Nat.shiftRight_eq_div_pow]

theorem save_digit_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x2 0]) s fun t => t.gpr .x6=s.gpr .x2 ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show (0 : Nat) < 4096 by decide,BitVec.setWidth_eq,BitVec.add_zero,ite_true,
    Option.some.injEq,exists_eq_left']
  refine ⟨True.intro,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

theorem combine_ok (s : State) {a b : Nat}
    (h6 : s.gpr .x6=BitVec.ofNat 64 a) (h2 : s.gpr .x2=BitVec.ofNat 64 b) :
    WP isa (.block [.lsl .x .x2 .x2 2,.add .x .x2 .x2 .x6]) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (a+4*b) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 2 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h6,h2,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 b*BitVec.ofNat 64 4+BitVec.ofNat 64 a=BitVec.ofNat 64 (a+4*b)
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega_using [])
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

theorem digit_ok {base : Addr} {s : State} (hs : Scr s base 8192) {u v j : Nat}
    (hb : Bits c base u v s) (hj : j < 32*c.n) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block (digit c)) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t := by
  rw [digit]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (index2_ok hs h19) fun s₁ ⟨p₁,k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (read2_ok (hs.of_keeps k₁ (by jd c)) (bits:=bitsU) (k:=u) (by jd c) (by jd c) hj p₁
    (by rw [k₁.mem]; exact hb.1)) fun s₂ ⟨v₂,k₂⟩ => ?_
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (save_digit_ok s₂) fun s₃ ⟨v₃,k₃⟩ => ?_
  rw [WP.block_append_iff]
  have hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have p₃ : s₃.gpr .x16=off base (2*j) := by rw [k₃.gpr _ (by decide),k₂.gpr _ (by decide),p₁]
  refine WP.mono (read2_ok hs₃ (bits:=(bitsV c)) (k:=v) (by jd c) (by jd c) hj p₃
    (by rw [k₃.mem,k₂.mem,k₁.mem]; exact hb.2)) fun s₄ ⟨v₄,k₄⟩ => ?_
  have e₆ : s₄.gpr .x6=BitVec.ofNat 64 ((u >>> (2*j)) % 4) := by rw [k₄.gpr _ (by decide),v₃,v₂]
  refine WP.mono (combine_ok s₄ e₆ v₄) fun t ⟨v₅,k₅⟩ => ?_
  exact ⟨v₅,((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))⟩

/-! Copies through the joint table's public entry pointer. -/

theorem word_at_offset (m : Mem) (base : Addr) (a b : Nat) :
    word m (off base a) b = word m base (a+b) := by
  unfold word off
  rw [VG.Offset.add_add]

theorem source_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    Ptr s .x16 (off base a) (size-a) where
  reg := hr
  enc := by have := hs.enc; omega
  ld d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,List.mem_append_right _ hs.wr,hs.contains (by omega_using [hd]) (by decide)⟩

/-- The selected entry is above or wholly below the destination. -/
theorem copyFrom_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a src dst : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    dst + 8*n ≤ size → a + src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (dst + 8*n ≤ a + src ∨ a + src + 8*n ≤ dst) →
    WP isa (.block (copyFrom n dst src)) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base (a+src) n ∧
      KeepRegs [.x4] s t ∧ Outside base dst (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, src, dst, hs, hr, hd, ha, hd8, hs8, hsep => by
    have hn := hs.nowrap
    have hp := source_ptr hs (by omega_using [ha] : a ≤ size) hr
    rw [copyFrom,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d:=src) (by omega_using [ha]) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    rw [word_at_offset] at e₀
    have hs₀ := hs.of_keeps k₀ (by decide)
    refine WP.mono (st_out hs₀ (o:=dst) (by omega_using [hd]) hd8 .x4) fun s₁ ⟨m₁,k₁,g₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    have k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    have hs₁ := hs.of_keepRegs k₀₁ (by decide)
    have O₁ : Outside base dst 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hd, hn])
    have hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    have e₁ : wordsVal s₁.mem base (a+src+8) n = wordsVal s.mem base (a+src+8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [ha, hn])
    refine WP.mono (copyFrom_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega_using [hd]) (by omega_using [ha]) (by omega_using [hd8]) (by omega_using [hs8]) (by omega_using [hsep])) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega_using [hx]),O₁ x (by omega_using [hx])]⟩
    rw [show a+(src+8)=a+src+8 by omega_using []] at e₂
    rw [wordsVal,O₂.word (by omega_using []) (by omega_using [hd, hn]),m₁,word_writeW_self,e₂,e₁,wordsVal]

/-! The fifteen projective table entries fit beside the existing arithmetic workspace. -/

theorem resultWork_sub : ∀ w ∈ (resultWork c),w ∈ (loopWork c) := by jd c

theorem table_coord_bounds {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ x ∈ coordinates (tablePt c d),tableAt ≤ x ∧ x+8*c.n ≤ (5280+360*c.n) ∧ x % 8 = 0 := by
  intro x hx
  change 5280 ≤ x ∧ x+8*c.n ≤ (5280+360*c.n) ∧ x % 8 = 0
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by jo c,by jo c,by jo c⟩

theorem tableWork_cover {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ w ∈ (coordinates (tablePt c d)).map (·,8*c.n),
      ∃ w' ∈ (arithmeticWork c),w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2 := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  have h := table_coord_bounds h1 h15 x hx
  exact ⟨(tableAt,360*c.n),List.mem_append_right _ (by simp),h.1,h.2.1⟩

theorem Changes.table {base : Addr} {s t : State} (h : Changes base (loopWork c) s t)
    (hs : Scr s base 8192) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    {P : VG.Spec.Weierstrass.Point c.C} (hp : PointAt c base s (tablePt c d) P) :
    PointAt c base t (tablePt c d) P := by
  refine h.point hs hp (fun x hx => Nat.le_trans (table_coord_bounds h1 h15 x hx).2.1 (by jd c)) ?_
  intro x hx w hw
  have hb := (table_coord_bounds h1 h15 x hx).1
  have hh : ∀ w ∈ (loopWork c),w.1+w.2 ≤ tableAt := by jd c
  exact Or.inr (Nat.le_trans (hh w hw) hb)

omit [Kit c] in
theorem earlier_table_apart {j d : Nat} (hj : 1 ≤ j) (hjd : j < d) :
    ∀ x ∈ coordinates (tablePt c j),∀ w ∈ (coordinates (tablePt c d)).map (·,8*c.n),
      x+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  have key : 24*c.n*(j-1)+24*c.n ≤ 24*c.n*(d-1) := by
    rw [←Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> exact Or.inl (by omega_using [key])

/-! Building the joint digit-pair table with the existing complete addition. -/

abbrev Table (c : Cfg) (base : Addr) (P Q : Point c.C) (m : Nat) (s : State) : Prop :=
  ∀ d,1 ≤ d → d ≤ m → PointAt c base s (tablePt c d) (pair P Q (d%4) (d/4))

/-- What `setupWith` needs of the table's program. -/
abbrev BuildOk (c : Cfg) (build : Prog isa) : Prop :=
  ∀ {base : Addr} {P Q : Point c.C} {s : State}, BaseCfgOk c → Law c.C → onCurve c.C P=true → onCurve c.C Q=true →
    Inputs c base P Q s → WP isa build s fun t =>
      Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q 15 t

theorem entry_from_generator : CopyLayout c (entry c) (gSource c) := ⟨by jd c,by jd c,by jd c,by jd c,by jd c⟩
theorem entry_from_peer : CopyLayout c (entry c) (qSource c) := ⟨by jd c,by jd c,by jd c,by jd c,by jd c⟩

/-! Public lookup of a nonzero digit pair, with all pointer bounds checked. -/

theorem fetchHead_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d) :
    WP isa (.block (fetchHead c)) s fun t =>
      t.gpr .x16 = off base (tablePt c d).x ∧ Keeps [.x2,.x16,.x17] s t := by
  have hsub : BitVec.ofNat 64 d - 1 = BitVec.ofNat 64 (d-1) := by
    apply BitVec.eq_of_toNat_eq
    change (2^64-1+d%(2^64))%(2^64)=(d-1)%(2^64)
    omega
  apply WP.of_runBlock
  simp only [fetchHead,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat) < 4096 by decide,show 16*0 < Size.x.bits by decide,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,h2,hs.x0,
    Nat.mul_zero,BitVec.shiftLeft_zero,
    movz_val (k:=24*c.n) (by have := (Kit.n_le c); omega),
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change base+BitVec.ofNat 64 5280+(BitVec.ofNat 64 d-1)*BitVec.ofNat 64 (24*c.n) = off base (tablePt c d).x
    rw [hsub,←BitVec.ofNat_mul]
    change base+BitVec.ofNat 64 5280+BitVec.ofNat 64 ((d-1)*(24*c.n))=
      base+BitVec.ofNat 64 (5280+24*c.n*(d-1))
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (base+·) (congrArg (BitVec.ofNat 64) (by rw [Nat.mul_comm (d-1)]))
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem fetch_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point c.C} (hp : PointAt c base s (tablePt c d) P) :
    WP isa (.block (fetch c)) s fun t =>
      Changes base (entryWork c) s t ∧ PointAt c base t (entry c) P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  have ex_bound : (entry c).x+8*c.n ≤ 8192 := by jd c
  have ey_bound : (entry c).y+8*c.n ≤ 8192 := by jd c
  have htab := table_coord_bounds (c := c) h1 h15
  have ha : (tablePt c d).x+24*c.n ≤ 8192 := by
    have hb := (htab (tablePt c d).z (by simp)).2.1
    change _+8*c.n ≤ (5280+360*c.n) at hb
    dsimp only [tablePt] at hb ⊢; have := (Kit.n_le c); omega_using [hb, this]
  have hab : (tablePt c d).x ≤ 8192 := by omega_using [ha]
  have hsep : ∀ e ∈ coordinates (entry c),e+8*c.n ≤ (tablePt c d).x := by
    have hh : ∀ e ∈ coordinates (entry c),e+8*c.n ≤ tableAt := by jd c
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  have sepX := hsep (entry c).x (by jd c)
  have sepY := hsep (entry c).y (by jd c)
  have sepZ := hsep (entry c).z (by jd c)
  rw [fetch]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok c.n hs₁ p₁ (a:=(tablePt c d).x) (src:=0) (dst:=(entry c).x)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by simpa using hsep _ (by simp))))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok c.n hs₂ p₂ (a:=(tablePt c d).x) (src:=8*c.n) (dst:=(entry c).y)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by omega_using [sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok c.n hs₃ p₃ (a:=(tablePt c d).x) (src:=16*c.n) (dst:=(entry c).z)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by omega_using [sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  have e_x : num c base t (entry c).x = num c base s (tablePt c d).x := by
    change wordsVal t.mem base (entry c).x c.n = wordsVal s.mem base (tablePt c d).x c.n
    rw [u₄.wordsVal (by jd c) (by omega_using [ex_bound]),
      u₃.wordsVal (by jd c) (by omega_using [ex_bound]),x,k₁.mem]
    rfl
  have e_y : num c base t (entry c).y = num c base s (tablePt c d).y := by
    change wordsVal t.mem base (entry c).y c.n = wordsVal s.mem base (tablePt c d).y c.n
    rw [u₄.wordsVal (by jd c) (by omega_using [ey_bound]),y]
    rw [u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  have e_z : num c base t (entry c).z = num c base s (tablePt c d).z := by
    change wordsVal t.mem base (entry c).z c.n = wordsVal s.mem base (tablePt c d).z c.n
    rw [z,u₃.wordsVal (Or.inr (by omega_using [sepY])) (by omega_using [ha]),
      u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  have kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  have u : Unch base (entryWork c) s.mem t.mem := by
    rw [←k₁.mem]
    exact (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> jd c)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_x
    have ey := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_y
    have ez := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_z
    change val c base t (entry c).x = val c base s (tablePt c d).x at ex
    change val c base t (entry c).y = val c base s (tablePt c d).y at ey
    change val c base t (entry c).z = val c base s (tablePt c d).z at ez
    rw [ex,ey,ez]; exact hp.2

/-! A public digit addition, including the zero-pair case. -/

theorem Changes.of_keeps {base : Addr} {W : List (Nat × Nat)} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (h0 : .x0 ∉ rs) : Changes base W s t :=
  ⟨h.gpr _ h0,h.rd,h.wr,h.sp,fun _ _ => congrFun h.mem _⟩

omit [Kit c] in
theorem PointAt.of_mem {base : Addr} {s t : State} {p : Pt} {P : Point c.C}
    (hp : PointAt c base s p P) (he : t.mem=s.mem) : PointAt c base t p P := by
  simpa only [PointAt,num,val,tmv,he] using hp

theorem Table.of_changes {base : Addr} {s t : State} {P Q : Point c.C}
    (ht : Table c base P Q 15 s) (hs : Scr s base 8192) (h : Changes base (loopWork c) s t) :
    Table c base P Q 15 t := fun d h1 h15 => h.table hs h1 h15 (ht d h1 h15)

theorem zero_test {s : State} {d : Nat} (hd : d < 16) (h2 : s.gpr .x2=BitVec.ofNat 64 d) :
    eval (.zero .x .x2) s=some (decide (d=0)) := by
  change some (s.read .x .x2 == 0)=_
  rw [read_x,h2]
  by_cases hz : d=0
  · rw [hz]; rfl
  · have hn : BitVec.ofNat 64 d ≠ 0 := by
      intro he
      have h := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [hd])] at h
      exact hz h
    rw [decide_eq_false hz,beq_eq_false_iff_ne.mpr hn]

theorem addDigit_ok {base : Addr} {P Q A : Point c.C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (hA : onCurve c.C A=true) (hi : Inputs c base P Q s) (hb : Bits c base u v s)
    (ht : Table c base P Q 15 s) (hp : PointAt c base s (resultPt c) A) (hj : j < 32*c.n)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (addDigit c) s fun t => Changes base (loopWork c) s t ∧ Inputs c base P Q t ∧
      Bits c base u v t ∧ Table c base P Q 15 t ∧
      PointAt c base t (resultPt c) (add (pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)) A) ∧
      t.gpr .x19=s.gpr .x19 := by
  rw [addDigit, digitTail]
  refine WP.seq (WP.mono (digit_ok hi.scr hb hj h19) fun s₁ ⟨d₁,k₁⟩ => ?_)
  have W₁ : Changes base (loopWork c) s s₁ := Changes.of_keeps k₁ (by decide)
  have I₁ := hi.unch (W₁.mono loopWork_sub)
  have B₁ := (W₁.mono loopWork_sub).bits hb
  have T₁ := ht.of_changes hi.scr W₁
  have R₁ := hp.of_mem k₁.mem
  let d := digitPair u v j
  have hd : d < 16 := digitPair_lt u v j
  have hda : d%4=(u >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  have hdb : d/4=(v >>> (2*j))%4 := by dsimp only [d,digitPair]; omega_using []
  refine WP.ite (decide (d=0)) (zero_test hd d₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : d=0 := of_decide_eq_true hz
    have ha0 : (u >>> (2*j))%4=0 := by rw [hz'] at hda; omega_using [hda]
    have hb0 : (v >>> (2*j))%4=0 := by rw [hz'] at hdb; omega_using [hdb]
    have ep : pair P Q ((u >>> (2*j))%4) ((v >>> (2*j))%4)=.infinity := by
      rw [ha0,hb0]; exact pair_zero P Q
    rw [ep]
    exact WP.block_nil ⟨W₁,I₁,B₁,T₁,R₁,k₁.gpr _ (by decide)⟩
  · have hn' : d≠0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (fetch_ok I₁.scr (by omega) (by omega) d₁ (T₁ d (by omega_using [hn']) (by omega_using [hd])))
      fun s₂ ⟨k₂,E₂,c₂⟩ => ?_)
    have W₂ := W₁.trans (k₂.mono entryWork_sub)
    have I₂ := hi.unch (W₂.mono loopWork_sub)
    have R₂ := k₂.point I₁.scr R₁ (by jd c) (by jd c)
    rw [hda,hdb] at E₂
    refine WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt
      (pair_curve hC hP hQ _ _) hA E₂ R₂) fun t ⟨k₃,R₃,c₃⟩ => ?_
    have W := W₂.trans (k₃.mono addWork_sub)
    exact ⟨W,hi.unch (W.mono loopWork_sub),(W.mono loopWork_sub).bits hb,
      ht.of_changes hi.scr W,R₃,c₃.trans (c₂.trans (k₁.gpr _ (by decide)))⟩

/-! One shared Horner loop advances both public verification scalars. -/

structure Running (c : Cfg) (base : Addr) (P Q : Point c.C) (u v j : Nat) (s : State) : Prop where
  inputs : Inputs c base P Q s
  bits : Bits c base u v s
  table : Table c base P Q 15 s
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  point : PointAt c base s (resultPt c) (stage P Q u v j)

theorem step_ok {base : Addr} {P Q : Point c.C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 32*c.n) (h : Running c base P Q u v j s) :
    WP isa (step c) s fun t => Changes base (loopWork c) s t ∧ Running c base P Q u v (j-1) t := by
  rw [step]
  have hn8 := (Kit.n_le c)
  refine WP.seq (WP.mono (decCounter_ok s h1 (by omega_using [h256, hn8]) h.counter) fun s₀ ⟨c₀,k₀⟩ => ?_)
  have W₀ : Changes base (loopWork c) s s₀ := Changes.of_keeps k₀ (by decide)
  have I₀ := h.inputs.unch (W₀.mono loopWork_sub)
  have R₀ := h.point.of_mem k₀.mem
  have hA : onCurve c.C (stage P Q u v j)=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (double_points hc hC I₀ hA R₀) fun s₁ ⟨k₁,I₁,R₁,c₁⟩ => ?_)
  refine WP.seq (WP.mono (double_points hc hC I₁ (hC.onCurve_add hA hA) R₁) fun s₂ ⟨k₂,I₂,R₂,c₂⟩ => ?_)
  have W₂ := (W₀.trans k₁).trans k₂
  have B₂ := (W₂.mono loopWork_sub).bits h.bits
  have T₂ := h.table.of_changes h.inputs.scr W₂
  have C₂ : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := c₂.trans (c₁.trans c₀)
  have hAA := hC.onCurve_add hA hA
  refine WP.mono (addDigit_ok hc hC hP hQ (hC.onCurve_add hAA hAA) I₂ B₂ T₂ R₂
    (by omega_using [h256, h1]) C₂) fun t ⟨k₃,I₃,B₃,T₃,R₃,c₃⟩ => ?_
  have eqj : j-1+1=j := by omega_using [h1]
  have em := at_step hC hP hQ u v (j-1)
  rw [eqj] at em
  have hcmt := point_comm hC
    (pair_curve hC hP hQ ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
    (hC.onCurve_add hAA hAA)
  have final : add (pair P Q ((u >>> (2*(j-1)))%4) ((v >>> (2*(j-1)))%4))
      (add (add (stage P Q u v j) (stage P Q u v j))
        (add (stage P Q u v j) (stage P Q u v j))) = stage P Q u v (j-1) := hcmt.trans em
  rw [final] at R₃
  exact ⟨W₂.trans k₃,⟨I₃,B₃,T₃,c₃.trans C₂,R₃⟩⟩

theorem loop_ok {m : Nat} (hm : Rounds c m) {base : Addr} {P Q : Point c.C} {u v : Nat} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (h : Running c base P Q u v (32*m) s) :
    WP isa (.loop (step c) (.nonzero .x .x19)) s fun t =>
      Changes base (loopWork c) s t ∧ Running c base P Q u v 0 t := by
  let inv := fun j t => Changes base (loopWork c) s t ∧ Running c base P Q u v j t
  refine countLoop_ok (Inv:=inv) (n:=32*m) (by have := hm.le; have := Kit.n_le c; omega)
    (fun j t h1 h256 ⟨k,hi⟩ => ?_) (fun _ h => h) (Nat.mul_pos (by decide) hm.pos) ⟨⟨rfl,rfl,rfl,rfl,Unch.refl _ _ _⟩,h⟩
  exact WP.mono (step_ok hc hC hP hQ h1 (Nat.le_trans h256 (Nat.mul_le_mul_left 32 hm.le)) hi) fun u ⟨k',hi'⟩ => ⟨⟨k.trans k',hi'⟩,hi'.counter⟩

/-! Building the joint digit-pair table in a loop over its entries, with one complete addition. -/

theorem indexFrom_ok (s : State) {k j : Nat} (hk : k < 2^16) (hj : j ≤ k)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (indexFrom k)) s fun t =>
      t.gpr .x2 = BitVec.ofNat 64 (k-j) ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [indexFrom,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 16*0 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h19,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero,BitVec.shiftLeft_zero,BitVec.toNat_sub,BitVec.toNat_setWidth,
      BitVec.toNat_ofNat,show Size.x.bits = 64 from rfl]
    omega_using [hk, hj]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

/-- What `rowTest` leaves in `x2`. -/
def rowVal (j : Nat) : BitVec 64 := (BitVec.ofNat 64 j &&& 3) ^^^ 3

theorem rowVal_zero : ∀ j < 15, (rowVal j = 0) = ((15-j) % 4 = 0) := by decide

theorem rowTest_ok (s : State) {j : Nat} (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block rowTest) s fun t => t.gpr .x2 = rowVal j ∧ Keeps [.x2,.x5] s t := by
  apply WP.of_runBlock
  simp only [rowTest,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    show 16*0 < Size.x.bits by decide,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,h19,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

/-- A pointer into the working space the copies store through. -/
theorem dest_ptr {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size)
    (ha : a ≤ size) (hr : s.gpr .x16 = off base a) :
    PtrW s .x16 (off base a) (size-a) where
  reg := hr
  st d hd := by
    rw [VG.Offset.add_add]
    exact ⟨_,hs.wr,hs.contains (by omega) (by decide)⟩
  enc := by have := hs.enc; omega_using [this]
  nowrap := by
    have := hs.nowrap
    unfold off
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega_using [this]

theorem stR_out {s : State} {base : Addr} {size a : Nat} (hs : Scr s base size) (ha : a ≤ size)
    (hr : s.gpr .x16 = off base a) {d : Nat} (hd : a + d + 8 ≤ size) (hd8 : d % 8 = 0) (t : Reg) :
    WP isa (.block [.str .x t .x16 d]) s fun s' =>
      s'.mem = s.mem.writeW (off base (a+d)) (s.gpr t) ∧ KeepRegs [] s s' :=
  WP.mono (stR_ok (dest_ptr hs ha hr) (d:=d) (by omega_using [hd]) hd8 t) fun s' e => by
    subst e
    refine ⟨?_,⟨fun _ _ => rfl,rfl,rfl,rfl⟩⟩
    show s.mem.writeW (off (off base a) d) _ = _
    unfold off
    rw [VG.Offset.add_add]

/-- The destination is above or wholly below the source. -/
theorem copyTo_ok {size : Nat} : ∀ (n : Nat) {s : State} {base : Addr} {a dst src : Nat},
    Scr s base size → s.gpr .x16 = off base a →
    a + dst + 8*n ≤ size → src + 8*n ≤ size → dst % 8 = 0 → src % 8 = 0 →
    (a + dst + 8*n ≤ src ∨ src + 8*n ≤ a + dst) →
    WP isa (.block (copyTo n dst src)) s fun t =>
      wordsVal t.mem base (a+dst) n = wordsVal s.mem base src n ∧
      KeepRegs [.x4] s t ∧ Outside base (a+dst) (8*n) s.mem t.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Outside.refl _ _ _ _⟩
  | n+1, s, base, a, dst, src, hs, hr, hd, hsrc, hd8, hs8, hsep => by
    have hn := hs.nowrap
    rw [copyTo,WP.block_append_iff,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ld_ok hs (d:=src) (by omega_using [hsrc]) hs8 .x4) fun s₀ ⟨e₀,k₀,_⟩ => ?_
    obtain hs₀ := hs.of_keeps k₀ (by decide)
    obtain hr₀ : s₀.gpr .x16 = off base a := (k₀.gpr .x16 (by decide)).trans hr
    refine WP.mono (stR_out hs₀ (by omega_using [hd] : a ≤ size) hr₀ (d:=dst) (by omega_using [hd]) hd8 .x4)
      fun s₁ ⟨m₁,k₁⟩ => ?_
    rw [e₀,k₀.mem] at m₁
    obtain k₀₁ : KeepRegs [.x4] s s₁ := (Keeps.regs k₀).trans (k₁.mono (by simp))
    obtain hs₁ := hs.of_keepRegs k₀₁ (by decide)
    obtain O₁ : Outside base (a+dst) 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hd, hn])
    obtain hr₁ : s₁.gpr .x16 = off base a := (k₀₁.gpr .x16 (by decide)).trans hr
    obtain e₁ : wordsVal s₁.mem base (src+8) n = wordsVal s.mem base (src+8) n :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [hsrc, hn])
    refine WP.mono (copyTo_ok n hs₁ hr₁ (dst:=dst+8) (src:=src+8)
      (by omega_using [hd]) (by omega_using [hsrc]) (by omega_using [hd8]) (by omega_using [hs8]) (by omega_using [hsep])) fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
    rw [show a+(dst+8)=a+dst+8 by omega_using []] at e₂ O₂
    refine ⟨?_,k₀₁.trans k₂,fun x hx => by rw [O₂ x (by omega_using [hx]),O₁ x (by omega_using [hx])]⟩
    rw [wordsVal,O₂.word (by omega_using []) (by omega_using [hd, hn]),m₁,word_writeW_self,e₂,e₁,wordsVal]

/-- Entry `d` of the table into the result, as `fetch_ok` into the entry. -/
theorem load_ok {base : Addr} {s : State} (hs : Scr s base 8192) {d : Nat}
    (h1 : 1 ≤ d) (h15 : d ≤ 15) (h2 : s.gpr .x2 = BitVec.ofNat 64 d)
    {P : VG.Spec.Weierstrass.Point c.C} (hp : PointAt c base s (tablePt c d) P) :
    WP isa (.block ((fetchHead c) ++ copyFrom c.n (resultPt c).x 0 ++ copyFrom c.n (resultPt c).y (8*c.n) ++
        copyFrom c.n (resultPt c).z (16*c.n))) s fun t =>
      Changes base (resultWork c) s t ∧ PointAt c base t (resultPt c) P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  obtain htab := table_coord_bounds (c := c) h1 h15
  obtain ha : (tablePt c d).x+24*c.n ≤ 8192 := by
    obtain hb := (htab (tablePt c d).z (by simp)).2.1
    change _+8*c.n ≤ (5280+360*c.n) at hb
    dsimp only [tablePt] at hb ⊢; have := (Kit.n_le c); omega_using [hb, this]
  obtain hsep : ∀ e ∈ coordinates (resultPt c),e+8*c.n ≤ (tablePt c d).x := by
    obtain hh : ∀ e ∈ coordinates (resultPt c),e+8*c.n ≤ tableAt := by jd c
    intro e he; exact Nat.le_trans (hh e he) (htab _ (by simp)).1
  obtain sepX := hsep (resultPt c).x (by jd c)
  obtain sepY := hsep (resultPt c).y (by jd c)
  obtain sepZ := hsep (resultPt c).z (by jd c)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs h1 h15 h2) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok c.n hs₁ p₁ (a:=(tablePt c d).x) (src:=0) (dst:=(resultPt c).x)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by omega_using [sepX])))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyFrom_ok c.n hs₂ p₂ (a:=(tablePt c d).x) (src:=8*c.n) (dst:=(resultPt c).y)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by omega_using [sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyFrom_ok c.n hs₃ p₃ (a:=(tablePt c d).x) (src:=16*c.n) (dst:=(resultPt c).z)
    (by jd c) (by omega_using [ha]) (by jd c) (by jd c) (Or.inl (by omega_using [sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  obtain dx : (resultPt c).x + 8*c.n ≤ (resultPt c).y := by jd c
  obtain dy : (resultPt c).y + 8*c.n ≤ (resultPt c).z := by jd c
  obtain e_x : num c base t (resultPt c).x = num c base s (tablePt c d).x := by
    change wordsVal t.mem base (resultPt c).x c.n = wordsVal s.mem base (tablePt c d).x c.n
    rw [u₄.wordsVal (by omega_using [dx, dy]) (by omega_using [ha, sepX]),
      u₃.wordsVal (by omega_using [dx]) (by omega_using [ha, sepX]),x,k₁.mem]
    rfl
  obtain e_y : num c base t (resultPt c).y = num c base s (tablePt c d).y := by
    change wordsVal t.mem base (resultPt c).y c.n = wordsVal s.mem base (tablePt c d).y c.n
    rw [u₄.wordsVal (by omega_using [dy]) (by omega_using [ha, sepY]),y]
    rw [u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  obtain e_z : num c base t (resultPt c).z = num c base s (tablePt c d).z := by
    change wordsVal t.mem base (resultPt c).z c.n = wordsVal s.mem base (tablePt c d).z c.n
    rw [z,u₃.wordsVal (Or.inr (by omega_using [sepY])) (by omega_using [ha]),
      u₂.wordsVal (Or.inr (by omega_using [sepX])) (by omega_using [ha]),k₁.mem]
    rfl
  obtain kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    ((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))).trans (k₄.mono (by decide))
  obtain u : Unch base (resultWork c) s.mem t.mem := by
    rw [←k₁.mem]
    exact (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> jd c)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_x
    obtain ey := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_y
    obtain ez := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_z
    change val c base t (resultPt c).x = val c base s (tablePt c d).x at ex
    change val c base t (resultPt c).y = val c base s (tablePt c d).y at ey
    change val c base t (resultPt c).z = val c base s (tablePt c d).z at ez
    rw [ex,ey,ez]; exact hp.2

/-- The result into entry `15 - j` of the table. -/
theorem storeEntry_ok {base : Addr} {s : State} (hs : Scr s base 8192) {j : Nat} (hj : j < 15)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) {P : VG.Spec.Weierstrass.Point c.C}
    (hp : PointAt c base s (resultPt c) P) :
    WP isa (.block (storeEntry c)) s fun t =>
      Changes base ((coordinates (tablePt c (15-j))).map (·,8*c.n)) s t ∧
      PointAt c base t (tablePt c (15-j)) P ∧ t.gpr .x19 = s.gpr .x19 := by
  have hn := hs.nowrap
  obtain h1 : 1 ≤ 15-j := by omega_using [hj]
  obtain h15 : 15-j ≤ 15 := by omega_using []
  obtain htab := table_coord_bounds (c := c) h1 h15
  obtain hlo := (htab (tablePt c (15-j)).x (by simp)).1
  obtain ha : (tablePt c (15-j)).x+24*c.n ≤ 8192 := by
    obtain hb := (htab (tablePt c (15-j)).z (by simp)).2.1
    change _+8*c.n ≤ (5280+360*c.n) at hb
    dsimp only [tablePt] at hb ⊢; have := (Kit.n_le c); omega_using [hb, this]
  have ey : (tablePt c (15-j)).y = (tablePt c (15-j)).x + 8*c.n := rfl
  have ez : (tablePt c (15-j)).z = (tablePt c (15-j)).x + 16*c.n := rfl
  obtain hr : ∀ e ∈ coordinates (resultPt c),e+8*c.n ≤ tableAt := by jd c
  obtain sepX := hr (resultPt c).x (by jd c)
  obtain sepY := hr (resultPt c).y (by jd c)
  obtain sepZ := hr (resultPt c).z (by jd c)
  have hta : tableAt = 5280 := rfl
  simp only [storeEntry,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (indexFrom_ok s (k:=15) (by decide) (by omega_using [hj]) h19) fun s₀ ⟨v₀,k₀⟩ => ?_
  obtain hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (fetchHead_ok hs₀ h1 h15 v₀) fun s₁ ⟨p₁,k₁⟩ => ?_
  obtain hs₁ := hs₀.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok c.n hs₁ p₁ (a:=(tablePt c (15-j)).x) (dst:=0) (src:=(resultPt c).x)
    (by omega_using [ha]) (by jd c) (by jd c) (by jd c) (Or.inr (by omega_using [hlo, sepX])))
    fun s₂ ⟨x,k₂,u₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain p₂ := (k₂.gpr .x16 (by decide)).trans p₁
  rw [WP.block_append_iff]
  refine WP.mono (copyTo_ok c.n hs₂ p₂ (a:=(tablePt c (15-j)).x) (dst:=8*c.n) (src:=(resultPt c).y)
    (by omega_using [ha]) (by jd c) (by jd c) (by jd c) (Or.inr (by omega_using [hlo, sepY])))
    fun s₃ ⟨y,k₃,u₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain p₃ := (k₃.gpr .x16 (by decide)).trans p₂
  refine WP.mono (copyTo_ok c.n hs₃ p₃ (a:=(tablePt c (15-j)).x) (dst:=16*c.n) (src:=(resultPt c).z)
    (by omega_using [ha]) (by jd c) (by jd c) (by jd c) (Or.inr (by omega_using [hlo, sepZ])))
    fun t ⟨z,k₄,u₄⟩ => ?_
  obtain m₁ : s₁.mem = s.mem := k₁.mem.trans k₀.mem
  obtain e_x : num c base t (tablePt c (15-j)).x = num c base s (resultPt c).x := by
    change wordsVal t.mem base (tablePt c (15-j)).x c.n = wordsVal s.mem base (resultPt c).x c.n
    rw [u₄.wordsVal (by omega_using []) (by omega_using [ha]),u₃.wordsVal (by omega_using []) (by omega_using [ha])]
    rw [show (tablePt c (15-j)).x = (tablePt c (15-j)).x + 0 by omega_using [],x,m₁]
  obtain e_y : num c base t (tablePt c (15-j)).y = num c base s (resultPt c).y := by
    change wordsVal t.mem base (tablePt c (15-j)).y c.n = wordsVal s.mem base (resultPt c).y c.n
    rw [ey,u₄.wordsVal (by omega_using []) (by omega_using [ha]),y,
      u₂.wordsVal (by omega_using [hlo, sepY]) (by omega_using [sepY, hta]),m₁]
  obtain e_z : num c base t (tablePt c (15-j)).z = num c base s (resultPt c).z := by
    change wordsVal t.mem base (tablePt c (15-j)).z c.n = wordsVal s.mem base (resultPt c).z c.n
    rw [ez,z,u₃.wordsVal (by omega_using [hlo, sepZ]) (by omega_using [sepZ, hta]),
      u₂.wordsVal (by omega_using [hlo, sepZ]) (by omega_using [sepZ, hta]),m₁]
  obtain kt : KeepRegs [.x2,.x4,.x16,.x17] s t :=
    (((((Keeps.regs k₀).mono (by decide)).trans ((Keeps.regs k₁).mono (by decide))).trans
      (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans (k₄.mono (by decide))
  obtain u : Unch base ((coordinates (tablePt c (15-j))).map (·,8*c.n)) s.mem t.mem := by
    rw [←m₁]
    refine (u₂.unch.trans (u₃.unch.trans u₄.unch)).mono ?_
    intro w hw
    simp only [List.mem_append,List.mem_singleton] at hw
    simp only [coordinates,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,ey,ez]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  refine ⟨⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,u⟩,⟨?_,?_⟩,kt.gpr _ (by decide)⟩
  · intro e he
    simp only [coordinates,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · rw [e_x]; exact hp.1 _ (by simp)
    · rw [e_y]; exact hp.1 _ (by simp)
    · rw [e_z]; exact hp.1 _ (by simp)
  · have ex := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_x
    obtain ey' := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_y
    obtain ez' := congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e_z
    change val c base t (tablePt c (15-j)).x = val c base s (resultPt c).x at ex
    change val c base t (tablePt c (15-j)).y = val c base s (resultPt c).y at ey'
    change val c base t (tablePt c (15-j)).z = val c base s (resultPt c).z at ez'
    rw [ex,ey',ez']; exact hp.2

/-- The entry numbered `k - j` into the result, or the point at infinity for number zero. -/
theorem previousEntry_ok {base : Addr} {s : State} (hs : Scr s base 8192)
    (hc : BaseCfgOk c) (hC : Law c.C) {k j : Nat} (hk : k ≤ 15) (hj : j ≤ k)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 j) {A : VG.Spec.Weierstrass.Point c.C}
    (hA : k - j = 0 → A = .infinity) (ht : k - j ≠ 0 → PointAt c base s (tablePt c (k-j)) A) :
    WP isa (previousEntry c k) s fun t =>
      Changes base (resultWork c) s t ∧ PointAt c base t (resultPt c) A ∧ t.gpr .x19 = s.gpr .x19 := by
  rw [previousEntry]
  refine WP.seq (WP.mono (indexFrom_ok s (k:=k) (by omega_using [hk]) hj h19) fun s₁ ⟨v₁,k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain W₁ : Changes base (resultWork c) s s₁ := Changes.of_keeps k₁ (by decide)
  obtain c₁ : s₁.gpr .x19 = s.gpr .x19 := k₁.gpr _ (by decide)
  refine WP.ite (decide (k-j=0)) (zero_test (by omega_using [hk]) v₁) (fun hz => ?_) (fun hn => ?_)
  · have hz' : k-j=0 := of_decide_eq_true hz
    rw [hA hz']
    exact WP.mono (infinity_ok hs₁ hc hC) fun t ⟨k₂,R₂,c₂⟩ => ⟨W₁.trans k₂,R₂,c₂.trans c₁⟩
  · have hn' : k-j≠0 := of_decide_eq_false hn
    obtain hp := (ht hn').of_mem k₁.mem
    exact WP.mono (load_ok hs₁ (by omega_using [hn']) (by omega_using [hk]) v₁ hp) fun t ⟨k₂,R₂,c₂⟩ =>
      ⟨W₁.trans k₂,R₂,c₂.trans c₁⟩

/-- The source `G` or `Q` into the addition's entry slots. -/
theorem affine_ok {base : Addr} {P Q : Point c.C} {s : State} (hi : Inputs c base P Q s) (b : Bool) :
    WP isa (.block (if b then affineEntry c PX PY else affineEntry c GX GY)) s fun t =>
      Changes base (entryWork c) s t ∧ PointAt c base t (entry c) (if b then Q else P) ∧
      t.gpr .x19 = s.gpr .x19 := by
  cases b
  · change WP isa (.block (copyPt c.n (entry c) (gSource c))) s _
    exact WP.mono (copy_point hi.scr entry_from_generator hi.generator) fun t ⟨k,p,c⟩ => ⟨k,p,c⟩
  · change WP isa (.block (copyPt c.n (entry c) (qSource c))) s _
    exact WP.mono (copy_point hi.scr entry_from_peer hi.peer) fun t ⟨k,p,c⟩ => ⟨k,p,c⟩

/-- Entry `d = 16 - j` of the table, from the counter `j`. -/
theorem buildStep_ok {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P = true) (hQ : onCurve c.C Q = true)
    {j : Nat} (h1 : 1 ≤ j) (h15 : j ≤ 15) (hi : Inputs c base P Q s)
    (ht : Table c base P Q (15-j) s) (h19 : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (buildStep c) s fun t =>
      (Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q (15-(j-1)) t) ∧
      t.gpr .x19 = BitVec.ofNat 64 (j-1) := by
  rw [buildStep,←List.singleton_append]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decCounter_ok s h1 (by omega_using [h15]) h19) fun s₀ ⟨c₀,k₀⟩ => ?_
  refine WP.mono (rowTest_ok s₀ c₀) fun s₁ ⟨v₁,k₁⟩ => ?_
  obtain k₀₁ : Keeps [.x19,.x2,.x5] s s₁ := (k₀.mono (by decide)).trans (k₁.mono (by decide))
  obtain W₁ : Changes base (arithmeticWork c) s s₁ := Changes.of_keeps k₀₁ (by decide)
  obtain I₁ := hi.unch W₁
  obtain c₁ : s₁.gpr .x19 = BitVec.ofNat 64 (j-1) := (k₁.gpr _ (by decide)).trans c₀
  obtain T₁ : Table c base P Q (15-j) s₁ := fun e he1 he => (ht e he1 he).of_mem k₀₁.mem
  let d := 15-(j-1)
  obtain hd1 : 1 ≤ d := by omega
  obtain hd15 : d ≤ 15 := by omega_using []
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  obtain hpl := previous_lt hd1
  -- the source of the previous (entry c) and `G` or `Q`, for either row case
  obtain src : ∀ (b : Bool), b = decide (d%4=0) →
      WP isa (.seq (previousEntry c (if b then 11 else 14))
        (.block (if b then affineEntry c PX PY else affineEntry c GX GY))) s₁ fun t =>
        Changes base (loopWork c) s₁ t ∧ Inputs c base P Q t ∧ PointAt c base t (resultPt c) A ∧
        PointAt c base t (entry c) (if d%4=0 then Q else P) ∧ t.gpr .x19 = s₁.gpr .x19 := by
    intro b hb
    obtain hkj : (if b then 11 else 14) - (j-1) = previous d := by
      unfold previous
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb
        rw [ite_eq_left hz]; simp only [ite_true]; omega_using []
      · rw [decide_eq_false hz] at hb; subst hb
        rw [ite_eq_right hz]; simp only [Bool.false_eq_true,ite_false]; omega_using []
    obtain hk15 : (if b then 11 else 14) ≤ 15 := by cases b <;> decide
    obtain hjk : j-1 ≤ (if b then 11 else 14) := by
      cases b
      · simp only [Bool.false_eq_true,ite_false]; omega_using [h15]
      · simp only [ite_true]
        obtain hz : d%4=0 := of_decide_eq_true hb.symm
        omega_using [h15, hz]
    refine WP.seq (WP.mono (previousEntry_ok I₁.scr hc hC hk15 hjk c₁ (A:=A)
      (fun h0 => by dsimp only [A]; rw [hkj] at h0; rw [h0]; exact pair_zero P Q)
      (fun h0 => by
        rw [hkj] at h0 ⊢
        exact T₁ _ (by omega_using [h0]) (by omega_using [hpl])))
      fun s₂ ⟨k₂,R₂,c₂⟩ => ?_)
    obtain W₂ := k₂.mono resultWork_sub
    obtain I₂ := I₁.unch (W₂.mono loopWork_sub)
    obtain e : (if b then Q else P) = (if d%4=0 then Q else P) := by
      by_cases hz : d%4=0
      · rw [decide_eq_true hz] at hb; subst hb; simp only [ite_true,ite_eq_left hz]
      · rw [decide_eq_false hz] at hb; subst hb; simp only [Bool.false_eq_true,ite_false,ite_eq_right hz]
    refine WP.mono (affine_ok I₂ b) fun t ⟨k₃,E₃,c₃⟩ => ?_
    obtain W₃ := W₂.trans (k₃.mono entryWork_sub)
    exact ⟨W₃,I₁.unch (W₃.mono loopWork_sub),k₃.point I₂.scr R₂ (by jd c) (by jd c),e ▸ E₃,
      c₃.trans c₂⟩
  obtain hrow : isa.eval (.zero .x .x2) s₁ = some (decide (d%4=0)) := by
    change some (s₁.read .x .x2 == 0) = _
    rw [read_x,v₁]
    obtain hz := rowVal_zero (j-1) (by omega_using [h15])
    by_cases h : (15-(j-1))%4=0
    · rw [decide_eq_true h,beq_iff_eq.mpr (hz ▸ h)]
    · rw [decide_eq_false h]
      exact congrArg some (beq_eq_false_iff_ne.mpr fun e => h (hz ▸ e))
  obtain cont : ∀ s₂, (Changes base (loopWork c) s₁ s₂ ∧ Inputs c base P Q s₂ ∧ PointAt c base s₂ (resultPt c) A ∧
      PointAt c base s₂ (entry c) (if d%4=0 then Q else P) ∧ s₂.gpr .x19 = s₁.gpr .x19) →
      WP isa (.seq (addPoints c) (.block (storeEntry c))) s₂ fun t =>
        (Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q (15-(j-1)) t) ∧
        t.gpr .x19 = BitVec.ofNat 64 (j-1) := by
    intro s₂ ⟨k₂,I₂,R₂,E₂,c₂⟩
    obtain he : onCurve c.C (if d%4=0 then Q else P)=true := by
      by_cases hz : d%4=0
      · rw [ite_eq_left hz]; exact hQ
      · rw [ite_eq_right hz]; exact hP
    obtain hA : onCurve c.C A=true := pair_curve hC hP hQ _ _
    refine WP.seq (WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt he hA E₂ R₂)
      fun s₃ ⟨k₃,R₃,c₃⟩ => ?_)
    obtain W₃ := k₂.trans (k₃.mono addWork_sub)
    obtain I₃ := I₁.unch (W₃.mono loopWork_sub)
    obtain c₃' : s₃.gpr .x19 = BitVec.ofNat 64 (j-1) := c₃.trans (c₂.trans c₁)
    obtain e : add (if d%4=0 then Q else P) A = pair P Q (d%4) (d/4) := table_step hC hP hQ hd1
    rw [e] at R₃
    refine WP.mono (storeEntry_ok I₃.scr (j:=j-1) (by omega_using [h15]) c₃' R₃) fun t ⟨k₄,R₄,c₄⟩ => ?_
    obtain W₄ := (W₃.mono loopWork_sub).trans (k₄.cover (tableWork_cover hd1 hd15))
    obtain W := W₁.trans W₄
    refine ⟨⟨W,hi.unch W,fun i hi1 hid => ?_⟩,c₄.trans c₃'⟩
    by_cases heq : i=d
    · subst i; exact R₄
    · have hi' : i < d := by omega_using [hid, heq]
      obtain old := W₃.table I₁.scr hi1 (by omega_using [hid]) (T₁ i hi1 (by omega_using [hid, heq]))
      exact k₄.point I₃.scr old
        (fun x hx => Nat.le_trans (table_coord_bounds hi1 (by omega_using [hid]) x hx).2.1 (by jd c))
        (earlier_table_apart hi1 hi')
  exact WP.seq (WP.ite (decide (d%4=0)) hrow
    (fun hb => WP.mono (src true hb.symm) cont)
    (fun hb => WP.mono (src false hb.symm) cont))

theorem build_ok {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (hi : Inputs c base P Q s) :
    WP isa (build c) s fun t =>
      Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q 15 t := by
  rw [build]
  refine WP.seq (WP.mono (setCounter_ok s (j:=15) (by decide)) fun s₁ ⟨c₁,k₁⟩ => ?_)
  obtain W₁ : Changes base (arithmeticWork c) s s₁ := Changes.of_keeps k₁ (by decide)
  let inv := fun j t => (Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧
    Table c base P Q (15-j) t) ∧ t.gpr .x19 = BitVec.ofNat 64 j
  refine countLoop_ok (Inv:=inv) (n:=15) (by decide) (fun j t h1 h15 ⟨⟨k,I,T⟩,c⟩ => ?_)
    (fun t ⟨⟨k,I,T⟩,_⟩ => ⟨k,I,T⟩) (by decide)
    ⟨⟨W₁,hi.unch W₁,fun _ h1 h0 => False.elim (by omega_using [h1, h0])⟩,c₁⟩
  exact WP.mono (buildStep_ok hc hC hP hQ h1 h15 I T c) fun u ⟨⟨k',I',T'⟩,c'⟩ =>
    ⟨⟨⟨k.trans k',I',T'⟩,c'⟩,c'⟩

/-! The joint multiplier feeds the unchanged complete ECDSA final check. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/Secp256k1/Joint/Prepare.lean`, which only this module imported.

/-! Preparing the two bit tables and the general complete-addition coefficient. -/

omit [Kit c] in
theorem generator_point {base : Addr} {s : State} {g : Reg → BitVec 64}
    (hc : BaseCfgOk c) (hC : Law c.C) (hf : Fixed c base g s.mem) :
    PointAt c base s (gSource c) (G c.C) := by
  obtain hp : 0 < c.C.p := by have := hc.p_ge; omega_using [this]
  have hm (x : Nat) : c.mont x < c.C.p := Nat.mod_lt _ hp
  obtain e1 : num c base s (c.sl ONEP)=c.mont 1 := by
    rw [num,hf.onep]; simp only [Cfg.mont,Cfg.R,Nat.one_mul]
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [coordinates,gSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [num,hf.gx]; exact hm _
    · rw [num,hf.gy]; exact hm _
    · rw [e1]; exact hm _
  · have ex : val c base s (gSource c).x=Fin.ofNat c.C.p c.C.gx :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) hf.gx).trans (toM_cmont hc _)
    obtain ey : val c base s (gSource c).y=Fin.ofNat c.C.p c.C.gy :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) hf.gy).trans (toM_cmont hc _)
    obtain ez : val c base s (gSource c).z=1 :=
      (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) e1).trans (toM_cmont hc 1)
    rw [ex,ey,ez]
    exact rep_affine' hC _ _

theorem prepare_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (prepare c) s fun t =>
      Changes base (prepWork c) s t ∧ Inputs c base (G c.C) P t ∧
      Bits c base (sv c base s U) (sv c base s V) t := by
  have hn8 := (Kit.n_le c)
  obtain boundV : c.sl V+8*c.n ≤ 8192 := by jd c
  have hs := hM.scr
  have hn := hs.nowrap
  obtain hm0 : 0 < c.C.p := by have := hc.p_ge; omega_using [this]
  have hm (x : Nat) : c.mont x < c.C.p := Nat.mod_lt _ hm0
  obtain hbconst : c.mont (3*c.C.b) < 2^(64*c.n) := Nat.lt_trans (hm _) hc.p_lt
  rw [prepare]
  refine WP.seq (WP.mono (bits_ok hs (n:=c.n) (src:=c.sl U) (dst:=bitsU)
    (by jd c) (by jd c) (by jd c) (by jd c) (by jd c) (by jd c) (Or.inl (by jd c)))
    fun s₁ ⟨b₁,k₁,u₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain v₁ : wordsVal s₁.mem base (c.sl V) c.n=wordsVal s.mem base (c.sl V) c.n :=
    u₁.wordsVal (by jd c) (by omega_using [boundV])
  refine WP.seq (WP.mono (bits_ok hs₁ (n:=c.n) (src:=c.sl V) (dst:=(bitsV c))
    (by jd c) (by jd c) (by jd c) (by jd c) (by jd c) (by jd c) (Or.inl (by jd c)))
    fun s₂ ⟨b₂,k₂,u₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n:=c.n) (o:=c.sl EXPP) (by jd c) (by jd c) hbconst)
    fun t ⟨b₃,k₃,u₃⟩ => ?_
  obtain W : Changes base (prepWork c) s t := by
    obtain kt := (k₁.trans k₂).trans (k₃.mono (by decide))
    refine ⟨kt.gpr _ (by decide),kt.rd,kt.wr,kt.sp,?_⟩
    exact (u₁.unch.trans (u₂.unch.trans u₃.unch)).cover (by
      intro w hw
      simp only [List.mem_append,List.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨(bitsU,128*c.n),by simp,by jd c,by jd c⟩
      · exact ⟨(bitsU,128*c.n),by simp,by jd c,by jd c⟩
      · exact ⟨(c.sl EXPP,8*c.n),by simp,by jd c,by jd c⟩)
  obtain F := hM.fixed.unch hc.n10 hn (by unfold FixedOk prepWork; jd c) W.mem
  obtain hqp : PointAt c base s (qSource c) P := by
    refine ⟨?_,hrep⟩
    intro x hx
    simp only [coordinates,qSource,Cfg.pt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hM.px_lt
    · exact hM.py_lt
    · rw [num,hM.fixed.onep]; exact Nat.mod_lt _ hm0
  obtain I : Inputs c base (G c.C) P t := by
    refine ⟨W.scr hs,modP_of hc F.mp,?_,?_,?_,?_,generator_point hc hC F,
      W.point hs hqp (by jd c) (by jd c)⟩
    · rw [num,F.ap]; exact hm _
    · rw [num,b₃]; exact hm _
    · exact (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) F.ap).trans (toM_cmont hc _)
    · exact (congrArg (fun x => toM c.C.p (2^(64*c.n)) x) b₃).trans (toM_cmont hc _)
  obtain hE : c.sl EXPP+8*c.n ≤ 2944 := by jd c
  refine ⟨W,I,?_,?_⟩
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ c.sl EXPP+8*c.n ≤ 2944+j; omega_using [hE])
        (by have := (Kit.n_le c); change 2944+j < 2^64; omega_using [hj, this]),
      u₂.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change 2944+j+1 ≤ (2944+64*c.n) ∨ _; omega_using [hj])
        (by have := (Kit.n_le c); change 2944+j < 2^64; omega_using [hj, this]),b₁ j hj]
  · intro j hj
    rw [u₃.unch.byte (by intro w hw; rw [List.mem_singleton.mp hw]; change _ ≤ _ ∨ c.sl EXPP+8*c.n ≤ (2944+64*c.n)+j; omega_using [hE])
        (by have := (Kit.n_le c); change (2944+64*c.n)+j < 2^64; omega_using [hj, this]),b₂ j hj,v₁]

theorem arithmeticWork_sub : ∀ w ∈ (arithmeticWork c),w ∈ (work c) := by jd c
theorem prepWork_sub : ∀ w ∈ (prepWork c),w ∈ (work c) := by jd c

theorem setupWith_ok {m : Nat} (hm : Rounds c m) {build : Prog isa} (hb : BuildOk c build)
    {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (setupWith c m build) s fun t => Changes base (work c) s t ∧
      Running c base (G c.C) P (sv c base s U) (sv c base s V) (32*m) t := by
  rw [setupWith]
  refine WP.seq (WP.mono (prepare_ok hc hC hM hrep) fun s₁ ⟨k₁,I₁,B₁⟩ => ?_)
  refine WP.seq (WP.mono (hb hc hC hc.onG hP I₁) fun s₂ ⟨k₂,I₂,T₂⟩ => ?_)
  obtain B₂ := k₂.bits B₁
  rw [WP.block_append_iff]
  refine WP.mono (infinity_ok I₂.scr hc hC) fun s₃ ⟨k₃,R₃,_⟩ => ?_
  obtain W₃ := k₃.mono resultWork_sub
  obtain I₃ := I₂.unch (W₃.mono loopWork_sub)
  obtain B₃ := (W₃.mono loopWork_sub).bits B₂
  obtain T₃ := T₂.of_changes I₂.scr W₃
  refine WP.mono (setCounter_ok s₃ (j:=32*m) (by have := hm.le; have := Kit.n_le c; omega))
    fun s₄ ⟨c₄,k₄⟩ => ?_
  obtain W₄ : Changes base (loopWork c) s₃ s₄ := Changes.of_keeps k₄ (by decide)
  obtain I₄ := I₃.unch (W₄.mono loopWork_sub)
  obtain B₄ := (W₄.mono loopWork_sub).bits B₃
  obtain T₄ := T₃.of_changes I₃.scr W₄
  obtain R₄ := R₃.of_mem k₄.mem
  obtain hu := Nat.lt_trans hM.u_lt (hm.order_lt hc)
  obtain hv := Nat.lt_trans hM.v_lt (hm.order_lt hc)
  obtain hstart := at_top (G c.C) P (n:=m) hu hv
  rw [←hstart] at R₄
  exact ⟨(((k₁.mono prepWork_sub).trans (k₂.mono arithmeticWork_sub)).trans
    ((W₃.mono loopWork_sub).mono arithmeticWork_sub)).trans
    ((W₄.mono loopWork_sub).mono arithmeticWork_sub),⟨I₄,B₄,T₄,c₄,R₄⟩⟩

theorem pointsWith_raw {m : Nat} (hm : Rounds c m) {build : Prog isa} (hb : BuildOk c build)
    {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (pointsWith c m build) s fun t =>
      Changes base (work c) s t ∧ PointAt c base t (resultPt c)
        (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)) := by
  rw [pointsWith]
  refine WP.seq (WP.mono (setupWith_ok hm hb hc hC hP hM hrep) fun s₄ ⟨k₄,R₄⟩ => ?_)
  refine WP.mono (loop_ok hm hc hC hc.onG hP R₄) fun t ⟨k₅,h₅⟩ => ?_
  obtain W := k₄.trans ((k₅.mono loopWork_sub).mono arithmeticWork_sub)
  have p := h₅.point
  rw [at_zero] at p
  exact ⟨W,p⟩

theorem final_state {base : Addr} {s₀ s t : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hM : Mid c s₀ base g s) (h : Changes base (work c) s t)
    (hp : PointAt c base t (resultPt c) P) : FinalState c s₀ base g t := by
  have hn := hM.scr.nowrap
  obtain flagBound : c.sl FLAG+8 ≤ 8192 := by jd c
  have hn8 := (Kit.n_le c)
  have same (i : Nat) (hle : c.sl i+8*c.n ≤ 8192)
      (hap : ∀ w ∈ (work c),c.sl i+8*c.n ≤ w.1 ∨ w.1+w.2 ≤ c.sl i) :
      sv c base t i=sv c base s i :=
    h.mem.wordsVal hap (by omega_using [hn8, hle])
  obtain r := same RM' (by jd c) (by jd c)
  obtain k := same Impl.Ecdsa.AArch64.K (by jd c) (by jd c)
  refine ⟨h.scr hM.scr,h.wr.trans hM.wr,h.rd.trans hM.rd,
    hM.fixed.unch hc.n10 hn (by unfold FixedOk work loopWork addWork entryWork; jd c) h.mem,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h.mem.word (by jd c) (by omega_using [flagBound])]
    exact hM.flag
  · rw [r]; exact hM.rm_lt
  · rw [r]; exact hM.rm
  · exact hp.1 _ (by jd c)
  · exact (hM.unch.trans h.mem).cover (by
      intro w hw
      refine ⟨(0,8192),by simp,by omega_using [],?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
      · have hd : ∀ w ∈ (work c),w.1+w.2 ≤ 8192 := by jd c
        exact hd w hw)
  · exact k.trans hM.k
  · exact hp.1 _ (by jd c)

theorem pointsWith_ok {m : Nat} (hm : Rounds c m) {build : Prog isa} (hb : BuildOk c build)
    {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (pointsWith c m build) s fun t => FinalState c s₀ base g t ∧
      Rep c.C (val c base t (resultPt c).x) (val c base t (resultPt c).y) (val c base t (resultPt c).z)
        (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)) :=
  WP.mono (pointsWith_raw hm hb hc hC hP hM hrep) fun _ ⟨W,p⟩ => ⟨final_state hc hM W p,p.2⟩

/-! ## With the table by pointers the counter selects (`build`) -/

theorem setup_ok {m : Nat} (hm : Rounds c m) {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (setup c m) s fun t => Changes base (work c) s t ∧
      Running c base (G c.C) P (sv c base s U) (sv c base s V) (32*m) t :=
  setupWith_ok hm (fun hc hC hP hQ hi => build_ok hc hC hP hQ hi) hc hC hP hM hrep

theorem points_ok {m : Nat} (hm : Rounds c m) {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (points c m) s fun t => FinalState c s₀ base g t ∧
      Rep c.C (val c base t (resultPt c).x) (val c base t (resultPt c).y) (val c base t (resultPt c).z)
        (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)) :=
  pointsWith_ok hm (fun hc hC hP hQ hi => build_ok hc hC hP hQ hi) hc hC hP hM hrep

/-! ## With the table by a choice of copies the counter selects (`buildTable`) -/

/-- Select one of fifteen short copy paths using the public table counter. -/
def choose (f : Nat → Prog isa) : Nat → Prog isa
  | 0 => .block []
  | m+1 => .seq (.block [.subImm .x .x2 .x19 (m+1)])
      (.ite (.zero .x .x2) (f (m+1)) (choose f m))

def tablePrep (c : Cfg) (d : Nat) : Prog isa :=
  let previous := if d % 4 = 0 then d-4 else d-1
  let source := if previous = 0 then infinity c else copyPt c.n (resultPt c) (tablePt c previous)
  let (x,y) := if d % 4 = 0 then (PX,PY) else (GX,GY)
  .block (source ++ affineEntry c x y)

def tableStore (c : Cfg) (d : Nat) : Prog isa := .block (copyPt c.n (tablePt c d) (resultPt c))

def prepChoice (c : Cfg) : Prog isa := choose (tablePrep c) 15
def storeChoice (c : Cfg) : Prog isa := choose (tableStore c) 15

/-- One shared complete addition serves every table entry. -/
def tableLoopStep (c : Cfg) : Prog isa :=
  .seq (prepChoice c) <| .seq (addPoints c) <| .seq (storeChoice c)
    (.block [.addImm .x .x19 .x19 1,.subImm .x .x6 .x19 16])

def buildTable (c : Cfg) : Prog isa :=
  .seq (.block [.movz .x .x19 1 0]) (.loop (tableLoopStep c) (.nonzero .x .x6))

/-- What the proof of `buildTable` needs of a configuration, besides its `Kit`:
the two choices keep the table's counter. -/
class Compact (c : Cfg) : Prop where
  prep_counter : ∀ i ∈ instrs (prepChoice c), clobbers i .x19 = false
  store_counter : ∀ i ∈ instrs (storeChoice c), clobbers i .x19 = false

theorem store_layout {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) : CopyLayout c (tablePt c d) (resultPt c) := by
  constructor
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact Nat.le_trans (table_coord_bounds h1 h15 x h).2.1 (by jd c)
    · have hc : ∀ x ∈ coordinates (resultPt c),x+8*c.n ≤ 8192 := by jd c
      exact hc x h
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact (table_coord_bounds h1 h15 x h).2.2
    · have hc : ∀ x ∈ coordinates (resultPt c),x % 8 = 0 := by jd c
      exact hc x h
  · intro x hx y hy hne
    rcases List.mem_append.mp hy with hy | hy
    · simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        omega_arith
    · have hh : ∀ x ∈ coordinates (resultPt c),x+8*c.n ≤ tableAt := by jd c
      exact Or.inr (Nat.le_trans (hh y hy) (table_coord_bounds h1 h15 x hx).1)

  · intro x hx hy
    have hb := (table_coord_bounds (c := c) h1 h15 x hx).1
    have hc : ∀ x ∈ coordinates (resultPt c),x < tableAt := by jd c
    have := hc x hy; omega_using [hb, this]
  · have hn0 := Kit.n_pos c
    simp only [tablePt]; exact ⟨by omega_using [hn0],by omega_using [hn0],by omega_using [hn0]⟩

theorem load_layout {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) : CopyLayout c (resultPt c) (tablePt c d) := by
  have hs := store_layout (c := c) h1 h15
  constructor
  · intro x hx; exact hs.end_le x (List.mem_append.mpr ((List.mem_append.mp hx).elim Or.inr Or.inl))
  · intro x hx; exact hs.aligned x (List.mem_append.mpr ((List.mem_append.mp hx).elim Or.inr Or.inl))
  · intro x hx y hy hne
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · have hf : ∀ x ∈ coordinates (resultPt c),∀ y ∈ coordinates (resultPt c),x ≠ y →
        x+8*c.n ≤ y ∨ y+8*c.n ≤ x := by jd c
      exact hf x hx y hy hne
    · have hx' : x+8*c.n ≤ tableAt := by
        have hc : ∀ x ∈ coordinates (resultPt c),x+8*c.n ≤ tableAt := by jd c
        exact hc x hx
      exact Or.inl (Nat.le_trans hx' (table_coord_bounds h1 h15 y hy).1)
  · intro x hx hy
    exact hs.different x hy hx
  · jd c

theorem tablePrep_ok {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs c base P Q s)
    (ht : Table c base P Q (d-1) s) :
    WP isa (tablePrep c d) s fun t =>
      Changes base (loopWork c) s t ∧ Inputs c base P Q t ∧
      PointAt c base t (resultPt c) (pair P Q ((previous d)%4) ((previous d)/4)) ∧
      PointAt c base t (entry c) (if d%4=0 then Q else P) := by
  have hp : previous d < d := previous_lt h1
  have hp15 : previous d ≤ 15 := by omega_using [h15, hp]
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  have prep : WP isa (.block (if previous d=0 then (infinity c) else copyPt c.n (resultPt c) (tablePt c (previous d)))) s
      fun t => Changes base (loopWork c) s t ∧ Inputs c base P Q t ∧ PointAt c base t (resultPt c) A := by
    by_cases hz : previous d=0
    · rw [ite_eq_left hz]
      refine WP.mono (infinity_ok hi.scr hc hC) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      refine ⟨W,hi.unch (W.mono loopWork_sub),?_⟩
      have e : A=.infinity := by dsimp only [A]; rw [hz]; exact pair_zero P Q
      rw [e]; exact p
    · rw [ite_eq_right hz]
      refine WP.mono (copy_point hi.scr (load_layout (by omega_using [hz]) hp15)
        (ht (previous d) (by omega_using [hz]) (by omega_using [hp]))) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      exact ⟨W,hi.unch (W.mono loopWork_sub),p⟩
  have code : tablePrep c d = .block ((if previous d=0 then (infinity c) else copyPt c.n (resultPt c) (tablePt c (previous d))) ++
      affineEntry c (if d%4=0 then PX else GX) (if d%4=0 then PY else GY)) := by
    by_cases hz : d%4=0
    · simp only [tablePrep,previous,ite_eq_left hz]
    · simp only [tablePrep,previous,ite_eq_right hz]
  rw [code,WP.block_append_iff]
  refine WP.mono prep fun s₁ ⟨k₁,I₁,R₁⟩ => ?_
  have aff : WP isa (.block (affineEntry c (if d%4=0 then PX else GX) (if d%4=0 then PY else GY))) s₁
      fun t => Changes base (entryWork c) s₁ t ∧ PointAt c base t (entry c) (if d%4=0 then Q else P) := by
    by_cases hz : d%4=0
    · simp only [ite_eq_left hz]
      change WP isa (.block (copyPt c.n (entry c) (qSource c))) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_peer I₁.peer) fun t ⟨k,p,_⟩ => ⟨k,p⟩
    · simp only [ite_eq_right hz]
      change WP isa (.block (copyPt c.n (entry c) (gSource c))) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_generator I₁.generator) fun t ⟨k,p,_⟩ => ⟨k,p⟩
  refine WP.mono aff fun s₂ ⟨k₂,E₂⟩ => ?_
  have W₂ := k₁.trans (k₂.mono entryWork_sub)
  have I₂ := hi.unch (W₂.mono loopWork_sub)
  have R₂ := k₂.point I₁.scr R₁ (by jd c) (by jd c)
  exact ⟨W₂,I₂,R₂,E₂⟩

/-! Selecting a short copy path using only the public table counter. -/

theorem choose_sub (s : State) {m : Nat} (hm : m < 4096) :
    WP isa (.block [.subImm .x .x2 .x19 m]) s fun t =>
      t.gpr .x2=s.gpr .x19-BitVec.ofNat 64 m ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,hm,ite_true,BitVec.setWidth_eq,
    RegUpd.gpr_write_self,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem choose_wp (f : Nat → Prog isa) {Q : State → Prop} :
    ∀ m,m ≤ 15 → ∀ {j : Nat} {s : State},1 ≤ j → j ≤ m →
      s.gpr .x19=BitVec.ofNat 64 j →
      (∀ t,Keeps [.x2] s t → WP isa (f j) t Q) → WP isa (choose f m) s Q
  | 0,_,_,_,hj,hjm,_,_ => False.elim (by omega_using [hj, hjm])
  | m+1,hm,j,s,hj,hjm,h19,h => by
    rw [choose]
    refine WP.seq (WP.mono (choose_sub s (m:=m+1) (by omega_using [hm])) fun t ⟨v,k⟩ => ?_)
    have z : (t.read .x .x2 == 0)=decide (j=m+1) := by
      rw [read_x,v,h19]
      by_cases e : j=m+1
      · rw [e,BitVec.sub_self]
        change true = decide (m+1=m+1)
        exact (decide_eq_true rfl).symm
      · rw [decide_eq_false e,beq_eq_false_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega_using [hm, hjm] : j < 2^64),
          Nat.mod_eq_of_lt (by omega_using [hm] : m+1 < 2^64)] at hh
        change (2^64-(m+1)+j)%(2^64)=0 at hh
        omega_using [hm, hjm, e, hh]
    apply WP.ite (decide (j=m+1)) (by change some (t.read .x .x2 == 0)=_; rw [z])
    · intro e
      rw [decide_eq_true_eq] at e
      subst j
      exact h t k
    · intro e
      rw [decide_eq_false_iff_not] at e
      exact choose_wp f m (by omega_using [hm]) hj (by omega_using [hjm, e]) ((k.gpr _ (by decide)).trans h19)
        fun u ku => h u (k.trans ku)

/-! One complete addition shared by the fifteen public table entries. -/

theorem with_counter {p : Prog isa} {s : State} {Q : State → Prop}
    (h : ∀ i ∈ instrs p,clobbers i .x19=false) (w : WP isa p s Q) :
    WP isa p s fun t => Q t ∧ t.gpr .x19=s.gpr .x19 := by
  obtain ⟨tr,t,e,q⟩ := w
  exact ⟨tr,t,e,q,Exec.gpr h e⟩

theorem prepChoice_ok [Compact c] {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    (hi : Inputs c base P Q s) (ht : Table c base P Q (d-1) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (prepChoice c) s fun t =>
      (Changes base (loopWork c) s t ∧ Inputs c base P Q t ∧
        PointAt c base t (resultPt c) (pair P Q ((previous d)%4) ((previous d)/4)) ∧
        PointAt c base t (entry c) (if d%4=0 then Q else P)) ∧ t.gpr .x19=s.gpr .x19 := by
  apply with_counter Compact.prep_counter
  apply choose_wp (tablePrep c) 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base (loopWork c) s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table c base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega_using [h15, hjm]) (ht j hj hjm)
  exact WP.mono (tablePrep_ok hc hC h1 h15 I T) fun t ⟨w,i,r,e⟩ => ⟨W.trans w,i,r,e⟩

theorem storeChoice_ok [Compact c] {base : Addr} {P Q : Point c.C} {s : State}
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs c base P Q s)
    (ht : Table c base P Q (d-1) s)
    (hp : PointAt c base s (resultPt c) (pair P Q (d%4) (d/4)))
    (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (storeChoice c) s fun t =>
      (Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q d t) ∧
      t.gpr .x19=s.gpr .x19 := by
  apply with_counter Compact.store_counter
  apply choose_wp (tableStore c) 15 (by decide) h1 h15 h19
  intro u ku
  have W : Changes base (loopWork c) s u := Changes.of_keeps ku (by decide)
  have I := hi.unch (W.mono loopWork_sub)
  have T : Table c base P Q (d-1) u := fun j hj hjm =>
    W.table hi.scr hj (by omega_using [h15, hjm]) (ht j hj hjm)
  have R := hp.of_mem ku.mem
  refine WP.mono (copy_point I.scr (store_layout h1 h15) R) fun t ⟨k,p,_⟩ => ?_
  have K := (W.mono loopWork_sub).trans (k.cover (tableWork_cover h1 h15))
  refine ⟨K,hi.unch K,fun j hj hjd => ?_⟩
  by_cases heq : j=d
  · subst j; exact p
  · have hj' : j < d := by omega_using [hjd, heq]
    exact k.point I.scr (T j hj (by omega_using [hjd, heq]))
      (fun x hx => Nat.le_trans (table_coord_bounds hj (by omega_using [h15, hjd]) x hx).2.1 (by jd c))
      (earlier_table_apart hj hj')

theorem tableIncrement_ok (s : State) {d : Nat} (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (.block [.addImm .x .x19 .x19 1,.subImm .x .x6 .x19 16]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧
      t.gpr .x6=BitVec.ofNat 64 (d+1)-16 ∧ Keeps [.x19,.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat)<4096 by decide,show (16 : Nat)<4096 by decide,
    ite_true,BitVec.setWidth_eq,RegUpd.gpr_write,reduceCtorEq,ite_false,h19,
    Option.some.injEq,exists_eq_left']
  have e : BitVec.ofNat 64 d+1=BitVec.ofNat 64 (d+1) := by
    change BitVec.ofNat 64 d+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  refine ⟨e,congrArg (fun x : BitVec 64 => x-BitVec.ofNat 64 16) e,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem tableLoopStep_ok [Compact c] {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs c base P Q s)
    (ht : Table c base P Q (d-1) s) (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (tableLoopStep c) s fun t =>
      Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q d t ∧
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧ t.gpr .x6=BitVec.ofNat 64 (d+1)-16 := by
  rw [tableLoopStep]
  refine WP.seq (WP.mono (prepChoice_ok hc hC h1 h15 hi ht h19) fun a ⟨⟨W,I,R,E⟩,cn⟩ => ?_)
  have hA : onCurve c.C (pair P Q ((previous d)%4) ((previous d)/4))=true := pair_curve hC hP hQ _ _
  have he : onCurve c.C (if d%4=0 then Q else P)=true := by split <;> with_reducible assumption
  refine WP.seq (WP.mono (sum_points hc hC I.scr I.mod I.a I.b I.a_lt I.b_lt he hA E R)
    fun b ⟨W',R',c'⟩ => ?_)
  have K := W.trans (W'.mono addWork_sub)
  have I' := hi.unch (K.mono loopWork_sub)
  have T : Table c base P Q (d-1) b := fun j hj hjm => K.table hi.scr hj (by omega_using [h15, hjm]) (ht j hj hjm)
  rw [table_step hC hP hQ h1] at R'
  refine WP.seq (WP.mono (storeChoice_ok h1 h15 I' T R' (c'.trans (cn.trans h19)))
    fun u ⟨⟨L,Iu,Tu⟩,cu⟩ => ?_)
  refine WP.mono (tableIncrement_ok u (cu.trans (c'.trans (cn.trans h19)))) fun t ⟨ct,ft,kt⟩ => ?_
  have Z : Changes base (arithmeticWork c) u t := Changes.of_keeps kt (by decide)
  exact ⟨((K.mono loopWork_sub).trans L).trans Z,Iu.unch Z,
    fun j hj hjd => (Tu j hj hjd).of_mem kt.mem,ct,ft⟩

theorem buildTable_ok [Compact c] {base : Addr} {P Q : Point c.C} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (hi : Inputs c base P Q s) :
    WP isa (buildTable c) s fun t =>
      Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧ Table c base P Q 15 t := by
  rw [buildTable]
  refine WP.seq (WP.mono (setCounter_ok s (j:=1) (by decide)) fun a ⟨ca,ka⟩ => ?_)
  have Wa : Changes base (arithmeticWork c) s a := Changes.of_keeps ka (by decide)
  let Inv := fun j t => Changes base (arithmeticWork c) s t ∧ Inputs c base P Q t ∧
    Table c base P Q (15-j) t ∧ t.gpr .x19=BitVec.ofNat 64 (16-j)
  refine WP.loop (M:=isa) (fun j t => 1 ≤ j ∧ j ≤ 15 ∧ Inv j t)
    (fun j t ⟨h1,h15,ht⟩ => ?_) 15 a ⟨by decide,by decide,Wa,hi.unch Wa,?_,ca⟩
  · obtain ⟨W,I,T,cn⟩ := ht
    have T' : Table c base P Q ((16-j)-1) t := by simpa only [show 16-j-1=15-j by omega_using []] using T
    refine WP.mono (tableLoopStep_ok hc hC hP hQ (by omega_using [h15]) (by omega_using [h1]) I T' cn)
      fun u ⟨L,Iu,Tu,cu,fu⟩ => ?_
    by_cases e : j=1
    · subst j
      refine Or.inl ⟨?_,W.trans L,Iu,Tu⟩
      change some (u.read .x .x6 != 0)=some false
      rw [read_x,fu]; rfl
    · refine Or.inr ⟨?_,j-1,by omega_using [h1],by omega_using [h1, e],by omega_using [h15],W.trans L,Iu,?_,?_⟩
      · change some (u.read .x .x6 != 0)=some true
        rw [read_x,fu]
        apply congrArg some
        rw [bne_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at hh
        change (2^64-16+((16-j+1)%(2^64)))%(2^64)=0 at hh
        rw [Nat.mod_eq_of_lt (by omega_using [] : 16-j+1 < 2^64)] at hh
        omega_using [e, hh]
      · simpa only [show 15-(j-1)=16-j by omega_using [h1]] using Tu
      · simpa only [show 16-(j-1)=16-j+1 by omega_using [h1, h15]] using cu
  · intro j hj h0; omega

theorem setupCompact_ok [Compact c] {m : Nat} (hm : Rounds c m) {base : Addr} {s₀ s : State} {g : Reg → BitVec 64}
    {P : Point c.C} (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (setupWith c m (buildTable c)) s fun t => Changes base (work c) s t ∧
      Running c base (G c.C) P (sv c base s U) (sv c base s V) (32*m) t :=
  setupWith_ok hm (fun hc hC hP hQ hi => buildTable_ok hc hC hP hQ hi) hc hC hP hM hrep

theorem pointsCompact_ok [Compact c] {m : Nat} (hm : Rounds c m) {base : Addr} {s₀ s : State} {g : Reg → BitVec 64}
    {P : Point c.C} (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hM : Mid c s₀ base g s)
    (hrep : Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P) :
    WP isa (pointsWith c m (buildTable c)) s fun t => FinalState c s₀ base g t ∧
      Rep c.C (val c base t (resultPt c).x) (val c base t (resultPt c).y) (val c base t (resultPt c).z)
        (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)) :=
  pointsWith_ok hm (fun hc hC hP hQ hi => buildTable_ok hc hC hP hQ hi) hc hC hP hM hrep

/-! ## The loop's timing -/

/-- A round to its digit pair: what the lookup's trace depends on. -/
def stepFront (c : Cfg) : Prog isa :=
  .seq (.block [decCounter]) (.seq (double c) (.seq (double c) (.block (digit c))))

/-- The two pieces of a round run in constant time, given the base and the
counter, and the base and the digit pair: the curve's `taint_decide`s. -/
structure StepCt (c : Cfg) : Prop where
  front : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x19])) (stepFront c)
  tail : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x2])) (digitTail c)

theorem stepFront_ok {base : Addr} {P Q : Point c.C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true) (hQ : onCurve c.C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 32*c.n) (h : Running c base P Q u v j s) :
    WP isa (stepFront c) s fun t => Scr t base 8192 ∧
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v (j-1)) := by
  rw [stepFront]
  have hn8 := Kit.n_le c
  refine WP.seq (WP.mono (decCounter_ok s h1 (by omega_using [h256, hn8]) h.counter) fun s₀ ⟨c₀,k₀⟩ => ?_)
  have W₀ : Changes base (loopWork c) s s₀ := Changes.of_keeps k₀ (by decide)
  have I₀ := h.inputs.unch (W₀.mono loopWork_sub)
  have R₀ := h.point.of_mem k₀.mem
  have hA : onCurve c.C (stage P Q u v j)=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (double_points hc hC I₀ hA R₀) fun s₁ ⟨k₁,I₁,R₁,c₁⟩ => ?_)
  refine WP.seq (WP.mono (double_points hc hC I₁ (hC.onCurve_add hA hA) R₁) fun s₂ ⟨k₂,I₂,_,c₂⟩ => ?_)
  have W₂ := (W₀.trans k₁).trans k₂
  have B₂ := (W₂.mono loopWork_sub).bits h.bits
  have C₂ : s₂.gpr .x19=BitVec.ofNat 64 (j-1) := c₂.trans (c₁.trans c₀)
  exact WP.mono (digit_ok I₂.scr B₂ (by omega_using [h256, h1]) C₂) fun t ⟨d,k⟩ =>
    ⟨I₂.scr.of_keeps k (by decide),d⟩

omit [Kit c] in
theorem step_cut {s t : State} {tr : List Leak} (e : Exec isa (step c) s tr t) :
    ∃ a tf tt, Exec isa (stepFront c) s tf a ∧ Exec isa (digitTail c) a tt t ∧ tr=tf++tt := by
  cases e with
  | seq ed e => cases e with
    | seq ea e => cases e with
      | seq eb e => cases e with
        | seq eg et =>
          exact ⟨_,_,_,.seq ed (.seq ea (.seq eb eg)),et,by simp only [List.append_assoc]⟩

/-- The peers may differ: only the public (digit c) pair controls the lookup's trace. -/
theorem step_ct (hct : StepCt c) {base : Addr} {P Q₁ Q₂ : Point c.C} {u v j : Nat}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true)
    (hQ₁ : onCurve c.C Q₁=true) (hQ₂ : onCurve c.C Q₂=true) (h1 : 1 ≤ j) (h256 : j ≤ 32*c.n) :
    RelCT isa (fun s t => Running c base P Q₁ u v j s ∧ Running c base P Q₂ u v j t ∧ s.sp=t.sp)
      (step c) (fun s t => Running c base P Q₁ u v (j-1) s ∧ Running c base P Q₂ u v (j-1) t ∧ s.sp=t.sp) := by
  intro s t ts tt s' t' ⟨hs,ht,sp⟩ es et
  obtain ⟨a,tf,ta,ef,ea,etr⟩ := step_cut es
  obtain ⟨b,tg,tb,eg,eb,ttr⟩ := step_cut et
  have hfg := hct.front _ _ _ _ _ _ trivial trivial ⟨sp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.inputs.scr.x0.trans ht.inputs.scr.x0.symm
    · exact hs.counter.trans ht.counter.symm⟩ ef eg
  obtain ⟨_,_,ew,ha⟩ := stepFront_ok hc hC hP hQ₁ h1 h256 hs
  obtain ⟨_,rfl⟩ := Exec.det ef ew
  obtain ⟨_,_,ew,hb⟩ := stepFront_ok hc hC hP hQ₂ h1 h256 ht
  obtain ⟨_,rfl⟩ := Exec.det eg ew
  have hsp := (Exec.rdwr ef).2.2.trans (sp.trans (Exec.rdwr eg).2.2.symm)
  have hab := hct.tail _ _ _ _ _ _ trivial trivial ⟨hsp,fun r hr => by
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.1.x0.trans hb.1.x0.symm
    · exact ha.2.trans hb.2.symm⟩ ea eb
  obtain ⟨_,_,ew,_,hs'⟩ := step_ok hc hC hP hQ₁ h1 h256 hs
  obtain ⟨_,rfl⟩ := Exec.det es ew
  obtain ⟨_,_,ew,_,ht'⟩ := step_ok hc hC hP hQ₂ h1 h256 ht
  obtain ⟨_,rfl⟩ := Exec.det et ew
  exact ⟨by rw [etr,ttr,hfg,hab],hs',ht',(Exec.rdwr es).2.2.trans (sp.trans (Exec.rdwr et).2.2.symm)⟩

theorem loop_ct (hct : StepCt c) {m : Nat} (hm : Rounds c m) {base : Addr} {P Q₁ Q₂ : Point c.C} {u v : Nat}
    (hc : BaseCfgOk c) (hC : Law c.C) (hP : onCurve c.C P=true)
    (hQ₁ : onCurve c.C Q₁=true) (hQ₂ : onCurve c.C Q₂=true) :
    RelCT isa (fun s t => Running c base P Q₁ u v (32*m) s ∧ Running c base P Q₂ u v (32*m) t ∧ s.sp=t.sp)
      (.loop (step c) (.nonzero .x .x19))
      (fun s t => Running c base P Q₁ u v 0 s ∧ Running c base P Q₂ u v 0 t ∧ s.sp=t.sp) := by
  have hm8 : m ≤ 8 := Nat.le_trans hm.le (Kit.n_le c)
  let I := fun j s t => 1 ≤ j ∧ j ≤ 32*m ∧
    Running c base P Q₁ u v j s ∧ Running c base P Q₂ u v j t ∧ s.sp=t.sp
  have H := RelCT.loop (M:=isa) (body:=(step c)) (c:=.nonzero .x .x19)
    (Q:=fun s t => Running c base P Q₁ u v 0 s ∧ Running c base P Q₂ u v 0 t ∧ s.sp=t.sp) I (fun j => ?_) (32*m)
  · exact H.mono (fun _ _ h => ⟨Nat.mul_pos (by decide) hm.pos,Nat.le_refl _,h⟩) (fun _ _ h => h)
  intro s t ts tt s' t' ⟨h1,h256,hs,ht,sp⟩ es et
  obtain ⟨eqtr,hs',ht',sp'⟩ := step_ct hct hc hC hP hQ₁ hQ₂ h1 (Nat.le_trans h256 (Nat.mul_le_mul_left 32 hm.le)) _ _ _ _ _ _ ⟨hs,ht,sp⟩ es et
  have heq : isa.eval (.nonzero .x .x19) s'=isa.eval (.nonzero .x .x19) t' := by
    change some (s'.read .x .x19 != 0)=some (t'.read .x .x19 != 0)
    rw [VG.Proof.Ed25519.AArch64.read_x,VG.Proof.Ed25519.AArch64.read_x,hs'.counter,ht'.counter]
  have ev : isa.eval (.nonzero .x .x19) s'=some (decide (j-1 ≠ 0)) := by
    change some (s'.read .x .x19 != 0)=_
    rw [VG.Proof.Ed25519.AArch64.read_x,hs'.counter]
    congr 1
    by_cases hz : j-1=0
    · rw [hz]; rfl
    · rw [decide_eq_true hz,bne_iff_ne,ne_eq]
      intro hh
      have hn := congrArg BitVec.toNat hh
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [h256, hm8])] at hn
      exact hz hn
  refine ⟨eqtr,heq,?_,?_⟩
  · intro hz
    rw [ev,Option.some.injEq,decide_eq_false_iff_not,ne_eq,not_not] at hz
    rw [hz] at hs' ht'
    exact ⟨hs',ht',sp'⟩
  · intro hn
    rw [ev,Option.some.injEq,decide_eq_true_eq] at hn
    exact ⟨j-1,by omega_using [h1],by omega_using [hn],by omega_using [h256],hs',ht',sp'⟩

/-! ## The verification -/

section Verification

open VG.Proof.Ecdh.AArch64

/-- `Impl.Ecdsa.Verify.AArch64.<Curve>.verifyWithPoints`, which each curve's
module states, the same, for every configuration. -/
def verifyWithPoints (c : Cfg) (pointCode : Prog isa) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) <| .seq pointCode (Impl.Ecdsa.Verify.AArch64.Cfg.tail c)

omit [Kit c] in
/-- The verification with points that leave `[u]G + [v]Q` in `R`, as `pointsWith_ok` states. -/
theorem verifyWith_ok {points : Prog isa}
    (hpts : ∀ {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point c.C}, onCurve c.C P=true →
      Mid c s₀ base g s →
      Rep c.C (val c base s (qSource c).x) (val c base s (qSource c).y) (val c base s (qSource c).z) P →
      WP isa points s fun t => FinalState c s₀ base g t ∧
        Rep c.C (val c base t (resultPt c).x) (val c base t (resultPt c).y) (val c base t (resultPt c).z)
          (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)))
    (hc : BaseCfgOk c) (hC : Law c.C) {s₀ : State} (hp : FrontPre c s₀) :
    WP isa (verifyWithPoints c points) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold verifyWithPoints
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The validated peer point.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine WP.seq (WP.mono (hpts hPc hM hQ) fun s₃ ⟨hP,hR⟩ => ?_)
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved,xo,hxo,hx,ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr),?_⟩
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_using []
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega_using []
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  split <;> split
  · rfl
  · rename_i ht hf
    exact False.elim (hf (decide_eq_true (hiff.mpr ht)))
  · rename_i hf ht
    exact False.elim (hf (hiff.mp (of_decide_eq_true ht)))
  · rfl


end Verification

end VG.Proof.Ecdsa.Verify.AArch64.JointKit
