module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOneD
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Finset.Attr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx.Reduction
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
public import VerifiedGarbage.Proof.Framework.X86_64.Lane0
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupDispatch
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! ### `Gcm.X86_64.StitchAvx8.Blocks`, which this module and modules that import it used -/

section

/-! ## Schedule -/

@[expose] public section

section

/-! # Connecting the hash and counter work to the fixed AES schedules -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs q8 prepCounter gh8 reduceFinal)
open VG.Spec.Gcm (Block)

/-- Number of hash inputs consumed before round `j`. -/
def hashCount (nr j : Nat) : Nat :=
  ((if nr = 10 then [1, 2, 3, 4, 5, 6, 7, 8]
    else if nr = 12 then [1, 2, 3, 5, 6, 7, 9, 10]
    else [1, 2, 4, 6, 8, 10, 11, 12]).filter (fun k => k < j)).length

/-- Counter preparation is split over the first two AES rounds. -/
def counterCount (j : Nat) : Nat := if j ≤ 1 then 0 else if j = 2 then 4 else 8

def workRegs : List XReg := .xmm1 :: .xmm2 :: ghRegs

/-- The three schedules have the same abstract steps: eight products,
then one reduction, with idle slots in the longer AES schedules. -/
theorem schedule_cases (hs : Bool) : ∀ nr < 15, nr = 10 ∨ nr = 12 ∨ nr = 14 → ∀ j < 15,
    1 ≤ j → j < nr →
    (hashCount nr j < 8 ∧ hashCount nr (j + 1) = hashCount nr j + 1 ∧
      j + 1 < nr ∧ q8 nr hs j = gh8 0 ((hashCount nr j + 1) % 8) hs) ∨
    (hashCount nr j = 8 ∧ hashCount nr (j + 1) = 8 ∧ j + 1 = nr ∧
      q8 nr hs j = reduceFinal) ∨
    (hashCount nr (j + 1) = hashCount nr j ∧ j + 1 < nr ∧ q8 nr hs j = []) := by
  intro nr _ hn j _ hj hjn
  rcases hn with rfl | rfl | rfl <;> interval_cases j <;> simp [hashCount, q8]

theorem q8_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j) (hjn : j < nr s₀)
    (h : StageInv s₀ start P X y c nc (hashCount (nr s₀) j) false s) (hs : Bool)
    (hx : HashSrc s₀ (hashBase start hs) start.mem X) :
    WP isa (.block (q8 (nr s₀) hs j)) s fun t =>
      StageInv s₀ start P X y c nc (hashCount (nr s₀) (j + 1))
        (decide (nr s₀ ≤ j + 1)) t ∧ FlowFrame workRegs s t := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega_arith
  rcases schedule_cases hs _ hn hp.rounds j (by omega_arith) hj hjn with
    ⟨h8, hnext, hlt, hc⟩ | ⟨h8, hnext, he, hc⟩ | ⟨hnext, hlt, hc⟩
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega_arith)]
    exact WP.mono (h.hashStep hp h8 hs hx) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · rw [hc, hnext, he, show decide (nr s₀ ≤ nr s₀) = true from decide_eq_true (Nat.le_refl _)]
    rw [h8] at h
    exact h.finishHash hp
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega_arith)]
    exact WP.block_nil ⟨h, .refl _ _⟩
 
/-- The counter work appended to the hash work in each AES round. -/
def counterWork (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 2 then
    (List.range 4).flatMap (fun i => prepCounter (4 * (j - 1) + i)) else []

theorem counters_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c nh : Nat} {finished : Bool} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j)
    (h : StageInv s₀ start P X y c (counterCount j) nh finished s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block (counterWork j)) s fun t =>
      StageInv s₀ start P X y c (counterCount (j + 1)) nh finished t ∧
        FlowFrame workRegs s t := by
  by_cases h1 : j = 1
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  by_cases h2 : j = 2
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · have hgt : 2 < j := by omega_arith
    simp only [counterWork, show ¬(1 ≤ j ∧ j ≤ 2) from by omega_arith, ite_false]
    have he : counterCount (j + 1) = counterCount j := by
      simp only [counterCount, show ¬j ≤ 1 from by omega_arith,
        show ¬j + 1 ≤ 1 from by omega_arith, show j + 1 ≠ 2 from by omega_arith, h2, ite_false]
    rw [he]
    exact WP.block_nil ⟨h, .refl _ _⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Rounds -/
section

/-! # Eight AES states with the verified hash and counter schedule -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs q8 aesFixed)
open VG.Spec.Gcm (Block)

/-- The first two encryption batches omit hashing while filling the pipeline. -/
def roundWork (nr : Nat) (hashing hs : Bool) (j : Nat) : List Instr :=
  (if hashing then q8 nr hs j else []) ++ counterWork j

def RoundInv (s₀ start : State) (P X : Nat → Block) (y : Block) (c : Nat)
    (hashing : Bool) (j : Nat) (s : State) : Prop :=
  StageInv s₀ start P X y c (counterCount j)
    (if hashing then hashCount (nr s₀) j else 0) (hashing && decide (nr s₀ ≤ j)) s

theorem roundWork_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing hs : Bool) (j : Nat)
    (hj : 1 ≤ j) (hjn : j < nr s₀) (h : RoundInv s₀ start P X y c hashing j s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (hashBase start hs) start.mem X) :
    WP isa (.block (roundWork (nr s₀) hashing hs j)) s fun t =>
      RoundInv s₀ start P X y c hashing (j + 1) t ∧ FlowFrame workRegs s t := by
  cases hashing with
  | false => exact counters_ok hp j hj h hv
  | true =>
    have hh : StageInv s₀ start P X y c (counterCount j) (hashCount (nr s₀) j) false s := by
      simpa only [RoundInv, Bool.true_eq, ite_true, Bool.true_and,
        show decide (nr s₀ ≤ j) = false from decide_eq_false (by omega_arith)] using h
    rw [roundWork, ite_eq_left rfl, WP.block_append_iff]
    refine WP.mono (q8_ok hp j hj hjn hh hs (hx rfl))
      fun t ⟨ht, hf⟩ => ?_
    exact WP.mono (counters_ok hp j hj ht hv) fun u ⟨hu, hfu⟩ => ⟨hu, hf.trans hfu⟩

theorem aesPipeline_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing hs : Bool)
    (h : RoundInv s₀ start P X y c hashing 1 s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (hashBase start hs) start.mem X) :
    WP isa (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing hs)) s fun t =>
      (∀ b ∈ aregs, VG.Proof.Aes.X86_64.AesNi.st (t.lane b 0) =
        Spec.Aes.cipher (nr s₀) (sch s₀) (VG.Proof.Aes.X86_64.AesNi.st (s.lane b 0))) ∧
      RoundInv s₀ start P X y c hashing (nr s₀) t := by
  have hpos : 0 < nr s₀ := by rcases hp.rounds with h | h | h <;> omega_arith
  refine WP.mono (aesFixed_ok (nr s₀) hpos aregs (by decide) (by decide)
    (roundWork (nr s₀) hashing hs) (RoundInv s₀ start P X y c hashing)
    (fun _ _ h => h.env.keys hp) (fun j hj hjn s h => ?_)
    (fun _ _ _ h hf => h.yframe hf) (fun s h => ?_) s h)
    fun t ⟨ha, hq⟩ => ⟨fun b hb => ha b hb 0 (by decide), hq⟩
  · refine WP.mono (roundWork_ok hp hashing hs j hj hjn h hv hx)
      fun t ⟨ht, hf⟩ => ⟨ht, fun b hb l hl => ?_⟩
    exact hf.lane b ((by decide : ∀ r ∈ aregs, r ∉ workRegs) b hb) l (by
      change l < 1 at hl; omega_arith)
  · simp only [VG.Proof.Aes.X86_64.AesNi.ea_at, BitVec.ofInt_natCast,
      BitVec.add_zero, h.env.r10, h.env.rdi]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Cipher -/
section

/-! # Loading and encrypting the eight counter templates -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs aesFixed)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_rev)
open VG.Proof.Aes.X86_64.AesNi (ea_at aesWith_eq)

theorem round_bounds : ∀ n < 15, n = 10 ∨ n = 12 ∨ n = 14 →
    hashCount n 1 = 0 ∧ hashCount n n = 8 ∧ counterCount n = 8 := by decide

theorem RoundInv.first {s₀ start s : State} {P X : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing : Bool)
    (h : StageInv s₀ start P X y c 0 0 false s) : RoundInv s₀ start P X y c hashing 1 s := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega_arith
  have h1 : ¬nr s₀ ≤ 1 := by rcases hp.rounds with h | h | h <;> omega_arith
  simp only [RoundInv, (round_bounds _ hn hp.rounds).1, counterCount,
    Nat.le_refl, ite_true, ite_self, decide_eq_false h1, Bool.and_false]
  exact h

theorem RoundInv.last {s₀ start s : State} {P X : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) {hashing : Bool} (h : RoundInv s₀ start P X y c hashing (nr s₀) s) :
    StageInv s₀ start P X y c 8 (if hashing then 8 else 0) hashing s := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega_arith
  simpa only [RoundInv, (round_bounds _ hn hp.rounds).2.1,
    (round_bounds _ hn hp.rounds).2.2, Nat.le_refl, decide_true, Bool.and_true] using h

theorem Templates.read {s₀ : State} {c : Nat} {m : Mem}
    (h : Templates s₀ c 0 m) (i : Nat) (hi : i < 8) :
    m.readW (templateAddr s₀ i) 128 =
      XBinOp.eval .pshufb (Nat.repeat inc32 (c + i) (cb s₀)) revMask := by
  have ht := h i hi
  simp only [Nat.not_lt_zero, ite_false, Nat.add_zero] at ht
  rw [← ht, blockAt_eq, pshufb_rev_rev]

theorem StageInv.ldframe {s₀ start s t : State} {P X : Nat → Block} {y : Block}
    {c nc nh : Nat} {finished : Bool} (h : StageInv s₀ start P X y c nc nh finished s)
    (hf : LdFrame s t) : StageInv s₀ start P X y c nc nh finished t := by
  refine ⟨h.env.move (fun r hr _ _ _ => hf.gpr r hr) hf.mem hf.rd hf.wr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.mem]; exact h.templates
  · rw [hf.lane .xmm2 (by decide) 0 (by decide)]; exact h.hash
  · intro hfin hn
    have hp := h.product hfin hn
    simpa only [VG.Proof.Gcm.X86_64.Pclmul.prod, State.proj_xmm,
      hf.lane .xmm8 (by decide) 0 (by decide), hf.lane .xmm9 (by decide) 0 (by decide),
      hf.lane .xmm10 (by decide) 0 (by decide)] using hp
  · intro r hr; rw [hf.gpr r hr]; exact h.regs r hr
  · rw [hf.mem]; exact h.frame

/-- What the code that starts a batch must leave: the counter blocks
`c` to `c + 7`, byte-reversed, in `aregs`. -/
def CountersIn (s₀ : State) (c : Nat) (s t : State) : Prop :=
  (∀ i < 8, t.lane (aregs.getD i .xmm3) 0 =
    XBinOp.eval .pshufb (Nat.repeat inc32 (c + i) (cb s₀)) revMask) ∧ LdFrame s t

/-- Loading the counter blocks from their templates. -/
theorem loads_ok {s₀ s : State} {P : Nat → Block} {c : Nat} (hp : SPre s₀) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) :
    WP isa (.block (Impl.Gcm.X86_64.StitchAvx8.loads 8)) s (CountersIn s₀ c s) :=
  WP.mono (loadCounters_ok s (fun i hi => by
    rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
    exact in_rdwr (in_sub hp.p_in (by omega_arith))) 8 (by decide)) fun t ⟨ht, hf⟩ =>
    ⟨fun i hi => by rw [ht i hi, ea_at, BitVec.ofInt_natCast, hE.r11]; exact hT.read i hi,
      LdFrame.of_yframe hf⟩

/-- The first two phases of `batchL ld`: the counters from `ld`, then encrypt them
while refreshing the next counters and, optionally, hashing eight inputs. -/
theorem cipherBatch_ok {s₀ s : State} {P X : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing hs : Bool) (hE : Env s₀ P s) {ld : List Instr}
    (hld : WP isa (.block ld) s (CountersIn s₀ c s))
    (hT : Templates s₀ c 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (hashBase s hs) s.mem X) :
    WP isa (.seq (.block ld)
      (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing hs))) s fun t =>
      (∀ i < 8, XBinOp.eval .pshufb (t.lane (aregs.getD i .xmm3) 0) revMask =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      StageInv s₀ s P X y c 8 (if hashing then 8 else 0) hashing t := by
  have h0 : StageInv s₀ s P X y c 0 0 false s :=
    ⟨hE, hT, hy, fun _ h => (h rfl).elim, fun _ _ => rfl, Frame.refl _ _⟩
  refine WP.seq (WP.mono hld fun t ⟨ht, hf⟩ => ?_)
  refine WP.mono (aesPipeline_ok hp hashing hs (RoundInv.first hp hashing
    (h0.ldframe hf)) hv hx) fun u ⟨hu, hQ⟩ => ?_
  refine ⟨fun i hi => ?_, hQ.last hp⟩
  apply Eq.symm
  apply aesWith_eq
  rw [hu _ (aregs_member i hi), ht i hi]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Batch -/
section

/-! # One complete eight-block pipeline batch -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs batch batchL xorData)
open VG.Spec.Gcm (Block inc32 blockAt)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Proof.Gcm.X86_64 (revMask)

def batchR (s : State) (j : Nat) : Region :=
  ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩

structure BatchPost (s₀ start : State) (ix : Bool) (P X : Nat → Block) (y : Block)
    (c j : Nat) (hashing : Bool) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ (c + 8) 0 s.mem
  hash : s.lane .xmm2 0 = if hashing then reduceB (accN X P y 8) else y
  data : ∀ k < 8, blockAt s.mem (start.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
    blockAt start.mem (srcAddr start ix (16 * (j + k))) ^^^
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  frame : Frame [batchR start j, workR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .r8 → s.gpr r = start.gpr r
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 16)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem batchL_ok {s₀ s : State} {P X : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (ix hashing hs : Bool) (j : Nat) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    {ld : List Instr} (hld : WP isa (.block ld) s (CountersIn s₀ c s))
    (hw : ∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwrap : (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64)
    (hsub : Region.Sub (batchR s j) (dR s₀))
    (hsr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (srcAddr s ix (16 * (j + k))) 16)
    (hss : ∀ a b, a < b → b < 8 → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩)
    (hsw : ∀ k < 8, Region.Disjoint ⟨srcAddr s ix (16 * (j + k)), 16⟩ (pR s₀))
    (hx : hashing = true → HashSrc s₀ (hashBase s hs) s.mem X) :
    WP isa (batchL ld (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) hs r else []) ix) s
      (BatchPost s₀ s ix P X y c j hashing) := by
  have hsep : (batchR s j).Disjoint (pR s₀) := hp.d_p.sub_left hsub
  simp only [batchL, show aregs.take 8 = aregs from rfl]
  apply seq_assoc
  refine WP.seq (WP.mono (cipherBatch_ok hp hashing hs hE hld hT hy hv hx)
    fun t ⟨hks, ht⟩ => ?_)
  rw [WP.block_append_iff]
  have hrdx : t.gpr .rdx = s.gpr .rdx := ht.regs _ (by decide)
  have hsa : ∀ d, srcAddr t ix d = srcAddr s ix d := fun d => by
    simp only [srcAddr, hrdx, ht.regs .rbx (by decide)]
  refine WP.mono (xorData_ok ix aregs j t (by decide) (fun k hk => by
    rw [ht.env.wr, hrdx, BitVec.ofInt_natCast]; exact hw k hk)
    (fun k hk => by rw [ht.env.rd, ht.env.wr, hsa]; exact hsr k hk)
    (fun a b hab hb => by rw [hrdx, hsa]; exact hss a b hab hb)
    (by rw [hrdx]; exact hwrap)) fun u ⟨hdata, hm, hg, hrd, hwr, hlanes⟩ => ?_
  rw [hrdx] at hdata hm
  simp only [hsa] at hdata
  have hmD : Frame [dR s₀] t.mem u.mem := hm.sub fun r hr' => by
    simp only [List.mem_singleton] at hr'
    subst r
    exact ⟨dR s₀, List.mem_singleton_self _, hsub⟩
  have hEu := ht.env.writeData hp hg hrd hwr hmD
  have hTu : Templates s₀ (c + 8) 0 u.mem := ht.templates.next.frame hm (by
    intro r hr'; simp only [List.mem_singleton] at hr'; subst r
    exact hsep.symm.sub_left (Offset.sub_base (pp s₀) (d := 640) (n := 128) (k := 1024) (by decide)))
  have hDu : ∀ k < 8, blockAt u.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
      blockAt s.mem (srcAddr s ix (16 * (j + k))) ^^^
        ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := by
    intro k hk
    have hks' := hks k hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < aregs.length from hk), Option.getD_some] at hks'
    rw [hdata k hk]
    refine congrArg₂ (fun a b : Block => a ^^^ b) ?_ hks'
    exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame ht.frame (by
      intro r hr'; simp only [List.mem_singleton] at hr'; subst r
      exact (hsw k hk).sub_right (work_sub_p s₀))
  have hFu : Frame [batchR s j, workR s₀] s.mem u.mem :=
    (ht.frame.mono (by simp)).trans (hm.mono (by simp [batchR, aregs]))
  refine WP.mono (bump_ok u) fun v ⟨hv8, hvg, hvm, hvl, hvrd, hvwr⟩ => ?_
  refine ⟨hEu.move (fun r _ _ h8 _ => hvg r h8) hvm hvrd hvwr,
    hvm ▸ hTu, ?_, ?_, hvm ▸ hFu, ?_, ?_⟩
  · rw [hvl, hlanes .xmm2 (by decide) 0 (by decide)]; exact ht.hash
  · rw [hvm]; exact hDu
  · intro r hrax hr8; rw [hvg r hr8, hg]; exact ht.regs r hrax
  · rw [hv8, hg, ht.regs .r8 (by decide), hv, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 32 (c + 8) + BitVec.ofNat 32 8 = BitVec.ofNat 32 (c + 16)
    rw [← BitVec.ofNat_add]


theorem batch_ok {s₀ s : State} {P X : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (ix hashing hs : Bool) (j : Nat) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hw : ∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwrap : (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64)
    (hsub : Region.Sub (batchR s j) (dR s₀))
    (hsr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (srcAddr s ix (16 * (j + k))) 16)
    (hss : ∀ a b, a < b → b < 8 → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩)
    (hsw : ∀ k < 8, Region.Disjoint ⟨srcAddr s ix (16 * (j + k)), 16⟩ (pR s₀))
    (hx : hashing = true → HashSrc s₀ (hashBase s hs) s.mem X) :
    WP isa (batch (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) hs r else []) ix) s
      (BatchPost s₀ s ix P X y c j hashing) :=
  batchL_ok hp ix hashing hs j hE hT hy hv (loads_ok hp hE hT) hw hwrap hsub hsr hss hsw hx
end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## DataInv -/
section

/-! # The prefix of data already transformed by counter mode -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

/-- How far past block `k` of the output its data is read: nothing in place,
`rbx` (`src - dst`) out of place (`ix`). -/
def off (s₀ : State) (ix : Bool) : Addr := if ix then s₀.gpr .rbx else BitVec.ofNat 64 0

/-- Where the data of block `k` is read. -/
abbrev srcBlk (s₀ : State) (ix : Bool) (k : Nat) : Addr := bAddr s₀ k + off s₀ ix

/-- The blocks of the data, as the loop reads them: readable, apart from the
working space, and each apart from the output blocks before it. -/
structure SrcOk (s₀ : State) (ix : Bool) : Prop where
  rd : ∀ k < nb s₀, InRegions (s₀.rd ++ s₀.wr) (srcBlk s₀ ix k) 16
  sep : ∀ k < nb s₀, Region.Disjoint ⟨dp s₀, 16 * k⟩ ⟨srcBlk s₀ ix k, 16⟩
  p : ∀ k < nb s₀, Region.Disjoint ⟨srcBlk s₀ ix k, 16⟩ (pR s₀)

/-- Blocks before `c` of the output hold the ciphertext; the data of the
others is still there to be read. -/
def DataInv (s₀ : State) (ix : Bool) (c : Nat) (m : Mem) : Prop :=
  ∀ k < nb s₀, (k < c → blockAt m (bAddr s₀ k) = ctb s₀ k) ∧
    (c ≤ k → blockAt m (srcBlk s₀ ix k) = blk s₀ k)

theorem bAddr_add (s₀ : State) (g k : Nat) :
    bAddr s₀ g + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by
  simp only [bAddr, Offset.add_add]
  congr 2
  omega_arith

theorem bAddr_toNat {s₀ : State} (hp : SPre s₀) (k : Nat) (hk : k < nb s₀) :
    (bAddr s₀ k).toNat = (dp s₀).toNat + 16 * k := by
  have hw := hp.wrap_d
  rw [bAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith : 16 * k < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith)]

theorem srcBlk_false (s₀ : State) (k : Nat) : srcBlk s₀ false k = bAddr s₀ k := by
  simp only [srcBlk, off, Bool.false_eq_true, ite_false, BitVec.add_zero]

/-- In place, the data is the output. -/
theorem SrcOk.inplace {s₀ : State} (hp : SPre s₀) : SrcOk s₀ false where
  rd k hk := by rw [srcBlk_false]; exact in_rdwr (in_sub hp.d_in (by omega_arith))
  sep k hk := by
    rw [srcBlk_false]; have hw := hp.wrap_d
    exact Offset.base_disjoint (dp s₀) (by omega_arith) (by omega_arith)
  p k hk := by
    rw [srcBlk_false]
    exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega_arith))

/-- The data of block `c + i`, at `rdx + 16 j` at block `c`, and `rbx` as at
the start. -/
theorem srcAddr_eq' {s₀ s : State} (ix : Bool) {c j : Nat}
    (ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c)
    (hrbx : s.gpr .rbx = s₀.gpr .rbx) (i : Nat) : srcAddr s ix (16 * (j + i)) = srcBlk s₀ ix (c + i) := by
  have e : s.gpr .rdx + BitVec.ofNat 64 (16 * (j + i)) = bAddr s₀ (c + i) := by
    rw [show 16 * (j + i) = 16 * j + 16 * i by omega_arith, ← Offset.add_add, ha, bAddr_add]
  cases ix
  · rw [srcAddr_false, srcBlk_false, e]
  · simp only [srcAddr, srcBlk, off, ite_true, hrbx]
    rw [BitVec.add_assoc, BitVec.add_comm (s₀.gpr .rbx), ← BitVec.add_assoc, e]

/-- Output blocks `j + a` and data blocks `j + b` for `a < b < n`, from block
`c` on, are apart. -/
theorem SrcOk.sepAt {s₀ s : State} {ix : Bool} (hp : SPre s₀) (hS : SrcOk s₀ ix) {c j n : Nat}
    (hcn : c + n ≤ nb s₀) (ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c)
    (hrbx : s.gpr .rbx = s₀.gpr .rbx) :
    ∀ a b, a < b → b < n → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩ := by
  intro a b hab hb
  have e : s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)) = bAddr s₀ (c + a) := by
    rw [show 16 * (j + a) = 16 * j + 16 * a by omega_arith, ← Offset.add_add, ha, bAddr_add]
  rw [e, srcAddr_eq' ix ha hrbx]
  have hw := hp.wrap_d
  exact (hS.sep (c + b) (by omega_arith)).sub_left (Offset.sub_base (dp s₀) (by omega_arith))

/-- Writes apart from the output and the data keep `DataInv`. -/
theorem DataInv.frame {s₀ : State} {ix : Bool} {c : Nat} {m m' : Mem} {rs : List Region}
    (h : DataInv s₀ ix c m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, (dR s₀).Disjoint r)
    (hsrc : ∀ r ∈ rs, ∀ k < nb s₀, c ≤ k → Region.Disjoint ⟨srcBlk s₀ ix k, 16⟩ r) : DataInv s₀ ix c m' := by
  intro k hk
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr =>
      (hs r hr).sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega_arith)))).trans
      ((h k hk).1 hc)
  · exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr => hsrc r hr k hk hc)).trans ((h k hk).2 hc)

/-- Writes within the working space keep `DataInv`. -/
theorem DataInv.frameP {s₀ : State} {ix : Bool} {c : Nat} {m m' : Mem} {rs : List Region}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : DataInv s₀ ix c m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (pR s₀)) : DataInv s₀ ix c m' :=
  h.frame hf (fun r hr => hp.d_p.sub_right (hs r hr)) (fun r hr k hk _ => (hS.p k hk).sub_right (hs r hr))

/-- All the blocks done: the output is the ciphertext. -/
theorem DataInv.done {s₀ : State} {ix : Bool} {m : Mem} (h : DataInv s₀ ix (nb s₀) m) :
    ∀ k < nb s₀, blockAt m (bAddr s₀ k) = ctb s₀ k := fun k hk => (h k hk).1 hk

/-- At the start, from the data where the loop reads it. -/
theorem DataInv.initial {s₀ : State} {ix : Bool} {m : Mem}
    (h : ∀ k < nb s₀, blockAt m (srcBlk s₀ ix k) = blk s₀ k) : DataInv s₀ ix 0 m :=
  fun k hk => ⟨fun h0 => absurd h0 (Nat.not_lt_zero _), fun _ => h k hk⟩

theorem DataInv.batch {s₀ s t : State} {ix : Bool} {P X : Nat → Block} {y : Block}
    {c j : Nat} {hashing : Bool} (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : DataInv s₀ ix c s.mem)
    (hc : c + 8 ≤ nb s₀) (ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c)
    (hbx : s.gpr .rbx = s₀.gpr .rbx)
    (hb : BatchPost s₀ s ix P X y c j hashing t) : DataInv s₀ ix (c + 8) t.mem := by
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (16 * (j + i)) = bAddr s₀ (c + i) := by
    intro i
    rw [show 16 * (j + i) = 16 * j + 16 * i by omega_arith, ← Offset.add_add, ha, bAddr_add]
  have hm : Frame [⟨bAddr s₀ c, 128⟩, workR s₀] s.mem t.mem := by
    simpa only [batchR, ha] using hb.frame
  intro k hk
  refine ⟨fun hk8 => ?_, fun hk8 => ?_⟩
  · by_cases hin : c ≤ k
    · have hi : k - c < 8 := by omega_arith
      have hv := hb.data (k - c) hi
      rw [addr, show c + (k - c) = k by omega_arith] at hv
      rw [hv, srcAddr_eq' ix ha hbx, show c + (k - c) = k by omega_arith, (h k hk).2 hin]
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · have hw := hp.wrap_d
          exact Offset.disjoint (dp s₀) (d := 16 * k) (n := 16) (e := 16 * c) (k := 128)
            (by omega_arith) (by omega_arith) (by omega_arith)
        · exact (hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega_arith))).sub_right (work_sub_p s₀))]
      exact (h k hk).1 (by omega_arith)
  · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hw := hp.wrap_d
        exact (hS.sep k hk).symm.sub_right (Offset.sub_base (dp s₀) (by omega_arith))
      · exact (hS.p k hk).sub_right (work_sub_p s₀))]
    exact (h k hk).2 (by omega_arith)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Core -/
section

/-! # Data and hash positions shared by the encrypt and decrypt loops -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block ghashFrom blockAt)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Proof.Gcm.X86_64 (revMask)

def hashBlock (s₀ : State) (dec : Bool) (k : Nat) : Block := if dec then blk s₀ k else ctb s₀ k

def hashPrefix (s₀ : State) (dec : Bool) (g : Nat) : Block :=
  ghashFrom (hk s₀) (y₀ s₀) ((List.range g).map (hashBlock s₀ dec))

def HashLaw (s₀ : State) (P : Nat → Block) : Prop := ∀ X y,
  reduceB (accN X P y 8) = ghashFrom (hk s₀) y ((List.range 8).map X)

theorem ghash_append8 (h y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom h y ((List.range (g + 8)).map f) =
      ghashFrom h (ghashFrom h y ((List.range g).map f)) ((List.range 8).map fun i => f (g + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

structure CoreInv (s₀ : State) (ix : Bool) (P : Nat → Block) (dec : Bool) (c g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ ix c s.mem
  templates : Templates s₀ c 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ dec g
  c_le : c ≤ nb s₀
  g_le : g ≤ nb s₀

/-- What the setup leaves, but where the data is: the state before the
first batch. -/
structure ReadyC (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ 0 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + 8
  cursor : s.gpr .rdx = dp s₀
  remaining : s.gpr .r9 = s₀.gpr .r9
  hash : s.lane .xmm2 0 = y₀ s₀
  mask : s.lane .xmm0 0 = revMask
  base : XBinOp.eval .pshufb (s.lane .xmm7 0) revMask = cb s₀

theorem Ready.toC {s₀ s : State} {P : Nat → Block} (h : Ready s₀ P s) : ReadyC s₀ P s :=
  ⟨h.env, h.templates, h.counter, h.cursor, h.remaining, h.hash, h.mask, h.base⟩

/-- In place, the data is where the setup found it. -/
theorem Ready.src {s₀ s : State} {lo : Nat} {P : Nat → Block} (hp : SPre s₀ lo) (h : Ready s₀ P s) :
    ∀ k < nb s₀, blockAt s.mem (srcBlk s₀ false k) = blk s₀ k := fun k hk => by
  rw [srcBlk_false]
  exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame h.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega_arith)))

theorem CoreInv.initial {s₀ s : State} {ix : Bool} {P : Nat → Block}
    (h : ReadyC s₀ P s) (hsrc : ∀ k < nb s₀, blockAt s.mem (srcBlk s₀ ix k) = blk s₀ k) (dec : Bool) :
    CoreInv s₀ ix P dec 0 0 s := by
  refine ⟨h.env, DataInv.initial hsrc, h.templates, h.counter, ?_, ?_, ?_, Nat.zero_le _, Nat.zero_le _⟩
  · simpa only [bAddr, Nat.mul_zero, BitVec.add_zero] using h.cursor
  · simpa only [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.remaining
  · exact h.hash

theorem CoreInv.addr {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (h : CoreInv s₀ ix P dec c g s) (k : Nat) :
    s.gpr .rdx + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by rw [h.cursor, bAddr_add]

/-- `rbx` is as at the start. -/
theorem CoreInv.rbx {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (h : CoreInv s₀ ix P dec c g s) : s.gpr .rbx = s₀.gpr .rbx :=
  h.env.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem CoreInv.batchBounds {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ ix P dec c g s) (j : Nat) (hj : g + j = c) (hc : c + 8 ≤ nb s₀) :
    (∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16) ∧
    (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64 ∧ Region.Sub (batchR s j) (dR s₀) := by
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [h.addr, ← Nat.add_assoc, hj]
    exact in_sub hp.d_in (by omega_arith)
  · rw [h.cursor, bAddr_toNat hp g (by omega_arith)]
    have hw := hp.wrap_d
    omega_arith
  · change Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩ (dR s₀)
    rw [h.addr, hj]
    exact Offset.sub_base (dp s₀) (d := 16 * c) (n := 128) (k := 16 * nb s₀) (by omega_arith)

/-- What a batch at block `c` needs of its data. -/
theorem CoreInv.srcBounds {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (j : Nat) (hj : g + j = c)
    (hc : c + 8 ≤ nb s₀) :
    (∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (srcAddr s ix (16 * (j + k))) 16) ∧
    (∀ a b, a < b → b < 8 → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩) ∧
    (∀ k < 8, Region.Disjoint ⟨srcAddr s ix (16 * (j + k)), 16⟩ (pR s₀)) := by
  have ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c := by rw [h.addr, hj]
  refine ⟨fun k hk => ?_, hS.sepAt hp hc ha h.rbx, fun k hk => ?_⟩
  · rw [srcAddr_eq' ix ha h.rbx]; exact hS.rd _ (by omega_arith)
  · rw [srcAddr_eq' ix ha h.rbx]; exact hS.p _ (by omega_arith)

theorem CoreInv.bareBatchL {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (j : Nat) (hj : g + j = c)
    (hc : c + 8 ≤ nb s₀) {ld : List Instr} (hld : WP isa (.block ld) s (CountersIn s₀ c s)) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batchL ld (nr s₀) 8 j (fun _ => []) ix) s
      (CoreInv s₀ ix P dec (c + 8) g) := by
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp j hj hc
  obtain ⟨hsr, hss, hsw⟩ := h.srcBounds hp hS j hj hc
  refine WP.mono (batchL_ok hp ix false false j h.env h.templates (X := fun _ => 0) h.hash h.counter hld
    hw hwrap hsub hsr hss hsw (fun he => Bool.noConfusion he)) fun t ht => ?_
  refine ⟨ht.env, h.data.batch hp hS hc (by rw [h.addr, hj]) h.rbx ht, ht.templates, ?_,
    (ht.regs _ (by decide) (by decide)).trans h.cursor,
    (ht.regs _ (by decide) (by decide)).trans h.remaining, ht.hash, hc, h.g_le⟩
  simpa only [Nat.add_assoc, Nat.reduceAdd] using ht.counter


theorem CoreInv.bareBatch {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (j : Nat) (hj : g + j = c)
    (hc : c + 8 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 j (fun _ => []) ix) s
      (CoreInv s₀ ix P dec (c + 8) g) :=
  h.bareBatchL hp hS j hj hc (loads_ok hp h.env h.templates)
end VG.Proof.Gcm.X86_64.StitchAvx8

end

end

end

/-! ### `Gcm.X86_64.StitchAvx8.Tail`, which this module and modules that import it used -/

section

/-! ### `Gcm.X86_64.StitchAvx.Loop`, which this module and modules that import it used -/

section

/-!
# Interleaved counter mode and GHASH in AVX: clearing the product

`zero_ok`: `zero` clears the product (`Prod.zero`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduceB prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.StitchAvx (aregs batch gq group ordE ordD first body dbody ghLoad lastG)
open VG.Impl.Gcm.X86_64.Stitch (storeCtr storeY)
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost kp nr cp yp dp nb pp kR cR yR dR pR sch ciph cb hk y₀ bAddr
  blk ctb in_sub in_sub_int in_rdwr addr_eq ghash_append16 nextE_ok nextD_ok store16_ok blocks_ctr32
  blockAt_writeW_sep')
open VG.Proof.Aes.X86_64.AesNi (Keys blockAt_frame)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## A group -/

/-- Clear the product. -/
theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx.zero) s fun s' => prod (s'.proj 0) = Prod.zero ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' := by
  refine WP.mono (WP.lane0 (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl (Pclmul.zero_ok (s.proj 0)))
    fun s' ⟨⟨z, o⟩, hi, hg⟩ => ⟨z, hg rfl, by simpa using o.mem, by simpa using o.rd, by simpa using o.wr,
      fun r hr l hl => ?_⟩
  rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using o.xmm r hr
  · refine hi r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h8, h9, h10⟩ := hr
    simp [Impl.Gcm.X86_64.StitchAvx.zero, vdst, h8, h9, h10]

end VG.Proof.Gcm.X86_64.StitchAvx

end

end

/-! ### `Gcm.X86_64.StitchAvx8.Loop`, which only this module used -/

section

/-! ## FinalCommon -/

@[expose] public section

section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blocksAt)

def Post (s₀ : State) (dec : Bool) (s : State) : Prop := if dec then DPost s₀ s else EPost s₀ s

theorem finish_complete {s₀ s : State} {ix : Bool} {lo : Nat} {P : Nat → Block} (hp : SPre s₀ lo) (dec : Bool)
    (hE : Env s₀ P s) (hD : DataInv s₀ ix (nb s₀) s.mem)
    (hc : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (nb s₀ + 8))
    (hy : s.lane .xmm2 0 = hashPrefix s₀ dec (nb s₀)) :
    WP isa (.block Impl.Gcm.X86_64.StitchAvx8.finish) s fun t =>
      Post s₀ dec t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
  refine WP.mono (finish_ok hp hE (nb s₀) hc) fun t ht => ?_
  obtain hsv : t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
    refine (ht.frame.readW (r := ⟨pp s₀ + BitVec.ofNat 64 816, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)).trans hE.saved
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.p_c.sub_left (Offset.sub_base (pp s₀) (d := 816) (n := 8) (k := 1024) (by decide))
    · exact hp.p_y.sub_left (Offset.sub_base (pp s₀) (d := 816) (n := 8) (k := 1024) (by decide))
  obtain hd : DataInv s₀ ix (nb s₀) t.mem := hD.frame ht.frame (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_c
    · exact hp.d_y) (fun _ _ k hk hc => absurd hk (by omega_using [hc]))
  have hb : ∀ k < nb s₀, Spec.Gcm.blockAt t.mem (bAddr s₀ k) = ctb s₀ k := hd.done
  obtain hm : blocksAt t.mem (dp s₀) (nb s₀) = (List.range (nb s₀)).map (ctb s₀) := by
    apply List.map_congr_left
    intro k hk
    exact hb k (List.mem_range.mp hk)
  obtain hf : Frame [cR s₀, yR s₀, dR s₀, pR s₀] s₀.mem t.mem :=
    (hE.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  refine ⟨?_, hsv⟩
  cases dec with
  | false =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy, hm]
    rfl
  | true =>
    refine ⟨blocks_ctr32 hb, ht.counter, ?_, hf, ht.regs, ht.rd, ht.wr⟩
    rw [ht.hash, hy]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## HashBatch -/
section

/-! # A batch hashes ciphertext before it can be overwritten -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

def lead (dec : Bool) : Nat := if dec then 0 else 16

def window (s₀ : State) (dec : Bool) (g : Nat) : Nat → Block := fun i => hashBlock s₀ dec (g + i)

/-- The blocks a batch at `g` hashes: encrypting, the ciphertext of the
batch before last, from `rdx`; decrypting, the batch's own data, where it
reads it (`hashBase s ix`: `rdx`, or, out of place, `rdx + rbx`). -/
theorem CoreInv.hashSrc {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (hcg : c = g + lead dec)
    (hc : c + 8 ≤ nb s₀) :
    HashSrc s₀ (hashBase s (dec && ix)) s.mem (window s₀ dec g) := by
  cases dec with
  | false =>
    obtain hb : ∀ k, hashBase s (false && ix) + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := fun k => by
      simp only [hashBase, Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.add_zero, h.addr]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [hb]; exact in_rdwr (in_sub hp.d_in (by change c = g + 16 at hcg; omega_using [hc, hk, hcg]))
    · rw [hb]
      exact hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * (g + k)) (n := 16) (k := 16 * nb s₀)
        (by change c = g + 16 at hcg; omega_using [hc, hk, hcg]))
    · have he : g + k < c := by change c = g + 16 at hcg; omega_using [hk, hcg]
      rw [hb, (h.data (g + k) (by change c = g + 16 at hcg; omega_using [hc, he])).1 he]
      rfl
  | true =>
    have hcg' : c = g := hcg
    subst hcg'
    obtain ha : s.gpr .rdx + BitVec.ofNat 64 (16 * 0) = bAddr s₀ c := by rw [h.addr, Nat.add_zero]
    obtain hb : ∀ k, hashBase s (true && ix) + BitVec.ofNat 64 (16 * k) = srcBlk s₀ ix (c + k) := fun k => by
      rw [← srcAddr_eq' ix ha h.rbx k, Nat.zero_add]
      rfl
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [hb]; exact hS.rd _ (by omega_using [hc, hk])
    · rw [hb]; exact hS.p _ (by omega_using [hc, hk])
    · rw [hb, (h.data (c + k) (by omega_using [hc, hk])).2 (by omega_using [])]
      rfl

theorem CoreInv.hashBatch {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (h : CoreInv s₀ ix P dec c g s) (hcg : c = g + lead dec)
    (hc : c + 8 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 (lead dec)
      (Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) (dec && ix)) ix) s
      (BatchPost s₀ s ix P (window s₀ dec g) (hashPrefix s₀ dec g) c (lead dec) true) := by
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp (lead dec) hcg.symm hc
  obtain ⟨hsr, hss, hsw⟩ := h.srcBounds hp hS (lead dec) hcg.symm hc
  exact batch_ok hp ix true (dec && ix) (lead dec) h.env h.templates h.hash h.counter hw hwrap hsub hsr hss hsw
    (fun _ => h.hashSrc hp hS hcg hc)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopStep -/
section

/-! # One iteration of either public-length loop -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

def threshold (dec : Bool) : Nat := if dec then 16 else 24

def tailSize (dec : Bool) : Nat := if dec then 8 else 16

structure LoopInv (s₀ : State) (ix : Bool) (P : Nat → Block) (dec : Bool) (g : Nat) (s : State) : Prop where
  core : CoreInv s₀ ix P dec (g + lead dec) g s
  multiple : g % 8 = 0
  tail_le : g + tailSize dec ≤ nb s₀

def body8 (dec : Bool) (nr : Nat) (ix : Bool) : Prog isa :=
  .seq (.block []) (.seq (Impl.Gcm.X86_64.StitchAvx8.batch nr 8 (lead dec)
    (Impl.Gcm.X86_64.StitchAvx8.q8 nr (dec && ix)) ix)
    (.block [.alu .add .rdx (.imm 128), .alu .sub .r9 (.imm 8),
      .alu .cmp .r9 (.imm (if dec then 16 else 24))]))

theorem body8_enc (nr : Nat) (ix : Bool) : body8 false nr ix = Impl.Gcm.X86_64.StitchAvx8.encBody8 nr ix := rfl
theorem body8_dec (nr : Nat) (ix : Bool) : body8 true nr ix = Impl.Gcm.X86_64.StitchAvx8.decBody8 nr ix := rfl
theorem loopStep_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (body8 dec (nr s₀) ix) s fun t => LoopInv s₀ ix P dec (g + 8) t ∧
      t.cf = some (decide (nb s₀ - (g + 8) < threshold dec)) := by
  obtain hc : g + lead dec + 8 ≤ nb s₀ := by cases dec <;> simp [threshold, lead] at hn ⊢ <;> omega_using [hn]
  obtain htail : g + 8 + tailSize dec ≤ nb s₀ := by cases dec <;> simp [threshold, tailSize] at hn ⊢ <;> omega_using [hn]
  obtain hec : g + lead dec + 8 = g + 8 + lead dec := by omega_using []
  have hm := h.multiple
  obtain hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.block_nil (WP.seq (WP.mono
    (h.core.hashBatch hp hS rfl hc) fun u hu => ?_)))
  refine WP.mono (next8_ok u (if dec then 16 else 24)) fun t ⟨htD, htN, htC, htG, htX, htM, htR, htW⟩ => ?_
  obtain un : u.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g) :=
    (hu.regs _ (by decide) (by decide)).trans h.core.remaining
  obtain un8 : u.gpr .r9 - 8 = BitVec.ofNat 64 (nb s₀ - (g + 8)) := by
    rw [un]
    change BitVec.ofNat 64 (nb s₀ - g) - BitVec.ofNat 64 8 = _
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  obtain hlimit : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  obtain hDt := h.core.data.batch hp hS hc (by rw [h.core.addr]) h.core.rbx hu
  rw [hec] at hDt
  refine ⟨⟨⟨hu.env.move (fun r _ hdx _ h9 => htG r hdx h9) htM htR htW,
    htM ▸ hDt, ?_, ?_, ?_, htN.trans un8, ?_, by omega_using [hc], by omega_using [hc]⟩, by omega_using [hm], htail⟩, ?_⟩
  · rw [htM, ← hec]; exact hu.templates
  · rw [htG _ (by decide) (by decide), hu.counter]
    congr 2
    omega_using []
  · rw [htD, hu.regs _ (by decide) (by decide), h.core.cursor]
    exact bAddr_add s₀ g 8
  · rw [htX, hu.hash]
    change VG.Proof.Gcm.X86_64.Pclmul.reduceB (accN (window s₀ dec g) P (hashPrefix s₀ dec g) 8) = _
    rw [hlaw]
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ dec) g).symm
  · rw [htC, un8, hlimit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn64])]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## HashBuffer -/
section

/-! # Hashing the last two batches at the end of encryption -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

theorem accN_congr {X X' P P' : Nat → Block} (y : Block)
    (hx : ∀ i < 8, X i = X' i) (hp : ∀ i < 8, P i = P' i) (n : Nat) (hn : n ≤ 8) :
    accN X P y n = accN X' P' y n := by
  induction n with
  | zero => simp only [accN, List.range_zero, List.foldl_nil]
  | succ n ih =>
    rw [accN_succ, accN_succ, ih (by omega_using [hn])]
    obtain hk : (n + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [hashInput, hx _ hk, hp _ hk]

def hashClobbers : List XReg := ghRegs ++ [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11]

theorem hashBuffer_ok {s₀ s : State} {P X : Nat → Block} (hp : SPre s₀) (hlaw : HashLaw s₀ P)
    (hE : Env s₀ P s) (d : Nat)
    (hR : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (d + 16 * i)) 16)
    (hB : ∀ i < 8, blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (d + 16 * i)) = X i) :
    WP isa (.block (hash8 d)) s fun t => Env s₀ P t ∧
      t.lane .xmm2 0 = Spec.Gcm.ghashFrom (hk s₀) (s.lane .xmm2 0) ((List.range 8).map X) ∧
      YFrame hashClobbers s t := by
  refine WP.mono (hash8_ok s d
    (fun k hk => by
      rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
      exact in_rdwr (in_sub hp.p_in (by omega_using [hk])))
    (fun k hk => by rw [ea_at, BitVec.ofInt_natCast]; exact hR k hk)
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 768) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
        exact in_rdwr (in_sub hp.p_in (off := 784) (by decide)))
    (by rw [ea_at, BitVec.ofInt_natCast, hE.r11]; exact hE.poly)) fun t ⟨ht, hf⟩ => ?_
  refine ⟨hE.yframe hf, ?_, hf⟩
  rw [ht, accN_congr (s.lane .xmm2 0) (fun i hi => ?_) (fun i hi => ?_) 8 (by decide), hlaw]
  · rw [bufferBlock, ea_at, ea_at, BitVec.ofInt_natCast, BitVec.ofInt_natCast, hE.r11, ← hB i hi,
      VG.Proof.Gcm.X86_64.blockAt_eq]
    exact congrArg _ hE.mask
  · simp only [bufferPower, ea_at, BitVec.ofInt_natCast, hE.r11]
    rw [show 16 * (8 + i) = 128 + 16 * i by omega_using []]
    exact hE.powers i hi

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## FinalEnc -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.StitchAvx8 (hash8)

/-- After the pipeline's last two batches are hashed: the blocks before
`g + 16` encrypted and hashed, the counters of the next eight prepared, and
`nb - g - 16 < 8` blocks left. -/
structure TailReady (s₀ : State) (ix : Bool) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ ix (g + 16) s.mem
  templates : Templates s₀ (g + 16) 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (g + 16 + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ false (g + 16)
  le : g + 16 ≤ nb s₀
  lt : nb s₀ - g < 24

theorem finalHash_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P false g s) (hn : nb s₀ - g < 24) :
    WP isa (.block (hash8 0 ++ hash8 128)) s (TailReady s₀ ix P g) := by
  have hle : g + 16 ≤ nb s₀ := h.tail_le
  have hd : DataInv s₀ ix (g + 16) s.mem := h.core.data
  obtain hR : ∀ e, e ≤ 8 → ∀ i < 8,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (16 * e + 16 * i)) 16 := by
    intro e he i hi
    rw [show 16 * e + 16 * i = 16 * (e + i) by omega_using [], h.core.addr, h.core.env.rd, h.core.env.wr]
    exact in_rdwr (in_sub hp.d_in (by omega_using [hle, he, hi]))
  obtain hB : ∀ e, e ≤ 8 → ∀ i < 8, Spec.Gcm.blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * e + 16 * i)) = window s₀ false (g + e) i := by
    intro e he i hi
    rw [show 16 * e + 16 * i = 16 * (e + i) by omega_using [], h.core.addr, ← Nat.add_assoc,
      (hd _ (by omega_using [hle, he, hi])).1 (by omega_using [he, hi])]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hashBuffer_ok (X := window s₀ false g) hp hlaw h.core.env 0 (hR 0 (by decide)) (hB 0 (by decide)))
    fun t ⟨htE, htY, htF⟩ => ?_
  refine WP.mono (hashBuffer_ok (X := window s₀ false (g + 8)) hp hlaw htE 128
    (by simpa only [htF.rd, htF.wr, htF.gpr] using hR 8 (by decide))
    (by simpa only [htF.mem, htF.gpr] using hB 8 (by decide))) fun v ⟨hvE, hvY, hvF⟩ => ?_
  refine ⟨hvE, ?_, ?_, ?_, ?_, ?_, ?_, hle, hn⟩
  · rw [hvF.mem, htF.mem]; exact hd
  · rw [hvF.mem, htF.mem]; exact h.core.templates
  · rw [hvF.gpr, htF.gpr]; exact h.core.counter
  · rw [hvF.gpr, htF.gpr]; exact h.core.cursor
  · rw [hvF.gpr, htF.gpr]; exact h.core.remaining
  · rw [hvY, htY, h.core.hash]
    change Spec.Gcm.ghashFrom (hk s₀)
      (Spec.Gcm.ghashFrom (hk s₀) (hashPrefix s₀ false g) ((List.range 8).map (fun i => hashBlock s₀ false (g + 0 + i))))
      ((List.range 8).map (fun i => hashBlock s₀ false (g + 8 + i))) = _
    simp only [hashPrefix, Nat.add_zero]
    rw [← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) g,
      ← ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ false) (g + 8)]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopRun -/
section

/-! # The loops stop with fewer than `threshold` blocks left -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)

theorem loopRun_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hn : g + threshold dec ≤ nb s₀) :
    WP isa (.loop (body8 dec (nr s₀) ix) .ae) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g t := by
  let I : Nat → State → Prop := fun m t => ∃ g,
    m = nb s₀ - g ∧ g + threshold dec ≤ nb s₀ ∧ LoopInv s₀ ix P dec g t
  obtain step : ∀ m t, I m t → WP isa (body8 dec (nr s₀) ix) t fun u =>
      (eval .ae u = some false ∧ ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g u) ∨
      (eval .ae u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨g, rfl, hn, h⟩
    refine WP.mono (loopStep_ok hp hS hlaw h hn) fun u ⟨hu, hcf⟩ => ?_
    by_cases halt : nb s₀ - (g + 8) < threshold dec
    · exact .inl ⟨by simp only [eval, hcf, halt, decide_true, Option.map_some, Bool.not_true],
        g + 8, halt, hu⟩
    · have hg := hu.core.g_le
      refine .inr ⟨by simp only [eval, hcf, halt, decide_false, Option.map_some, Bool.not_false],
        nb s₀ - (g + 8), ?_, g + 8, rfl, by omega_using [halt, hg], hu⟩
      have ht := hu.tail_le
      obtain hl : 0 < tailSize dec := by cases dec <;> decide
      omega_using [hg]
  exact WP.loop (M := isa) I step (nb s₀ - g) s ⟨g, rfl, hn, h⟩

theorem loopMaybe_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P dec g s)
    (hcf : s.cf = some (decide (nb s₀ - g < threshold dec))) :
    WP isa (.ite .b (.block []) (.loop (body8 dec (nr s₀) ix) .ae)) s fun t =>
      ∃ g, nb s₀ - g < threshold dec ∧ LoopInv s₀ ix P dec g t := by
  refine WP.ite (decide (nb s₀ - g < threshold dec)) (by simp only [eval, hcf]) (fun he => ?_) (fun he => ?_)
  · exact WP.block_nil ⟨g, by simpa using he, h⟩
  · have hn : ¬nb s₀ - g < threshold dec := by simpa using he
    have hg := h.core.g_le
    exact loopRun_ok hp hS hlaw h (by omega_using [hn, hg])

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## LoopStart -/
section

/-! # Filling the pipeline -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch batchL regCounters)

theorem CoreInv.yframe {s₀ s t : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {c g : Nat} {rs : List XReg}
    (h : CoreInv s₀ ix P dec c g s) (hf : YFrame rs s t) (hy : .xmm2 ∉ rs) : CoreInv s₀ ix P dec c g t := by
  refine ⟨h.env.yframe hf, hf.mem ▸ h.data, hf.mem ▸ h.templates, ?_, ?_, ?_, ?_, h.c_le, h.g_le⟩
  · rw [hf.gpr]; exact h.counter
  · rw [hf.gpr]; exact h.cursor
  · rw [hf.gpr]; exact h.remaining
  · rw [hf.lane _ hy 0 (by decide)]; exact h.hash

theorem firstEnc_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} (hp : SPre s₀) (hS : SrcOk s₀ ix)
    (h : ReadyC s₀ P s) (hsrc : ∀ k < nb s₀, blockAt s.mem (srcBlk s₀ ix k) = blk s₀ k) :
    WP isa (.seq (batchL regCounters (nr s₀) 8 0 (fun _ => []) ix)
      (batch (nr s₀) 8 8 (fun _ => []) ix)) s (LoopInv s₀ ix P false 0) := by
  refine WP.seq (WP.mono ((CoreInv.initial h hsrc false).bareBatchL hp hS 0 rfl (by have := hp.nb16; omega)
    (WP.mono (regCounters_ok s h.mask) fun t ⟨ht, hf⟩ =>
      ⟨fun i hi => by rw [ht i hi, h.base, Nat.zero_add], hf⟩))
    fun u hu => ?_)
  exact WP.mono (hu.bareBatch hp hS 8 rfl (by have := hp.nb16; omega)) fun t ht =>
    ⟨ht, rfl, hp.nb16⟩

theorem firstDec_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} (hp : SPre s₀) (h : ReadyC s₀ P s)
    (hsrc : ∀ k < nb s₀, blockAt s.mem (srcBlk s₀ ix k) = blk s₀ k) :
    WP isa (.block []) s (LoopInv s₀ ix P true 0) :=
  WP.block_nil ⟨CoreInv.initial h hsrc true, rfl,
    by have := hp.nb16; change 0 + 8 ≤ nb s₀; omega⟩

theorem LoopInv.compare {s₀ s : State} {ix : Bool} {P : Nat → Block} {dec : Bool} {g : Nat}
    (h : LoopInv s₀ ix P dec g s) :
    WP isa (.block [.alu .cmp .r9 (.imm (if dec then 16 else 24))]) s fun t =>
      LoopInv s₀ ix P dec g t ∧ t.cf = some (decide (nb s₀ - g < threshold dec)) := by
  refine WP.mono (cmp8_ok s (if dec then 16 else 24)) fun t ⟨hcf, hf⟩ => ?_
  refine ⟨⟨h.core.yframe hf (by decide), h.multiple, h.tail_le⟩, ?_⟩
  obtain hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  obtain he : ((if dec then 16 else 24 : BitVec 32).signExtend 64).toNat = threshold dec := by
    cases dec <;> rfl
  rw [hcf, h.core.remaining, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn]), he]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

end

end


/-!
# The blocks after the pipeline's

`tail_ok`: once the pipeline has encrypted and hashed the blocks before
`g + 16` (`TailReady`), with `t = nb - g - 16 < 8` blocks left,
`StitchAvx8.tailT` and `finish` meet `EPost`. With blocks left, `ksTail`
encrypts the eight counters the pipeline prepared, of the blocks from
`g + 16` on, and stores their keystream at `scratch + 832` (`ksTail_ok`);
`tailSetup` advances the counter by `t` and points `rax` at the powers
`H'ᵗ` … `H'` (`tailSetup_ok`); `StitchZH`'s loop encrypts the `t` blocks
and adds their products with their powers (`StitchZH.remLoop_ok`), which
`tailEnd` reduces into `Y`, for powers whose products add up to `GHASH`
(`TailLaw`, which `Ok.lean` proves of the powers the setup stores).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs aesFixed ksTail tailSetup tailEnd tailT finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32 blockAt ghashFrom)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_rev)
open VG.Proof.Aes.X86_64.AesNi (ea_at aesWith_eq)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)

/-- What the products of the last `r` blocks with the powers of the
pipeline add up to: `GHASH` over the `r` blocks (`Ok.lean` proves it of the
powers the setup stores, `H'⁸⁻ᵏ` at `128 + 16 k`). -/
def TailLaw (s₀ : State) (P : Nat → Block) : Prop :=
  ∀ r, 1 ≤ r → r ≤ 7 → ∀ (X : Nat → Block) (y : Block),
    reduceB (StitchZH.accR X (fun j => P (8 - r + j)) y r) = ghashFrom (hk s₀) y ((List.range r).map X)

/-- Where `ksTail _ off` stores the keystream of block `i`. -/
abbrev ksAddr (s₀ : State) (i : Nat) (off : Nat := 832) : Addr := pp s₀ + BitVec.ofNat 64 (off + 16 * i)
abbrev ksR (s₀ : State) (off : Nat := 832) : Region := ⟨pp s₀ + BitVec.ofNat 64 off, 128⟩

/-- Where `ksTail` may store the keystream without overwriting what `Env`
keeps: below the constants at `scratch + 768`, or after them. -/
abbrev KsOff (off : Nat) : Prop := off = 384 ∨ off = 512 ∨ off = 832

/-! ## The keystream -/

theorem ksStores_ok (s : State) (p : Addr) (off : Nat) (hoff : off + 128 ≤ 1024) (hr11 : s.gpr .r11 = p)
    (hin : ∀ i < 8, InRegions s.wr (p + BitVec.ofNat 64 (off + 16 * i)) 16)
    (hwrap : p.toNat + 1024 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).map fun i =>
      .vmovdquStore .l128 (at_ .r11 (off + 16 * i)) (aregs.getD i .xmm3))) s fun t =>
      (∀ i < n, t.mem.readW (p + BitVec.ofNat 64 (off + 16 * i)) 128 = s.lane (aregs.getD i .xmm3) 0) ∧
      Frame [⟨p + BitVec.ofNat 64 off, 128⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ (∀ r l, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega_arith), Frame.refl _ _, rfl, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ksStores_ok s p off hoff hr11 hin hwrap n (by omega_arith)) fun t ⟨v, f, g, l, rd, wr⟩ => ?_
    simp only [List.map_cons, List.map_nil]
    obtain ea : t.ea (at_ .r11 (off + 16 * n)) = p + BitVec.ofNat 64 (off + 16 * n) := by
      rw [ea_at, BitVec.ofInt_natCast, g, hr11]
    obtain hw : InRegions t.wr (p + BitVec.ofNat 64 (off + 16 * n)) 16 := by rw [wr]; exact hin n (by omega_arith)
    rw [WP.block_cons_iff]
    refine ⟨t.setMem (t.mem.writeW (p + BitVec.ofNat 64 (off + 16 * n)) (t.xmm (aregs.getD n .xmm3))),
      by simp only [isa, exec, State.store128_eq, ea, hw, ite_true], WP.block_nil ⟨fun i hi => ?_, ?_,
        by rw [State.setMem_gpr, g], fun r l' => by rw [State.setMem_lane, l], by rw [State.setMem_rd, rd],
        by rw [State.setMem_wr, wr]⟩⟩
    · simp only [State.setMem_mem]
      by_cases hin' : i = n
      · subst hin'
        rw [Mem.readW_writeW_self _ _ 16 _ (by decide), ← l]
        rfl
      · rw [Mem.readW_writeW_sep (Offset.sep p (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
        exact v i (by omega_arith)
    · simp only [State.setMem_mem]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains p (by omega_arith) (by omega_arith) (by omega_arith))

/-- A write of the keystream keeps what the working space holds outside it. -/
theorem ks_read {s₀ : State} {off : Nat} {m m' : Mem} (hf : Frame [ksR s₀ off] m m') (hoff : off + 128 ≤ 1024)
    (d n : Nat) (hd : d + n ≤ off ∨ off + 128 ≤ d) (hdn : d + n ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) = m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, n⟩)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint (pp s₀) hd (by omega_arith) (by omega_arith)
  · omega_arith

theorem Env.ksFrame {s₀ u v : State} {P : Nat → Block} {off : Nat} (hoff : KsOff off) (h : Env s₀ P u)
    (hf : Frame [ksR s₀ off] u.mem v.mem)
    (hg : v.gpr = u.gpr) (hrd : v.rd = u.rd) (hwr : v.wr = u.wr) : Env s₀ P v := by
  obtain ho : off + 128 ≤ 1024 := by rcases hoff with h | h | h <;> omega_arith
  refine ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rcx,
    by rw [hg]; exact h.r11, by rw [hg]; exact h.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [hg]; exact h.other r h1 h2 h3 h4 h5 h6,
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega_arith)⟩),
    fun k hk => (ks_read hf ho (128 + 16 * k) 16 (by omega) (by omega_using [hk])).trans (h.powers k hk),
    (ks_read hf ho 768 16 (by omega) (by omega_using [])).trans h.mask,
    (ks_read hf ho 784 16 (by omega) (by omega_using [])).trans h.poly,
    (ks_read hf ho 800 8 (by omega) (by omega_using [])).trans h.rounds,
    (ks_read hf ho 808 8 (by omega) (by omega_using [])).trans h.data,
    (ks_read hf ho 816 8 (by omega) (by omega_using [])).trans h.saved,
    by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr⟩

theorem ksTail_ok {s₀ s : State} {lo : Nat} {P : Nat → Block} {c off : Nat} (hp : SPre s₀ lo) (hoff : KsOff off)
    (hE : Env s₀ P s) (hT : Templates s₀ c 0 s.mem) :
    WP isa (ksTail (nr s₀) off) s fun t => Env s₀ P t ∧
      (∀ i < 8, blockAt t.mem (ksAddr s₀ i off) = ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      Frame [ksR s₀ off] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.lane .xmm2 0 = s.lane .xmm2 0 ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hpos : 0 < nr s₀ := by rcases hp.rounds with h | h | h <;> omega_arith
  have hwp := hp.wrap_p
  obtain ho : off + 128 ≤ 1024 := by rcases hoff with h | h | h <;> omega_arith
  refine WP.seq (WP.mono (loadCounters_ok s (fun i hi => by
    rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
    exact in_rdwr (in_sub hp.p_in (by omega_arith))) 8 (by decide)) fun t ⟨ht, hf⟩ => ?_)
  let Q : Nat → State → Prop := fun _ u => Env s₀ P u ∧ YFrame (.xmm1 :: aregs) t u
  obtain hEt : Env s₀ P t := hE.yframe hf
  refine WP.seq (WP.mono (aesFixed_ok (nr s₀) hpos aregs (by decide) (by decide) (fun _ => []) Q
    (fun _ _ h => h.1.keys hp) (fun _ _ _ _ h => WP.block_nil ⟨h, fun _ _ _ _ => rfl⟩)
    (fun _ _ _ h hf' => ⟨h.1.yframe hf', h.2.trans hf'⟩) (fun u h => by
      simp only [ea_at, BitVec.ofInt_natCast, BitVec.add_zero, h.1.r10, h.1.rdi])
    t ⟨hEt, YFrame.refl _ _⟩) fun u ⟨hu, hQ⟩ => ?_)
  obtain hct : ∀ i < 8, XBinOp.eval .pshufb (u.lane (aregs.getD i .xmm3) 0) revMask =
      ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀)) := by
    intro i hi
    apply Eq.symm
    apply aesWith_eq
    rw [hu _ (aregs_member i hi) 0 (by decide), ht i hi, ea_at, BitVec.ofInt_natCast, hE.r11]
    exact congrArg (fun x => Spec.Aes.cipher (nr s₀) (sch s₀)
      (VG.Proof.Aes.X86_64.AesNi.st x)) (hT.read i hi)
  refine WP.mono (ksStores_ok u (pp s₀) off ho hQ.1.r11 (fun i hi => by
    rw [hQ.1.wr]; exact in_sub hp.p_in (by omega_arith)) (by omega_arith) 8 (by decide))
    fun v ⟨hv, hvF, hvG, hvL, hvR, hvW⟩ => ?_
  obtain hm : u.mem = s.mem := by rw [hQ.2.mem, hf.mem]
  obtain hFv : Frame [ksR s₀ off] s.mem v.mem := hm ▸ hvF
  refine ⟨?_, fun i hi => ?_, hFv, ?_, ?_, ?_, ?_⟩
  · exact hQ.1.ksFrame hoff hvF hvG hvR hvW
  · rw [blockAt_eq, hv i hi]; exact hct i hi
  · rw [hvG, hQ.2.gpr, hf.gpr]
  · rw [hvL, hQ.2.lane _ (by decide) 0 (by decide), hf.lane _ (by decide) 0 (by decide)]
  · rw [hvR, hQ.2.rd, hf.rd]
  · rw [hvW, hQ.2.wr, hf.wr]

/-! ## Before the loop -/

theorem tailSetup_ok (s : State) {t : Nat} (ht : t < 8) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + t))
    (hin0 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 768) 16)
    (hin1 : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 784) 16) :
    WP isa (.block tailSetup) s fun u =>
      u.gpr .r10 = BitVec.ofNat 64 (16 * 0) ∧
      u.gpr .rax = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) ∧
      u.gpr .rdx = s.gpr .rdx + 256 ∧ u.gpr .r11 = s.gpr .r11 + 64 ∧
      (u.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32 + BitVec.ofNat 32 t ∧
      (∀ q, q ≠ .r10 → q ≠ .rax → q ≠ .rdx → q ≠ .r11 → q ≠ .r8 → u.gpr q = s.gpr q) ∧
      u.lane .xmm0 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 768) 128 ∧
      u.lane .xmm1 0 = s.mem.readW (s.gpr .r11 + BitVec.ofNat 64 784) 128 ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → u.lane r 0 = s.lane r 0) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  obtain e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  obtain e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  obtain s9 : s.gpr .r9 - 16 = BitVec.ofNat 64 t := by
    rw [h9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  obtain sh : BitVec.ofNat 64 t <<< 4 = BitVec.ofNat 64 (16 * t) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega_arith)]
    omega_arith
  obtain hax : s.gpr .r11 + 256 - BitVec.ofNat 64 (16 * t) = s.gpr .r11 + BitVec.ofNat 64 (256 - 16 * t) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain hin0' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin0
  obtain hin1' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofInt 64 ((784 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast]; exact hin1
  obtain w32 : (BitVec.ofNat 64 t).setWidth 32 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  apply WP.of_runBlock
  simp only [tailSetup, runBlock_cons, runStep_some, runBlock_nil, exec, isa, execAlu, execAlu32, execShift,
    show 1 ≤ 4 ∧ 4 ≤ 63 from by decide, and_self, readSrc, readSrc32,
    State.setReg32, State.load128, ea_at, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags,
    mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags,
    gpr_setV, mem_setV, rd_setV, wr_setV, e16, e64, e256, State.lane, xmm_setV,
    xmm_setReg, xmm_arithFlags, xmm_setFlags,
    setWidth_setWidth_32, w32, hax, reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', s9, sh,
    hin0', hin1']
  exact ⟨rfl, trivial, trivial, trivial, trivial, fun q h1 h2 h3 h4 h5 => by simp only [h1, h2, h3, h4, h5, ↓reduceIte],
    by rw [BitVec.ofInt_natCast], by rw [BitVec.ofInt_natCast],
    fun r h0 h1 => by simp only [h0, h1, ↓reduceIte], trivial⟩


/-! ## After the loop -/

/-- `tailEnd nr back`, where `back` leaves `v` in `r11` and the rest as it was. -/
theorem tailEndWith_ok (s : State) {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (h1 : s.lane .xmm1 0 = poly) {back : Instr} {v : Addr}
    (hA : WP isa (.block [back]) s fun s₁ =>
      s₁.gpr .r11 = v ∧ (∀ q, q ≠ .r11 → s₁.gpr q = s.gpr q) ∧
      (∀ r l, s₁.lane r l = s.lane r l) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) :
    WP isa (.block (tailEnd nr back)) s fun u =>
      u.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧ u.gpr .r11 = v ∧
      u.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr) ∧
      (∀ q, q ≠ .r11 → q ≠ .r10 → u.gpr q = s.gpr q) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain enr : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * nr)) = BitVec.ofNat 64 (16 * nr) := by
    rcases hnr with rfl | rfl | rfl <;> decide
  rw [tailEnd, List.append_assoc, WP.block_append_iff]
  refine WP.mono hA fun s₁ ⟨a11, ag, al, am, ard, awr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (StitchAvx.reduceHash_ok s₁ (by rw [al]; exact h1)) fun s₂ ⟨y₂, f₂⟩ => ?_
  obtain hC : WP isa (.block [.mov .r10 (.reg .rdi), .alu .add .r10 (.imm (BitVec.ofNat 32 (16 * nr)))]) s₂
      fun u => u.gpr .r10 = s₂.gpr .rdi + BitVec.ofNat 64 (16 * nr) ∧ (∀ q, q ≠ .r10 → u.gpr q = s₂.gpr q) ∧
        (∀ r l, u.lane r l = s₂.lane r l) ∧ u.mem = s₂.mem ∧ u.rd = s₂.rd ∧ u.wr = s₂.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, enr, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      ↓reduceIte, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩
  refine WP.mono hC fun u ⟨c10, cg, cl, cm, crd, cwr⟩ => ?_
  obtain hp₁ : prod (s₁.proj 0) = prod (s.proj 0) := by simp only [prod, State.proj_xmm, al]
  refine ⟨by rw [cl, y₂, hp₁], by rw [cg _ (by decide), f₂.gpr, a11], ?_, fun q h11 h10 => ?_,
    by rw [cm, f₂.mem, am], by rw [crd, f₂.rd, ard], by rw [cwr, f₂.wr, awr]⟩
  · rw [c10, f₂.gpr, ag _ (by decide)]
  · rw [cg q h10, f₂.gpr, ag q h11]

theorem tailEnd_ok (s : State) {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (h1 : s.lane .xmm1 0 = poly) :
    WP isa (.block (tailEnd nr)) s fun u =>
      u.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧ u.gpr .r11 = s.gpr .r11 - 64 ∧
      u.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr) ∧
      (∀ q, q ≠ .r11 → q ≠ .r10 → u.gpr q = s.gpr q) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  refine tailEndWith_ok s hnr h1 ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, e64, gpr_setReg,
    gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `cmp r9, 16`. -/
theorem cmp16z_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.zf = some (s.gpr .r9 - 16 == 0) ∧ YFrame [] s s' := by
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩⟩

/-- Writes to a region of the data keep `Env`. -/
theorem Env.dataWrite {s₀ s t : State} {lo : Nat} {P : Nat → Block} (hp : SPre s₀ lo) (h : Env s₀ P s) {R : Region}
    (hR : Region.Sub R (dR s₀)) (hf : Frame [R] s.mem t.mem)
    (hg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Env s₀ P t := by
  obtain rdP : ∀ d w, d + w / 8 ≤ 1024 → w / 8 < 2 ^ 64 →
      t.mem.readW (pp s₀ + BitVec.ofNat 64 d) w = s.mem.readW (pp s₀ + BitVec.ofNat 64 d) w :=
    fun d w hd hn => hf.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, w / 8⟩) (Region.contains_self _ _)
      (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst r
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ hd)).sub_right hR) hn
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rsi,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.rcx,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r11,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide)]; exact h.r10,
    fun r h1 h2 h3 h4 h5 h6 => by rw [hg r h1 h2 h3 h4]; exact h.other r h1 h2 h3 h4 h5 h6,
    h.frame.trans (hf.sub fun r hr' => by
      simp only [List.mem_singleton] at hr'; subst r
      exact ⟨dR s₀, by simp, hR⟩),
    fun k hk => (rdP _ 128 (by omega_arith) (by decide)).trans (h.powers k hk),
    (rdP 768 128 (by decide) (by decide)).trans h.mask, (rdP 784 128 (by decide) (by decide)).trans h.poly,
    (rdP 800 64 (by decide) (by decide)).trans h.rounds, (rdP 808 64 (by decide) (by decide)).trans h.data,
    (rdP 816 64 (by decide) (by decide)).trans h.saved,
    hr.trans h.rd, hw.trans h.wr⟩

/-! ## Out of place: `rbx` moved to the data and back -/

theorem rbxAdd_ok (s : State) :
    WP isa (.block [.alu .add .rbx (.reg .rdx)]) s fun u =>
      u.gpr .rbx = s.gpr .rbx + s.gpr .rdx ∧ (∀ q, q ≠ .rbx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, gpr_setReg,
    gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

theorem rbxSub_ok (s : State) :
    WP isa (.block [.alu .sub .rbx (.reg .rdx)]) s fun u =>
      u.gpr .rbx = s.gpr .rbx - s.gpr .rdx ∧ (∀ q, q ≠ .rbx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, gpr_setReg,
    gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    ↓reduceIte, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q h => by simp only [h, ↓reduceIte], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- Out of place, `rbx` moved from `src - dst` to the data at `rdx`. -/
theorem rbxTo_ok (ix : Bool) (s : State) :
    WP isa (.block (if ix then [.alu .add .rbx (.reg .rdx)] else [])) s fun u =>
      u.gpr .rbx = s.gpr .rbx + (if ix then s.gpr .rdx else BitVec.ofNat 64 0) ∧
      (∀ q, q ≠ .rbx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  cases ix
  · exact WP.block_nil ⟨by simp only [Bool.false_eq_true, ite_false, BitVec.add_zero], fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  · exact WP.mono (rbxAdd_ok s) fun u ⟨u1, u2⟩ => ⟨by simp only [ite_true, u1], u2⟩

/-- And back. -/
theorem rbxToDec_ok (ix : Bool) (s : State) :
    WP isa (.block (if ix then [.alu .sub .rbx (.reg .rdx)] else [])) s fun u =>
      u.gpr .rbx = s.gpr .rbx - (if ix then s.gpr .rdx else BitVec.ofNat 64 0) ∧
      (∀ q, q ≠ .rbx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  cases ix
  · exact WP.block_nil ⟨by simp only [Bool.false_eq_true, ite_false, BitVec.sub_zero], fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  · exact WP.mono (rbxSub_ok s) fun u ⟨u1, u2⟩ => ⟨by simp only [ite_true, u1], u2⟩

/-! ## The blocks after the pipeline's -/

theorem srcBlk_add (s₀ : State) (ix : Bool) (g k : Nat) :
    srcBlk s₀ ix g + BitVec.ofNat 64 (16 * k) = srcBlk s₀ ix (g + k) := by
  simp only [srcBlk]
  rw [BitVec.add_assoc, BitVec.add_comm (off s₀ ix), ← BitVec.add_assoc, bAddr_add]

/-- The register the blocks after the pipeline's are read through. -/
abbrev srcReg (ix : Bool) : Reg := if ix then .rbx else .rdx

theorem tail_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat} (hp : SPre s₀) (hS : SrcOk s₀ ix)
    (hlaw : TailLaw s₀ P) (h : TailReady s₀ ix P g s) :
    WP isa (.seq (tailT (nr s₀) ix) (.block finish)) s fun t =>
      EPost s₀ t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  obtain hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hlt := h.lt
  obtain ⟨t, ht⟩ : ∃ t, t = nb s₀ - (g + 16) := ⟨_, rfl⟩
  obtain ht8 : t < 8 := by omega_arith
  obtain hnb : nb s₀ = g + 16 + t := by omega_arith
  obtain h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + t) := by rw [h.remaining]; congr 1; omega_arith
  obtain hz : (BitVec.ofNat 64 (16 + t) - 16 == 0) = decide (t = 0) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith
  rw [tailT]
  refine WP.seq (WP.seq (WP.mono (cmp16z_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_))
  obtain hE₁ : Env s₀ P s₁ := h.env.yframe f₁
  refine WP.ite (decide (t = 0)) (by simp only [eval, z₁, h9, hz]) (fun he => ?_) (fun he => ?_)
  · -- No blocks left.
    obtain t0 : t = 0 := by simpa using he
    subst t0
    refine WP.block_nil (finish_complete (ix := ix) hp false hE₁ ?_ ?_ ?_)
    · rw [f₁.mem, hnb]; exact h.data
    · rw [f₁.gpr, hnb]; exact h.counter
    · rw [f₁.lane .xmm2 (by simp) 0 (by decide), h.hash, hnb]
  -- `t` blocks left.
  obtain t1 : 1 ≤ t := by
    have : t ≠ 0 := by simpa using he
    omega_arith
  refine WP.seq (WP.mono (ksTail_ok hp (.inr (.inr rfl)) hE₁ (f₁.mem ▸ h.templates))
    fun s₂ ⟨hE₂, hks, hF₂, hg₂, hy₂, hrd₂, hwr₂⟩ => ?_)
  obtain g₂ : ∀ q, s₂.gpr q = s.gpr q := fun q => by rw [hg₂, f₁.gpr]
  obtain rbx₂ : s₂.gpr .rbx = s₀.gpr .rbx :=
    hE₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (tailSetup_ok s₂ ht8 (by rw [g₂]; exact h9)
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide))))
    fun s₃ ⟨a10, aax, adx, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  obtain hA : bAddr s₀ g + 256 = bAddr s₀ (g + 16) := bAddr_add s₀ g 16
  obtain rdx₃ : s₃.gpr .rdx = bAddr s₀ (g + 16) := by rw [adx, g₂, h.cursor, hA]
  obtain rbx₃ : s₃.gpr .rbx = s₀.gpr .rbx := by
    rw [ag _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rbx₂
  refine WP.mono (rbxTo_ok ix s₃) fun s₃' ⟨b₃, bg, bl, bm, brd, bwr⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₃') fun s₄ ⟨p₄, f₄⟩ => ?_
  obtain g₄ : ∀ q, q ≠ .rbx → s₄.gpr q = s₃.gpr q := fun q hq => by rw [f₄.gpr, bg q hq]
  obtain rbx₄ : s₄.gpr .rbx = s₀.gpr .rbx + (if ix then bAddr s₀ (g + 16) else BitVec.ofNat 64 0) := by
    rw [f₄.gpr, b₃, rbx₃, rdx₃]
  let E : StitchZH.REnv := ⟨t, srcReg ix, srcBlk s₀ ix (g + 16), bAddr s₀ (g + 16), pp s₀ + BitVec.ofNat 64 64,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * t), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  obtain rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, brd, ard, hE₂.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, bwr, awr, hE₂.wr]
  obtain m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, bm, am]
  obtain rdx₄ : s₄.gpr .rdx = bAddr s₀ (g + 16) := by rw [g₄ _ (by decide), rdx₃]
  obtain src₄ : s₄.gpr (srcReg ix) = srcBlk s₀ ix (g + 16) := by
    cases ix
    · rw [srcBlk_false]; exact rdx₄
    · simp only [srcReg, ite_true, srcBlk, off]
      rw [rbx₄]; simp only [↓reduceIte]; exact BitVec.add_comm _ _
  obtain hEok : E.Ok :=
    { r1 := t1, r15 := show t ≤ 15 by omega_arith, gS := src₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [g₄ _ (by decide), a11, hE₂.r11]; rfl
      gW := by show s₄.gpr .rax = _; rw [g₄ _ (by decide), aax, hE₂.r11]
      src9 := show srcReg ix ≠ .r9 by cases ix <;> decide
      src10 := show srcReg ix ≠ .r10 by cases ix <;> decide
      inS := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (srcBlk s₀ ix (g + 16) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, srcBlk_add]
        exact hS.rd _ (by omega_arith)
      inK := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j < t) => by
        show InRegions s₄.wr (bAddr s₀ (g + 16) + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hp.d_in (by omega_arith)
      inW := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      dS := fun j (hj : j < t) i hi => by
        show Region.Disjoint ⟨srcBlk s₀ ix (g + 16) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (g + 16), 16 * i⟩
        rw [srcBlk_add]
        exact (hS.sep _ (by omega_arith)).symm.sub_right (Offset.sub_base _ (by omega_arith))
      dK := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (g + 16), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (g + 16), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)) }
  obtain hI₄ : StitchZH.RInv E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [g₄ _ (by decide)]; exact a10
      r9 := by
        show s₄.gpr .r9 = _
        rw [g₄ _ (by decide), ag _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂, h9, Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by
        rw [f₄.lane _ (by decide) 0 (by decide), bl, a0, hE₂.r11]
        exact hE₂.mask
      m1 := by
        rw [f₄.lane _ (by decide) 0 (by decide), bl, a1, hE₂.r11]
        exact hE₂.poly }
  refine WP.seq (WP.mono (StitchZH.remLoop_ok hEok hI₄) fun s₅ hI₅ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (rbxToDec_ok ix s₅) fun s₅' ⟨c₅, cg, cl, cm, crd, cwr⟩ => ?_
  refine WP.mono (tailEnd_ok s₅' hp.rounds (by rw [cl]; exact hI₅.m1))
    fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the tail leaves.
  obtain g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → q ≠ .rbx → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' hb => by
    rw [g₆ q h11 h10, cg q hb, hI₅.gpr q h9' h10]
  obtain rbx₆ : s₆.gpr .rbx = s₀.gpr .rbx := by
    rw [g₆ _ (by decide) (by decide), c₅, hI₅.gpr _ (by decide) (by decide),
      show E.g .rbx = s₄.gpr .rbx from rfl, rbx₄,
      show s₅.gpr .rdx = bAddr s₀ (g + 16) from (hI₅.gpr _ (by decide) (by decide)).trans rdx₄]
    cases ix
    · simp only [Bool.false_eq_true, ite_false, BitVec.add_zero, BitVec.sub_zero]
    · simp only [ite_true, BitVec.add_sub_cancel]
  obtain hR : Region.Sub ⟨bAddr s₀ (g + 16), 16 * t⟩ (dR s₀) := Offset.sub_base _ (by omega_arith)
  obtain hF : Frame [⟨bAddr s₀ (g + 16), 16 * t⟩] s₂.mem s₆.mem := by
    rw [m₆, cm, ← m₄]; exact hI₅.frame
  obtain hE₆ : Env s₀ P s₆ := hE₂.dataWrite hp hR hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, cg _ (by decide), hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 - 64 = _
        rw [g₄ _ (by decide), a11, BitVec.add_sub_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, cg _ (by decide), hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [g₄ _ (by decide), ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE₂.rdi, hE₂.r10]
      by_cases hb : q = .rbx
      · subst hb; rw [rbx₆, rbx₂]
      · rw [g₆₄ q h11 h10 h4 hb, g₄ q hb, ag q h10 h1 h2 h11 h3])
    (by rw [rd₆, crd, hI₅.rd]; exact f₄.rd.trans (brd.trans ard))
    (by rw [wr₆, cwr, hI₅.wr]; exact f₄.wr.trans (bwr.trans awr))
  obtain hD₂ : DataInv s₀ ix (g + 16) s₂.mem := (f₁.mem ▸ h.data).frameP hp hS hF₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.sub_base (pp s₀) (d := 832) (n := 128) (k := 1024) (by decide))
  obtain hX : ∀ j < t, E.X j = ctb s₀ (g + 16 + j) := fun j hj => by
    show blockAt s₄.mem (srcBlk s₀ ix (g + 16) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [m₄, srcBlk_add, Offset.add_add, (hD₂ _ (by omega_arith)).2 (by omega_arith),
      show 64 + (768 + 16 * j) = 832 + 16 * j by omega_arith, hks j (by omega_arith)]
  obtain hT : ∀ j < t, E.T j = P (8 - t + j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * t + 16 * j = 128 + 16 * (8 - t + j) by omega_arith]
    exact hE₂.powers _ (by omega_arith)
  refine finish_complete (ix := ix) hp false hE₆ (fun k hk => ⟨fun hk' => ?_, fun hk' => absurd hk (by omega_arith)⟩) ?_ ?_
  · by_cases hkg : k < g + 16
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (dp s₀) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        (hD₂ k (by omega_arith)).1 hkg]
    · obtain ⟨j, rfl⟩ : ∃ j, k = g + 16 + j := ⟨k - (g + 16), by omega_arith⟩
      obtain ct := hI₅.ct j (show j < t by omega_arith)
      rw [show E.aD j = bAddr s₀ (g + 16 + j) from bAddr_add s₀ (g + 16) j, ← cm, ← m₆] at ct
      rw [ct, hX j (by omega_arith)]
  · rw [g₆₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide), a8, g₂, h.counter, hnb,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, show g + 16 + 8 + t = g + 16 + t + 8 by omega_arith]
  · rw [y₆, show prod (s₅'.proj 0) = prod (s₅.proj 0) by simp only [prod, State.proj_xmm, cl], hI₅.prod,
      StitchZH.accR_congr _ t hX hT, hlaw t t1 (by omega_arith)]
    obtain hy : E.y = hashPrefix s₀ false (g + 16) := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), bl, al _ (by decide) (by decide), hy₂,
        f₁.lane _ (by simp) 0 (by decide), h.hash]
    rw [hy, hnb]
    simp only [hashPrefix, List.range_add, List.map_append, List.map_map, ghashFrom, List.foldl_append]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8

end

end

/-!
# The blocks after the last batch of decryption

`finalDec_ok`: after the loop, the last batch decrypts and hashes the eight
blocks from `g`, leaving `t = nb - g - 8 < 8` blocks (`TailReadyD`);
`tailD_ok`: `StitchAvx8.tailD` and `finish` then meet `DPost` (`tailNone_ok`:
`finish` alone, when there are none). The tail is
`tail_ok`'s (`Tail.lean`), once `r9` and `rdx` are moved to where encryption
leaves them: `ksTail` encrypts the eight counters the last batch prepared,
`tailSetup` advances the counter by `t` and points `rax` at the powers
`H'ᵗ` … `H'`, and the loop (`StitchZH.remLoopD1_ok`) decrypts the `t` blocks,
read where the loop reads its data (`srcBlk`: in place, or out of place at
`rbx`, moved for the loop as `tail_ok` moves it), and adds the products of
the blocks as they were with their powers, which `tailEnd` reduces into `Y`
(`TailLaw`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (batch q8 ksTail tailSetup tailEnd tailD finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Spec.Gcm (Block inc32 blockAt ghashFrom)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (prod reduceB)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInvD accR accR_congr remLoopD1_ok)

/-- After the last batch of decryption: the blocks before `g + 8` decrypted
and hashed, the counters of the next eight prepared, and `nb - g - 8 < 8`
blocks left. -/
structure TailReadyD (s₀ : State) (ix : Bool) (P : Nat → Block) (g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ ix (g + 8) s.mem
  templates : Templates s₀ (g + 8) 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (g + 8 + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ true (g + 8)
  le : g + 8 ≤ nb s₀
  lt : nb s₀ - g < 16

theorem finalDec_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat}
    (hp : SPre s₀) (hS : SrcOk s₀ ix) (hlaw : HashLaw s₀ P) (h : LoopInv s₀ ix P true g s)
    (hn : nb s₀ - g < 16) :
    WP isa (batch (nr s₀) 8 0 (q8 (nr s₀) ix) ix) s (TailReadyD s₀ ix P g) := by
  have hc : CoreInv s₀ ix P true g g s := h.core
  have hle : g + 8 ≤ nb s₀ := h.tail_le
  obtain hb := hc.hashBatch hp hS (by simp [lead]) hle
  rw [show lead true = 0 from rfl, Bool.true_and] at hb
  refine WP.mono hb fun t ht => ?_
  obtain hd := hc.data.batch hp hS hle (by simpa only [lead, Bool.true_eq, ite_true,
    Nat.mul_zero, BitVec.add_zero] using hc.cursor) hc.rbx ht
  refine ⟨ht.env, hd, ht.templates, ?_, ?_, ?_, ?_, hle, hn⟩
  · rw [ht.counter]
  · rw [ht.regs _ (by decide) (by decide)]; exact hc.cursor
  · rw [ht.regs _ (by decide) (by decide)]; exact hc.remaining
  · rw [ht.hash, hlaw]
    change ghashFrom (hk s₀) (hashPrefix s₀ true g) ((List.range 8).map (window s₀ true g)) = _
    exact (ghash_append8 (hk s₀) (y₀ s₀) (hashBlock s₀ true) g).symm

/-- With no blocks left, `finish` meets `DPost`, and keeps the 8 bytes at
`scratch + 816`. -/
theorem tailNone_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat} (hp : SPre s₀)
    (h : TailReadyD s₀ ix P g s) (hn : nb s₀ = g + 8) :
    WP isa (.block finish) s fun t =>
      DPost s₀ t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 :=
  WP.mono (finish_complete (ix := ix) hp true h.env (by rw [hn]; exact h.data) (by rw [h.counter, hn])
    (by rw [h.hash, hn])) fun _ hu => hu

/-- `add r9, 8`, `sub rdx, 128`, `cmp r9, 16`: the tail's registers where
encryption's has them, and whether there are blocks left. -/
theorem tailHead_ok (s : State) {t : Nat} (ht : t < 8) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 + t)) :
    WP isa (.block [.alu .add .r9 (.imm 8), .alu .sub .rdx (.imm 128), .alu .cmp .r9 (.imm 16)]) s fun u =>
      u.gpr .r9 = BitVec.ofNat 64 (16 + t) ∧ u.gpr .rdx = s.gpr .rdx - 128 ∧
      u.zf = some (decide (t = 0)) ∧ (∀ q, q ≠ .r9 → q ≠ .rdx → u.gpr q = s.gpr q) ∧
      (∀ r l, u.lane r l = s.lane r l) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  obtain e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  obtain e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  obtain a9 : BitVec.ofNat 64 (8 + t) + 8 = BitVec.ofNat 64 (16 + t) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]; congr 1; omega_arith
  obtain hz : (BitVec.ofNat 64 (16 + t) - 16 == 0) = decide (t = 0) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    isa, State.setReg, e8, e16, e128, h9, a9, hz, reduceCtorEq, ↓reduceIte,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun q h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl,
    trivial, trivial, trivial⟩

theorem tailD_ok {s₀ s : State} {ix : Bool} {P : Nat → Block} {g : Nat} (hp : SPre s₀) (hS : SrcOk s₀ ix)
    (hlaw : TailLaw s₀ P) (h : TailReadyD s₀ ix P g s) :
    WP isa (.seq (tailD (nr s₀) ix) (.block finish)) s fun t =>
      DPost s₀ t ∧ t.mem.readW (pp s₀ + 816) 64 = s₀.mem.readW (pp s₀ + 816) 64 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  obtain hn64 : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hle := h.le
  have hlt := h.lt
  obtain ⟨t, ht⟩ : ∃ t, t = nb s₀ - (g + 8) := ⟨_, rfl⟩
  obtain ht8 : t < 8 := by omega_arith
  obtain hnb : nb s₀ = g + 8 + t := by omega_arith
  obtain h9 : s.gpr .r9 = BitVec.ofNat 64 (8 + t) := by rw [h.remaining]; congr 1; omega_arith
  rw [tailD]
  refine WP.seq (WP.seq (WP.mono (tailHead_ok s ht8 h9) fun s₁ ⟨r9₁, dx₁, z₁, g₁, l₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain hR : Region.Sub ⟨bAddr s₀ (g + 8), 16 * t⟩ (dR s₀) := Offset.sub_base _ (by omega_arith)
  obtain hE₁ : Env s₀ P s₁ := h.env.dataWrite hp hR (by rw [m₁]; exact Frame.refl _ _)
    (fun r _ h2 _ h4 => g₁ r h4 h2) rd₁ wr₁
  refine WP.ite (decide (t = 0)) z₁ (fun he => ?_) (fun he => ?_)
  · -- No blocks left.
    obtain t0 : t = 0 := by simpa using he
    subst t0
    refine WP.block_nil (WP.mono (finish_complete (ix := ix) hp true hE₁ ?_ ?_ ?_) fun u hu => hu)
    · rw [m₁, hnb]; exact h.data
    · rw [g₁ _ (by decide) (by decide), hnb]; exact h.counter
    · rw [l₁, h.hash, hnb]
  -- `t` blocks left.
  obtain t1 : 1 ≤ t := by
    have : t ≠ 0 := by simpa using he
    omega_arith
  refine WP.seq (WP.mono (ksTail_ok hp (.inr (.inr rfl)) hE₁ (m₁ ▸ h.templates))
    fun s₂ ⟨hE₂, hks, hF₂, hg₂, hy₂, hrd₂, hwr₂⟩ => ?_)
  obtain rbx₂ : s₂.gpr .rbx = s₀.gpr .rbx :=
    hE₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (tailSetup_ok s₂ ht8 (by rw [hg₂]; exact r9₁)
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide)))
    (by rw [hE₂.rd, hE₂.wr, hE₂.r11]; exact in_rdwr (in_sub hp.p_in (by decide))))
    fun s₃ ⟨a10, aax, adx, a11, a8, ag, a0, a1, al, am, ard, awr⟩ => ?_
  obtain hA : bAddr s₀ g - 128 + 256 = bAddr s₀ (g + 8) := by
    rw [← bAddr_add s₀ g 8, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain rdx₃ : s₃.gpr .rdx = bAddr s₀ (g + 8) := by rw [adx, hg₂, dx₁, h.cursor, hA]
  obtain rbx₃ : s₃.gpr .rbx = s₀.gpr .rbx := by
    rw [ag _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rbx₂
  refine WP.mono (rbxTo_ok ix s₃) fun s₃' ⟨b₃, bg, bl, bm, brd, bwr⟩ => ?_
  refine WP.mono (StitchAvx.zero_ok s₃') fun s₄ ⟨p₄, f₄⟩ => ?_
  obtain g₄ : ∀ q, q ≠ .rbx → s₄.gpr q = s₃.gpr q := fun q hq => by rw [f₄.gpr, bg q hq]
  obtain rbx₄ : s₄.gpr .rbx = s₀.gpr .rbx + (if ix then bAddr s₀ (g + 8) else BitVec.ofNat 64 0) := by
    rw [f₄.gpr, b₃, rbx₃, rdx₃]
  let E : REnv := ⟨t, srcReg ix, srcBlk s₀ ix (g + 8), bAddr s₀ (g + 8), pp s₀ + BitVec.ofNat 64 64,
    pp s₀ + BitVec.ofNat 64 (256 - 16 * t), s₄.mem, s₄.gpr, s₄.rd, s₄.wr, s₄.lane .xmm2 0⟩
  obtain rd₄ : s₄.rd = s₀.rd := by rw [f₄.rd, brd, ard, hE₂.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [f₄.wr, bwr, awr, hE₂.wr]
  obtain m₄ : s₄.mem = s₂.mem := by rw [f₄.mem, bm, am]
  obtain rdx₄ : s₄.gpr .rdx = bAddr s₀ (g + 8) := by rw [g₄ _ (by decide), rdx₃]
  obtain src₄ : s₄.gpr (srcReg ix) = srcBlk s₀ ix (g + 8) := by
    cases ix
    · rw [srcBlk_false]; exact rdx₄
    · simp only [srcReg, ite_true, srcBlk, off]
      rw [rbx₄]; simp only [↓reduceIte]; exact BitVec.add_comm _ _
  obtain hEok : E.Ok :=
    { r1 := t1, r15 := show t ≤ 15 by omega_arith, gS := src₄, gA := rdx₄
      gP := by show s₄.gpr .r11 = _; rw [g₄ _ (by decide), a11, hE₂.r11]; rfl
      gW := by show s₄.gpr .rax = _; rw [g₄ _ (by decide), aax, hE₂.r11]
      src9 := show srcReg ix ≠ .r9 by cases ix <;> decide
      src10 := show srcReg ix ≠ .r10 by cases ix <;> decide
      inS := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (srcBlk s₀ ix (g + 8) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, srcBlk_add]
        exact hS.rd _ (by omega_arith)
      inK := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      inD := fun j (hj : j < t) => by
        show InRegions s₄.wr (bAddr s₀ (g + 8) + BitVec.ofNat 64 (16 * j)) 16
        rw [wr₄, bAddr_add]
        exact in_sub hp.d_in (by omega_arith)
      inW := fun j (hj : j < t) => by
        show InRegions (s₄.rd ++ s₄.wr) (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 16
        rw [rd₄, wr₄, Offset.add_add]
        exact in_rdwr (in_sub hp.p_in (by omega_arith))
      dS := fun j (hj : j < t) i hi => by
        show Region.Disjoint ⟨srcBlk s₀ ix (g + 8) + BitVec.ofNat 64 (16 * j), 16⟩ ⟨bAddr s₀ (g + 8), 16 * i⟩
        rw [srcBlk_add]
        exact (hS.sep _ (by omega_arith)).symm.sub_right (Offset.sub_base _ (by omega_arith))
      dK := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j), 16⟩
          ⟨bAddr s₀ (g + 8), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
      dW := fun j (hj : j < t) => by
        show Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j), 16⟩
          ⟨bAddr s₀ (g + 8), 16 * t⟩
        rw [Offset.add_add]
        exact (hp.d_p.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith)) }
  obtain hI₄ : RInvD E 0 s₄ :=
    { le := Nat.zero_le _
      r10 := by rw [g₄ _ (by decide)]; exact a10
      r9 := by
        show s₄.gpr .r9 = _
        rw [g₄ _ (by decide), ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hg₂, r9₁,
          Nat.sub_zero]
      gpr := fun _ _ _ => rfl, rd := rfl, wr := rfl
      frame := Frame.refl _ _
      ct := fun j hj => absurd hj (Nat.not_lt_zero _)
      prod := p₄
      y := by simp only [↓reduceIte]; rfl
      m0 := by
        rw [f₄.lane _ (by decide) 0 (by decide), bl, a0, hE₂.r11]
        exact hE₂.mask
      m1 := by
        rw [f₄.lane _ (by decide) 0 (by decide), bl, a1, hE₂.r11]
        exact hE₂.poly }
  refine WP.seq (WP.mono (remLoopD1_ok hEok hI₄) fun s₅ hI₅ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (rbxToDec_ok ix s₅) fun s₅' ⟨c₅, cg, cl, cm, crd, cwr⟩ => ?_
  refine WP.mono (tailEnd_ok s₅' hp.rounds (by rw [cl]; exact hI₅.m1))
    fun s₆ ⟨y₆, r11₆, r10₆, g₆, m₆, rd₆, wr₆⟩ => ?_
  -- What the tail leaves.
  obtain g₆₄ : ∀ q, q ≠ .r11 → q ≠ .r10 → q ≠ .r9 → q ≠ .rbx → s₆.gpr q = s₄.gpr q := fun q h11 h10 h9' hb => by
    rw [g₆ q h11 h10, cg q hb, hI₅.gpr q h9' h10]
  obtain rbx₆ : s₆.gpr .rbx = s₀.gpr .rbx := by
    rw [g₆ _ (by decide) (by decide), c₅, hI₅.gpr _ (by decide) (by decide),
      show E.g .rbx = s₄.gpr .rbx from rfl, rbx₄,
      show s₅.gpr .rdx = bAddr s₀ (g + 8) from (hI₅.gpr _ (by decide) (by decide)).trans rdx₄]
    cases ix
    · simp only [Bool.false_eq_true, ite_false, BitVec.add_zero, BitVec.sub_zero]
    · simp only [ite_true, BitVec.add_sub_cancel]
  obtain hF : Frame [⟨bAddr s₀ (g + 8), 16 * t⟩] s₂.mem s₆.mem := by
    rw [m₆, cm, ← m₄]; exact hI₅.frame
  obtain hE₆ : Env s₀ P s₆ := hE₂.dataWrite hp hR hF (fun q h1 h2 h3 h4 => by
      by_cases h11 : q = .r11
      · subst h11
        rw [r11₆, cg _ (by decide), hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .r11 - 64 = _
        rw [g₄ _ (by decide), a11, BitVec.add_sub_cancel]
      by_cases h10 : q = .r10
      · subst h10
        rw [r10₆, cg _ (by decide), hI₅.gpr _ (by decide) (by decide)]
        show s₄.gpr .rdi + _ = _
        rw [g₄ _ (by decide), ag _ (by decide) (by decide) (by decide) (by decide) (by decide), hE₂.rdi, hE₂.r10]
      by_cases hb : q = .rbx
      · subst hb; rw [rbx₆, rbx₂]
      · rw [g₆₄ q h11 h10 h4 hb, g₄ q hb, ag q h10 h1 h2 h11 h3])
    (by rw [rd₆, crd, hI₅.rd]; exact f₄.rd.trans (brd.trans ard))
    (by rw [wr₆, cwr, hI₅.wr]; exact f₄.wr.trans (bwr.trans awr))
  obtain hD₂ : DataInv s₀ ix (g + 8) s₂.mem := (m₁ ▸ h.data).frameP hp hS hF₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.sub_base (pp s₀) (d := 832) (n := 128) (k := 1024) (by decide))
  obtain hB : ∀ j < t, E.H j = blk s₀ (g + 8 + j) := fun j hj => by
    show blockAt s₄.mem (srcBlk s₀ ix (g + 8) + BitVec.ofNat 64 (16 * j)) = _
    rw [m₄, srcBlk_add, (hD₂ _ (by omega_arith)).2 (by omega_arith)]
  obtain hX : ∀ j < t, E.X j = ctb s₀ (g + 8 + j) := fun j hj => by
    show blockAt s₄.mem (srcBlk s₀ ix (g + 8) + BitVec.ofNat 64 (16 * j)) ^^^
      blockAt s₄.mem (pp s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (768 + 16 * j)) = _
    rw [show blockAt s₄.mem (srcBlk s₀ ix (g + 8) + BitVec.ofNat 64 (16 * j)) = E.H j from rfl, hB j hj, m₄,
      Offset.add_add, show 64 + (768 + 16 * j) = 832 + 16 * j by omega_arith, hks j (by omega_arith)]
  obtain hT : ∀ j < t, E.T j = P (8 - t + j) := fun j hj => by
    show s₄.mem.readW (pp s₀ + BitVec.ofNat 64 (256 - 16 * t) + BitVec.ofNat 64 (16 * j)) 128 = _
    rw [m₄, Offset.add_add, show 256 - 16 * t + 16 * j = 128 + 16 * (8 - t + j) by omega_arith]
    exact hE₂.powers _ (by omega_arith)
  refine WP.mono (finish_complete (ix := ix) hp true hE₆
    (fun k hk => ⟨fun hk' => ?_, fun hk' => absurd hk (by omega_arith)⟩) ?_ ?_) fun u hu => hu
  · by_cases hkg : k < g + 8
    · rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hF (fun r hr => by
          simp only [List.mem_singleton] at hr; subst r
          exact Offset.disjoint (dp s₀) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        (hD₂ k (by omega_arith)).1 hkg]
    · obtain ⟨j, rfl⟩ : ∃ j, k = g + 8 + j := ⟨k - (g + 8), by omega_arith⟩
      obtain ct := hI₅.ct j (show j < t by omega_arith)
      rw [show E.aD j = bAddr s₀ (g + 8 + j) from bAddr_add s₀ (g + 8) j, ← cm, ← m₆] at ct
      rw [ct, hX j (by omega_arith)]
  · rw [g₆₄ _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide), a8, hg₂,
      g₁ _ (by decide) (by decide), h.counter,
      hnb, BitVec.add_assoc, BitVec.ofNat_add_ofNat, show g + 8 + 8 + t = g + 8 + t + 8 by omega_arith]
  · rw [y₆, show prod (s₅'.proj 0) = prod (s₅.proj 0) by simp only [prod, State.proj_xmm, cl], hI₅.prod,
      accR_congr _ t hB hT, hlaw t t1 (by omega_arith)]
    obtain hy : E.y = hashPrefix s₀ true (g + 8) := by
      show s₄.lane .xmm2 0 = _
      rw [f₄.lane _ (by decide) 0 (by decide), bl, al _ (by decide) (by decide), hy₂, l₁, h.hash]
    rw [hy, hnb]
    simp only [hashPrefix, List.range_add, List.map_append, List.map_map, ghashFrom, List.foldl_append]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8
