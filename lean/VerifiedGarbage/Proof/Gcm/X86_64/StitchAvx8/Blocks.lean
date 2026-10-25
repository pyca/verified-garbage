module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupDispatch
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

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
theorem schedule_cases : ∀ nr < 15, nr = 10 ∨ nr = 12 ∨ nr = 14 → ∀ j < 15,
    1 ≤ j → j < nr →
    (hashCount nr j < 8 ∧ hashCount nr (j + 1) = hashCount nr j + 1 ∧
      j + 1 < nr ∧ q8 nr j = gh8 0 ((hashCount nr j + 1) % 8)) ∨
    (hashCount nr j = 8 ∧ hashCount nr (j + 1) = 8 ∧ j + 1 = nr ∧
      q8 nr j = reduceFinal) ∨
    (hashCount nr (j + 1) = hashCount nr j ∧ j + 1 < nr ∧ q8 nr j = []) := by
  intro nr _ hn j _ hj hjn
  rcases hn with rfl | rfl | rfl <;> interval_cases j <;> simp [hashCount, q8]

theorem q8_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j) (hjn : j < nr s₀)
    (h : StageInv s₀ start P X y c nc (hashCount (nr s₀) j) false s)
    (hx : HashSrc s₀ (start.gpr .rdx) start.mem X) :
    WP isa (.block (q8 (nr s₀) j)) s fun t =>
      StageInv s₀ start P X y c nc (hashCount (nr s₀) (j + 1))
        (decide (nr s₀ ≤ j + 1)) t ∧ FlowFrame workRegs s t := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega_arith
  rcases schedule_cases _ hn hp.rounds j (by omega_arith) hj hjn with
    ⟨h8, hnext, hlt, hc⟩ | ⟨h8, hnext, he, hc⟩ | ⟨hnext, hlt, hc⟩
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega_arith)]
    exact WP.mono (h.hashStep hp h8 hx) fun t ⟨ht, hf⟩ =>
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
def roundWork (nr : Nat) (hashing : Bool) (j : Nat) : List Instr :=
  (if hashing then q8 nr j else []) ++ counterWork j

def RoundInv (s₀ start : State) (P X : Nat → Block) (y : Block) (c : Nat)
    (hashing : Bool) (j : Nat) (s : State) : Prop :=
  StageInv s₀ start P X y c (counterCount j)
    (if hashing then hashCount (nr s₀) j else 0) (hashing && decide (nr s₀ ≤ j)) s

theorem roundWork_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing : Bool) (j : Nat)
    (hj : 1 ≤ j) (hjn : j < nr s₀) (h : RoundInv s₀ start P X y c hashing j s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (start.gpr .rdx) start.mem X) :
    WP isa (.block (roundWork (nr s₀) hashing j)) s fun t =>
      RoundInv s₀ start P X y c hashing (j + 1) t ∧ FlowFrame workRegs s t := by
  cases hashing with
  | false => exact counters_ok hp j hj h hv
  | true =>
    have hh : StageInv s₀ start P X y c (counterCount j) (hashCount (nr s₀) j) false s := by
      simpa only [RoundInv, Bool.true_eq, ite_true, Bool.true_and,
        show decide (nr s₀ ≤ j) = false from decide_eq_false (by omega_arith)] using h
    rw [roundWork, ite_eq_left rfl, WP.block_append_iff]
    refine WP.mono (q8_ok hp j hj hjn hh (hx rfl))
      fun t ⟨ht, hf⟩ => ?_
    exact WP.mono (counters_ok hp j hj ht hv) fun u ⟨hu, hfu⟩ => ⟨hu, hf.trans hfu⟩

theorem aesPipeline_ok {s₀ start s : State} {P X : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing : Bool)
    (h : RoundInv s₀ start P X y c hashing 1 s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (start.gpr .rdx) start.mem X) :
    WP isa (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing)) s fun t =>
      (∀ b ∈ aregs, VG.Proof.Aes.X86_64.AesNi.st (t.lane b 0) =
        Spec.Aes.cipher (nr s₀) (sch s₀) (VG.Proof.Aes.X86_64.AesNi.st (s.lane b 0))) ∧
      RoundInv s₀ start P X y c hashing (nr s₀) t := by
  have hpos : 0 < nr s₀ := by rcases hp.rounds with h | h | h <;> omega_arith
  refine WP.mono (aesFixed_ok (nr s₀) hpos aregs (by decide) (by decide)
    (roundWork (nr s₀) hashing) (RoundInv s₀ start P X y c hashing)
    (fun _ _ h => h.env.keys hp) (fun j hj hjn s h => ?_)
    (fun _ _ _ h hf => h.yframe hf) (fun s h => ?_) s h)
    fun t ⟨ha, hq⟩ => ⟨fun b hb => ha b hb 0 (by decide), hq⟩
  · refine WP.mono (roundWork_ok hp hashing j hj hjn h hv hx)
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
    (hp : SPre s₀) (hashing : Bool) (hE : Env s₀ P s) {ld : List Instr}
    (hld : WP isa (.block ld) s (CountersIn s₀ c s))
    (hT : Templates s₀ c 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hx : hashing = true → HashSrc s₀ (s.gpr .rdx) s.mem X) :
    WP isa (.seq (.block ld)
      (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing))) s fun t =>
      (∀ i < 8, XBinOp.eval .pshufb (t.lane (aregs.getD i .xmm3) 0) revMask =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      StageInv s₀ s P X y c 8 (if hashing then 8 else 0) hashing t := by
  have h0 : StageInv s₀ s P X y c 0 0 false s :=
    ⟨hE, hT, hy, fun _ h => (h rfl).elim, fun _ _ => rfl, Frame.refl _ _⟩
  refine WP.seq (WP.mono hld fun t ⟨ht, hf⟩ => ?_)
  refine WP.mono (aesPipeline_ok hp hashing (RoundInv.first hp hashing
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
    (hp : SPre s₀) (ix hashing : Bool) (j : Nat) (hE : Env s₀ P s)
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
    (hx : hashing = true → HashSrc s₀ (s.gpr .rdx) s.mem X) :
    WP isa (batchL ld (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) r else []) ix) s
      (BatchPost s₀ s ix P X y c j hashing) := by
  have hsep : (batchR s j).Disjoint (pR s₀) := hp.d_p.sub_left hsub
  simp only [batchL, show aregs.take 8 = aregs from rfl]
  apply seq_assoc
  refine WP.seq (WP.mono (cipherBatch_ok hp hashing hE hld hT hy hv hx)
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
    (hp : SPre s₀) (ix hashing : Bool) (j : Nat) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hw : ∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwrap : (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64)
    (hsub : Region.Sub (batchR s j) (dR s₀))
    (hsr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (srcAddr s ix (16 * (j + k))) 16)
    (hss : ∀ a b, a < b → b < 8 → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩)
    (hsw : ∀ k < 8, Region.Disjoint ⟨srcAddr s ix (16 * (j + k)), 16⟩ (pR s₀))
    (hx : hashing = true → HashSrc s₀ (s.gpr .rdx) s.mem X) :
    WP isa (batch (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) r else []) ix) s
      (BatchPost s₀ s ix P X y c j hashing) :=
  batchL_ok hp ix hashing j hE hT hy hv (loads_ok hp hE hT) hw hwrap hsub hsr hss hsw hx
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

/-- The data of block `g + j`, at `rdx` at block `g`, and `rbx` as at the start. -/
theorem srcAddr_eq {s₀ s : State} (ix : Bool) {g : Nat} (hrdx : s.gpr .rdx = bAddr s₀ g)
    (hrbx : s.gpr .rbx = s₀.gpr .rbx) (j : Nat) : srcAddr s ix (16 * j) = srcBlk s₀ ix (g + j) := by
  cases ix
  · rw [srcAddr_false, srcBlk_false, hrdx, bAddr_add]
  · simp only [srcAddr, srcBlk, off, ite_true, hrdx, hrbx]
    rw [BitVec.add_assoc, BitVec.add_comm (s₀.gpr .rbx), ← BitVec.add_assoc, bAddr_add]

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
  refine WP.mono (batchL_ok hp ix false j h.env h.templates (X := fun _ => 0) h.hash h.counter hld
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
