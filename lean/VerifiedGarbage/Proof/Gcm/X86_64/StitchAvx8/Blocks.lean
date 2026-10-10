import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Pipeline
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.AesHash
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Data
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffers
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.SetupDispatch

/-! ## Schedule -/
section

/-! # Connecting the hash and counter work to the fixed AES schedules -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs q8 prepCounter gh8 prepare reduceFinal)
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
    1 ≤ j → j < nr → ∀ more : Bool,
    (hashCount nr j < 8 ∧ hashCount nr (j + 1) = hashCount nr j + 1 ∧
      j + 1 < nr ∧ q8 nr more j = gh8 ((hashCount nr j + 1) % 8) ++
        (if more then prepare (8 + (hashCount nr j + 1) % 8) else [])) ∨
    (hashCount nr j = 8 ∧ hashCount nr (j + 1) = 8 ∧ j + 1 = nr ∧
      q8 nr more j = reduceFinal) ∨
    (hashCount nr (j + 1) = hashCount nr j ∧ j + 1 < nr ∧ q8 nr more j = []) := by
  intro nr _ hn j _ hj hjn more
  rcases hn with rfl | rfl | rfl <;> interval_cases j <;> simp [hashCount, q8]

theorem q8_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nc : Nat} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j) (hjn : j < nr s₀)
    (h : StageInv s₀ start P X Y y c nc (hashCount (nr s₀) j) false s)
    (more : Bool)
    (hr : more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.block (q8 (nr s₀) more j)) s fun t =>
      StageInv s₀ start P X Y y c nc (hashCount (nr s₀) (j + 1))
        (decide (nr s₀ ≤ j + 1)) t ∧ FlowFrame workRegs s t := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega
  rcases schedule_cases _ hn hp.rounds j (by omega) hj hjn more with
    ⟨h8, hnext, hlt, hc⟩ | ⟨h8, hnext, he, hc⟩ | ⟨hnext, hlt, hc⟩
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega)]
    exact WP.mono (h.hashStep hp h8 more hr hs hx hY) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · rw [hc, hnext, he, show decide (nr s₀ ≤ nr s₀) = true from decide_eq_true (Nat.le_refl _)]
    rw [h8] at h
    exact h.finishHash hp
  · rw [hc, hnext, show decide (nr s₀ ≤ j + 1) = false from decide_eq_false (by omega)]
    exact WP.block_nil ⟨h, .refl _ _⟩
 
/-- The counter work appended to the hash work in each AES round. -/
def counterWork (j : Nat) : List Instr :=
  if 1 ≤ j ∧ j ≤ 2 then
    (List.range 4).flatMap (fun i => prepCounter (4 * (j - 1) + i)) else []

theorem counters_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c nh : Nat} {finished : Bool} (hp : SPre s₀) (j : Nat) (hj : 1 ≤ j)
    (h : StageInv s₀ start P X Y y c (counterCount j) nh finished s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)) :
    WP isa (.block (counterWork j)) s fun t =>
      StageInv s₀ start P X Y y c (counterCount (j + 1)) nh finished t ∧
        FlowFrame workRegs s t := by
  by_cases h1 : j = 1
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  by_cases h2 : j = 2
  · subst j
    exact WP.mono (h.counters hp 4 (by decide) hv) fun t ⟨ht, hf⟩ =>
      ⟨ht, hf.mono (by decide)⟩
  · have hgt : 2 < j := by omega
    simp only [counterWork, show ¬(1 ≤ j ∧ j ≤ 2) from by omega, ite_false]
    have he : counterCount (j + 1) = counterCount j := by
      simp only [counterCount, show ¬j ≤ 1 from by omega,
        show ¬j + 1 ≤ 1 from by omega, show j + 1 ≠ 2 from by omega, h2, ite_false]
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
def roundWork (nr : Nat) (hashing more : Bool) (j : Nat) : List Instr :=
  (if hashing then q8 nr more j else []) ++ counterWork j

def RoundInv (s₀ start : State) (P X Y : Nat → Block) (y : Block) (c : Nat)
    (hashing : Bool) (j : Nat) (s : State) : Prop :=
  StageInv s₀ start P X Y y c (counterCount j)
    (if hashing then hashCount (nr s₀) j else 0) (hashing && decide (nr s₀ ≤ j)) s

theorem roundWork_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing more : Bool) (j : Nat)
    (hj : 1 ≤ j) (hjn : j < nr s₀) (h : RoundInv s₀ start P X Y y c hashing j s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hr : hashing = true → more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : hashing = true → more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : hashing = true → more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : hashing = true → ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.block (roundWork (nr s₀) hashing more j)) s fun t =>
      RoundInv s₀ start P X Y y c hashing (j + 1) t ∧ FlowFrame workRegs s t := by
  cases hashing with
  | false => exact counters_ok hp j hj h hv
  | true =>
    have hh : StageInv s₀ start P X Y y c (counterCount j) (hashCount (nr s₀) j) false s := by
      simpa only [RoundInv, Bool.true_eq, ite_true, Bool.true_and,
        show decide (nr s₀ ≤ j) = false from decide_eq_false (by omega)] using h
    rw [roundWork, ite_eq_left rfl, WP.block_append_iff]
    refine WP.mono (q8_ok hp j hj hjn hh more (hr rfl) (hs rfl) (hx rfl) (hY rfl))
      fun t ⟨ht, hf⟩ => ?_
    exact WP.mono (counters_ok hp j hj ht hv) fun u ⟨hu, hfu⟩ => ⟨hu, hf.trans hfu⟩

theorem aesPipeline_ok {s₀ start s : State} {P X Y : Nat → Block} {y : Block}
    {c : Nat} (hp : SPre s₀) (hashing more : Bool)
    (h : RoundInv s₀ start P X Y y c hashing 1 s)
    (hv : (start.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hr : hashing = true → more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : hashing = true → more = true → ∀ k < 16, Region.Disjoint
      ⟨start.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : hashing = true → more = true → ∀ k < 16, Spec.Gcm.blockAt start.mem
      (start.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : hashing = true → ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing more)) s fun t =>
      (∀ b ∈ aregs, VG.Proof.Aes.X86_64.AesNi.st (t.lane b 0) =
        Spec.Aes.cipher (nr s₀) (sch s₀) (VG.Proof.Aes.X86_64.AesNi.st (s.lane b 0))) ∧
      RoundInv s₀ start P X Y y c hashing (nr s₀) t := by
  have hpos : 0 < nr s₀ := by rcases hp.rounds with h | h | h <;> omega
  refine WP.mono (aesFixed_ok (nr s₀) hpos aregs (by decide) (by decide)
    (roundWork (nr s₀) hashing more) (RoundInv s₀ start P X Y y c hashing)
    (fun _ _ h => h.env.keys hp) (fun j hj hjn s h => ?_)
    (fun _ _ _ h hf => h.yframe hf) (fun s h => ?_) s h)
    fun t ⟨ha, hq⟩ => ⟨fun b hb => ha b hb 0 (by decide), hq⟩
  · refine WP.mono (roundWork_ok hp hashing more j hj hjn h hv hr hs hx hY)
      fun t ⟨ht, hf⟩ => ⟨ht, fun b hb l hl => ?_⟩
    exact hf.lane b ((by decide : ∀ r ∈ aregs, r ∉ workRegs) b hb) l (by
      change l < 1 at hl; omega)
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

theorem RoundInv.first {s₀ start s : State} {P X Y : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing : Bool)
    (h : StageInv s₀ start P X Y y c 0 0 false s) : RoundInv s₀ start P X Y y c hashing 1 s := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega
  have h1 : ¬nr s₀ ≤ 1 := by rcases hp.rounds with h | h | h <;> omega
  simp only [RoundInv, (round_bounds _ hn hp.rounds).1, counterCount,
    Nat.le_refl, ite_true, ite_self, decide_eq_false h1, Bool.and_false]
  exact h

theorem RoundInv.last {s₀ start s : State} {P X Y : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) {hashing : Bool} (h : RoundInv s₀ start P X Y y c hashing (nr s₀) s) :
    StageInv s₀ start P X Y y c 8 (if hashing then 8 else 0) hashing s := by
  have hn : nr s₀ < 15 := by rcases hp.rounds with h | h | h <;> omega
  simpa only [RoundInv, (round_bounds _ hn hp.rounds).2.1,
    (round_bounds _ hn hp.rounds).2.2, Nat.le_refl, decide_true, Bool.and_true] using h

theorem Templates.read {s₀ : State} {c : Nat} {m : Mem}
    (h : Templates s₀ c 0 m) (i : Nat) (hi : i < 8) :
    m.readW (templateAddr s₀ i) 128 =
      XBinOp.eval .pshufb (Nat.repeat inc32 (c + i) (cb s₀)) revMask := by
  have ht := h i hi
  simp only [Nat.not_lt_zero, ite_false, Nat.add_zero] at ht
  rw [← ht, blockAt_eq, pshufb_rev_rev]

/-- The first two phases of `batch`: load the counters, then encrypt them
while refreshing the next counters and, optionally, hashing eight inputs. -/
theorem cipherBatch_ok {s₀ s : State} {P X Y : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing more : Bool) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hB : Prepared s₀ X Y 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hr : hashing = true → more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : hashing = true → more = true → ∀ k < 16, Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : hashing = true → more = true → ∀ k < 16, Spec.Gcm.blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : hashing = true → ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (.seq (.block ((List.range 8).map fun i =>
      .vmovdquLoad .l128 (aregs.getD i .xmm3) (at_ .r11 (640 + 16 * i))))
      (aesFixed (nr s₀) aregs (roundWork (nr s₀) hashing more))) s fun t =>
      (∀ i < 8, XBinOp.eval .pshufb (t.lane (aregs.getD i .xmm3) 0) revMask =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      StageInv s₀ s P X Y y c 8 (if hashing then 8 else 0) hashing t := by
  have h0 : StageInv s₀ s P X Y y c 0 0 false s :=
    ⟨hE, hT, hB, hy, fun _ h => (h rfl).elim, fun _ _ => rfl, Frame.refl _ _⟩
  refine WP.seq (WP.mono (loadCounters_ok s (fun i hi => by
    rw [ea_at, BitVec.ofInt_natCast, hE.rd, hE.wr, hE.r11]
    exact in_rdwr (in_sub hp.p_in (by omega))) 8 (by decide)) fun t ⟨ht, hf⟩ => ?_)
  refine WP.mono (aesPipeline_ok hp hashing more (RoundInv.first hp hashing
    (h0.yframe (hf.mono (fun _ hr => List.mem_cons_of_mem _ hr)))) hv hr hs hx hY) fun u ⟨hu, hQ⟩ => ?_
  refine ⟨fun i hi => ?_, hQ.last hp⟩
  apply Eq.symm
  apply aesWith_eq
  rw [hu _ (aregs_member i hi), ht i hi, ea_at, BitVec.ofInt_natCast, hE.r11]
  exact congrArg (fun x => Spec.Aes.cipher (nr s₀) (sch s₀)
    (VG.Proof.Aes.X86_64.AesNi.st x)) (hT.read i hi)

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Batch -/
section

/-! # One complete eight-block pipeline batch -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Impl.Gcm.X86_64.StitchAvx8 (aregs batch xorData)
open VG.Spec.Gcm (Block inc32 blockAt)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Proof.Gcm.X86_64 (revMask)

def batchR (s : State) (j : Nat) : Region :=
  ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩

structure BatchPost (s₀ start : State) (P X Y : Nat → Block) (y : Block)
    (c j : Nat) (hashing : Bool) (s : State) : Prop where
  env : Env s₀ P s
  templates : Templates s₀ (c + 8) 0 s.mem
  prepared : Prepared s₀ X Y (if hashing then 8 else 0) s.mem
  hash : s.lane .xmm2 0 = if hashing then reduceB (accN X P y 8) else y
  data : ∀ k < 8, blockAt s.mem (start.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
    blockAt start.mem (start.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  frame : Frame [batchR start j, workR s₀] start.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .r8 → s.gpr r = start.gpr r
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 16)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem batch_ok {s₀ s : State} {P X Y : Nat → Block} {y : Block} {c : Nat}
    (hp : SPre s₀) (hashing more : Bool) (j : Nat) (hE : Env s₀ P s)
    (hT : Templates s₀ c 0 s.mem) (hB : Prepared s₀ X Y 0 s.mem) (hy : s.lane .xmm2 0 = y)
    (hv : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8))
    (hw : ∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16)
    (hwrap : (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64)
    (hsub : Region.Sub (batchR s j) (dR s₀))
    (hr : hashing = true → more = true → ∀ k < 16, InRegions (s₀.rd ++ s₀.wr)
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) 16)
    (hs : hashing = true → more = true → ∀ k < 16, Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * k), 16⟩ (pR s₀))
    (hx : hashing = true → more = true → ∀ k < 16, blockAt s.mem
      (s.gpr .rdx + BitVec.ofNat 64 (16 * k)) = X k)
    (hY : hashing = true → ∀ i < 8, Y i = if more then X (8 + i) else X i) :
    WP isa (batch (nr s₀) 8 j (fun r => if hashing then
      VG.Impl.Gcm.X86_64.StitchAvx8.q8 (nr s₀) more r else [])) s
      (BatchPost s₀ s P X Y y c j hashing) := by
  have hsep : (batchR s j).Disjoint (pR s₀) := hp.d_p.sub_left hsub
  simp only [batch, show aregs.take 8 = aregs from rfl]
  apply seq_assoc
  refine WP.seq (WP.mono (cipherBatch_ok hp hashing more hE hT hB hy hv hr hs hx hY)
    fun t ⟨hks, ht⟩ => ?_)
  rw [WP.block_append_iff]
  have hrdx : t.gpr .rdx = s.gpr .rdx := ht.regs _ (by decide)
  refine WP.mono (xorData_ok aregs j t (by decide) (fun k hk => by
    rw [ht.env.wr, hrdx, BitVec.ofInt_natCast]; exact hw k hk)
    (by rw [hrdx]; exact hwrap)) fun u ⟨hdata, hm, hg, hrd, hwr, hlanes⟩ => ?_
  rw [hrdx] at hdata hm
  have hmD : Frame [dR s₀] t.mem u.mem := hm.sub fun r hr' => by
    simp only [List.mem_singleton] at hr'
    subst r
    exact ⟨dR s₀, List.mem_singleton_self _, hsub⟩
  have hEu := ht.env.writeData hp hg hrd hwr hmD
  have hTu : Templates s₀ (c + 8) 0 u.mem := ht.templates.next.frame hm (by
    intro r hr'; simp only [List.mem_singleton] at hr'; subst r
    exact hsep.symm.sub_left (Offset.sub_base (pp s₀) (d := 640) (n := 128) (k := 1024) (by decide)))
  have hBu := ht.prepared.frame hm (by
    intro r hr'; simp only [List.mem_singleton] at hr'; subst r
    exact hsep.symm.sub_left (Offset.sub_base (pp s₀) (d := 512) (n := 128) (k := 1024) (by decide)))
  have hDu : ∀ k < 8, blockAt u.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
      blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
        ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := by
    intro k hk
    have hks' := hks k hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < aregs.length from hk), Option.getD_some] at hks'
    rw [hdata k hk]
    refine congrArg₂ (fun a b : Block => a ^^^ b) ?_ hks'
    exact VG.Proof.Aes.X86_64.AesNi.blockAt_frame ht.frame (by
      intro r hr'; simp only [List.mem_singleton] at hr'; subst r
      exact (hsep.sub_left (by
        simpa only [batchR, ← Offset.add_add, Nat.mul_add] using
          (Offset.sub (s.gpr .rdx) (d := 16 * (j + k)) (e := 16 * j)
            (n := 16) (k := 128) (by omega) (by omega)))).sub_right (work_sub_p s₀))
  have hFu : Frame [batchR s j, workR s₀] s.mem u.mem :=
    (ht.frame.mono (by simp)).trans (hm.mono (by simp [batchR, aregs]))
  refine WP.mono (bump_ok u) fun v ⟨hv8, hvg, hvm, hvl, hvrd, hvwr⟩ => ?_
  refine ⟨hEu.move (fun r _ _ h8 _ => hvg r h8) hvm hvrd hvwr,
    hvm ▸ hTu, hvm ▸ hBu, ?_, ?_, hvm ▸ hFu, ?_, ?_⟩
  · rw [hvl, hlanes .xmm2 (by decide) 0 (by decide)]; exact ht.hash
  · rw [hvm]; exact hDu
  · intro r hrax hr8; rw [hvg r hr8, hg]; exact ht.regs r hrax
  · rw [hv8, hg, ht.regs .r8 (by decide), hv, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 32 (c + 8) + BitVec.ofNat 32 8 = BitVec.ofNat 32 (c + 16)
    rw [← BitVec.ofNat_add]

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## DataInv -/
section

/-! # The prefix of data already transformed by counter mode -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block blockAt)

def DataInv (s₀ : State) (c : Nat) (m : Mem) : Prop :=
  ∀ k < nb s₀, blockAt m (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k

theorem bAddr_add (s₀ : State) (g k : Nat) :
    bAddr s₀ g + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by
  simp only [bAddr, Offset.add_add]
  congr 2
  omega

theorem bAddr_toNat {s₀ : State} (hp : SPre s₀) (k : Nat) (hk : k < nb s₀) :
    (bAddr s₀ k).toNat = (dp s₀).toNat + 16 * k := by
  have hw := hp.wrap_d
  rw [bAddr, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 16 * k < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

theorem DataInv.frame {s₀ : State} {c : Nat} {m m' : Mem} {rs : List Region}
    (h : DataInv s₀ c m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, (dR s₀).Disjoint r) : DataInv s₀ c m' := by
  intro k hk
  exact (VG.Proof.Aes.X86_64.AesNi.blockAt_frame hf (fun r hr =>
    (hs r hr).sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega)))).trans (h k hk)

theorem DataInv.initial {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Ready s₀ P s) : DataInv s₀ 0 s.mem :=
  (show DataInv s₀ 0 s₀.mem from fun _ _ => rfl).frame h.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.d_p)

theorem DataInv.batch {s₀ s t : State} {P X Y : Nat → Block} {y : Block}
    {c j : Nat} {hashing : Bool} (hp : SPre s₀) (h : DataInv s₀ c s.mem)
    (hc : c + 8 ≤ nb s₀) (ha : s.gpr .rdx + BitVec.ofNat 64 (16 * j) = bAddr s₀ c)
    (hb : BatchPost s₀ s P X Y y c j hashing t) : DataInv s₀ (c + 8) t.mem := by
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (16 * (j + i)) = bAddr s₀ (c + i) := by
    intro i
    rw [show 16 * (j + i) = 16 * j + 16 * i by omega, ← Offset.add_add, ha, bAddr_add]
  have hm : Frame [⟨bAddr s₀ c, 128⟩, workR s₀] s.mem t.mem := by
    simpa only [batchR, ha] using hb.frame
  intro k hk
  by_cases hin : c ≤ k ∧ k < c + 8
  · have hi : k - c < 8 := by omega
    have hv := hb.data (k - c) hi
    rw [addr, show c + (k - c) = k by omega] at hv
    rw [hv, h k hk, ite_eq_right (by omega : ¬k < c), ite_eq_left hin.2]
  · have he : (if k < c + 8 then ctb s₀ k else blk s₀ k) =
        (if k < c then ctb s₀ k else blk s₀ k) := by
      split_ifs <;> first | rfl | omega
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame hm (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hw := hp.wrap_d
        exact Offset.disjoint (dp s₀) (d := 16 * k) (n := 16) (e := 16 * c) (k := 128)
          (by omega) (by omega) (by omega)
      · exact (hp.d_p.sub_left (Offset.sub_base (dp s₀) (d := 16 * k) (n := 16) (k := 16 * nb s₀) (by omega))).sub_right (work_sub_p s₀)), he]
    exact h k hk

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Core -/
section

/-! # Data and hash positions shared by the encrypt and decrypt loops -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block ghashFrom)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)

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

structure CoreInv (s₀ : State) (P : Nat → Block) (dec : Bool) (c g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ c s.mem
  templates : Templates s₀ c 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ dec g
  c_le : c ≤ nb s₀
  g_le : g ≤ nb s₀

theorem CoreInv.initial {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Ready s₀ P s) (dec : Bool) : CoreInv s₀ P dec 0 0 s := by
  refine ⟨h.env, DataInv.initial hp h, h.templates, h.counter, ?_, ?_, ?_, Nat.zero_le _, Nat.zero_le _⟩
  · simpa only [bAddr, Nat.mul_zero, BitVec.add_zero] using h.cursor
  · simpa only [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.remaining
  · exact h.hash

theorem CoreInv.addr {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (h : CoreInv s₀ P dec c g s) (k : Nat) :
    s.gpr .rdx + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by rw [h.cursor, bAddr_add]

theorem CoreInv.batchBounds {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (j : Nat) (hj : g + j = c) (hc : c + 8 ≤ nb s₀) :
    (∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16) ∧
    (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64 ∧ Region.Sub (batchR s j) (dR s₀) := by
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [h.addr, ← Nat.add_assoc, hj]
    exact in_sub hp.d_in (by omega)
  · rw [h.cursor, bAddr_toNat hp g (by omega)]
    have hw := hp.wrap_d
    omega
  · change Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩ (dR s₀)
    rw [h.addr, hj]
    exact Offset.sub_base (dp s₀) (d := 16 * c) (n := 128) (k := 16 * nb s₀) (by omega)

theorem CoreInv.bareBatch {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (j : Nat) (hj : g + j = c) (hc : c + 8 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 j (fun _ => [])) s
      (CoreInv s₀ P dec (c + 8) g) := by
  let X : Nat → Block := fun i => s.mem.readW (hashAddr s₀ i) 128
  have hB : Prepared s₀ X X 0 s.mem := fun _ _ => rfl
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp j hj hc
  refine WP.mono (batch_ok hp false false j h.env h.templates hB h.hash h.counter hw hwrap hsub
    (fun he => Bool.noConfusion he) (fun he => Bool.noConfusion he)
    (fun he => Bool.noConfusion he) (fun he => Bool.noConfusion he)) fun t ht => ?_
  refine ⟨ht.env, h.data.batch hp hc (by rw [h.addr, hj]) ht, ht.templates, ?_,
    (ht.regs _ (by decide) (by decide)).trans h.cursor,
    (ht.regs _ (by decide) (by decide)).trans h.remaining, ht.hash, hc, h.g_le⟩
  simpa only [Nat.add_assoc, Nat.reduceAdd] using ht.counter

end VG.Proof.Gcm.X86_64.StitchAvx8

end
