import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Schedule

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
