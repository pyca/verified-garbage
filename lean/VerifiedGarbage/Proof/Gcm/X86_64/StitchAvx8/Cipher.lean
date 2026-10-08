import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Loads

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
