module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundState
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCompare

/-! # Effects of one residue square and its terminal comparisons -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

def roundWrites (n : Nat) : List (Nat × Nat) := productRanges n ++ [(roundCount, 4), (roundStatus, 4)]

theorem roundWrites_square {base : Addr} {n : Nat} {s t : Mem} (O : Outs base (productRanges n) s t) :
    Outs base (roundWrites n) s t := O.mono (by intro r hr; exact List.mem_append_left _ hr)

theorem roundWrites_control {base : Addr} {n d : Nat} {s t : Mem}
    (O : Outside base d 4 s t) (hd : d = roundCount ∨ d = roundStatus) :
    Outs base (roundWrites n) s t := by
  apply Outs.of_outside O
  rcases hd with rfl | rfl <;> simp [roundWrites]

theorem roundCompare_ready {base : Addr} {n m size : Nat} {s : State} (R : RoundReady base n m size s) :
    WP isa (roundCompare n) s fun t => RoundReady base n m size t ∧
      t.zf = some (decide (¬ (wordsVal s.mem base (slot n 6) n = 1 ∨ wordsVal s.mem base (slot n 6) n = m - 1))) ∧
      t.mem.readW (off base roundStatus) 32 = mask32 (wordsVal s.mem base (slot n 6) n = m - 1) ∧
      wordsVal t.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n ∧
      t.mem.readW (off base roundCount) 32 = s.mem.readW (off base roundCount) 32 ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
  refine WP.mono (roundCompare_ok R.context R.width R.room R.one R.minus rfl)
    fun t ⟨zf, status, O, K⟩ => ?_
  have count : t.mem.readW (off base roundCount) 32 = s.mem.readW (off base roundCount) 32 := by
    apply BitVec.eq_of_toNat_eq
    exact O.w32 (by decide) (by decide)
  refine ⟨R.control (.inr rfl) O K (by decide) (by decide), zf, status, ?_, count,
    roundWrites_control O (.inr rfl), K⟩
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact O.val32 (by have := R.bound (j := 6) (by decide); simp only [roundCount, roundStatus] at *; omega)
    (by have := R.bound (j := 6) (by decide); unfold roundCount at *; omega)

theorem roundSquare_ok {base : Addr} {n m size : Nat} {s : State} (R : RoundReady base n m size s) :
    WP isa (roundSquare n) s fun t =>
      let z := wordsVal s.mem base (slot n 6) n * wordsVal s.mem base (slot n 6) n % m
      RoundReady base n m size t ∧ t.zf = some (decide (¬ (z = 1 ∨ z = m - 1))) ∧
      t.mem.readW (off base roundStatus) 32 = mask32 (z = m - 1) ∧
      wordsVal t.mem base (slot n 6) n = z ∧
      t.mem.readW (off base roundCount) 32 = s.mem.readW (off base roundCount) 32 ∧
      Outs base (roundWrites n) s.mem t.mem ∧ Keeps clob s t := by
  unfold roundSquare
  refine WP.seq (WP.mono R.square fun a ⟨Ra, value, Oa, Ka⟩ => ?_)
  have count : a.mem.readW (off base roundCount) 32 = s.mem.readW (off base roundCount) 32 := by
    apply BitVec.eq_of_toNat_eq
    have v := Oa.val32 (d := roundCount) (k := 1) (by
      intro r hr
      simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hn := R.width
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride, roundCount] <;> omega) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using v
  refine WP.mono (roundCompare_ready Ra) fun t ⟨Rt, zf, status, vt, ct, Ot, Kt⟩ => ?_
  rw [value] at zf status vt
  exact ⟨Rt, zf, status, vt, ct.trans count, (roundWrites_square Oa).trans Ot, Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
