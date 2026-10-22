module

public import VerifiedGarbage.Proof.MillerRabin.X86.ProductTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.SquareFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Window

/-! # Weak value invariants needed to compose timing certificates -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

structure BaseReady (σ : State) (base : Addr) (bytes w : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)
  flag : ∃ F : Bool, w32 s.mem base sF = F.toNat

structure SquareReady (σ : State) (base : Addr) (bytes w q : Nat) (s : State) : Prop
    extends BaseReady σ base bytes w s where
  count : w32 s.mem base sQ = q
  threshold : w32 s.mem base sR < 2 ^ 31

structure WindowReady (σ : State) (base : Addr) (bytes w k : Nat) (s : State) : Prop
    extends BaseReady σ base bytes w s where
  count : w32 s.mem base sK = k
  table : ∀ i, i < 16 → numAt s.mem base w (11 + i) < val32 σ.mem base 256 (2 * w)

theorem square_ready_step {σ s : State} {base : Addr} {bytes w q : Nat}
    (facts : RoundFacts σ base bytes w) (h : SquareReady σ base bytes w q s) (hq : 0 < q ∧ q < 2 ^ 31) :
    WP isa sqStep s fun t => SquareReady σ base bytes w (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨F, flag⟩ := h.flag
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  refine WP.mono (square_step facts h.stage hq h.threshold
    (readW_of_w32 (by omega) h.count) (readW_of_w32 (by have := h.threshold; omega) rfl)
    (readW_of_w32 (boolSmall F) flag) h.reduced) ?_
  rintro t ⟨stage, count, zero, value, flagT, frame⟩
  have pos : 0 < val32 σ.mem base 256 (2 * w) := by have := facts.odd; omega
  have sameR := square_frame_header h.stage.context h.stage.room facts.fit (by decide : sR + 4 ≤ 256)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl <;> decide) frame
  refine ⟨⟨⟨stage, by rw [value]; exact VG.Proof.MillerRabin.Math.mm_lt pos, ⟨_, flagT⟩⟩, count, ?_⟩, zero⟩
  change (t.mem.readW (off base sR) 32).toNat < 2 ^ 31
  rw [sameR]
  exact h.threshold

theorem window_ready_step {σ s : State} {base : Addr} {bytes w k : Nat}
    (facts : RoundFacts σ base bytes w) (h : WindowReady σ base bytes w k s) (hk : 0 < k ∧ k < 2 ^ 32) :
    WP isa win s fun t => WindowReady σ base bytes w (k - 1) t ∧
      t.zf = some (decide ((k - 1) % 8 = 0)) := by
  obtain ⟨F, flag⟩ := h.flag
  let v := s.mem.readW (off base sV) 32
  let d := (v >>> 28).toNat
  have digit : v >>> 28 = BitVec.ofNat 32 d := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (v >>> 28).isLt).symm
  have hd : d < 16 := by
    dsimp only [d]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := v.isLt
    omega
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  let T := fun i => numAt s.mem base w (11 + i)
  have headers : WindowHeaders s.mem base v k F :=
    ⟨rfl, readW_of_w32 hk.2 h.count, readW_of_w32 (boolSmall F) flag⟩
  refine WP.mono (window_ok (T := T) facts h.stage headers hd hk digit (fun _ _ => rfl) h.table h.reduced) ?_
  rintro t ⟨stage, value, flagT, _, count, zero, same⟩
  have pos : 0 < val32 σ.mem base 256 (2 * w) := by have := facts.odd; omega
  refine ⟨⟨⟨stage, ?_, ⟨_, flagT⟩⟩, count, ?_⟩, zero⟩
  · rw [value]
    exact VG.Proof.MillerRabin.Math.mm_lt pos
  · intro i hi
    rw [same (11 + i) (by omega) (by omega) (by omega) (by omega)]
    exact h.table i hi

end VG.Proof.MillerRabin.X86
