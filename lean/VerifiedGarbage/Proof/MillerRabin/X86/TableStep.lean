module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableStore
public import VerifiedGarbage.Proof.MillerRabin.X86.ProductFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts

/-! # One power-table iteration reuses the Montgomery arithmetic and copy -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem table_step {σ s : State} {base : Addr} {bytes w j k : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (hj : 13 ≤ j ∧ j < 27) (hk : 0 < k ∧ k < 2 ^ 32)
    (witness : numAt s.mem base w 5 = numAt σ.mem base w 5)
    (cursor : s.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w j))
    (count : s.mem.readW (off base sK) 32 = BitVec.ofNat 32 k) :
    WP isa tabStep s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sK = k - 1 ∧ t.zf = some (decide (k = 1)) ∧
      t.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w (j + 1)) ∧
      numAt t.mem base w 6 = VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w 6) (numAt σ.mem base w 5) ∧
      numAt t.mem base w j = numAt t.mem base w 6 ∧
      (∀ a, 5 ≤ a → a < 28 → a ≠ 6 → a ≠ j → numAt t.mem base w a = numAt s.mem base w a) := by
  unfold tabStep
  refine WP.seq (WP.mono (facts.multiply (o := 6) (a := 6) (b := 5) h (by decide) (by decide) (by decide) (.inr (.inl rfl))
    (by rw [witness]; exact facts.witness)) ?_)
  rintro u ⟨value, hu, _, frame⟩
  have countU : u.mem.readW (off base sK) 32 = BitVec.ofNat 32 k :=
    (product_frame_header h.context h.room facts.fit (by decide) (by decide : sK + 4 ≤ 256) frame).trans count
  have cursorU : u.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w j) := by
    have e := product_frame_stack h.context h.room facts.fit (by decide)
      (by decide : tableCursor + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes) frame
    have e32 := congrArg (BitVec.setWidth 32) e
    change u.mem.readW (off (byteAddr (s.gpr .esp)) tableCursor) 32 =
      s.mem.readW (off (byteAddr (s.gpr .esp)) tableCursor) 32 at e32
    rw [h.stack] at e32
    exact e32.trans cursor
  refine WP.mono (table_store hu facts.lower facts.upper facts.fit hj hk facts.width cursorU countU) ?_
  rintro t ⟨ht, countT, zero, cursorT, appended, same⟩
  have acc := same 6 (by decide) (by omega)
  rw [witness] at value
  refine ⟨ht, countT, zero, cursorT, acc.trans value, appended.trans acc.symm, ?_⟩
  intro a lo hi ne6 nej
  exact (same a hi nej).trans (product_frame_num h.context h.room facts.fit (by decide) ⟨lo, hi⟩ ne6 frame)

end VG.Proof.MillerRabin.X86
