module

public import VerifiedGarbage.Proof.MillerRabin.X86.HeaderPair
public import VerifiedGarbage.Proof.MillerRabin.X86.SquareLoop

/-! # Initialize the fixed four-squaring run of each exponent window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem square_four_init {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes) :
    WP isa (.block sqFour) s fun t => Stage base bytes w σ t ∧
      w32 t.mem base sR = 0 ∧ w32 t.mem base sQ = 4 ∧
      Frame ([sR, sQ].map (fun d => ⟨off base d, 4⟩)) s.mem t.mem := by
  refine WP.mono (h.header_pair (d := sR) (e := sQ) (x := 0) (y := 4) hf (by decide) (by decide)) ?_
  rintro t ⟨ht, mem, frame⟩
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have nw256 : base.toNat + 256 ≤ 2 ^ 32 := Nat.le_trans (Nat.add_le_add_left hdrFit _) h.context.ws.nowrap
  refine ⟨ht, ?_, ?_, frame⟩
  · rw [mem, w32_write_ne nw256 (by decide : sQ + 4 ≤ 256) (by decide : sR + 4 ≤ 256)
      (by decide), w32_write_self]
    rfl
  · rw [mem, w32_write_self]
    rfl

end VG.Proof.MillerRabin.X86
