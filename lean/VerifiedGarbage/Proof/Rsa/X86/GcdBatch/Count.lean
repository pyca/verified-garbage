module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The fixed public batch count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem countDown_ok {s : State} {base : Addr} {size j d : Nat}
    (hs : Scr s base size) (ht : d+4 ≤ size) (hj : 1 ≤ j) (hj32 : j < 2 ^ 32)
    (hc : w32 s.mem base d = j) :
    WP isa (.block (countDown d)) s fun z =>
      w32 z.mem base d = j - 1 ∧ z.zf = some (decide (j - 1 = 0)) ∧
      Keeps [.esi] s z ∧ Outside base d 4 s.mem z.mem := by
  have hn := hs.nowrap
  unfold countDown
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ U₁ _ => ?_
  have J : s₁.gpr .esi = BitVec.ofNat 32 j := by
    rw [U₁.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj32]
    exact hc
  refine wp_decCounter hj J fun s₂ J₂ K₂ M₂ => ?_
  have K := U₁.keeps.trans K₂
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (by omega)) fun s₃ U₃ => ?_
  have J₃ : s₃.gpr .esi = BitVec.ofNat 32 (j - 1) := by rw [U₃.gpr, J₂]
  refine wp_testCounter (by omega) J₃ fun z F hz => WP.block_nil ⟨?_, hz, ?_, ?_⟩
  · rw [F.mem, U₃.mem, w32_write_self, J₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · exact (K.trans (U₃.keeps _)).trans (F.keeps _)
  · rw [F.mem, U₃.mem, M₂, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Rsa.X86.GcdBatch
