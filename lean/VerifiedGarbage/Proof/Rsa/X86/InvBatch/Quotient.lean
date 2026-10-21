module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # A runtime Montgomery quotient word -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
  VG.Proof.Mont VG.Proof.Mont.X86

theorem quo_ok {s : State} {base : Addr} {size acc tmp iv : Nat}
    (hs : Scr s base size) (ha : acc+4 ≤ size) (ht : tmp+4 ≤ size) (hi : iv+4 ≤ size) :
    WP isa (.block (quo acc tmp iv)) s fun z =>
      w32 z.mem base tmp = w32 s.mem base acc*w32 s.mem base iv%2^32 ∧
      Keeps [.eax,.ecx,.edx] s z ∧ Outside base tmp 4 s.mem z.mem := by
  have nowrap := hs.nowrap
  unfold quo
  refine wp_movS (readSrc_sc hs ha) fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_movS (readSrc_sc hs₁ hi) fun s₂ U₂ _ => ?_
  refine wp_mul fun s₃ U₃ => ?_
  have K : Keeps [.eax,.ecx,.edx] s s₃ :=
    ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))
  have hs₃ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write ht) fun z U₄ => WP.block_nil ?_
  refine ⟨?_,K.trans (U₄.keeps _),?_⟩
  · rw [U₄.mem,w32_write_self,U₃.eax,U₂.other _ (by decide),U₁.gpr,U₂.gpr,U₁.mem,BitVec.toNat_ofNat]
  · rw [U₄.mem,U₃.mem,U₂.mem,U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Rsa.X86.InvBatch
