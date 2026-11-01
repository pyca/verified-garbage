module
public import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Weierstrass.MontContract
/-! # Setting one divstep workspace word -/
@[expose] public section
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86
theorem setWord_ok {s : State} {base : Addr} {size dst : Nat} (x : BitVec 32)
    (hs : Scr s base size) (hd : dst + 4 ≤ size) :
    WP isa (.block (setWord dst x)) s fun u =>
      w32 u.mem base dst = x.toNat ∧ Keeps [.eax] s u ∧ Outside base dst 4 s.mem u.mem := by
  have hn := hs.nowrap
  unfold setWord
  refine wp_movS rfl fun s₁ U₁ _ => ?_
  have hs₁ := hs.of_keeps U₁.keeps (by decide)
  refine wp_storeS (hs₁.ea (by omega)) (hs₁.write hd) fun u U₂ => WP.block_nil ?_
  refine ⟨?_, U₁.keeps.trans (U₂.keeps _), ?_⟩
  · rw [U₂.mem, w32_write_self, U₁.gpr]
  · rw [U₂.mem, U₁.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Weierstrass.X86.Inv
