module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Accept precisely the compressed SEC 1 tags and retain their parity -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_str wp_dp wp_mov op2_imm op2_reg op2_lsr dpVal)

private theorem tagMask : ∀ b : Byte,
    0 - (((((b.setWidth 32 ||| 1) ^^^ 3) - 1) >>> 31)) = mask32 (b = 2 ∨ b = 3) := by
  decide

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : s.gpr .r1 = q)
    (hin : InRegions (s.rd ++ s.wr) (State.addr q) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressTag c)) s fun t =>
      t.gpr .r5 = mask32 (s.mem (State.addr q) = 2 ∨ s.mem (State.addr q) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr q)).setWidth 32 ∧
      Rest [.r4, .r5] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.Arm.decompressTag
  refine wp_ldrb (by decide) (a := State.addr q) (by rw [hq]; simp) hin fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_str (hs₁.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.write hD) fun s₂ m₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun t u₈ => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (State.addr q)).setWidth 32) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, u₁.gpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₈.gpr, dpVal, u₇.gpr, u₇.other .r4 (by decide), u₆.gpr, u₅.gpr, dpVal,
      u₄.gpr, dpVal, u₃.gpr, dpVal, m₂.gpr, u₁.gpr]
    exact tagMask _
  · rw [hm, Mem.readW_writeW_self32]
  · exact (u₁.rest (by simp)).trans ((m₂.rest _).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans
      ((u₇.rest (by simp)).trans (u₈.rest (by simp))))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.Arm
