module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout

/-! # Accept exactly SEC 1 tags 02 and 03 on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86

private theorem tag_key (b : Byte) :
    (((b.setWidth 32 ||| 1) ^^^ 3).toNat < (1 : BitVec 32).toNat) ↔ b = 2 ∨ b = 3 := by
  revert b; decide +kernel

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : readSrc s (.mem (Cfg.argOp 1)) = some q)
    (hin : InRegions (s.rd ++ s.wr) (q.setWidth 64) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressTag c)) s fun t =>
      t.gpr .edx = mask32 (s.mem (q.setWidth 64) = 2 ∨ s.mem (q.setWidth 64) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q.setWidth 64)).setWidth 32 ∧
      Keeps [.ebx, .edx] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.X86.decompressTag
  refine wp_movS hq fun s₁ u₁ _ => ?_
  refine wp_movzx8S (a := q.setWidth 64)
    (by show (s₁.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = _; rw [u₁.gpr, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.ebx, .edx] s s₂ := (u₁.keeps.mono (by simp)).trans (u₂.keeps.mono (by simp))
  have hs₂ := hs.of_keeps K₂ (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hD) fun s₃ m₃ => ?_
  refine wp_orS rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  refine wp_subS rfl fun s₆ u₆ cf₆ => ?_
  refine wp_sbbS rfl cf₆ fun t u₇ _ => WP.block_nil ?_
  have hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (q.setWidth 64)).setWidth 32) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₇.gpr, sbb_mask]
    simp only [u₅.gpr, u₄.gpr, m₃.gpr, u₂.gpr, u₁.mem, reduceCtorEq, ite_false, decide_eq_true_eq, tag_key]
  · rw [hm, Mem.readW_writeW_self32]
  · exact K₂.trans ((m₃.keeps _).trans ((u₄.keeps.mono (by simp)).trans
      ((u₅.keeps.mono (by simp)).trans ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86
