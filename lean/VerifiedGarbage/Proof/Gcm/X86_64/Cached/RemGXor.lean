module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemQuadK
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemGLanes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-!
# The blocks after the last group, added to their keystream in registers

`xorG_ok`: `StitchZH.xorG src rs j` adds the data at `src + 64 j` … to the
keystream registers `rs` and stores them to `rdx + 64 j` …, the last
register through the mask of its `c` blocks: each block stored is the data
block and the keystream added, and is what its register's lane, byte-
reversed, holds, which the hash then takes.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (xorG)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane blockAt_writeW_lane load512_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.ofInt_natCast]

/-- A register XORed with the 64 bytes at `src + d` and stored to `rdx + d`. -/
theorem xor1G_ok (src : Reg) (b : XReg) (d : Nat) (s : State) (hb : b ≠ .xmm13)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 64)
    (hinD : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 d) 64) :
    WP isa (.block [.vmovdqu32Load .xmm13 (at_ src d), .zop (.zbin .vpxord b b .xmm13),
        .vmovdqu32Store (at_ .rdx d) b]) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 d) v) ∧
      (∀ l < 4, blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) =
        blockAt s.mem (s.gpr src + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) ^^^
          XBinOp.eval .pshufb (s.zlane b l) revMask) ∧
      (∀ l < 4, XBinOp.eval .pshufb (s'.zlane b l) revMask =
        blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm13 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let a := s.gpr .rdx + BitVec.ofNat 64 d
  let as := s.gpr src + BitVec.ofNat 64 d
  let v := s.mem.readW as 512
  let s₁ := setZv s .xmm13 v
  let s₂ := (ZOp.zbin .vpxord b b .xmm13).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane .xmm13 l = s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [zlane_setZv _ _ _ hl]; exact load512_lane _ _ hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at', hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ .rdx d) b) s₂ = some (s₂.setMem (s.mem.writeW a (s₂.zmm b))) := by
    simp only [isa, exec, State.store512_eq, ea_at', s₂, s₁, ZOp.exec_gpr,
      State.setZ_gpr, ZOp.exec_wr, State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hinD, ite_true, a]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane b l = s.zlane b l ^^^ s.mem.readW (as + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl]
      rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
      simp only [hb, ite_false, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  have bD : ∀ l < 4, blockAt (s.mem.writeW a (s₂.zmm b)) (a + BitVec.ofNat 64 (16 * l)) =
      XBinOp.eval .pshufb (s₂.zlane b l) revMask := fun l hl => by
    rw [blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁],
    fun r h1 h2 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [bD l hl, z₂ l hl, pshufb_rev_xor, BitVec.xor_comm, ← blockAt_eq]
  · simp only [State.setMem_mem, State.setMem_zlane]
    exact (bD l hl).symm
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1, h2]

end VG.Proof.Gcm.X86_64.StitchZH
