module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBody
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-!
# Four of the blocks after the last group

What the loop over four of the blocks after the last group at a time
(`StitchZH.remQuadD`, `RemQuadD.lean`) shares: the registers it writes
(`quadRegs`), the lanes of a 64-byte load (`zlane_ld`), and the step to the
next four (`remNext4_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchZH (remNext4)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx)
open VG.Proof.Gcm.X86_64.StitchZ (restZ ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane zmm_lane blockAt_writeW_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- The registers `remQuad` writes. -/
abbrev quadRegs : List XReg := [.xmm7, .xmm12, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11]

theorem zlane_ld (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)).zlane d l =
      s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) hl]
  exact load512_lane _ _ hl

/-- `add r10, 64`, `sub r9, 4`, `cmp r9, 16`. -/
theorem remNext4_ok (s : State) {m : Nat} (h4 : 4 ≤ m) (h15 : m ≤ 15) {i : Nat}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * i)) :
    WP isa (.block remNext4) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * (i + 4)) ∧ s'.gpr .r9 = BitVec.ofNat 64 (16 + (m - 4)) ∧
      s'.zf = some (decide (m = 4)) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e4 : BitVec.signExtend 64 (4 : BitVec 32) = 4 := by decide
  have a10 : BitVec.ofNat 64 (16 * i) + 64 = BitVec.ofNat 64 (16 * (i + 4)) := by
    rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add]; congr 1
  have s9 : BitVec.ofNat 64 (16 + m) - 4 = BitVec.ofNat 64 (16 + (m - 4)) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have z9 : (BitVec.ofNat 64 (16 + (m - 4)) - 16 == 0) = decide (m = 4) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    by_cases h : m = 4
    · subst h; rfl
    · have : BitVec.ofNat 64 (16 + (m - 4) - 16) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 + (m - 4) - 16 < 2 ^ 64 by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  apply WP.of_runBlock
  simp only [remNext4, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e64, e16, e4, h9, h10, a10, s9, z9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl,
    trivial, trivial, trivial⟩

end VG.Proof.Gcm.X86_64.StitchZH
