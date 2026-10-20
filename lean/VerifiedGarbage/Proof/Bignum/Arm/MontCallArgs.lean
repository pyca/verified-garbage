module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Arguments for one shared ARMv7 Montgomery call -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem montCallArgs_ok (s : State) {base : BitVec 32} {size o a b : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (ptr : s.gpr .r0 = base)
    (_spFits : s.sp.toNat + 8 ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr s.sp) 4)
    (ho : o < 8) (ha : a < 8) (hb : b < 8) :
    WP isa (.block (MontCall.opArgs o a b)) s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = BitVec.ofNat 32 o ∧ t.gpr .r3 = BitVec.ofNat 32 a ∧
      t.mem = s.mem.writeW (State.addr s.sp) (BitVec.ofNat 32 b) ∧
      Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem ∧ Rest [.r1, .r2, .r3, .r12, .lr] s t := by
  have immediate : ∀ j < 8, encodable (BitVec.ofNat 32 j) = true := by decide
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 48)) 4 := by
    rw [ptr, addr_add (by have := ws.nowrap; omega)]
    exact ws.read fit
  let m := s.mem.writeW (State.addr s.sp) (BitVec.ofNat 32 b)
  let u := { (((s.setReg .r2 (BitVec.ofNat 32 o)).setReg .r3 (BitVec.ofNat 32 a)).setReg
    .lr (BitVec.ofNat 32 b)).setReg .r12 s.sp with mem := m }
  let t := u.setReg .r1 ((m.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 48)) 32 + 6) <<< 3)
  refine WP.of_runBlock ⟨t, ?_, ?_⟩
  · simp only [MontCall.opArgs, runBlock_cons, runStep_some, isa, exec, Op2.eval,
      immediate o ho, immediate a ha, immediate b hb,
      show encodable (6 : BitVec 32) = true from rfl,
      show (0 < 256) = True by decide, show (0 < 4096) = True by decide,
      show (48 < 4096) = True by decide, show (1 ≤ 3 ∧ 3 ≤ 31) = True by decide,
      ↓reduceIte, State.store32, State.load32, gpr_setReg, reduceCtorEq,
      sp_setReg, mem_setReg, rd_setReg, wr_setReg, write, read,
      BitVec.add_zero, Option.map_some, runBlock_nil]
    congr 1
    simp only [t, u, m, State.setReg]
    congr 1
    funext r
    cases r <;> rfl
  · refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [t, u, gpr_setReg, reduceCtorEq, ↓reduceIte]; exact ptr
    · simp only [t, u, gpr_setReg, reduceCtorEq, ↓reduceIte]
    · simp only [t, u, gpr_setReg, reduceCtorEq, ↓reduceIte]
    · exact (Frame.refl _ s.mem).writeW (by simp) (BitVec.ofNat 32 b) (Region.contains_self _ _)
    · refine ⟨?_, rfl, rfl, rfl⟩
      intro r hr
      simp only [List.mem_cons, not_or] at hr
      simp only [t, u, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2, ↓reduceIte]

end VG.Proof.Bignum.Arm
