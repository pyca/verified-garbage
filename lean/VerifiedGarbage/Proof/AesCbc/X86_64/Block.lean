import VerifiedGarbage.Proof.AesCbc.X86_64.Call
import VerifiedGarbage.Proof.AesCbc.Mem

/-!
# AES-CBC on x86-64: the code between the calls

The straight-line pieces of `encBody` and `decBody`, run once each:
`xorInto .r13 .r12` (the block at `r13` XORed with the chaining value) and
`copy` (a block copied, as two words), with their memories as explicit
writes (`xorMem`, `copyMem`, `Proof/AesCbc/Mem.lean`).
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-! ## Runs -/

/-- The block at `r13` XORed with the one at `r12`. -/
theorem xorInto_ok (s : State) {P Q : Addr} (hp : s.gpr .r13 = P) (hq : s.gpr .r12 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (xorInto .r13 .r12) s = some s' ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, xorInto, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, hp, hq, BitVec.add_zero, rp, rp8, rq, rq8, wp, wp8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

/-- The block at `src + s₀` copied to `dst + d`, given as `P` and `Q`. -/
theorem copy_ok (s : State) {dst src : Reg} {d e : Nat} {P Q : Addr}
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (hsrc : src ≠ .rax) (hdst : dst ≠ .rax) :
    ∃ s', runBlock isa (copy dst d src e) s = some s' ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = copyMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, copy, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, hsrc, hdst, hp, hp8, hq, hq8, rq, rq8, wp, wp8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

end VG.Proof.AesCbc.X86_64
