module
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# AES-GCM-SIV's interleaved loop: the end of the setup

`setupC_ok`: `Y`, in GHASH's order, the counter pair (the counter block at
`rdx`, as it is, and with 1 added to its first word), the increment, the
last round key's address, the counter block's address in `rax` and the data's
in `rdx`. The powers before it are stored as AES-GCM's
(`Proof.Gcm.X86_64.Stitch.storesK_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.AesGcmSiv.X86_64Stitch (setupC)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Gcm.X86_64.Stitch (in_rdwr)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (blockAt)

theorem setupC_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      s'.lane .xmm14 0 = s.mem.readW (s.gpr .rdx) 128 ∧
      s'.lane .xmm14 1 = XBinOp.eval .paddd (s.mem.readW (s.gpr .rdx) 128) ((0 : BitVec 64) ++ BitVec.ofNat 64 1) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, reduceVOpExec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, ?_, ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; rfl
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

end VG.Proof.AesGcmSiv.X86_64.Stitch
