import VerifiedGarbage.Proof.AesSiv.X86_64.S2vAd
import VerifiedGarbage.Proof.AesSiv.X86_64.Finish
import VerifiedGarbage.Proof.AesSiv.X86_64.CtrCT
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-SIV on x86-64: the counter

`encrypt` and `decrypt` set the counter `Q` at `W + 64` from an IV at `W`
(`counter_ok`): the IV's second word with bit 7 of its bytes 0 and 4 cleared
(`counter_words`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem counter_ok (h : Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 (cntOff + 8)) (s.mem.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  have w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [counter, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, h15, r₀, r₈, w₀, w₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := 0 + 8) (n := 8) (e := cntOff) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), k0]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The counter `Q` of the IV `v`, as `ctr` takes it. -/
theorem counter_cnt (m : Mem) (W : Addr) :
    ∃ hi lo : BitVec 64,
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt m W 16)) := by
  refine ⟨bswap64 (m.readW (W + BitVec.ofNat 64 0) 64), bswap64 (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask),
    ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [← Proof.Cmac.ofBytes_toBytes (bswap64 _ ++ bswap64 _), ← VG.Proof.CmacAes.X86_64.le8_bswap,
      Proof.Gcm.X86_64.bswap64_bswap64, Proof.Gcm.X86_64.bswap64_bswap64, counter_words, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, k0, ← Proof.Cmac.bytesAt_split]

end VG.Proof.AesSiv.X86_64
