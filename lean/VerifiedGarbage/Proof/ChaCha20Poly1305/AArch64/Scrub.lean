module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut

/-!
# ChaCha20-Poly1305 on AArch64, without secret residue

The postconditions of `vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather` read
the memory on return only within their buffers (`Proof/ChaCha20Poly1305/Scratch.lean`,
`Proof/ChaCha20Poly1305/OpenToScratch.lean`, which RISC-V uses too; given
the precondition for `open_to`): each as it is emitted
(`Impl.ChaCha20Poly1305.AArch64.Fn`), over any implementation of ChaCha20's
keystream, returns with every register it may leave secret cleared and its
whole stack zeroed (`Fn`, below). Their code wipes only the first
768 bytes of its working space, and keeps keystream above them.

`seal_gather` calls `seal` as it is exported (`sealFnWhole`), cleanup
included, rather than a copy of its code without it.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305 VG.Impl.Scrub.AArch64

theorem sealOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (sealContract abi W) W (sealSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := sealSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.ChaCha20Poly1305.sealPost_out 64)

theorem openOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (openZeroContract abi W) W (openSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := openSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.ChaCha20Poly1305.openZeroPost_out 64)

theorem openToOk (W : Nat) :
    ScrubAllOk (openToContract abi W) W (openToSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := openToSig) (Proof.ChaCha20Poly1305.openToPost_out 64)

theorem gatherOk (W : Nat) :
    ScrubAllOk (sealGatherContract abi W) W (sealGatherSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := sealGatherSig) (Proof.ChaCha20Poly1305.sealGatherPost_out 64)

/-! ## What the cleanup needs of the code

Of `seal`, `open` and `open_to` in their frames with the stream `v`, it is
what `v` proves where it is defined (`XorImpl.sealSide`, `openSide`,
`openToSide`); of `seal_gather`, its own instructions' and `seal`'s. -/

theorem seal_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.sealBody v.callee v.stitched) 1280 0
      (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) [] = true := by
  have h := v.sealSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

theorem open_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.openBody v.callee v.stitched) 1312 32
      (Impl.ChaCha20Poly1305.AArch64.Fn.openOwn.union v.callee.clear) [] = true := by
  have h := v.openSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

theorem openTo_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.openToBody v.callee v.stitched) 1328 32
      (Impl.ChaCha20Poly1305.AArch64.Fn.openOwn.union v.callee.clear) [] = true := by
  have h := v.openToSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

/-- `seal_gather`'s own instructions, with nothing in `seal`'s place, write
only the registers `Impl/` states (`Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn`). -/
private theorem gather_own :
    calleeSide (Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather "" (.block []))
      Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn = true := by
  kernel_rfl

end VG.Proof.ChaCha20Poly1305.AArch64.Scrub

/-! ## The functions

Of each function `Artifacts/ChaCha20Poly1305/AArch64.lean` registers, with
the stream `v`: the code that is emitted (`Impl.ChaCha20Poly1305.AArch64.Fn`)
meets the function's contract in constant time and returns without secret
residue. -/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Fn

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305

theorem sealWhole (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched)
      (sealContract abi 1280) 0 :=
  verifiedScrubbedAll (api := sealApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.sealBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v }
    _ (Scrub.sealOk 1280) (Scrub.seal_side v)

theorem openZero (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.openZero v.callee v.stitched)
      (openZeroContract abi 1312) 32 :=
  verifiedScrubbedAll (api := openZeroApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.openBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.open_framed v }
    _ (Scrub.openOk 1312) (Scrub.open_side v)

theorem openTo (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.openTo v.callee v.stitched)
      (openToContract abi 1328) 32 :=
  verifiedScrubbedAll (api := openToApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.openToBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.openTo_framed v }
    _ (Scrub.openToOk 1328) (Scrub.openTo_side v)

end VG.Proof.ChaCha20Poly1305.AArch64.Fn

/-! ## `seal_gather`, calling `seal` as exported -/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305 VG.Impl.Scrub.AArch64

/-- A cleanup's clears of the registers of `cl` write no register `cl`
leaves, and no PSTATE.DIT. -/
theorem clears_side (cl : Clear) (hwf : wfB cl = true) :
    calleeSide (.block (clearsOf cl)) cl = true := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true] at hwf
  obtain ⟨⟨hg, hv⟩, hh⟩ := hwf
  simp only [calleeSide, sideAll, Code.allInstrs_eq, instrs, List.all_eq_true]
  intro i hi
  simp only [clearsOf, List.mem_append, List.mem_map, List.mem_singleton] at hi
  rcases hi with ((⟨r, hr, rfl⟩ | ⟨w, hw, rfl⟩) | rfl) | ⟨w, hw, rfl⟩
  · have hk : (RegSet.ofList (keptG cl)).mem r = false := Bool.eq_false_iff.mpr fun h => by
      have := RegSet.mem_ofList.mp h
      simp [keptG, List.mem_filter, hr] at this
    have e1 : (Instr.movz .x r 0 0).writesDit = false := rfl
    have e2 : dstOf (Instr.movz .x r 0 0) = some r := rfl
    have e3 : vdstOf (Instr.movz .x r 0 0) = none := rfl
    simp only [sideI, keeps, vkeeps, e1, e2, e3, hk]; rfl
  · have hk : (RegSet.ofList (keptV cl)).mem w = false := Bool.eq_false_iff.mpr fun h => by
      have := RegSet.mem_ofList.mp h
      have ha := hv w hw
      simp [keptV, List.mem_filter, hw] at this
      have hx := this.1
      revert ha hx; cases w <;> decide
    have e1 : (Instr.vop (.movi0 w)).writesDit = false := rfl
    have e2 : dstOf (Instr.vop (.movi0 w)) = none := rfl
    have e3 : vdstOf (Instr.vop (.movi0 w)) = some w := rfl
    simp only [sideI, keeps, vkeeps, e1, e2, e3, hk]; rfl
  · rfl
  · have hk : (RegSet.ofList (keptV cl)).mem w = false := Bool.eq_false_iff.mpr fun h => by
      have := RegSet.mem_ofList.mp h
      have ha := hh w hw
      simp [keptV, List.mem_filter, hw] at this
      have hx := this.1
      revert ha hx; cases w <;> decide
    have e1 : (Instr.vop (.ins .d2 w 1 .x1)).writesDit = false := rfl
    have e2 : dstOf (Instr.vop (.ins .d2 w 1 .x1)) = none := rfl
    have e3 : vdstOf (Instr.vop (.ins .d2 w 1 .x1)) = some w := rfl
    simp only [sideI, keeps, vkeeps, e1, e2, e3, hk]; rfl

/-- `seal` as exported: its code, its clears, the result's bits, then the
stack zeroed. -/
private theorem sealWhole_eq (c : Impl.ChaCha20.AArch64.XorCallee) (st : Bool) :
    Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole c st =
      .seq (.seq (.seq (Impl.ChaCha20Poly1305.AArch64.Fn.sealBody c st)
        (.block (clearsOf (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union c.clear))))
        (.block (retFix 0))) (scrubTailG 1280 (List.range (1280 / 16))) := rfl

/-- `seal`'s cleanup but its clears: the result's bits, then the stack
zeroed, which write only registers `seal` clears. -/
private theorem tail_own :
    calleeSide (.seq (.block (retFix 0)) (scrubTailG 1280 (List.range (1280 / 16))))
      Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn = true := by
  kernel_rfl

/-- `seal` as exported, cleanup included, writes only the registers it
clears. -/
theorem sealWhole_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    calleeSide (Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched)
      (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) = true := by
  have h := v.sealSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := sideAll_union_left (b := v.callee.clear) tail_own
  have hc := clears_side (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) (wfB_union _ _)
  rw [sealWhole_eq]
  simp only [calleeSide, sideAll, Bool.and_eq_true] at ht hc h ⊢
  exact ⟨⟨⟨h.1, hc⟩, ht.1⟩, ht.2⟩

/-- The frames of `seal` as exported fit in its 1280 bytes. -/
theorem sealWhole_depth (v : Proof.ChaCha20.AArch64.XorImpl) :
    16 * (Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched).aarch64Depth ≤ 1280 := by
  have h := v.sealSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [sealWhole_eq]
  simp only [scrubTailG, Code.aarch64Depth, Instr.frameUnits, ← Nat.mul_max_mul_left, Nat.max_le, h.2,
    true_and]
  decide

/-- `vg_chacha20_poly1305_seal` over the backend `v`, as it is exported,
cleanup included: what `seal_gather` calls. -/
def sealFnWhole (v : Proof.ChaCha20.AArch64.XorImpl) : Proof.ChaCha20Poly1305.AArch64.Gather.SealFn where
  name := "vg_chacha20_poly1305_seal" ++ v.callee.suffix
  code := Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched
  verified := (Proof.ChaCha20Poly1305.AArch64.Fn.sealWhole v).verified
  depth := sealWhole_depth v

theorem gather_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody v.callee v.stitched) 1296 0
      (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) [] = true := by
  have hs := sealWhole_side v
  have hd := sealWhole_depth v
  have h0 := sideAll_union_left (b := v.callee.clear) gather_own
  refine scrubSide_union (by decide) ?_ (by decide) ?_ (by decide)
  · have hg : Impl.AesGcm.AArch64.SealGather.gather.aarch64Depth = 0 := by decide
    simp only [Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody,
      Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather, Code.aarch64Depth, Instr.frameUnits, hg,
      Nat.zero_max, Nat.max_zero, Nat.reduceDiv]
    generalize (Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched).aarch64Depth = d at hd ⊢
    exact Nat.le_trans (Nat.mul_add 16 _ 1 ▸ Nat.add_le_add_right hd 16) (by decide)
  · simp only [calleeSide, Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody,
      Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather, sideAll, Bool.and_eq_true] at h0 hs ⊢
    simp only [h0, hs, and_self]

end VG.Proof.ChaCha20Poly1305.AArch64.Scrub

namespace VG.Proof.ChaCha20Poly1305.AArch64.Fn

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305

theorem sealGather (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.sealGather v.callee v.stitched)
      (sealGatherContract abi 1296) 0 :=
  verifiedScrubbedAll (api := sealGatherApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified (Scrub.sealFnWhole v) }
    _ (Scrub.gatherOk 1296) (Scrub.gather_side v)

end VG.Proof.ChaCha20Poly1305.AArch64.Fn
