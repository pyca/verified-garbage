module

public import VerifiedGarbage.Proof.MillerRabin.X86.Entry
public import VerifiedGarbage.Proof.MillerRabin.X86.OperandFrame

/-! # Return the result and restore registers with the shared spill framework -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

theorem finish_ok {s g : State} {base : Addr} {bytes w : Nat} {F : Bool}
    (ctx : ProtectedContext s base bytes) (hf : arrAt w 28 ≤ bytes)
    (saved : Spill.Saved s.mem (off (byteAddr (s.gpr .esp))) g.gpr savedRegisters)
    (sp : s.gpr .esp = g.gpr .esp) (flag : w32 s.mem base sF = F.toNat) :
    WP isa (.block finish) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = g.gpr r) ∧ t.gpr .eax = BitVec.ofNat 32 F.toNat ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have word := readW_of_w32 (by cases F <;> decide : F.toNat < 2 ^ 32) flag
  unfold finish
  refine wp_movS (by rw [readSrc_sc ctx.ws (Nat.le_trans (by decide : sF + 4 ≤ 256) hdrFit), word]) fun u U _ => ?_
  have ctxU := ctx.of_keeps U.keeps
  have slotsFit : Spill.Fits VG.Impl.MillerRabin.X86.frameBytes savedRegisters := by decide
  change WP isa (.block (Spill.restoreCode .esp savedRegisters ++ [])) u _
  refine Spill.restore_ofNat_ok (g := g.gpr) savedRegisters slotsFit ctxU.stackFit (by decide) (fun p hp => ?_) ?_ fun t R =>
    WP.block_nil ?_
  · obtain ⟨r, hr, hc⟩ := VG.CallLay.inRegions_sub ctxU.stack (slotsFit.1 p hp) (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [U.mem, U.other .esp (by decide)]
    exact saved
  · refine ⟨R.abi (by decide) (by decide) ((U.other .esp (by decide)).trans sp), ?_,
      R.mem.trans U.mem, R.rd.trans U.rd, R.wr.trans U.wr⟩
    rw [R.other .eax (by decide), U.gpr]

end VG.Proof.MillerRabin.X86
