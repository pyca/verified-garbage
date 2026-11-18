module

public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Verified
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming AES-CMAC on AArch64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): 2304 bytes for `init` and `finish`, and for
`absorb` 64 more than the chaining implementation it calls needs. Their code uses no other stack: their calls keep
the return address in `x30`, which they save in the working space.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre64 : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 64).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSat_pre2240 : ∃ s, (Spec.Cmac.aesAbsorbContract AArch64.abi 2240).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, AArch64.abi, AArch64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract AArch64.abi 2304).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, AArch64.abi, AArch64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (init_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

/-- `vg_cmac_aes_absorb`, in a frame of `64 + n` bytes for a chaining
implementation that needs `n` (`UpdateImpl.scratch`): its saved registers
and the working space of the function it calls. -/
theorem absorb_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (64 + v.scratch) .x5 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract AArch64.abi (64 + v.scratch)) := by
  obtain hv := absorb_verified v
  rcases v.scratch_ok with h | h <;> simp only [h, Nat.reduceAdd, Nat.reduceDiv] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
      (n := 8) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 64) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre64
  · exact AArch64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
      (n := 280) (pre := Spec.Cmac.aesAbsorbPre AArch64.abi.ptrBits)
      (post := Spec.Cmac.aesAbsorbPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
      (bytes := 2240) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre2240

theorem finish_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2304 .x4 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract AArch64.abi 2304) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 2304) (finish_verified v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacAes.Stream.finishPostOut_local _ vs m m₁ m₂ r hl) finishFrameSat_pre

/-! ## Without secret residue -/

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on a
region of at least `n` bytes there. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

/-- `vg_cmac_aes_absorb`'s postcondition reads the memory on return only
within the state's 304 bytes (`repr_congr_304`, as x86-64's
`Stream/X86_64/Scrub.lean` proves it), so it returns with every register it
may leave secret cleared and its whole frame zeroed
(`ScrubAll.withScrubAll`). -/
theorem absorbOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesAbsorbContract abi W) W (Spec.Cmac.aesAbsorbSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Cmac.aesAbsorbSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, _, _, _, _], _ =>
      simp only [Spec.Cmac.aesAbsorbSig, Sig.bufs, List.mem_cons, forall_eq_or_imp] at hb
      intro key msg hr hro hc hlt
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_of hb.1 (by decide)) (h key msg hr hro hc hlt)

/-- `absorbOk` for the frame of `absorb_framed`. -/
theorem absorbOk_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ScrubAll.ScrubAllOk (Spec.Cmac.aesAbsorbContract abi (64 + v.scratch)) (64 + v.scratch)
      (Spec.Cmac.aesAbsorbSig.retBits abi.ptrBits) :=
  absorbOk _ (by omega_using [])

/-- `vg_cmac_aes_absorb` in its frame (`absorb_framed`), scrubbed whole
(`ScrubAll.withScrubAll`) when the chaining implementation it calls needs no
working space, so that the frame is 64 bytes. With one that needs some,
zeroing it would cost more than the budget (zeroing 2240 bytes, about 20 ns,
next to about 550 ns for 64 bytes of scalar AES): that function stays on
`ci/residue_allowlist.txt`. -/
def absorbReg (v : Proof.CmacAes.AArch64.UpdateImpl) : Registration Spec.Cmac.aesAbsorbApi AArch64.target :=
  let r : Registration Spec.Cmac.aesAbsorbApi AArch64.target :=
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch (64 + v.scratch) .x5 (absorb v.callee)
      verified := absorb_framed v
      consts := []
      stack := 64 + v.scratch }
  if v.scratch = 0 then ScrubAll.withScrubAll r (absorbOk_framed v) else r

end VG.Proof.CmacAes.Stream.AArch64
