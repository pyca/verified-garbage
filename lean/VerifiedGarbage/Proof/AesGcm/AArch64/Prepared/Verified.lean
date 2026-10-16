module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Init
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Prepared.Init
public import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
meta import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.AArch64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.InitCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64: `vg_aes_gcm_init_prepared` is `Verified`

Untrusted: everything here is checked by Lean. Correctness
(`initPrepared_wp`, for the algebra `PrepPow`), constant time (`initWith_ct`:
the powers' loads, stores and loop depend only on the context's address), a
state satisfying the precondition, and the shared contract, with the working
space in a register (`initPreparedScratchContract`) and then on the stack.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)

theorem initPrepared_keepsV (v : GcmImpl) :
    (Impl.AesGcm.AArch64.Prepared.init v.callees).allInstrs keepsV = true := by
  simp only [Impl.AesGcm.AArch64.Prepared.init, initWith, Impl.AesGcm.AArch64.Prepared.powers, ctrCall,
    GcmImpl.callees, Code.allInstrs, v.ctr.keepsV, v.key.keepsV]
  decide +kernel

theorem initPrepared_correct (v : GcmImpl) (hP : PrepPow) (s : State) (hs : initPreparedAArch64.pre s) :
    ∃ t s', Exec isa (Impl.AesGcm.AArch64.Prepared.init v.callees) s t s' ∧ abiPreserved s s' ∧
      initPreparedAArch64.post s s' :=
  WP.withPreservedV (initPrepared_wp v hP hs) (initPrepared_keepsV v)

theorem initPrepared_ct (v : GcmImpl) :
    ConstantTime isa initPreparedAArch64.pre initPreparedAArch64.pub
      (Impl.AesGcm.AArch64.Prepared.init v.callees) :=
  initWith_ct v _ (cl := 1024) (by decide) (fun s h => by
      simp only [initPreparedAArch64] at h
      obtain ⟨hrd, hwr, d_kc, d_ks, d_cs, wc, -, hL⟩ := h
      exact ⟨hrd, hwr, d_kc, d_ks, d_cs, by omega, hL⟩)
    ⟨_, by taint_decide⟩

def initPreparedSat : State := { initSat with wr := [⟨0x2000, 1024⟩, ⟨0x4000, 2560⟩] }

theorem initPrepared_verified (v : GcmImpl) (hP : PrepPow) :
    Verified AArch64.target (Impl.AesGcm.AArch64.Prepared.init v.callees)
      (Proof.AesGcm.initPreparedScratchContract AArch64.abi) :=
  Verified.of_correct (initPrepared_correct v hP) (initPrepared_ct v) (by
    sig_implies [Proof.AesGcm.initPreparedScratchContract, Proof.AesGcm.initPrecomputedScratchSig,
      Spec.Gcm.initPre, Spec.Gcm.initPreparedPost, initPreparedAArch64, initAArch64, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [initPreparedSat, initSat] using initPreparedSat)

/-- A state satisfying `vg_aes_gcm_init_prepared`'s precondition, without the
working space. -/
def initPreparedFrameSat : State := { initSat with wr := [⟨0x2000, 1024⟩] }

theorem initPreparedFrameSat_pre : ∃ s, (Spec.Gcm.initPreparedContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initPreparedContract, Spec.Gcm.initPreparedSig, Spec.Gcm.initPrecomputedSig,
    Spec.Gcm.initPre, Spec.Gcm.initPreparedPost, AArch64.abi, AArch64.argRegs]
    [initPreparedFrameSat, initSat] using initPreparedFrameSat

theorem initPrepared_framed (v : GcmImpl) (hP : PrepPow) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (Impl.AesGcm.AArch64.Prepared.init v.callees))
      (Spec.Gcm.initPreparedContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.initPreparedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre AArch64.abi.ptrBits) (post := Spec.Gcm.initPreparedPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (initPrepared_verified v hP) (by decide) (by decide)
    initPreparedFrameSat_pre

end VG.Proof.AesGcm.AArch64
