module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# `vg_ed448_verify` on PPC64LE, verified

The code meets `verifyContract` with the frame as one more argument
(`Sig.scratchContract`) and 48 bytes of stack for the callees' frames (the
proof against the contract's facts by register, `verC`), and, in a frame of
304 bytes (`Verified.stackScratchL`), the contract itself. The contract
declares the inputs public; the proof of constant time needs only the
registers (`verifyMessage_ct`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Spec.Ed448 (bytesAt)

/-- The contract by register: `VerPre`, as the contract's facts. -/
def verC : Contract isa where
  pre s :=
    s.rd = [vpkR s, vcxR s, vmsR s, vsgR s] ∧ s.wr = [vscR s, vfR s] ∧
      (vscR s).Disjoint (vpkR s) ∧ (vscR s).Disjoint (vcxR s) ∧ (vscR s).Disjoint (vmsR s) ∧
      (vscR s).Disjoint (vsgR s) ∧ (vscR s).Disjoint (vfR s) ∧
      (vfR s).Disjoint (vpkR s) ∧ (vfR s).Disjoint (vcxR s) ∧ (vfR s).Disjoint (vmsR s) ∧
      (vfR s).Disjoint (vsgR s) ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint (vpkR s) ∧ (below s.sp 48).Disjoint (vcxR s) ∧
      (below s.sp 48).Disjoint (vmsR s) ∧ (below s.sp 48).Disjoint (vsgR s) ∧
      (below s.sp 48).Disjoint (vscR s) ∧ (below s.sp 48).Disjoint (vfR s)
  post s s' := (s'.gpr .r3).setWidth 32 = verResult s
  pub s₁ s₂ := VPub s₁ s₂ ∧
    (vpkB s₁ ++ vctxB s₁ ++ vmsgB s₁ ++ vsigB s₁).map (·.toNat) =
      (vpkB s₂ ++ vctxB s₂ ++ vmsgB s₂ ++ vsigB s₂).map (·.toNat)

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s :=
  let ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩

theorem ver_ok (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := verifyMessage_wp hR hV (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem ver_ct (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    ConstantTime isa verC.pre verC.pub verifyMessage :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    verifyMessage_ct hR hV s₁ s₂ t₁ t₂ s₁' s₂' (verC_pre h₁) (verC_pre h₂) hp.1 e₁ e₂

/-- A state satisfying the precondition. -/
def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | .r9 => 0x5000 | .r10 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩]
  wr := [⟨0x5000, 8192⟩, ⟨0x8000, 272⟩]

theorem verify_verified (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    Verified PPC64LE.target verifyMessage (Sig.scratchContract PPC64LE.abi Spec.Ed448.verifySig "frame" .u8 272
      (Curry.const (fun _ => True) _) (Proof.Ed448.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
      (some (Proof.Ed448.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct (ver_ok hR hV) (ver_ct hR hV) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.verifyPost, Proof.Ed448.WholeLocal.verifyLeak, verC, VPub,
      verResult, vpkR, vcxR, vmsR, vsgR, vscR, vfR, vpkB, vctxB, vmsgB, vsigB, PPC64LE.abi, PPC64LE.argRegs]
      [verSat] using verSat)

/-- A state satisfying `vg_ed448_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSat with wr := [⟨0x5000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed448.verifyContract PPC64LE.abi (48 + 304)).pre s := by
  implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs] [verFrameSat, verSat] using verFrameSat

/-- In its frame of 304 bytes. -/
theorem verify_framed (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) :
    Verified PPC64LE.target verifyCode (Spec.Ed448.verifyContract PPC64LE.abi (48 + 304)) :=
  Verified.stackScratchL (sig := Spec.Ed448.verifySig) (nm := "frame") (e := .u8) (n := 272)
    (post := Proof.Ed448.WholeLocal.verifyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 304)
    (leak := some (Proof.Ed448.WholeLocal.verifyLeak PPC64LE.abi.ptrBits)) (verify_verified hR hV) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Ed448.WholeLocal.verifyPost_local _) (Proof.Ed448.WholeLocal.verifyLeak_local _) verFrameSat_pre

end VG.Proof.Ed448.PPC64LE.Whole
