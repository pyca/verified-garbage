module

public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame

/-!
# RSASSA-PSS verification with a precomputed public key on x86-64: the
precondition

`Pre` is `VPre`, which names the facts of `verifyK.pre`, the cache `pre` of
the public key's values among them; `preR` and `argsR` are its region and the
stack arguments'.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (tsH tsG : List FnTable)

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

/-- All ten stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 80⟩

/-- The precondition, by name. -/
abbrev Pre (s : State) : Prop := VPre tsH tsG s

variable {tsH tsG}

theorem Pre.toVPre {s : State} (h : Pre tsH tsG s) : VPre tsH tsG s := h

theorem pre_of {s : State} (h : (verifyK tsH tsG).pre s) : Pre tsH tsG s := VPre.of tsH tsG h

theorem Pre.argsScr {s : State} (h : Pre tsH tsG s) :
    (argsR s).Disjoint (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) := h.dsa.symm

theorem Pre.argsStack {s : State} (h : Pre tsH tsG s) : (argsR s).Disjoint (vstkR s) := h.dKa.symm

theorem Pre.preScr {s : State} (h : Pre tsH tsG s) :
    (preR s).Disjoint (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) := h.dsp.symm

theorem Pre.preStack {s : State} (h : Pre tsH tsG s) : (preR s).Disjoint (vstkR s) := h.dKp.symm

end VG.Proof.RsaPss.X86_64.Pc
