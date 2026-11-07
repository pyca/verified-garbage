module

public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Fn
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.CT
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES-GCM decryption out of place, by a copy, x86: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_open_to`, with the 2688 bytes of stack below the stack pointer
that its frame and its call use (`Proof.AesGcm.openToRoundsContract`),
implies the one the proof is written against (`toK`, `to_implies`), and so
the code, calling an instance of `vg_aes_gcm_open` by its shared contract
(`openFn`), is `Verified` against it (`openTo_verified`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.OpenTo

open VG VG.X86 VG.Impl.AesGcm.X86.OpenTo
open VG.Proof.AesGcm.X86.Gather (sw32)

theorem openTo_correct (F : OpenFn) (s : State) (hs : toK.pre s) :
    ∃ t s', Exec isa (openTo F.name F.code) s t s' ∧ abiPreserved s s' ∧ toK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := openTo_wp F hs
  exact ⟨t, s', he, ha, hp⟩

theorem toPre_of_spec {s : State} (h : (Proof.AesGcm.openToRoundsContract X86.abi 2688).pre s) : ToPre s := by
  sig_pre [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64] at h
  sig_split h
  rename_i w₁ w₂ rd wr kd ka nd na ad aa sd sa dt da ta ek en ea es ed et earg bk bn ba bs bd bt barg ok on oa os od
    ot hR
  rw [h] at wr kd nd ad sd dt da ed bd od
  exact ⟨w₁, w₂, rd, wr, kd, nd, ad, sd, dt, da, ed, bk, bn, ba, bs, bd, bt, ok, on, oa, os, od, ot, hR⟩

theorem toPost_of {s s' : State} (h : toPost s s') :
    (Proof.AesGcm.openToRoundsContract X86.abi 2688).post s s' := by
  sig_post [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Proof.AesGcm.openToRoundsPost, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceMul, sw32, toNat_w64]
  intro _
  rw [ret32_eq]
  exact h

theorem toPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.openToRoundsContract X86.abi 2688).pub s₁ s₂) :
    toPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToLeak, X86.abi, argVal,
    ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd,
    Nat.reduceMul, sw32, toNat_w64] at hp
  obtain ⟨qsp, ql, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  refine ⟨qsp, ql, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 by
    omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]

/-- A state satisfying the precondition of `vg_aes_gcm_open_to`: no nonce,
additional data, text or tag; its twelve argument slots at `0x8004`. -/
def toSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else 0
  rd := [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
  wr := [⟨0, 0⟩, ⟨0x8004, 48⟩]

theorem toSat_pre : ∃ s, (Proof.AesGcm.openToRoundsContract X86.abi 2688).pre s := by
  implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [toSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using toSat

theorem to_implies : toK.Implies (Proof.AesGcm.openToRoundsContract X86.abi 2688) :=
  ⟨fun _ h => toPre_of_spec h, fun _ _ _ h => toPost_of h, fun _ _ _ _ h => toPub_of h, toSat_pre⟩

theorem openTo_verified (F : OpenFn) :
    Verified X86.target (openTo F.name F.code) (Proof.AesGcm.openToRoundsContract X86.abi 2688) :=
  Verified.of_correct (k := toK) (openTo_correct F) (openTo_ct F) to_implies

open VG.Impl.AesGcm.X86 VG.Impl.StackScratch.X86 in
/-- The instance of `vg_aes_gcm_open` calling the implementations `v`, with
its working space in a frame of its own. -/
def openFn (v : GcmImpl) : OpenFn where
  name := Spec.Gcm.openApi.name ++ v.suffix
  code := withStackScratch 2608 10 («open» v.callees)
  verified := open_framed v
  noSp := by
    have hs := NoSp.of_all (open_noEsp v)
    have ha : NoSp (.block (setArgs 2608 10) : Prog isa) := NoSp.of_all (by decide +kernel)
    intro i hi
    simp only [withStackScratch, instrs, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | hi | hi) | rfl
    · rfl
    · exact ha i hi
    · exact hs i hi
    · rfl
  depth := by
    have := open_stackUse v
    simp only [withStackScratch, stackUse, frameBytes, Nat.zero_max]
    exact Nat.le_trans (Nat.add_le_add_right this 2608) (by decide)

/-- No instruction of the code, or of the instance it calls, writes `esp`
but its frames' push and pop. -/
theorem openTo_spSafe (v : GcmImpl) :
    (openTo (openFn v).name (openFn v).code).all (fun i => !X86.isa.writesSp i) = true := by
  have hc : (openFn v).code.all (fun i => !X86.isa.writesSp i) = true :=
    withStackScratch_spSafe (bytes := 2608) (n := 10) (open_spSafe v)
  have he : (Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) = true := by decide
  have hs : Impl.AesGcm.X86.SealGather.copySlice.all (fun i => !X86.isa.writesSp i) = true := by decide
  have ha : after.all (fun i => !X86.isa.writesSp i) = true := by decide
  have hr : (Code.block restore : Prog isa).all (fun i => !X86.isa.writesSp i) = true := by decide
  show (!X86.isa.writesSp (.alloc 48) && ((Code.block entry : Prog isa).all (fun i => !X86.isa.writesSp i) &&
      (Impl.AesGcm.X86.SealGather.copySlice.all (fun i => !X86.isa.writesSp i) &&
        ((openFn v).code.all (fun i => !X86.isa.writesSp i) && (after.all (fun i => !X86.isa.writesSp i) &&
          (Code.block restore : Prog isa).all (fun i => !X86.isa.writesSp i))))) &&
      !X86.isa.writesSp (.free 48)) = true
  rw [he, hs, hc, ha, hr]; rfl

end VG.Proof.AesGcm.X86.OpenTo
