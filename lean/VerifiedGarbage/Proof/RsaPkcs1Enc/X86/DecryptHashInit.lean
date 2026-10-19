module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashArgs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashFrames
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptFns
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScratch

/-! # Start SHA-256 over the fixed-width private exponent -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem callArgument_value {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    {values : Nat → BitVec 32} {n j : Nat} (h : Context g bs s) (a : Arguments g values n s)
    (bound : n ≤ 20) (index : j < n) (rd wr : List Region) :
    arg (s.callEntry.withRegions rd wr) j = values j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; unfold calleeBytes at this; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes; omega)]
  exact a j index

def initRd (g : Geometry) : List Region := [⟨byteAddr g.stack, 4⟩]
def initWr (g : Geometry) : List Region := [g.scratch sSt 96]

theorem shaInit_pre {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (fun j => (shaInitPlan j).valueAt g) 1 s) :
    (Spec.Sha256.initContract abi).pre (s.callEntry.withRegions (initRd g) (initWr g)) := by
  have sa := callArgument_value h a (by decide : 1 ≤ 20) (by decide : 0 < 1) (initRd g) (initWr g)
  sig_pre [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa, shaInitPlan, CallArg.valueAt, sSt, BitVec.add_zero, argAddr_withRegions, argAddr_callEntry,
    h.sp, Nat.mul_zero]
  have argsSub : (⟨byteAddr g.stack, 4⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have stateSub : (⟨byteAddr g.workspace, 96⟩ : Region).Sub g.workspaceRegion :=
    Region.sub_prefix (by have := h.valid.scratchMinimum; omega)
  have argsState := (h.valid.stackWorkspace.sub_left
    (fun x hx => h.valid.innerSub x (argsSub x hx))).sub_right stateSub
  have retState := ((h.valid.stackWorkspace.sub_left h.valid.calleeSub).sub_left h.retSub).sub_right stateSub
  have retArgs := (h.valid.calleeInner.sub_right argsSub).sub_left h.retSub
  refine ⟨?_, rfl, by simp [initWr, Geometry.scratch, sSt, byteAddr], argsState.symm, retState, retArgs, ?_⟩
  · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
    rw [sub_toNat (sp := g.stack) (k := 4) (by have := h.valid.stackLow; unfold calleeBytes at this; omega)]
    have := h.valid.stackHigh
    have := h.valid.stackLow
    unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes calleeBytes at *
    omega
  · have := h.valid.scratchMinimum
    have := h.valid.workspaceFit
    omega

theorem shaInit_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (fun j => (shaInitPlan j).valueAt g) 1 s) :
    WP isa (.call (hashFns v).initN (hashFns v).initC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (initWr g ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Sha256.Repr t.mem (g.scratch sSt 96).base [] := by
  have W : Covers (initWr g) s.wr := Covers.one (h.scratchWrite (by decide : sSt + 96 ≤ 8448))
  have R : Covers (initRd g) (s.rd ++ s.wr) := Covers.one (by
    have read := h.inner.read (d := 0) (n := 4) (by decide)
    simpa only [BitVec.add_zero] using read)
  refine WP.mono (hash_call_ok h (init_verified v)
    (by change stackUse VG.Impl.Sha256.X86.Stream.init ≤ 3368; decide +kernel)
    (NoSp.of_all (by change VG.Impl.Sha256.X86.Stream.init.allInstrs (fun i => !Taint.clobbers i .esp) = true; decide +kernel)) (shaInit_pre h a)
    (Covers.append_left R W.right) W ?_) ?_
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
  · rintro t ⟨ht, F, Ffine, K, u, M, _, post⟩
    refine ⟨ht, F, Ffine, K, ?_⟩
    sig_post [Spec.Sha256.initContract, Spec.Sha256.initSig, abi, argSlots, argVal, argBytes] at post
    have sa := callArgument_value h a (by decide : 1 ≤ 20) (by decide : 0 < 1) (initRd g) (initWr g)
    rw [sa, M] at post
    simpa only [shaInitPlan, CallArg.valueAt, sSt, BitVec.add_zero, Geometry.scratch, byteAddr] using post

end VG.Proof.RsaPkcs1Enc.X86.Dec
