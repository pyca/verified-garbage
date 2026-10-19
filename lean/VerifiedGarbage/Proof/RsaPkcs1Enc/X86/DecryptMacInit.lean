module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacInitPre
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacState

/-! # Initialize a verified HMAC-SHA-256 with DH or KDK -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem macInit_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : Nat} {K0 : List Byte}
    (h : Context g bs s) (a : Arguments g (fun j => (macInitPlan key j).valueAt g) 5 s)
    (keyLow : 192 ≤ key) (keyHigh : key + 32 ≤ sHash)
    (keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch key 32).base 32 = K0) :
    WP isa (.call (hashFns v).hiN (hashFns v).hiC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (macInitWr g ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧ MacRepr g K0 [] t := by
  have keyFit : key + 32 ≤ 8448 := by unfold sHash at keyHigh; omega
  have keyStart : key < 8448 := by omega
  have argsWrite : InRegions s.wr (callArgsRegion g 20).base 20 := by
    have raw := h.inner.write (d := 0) (n := 20) (by decide)
    simpa only [BitVec.add_zero, callArgsRegion] using raw
  have W : Covers (macInitWr g) s.wr := (Covers.one (h.scratchWrite (by decide : sSt + 96 ≤ 8448))).cons
    ((Covers.one (h.scratchWrite (by decide : sOuter + 96 ≤ 8448))).cons
      ((Covers.one (h.scratchWrite (by decide : sHash + 832 ≤ 8448))).pair (Covers.one argsWrite)))
  have R : Covers (macInitRd g key) (s.rd ++ s.wr) := Covers.one (h.scratchRead keyFit)
  refine WP.mono (hash_call_ok h (hmacInit_verified v)
    (Nat.le_trans v.initStack (by decide)) v.initNoSp (macInit_pre h a keyLow keyHigh)
    (Covers.append_left R W.right) W ?_) ?_
  · intro r hr
    simp only [macInitWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sOuter + 96 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sHash + 832 ≤ 8448)⟩
    · exact ⟨_, by simp [hashWrites], Region.sub_prefix (by decide : 20 ≤ 80)⟩
  · rintro t ⟨ht, F, Ffine, K, u, M, _, post⟩
    refine ⟨ht, F, Ffine, K, ?_⟩
    sig_post [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig,
      Spec.Hmac.initPost, Spec.Hmac.initSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      abi, argSlots, argVal, argBytes] at post
    have sa := fun {j : Nat} (hj : j < 5) => callArgument_value h a (by decide : 5 ≤ 20) hj (macInitRd g key) (macInitWr g)
    have v0 : (macInitPlan key 0).valueAt g = g.workspace := by simp [macInitPlan, CallArg.valueAt, sSt]
    have v1 : (macInitPlan key 1).valueAt g = g.workspace + BitVec.ofNat 32 sOuter := rfl
    have v2 : (macInitPlan key 2).valueAt g = g.workspace + BitVec.ofNat 32 key := rfl
    have v3 : (macInitPlan key 3).valueAt g = BitVec.ofNat 32 32 := rfl
    simp only [sa (by decide : 0 < 5), sa (by decide : 1 < 5), sa (by decide : 2 < 5),
      sa (by decide : 3 < 5), v0, v1, v2, v3, show (32#32).toNat = 32 from rfl, M] at post
    have entryKey : Spec.Rsa.bytesAt s.callEntry.mem (g.scratch key 32).base 32 = K0 := by
      have same : Spec.Rsa.bytesAt s.callEntry.mem (g.scratch key 32).base 32 =
          Spec.Rsa.bytesAt s.mem (g.scratch key 32).base 32 := by
        apply VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by decide)
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact (h.calleeScratch keyFit).symm
      exact same.trans keyBytes
    change Spec.Sha256.Repr t.mem (byteAddr g.workspace)
        (Spec.Hmac.xorPad (macKey (Spec.Rsa.bytesAt s.callEntry.mem
          (byteAddr (g.workspace + BitVec.ofNat 32 key)) 32)) Spec.Hmac.ipad) ∧
      Spec.Sha256.Repr t.mem (byteAddr (g.workspace + BitVec.ofNat 32 sOuter))
        (Spec.Hmac.xorPad (macKey (Spec.Rsa.bytesAt s.callEntry.mem
          (byteAddr (g.workspace + BitVec.ofNat 32 key)) 32)) Spec.Hmac.opad) at post
    have keyAddr : byteAddr (g.workspace + BitVec.ofNat 32 key) = (g.scratch key 32).base :=
      h.valid.scratchAddress keyStart
    have outerAddr : byteAddr (g.workspace + BitVec.ofNat 32 sOuter) = (g.scratch sOuter 96).base :=
      h.valid.scratchAddress (by decide)
    rw [keyAddr, entryKey, outerAddr] at post
    simpa only [MacRepr, List.append_nil, Geometry.scratch, sSt, BitVec.add_zero] using post

end VG.Proof.RsaPkcs1Enc.X86.Dec
