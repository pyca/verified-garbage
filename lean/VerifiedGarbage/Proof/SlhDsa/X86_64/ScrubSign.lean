module

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

public import VerifiedGarbage.Proof.SlhDsa.X86_64.SignTopCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGen
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubSignLit
import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssCT
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubSignLit
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.XmssCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.KCall
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# SLH-DSA (SHAKE) on x86-64: signing, verified and without secret residue

`sign` over any implementation `T` of `thash4`, with `forsSign` over `T`
(`forsFn`), meets `signContract` in constant time (`sign_verified`); as
emitted (`Impl.SlhDsa.X86_64.Fn.sign`), with the 120 bytes below its stack
pointer wiped and the registers cleared at `T`'s level, it returns without
secret residue: its code is its code over the stub `KeyGen.stubFns`
(`ScrubSignLit.lean`), with `T`'s where it calls it (`Fill`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.SignTop

open VG VG.X86_64 VG.X86_64.Scrub
open VG.Spec.SlhDsa
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.SlhDsa.X86_64.Shake (Arg callA kabs kpad ksqz hashM' signBody layerBody)
open VG.Proof.SlhDsa.X86_64.KeyGen (Shake6 fnsOf spSafe_of_nosp)

/-! ## FORS signing over `T` -/

theorem fset_of {p : Params} (hp : Shake6 p) : Fors.FSet p := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

theorem forsCode_eq {p : Params} (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns} (ht : f.t4 = T.code) :
    Impl.SlhDsa.X86_64.Shake.forsCode p f =
      Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k f.t4name f.levelsName T.code := by
  rw [Impl.SlhDsa.X86_64.Shake.forsCode, ht]; rfl

/-- `forsSign` over `T`, as `sign` calls it. -/
def forsFn {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) : ForsFn p (Impl.SlhDsa.X86_64.Shake.forsCode p f) where
  stack := T.stack + 24
  correct := by
    rw [forsCode_eq T ht]
    exact Fors.fors_correct (fset_of hp) T _ _ (Nat.le_refl _) (by have := T.stack_le; omega)
  ct := by
    rw [forsCode_eq T ht]
    exact Fors.fors_ct (fset_of hp) T _ _ (Nat.le_refl _) (by have := T.stack_le; omega)
  nosp := by
    rw [forsCode_eq T ht]
    exact Fors.fors_nospT (fset_of hp) T _ _
  depth := by
    rw [forsCode_eq T ht, Fors.fors_depth]
    have := T.depth_le; omega

/-! ## `Verified` -/

/-- `vg_slhdsa_shake_*_sign` for a SHAKE parameter set `p` and any
implementation `T` of `thash4` meets `signContract` in constant time. -/
theorem sign_verified {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) {stack : Nat} (hst : T.stack + 104 ≤ stack) (h62 : stack < 2 ^ 62) :
    Verified X86_64.target (Impl.SlhDsa.X86_64.Shake.sign p f) (Spec.SlhDsa.signContract p X86_64.abi stack) :=
  sign_verified' hp hp.sz hp.hps T ht (forsFn hp T ht) hst (by show T.stack + 24 + 80 ≤ stack; omega) h62

/-! ## The stack pointer -/

theorem argMov_nosp (a : Arg) {d : Reg} (hd : d ≠ .rsp) :
    (a.mov d).all (fun i => !Taint.clobbers i .rsp) = true := by
  cases a <;> simp [Arg.mov, Taint.clobbers, Taint.dstOf, hd]

theorem callA_nosp {n : String} {c : Prog isa} (as : List Arg) (hc : NoSp c) : NoSp (callA n c as) := by
  refine Levels.nosp_seq (Levels.nosp_block ?_) hc
  rw [List.all_flatMap, List.all_eq_true]
  rintro ⟨d, a⟩ h
  refine argMov_nosp a ?_
  have hd := (List.of_mem_zip h).1
  intro e; subst e; revert hd; decide

theorem hashM_nosp (p : Params) (xs : List Arg) (dst : Arg) (len : Nat) : NoSp (hashM' p xs dst len) := by
  unfold hashM'
  refine Levels.nosp_seq (Levels.nosp_block ?_) ?_
  · simp [Impl.SlhDsa.X86_64.Shake.zeroState, Taint.clobbers, Taint.dstOf]
  · generalize xs.zipIdx = l
    induction l with
    | nil =>
      exact Levels.nosp_seq (callA_nosp _ MlKem.X86_64.absorb_nosp) (Levels.nosp_seq
        (callA_nosp _ MlKem.X86_64.absorb_nosp) (Levels.nosp_seq (callA_nosp _ MlKem.X86_64.absorb_nosp)
          (Levels.nosp_seq (callA_nosp _ MlKem.X86_64.pad_nosp) (callA_nosp _ MlKem.X86_64.squeeze_nosp))))
    | cons x l ih => exact Levels.nosp_seq (callA_nosp _ MlKem.X86_64.absorb_nosp) ih

/-- The body of `sign`'s frame never writes `rsp` itself. -/
theorem signBody_nosp {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) : NoSp (signBody p f) := by
  have hx : NoSp (Impl.SlhDsa.X86_64.Shake.xmssCode p f) := by
    have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
        Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
      rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
    rw [hcode]; exact XmssTree.xmss_nosp hp.sz f.t4name f.wotsName f.levelsName T.nosp
  have hF := (forsFn hp T ht).nosp
  unfold signBody layerBody
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (hashM_nosp _ _ _ _)
    (Levels.nosp_seq (hashM_nosp _ _ _ _) (Levels.nosp_seq (Levels.nosp_block ?_)
      (Levels.nosp_seq (fun i hi => hF i hi) (Levels.nosp_seq (Levels.nosp_block ?_)
        (Levels.nosp_seq (Fors.nosp_loop (Levels.nosp_seq (Levels.nosp_block ?_)
          (Levels.nosp_seq (fun i hi => hx i hi) (Levels.nosp_block ?_)))) (Levels.nosp_block ?_)))))))
  all_goals rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> kernel_rfl

/-- `sign` never writes `rsp` but in its frame's push and pop. -/
theorem sign_spSafe {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) : (Impl.SlhDsa.X86_64.Shake.sign p f).all (fun i => !isa.writesSp i) = true := by
  have hb := spSafe_of_nosp (signBody_nosp hp T ht)
  unfold Impl.SlhDsa.X86_64.Shake.sign
  simp only [Code.all, hb]
  rfl

/-! ## Without secret residue -/

theorem signOut (p : Params) (stack : Nat) :
    PostOut (signContract p X86_64.abi stack) ((signSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sk, msg, ml, ctx, cl, rnd, sig, sc], _ =>
      simp only [signSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      have e := KeyGen.bytesAt_of (Nat.le_refl _) hb.2.2.2.2.1
      revert h
      show (match formatMessage (Spec.Sha3.bytesAt m ctx cl.toNat) (Spec.Sha3.bytesAt m msg ml.toNat) with
        | none => r = 2 ∧ Spec.Sha3.bytesAt m₁ sig p.sigLen = Spec.Sha3.bytesAt m sig p.sigLen
        | some M' => r = 1 ∧ Spec.Sha3.bytesAt m₁ sig p.sigLen =
            signInternal p M' (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m rnd p.n)) →
        (match formatMessage (Spec.Sha3.bytesAt m ctx cl.toNat) (Spec.Sha3.bytesAt m msg ml.toNat) with
        | none => r = 2 ∧ Spec.Sha3.bytesAt m₂ sig p.sigLen = Spec.Sha3.bytesAt m sig p.sigLen
        | some M' => r = 1 ∧ Spec.Sha3.bytesAt m₂ sig p.sigLen =
            signInternal p M' (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m rnd p.n))
      rw [e]
      exact id

theorem sign_scrubbed_of {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String)
    {a : Prog isa} (ha : stubSide a VecLevel.sse.level (fun _ => 16) 120 [] = true)
    (hf : Fill T.level.level (fun _ => 16) a (Impl.SlhDsa.X86_64.Shake.sign p (fnsOf p T set))) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level p (fnsOf p T set))
      ((signApi p module name).contract X86_64.abi 120) 32 :=
  verifiedScrubbedAllFill (api := signApi p module name)
    { suffix := T.sfx
      code := Impl.SlhDsa.X86_64.Shake.sign p (fnsOf p T set)
      verified := sign_verified hp T rfl (by have := T.stack_le; omega) (by decide)
      spSafe := sign_spSafe hp T rfl }
    T.level (signOut p 120) hf (by cases T.level <;> decide) (Nat.le_refl _) (ha := ha)

/-- `vg_slhdsa_shake_*_sign` as emitted, over any implementation `T` of
`thash4`, meets its contract in constant time and returns without secret
residue. -/
theorem sign_scrubbed {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level p (fnsOf p T set))
      ((signApi p module name).contract X86_64.abi 120) 32 := by
  have := T.side
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sign_scrubbed_of (.inl rfl) T module name set (a := stubS128s) (by lit_decide) (by fill_calls)
  · exact sign_scrubbed_of (.inr (.inl rfl)) T module name set (a := stubS128f) (by lit_decide) (by fill_calls)
  · exact sign_scrubbed_of (.inr (.inr (.inl rfl))) T module name set (a := stubS192s) (by lit_decide)
      (by fill_calls)
  · exact sign_scrubbed_of (.inr (.inr (.inr (.inl rfl)))) T module name set (a := stubS192f) (by lit_decide)
      (by fill_calls)
  · exact sign_scrubbed_of (.inr (.inr (.inr (.inr (.inl rfl))))) T module name set (a := stubS256s)
      (by lit_decide) (by fill_calls)
  · exact sign_scrubbed_of (.inr (.inr (.inr (.inr (.inr rfl))))) T module name set (a := stubS256f)
      (by lit_decide) (by fill_calls)

theorem sign_spSafeFn {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level p (fnsOf p T set)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (sign_spSafe hp T rfl)

/-! The parameter sets, as their registrations name them. -/

theorem sign128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_128s (fnsOf shake_128s T "128s"))
      (signShake_128sApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inl rfl) T _ _ "128s"

theorem sign128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_128s (fnsOf shake_128s T "128s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inl rfl) T "128s"

theorem sign128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_128f (fnsOf shake_128f T "128f"))
      (signShake_128fApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inr (.inl rfl)) T _ _ "128f"

theorem sign128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_128f (fnsOf shake_128f T "128f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inr (.inl rfl)) T "128f"

theorem sign192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_192s (fnsOf shake_192s T "192s"))
      (signShake_192sApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s"

theorem sign192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_192s (fnsOf shake_192s T "192s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inr (.inr (.inl rfl))) T "192s"

theorem sign192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_192f (fnsOf shake_192f T "192f"))
      (signShake_192fApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f"

theorem sign192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_192f (fnsOf shake_192f T "192f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inr (.inr (.inr (.inl rfl)))) T "192f"

theorem sign256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_256s (fnsOf shake_256s T "256s"))
      (signShake_256sApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s"

theorem sign256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_256s (fnsOf shake_256s T "256s")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s"

theorem sign256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.sign T.level shake_256f (fnsOf shake_256f T "256f"))
      (signShake_256fApi.contract X86_64.abi 120) 32 :=
  sign_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f"

theorem sign256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.sign T.level shake_256f (fnsOf shake_256f T "256f")).all (fun i => !isa.writesSp i) = true :=
  sign_spSafeFn (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f"

end VG.Proof.SlhDsa.X86_64.SignTop
