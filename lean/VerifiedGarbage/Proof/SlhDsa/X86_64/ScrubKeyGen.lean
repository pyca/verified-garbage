module

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

public import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGenCT
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGenLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# SLH-DSA (SHAKE) on x86-64: key generation without secret residue

Key generation as emitted (`Impl.SlhDsa.X86_64.Fn.keyGen`), over any
implementation `T` of `thash4`, with the 48 bytes below its stack pointer
wiped and the registers cleared at `T`'s level: its code is its code over
the stub `stubFns` (`ScrubKeyGenLit.lean`), with `T`'s where it calls it
(`Fill`), so the kernel evaluates what the cleanup needs of the stub once
for each parameter set, and `T` proves what it needs of its own code
(`Thash4Impl.side`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.KeyGen

open VG VG.X86_64 VG.X86_64.Scrub
open VG.Spec.SlhDsa
open VG.Impl.Scrub.X86_64 (VecLevel)

/-- The `n` bytes at `q` read the memory only within a region at `q` of at
least `n` bytes. -/
theorem bytesAt_of {m₁ m₂ : Mem} {q : Addr} {N n : Nat} (hn : n ≤ N)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Sha3.bytesAt m₂ q n = Spec.Sha3.bytesAt m₁ q n := by
  simp only [Spec.Sha3.bytesAt]
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have hi := List.mem_range.mp hi
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_using [this, hi, hn]

theorem keyGenOut (p : Params) (stack : Nat) :
    PostOut (keyGenContract p X86_64.abi stack) ((keyGenSig p).retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [seeds, sk, pk, sc], _ =>
      simp only [keyGenSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show (Spec.Sha3.bytesAt m₂ sk p.skLen, Spec.Sha3.bytesAt m₂ pk p.pkLen) = _
      rw [bytesAt_of (Nat.le_refl _) hb.2.1, bytesAt_of (Nat.le_refl _) hb.2.2.1]
      exact h

/-- An instruction that does not clobber `rsp` does not write it. -/
theorem writesSp_of_clobbers (i : Instr) (h : Taint.clobbers i .rsp = false) : isa.writesSp i = false := by
  rw [← Bool.not_eq_true', ← Taint.keepsSp_eq] at *
  cases i <;> simp_all [Taint.clobbers, Taint.dstOf, Taint.keepsSp, Taint.ctorIdx_beq]
  exact ⟨fun e => h.1 e.symm, fun e => h.2 e.symm⟩

theorem spSafe_of_nosp {c : Prog isa} (h : NoSp c) : c.all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [writesSp_of_clobbers i (h i hi)]; rfl

/-- Key generation never writes `rsp` itself. -/
theorem keyGen_nosp {p : Params} (hz : Wots4.Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.X86_64.Shake.Fns}
    (ht : f.t4 = T.code) : NoSp (Impl.SlhDsa.X86_64.Shake.keyGen p f) := by
  have hcode : Impl.SlhDsa.X86_64.Shake.xmssCode p f =
      Impl.SlhDsa.X86_64.Xmss.xmssTree (Wots4.L p) p.hp f.t4name f.wotsName f.levelsName T.code := by
    rw [Impl.SlhDsa.X86_64.Shake.xmssCode, ht]; rfl
  unfold Impl.SlhDsa.X86_64.Shake.keyGen
  rw [hcode]
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (fun i hi => ?_) (Levels.nosp_block ?_))
  · simp [Impl.SlhDsa.X86_64.Shake.kgSave, Impl.SlhDsa.X86_64.Shake.rcTable, Impl.SlhDsa.X86_64.Shake.seedLanes,
      Impl.SlhDsa.X86_64.Shake.treeLanes, Impl.SlhDsa.X86_64.setField, Impl.SlhDsa.X86_64.setFieldR,
      Impl.SlhDsa.X86_64.copyWords, List.all_flatMap, List.all_map, Taint.clobbers, Taint.dstOf]
  · exact XmssTree.xmss_nosp hz f.t4name f.wotsName f.levelsName T.nosp i hi
  · simp [Impl.SlhDsa.X86_64.Shake.writeKeys, Impl.SlhDsa.X86_64.Shake.kgRestore, Impl.SlhDsa.X86_64.copyWords, List.all_flatMap,
      List.all_map, Taint.clobbers, Taint.dstOf]
    decide

/-- The functions key generation over `T` calls, for the parameter set named `set`. -/
abbrev fnsOf {n : Nat} (p : Params) (T : Thash4Impl n) (set : String) : Impl.SlhDsa.X86_64.Shake.Fns :=
  Impl.SlhDsa.X86_64.Shake.Fns.ofVariant p T.sfx T.code set

theorem keyGen_scrubbed_of {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String)
    {a : Prog isa} (ha : stubSide a VecLevel.sse.level (fun _ => 16) 48 [] = true)
    (hf : Fill T.level.level (fun _ => 16) a (Impl.SlhDsa.X86_64.Shake.keyGen p (fnsOf p T set))) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level p (fnsOf p T set))
      ((keyGenApi p module name).contract X86_64.abi 48) 0 :=
  verifiedScrubbedAllFill (api := keyGenApi p module name)
    { suffix := T.sfx
      code := Impl.SlhDsa.X86_64.Shake.keyGen p (fnsOf p T set)
      verified := keyGen_verified hp T rfl (by have := T.stack_le; omega) (by decide)
      spSafe := spSafe_of_nosp (keyGen_nosp hp.sz T rfl) }
    T.level (keyGenOut p 48) hf (by cases T.level <;> decide) (Nat.le_refl _) (ha := ha)

/-- `vg_slhdsa_shake_*_keygen` as emitted, over any implementation `T` of
`thash4`, meets its contract in constant time and returns without secret
residue. -/
theorem keyGen_scrubbed {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (module name set : String) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level p (fnsOf p T set))
      ((keyGenApi p module name).contract X86_64.abi 48) 0 := by
  have := T.side
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact keyGen_scrubbed_of (.inl rfl) T module name set (a := stub128s) (by lit_decide) (by fill_calls)
  · exact keyGen_scrubbed_of (.inr (.inl rfl)) T module name set (a := stub128f) (by lit_decide) (by fill_calls)
  · exact keyGen_scrubbed_of (.inr (.inr (.inl rfl))) T module name set (a := stub192s) (by lit_decide)
      (by fill_calls)
  · exact keyGen_scrubbed_of (.inr (.inr (.inr (.inl rfl)))) T module name set (a := stub192f) (by lit_decide)
      (by fill_calls)
  · exact keyGen_scrubbed_of (.inr (.inr (.inr (.inr (.inl rfl))))) T module name set (a := stub256s)
      (by lit_decide) (by fill_calls)
  · exact keyGen_scrubbed_of (.inr (.inr (.inr (.inr (.inr rfl))))) T module name set (a := stub256f)
      (by lit_decide) (by fill_calls)

theorem keyGen_spSafeFn {p : Params} (hp : Shake6 p) (T : Thash4Impl p.n) (set : String) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level p (fnsOf p T set)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (spSafe_of_nosp (keyGen_nosp hp.sz T rfl))

/-! The parameter sets, as their registrations name them. -/

theorem keyGen128s_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_128s (fnsOf shake_128s T "128s"))
      (keyGenShake_128sApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inl rfl) T _ _ "128s"

theorem keyGen128s_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_128s (fnsOf shake_128s T "128s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inl rfl) T "128s"

theorem keyGen128f_scrubbed (T : Thash4Impl 16) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_128f (fnsOf shake_128f T "128f"))
      (keyGenShake_128fApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inr (.inl rfl)) T _ _ "128f"

theorem keyGen128f_spSafe (T : Thash4Impl 16) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_128f (fnsOf shake_128f T "128f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inr (.inl rfl)) T "128f"

theorem keyGen192s_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_192s (fnsOf shake_192s T "192s"))
      (keyGenShake_192sApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inr (.inr (.inl rfl))) T _ _ "192s"

theorem keyGen192s_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_192s (fnsOf shake_192s T "192s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inr (.inr (.inl rfl))) T "192s"

theorem keyGen192f_scrubbed (T : Thash4Impl 24) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_192f (fnsOf shake_192f T "192f"))
      (keyGenShake_192fApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inl rfl)))) T _ _ "192f"

theorem keyGen192f_spSafe (T : Thash4Impl 24) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_192f (fnsOf shake_192f T "192f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inr (.inr (.inr (.inl rfl)))) T "192f"

theorem keyGen256s_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_256s (fnsOf shake_256s T "256s"))
      (keyGenShake_256sApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inr (.inl rfl))))) T _ _ "256s"

theorem keyGen256s_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_256s (fnsOf shake_256s T "256s")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inr (.inr (.inr (.inr (.inl rfl))))) T "256s"

theorem keyGen256f_scrubbed (T : Thash4Impl 32) :
    VerifiedScrubbed target (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_256f (fnsOf shake_256f T "256f"))
      (keyGenShake_256fApi.contract X86_64.abi 48) 0 :=
  keyGen_scrubbed (.inr (.inr (.inr (.inr (.inr rfl))))) T _ _ "256f"

theorem keyGen256f_spSafe (T : Thash4Impl 32) :
    (Impl.SlhDsa.X86_64.Fn.keyGen T.level shake_256f (fnsOf shake_256f T "256f")).all (fun i => !isa.writesSp i) = true :=
  keyGen_spSafeFn (.inr (.inr (.inr (.inr (.inr rfl))))) T "256f"

end VG.Proof.SlhDsa.X86_64.KeyGen
