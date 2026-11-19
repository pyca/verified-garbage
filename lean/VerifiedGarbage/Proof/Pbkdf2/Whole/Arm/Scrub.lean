module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha512.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Frame
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha224
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Sha1.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# PBKDF2-HMAC on ARMv7, without secret residue

`vg_pbkdf2_hmac_<hash>` runs in a frame that holds its working space
(`Frame.lean`), and the functions it calls push registers below it: its
frames use the working space's bytes and 16 more (`armStack`), within the
`24 + pbkFrame I` its contract reserves. That is no frame size of the model
(`FrameOk`), so it is registered with the next one
(`Arm.Scrub.Verified.stack_le`), of 8 bytes more, and followed by a wipe of
that many bytes below the stack pointer (`Arm.Scrub.scrubRegF`), then by
instructions that set the registers a callee may change and the flags to
constants. Its postcondition reads the memory on return only within `out`
(`pbkdf2OutArm`), as on RISC-V (`Proof/Pbkdf2/Whole/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

materialize_code md5Pbkdf2Arm := md5F.pbkdf2
materialize_code sha1Pbkdf2Arm := sha1F.pbkdf2
materialize_code sha224Pbkdf2Arm := sha224F.pbkdf2
materialize_code sha256Pbkdf2Arm := sha256F.pbkdf2
materialize_code sha384Pbkdf2Arm := sha384F.pbkdf2
materialize_code sha512Pbkdf2Arm := sha512F.pbkdf2
materialize_code sha512_224Pbkdf2Arm := sha512_224F.pbkdf2
materialize_code sha512_256Pbkdf2Arm := sha512_256F.pbkdf2

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2OutArm (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 32) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32] (Spec.Pbkdf2.pbkdf2Post I.S 32) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32] (Spec.Pbkdf2.pbkdf2Post I.S 32) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 32); omega_using [hi])]
    exact h

/-! ## The stacks of the registrations

`24 + pbkFrame I` rounded up to a frame size of the model: 1088 for MD5,
1184 for SHA-1, 1664 for SHA-224 and SHA-256, 3488 for SHA-384, SHA-512 and
its truncations. A state satisfies the precondition with them, as with the
fewer bytes (`Frame.lean`). -/

theorem md5_satArm : ∃ s, (Spec.Hmac.md5I.pbkdf2Contract abi 1088).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.md5I,
      Spec.Hmac.md5S, Spec.Hmac.md5, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha1_satArm : ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract abi 1184).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha1I,
      Spec.Hmac.sha1S, Spec.Hmac.sha1, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha224_satArm : ∃ s, (Spec.Hmac.sha224I.pbkdf2Contract abi 1664).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha224I,
      Spec.Hmac.sha224S, Spec.Hmac.sha224, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha256_satArm : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract abi 1664).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I,
      Spec.Hmac.sha256S, Spec.Hmac.sha256, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha384_satArm : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract abi 3488).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384I,
      Spec.Hmac.sha384S, Spec.Hmac.sha384, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_satArm : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract abi 3488).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512I,
      Spec.Hmac.sha512S, Spec.Hmac.sha512, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_224_satArm : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract abi 3488).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224I,
      Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

theorem sha512_256_satArm : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract abi 3488).pre s := by
  implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256I,
      Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, abi, argRegs, reduceClassify, Loc.val, State.addr]
    [pbkFrameSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using pbkFrameSat

/-- `vg_pbkdf2_hmac_<hash>`'s code, verified with `24 + pbkFrame I` bytes of
stack, then with `n` bytes, a frame size of the model, if its precondition is
satisfiable with them; its frames within `n` bytes and without indirect
calls, scrubbed (`scrubRegF`). -/
def regArm (I : Spec.Hmac.Instance) (F : Impl.Pbkdf2.Whole.Arm.Fns) (n : Nat)
    (hv : Verified target (Impl.StackScratch.Arm.withStackScratch (pbkFrame I) 3 F.pbkdf2)
      (I.pbkdf2Contract abi (24 + pbkFrame I)))
    (hle : 24 + pbkFrame I ≤ n) (hsat : ∃ s, (I.pbkdf2Contract abi n).pre s)
    (hd : armStack (Impl.StackScratch.Arm.withStackScratch (pbkFrame I) 3 F.pbkdf2) ≤ n)
    (hni : noIcall (Impl.StackScratch.Arm.withStackScratch (pbkFrame I) 3 F.pbkdf2) = true)
    (hn : FrameOk n) : Registration I.pbkdf2Api target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch (pbkFrame I) 3 F.pbkdf2
      contract := I.pbkdf2Contract abi n
      verified := Verified.stack_le (sig := Spec.Pbkdf2.pbkdf2Sig)
        (pre := Spec.Pbkdf2.pbkdf2Pre I.S abi.ptrBits) (post := Spec.Pbkdf2.pbkdf2Post I.S abi.ptrBits)
        (wa := true) (leak := none) hle hv hsat
      spSafe := spSafe_any _ }
    hd hni hn (pbkdf2OutArm I n) rfl

/-! ## The registrations -/

/-- `Spec.Hmac.md5I.pbkdf2Api`. -/
def md5RegArm : Registration Spec.Hmac.md5I.pbkdf2Api target :=
  regArm Spec.Hmac.md5I md5F 1088
    (pbkFramed md5 md5_pbkFrameSat) (by decide) md5_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha1I.pbkdf2Api`. -/
def sha1RegArm : Registration Spec.Hmac.sha1I.pbkdf2Api target :=
  regArm Spec.Hmac.sha1I sha1F 1184
    (pbkFramed sha1 sha1_pbkFrameSat) (by decide) sha1_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha224I.pbkdf2Api`. -/
def sha224RegArm : Registration Spec.Hmac.sha224I.pbkdf2Api target :=
  regArm Spec.Hmac.sha224I sha224F 1664
    (pbkFramed sha224 sha224_pbkFrameSat) (by decide) sha224_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha256I.pbkdf2Api`. -/
def sha256RegArm : Registration Spec.Hmac.sha256I.pbkdf2Api target :=
  regArm Spec.Hmac.sha256I sha256F 1664
    (pbkFramed sha256 sha256_pbkFrameSat) (by decide) sha256_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha384I.pbkdf2Api`. -/
def sha384RegArm : Registration Spec.Hmac.sha384I.pbkdf2Api target :=
  regArm Spec.Hmac.sha384I sha384F 3488
    (pbkFramed sha384 sha384_pbkFrameSat) (by decide) sha384_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha512I.pbkdf2Api`. -/
def sha512RegArm : Registration Spec.Hmac.sha512I.pbkdf2Api target :=
  regArm Spec.Hmac.sha512I sha512F 3488
    (pbkFramed sha512 sha512_pbkFrameSat) (by decide) sha512_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha512_224I.pbkdf2Api`. -/
def sha512_224RegArm : Registration Spec.Hmac.sha512_224I.pbkdf2Api target :=
  regArm Spec.Hmac.sha512_224I sha512_224F 3488
    (pbkFramed sha512_224 sha512_224_pbkFrameSat) (by decide) sha512_224_satArm
    (by lit_decide) (by lit_decide) (by decide)

/-- `Spec.Hmac.sha512_256I.pbkdf2Api`. -/
def sha512_256RegArm : Registration Spec.Hmac.sha512_256I.pbkdf2Api target :=
  regArm Spec.Hmac.sha512_256I sha512_256F 3488
    (pbkFramed sha512_256 sha512_256_pbkFrameSat) (by decide) sha512_256_satArm
    (by lit_decide) (by lit_decide) (by decide)

end VG.Proof.Pbkdf2.Whole.Arm.Scrub
