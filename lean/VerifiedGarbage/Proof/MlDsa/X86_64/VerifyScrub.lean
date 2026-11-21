module

public import VerifiedGarbage.Proof.MlDsa.X86_64.FnScrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Mask
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestRow
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp4
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
public import VerifiedGarbage.Proof.MlDsa.X86_64.PkTr
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Scrub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.ExternalMu
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Sat
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Scrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack

/-!
# ML-DSA's verification on x86-64, without secret residue

Each function as emitted (`Impl.MlDsa.X86_64.Fn`), over any implementation of
the polynomial arithmetic (`ArithImpl`), with its whole stack wiped by its
cleanup at the implementation's level: its code over the stub, but for the
call of the verification over the implementation, which is that over the stub with
the implementation's functions (`FnScrub`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.VerifyScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.FnScrub (stub stubStack)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_spSafe)
open VG.Proof.MlDsa.X86_64.Message (verifyFn verifyMessage_verified verifyMessage_spSafe
  verifyMessagePrepared_verified verifyPrepared_sat)

theorem verify44_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.verify44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verify44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0)
      ((Spec.MlDsa.verify44Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.verify44Api)
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) 0
      verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_self ..) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.verifyBody44_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verify44_stub)

theorem verify44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0)

theorem verify65_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.verify65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verify65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0)
      ((Spec.MlDsa.verify65Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.verify65Api)
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) 0
      verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.verifyBody65_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verify65_stub)

theorem verify65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0)

theorem verify87_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.verify87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verify87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0)
      ((Spec.MlDsa.verify87Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.verify87Api)
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) 0
      verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.verifyBody87_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verify87_stub)

theorem verify87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0)

theorem preparedVerify44_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerify44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"))
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) 1
      verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_self ..) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.verifyBody44_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerify44_stub)

theorem preparedVerify44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1)

theorem preparedVerify65_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerify65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"))
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) 1
      verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.verifyBody65_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerify65_stub)

theorem preparedVerify65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1)

theorem preparedVerify87_stub : stubSideG (Impl.MlDsa.X86_64.Verify.entry "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerify87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"))
    { code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) 1
      verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
      spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.verifyBody87_fill v; unfold Impl.MlDsa.X86_64.Verify.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerify87_stub)

theorem preparedVerify87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1)

theorem verifyMessage44_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verifyMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0)
      (((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0
      verified := verifyMessage_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyMessageCachedOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.verifyBody44_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verifyMessage44_stub)

theorem verifyMessage44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0)

theorem verifyMessage65_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verifyMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0)
      (((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0
      verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyMessageCachedOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.verifyBody65_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verifyMessage65_stub)

theorem verifyMessage65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0)

theorem verifyMessage87_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem verifyMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0)
      (((Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0
      verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.verifyMessageCachedOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.verifyBody87_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verifyMessage87_stub)

theorem verifyMessage87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0)

theorem preparedVerifyMessage44_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerifyMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1
      verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..) (verifyPrepared_sat (prims_okWith v) (List.mem_cons_self ..))
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyMessageOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.verifyBody44_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerifyMessage44_stub)

theorem preparedVerifyMessage44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1)

theorem preparedVerifyMessage65_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerifyMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1
      verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (verifyPrepared_sat (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyMessageOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.verifyBody65_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerifyMessage65_stub)

theorem preparedVerifyMessage65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1)

theorem preparedVerifyMessage87_stub : stubSideG (Impl.MlDsa.X86_64.Message.verifyMessageCached "s" (Impl.MlDsa.X86_64.Verify.verify (Proof.MlDsa.X86_64.Verify.primsWith stub) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedVerifyMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"))
    { code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1
      verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (verifyPrepared_sat (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedVerifyMessageOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.verifyBody87_fill v; unfold Impl.MlDsa.X86_64.Message.verifyMessageCached; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedVerifyMessage87_stub)

theorem preparedVerifyMessage87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1)

end VG.Proof.MlDsa.X86_64.VerifyScrub
