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
# ML-DSA's signing on x86-64, without secret residue

Each function as emitted (`Impl.MlDsa.X86_64.Fn`), over any implementation of
the polynomial arithmetic (`ArithImpl`), with its whole stack wiped by its
cleanup at the implementation's level: its code over the stub, but for the
call of the signing over the implementation, which is that over the stub with
the implementation's functions (`FnScrub`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.SignScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.FnScrub (stub stubStack)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe signMessagePrepared_verified
  signPrepared_sat)

theorem sign44_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.sign44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0)
      ((Spec.MlDsa.sign44Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.sign44Api)
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) 0
      verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_self ..) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.signBody44_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := sign44_stub)

theorem sign44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0)

theorem sign65_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.sign65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0)
      ((Spec.MlDsa.sign65Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.sign65Api)
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) 0
      verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.signBody65_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := sign65_stub)

theorem sign65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0)

theorem sign87_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) 0) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `Spec.MlDsa.sign87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem sign87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0)
      ((Spec.MlDsa.sign87Api).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.sign87Api)
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) 0
      verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.signBody87_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := sign87_stub)

theorem sign87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0)

theorem preparedSign44_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"))
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) 1
      verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_self ..) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.signBody44_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSign44_stub)

theorem preparedSign44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1)

theorem preparedSign65_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"))
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) 1
      verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.signBody65_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSign65_stub)

theorem preparedSign65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1)

theorem preparedSign87_stub : stubSideG (Impl.MlDsa.X86_64.Sign.entry "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) 1) VecLevel.sse.level stubStack 40 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSign87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract X86_64.abi 40) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"))
    { code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) 1
      verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
      spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.signBody87_fill v; unfold Impl.MlDsa.X86_64.Sign.entry; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSign87_stub)

theorem preparedSign87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1)

theorem signMessage44_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `Spec.MlDsa.signMessage44Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0)
      ((Spec.MlDsa.signMessage44Api).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.signMessage44Api)
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0
      verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.signBody44_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := signMessage44_stub)

theorem signMessage44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0)

theorem signMessage65_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `Spec.MlDsa.signMessage65Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0)
      ((Spec.MlDsa.signMessage65Api).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.signMessage65Api)
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0
      verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.signBody65_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := signMessage65_stub)

theorem signMessage65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0)

theorem signMessage87_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `Spec.MlDsa.signMessage87Api`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem signMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0)
      ((Spec.MlDsa.signMessage87Api).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := Spec.MlDsa.signMessage87Api)
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0
      verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 } _
    (VG.Proof.MlDsa.X86_64.Scrub.signMessageOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.signBody87_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := signMessage87_stub)

theorem signMessage87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0)

theorem preparedSignMessage44_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage44_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44"))
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1
      verified := signMessagePrepared_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..))
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa44 _)
    (by have hb := FnScrub.signBody44_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSignMessage44_stub)

theorem preparedSignMessage44_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1)

theorem preparedSignMessage65_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage65_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65"))
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1
      verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa65 _)
    (by have hb := FnScrub.signBody65_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSignMessage65_stub)

theorem preparedSignMessage65_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1)

theorem preparedSignMessage87_stub : stubSideG (Impl.MlDsa.X86_64.Message.signMessage "s" (Impl.MlDsa.X86_64.Sign.sign (Proof.MlDsa.X86_64.Sign.primsWith stub) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1) VecLevel.sse.level stubStack 112 [] = true := by decide +kernel

/-- `(Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")`'s function as emitted over `v` meets its contract in constant time
and returns without secret residue. -/
theorem preparedSignMessage87_scrubbed (v : ArithImpl) :
    VerifiedScrubbed target (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1)
      (((Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87")).contract X86_64.abi 112) 32 :=
  verifiedScrubbedAllFillG (api := (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87"))
    { code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1
      verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1 } _
    (VG.Proof.MlDsa.X86_64.Scrub.preparedSignMessageOut Spec.MlDsa.mlDsa87 _)
    (by have hb := FnScrub.signBody87_fill v; unfold Impl.MlDsa.X86_64.Message.signMessage; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := preparedSignMessage87_stub)

theorem preparedSignMessage87_spSafe (v : ArithImpl) : (Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1)

end VG.Proof.MlDsa.X86_64.SignScrub
