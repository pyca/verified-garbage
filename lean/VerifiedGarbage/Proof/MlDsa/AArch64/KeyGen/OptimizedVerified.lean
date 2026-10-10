import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestTiming
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat

/-! ## From `OptimizedTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem codeWith_ct {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2)
    (hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    ConstantTime isa (fun s => kgPre p S s ∧ Sign.StaticRoots S s)
      (fun s t => kgPub p S s t ∧ TableEq s t) (codeWith keccak.callee P cd p) := by
  have ht : RelCT isa (RootPair p S (fun σ s => s=σ))
      (codeWith keccak.callee P cd p) (fun _ _ => True) :=
    RelCT.seq (piece_rooted (prefix_piece hP C hF hm hs) hdprefix hP.s64)
      (RelCT.seq (rest_relCT hP hF hdpack hdrow) (epi_piece hF).tr)
  intro s t tr ur s' t' hs ht' pub es et
  exact (ht _ _ _ _ _ _ ⟨⟨s,t,hs.1,ht'.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht'.2⟩⟩,pub.2⟩ es et).1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedPrims.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem primitives_ok : PrimsOk (primitives keccak.callee) 16 :=
  { prims_okWith (keccak := keccak) with
    add := CalleeOk.of_verified (by decide) AddSub.add_verified (by decide) (by dsimp only [primitives]; decide)
    power2Round := CalleeOk.of_verified (by decide) KeygenRound.power2Round_verified (by decide) (by dsimp only [primitives]; decide)
    simpleBitPack := CalleeOk.of_verified (by decide) KeygenPack.simple_verified (by decide) (by dsimp only [primitives]; decide)
    bitPack := CalleeOk.of_verified (by decide) KeygenPack.signed_verified (by decide) (by dsimp only [primitives]; decide) }

theorem two_callee : CalleeOk 16 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    (Spec.MlDsa.rejNTT2Contract AArch64.abi 16) :=
  CalleeOk.of_verified (by decide) ResidentRej.two_verified (by decide) (by decide)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedDepth.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Message
variable (v : Proof.Sha3.AArch64.Permutation)

theorem packSecret_dle (p : Spec.MlDsa.Params) (j : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret (primitives v.callee) p j) := by
  have hb := DLe.of_fd (primitives_ok (keccak := v)).bitPack.fd
  dle_tac

theorem row_dle {p : Spec.MlDsa.Params}
    (hp : p=Spec.MlDsa.mlDsa44∨p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) (i : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.row (primitives v.callee) p i) := by
  have C := primitives_ok (keccak := v)
  have ha := DLe.of_fd C.add.fd
  have hr := DLe.of_fd C.power2Round.fd
  have hs := DLe.of_fd C.simpleBitPack.fd
  have hb := DLe.of_fd C.bitPack.fd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp with rfl|rfl|rfl <;> exact ⟨by decide +kernel⟩
  dle_tac

theorem prefix_dle {p : Spec.MlDsa.Params} (hF : PFacts p) :
    DLe 1 (prefixWith v.callee (primitives v.callee) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p) := by
  have C := primitives_ok (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hn := DLe.of_fd C.rejNtt.fd
  have h4 := DLe.of_fd C.rej4.fd
  have h2 := DLe.of_fd two_callee.fd
  have hb := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_callee 16 v.callee.pairedSha3
    (hF.eta.imp And.left And.left)).fd
  unfold prefixWith matrixWith secretsWith
  split <;> split <;> dle_tac

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts signRootConsts_eq)

theorem keyGen_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (keyGenWith v.callee p) (keyGenContract p (abi.withConsts signRootConsts) 16) := by
  have hF := pfacts hp
  have hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2 := by rcases hp with rfl|rfl|rfl <;> decide
  have hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3 := by rcases hp with rfl|rfl|rfl <;> decide
  have hP := primitives_ok (keccak := v)
  have hdpre : 16*(prefixWith v.callee (primitives v.callee)
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p).aarch64Depth≤16 := by
    have h := (prefix_dle v hF).le; omega
  have hdpack : ∀j<p.ℓ+p.k,16*(packSecret (primitives v.callee) p j).aarch64Depth≤16 := by
    intro j _; have h := (packSecret_dle v p j).le; omega
  have hdrow : ∀i<p.k,16*(row (primitives v.callee) p i).aarch64Depth≤16 := by
    intro i _; have h := (row_dle v hp i).le; omega
  refine ⟨?_,?_,⟨keyGenSat p,keyGen_sat hp⟩⟩
  · intro s h
    obtain ⟨pre,roots⟩ := staticRoots_entry (by decide) h
    exact codeWith_ok hP two_callee hF hm hs pre roots hdpre hdpack hdrow
  · intro s t tr ur s' t' hσ hτ pub es et
    have preσ := staticRoots_entry (by decide) hσ
    have preτ := staticRoots_entry (by decide) hτ
    have pb : kgPub p 16 s t ∧ TableEq s t := by
      sig_pub [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq] at pub
      obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := pub
      refine ⟨?_,hf,hi⟩
      dsimp only [kgPub]
      sig_pub [keyGenContract,keyGenSig,abi,argRegs]
      exact ⟨hsp,hb,h0,h1,h2,h3⟩
    exact codeWith_ct hP two_callee hF hm hs hdpre hdpack hdrow
      s t tr ur s' t' preσ preτ pb es et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end
