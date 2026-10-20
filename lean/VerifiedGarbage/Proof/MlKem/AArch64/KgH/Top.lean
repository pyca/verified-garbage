module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Timing
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # The key generation hashing `ek` during the matrix: constant time

`keyGenAArch64S`: `keyGenAArch64` with the 128 bytes of stack below `sp` the
`x3` calls use. `keyGenH_relCT`: two runs with the same public inputs leak the
same: `G` by the taint analysis from the arguments (`ha`), the noise and the
encodings of `ŝ` (`hpre`) and the tail (`htail`) by the taint analysis from the
pointers and the symbols, and the matrix with the rows of `t̂` by
`matrixRows_relCT`. `keyGenH_ct`: hence constant time. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk entryContractS entryS_tables entryS_symbols frame)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem

variable {P : KemLay}

/-- `keyGenAArch64 P`, with 128 bytes of stack. -/
def keyGenAArch64S (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 64⟩
    let ek : Region := ⟨s.gpr .x1, P.ekLen⟩
    let dk : Region := ⟨s.gpr .x2, P.dkLen⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 128, 128⟩
    s.rd = [seed] ∧ s.wr = [ek, dk, scratch] ∧ seed.Disjoint ek ∧ seed.Disjoint dk ∧
    seed.Disjoint scratch ∧ ek.Disjoint dk ∧ ek.Disjoint scratch ∧ dk.Disjoint scratch ∧
    128 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint ek ∧ stack.Disjoint dk ∧
    stack.Disjoint scratch
  post := (keyGenAArch64 P).post
  pub := (keyGenAArch64 P).pub

theorem preKS {s : State} (h : (keyGenAArch64S P).pre s) :
    (keyGenAArch64 P).pre s ∧ 128 ≤ s.sp.toNat ∧ ∀ b < 4, (frame s.sp).Disjoint ⟨kA s b, kL P b⟩ := by
  obtain ⟨rd, wr, d01, d02, d03, d12, d13, d23, sp128, k0, k1, k2, k3⟩ := h
  have sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd, wr, d01, d02, d03, d12, d13, d23, by omega,
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub⟩, sp128, ?_⟩
  intro b hb
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
  · exact k0
  · exact k1
  · exact k2
  · exact k3

theorem keyGenH_relCT (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    {σ τ : State} (hp : Pre P σ) (hq : Pre P τ) (hk : Stk128K P σ) (hk' : Stk128K P τ) (hr : Noise.Room P)
    (taσ : Tables σ) (taτ : Tables τ) (tsσ : TStk σ) (tsτ : TStk τ) (sm : SameK P σ τ)
    (shuffle : σ.syms "VG_MLKEM_REJ_SHUFFLE" = τ.syms "VG_MLKEM_REJ_SHUFFLE")
    (symbols : ∀ name ∈ restSymbols, σ.syms name = τ.syms name)
    (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Kem16.kgPre P).aarch64Depth ≤ 1)
    (ha : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashCallers.kgAUsing hash P) h).isSome = true)
    (hpre : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgPre P) h).isSome = true)
    (hrow : ∀ i < P.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow P i) h).isSome = true)
    (habs : ∀ blk, 136 * blk < (Kem16.kgSrc P).len → ∃ h, (taint.check (Taint.ofRegs [(Kem16.kgSrc P).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc P) blk)) h).isSome = true)
    (htail : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgTail v.callee P) h).isSome = true) :
    RelCT isa (fun s u => s = σ ∧ u = τ) (Kem16.keyGenH hash v.callee P) (fun _ _ => True) := by
  intro s u tr ur t w h et eu
  rcases h with ⟨hs, hu⟩; subst s; subst u
  have et' : Exec isa (.seq (FixedHashCallers.kgAUsing hash P) (.seq (Kem16.kgPre P)
      (.seq (seqs (Kem16.kgMatrixRows P)) (Kem16.kgTail v.callee P)))) σ tr t := et
  have eu' : Exec isa (.seq (FixedHashCallers.kgAUsing hash P) (.seq (Kem16.kgPre P)
      (.seq (seqs (Kem16.kgMatrixRows P)) (Kem16.kgTail v.callee P)))) τ ur w := eu
  obtain ⟨sA, ta, tb, rfl, ea, eb⟩ := Paired.seq_parts et'
  obtain ⟨uA, ua, ub, rfl, fa, fb⟩ := Paired.seq_parts eu'
  have aeq := (VectorTaint.relRegs [.x0,.x1,.x2,.x3]
    (P := fun s u => s = σ ∧ u = τ) (fun s u ⟨hs, hu⟩ => by
      subst s; subst u
      refine ⟨sm.sp, ?_⟩
      intro r hr
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sm.ptr 0
      · exact sm.ptr 1
      · exact sm.ptr 2
      · exact sm.ptr 3) ha.choose_spec _ _ _ _ _ _ ⟨rfl, rfl⟩ ea fa).1
  have hsA := Paired.exec_post (WP.tablesDepth (a_using_ok hash hG hp) taσ depthA) ea
  have huA := Paired.exec_post (WP.tablesDepth (a_using_ok hash hG hq) taτ depthA) fa
  obtain ⟨sB, tc, td, rfl, ec, ed⟩ := Paired.seq_parts eb
  obtain ⟨uB, uc, ud, rfl, fc, fd⟩ := Paired.seq_parts fb
  have symsA : ∀ name ∈ restSymbols, sA.syms name = uA.syms name := fun name hn => by
    rw [Exec.syms ea, Exec.syms fa]; exact symbols name hn
  have beq := symbol_taint [.x25,.x26,.x27,.x28] (by rw [hsA.1.kb.sp, huA.1.kb.sp, sm.sp]) (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [hsA.1.kb.x25, huA.1.kb.x25, sm.ptr 0]
      · rw [hsA.1.kb.x26, huA.1.kb.x26, sm.ptr 1]
      · rw [hsA.1.kb.x27, huA.1.kb.x27, sm.ptr 2]
      · rw [hsA.1.kb.x28, huA.1.kb.x28, sm.ptr 3]) symsA hpre ec fc
  have hsB := Paired.exec_post (pre_ok hp hr hsA.1 hsA.2 (tsσ.of (Exec.syms ea) hsA.1.kb.sp) depthP) ec
  have huB := Paired.exec_post (pre_ok hq hr huA.1 huA.2 (tsτ.of (Exec.syms fa) huA.1.kb.sp) depthP) fc
  obtain ⟨sC, te, tf, rfl, ee, ef⟩ := Paired.seq_parts ed
  obtain ⟨uC, ue, uf, rfl, fe, ff⟩ := Paired.seq_parts fd
  have mr := RelCTs.seqs (matrixRows_ne_nil P hp.wf.facts.1)
    (matrixRows_relCT hp hq hk hk' hr sm habs hrow) sB uB te ue sC uC
    ⟨hsB, huB, by rw [Exec.syms ec, Exec.syms fc, Exec.syms ea, Exec.syms fa]; exact shuffle,
      fun name hn => by rw [Exec.syms ec, Exec.syms fc]; exact symsA name hn⟩ ee fe
  have hsC := mr.2.1.b.kb
  have huC := mr.2.2.1.b.kb
  have deq := symbol_taint [.x25,.x26,.x27,.x28] (by rw [hsC.sp, huC.sp, sm.sp]) (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [hsC.x25, huC.x25, sm.ptr 0]
      · rw [hsC.x26, huC.x26, sm.ptr 1]
      · rw [hsC.x27, huC.x27, sm.ptr 2]
      · rw [hsC.x28, huC.x28, sm.ptr 3]) mr.2.2.2.2 htail ef ff
  exact ⟨by rw [aeq, beq, mr.1, deq], trivial⟩

theorem keyGenH_ct (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    (hw : P.Wf) (hr : Noise.Room P)
    (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Kem16.kgPre P).aarch64Depth ≤ 1)
    (ha : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashCallers.kgAUsing hash P) h).isSome = true)
    (hpre : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgPre P) h).isSome = true)
    (hrow : ∀ i < P.k, ∃ h, ((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Kem16.kgRow P i) h).isSome = true)
    (habs : ∀ blk, 136 * blk < (Kem16.kgSrc P).len → ∃ h, (taint.check (Taint.ofRegs [(Kem16.kgSrc P).r, .x28])
      (.block (Hybrid.absorbBlock (Kem16.kgSrc P) blk)) h).isSome = true)
    (htail : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgTail v.callee P) h).isSome = true) :
    ConstantTime isa (entryContractS (keyGenAArch64S P)).pre (entryContractS (keyGenAArch64S P)).pub
      (Kem16.keyGenH hash v.callee P) := by
  intro s u tr ur t w hs hu hpub et eu
  have ss := preKS hs.1
  have su := preKS hu.1
  have ps : Pre P s := keygen_unstrip (pre_of hw ss.1)
  have pu : Pre P u := keygen_unstrip (pre_of hw su.1)
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have ptr : ∀ i, kA s i = kA u i
    | 0 => hpub.1.1
    | 1 => hpub.1.2.1
    | 2 => hpub.1.2.2.1
    | _+3 => hpub.1.2.2.2.1
  have sp : s.sp = u.sp := hpub.1.2.2.2.2.1
  have rho : rhoK P s = rhoK P u := by
    have hh := map_toNat_inj hpub.1.2.2.2.2.2
    unfold rhoK dB
    rw [ptr_zero, ptr_zero]
    exact hh
  have sym := entryS_symbols hpub
  exact (keyGenH_relCT v hash hG ps pu ⟨ss.2.1, ss.2.2⟩ ⟨su.2.1, su.2.2⟩ hr ts.1 tu.1 ts.2 tu.2
    ⟨ptr, sp, rho⟩ sym.1 sym.2 depthA depthP ha hpre hrow habs htail _ _ _ _ _ _ ⟨rfl, rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.KeyGen
