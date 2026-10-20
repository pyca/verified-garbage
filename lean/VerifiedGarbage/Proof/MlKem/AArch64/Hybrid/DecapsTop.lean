module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.DecapsStart
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry

/-!
# The hashing decapsulation is constant time

`decapsHW_ct`: `Kem16.decaps` is constant time: the first phase with the
copy of `z ‖ c`, and the rest from `J(z ‖ c)` on, by the taint analyses; the
matrix sampled with 16 bits while it absorbs `z ‖ c` by `matrixH_relCT`
(`kemH_relCT`). `z` and `c` may differ between the runs; only their
pointers are public.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Decaps (deL rhoD)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem

variable {P : KemLay}

/-- **The 16-bit hashing decapsulation is constant time.** -/
theorem decapsHW_ct (hash : FixedHash.HashFn) (prf : Nat→Nat→Prog isa) (hw : P.Wf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    (hc : Calls P) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hsrc : SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P)) (ho : HashOk P (Impl.MlKem.AArch64.Kem16.jSrc P))
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth≤1)
    (habs : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Kem16.jSrc P).len → ∃ h,
      (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Kem16.jSrc P).r, .x28])
        (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Kem16.jSrc P) blk)) h).isSome = true)
    (ha : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (.seq (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P)
        (.block (Impl.MlKem.AArch64.Kem16.startJ P))) h).isSome=true)
    (hr : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (.block Impl.MlKem.AArch64.Kem16.tailJ) (Impl.MlKem.AArch64.Kem16.deRest prf P)) h).isSome=true) :
    ConstantTime isa (entryContractS (decapsAArch64S P)).pre (entryContractS (decapsAArch64S P)).pub
      (Impl.MlKem.AArch64.Kem16.decaps hash prf P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ss := preSD hs.1
  have su := preSD hu.1
  have ps := kem_unstrip (Decaps.pre_of hw ss.1)
  have pu := kem_unstrip (Decaps.pre_of hw su.1)
  have rs : ∀r∈[Reg.x0,.x1,.x2,.x3],s.gpr r=u.gpr r := by
    intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
  have ptr : ∀i<4,kA s ((deL P).slot i)=kA u ((deL P).slot i) := by
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl|rfl|rfl|rfl <;> exact rs _ (by simp [deL,argReg])
  have sp : s.sp=u.sp := hpub.1.2.2.2.2.1
  have rho : rhoD P s=rhoD P u := map_toNat_inj hpub.1.2.2.2.2.2
  have sym := entryS_symbols hpub
  have sm : Same (deL P) (jM P) s u :=
    ⟨ptr 3 (by decide), by rw [jM_base, jM_base]; exact congrArg (· + _) (ptr 3 (by decide)), sp⟩
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have wa := Decaps.prefixJ hash hG ps hc h8 ts.1 ts.2 depthA
  have wb := Decaps.prefixJ hash hG pu hc h8 tu.1 tu.2 depthA
  rw [←rho] at wb
  have ac : RelCT isa (fun a b=>a=s ∧ b=u)
      (.seq (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P)
        (.block (Impl.MlKem.AArch64.Kem16.startJ P))) (fun _ _=>True) := by
    intro a b atr btr a' b' h ea eb
    rcases h with ⟨hsa,hub⟩; subst a; subst b
    exact ⟨symbol_taint [.x0,.x1,.x2,.x3] sp rs sym.2 ha ea eb,trivial⟩
  have ks : Stk128 P (deL P) s := ⟨ss.2.sp, ss.2.args⟩
  have ku : Stk128 P (deL P) u := ⟨su.2.sp, su.2.args⟩
  have k := kemH_relCT ps pu ks ku (jM_ok ps ks hsrc) (jM_ok pu ku hsrc) sm ptr ho habs
    sym.1 sym.2 wa wb ac hr
  exact (RelCT.assoc k _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Hybrid
