module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.MatrixTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Consts
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The hashing encapsulation's contract and constant time

`encapsAArch64S`: `encapsAArch64` with the 128 bytes below the stack pointer
the x3 calls use (rather than 16) apart from the buffers, and
`entryContractS`: with the constant tables apart from them too.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE rhoE)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- `encapsAArch64 P`, with 128 bytes of stack. -/
def encapsAArch64S (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let ek : Region := ⟨s.gpr .x0, P.ekLen⟩
    let msg : Region := ⟨s.gpr .x1, 32⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let ct : Region := ⟨s.gpr .x3, P.ctLen⟩
    let scratch : Region := ⟨s.gpr .x4, P.scl⟩
    let stack : Region := ⟨s.sp - 128, 128⟩
    s.rd = [ek, msg] ∧ s.wr = [key, ct, scratch] ∧ ek.Disjoint key ∧ ek.Disjoint ct ∧
    ek.Disjoint scratch ∧ msg.Disjoint key ∧ msg.Disjoint ct ∧ msg.Disjoint scratch ∧ key.Disjoint ct ∧
    key.Disjoint scratch ∧ ct.Disjoint scratch ∧ 128 ≤ s.sp.toNat ∧ stack.Disjoint ek ∧ stack.Disjoint msg ∧
    stack.Disjoint key ∧ stack.Disjoint ct ∧ stack.Disjoint scratch
  post := (encapsAArch64 P).post
  pub := (encapsAArch64 P).pub

theorem preS {s : State} (h : (encapsAArch64S P).pre s) : (encapsAArch64 P).pre s ∧ Stk128 P (enL P) s := by
  obtain ⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp128, k0, k1, k2, k3, k4⟩ := h
  have sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, by omega,
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub, k4.sub_left sub⟩, sp128, ?_⟩
  intro b hb
  have hb : b < 5 := hb
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl
  · exact k0
  · exact k1
  · exact k2
  · exact k3
  · exact k4

/-- `entryContract`, with the tables apart from 128 bytes of stack. -/
def entryContractS (base : Contract isa) : Contract isa where
  pre s := base.pre (stripConsts constants s) ∧ ConstsOk constants 128 s
  post := base.post
  pub s t := base.pub s t ∧ ∀c∈constants,s.syms c.1=t.syms c.1

theorem consts16 {s : State} (h : ConstsOk constants 128 s) : ConstsOk constants 16 s ∧ TStk s := by
  have sub : Region.Sub ⟨s.sp - BitVec.ofNat 64 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  have st : ∀ t ∈ constRegs constants s, t.Disjoint (frame s.sp) := fun t ht =>
    (h.2.2 t ht).2.2 _ (by simp [abi, stackBelow])
  refine ⟨⟨h.1, h.2.1, fun t ht => ⟨(h.2.2 t ht).1, (h.2.2 t ht).2.1, fun r hr => ?_⟩⟩, ?_⟩
  · simp only [abi, stackBelow, List.mem_singleton] at hr
    subst hr
    exact (st t ht).sub_right sub
  · have mem : ∀ {r : Region}, r ∈ constRegs constants s → r.Disjoint (frame s.sp) := fun hr => st _ hr
    refine ⟨mem ?_, mem ?_, mem ?_, mem ?_, mem ?_⟩ <;> rw [constants_regions] <;> simp [Impl.MlKem.AArch64.Ntt16.Fast.name]

theorem entryS_tables {base : Contract isa} {s : State} (h : (entryContractS base).pre s) :
    Tables s ∧ TStk s :=
  let c := consts16 h.2
  ⟨tables_of_consts c.1, c.2⟩

theorem entryS_symbols {base : Contract isa} {s u : State} (h : (entryContractS base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name :=
  entry_symbols (base := base) h

end VG.Proof.MlKem.AArch64.Hybrid
