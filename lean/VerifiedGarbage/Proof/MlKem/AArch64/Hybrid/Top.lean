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
`entryContractS`: with the constant tables apart from them too. `kemH_relCT`:
two runs of the first phase, the matrix (by `matrixH_relCT`) and the rest
(by its taint analysis) leak the same, for `Kem16/EncapsTop.lean`.
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

theorem preS {s : State} (h : (encapsAArch64S P).pre s) : (encapsAArch64 P).pre s ∧ Stk128 P s := by
  obtain ⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp128, k0, k1, k2, k3, k4⟩ := h
  have sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, by omega,
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub, k4.sub_left sub⟩, sp128, ?_⟩
  intro b hb
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
    refine ⟨mem ?_, mem ?_, mem ?_, mem ?_⟩ <;> rw [constants_regions] <;> simp

theorem entryS_tables {base : Contract isa} {s : State} (h : (entryContractS base).pre s) :
    Tables s ∧ TStk s :=
  let c := consts16 h.2
  ⟨tables_of_consts c.1, c.2⟩

/-- The first phase, with what the matrix needs. -/
theorem prefixH {w16 : Bool} {s₀ : State} (hp : Pre P (enL P) s₀) (tables : Tables s₀) (ts : TStk s₀) :
    WP isa (Impl.MlKem.AArch64.Hybrid.startH P) s₀ fun t =>
      HInvW w16 P s₀ t.mem (rhoE P s₀) (ekE P s₀) 0 0 t ∧ MT3 P s₀ t := by
  refine WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun t ⟨hA, ta⟩ sy => ?_
  have tsA : TStk t := ts.of sy (by rw [hA.kb.sp])
  exact ⟨⟨BInvW.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [hstate_zero]; exact hA.zero⟩,
    matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩

theorem kemH_relCT {w16 : Bool} {σ τ : State} {ρ : List Byte} {start rest : Prog isa}
    (hp : Pre P (enL P) σ) (hq : Pre P (enL P) τ) (hk : Stk128 P σ) (hk' : Stk128 P τ)
    (sm : Same P σ τ) (ptr : ∀i<4,kA σ ((enL P).slot i)=kA τ ((enL P).slot i)) (ho : HashOk P)
    (habs : ∀ blk, 136 * blk < P.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock P blk)) h).isSome = true)
    (shuffle : σ.syms "VG_MLKEM_REJ_SHUFFLE"=τ.syms "VG_MLKEM_REJ_SHUFFLE")
    (symbols : ∀name∈restSymbols,σ.syms name=τ.syms name)
    (as : WP isa start σ (fun s=>HInvW w16 P σ s.mem ρ (ekE P σ) 0 0 s ∧ MT3 P σ s))
    (au : WP isa start τ (fun s=>HInvW w16 P τ s.mem ρ (ekE P τ) 0 0 s ∧ MT3 P τ s))
    (ac : RelCT isa (fun s u=>s=σ ∧ u=τ) start (fun _ _=>True))
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) rest h).isSome=true) :
    RelCT isa (fun s u=>s=σ ∧ u=τ) (.seq start (.seq (Impl.MlKem.AArch64.Hybrid.matrixH P w16) rest))
      (fun _ _=>True) := by
  intro s u tr ur t v h et eu
  rcases h with ⟨hs,hu⟩; subst s; subst u
  obtain ⟨sA,ta,tb,rfl,ea,eb⟩ := Paired.seq_parts et
  obtain ⟨uA,ua,ub,rfl,fa,fb⟩ := Paired.seq_parts eu
  have aeq := (ac _ _ _ _ _ _ ⟨rfl,rfl⟩ ea fa).1
  have hs := Paired.exec_post as ea
  have hu := Paired.exec_post au fa
  obtain ⟨sB,tc,td,rfl,ec,ed⟩ := Paired.seq_parts eb
  obtain ⟨uB,uc,ud,rfl,fc,fd⟩ := Paired.seq_parts fb
  have bm := matrixH_relCT hp hq hk hk' sm ho habs _ _ _ _ _ _
    ⟨hs.1,hu.1,hs.2,hu.2,by rw [Exec.syms ea,Exec.syms fa]; exact shuffle⟩ ec fc
  have beq := bm.1
  have bs := bm.2.1.b
  have bu := bm.2.2.1.b
  have ceq := symbol_taint [.x25,.x26,.x27,.x28]
    (by rw [bs.kb.sp,bu.kb.sp,sm.sp]) (fun r hr=>by
      rcases mem4 hr with rfl|rfl|rfl|rfl
      · rw [bs.kb.x25,bu.kb.x25,ptr 0 (by decide)]
      · rw [bs.kb.x26,bu.kb.x26,ptr 1 (by decide)]
      · rw [bs.kb.x27,bu.kb.x27,ptr 2 (by decide)]
      · rw [bs.kb.x28,bu.kb.x28,ptr 3 (by decide)])
    (fun name hn=>by rw [Exec.syms ec,Exec.syms fc,Exec.syms ea,Exec.syms fa]; exact symbols name hn) hc ed fd
  exact ⟨by rw [aeq,beq,ceq],trivial⟩

theorem entryS_symbols {base : Contract isa} {s u : State} (h : (entryContractS base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name :=
  entry_symbols (base := base) h

end VG.Proof.MlKem.AArch64.Hybrid
