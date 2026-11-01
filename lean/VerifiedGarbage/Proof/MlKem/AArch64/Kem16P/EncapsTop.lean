module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.MatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Start
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
import Mathlib.Data.Nat.Cast.Order.Ring

/-! # The encapsulation computing PRF outputs in the matrix is constant time

`encapsP_ct`: `Kem16P.encaps` is constant time: the first phase, `G` and the
rest by the taint analyses, the matrix around `G` by `matrixP_relCT`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE rhoE mE)
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HInvW HashOk SrcOk Same ekM ekM_ok ekM_base TStk
  encapsAArch64S entryContractS preS entryS_tables entryS_symbols startH_ok)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- The first phase, with what the matrix and `G` need. -/
theorem prefixP {s₀ : State} (hp : Pre P (enL P) s₀) (tables : Tables s₀) (ts : TStk s₀) :
    WP isa (Impl.MlKem.AArch64.Hybrid.startH P) s₀ fun t =>
      HInvW true P (enL P) (ekM P) s₀ t.mem (rhoE P s₀) (ekE P s₀) 0 0 t ∧ MT3 P (enL P) s₀ t ∧
      bytesAt t.mem (sA (enL P) s₀ MB) 32 = mE s₀ := by
  refine WP.mono_syms (WP.tablesDepth (startH_ok hp) tables
    (by unfold Impl.MlKem.AArch64.Hybrid.startH; exact Nat.zero_le _)) fun t ⟨hA, ta⟩ sy => ?_
  have tsA : TStk t := ts.of sy (by rw [hA.kb.sp])
  exact ⟨⟨BInvW.zero hA.kb hA.x24 hA.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hA.zero,
      by rw [ekM_base]; exact hA.kb.ro 0 (show 0 < 2 by decide)⟩,
    ⟨matrix_table_of_kb hp hA.kb ta, by rw [← hA.kb.sp]; exact tsA.shuffle⟩, hA.m⟩

/-- **The encapsulation computing PRF outputs in the matrix is constant time.** -/
theorem encapsP_ct (hash : FixedHash.HashFn) (prf : Nat → Nat → Prog isa) (hw : P.Wf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6 [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩]
      [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
    (hsrc : SrcOk (Impl.MlKem.AArch64.Hybrid.ekSrc P)) (ho : HashOk P (Impl.MlKem.AArch64.Hybrid.ekSrc P))
    (habs : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Hybrid.ekSrc P).len → ∃ h,
      (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Hybrid.ekSrc P).r, .x28])
        (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Hybrid.ekSrc P) blk)) h).isSome = true)
    (ha : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
      (Impl.MlKem.AArch64.Hybrid.startH P) h).isSome = true)
    (hg : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.gAt hash) h).isSome = true)
    (hc : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP prf P
        (Impl.MlKem.AArch64.Kem16P.placed P (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Hybrid.ekSrc P)))
        .x25 0 .x28 MB .x27 0) (.block P.kemEpilogue)) h).isSome = true) :
    ConstantTime isa (entryContractS (encapsAArch64S P)).pre (entryContractS (encapsAArch64S P)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps hash prf P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ss := preS hs.1
  have su := preS hu.1
  have ps := kem_unstrip (Encaps.pre_of hw ss.1)
  have pu := kem_unstrip (Encaps.pre_of hw su.1)
  have rs : ∀ r ∈ [Reg.x0,.x1,.x2,.x3,.x4], s.gpr r = u.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
    · exact hpub.1.2.2.2.2.1
  have ptr : ∀ i < 4, kA s ((enL P).slot i) = kA u ((enL P).slot i) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      exact rs _ (by simp [enL, argReg])
  have sp : s.sp = u.sp := hpub.1.2.2.2.2.2.1
  have rho : rhoE P s = rhoE P u := map_toNat_inj hpub.1.2.2.2.2.2.2
  have sym := entryS_symbols hpub
  have sm : Same (enL P) (ekM P) s u := ⟨ptr 3 (by decide), by rw [ekM_base, ekM_base]; exact ptr 0 (by decide), sp⟩
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have ks : Stk128 P (enL P) s := ⟨ss.2.sp, ss.2.args⟩
  have ku : Stk128 P (enL P) u := ⟨su.2.sp, su.2.args⟩
  have ac := VectorTaint.relRegs [.x0,.x1,.x2,.x3,.x4]
    (P := fun a b => a = s ∧ b = u) (fun a b ⟨ha, hb⟩ => by subst a; subst b; exact ⟨sp, rs⟩) ha.choose_spec
  -- Pointers both runs agree on.
  have regs : ∀ {a b : State}, KB P (enL P) s a → KB P (enL P) u b →
      ∀ r ∈ [Reg.x25,.x26,.x27,.x28], a.gpr r = b.gpr r := by
    intro a b ha hb r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [ha.x25, hb.x25, ptr 0 (by decide)]
    · rw [ha.x26, hb.x26, ptr 1 (by decide)]
    · rw [ha.x27, hb.x27, ptr 2 (by decide)]
    · rw [ha.x28, hb.x28, ptr 3 (by decide)]
  -- The first phase.
  obtain ⟨sA, ta, tb, rfl, ea, eb⟩ := Paired.seq_parts et
  obtain ⟨uA, ua, ub, rfl, fa, fb⟩ := Paired.seq_parts eu
  have aeq := (ac _ _ _ _ _ _ ⟨rfl, rfl⟩ ea fa).1
  have hsA := Paired.exec_post (prefixP ps ts.1 ts.2) ea
  have huA := Paired.exec_post (prefixP pu tu.1 tu.2) fa
  rw [← rho] at huA
  -- `G`, between the pairs hashing `ek` and those computing PRF outputs.
  have between : RelCT isa (fun a b => Hybrid.HRel true P (enL P) (ekM P) s u sA.mem uA.mem (rhoE P s)
      (ekE P s) (ekE P u) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S)
      (Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) a b ∧ a.syms = sA.syms ∧ b.syms = uA.syms)
      (Impl.MlKem.AArch64.Kem16P.gAt hash)
      (PRel P (enL P) s u (rhoE P s) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (ekM P).S) 0) := by
    intro a b tr' ur' a' b' h ea' eb'
    have ga := Paired.exec_post (gStep_ok hash hG ps ks ho ts.1 hsA.2.2 h.1.1 h.1.2.2.1
      (h.2.1.trans (Exec.syms ea))) ea'
    have gb := Paired.exec_post (gStep_ok hash hG pu ku ho tu.1 huA.2.2 h.1.2.1 h.1.2.2.2.1
      (h.2.2.trans (Exec.syms fa))) eb'
    refine ⟨symbol_taint [.x25,.x26,.x27,.x28] (by rw [h.1.1.b.kb.sp, h.1.2.1.b.kb.sp, sm.sp])
      (regs h.1.1.b.kb h.1.2.1.b.kb)
      (fun name hn => by rw [h.2.1, h.2.2, Exec.syms ea, Exec.syms fa]; exact sym.2 name hn) hg ea' eb',
      ⟨_, ga.2.1⟩, ⟨_, gb.2.1⟩, ga.2.2, gb.2.2, ?_⟩
    rw [Exec.syms ea', Exec.syms eb']; exact h.1.2.2.2.2
  -- The matrix.
  obtain ⟨sB, tc, td, rfl, ec, ed⟩ := Paired.seq_parts eb
  obtain ⟨uB, uc, ud, rfl, fc, fd⟩ := Paired.seq_parts fb
  have bm := matrixP_relCT ps pu ks ku (ekM_ok ps ks hsrc) (ekM_ok pu ku hsrc) sm ho habs between
    _ _ _ _ _ _ ⟨⟨hsA.1, huA.1, hsA.2.1, huA.2.1, by rw [Exec.syms ea, Exec.syms fa]; exact sym.1⟩, rfl, rfl⟩ ec fc
  obtain ⟨⟨_, bs⟩, ⟨_, bu⟩, _⟩ := bm.2
  -- The rest.
  have ceq := symbol_taint [.x25,.x26,.x27,.x28] (by rw [bs.b.kb.sp, bu.b.kb.sp, sm.sp]) (regs bs.b.kb bu.b.kb)
    (fun name hn => by rw [Exec.syms ec, Exec.syms fc, Exec.syms ea, Exec.syms fa]; exact sym.2 name hn) hc ed fd
  exact by rw [aeq, bm.1, ceq]

end VG.Proof.MlKem.AArch64.Kem16P
