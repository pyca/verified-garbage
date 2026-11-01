module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.MatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.DecapsStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix

/-! # The decapsulation computing PRF outputs in the matrix is constant time

`decapsP_ct`: `Kem16P.decaps` is constant time: the first phase with the copy
of `z ‖ c`, `J(z ‖ c)` and the rest by the taint analyses, the matrix around
`J(z ‖ c)` by `matrixP_relCT`. `z` and `c` may differ between the runs; only
their pointers are public. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Decaps (deL rhoD gD mD)
open VG.Proof.MlKem.AArch64.Hybrid (Stk128 MT3 HInvW HashOk SrcOk Same jM jE jM_ok jM_base TStk
  decapsAArch64S entryContractS preSD entryS_tables entryS_symbols)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- The first phase and `z ‖ c` copied to `scratch`, with what the matrix and `J` need. -/
theorem prefixJP (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (tables : Tables s₀) (ts : TStk s₀)
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth ≤ 1) :
    WP isa (.seq (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P)
      (.block (Impl.MlKem.AArch64.Kem16.startJ P))) s₀ fun t =>
      HInvW true P (deL P) (jM P) s₀ t.mem (rhoD P s₀) (jE P s₀) 0 0 t ∧ MT3 P (deL P) s₀ t ∧
      bytesAt t.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1 ∧ bytesAt t.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2 ∧
      bytesAt t.mem (sA (deL P) s₀ MB) 32 = mD P s₀ := by
  have hw := hp.wf
  have scratch0 : Covers [⟨kA s₀ (deL P).sc,P.scl⟩] s₀.wr := by
    have hh := cov_w₀ hp (b:=(deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩
      (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.seq (WP.mono_syms (WP.tablesDepth (Decaps.start_using_ok hash hG hp hc tables.transforms tables.gamma
    tables.gammaRead (Optimized.apart_of_covers tables.gammaApart scratch0)) tables depthA) fun uA ⟨hA,ta⟩ syA=>?_)
  have tsA : TStk uA := ts.of syA (by rw [hA.kb.sp])
  refine WP.mono_syms (WP.tablesDepth (Hybrid.startJ_ok hp h8 hA) ta (Nat.zero_le _))
    fun sJ ⟨hJ,tj⟩ syJ=>?_
  have tsJ : TStk sJ := tsA.of syJ (by rw [hJ.a.kb.sp, hA.kb.sp])
  exact ⟨⟨BInvW.zero hJ.a.kb hJ.a.x24 hJ.a.rho, Frame.refl _ _, by rw [Hybrid.hstate_zero]; exact hJ.zero,
    hJ.msg⟩, ⟨matrix_table_of_kb hp hJ.a.kb tj, by rw [← hJ.a.kb.sp]; exact tsJ.shuffle⟩,
    hJ.a.kp, hJ.a.r, hJ.a.m⟩

/-- **The decapsulation computing PRF outputs in the matrix is constant time.** -/
theorem decapsP_ct (hash : FixedHash.HashFn) (prf : Nat → Nat → Prog isa) (hw : P.Wf)
    (hG : FixedHash.HashCorrect hash .x28 KEM.ST KEM.WK 72 6
      [⟨.x28,KEM.MB,32⟩,⟨.x25,768*P.k+32,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
    (hc : Calls P) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hsrc : SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P)) (ho : HashOk P (Impl.MlKem.AArch64.Kem16.jSrc P))
    (depthA : (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P).aarch64Depth ≤ 1)
    (habs : ∀ blk, 136 * blk < (Impl.MlKem.AArch64.Kem16.jSrc P).len → ∃ h,
      (taint.check (Taint.ofRegs [(Impl.MlKem.AArch64.Kem16.jSrc P).r, .x28])
        (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock (Impl.MlKem.AArch64.Kem16.jSrc P) blk)) h).isSome = true)
    (ha : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (.seq (Impl.MlKem.AArch64.FixedHashDecaps.deStartUsing hash P)
        (.block (Impl.MlKem.AArch64.Kem16.startJ P))) h).isSome = true)
    (hj : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.block Impl.MlKem.AArch64.Kem16.tailJ) h).isSome = true)
    (hr : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.deRestP prf P (Impl.MlKem.AArch64.Kem16P.placed P
        (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc P)))) h).isSome = true) :
    ConstantTime isa (entryContractS (decapsAArch64S P)).pre (entryContractS (decapsAArch64S P)).pub
      (Impl.MlKem.AArch64.Kem16P.decaps hash prf P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ss := preSD hs.1
  have su := preSD hu.1
  have ps := kem_unstrip (Decaps.pre_of hw ss.1)
  have pu := kem_unstrip (Decaps.pre_of hw su.1)
  have rs : ∀ r ∈ [Reg.x0,.x1,.x2,.x3], s.gpr r = u.gpr r := by
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
  have ptr : ∀ i < 4, kA s ((deL P).slot i) = kA u ((deL P).slot i) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
      exact rs _ (by simp [deL, argReg])
  have sp : s.sp = u.sp := hpub.1.2.2.2.2.1
  have rho : rhoD P s = rhoD P u := map_toNat_inj hpub.1.2.2.2.2.2
  have sym := entryS_symbols hpub
  have sm : Same (deL P) (jM P) s u :=
    ⟨ptr 3 (by decide), by rw [jM_base, jM_base]; exact congrArg (· + _) (ptr 3 (by decide)), sp⟩
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have ks : Stk128 P (deL P) s := ⟨ss.2.sp, ss.2.args⟩
  have ku : Stk128 P (deL P) u := ⟨su.2.sp, su.2.args⟩
  have regs : ∀ {a b : State}, KB P (deL P) s a → KB P (deL P) u b →
      ∀ r ∈ [Reg.x25,.x26,.x27,.x28], a.gpr r = b.gpr r := by
    intro a b ha hb r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [ha.x25, hb.x25, ptr 0 (by decide)]
    · rw [ha.x26, hb.x26, ptr 1 (by decide)]
    · rw [ha.x27, hb.x27, ptr 2 (by decide)]
    · rw [ha.x28, hb.x28, ptr 3 (by decide)]
  -- The first phase and the copy of `z ‖ c`.
  obtain ⟨sQ, ta, tb, rfl, ea, eb⟩ := Paired.seq_parts et
  obtain ⟨uQ, ua, ub, rfl, fa, fb⟩ := Paired.seq_parts eu
  obtain ⟨sA, tc, td, rfl, ec, ed⟩ := Paired.seq_parts eb
  obtain ⟨uA, uc, ud, rfl, fc, fd⟩ := Paired.seq_parts fb
  have aeq := symbol_taint [.x0,.x1,.x2,.x3] sp rs sym.2 ha (Exec.seq ea ec) (Exec.seq fa fc)
  have hsA := Paired.exec_post (prefixJP hash hG ps hc h8 ts.1 ts.2 depthA) (Exec.seq ea ec)
  have huA := Paired.exec_post (prefixJP hash hG pu hc h8 tu.1 tu.2 depthA) (Exec.seq fa fc)
  rw [← rho] at huA
  have syA : sA.syms = s.syms := Exec.syms (Exec.seq ea ec)
  have uyA : uA.syms = u.syms := Exec.syms (Exec.seq fa fc)
  -- `J(z ‖ c)`, between the pairs hashing `z ‖ c` and those computing PRF outputs.
  have between : RelCT isa (fun a b => Hybrid.HRel true P (deL P) (jM P) s u sA.mem uA.mem (rhoD P s)
      (jE P s) (jE P u) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S)
      (Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S) a b ∧ a.syms = sA.syms ∧ b.syms = uA.syms)
      (.block Impl.MlKem.AArch64.Kem16.tailJ)
      (PRel P (deL P) s u (rhoD P s) (2 * Impl.MlKem.AArch64.Hybrid.hashPairs (jM P).S) 0) := by
    intro a b tr' ur' a' b' h ea' eb'
    have ga := Paired.exec_post (tailJP_ok ps ks ho hsA.2.2.1 hsA.2.2.2.1 hsA.2.2.2.2 h.1.1 h.1.2.2.1) ea'
    have gb := Paired.exec_post (tailJP_ok pu ku ho huA.2.2.1 huA.2.2.2.1 huA.2.2.2.2 h.1.2.1 h.1.2.2.2.1) eb'
    refine ⟨symbol_taint [.x25,.x26,.x27,.x28] (by rw [h.1.1.b.kb.sp, h.1.2.1.b.kb.sp, sm.sp])
      (regs h.1.1.b.kb h.1.2.1.b.kb)
      (fun name hn => by rw [h.2.1, h.2.2, syA, uyA]; exact sym.2 name hn) hj ea' eb',
      ⟨_, ga.2.1⟩, ⟨_, gb.2.1⟩, ga.2.2, gb.2.2, ?_⟩
    rw [Exec.syms ea', Exec.syms eb']; exact h.1.2.2.2.2
  -- The matrix.
  obtain ⟨sB, te, tf, rfl, ee, ef⟩ := Paired.seq_parts ed
  obtain ⟨uB, ue, uf, rfl, fe, ff⟩ := Paired.seq_parts fd
  have bm := matrixP_relCT ps pu ks ku (jM_ok ps ks hsrc) (jM_ok pu ku hsrc) sm ho habs between
    _ _ _ _ _ _ ⟨⟨hsA.1, huA.1, hsA.2.1, huA.2.1, by rw [syA, uyA]; exact sym.1⟩, rfl, rfl⟩ ee fe
  obtain ⟨⟨_, bs⟩, ⟨_, bu⟩, _⟩ := bm.2
  -- The rest.
  have ceq := symbol_taint [.x25,.x26,.x27,.x28] (by rw [bs.b.kb.sp, bu.b.kb.sp, sm.sp]) (regs bs.b.kb bu.b.kb)
    (fun name hn => by rw [Exec.syms ee, Exec.syms fe, syA, uyA]; exact sym.2 name hn) hr ef ff
  rw [← List.append_assoc ta, ← List.append_assoc ua, aeq, bm.1, ceq]
