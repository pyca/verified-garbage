module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads

/-!
# `vg_rsa_crt_values` on PPC64LE: a modulus that is not valid

`fail_ok`: zeros to the three results, and 0 in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (zeroBytes fail)

/-- One result zeroed: the pointer in `rP`, the length in `rL`. -/
theorem failStage_ok {s0 s : State} {m : Mem} (h : Fr s0 m s) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0)
    (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat} (hL : s.gpr rL = BitVec.ofNat 64 L)
    (hrw : (⟨O, L⟩ : Region) ∈ s0.wr) (hds : (⟨O, L⟩ : Region).Disjoint ⟨cvB s0, cvZ s0⟩)
    (hOw : O.toNat + L ≤ 2 ^ 64) (hL1 : 1 ≤ L) (hL2 : L < 2 ^ 32) :
    WP isa (.seq (.block [.addi .r5 rP 0, .addi .r8 rL 0]) zeroBytes) s fun t =>
      Fr s0 m t ∧ (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r8] s t := by
  rw [WP.seq_iff]
  refine WP.mono (mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun v ⟨⟨v5, v8, um⟩, kv⟩ => ?_
  have fv : Fr s0 m v := h.of_mem kv um
  refine WP.mono (zeroBytes_ok (v5.trans hO) (v8.trans hL) hL1 hL2
    (fun c hc => ⟨_, by rw [kv.wr, h.wr]; exact hrw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) hOw)
    fun t ⟨tz, tout, kt⟩ =>
      have tout' : Outside O 0 L s.mem t.mem := fun x hx => (tout x hx).trans (congrFun um x)
      ⟨fv.step (fun x hx => tout x hx) hds kt, tz, tout', (kv.trans kt).mono⟩

/-- `fail`: zeros to `dp`, `dq` and `qinv`, and 0 in `r3`. -/
theorem fail_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) :
    WP isa fail s fun t => Fr s0 s.mem t ∧ t.gpr .r3 = 0 ∧
      (∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r3) c) = 0) ∧
      (∀ c < (PPC64LE.stackArg s0 3).toNat, t.mem (off (s0.gpr .r5) c) = 0) ∧
      (∀ c < (PPC64LE.stackArg s0 1).toNat, t.mem (off (s0.gpr .r7) c) = 0) ∧
      Keep [.r0, .r3, .r5, .r8] s t := by
  obtain ⟨-, -, hwr, d12, d13, -, -, -, -, d1s, -, d23, -, -, -, -, d2s, -, -, -, -, -, d3s, -, -, -, -, -,
    -, w1, w2, w3, -, -, -, -, -, -, p1, p2, q1, q2, e4, e8, e6, -, -, -⟩ := h.pre
  obtain ⟨-, -, -, -, hk'⟩ := pre_scr h.pre
  rw [e4] at d12 d13 d1s w1
  rw [e6] at d12 d23 d2s w2
  rw [e8] at d13 d23 d3s w3
  have hk2 : (s0.gpr .r10).toNat ≤ 1024 := hk'
  have f0 := Fr.of_base h
  rw [fail, wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (failStage_ok f0 (rP := .r14) (rL := .r20) (by decide) (by decide) (by decide) ha.r14
    (by rw [ha.r20]; exact ofNat_toNat64 _) (by rw [hwr, ← e4]; simp) d1s w1 p1 (by omega_arith))
    fun t1 ⟨f1, v1, o1, k1⟩ => ?_
  have a1 := ha.of_keep k1
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (failStage_ok f1 (rP := .r15) (rL := .r22) (by decide) (by decide) (by decide) a1.r15
    (by rw [a1.r22]; exact ofNat_toNat64 _) (by rw [hwr, ← e6]; simp) d2s w2 q1 (by omega_arith))
    fun t2 ⟨f2, v2, o2, k2⟩ => ?_
  have a2 := a1.of_keep k2
  rw [wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (failStage_ok f2 (rP := .r16) (rL := .r20) (by decide) (by decide) (by decide) a2.r16
    (by rw [a2.r20]; exact ofNat_toNat64 _) (by rw [hwr, ← e8]; simp) d3s w3 p1 (by omega_arith))
    fun t3 ⟨f3, v3, o3, k3⟩ => ?_
  rw [show seqs [.block [.li .r3 0]] = .block [.li .r3 0] from rfl]
  have hb4 : WP isa (.block [.li .r3 0]) t3 fun t => (t.gpr .r3 = 0 ∧ t.mem = t3.mem) ∧ Keep [.r3] t3 t := by
    refine WP.keep _ ?_ (by decide)
    prun []
    rfl
  refine WP.mono hb4 fun t ⟨⟨t3', tm⟩, kt⟩ => ⟨f3.of_mem kt tm, t3', fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, (((k1.trans k2).trans k3).trans kt).mono⟩
  · have cc : (⟨s0.gpr .r3, (PPC64LE.stackArg s0 1).toNat⟩ : Region).Contains (off (s0.gpr .r3) c) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [tm, out_of_disjoint o3 d13.symm cc, out_of_disjoint o2 d12.symm cc]
    exact v1 c hc
  · have cc : (⟨s0.gpr .r5, (PPC64LE.stackArg s0 3).toNat⟩ : Region).Contains (off (s0.gpr .r5) c) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [tm, out_of_disjoint o3 d23.symm cc]
    exact v2 c hc
  · rw [tm]; exact v3 c hc

end VG.Proof.Rsa.PPC64LE.CrtValues
