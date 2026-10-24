module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_recover_primes` on PPC64LE: zeros written

`zeroOut_ok`: zeros to an output outside the working space; `fail_ok`: to
`p` and `q`, and 0 in `r3`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.Recover (fail)

/-- An output region: writable, apart from the working space. -/
structure OutR (s0 : State) (O : Addr) (L : Nat) : Prop where
  wr : (⟨O, L⟩ : Region) ∈ s0.wr
  disj : (⟨O, L⟩ : Region).Disjoint ⟨rvB s0, rvZ s0⟩
  nowrap : O.toNat + L ≤ 2 ^ 64
  l1 : 1 ≤ L
  l2 : L < 2 ^ 32

/-- Memory in the working space is kept by a write outside it. -/
theorem OutR.inside {s0 : State} {O : Addr} {L : Nat} (h : OutR s0 O L) {m m' : Mem} (o : Outside O 0 L m m') :
    ∀ x, ofs (rvB s0) x < rvZ s0 → m' x = m x := fun x hx =>
  CrtValues.out_of_disjoint o h.disj (by simp only [Region.Contains, ofs] at hx ⊢; omega)

/-- Zeros to the `L` bytes at `O`, from the pointer in `rP` and the length in `rL`. -/
theorem zeroOut_ok {s0 s : State} (h : RFin s0 s) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0)
    (hrL5 : rL ≠ .r5) {O : Addr} (hO : s.gpr rP = O) {L : Nat} (hL : s.gpr rL = BitVec.ofNat 64 L)
    (ho : OutR s0 O L) :
    WP isa (.seq (.block [.addi .r5 rP 0, .addi .r8 rL 0]) VG.Impl.Rsa.PPC64LE.CrtValues.zeroBytes) s fun t =>
      RFin s0 t ∧ (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r8] s t := by
  rw [WP.seq_iff]
  refine WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r5) (d₂ := .r8) hrP hrL hrL5 (by decide))
    fun v ⟨⟨v5, v8, um⟩, kv⟩ => ?_
  refine WP.mono (Keys.zeroBytes_ok (v5.trans hO) (v8.trans hL) ho.l1 ho.l2
    (fun c hc => ⟨_, by rw [kv.wr, h.wr]; exact ho.wr, Offset.contains_base _ (by omega) (by have := ho.nowrap; omega)⟩)
    ho.nowrap) fun t ⟨tz, tout, kt⟩ => ?_
  have tout' : Outside O 0 L s.mem t.mem := fun x hx => (tout x hx).trans (congrFun um x)
  exact ⟨h.of_out (rs := [.r0, .r5, .r8]) (ho.inside tout') (kv.trans kt).mono, tz, tout', (kv.trans kt).mono⟩

/-- `p` and `q` as outputs. -/
theorem out_p {s0 : State} (h : rvP.pre s0) : OutR s0 (s0.gpr .r3) (kK s0) := by
  obtain ⟨-, -, hwr, -, -, -, -, ps, -, -, -, -, -, -, -, -, -, -, wp, -, -, -, -, -, ⟨hk, hk'⟩, e4, -⟩ := h
  rw [e4] at ps wp
  exact ⟨by rw [hwr]; simp [e4, kK], ps, wp, by simp only [kK]; omega, by simp only [kK]; omega⟩

theorem out_q {s0 : State} (h : rvP.pre s0) : OutR s0 (s0.gpr .r5) (kK s0) := by
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, qs, -, -, -, -, -, -, wq, -, -, -, -, ⟨hk, hk'⟩, -, e6, -⟩ := h
  rw [e6] at qs wq
  exact ⟨by rw [hwr]; simp [e6, kK], qs, wq, by simp only [kK]; omega, by simp only [kK]; omega⟩

theorem pq_disj {s0 : State} (h : rvP.pre s0) :
    (⟨s0.gpr .r3, kK s0⟩ : Region).Disjoint ⟨s0.gpr .r5, kK s0⟩ := by
  obtain ⟨-, -, -, pq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e4, e6, -⟩ := h
  rw [e4, e6] at pq
  exact pq

/-- `fail`: zeros to `p` and `q`, and 0 in `r3`. -/
theorem fail_ok {s0 s : State} (h : RFin s0 s) (h21 : s.gpr .r21 = s0.gpr .r3) (h23 : s.gpr .r23 = s0.gpr .r5)
    (h25 : s.gpr .r25 = s0.gpr .r8) :
    WP isa fail s fun t => RFin s0 t ∧ t.gpr .r3 = 0 ∧
      (∀ c < kK s0, t.mem (off (s0.gpr .r3) c) = 0) ∧ (∀ c < kK s0, t.mem (off (s0.gpr .r5) c) = 0) ∧
      Keep [.r0, .r3, .r5, .r8] s t := by
  have op := out_p h.pre
  have oq := out_q h.pre
  have dpq := pq_disj h.pre
  rw [fail, CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok h (rP := .r21) (rL := .r25) (by decide) (by decide) (by decide) h21
    (by rw [h25]; exact CrtValues.ofNat_toNat64 _) op) fun t1 ⟨f1, v1, _, k1⟩ => ?_
  rw [CrtValues.wp_seqs_pair (List.cons_ne_nil _ _)]
  refine WP.mono (zeroOut_ok f1 (rP := .r23) (rL := .r25) (by decide) (by decide) (by decide)
    (by rw [k1.gpr _ (by decide), h23]) (by rw [k1.gpr _ (by decide), h25]; exact CrtValues.ofNat_toNat64 _) oq)
    fun t2 ⟨f2, v2, o2, k2⟩ => ?_
  rw [show seqs [.block [.li .r3 0]] = .block [.li .r3 0] from rfl]
  have hb : WP isa (.block [.li .r3 0]) t2 fun t => (t.gpr .r3 = 0 ∧ t.mem = t2.mem) ∧ Keep [.r3] t2 t := by
    refine WP.keep _ ?_ (by decide)
    prun []
    rfl
  refine WP.mono hb fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨f2.of_out (fun x _ => congrFun tm x) kt, t3, fun c hc => ?_,
    fun c hc => by rw [tm]; exact v2 c hc, ((k1.trans k2).trans kt).mono⟩
  have cc : (⟨s0.gpr .r3, kK s0⟩ : Region).Contains (off (s0.gpr .r3) c) 1 :=
    Offset.contains_base _ (by omega) (by have := op.nowrap; omega)
  rw [tm, CrtValues.out_of_disjoint o2 dpq.symm cc]
  exact v1 c hc

end VG.Proof.Rsa.PPC64LE.Recover
