module

public import VerifiedGarbage.Proof.Bignum.AArch64.PrivPreMain
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_private_precompute` on AArch64: correctness

`ppA` states the shared contract on the registers and the stack; the entry
(`ppEntry_ok`), `pre`'s zeroing (`zeroPre_ok`) and the whole function
(`ppCode_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.PrivPre
open VG.Impl.Rsa.AArch64.Crt (nSetup primesSetup checks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `vg_rsa_private_precompute(pre = x0, pre_len = x1, n = x2, n_len = x3,
p = x4, p_len = x5, q = x6, q_len = x7, scratch, scratch_len)`, the last
two on the stack. -/
def ppA : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let p : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let q : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, args] ∧ s.wr = [pre, scr] ∧
      pre.Disjoint n ∧ pre.Disjoint p ∧ pre.Disjoint q ∧ pre.Disjoint scr ∧ pre.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat < (s.gpr .x3).toNat ∧
      1 ≤ (s.gpr .x7).toNat ∧ (s.gpr .x7).toNat < (s.gpr .x3).toNat ∧
      (s.gpr .x1).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    match Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) with
    | some ws => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = ws
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = List.replicate (s.gpr .x1).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat

/-- `w`, `w_p` and `w_q` of a state. -/
abbrev ppW (s : State) : Nat := ((s.gpr .x3).toNat + 7) / 8
abbrev ppWP (s : State) : Nat := wsWords (s.gpr .x5).toNat
abbrev ppWQ (s : State) : Nat := wsWords (s.gpr .x7).toNat
/-- The working space's base and size. -/
abbrev ppB (s : State) : Addr := stackArg s 0
abbrev ppZ (s : State) : Nat := (stackArg s 1).toNat * 8

/-- What `code` uses of its contract's precondition. -/
structure PpCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x3).toNat
  hk2 : (s.gpr .x3).toNat ≤ 1024
  hpl1 : 1 ≤ (s.gpr .x5).toNat
  hpl2 : (s.gpr .x5).toNat < (s.gpr .x3).toNat
  hql1 : 1 ≤ (s.gpr .x7).toNat
  hql2 : (s.gpr .x7).toNat < (s.gpr .x3).toNat
  hpre : (s.gpr .x1).toNat = 2 * ppW s + ppWP s + ppWQ s
  hZ : 128 * (s.gpr .x3).toNat + 256 ≤ ppZ s
  hs : Scr s (ppB s) (ppZ s)
  ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  hnb : Src s (ppB s) (ppZ s) (s.gpr .x2) (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  hpb : Src s (ppB s) (ppZ s) (s.gpr .x4) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
  hqb : Src s (ppB s) (ppZ s) (s.gpr .x6) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
  hpw : ∀ i < (s.gpr .x1).toNat, InRegions s.wr (off (s.gpr .x0) (8 * i)) 8
  hpL : (s.gpr .x1).toNat * 8 ≤ 2 ^ 64
  hps : ∀ x, ofs (ppB s) x < ppZ s → (s.gpr .x1).toNat * 8 ≤ ofs (s.gpr .x0) x
  hnp : ∀ j < (s.gpr .x3).toNat, (s.gpr .x1).toNat * 8 ≤ ofs (s.gpr .x0) (s.gpr .x2 + BitVec.ofNat 64 j)
  hpp : ∀ j < (s.gpr .x5).toNat, (s.gpr .x1).toNat * 8 ≤ ofs (s.gpr .x0) (s.gpr .x4 + BitVec.ofNat 64 j)
  hqp : ∀ j < (s.gpr .x7).toNat, (s.gpr .x1).toNat * 8 ≤ ofs (s.gpr .x0) (s.gpr .x6 + BitVec.ofNat 64 j)
  hpb1 : ∀ j < (s.gpr .x1).toNat * 8, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  hpo : ∀ j < (s.gpr .x1).toNat * 8, ppZ s ≤ ofs (ppB s) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem ppCtx_of {s : State} (h : ppA.pre s) : PpCtx s := by
  simp only [ppA] at h
  obtain ⟨hsp, hrd, hwr, dPn, dPp, dPq, dPs, dPa, dns, dps, dqs, dsa, wP, wN, wPp, wQ, wS, hk, hpl1, hpl2,
    hql1, hql2, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords
    Spec.Rsa.primeWords at hpl
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hpreR : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hargs : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, by simp only [ppW, ppWP, ppWQ, wsWords, Spec.Rsa.modulusWords] at hpl ⊢; omega, by simp only [ppZ]; omega, hs,
    ⟨_, hargs, by simp [Region.Contains]⟩,
    src_of_region (by rw [hrd]; simp) (by omega) dns, src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    fun i hi => ⟨_, hpreR, Offset.contains_base _ (by omega) (by omega)⟩, by omega,
    fun x hx => out_scr dPs.symm (contains_scr hx),
    fun j hj => out_scr dPn.symm (contains_byte _ (by omega) (by omega)),
    fun j hj => out_scr dPp.symm (contains_byte _ (by omega) (by omega)),
    fun j hj => out_scr dPq.symm (contains_byte _ (by omega) (by omega)),
    fun j hj => ⟨_, hpreR, contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dPs (contains_byte _ (by omega) (by omega))⟩

/-! ## The entry -/

/-- The header after the entry's stores. -/
def ppEntryMem (m : Mem) (B : Addr) (vo vn vk vp vpl vq vql : BitVec 64) : Mem :=
  ((((((((((m.writeW (off B (8 * Public.sOut)) vo).writeW (off B (8 * Public.sN)) vn).writeW
    (off B (8 * Public.sK)) vk).writeW (off B (8 * Public.sIn)) vo).writeW (off B (8 * sP)) vp).writeW
    (off B (8 * sPlen)) vpl).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sQlen)) vql).writeW
    (off B (8 * sDp)) vp).writeW (off B (8 * sDq)) vq).writeW (off B (8 * sQinv)) vo

theorem ppEntryMem_facts {m m' : Mem} {B : Addr} {vo vn vk vp vpl vq vql : BitVec 64}
    (hm : m' = ppEntryMem m B vo vn vk vp vpl vq vql) :
    word m' B (8 * Public.sOut) = vo ∧ word m' B (8 * Public.sN) = vn ∧ word m' B (8 * Public.sK) = vk ∧
    word m' B (8 * Public.sIn) = vo ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vp ∧
    word m' B (8 * sDq) = vq ∧ word m' B (8 * sQinv) = vo ∧ Outside B 0 (8 * 32) m m' := by
  subst hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold ppEntryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments; `x8` the working space's base
(stack argument 0), `x9 = 0` and `x10 = pre`. -/
theorem ppEntry_ok {s : State} {B : Addr} (hB : stackArg s 0 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8) (ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block entry) s fun t => t.gpr .x8 = B ∧ t.gpr .x9 = 0 ∧ t.gpr .x10 = s.gpr .x0 ∧
      t.mem = ppEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6)
        (s.gpr .x7) ∧ Keep [.x8, .x9, .x10] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = B := hB
  have hB'' : s.mem.readW s.sp 64 = B := by simpa using hB'
  have ha0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := ha
  have ho : 0 % 8 = 0 ∧ 0 < 32768 := ⟨rfl, by decide⟩
  refine WP.mono (WP.keep [.x8, .x9, .x10] (Q := fun t => t.gpr .x8 = B ∧ t.gpr .x9 = 0 ∧
      t.gpr .x10 = s.gpr .x0 ∧ t.mem = ppEntryMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4)
        (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold entry
  brun [Impl.Rsa.AArch64.Crt.stw, exec_ldrSp ho ha0, hB', hB'', hdr_enc (show Public.sOut < 32 by decide),
    hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
    hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show sP < 32 by decide),
    hdr_enc (show sPlen < 32 by decide), hdr_enc (show sQ < 32 by decide), hdr_enc (show sQlen < 32 by decide),
    hdr_enc (show sDp < 32 by decide), hdr_enc (show sDq < 32 by decide), hdr_enc (show sQinv < 32 by decide),
    hw Public.sOut (by decide), hw Public.sN (by decide), hw Public.sK (by decide), hw Public.sIn (by decide),
    hw sP (by decide), hw sPlen (by decide), hw sQ (by decide), hw sQlen (by decide), hw sDp (by decide),
    hw sDq (by decide), hw sQinv (by decide)]
  rfl

/-! ## `pre := 0` -/

structure ZInv (s₀ : State) (D : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x10] s₀ t
  x10 : t.gpr .x10 = off D (8 * j)
  done : ∀ i < j, word t.mem D (8 * i) = 0
  frame : Outside D 0 (8 * j) s₀.mem t.mem

theorem zStep_ok {s₀ : State} {D : Addr} {L : Nat} (hL : 8 * L ≤ 2 ^ 64) (h9 : s₀.gpr .x9 = 0)
    (hwr : ∀ j < L, InRegions s₀.wr (off D (8 * j)) 8) {j : Nat} (hj : j < L) {t : State} (hI : ZInv s₀ D j t) :
    WP isa (.block ([st .x9 .x10, next .x10] ++ ([.subImm .x .x1 .x1 1] : List Instr))) t
      fun t' => ZInv s₀ D (j + 1) t' ∧ t'.gpr .x1 = t.gpr .x1 - BitVec.ofNat 64 1 := by
  have hst : InRegions t.wr (off D (8 * j)) 8 := by rw [hI.keep.wr]; exact hwr j hj
  have h9' : t.gpr .x9 = 0 := (hI.keep.gpr .x9 (by decide)).trans h9
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x10] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (8 * j)) (0 : BitVec 64) ∧ t₁.gpr .x10 = off D (8 * j + 8))
    (by brun [hI.x10, hst, h9']) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h10⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x1) fun t' ⟨⟨h1, hm', _⟩, k'⟩ => ⟨?_, by rw [h1, k₁.gpr .x1 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x10 (by decide), h10, Nat.mul_succ], fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `zeroPre`: the `L` words at `D` (`x10`) `:= 0` (`x9`), counted by `x1`. -/
theorem zeroPre_ok {s : State} {D : Addr} {L : Nat} (h10 : s.gpr .x10 = D) (h9 : s.gpr .x9 = 0)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (hL0 : 0 < L) (hL : 8 * L ≤ 2 ^ 64)
    (hwr : ∀ j < L, InRegions s.wr (off D (8 * j)) 8) :
    WP isa zeroPre s fun t => (∀ i < L, word t.mem D (8 * i) = 0) ∧ Outside D 0 (8 * L) s.mem t.mem ∧
      Keep [.x1, .x10] s t := by
  have h0 : ZInv s D 0 s := ⟨Keep.refl _ _, by rw [h10]; simp [off], fun i hi => absurd hi (Nat.not_lt_zero _),
    Outside.refl _ _ _ _⟩
  unfold zeroPre
  exact WP.mono (wp_countdown (N := L) (by omega) hL0 (ZInv s D)
    (fun j hj t hI _ => zStep_ok hL h9 hwr hj hI) h0 h1) fun t hI => ⟨hI.done, hI.frame, hI.keep⟩

/-! ## The whole function -/

/-- The bytes of zero words are zero (as PPC64LE's `os2ip_zero_words`). -/
theorem os2ip_zeros' {m : Mem} {P : Addr} {w k : Nat} (hz : ∀ i < w, word m P (8 * i) = 0)
    (hk : k ≤ 8 * w) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P k) = 0 := by
  have hb : ∀ i < k, m (P + BitVec.ofNat 64 i) = 0 := fun i hi => by
    have hw := hz (i / 8) (by omega_arith)
    have := Mem.extractLsb'_read m (P + BitVec.ofNat 64 (8 * (i / 8))) (n := 8) (j := i % 8) (Nat.mod_lt _ (by decide))
    simp only [word, off] at hw
    rw [show m.read (P + BitVec.ofNat 64 (8 * (i / 8))) 8 = m.readW (P + BitVec.ofNat 64 (8 * (i / 8))) 64 from rfl, hw,
      Offset.add_add, show 8 * (i / 8) + i % 8 = i by omega_arith] at this
    rw [← this]; exact BitVec.eq_of_toNat_eq (by simp)
  simp only [Spec.Rsa.bytesAt, Spec.Rsa.os2ip]
  suffices ∀ (l : List Nat) (x : Nat), (∀ i ∈ l, i < k) →
      (l.map fun i => m (P + BitVec.ofNat 64 i)).foldl (fun x b => 256 * x + b.toNat) x = 256 ^ l.length * x by
    have := this (List.range k) 0 (fun i hi => List.mem_range.mp hi)
    rw [this, Nat.mul_zero]
  intro l
  induction l with
  | nil => intro x _; simp
  | cons i l ih =>
    intro x hl
    simp only [List.map_cons, List.foldl_cons]
    rw [hb i (hl i (List.mem_cons_self ..)), ih _ fun j hj => hl j (List.mem_cons_of_mem _ hj)]
    rw [List.length_cons, Nat.pow_succ, Nat.mul_assoc]; rfl

/-- The checks' mask, for the input and `qInv` zero. -/
theorem keyMask_zero {N P Q : Nat} (hN : 1 < N) :
    keyMask (decide (0 < N)) N P Q 0 = decide (P * Q = N) := by
  unfold keyMask
  by_cases h : P * Q = N
  · have hP : 0 < P := Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at h; omega
    simp [h, hP, show 0 < N by omega]
  · simp [h]

/-- A factor of a valid modulus that is shorter than it is more than 1. -/
theorem factor_gt_one {N P Q k ql : Nat} (hpq : P * Q = N) (hN : 256 ^ (k - 1) ≤ N) (hq : Q < 256 ^ ql)
    (hql : ql < k) : 1 < P := by
  rcases Nat.lt_or_ge P 2 with h | h
  · by_cases h0 : P = 0
    · subst h0; rw [Nat.zero_mul] at hpq
      have := Nat.one_le_pow (k - 1) 256 (by decide); omega
    · have h1 : P = 1 := by omega
      subst h1; rw [Nat.one_mul] at hpq; subst hpq
      have := Nat.pow_le_pow_right (n := 256) (by decide) (show ql ≤ k - 1 by omega); omega
  · exact h

/-- Bytes kept, and readable, are the same source. -/
theorem Src.of_bytes {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : ∀ i < bs.length, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i))
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm i hi]; exact h.val i hi, h.out⟩

/-- `pre`'s words, as four numbers. -/
theorem wordsAt_four {m : Mem} {op : Addr} {a b c d x y z u : Nat} (h1 : wv m op 0 a = x)
    (h2 : wv m op (8 * a) b = y) (h3 : wv m op (8 * a + 8 * b) c = z) (h4 : wv m op (8 * a + 8 * b + 8 * c) d = u) :
    Spec.Rsa.wordsAt m op (a + b + c + d) =
      Spec.Rsa.toWords x a ++ Spec.Rsa.toWords y b ++ Spec.Rsa.toWords z c ++ Spec.Rsa.toWords u d := by
  have seg : ∀ (e n v : Nat), wv m op e n = v → ∀ q < n,
      m.readW (op + BitVec.ofNat 64 (e + 8 * q)) 64 = BitVec.ofNat 64 (v / 2 ^ (64 * q)) := fun e n v hv q hq => by
    have := word_eq_ofNat m op e n hq
    rw [hv] at this; exact this
  simp only [Spec.Rsa.wordsAt, Spec.Rsa.toWords, List.range_add, List.map_append, List.map_map, List.append_assoc]
  congr 1
  · exact List.map_congr_left fun q hq => by
      have := seg 0 a x h1 q (List.mem_range.mp hq); rwa [Nat.zero_add] at this
  congr 1
  · exact List.map_congr_left fun q hq => by
      simp only [Function.comp_apply]
      rw [show 8 * (a + q) = 8 * a + 8 * q by omega]; exact seg _ b y h2 q (List.mem_range.mp hq)
  congr 1
  · exact List.map_congr_left fun q hq => by
      simp only [Function.comp_apply]
      rw [show 8 * (a + b + q) = 8 * a + 8 * b + 8 * q by omega]; exact seg _ c z h3 q (List.mem_range.mp hq)
  · exact List.map_congr_left fun q hq => by
      simp only [Function.comp_apply]
      rw [show 8 * (a + b + c + q) = 8 * a + 8 * b + 8 * c + 8 * q by omega]
      exact seg _ d u h4 q (List.mem_range.mp hq)

theorem toWords_zero (n : Nat) : Spec.Rsa.toWords 0 n = List.replicate n 0 := by
  simp only [Spec.Rsa.toWords, Nat.zero_div]
  rw [List.map_const', List.length_range]; rfl

/-- What `head` leaves: `n`'s validity in `x9`, `pre` zero, and `main`'s
hypotheses. -/
structure HeadP (s t : State) : Prop where
  x9 : t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) (s.gpr .x3).toNat).toNat
  zeros : ∀ i < (s.gpr .x1).toNat, word t.mem (s.gpr .x0) (8 * i) = 0
  keep : Keep [.x0, .x1, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] s t
  crt : CrtPre t (ppB s) (ppZ s) (s.gpr .x3).toNat (s.gpr .x0) (s.gpr .x2) (s.gpr .x0) (s.gpr .x4)
    (s.gpr .x6) (s.gpr .x4) (s.gpr .x6) (s.gpr .x0) (s.gpr .x5).toNat (s.gpr .x7).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x5).toNat)

/-- `head`. -/
theorem ppHead_ok {s : State} (c : PpCtx s) : WP isa VG.Impl.Rsa.AArch64.PrivPre.head s (HeadP s) := by
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  have hpre := c.hpre
  have hpL := c.hpL
  have hwr0 := c.hpw
  unfold VG.Impl.Rsa.AArch64.PrivPre.head
  -- The entry.
  refine WP.seq (WP.mono (ppEntry_ok (s := s) (B := ppB s) rfl (fun i hi => c.hs.st (by omega_arith)) c.ha)
    fun t₁ ⟨h8₁, h9₁, h10₁, hm₁, k₁⟩ => ?_)
  obtain ⟨hO₁, hN₁, hK₁, hI₁, hP₁, hPl₁, hQ₁, hQl₁, hDp₁, hDq₁, hQi₁, ho₁⟩ := ppEntryMem_facts hm₁
  -- `pre := 0`.
  refine WP.seq (WP.mono (zeroPre_ok (L := (s.gpr .x1).toNat) h10₁ h9₁
    (by rw [k₁.gpr .x1 (by decide), ofNat_toNat64]) (by simp only [ppW, ppWP, ppWQ, wsWords] at hpre; omega) (by omega)
    (fun j hj => by rw [k₁.wr]; exact hwr0 j hj)) fun t₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hsepP : ∀ x, ofs (ppB s) x < ppZ s → ofs (s.gpr .x0) x < 0 ∨ 0 + 8 * (s.gpr .x1).toNat ≤ ofs (s.gpr .x0) x :=
    fun x hx => Or.inr (by have := c.hps x hx; omega)
  have hw₂ : ∀ d, d + 8 ≤ ppZ s → word t₂.mem (ppB s) d = word t₁.mem (ppB s) d := fun d hd =>
    word_of_pre ho₂ hsepP hd hn
  -- A byte outside the working space and `pre` is kept.
  have hkeep₂ : ∀ x, ppZ s ≤ ofs (ppB s) x → 8 * (s.gpr .x1).toNat ≤ ofs (s.gpr .x0) x → t₂.mem x = s.mem x :=
    fun x h1 h2 => by rw [ho₂ x (Or.inr (by omega)), ho₁ x (Or.inr (by omega))]
  have hsrc : ∀ {p : Addr} {bs : List Byte}, Src s (ppB s) (ppZ s) p bs →
      (∀ i < bs.length, 8 * (s.gpr .x1).toNat ≤ ofs (s.gpr .x0) (p + BitVec.ofNat 64 i)) →
      ∀ {t : State}, t.mem = t₂.mem → t.rd = s.rd → t.wr = s.wr → Src t (ppB s) (ppZ s) p bs :=
    fun hs hp t hm hrd hwr => Src.of_bytes hs (fun i hi => by rw [hm]; exact hkeep₂ _ (hs.out i hi) (hp i hi)) hrd hwr
  -- The modulus' check, from `n`'s base.
  rw [WP.block_append_iff]
  refine (WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = ppB s ∧ t.mem = t₂.mem)
    (by brun [(k₂.gpr .x8 (by decide)).trans h8₁]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h0₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  have hnb₃ := hsrc c.hnb (fun i hi => by
    rw [Nat.mul_comm]; exact c.hnp i (by rw [bytesAt_length] at hi; exact hi)) hm₃ k13.rd k13.wr
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (k13.gpr .x2 (by decide))
    (by rw [k13.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2 (bytesAt_length _ _ _)
    (fun i hi => hnb₃.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₃.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨hz₄, hm₄, _⟩, k₄⟩ => ?_
  have k14 := k13.trans k₄
  have hm42 : t₄.mem = t₂.mem := by rw [hm₄, hm₃]
  have hw₄ : ∀ d, d + 8 ≤ ppZ s → word t₄.mem (ppB s) d = word t₁.mem (ppB s) d := fun d hd => by
    rw [hm42]; exact hw₂ d hd
  have hL8 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat * 8 := by
    simp only [ppW, ppWP, ppWQ, wsWords] at hpre; omega
  have hpl8 : (s.gpr .x5).toNat ≤ (s.gpr .x1).toNat * 8 := by have := c.hpl2; omega
  have hpreS : ∀ {len : Nat}, len ≤ (s.gpr .x1).toNat * 8 →
      Src t₄ (ppB s) (ppZ s) (s.gpr .x0) (Spec.Rsa.bytesAt t₄.mem (s.gpr .x0) len) := fun hl =>
    ⟨fun i hi => by
        rw [bytesAt_length] at hi
        obtain ⟨r, hr, hc⟩ := c.hpb1 i (by omega)
        exact ⟨r, List.mem_append_right _ (by rw [k14.wr]; exact hr), hc⟩,
      fun i hi => by simp [Spec.Rsa.bytesAt],
      fun i hi => c.hpo i (by rw [bytesAt_length] at hi; omega)⟩
  have hpb₄ := hsrc c.hpb (fun i hi => by
    rw [Nat.mul_comm]; exact c.hpp i (by rw [bytesAt_length] at hi; exact hi)) hm42 k14.rd k14.wr
  have hqb₄ := hsrc c.hqb (fun i hi => by
    rw [Nat.mul_comm]; exact c.hqp i (by rw [bytesAt_length] at hi; exact hi)) hm42 k14.rd k14.wr
  have hnb₄ := hsrc c.hnb (fun i hi => by
    rw [Nat.mul_comm]; exact c.hnp i (by rw [bytesAt_length] at hi; exact hi)) hm42 k14.rd k14.wr
  have hsl : ∀ i < 32, 8 * i + 8 ≤ ppZ s := fun i hi => by omega
  have hcp : CrtPre t₄ (ppB s) (ppZ s) (s.gpr .x3).toNat (s.gpr .x0) (s.gpr .x2) (s.gpr .x0) (s.gpr .x4)
      (s.gpr .x6) (s.gpr .x4) (s.gpr .x6) (s.gpr .x0) (s.gpr .x5).toNat (s.gpr .x7).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt t₄.mem (s.gpr .x0) (s.gpr .x3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (Spec.Rsa.bytesAt t₄.mem (s.gpr .x0) (s.gpr .x5).toNat) :=
    { scr := c.hs.congr k14.wr, x0 := (k₄.gpr .x0 (by decide)).trans h0₃,
      z := crt_room hk1 c.hpl2 c.hql2 hZ, zk := by omega, k1 := hk1, k2 := hk2,
      hO := by rw [hw₄ _ (hsl _ (by decide))]; exact hO₁,
      hN := by rw [hw₄ _ (hsl _ (by decide))]; exact hN₁,
      hK := by rw [hw₄ _ (hsl _ (by decide)), hK₁, ofNat_toNat64],
      hIn := by rw [hw₄ _ (hsl _ (by decide))]; exact hI₁,
      hP := by rw [hw₄ _ (hsl _ (by decide))]; exact hP₁,
      hPl := by rw [hw₄ _ (hsl _ (by decide)), hPl₁, ofNat_toNat64],
      hQ := by rw [hw₄ _ (hsl _ (by decide))]; exact hQ₁,
      hQl := by rw [hw₄ _ (hsl _ (by decide)), hQl₁, ofNat_toNat64],
      hDp := by rw [hw₄ _ (hsl _ (by decide))]; exact hDp₁,
      hDq := by rw [hw₄ _ (hsl _ (by decide))]; exact hDq₁,
      hQi := by rw [hw₄ _ (hsl _ (by decide))]; exact hQi₁,
      n := hnb₄, x := hpreS hL8, p := hpb₄, q := hqb₄, dp := hpb₄, dq := hqb₄, qi := hpreS hpl8,
      nl := bytesAt_length _ _ _, xl := bytesAt_length _ _ _, pbl := bytesAt_length _ _ _,
      qbl := bytesAt_length _ _ _, dpl := bytesAt_length _ _ _, dql := bytesAt_length _ _ _,
      qil := bytesAt_length _ _ _, pl1 := c.hpl1, pl2 := c.hpl2, ql1 := c.hql1, ql2 := c.hql2,
      out := fun j hj => by rw [k14.wr]; exact c.hpb1 j (by omega),
      outSep := fun j hj => c.hpo j (by omega) }
  exact ⟨hz₄, fun i hi => by rw [hm42]; exact hz₂ i hi, k14.mono (by decide), hcp⟩

/-- `vg_rsa_private_precompute` with Montgomery multiplication `M`. -/
theorem ppCode_correct (M : Mont) (s : State) (h : ppA.pre s) :
    ∃ t s', Exec isa (code M.mm) s t s' ∧ abiPreserved s s' ∧ ppA.post s s' := by
  have c := ppCtx_of h
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  have hpre := c.hpre
  have hpL := c.hpL
  suffices hwp : WP isa (code M.mm) s fun s' => abiPreserved s s' ∧ ppA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hwr0 := c.hpw
  unfold code
  refine WP.seq (WP.mono (ppHead_ok c) fun t₄ hh => ?_)
  have k14 := hh.keep
  have hcp := hh.crt
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (s.gpr .x3).toNat) (by rw [eval_zero, hh.x9]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false := by simpa using hb
    refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₄.mem) (by brun [])
      (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
    refine ⟨abiPreserved_of_keep ((k14.trans k).mono (by decide)), ?_⟩
    have hnone : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
        none := by
      unfold Spec.Rsa.privatePrecompute
      split
      · simp only [Spec.Rsa.publicPrecompute, bytesAt_length, hv, Bool.false_eq_true, ite_false, Option.map_none]
      · rfl
    simp only [ppA, hnone]
    refine ⟨by rw [h0]; rfl, ?_⟩
    apply List.ext_getElem (by simp [Spec.Rsa.wordsAt])
    intro i hi _
    simp only [Spec.Rsa.wordsAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range] at hi
    rw [hm]
    exact hh.zeros i hi
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true := by simpa using hb
    obtain ⟨hodd, hN1, -⟩ := valid_facts hv hk1
    have hN256 : 256 ^ ((s.gpr .x3).toNat - 1) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) := by
      have := hv; simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
    have hz₄ : ∀ i < (s.gpr .x1).toNat, word t₄.mem (s.gpr .x0) (8 * i) = 0 := hh.zeros
    have hL8 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat * 8 := by
      simp only [ppW, ppWP, ppWQ, wsWords] at hpre; omega
    have hC : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₄.mem (s.gpr .x0) (s.gpr .x3).toNat) = 0 := os2ip_zeros' hz₄ (by omega)
    have hQI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₄.mem (s.gpr .x0) (s.gpr .x5).toNat) = 0 :=
      os2ip_zeros' hz₄ (by have := c.hpl2; omega)
    simp only [main]
    rw [show nSetup M.mm ++ primesSetup ++ checks ++ primes ++ outN =
      (nSetup M.mm ++ primesSetup ++ checks) ++ (primes ++ outN) by simp only [List.append_assoc]]
    refine wp_seqs_append (by simp [nSetup]) (by simp [primes]) (WP.mono (front_ok M hcp hv)
      fun t₅ ⟨minv, mp, mq, hr⟩ => ?_)
    rw [hC, hQI, keyMask_zero hN1] at hr
    have hpl := c.hpl2
    have hql := c.hql2
    refine WP.mono (tail_ok (op := s.gpr .x0) hr (by omega) (by omega) (crt_room hk1 c.hpl2 c.hql2 hZ)
      (wsWords_le (by omega) (by omega)) (wsWords_le (by omega) (by omega))
      ((hr.hfix Public.sOut (by decide) (by decide)).trans hcp.hO)
      (fun h' => factor_gt_one (of_decide_eq_true h') hN256 (by
        have := os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat); rwa [bytesAt_length] at this) hql)
      (fun h' => factor_gt_one (by rw [Nat.mul_comm]; exact of_decide_eq_true h') hN256 (by
        have := os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat); rwa [bytesAt_length] at this) hpl)
      (fun i hi => by rw [hr.keep.wr, k14.wr]; exact hwr0 i (by rw [hpre]; exact hi))
      (by rw [← hpre]; omega) (fun x hx => by rw [← hpre, Nat.mul_comm]; exact c.hps x hx))
      fun t ⟨h1, h2, h3, h4, h0, _, k⟩ => ?_
    refine ⟨abiPreserved_of_keep (((k14.trans hr.keep).trans k).mono (by decide)), ?_⟩
    have e16 : 16 * ((((s.gpr .x3).toNat + 7) / 8)) = 8 * ((((s.gpr .x3).toNat + 7) / 8)) +
        8 * ((((s.gpr .x3).toNat + 7) / 8)) := by omega
    rw [e16] at h3 h4
    have hlen : (s.gpr .x1).toNat = ((s.gpr .x3).toNat + 7) / 8 + ((s.gpr .x3).toNat + 7) / 8 +
        wsWords (s.gpr .x5).toNat + wsWords (s.gpr .x7).toNat := by
      simp only [ppW, ppWP, ppWQ] at hpre; omega
    have hr2 : 2 ^ (64 * (((s.gpr .x3).toNat + 7) / 8)) * 2 ^ (64 * (((s.gpr .x3).toNat + 7) / 8)) =
        2 ^ (128 * (((s.gpr .x3).toNat + 7) / 8)) := by rw [← Nat.pow_add]; congr 1; omega
    rw [hr2] at h2
    simp only [ppA]
    by_cases hpq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) *
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    · have hsome : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
          some (Spec.Rsa.toWords (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
              (((s.gpr .x3).toNat + 7) / 8) ++
            Spec.Rsa.toWords (2 ^ (128 * (((s.gpr .x3).toNat + 7) / 8)) %
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) (((s.gpr .x3).toNat + 7) / 8) ++
            Spec.Rsa.toWords (2 ^ (128 * wsWords (s.gpr .x5).toNat) %
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)) (wsWords (s.gpr .x5).toNat) ++
            Spec.Rsa.toWords (2 ^ (128 * wsWords (s.gpr .x7).toNat) %
              Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) (wsWords (s.gpr .x7).toNat)) := by
        unfold Spec.Rsa.privatePrecompute
        rw [ite_eq_left_of_eq_true _ _ (eq_true hpq), publicPrecompute_some (bytesAt_length _ _ _) hv]
        simp only [Spec.Rsa.primeR2, bytesAt_length, Option.map_some, List.append_assoc]
        rfl
      rw [hsome]
      have hM : decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) = true := decide_eq_true hpq
      simp only [hM, ite_true] at h1 h2 h3 h4 h0
      refine ⟨by rw [h0]; rfl, ?_⟩
      rw [hlen]
      exact wordsAt_four h1 h2 h3 h4
    · have hnone : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
          none := by
        unfold Spec.Rsa.privatePrecompute; rw [ite_eq_right_of_eq_false _ _ (eq_false hpq)]
      rw [hnone]
      have hM : decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) *
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) = false := decide_eq_false hpq
      simp only [hM, Bool.false_eq_true, ite_false] at h1 h2 h3 h4 h0
      refine ⟨by rw [h0]; rfl, ?_⟩
      rw [hlen, wordsAt_four h1 h2 h3 h4]
      simp only [toWords_zero, List.replicate_append_replicate]

end VG.Proof.Bignum.AArch64.PrivPre
