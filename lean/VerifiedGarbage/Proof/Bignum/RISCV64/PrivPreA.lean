module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreFront
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtLoad
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPrePQ
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the checks

`partA_ok`: from the entry, `save`, `args`, `zeroIn`, `setupX` and
`vg_rsa_private_crt`'s `loadX` and `checks`, with `pre` (its first words
zero) as the input and `qInv`: the mask of `n` valid and `p q = n`
(`privMask`, `crtMask_zero`) in the header's `oMask`, and `p` and `q` (or 3)
in `X`'s arrays 4 and 5 (`A`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Frm)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf wordsOf_ge wordsOf_le two_le_wordsOf Buf crtMask checksWith_ok loadX_ok
  setupX_ok Chk chkRegs loadXRegs frm_mid bytesAt_out savW)

/-- The mask of `vg_rsa_private_precompute`: `n` valid and `p q = n`. -/
def privMask (N k P Q : Nat) : Bool := Spec.Rsa.modulusValid N k && decide (P * Q = N)

/-- With the input and `qInv` zero, the CRT's checks are `n` valid and
`p q = n`. -/
theorem crtMask_zero (N k P Q : Nat) : crtMask N k 0 P Q 0 = privMask N k P Q := by
  unfold crtMask privMask
  cases hv : Spec.Rsa.modulusValid N k
  · simp
  · have hN : 2 ^ 511 ≤ N := by
      unfold Spec.Rsa.modulusValid at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
      exact hv.1.1.2
    by_cases h : P * Q = N
    · have hP : 0 < P := Nat.pos_of_ne_zero fun e => by
        rw [e, Nat.zero_mul] at h; have := Nat.one_le_two_pow (n := 511); omega_arith
      simp [h, hP, show 0 < N by omega_arith]
    · simp [h]

/-- The bytes of zero words are zero. -/
theorem os2ip_zero_words {m : Mem} {P : Addr} {w k : Nat} (hz : ∀ i < w, Mont.word m P (8 * i) = 0)
    (hk : k ≤ 8 * w) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P k) = 0 := by
  have hb : ∀ i < k, m (P + BitVec.ofNat 64 i) = 0 := fun i hi => by
    have hw := hz (i / 8) (by omega_arith)
    have := Mem.extractLsb'_read m (P + BitVec.ofNat 64 (8 * (i / 8))) (n := 8) (j := i % 8) (Nat.mod_lt _ (by decide))
    simp only [Mont.word, Mont.off] at hw
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

/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * cw s
/-- `p`'s and `q`'s lengths. -/
abbrev cpL (s : State) : Nat := (s.gpr .a5).toNat
abbrev cqL (s : State) : Nat := (s.gpr .a7).toNat
/-- `n`, `p` and `q` as numbers. -/
abbrev cN (s : State) : Nat := Spec.Rsa.os2ip (nB s)
abbrev cP (s : State) : Nat := Spec.Rsa.os2ip (pB s)
abbrev cQ (s : State) : Nat := Spec.Rsa.os2ip (qB s)
/-- The mask. -/
abbrev cb (s : State) : Bool := privMask (cN s) (ck s) (cP s) (cQ s)

/-- What the precondition gives. -/
structure PF (s₀ : State) : Prop where
  k64 : 64 ≤ ck s₀
  k1024 : ck s₀ ≤ 1024
  p1 : 1 ≤ cpL s₀
  pk : cpL s₀ < ck s₀
  q1 : 1 ≤ cqL s₀
  qk : cqL s₀ < ck s₀
  room : slot (cwX s₀) 8 + slot (wordsOf (cpL s₀)) 24 + slot (wordsOf (cqL s₀)) 24 ≤ cZ s₀
  nw : (cS s₀).toNat + cZ s₀ ≤ 2 ^ 64
  al : (cS s₀).toNat % 8 = 0
  preLen : (s₀.gpr .a1).toNat = 2 * cw s₀ + wordsOf (cpL s₀) + wordsOf (cqL s₀)
  pre : Scr s₀ (s₀.gpr .a0) ((s₀.gpr .a1).toNat * 8)
  sepPre : ∀ x, ofs (s₀.gpr .a0) x < (s₀.gpr .a1).toNat * 8 → cZ s₀ ≤ ofs (cS s₀) x
  rN : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a2) i) 1
  sN : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a2) i ≠ x
  rP : ∀ i < cpL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a4) i) 1
  sP : ∀ i < cpL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a4) i ≠ x
  rQ : ∀ i < cqL s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a6) i) 1
  sQ : ∀ i < cqL s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a6) i ≠ x
  rPre : ∀ i < ck s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .a0) i) 1
  sPre : ∀ i < ck s₀, ∀ x, ofs (cS s₀) x < cZ s₀ → off (s₀.gpr .a0) i ≠ x
  dN : ∀ r ∈ [preR s₀, scrR s₀], (nR s₀).Disjoint r

theorem wordsOf_eq (len : Nat) : wordsOf len = Spec.Rsa.primeWords len := by
  unfold wordsOf Spec.Rsa.primeWords Spec.Rsa.modulusWords; split <;> omega_arith

theorem pre_facts {s₀ : State} (h : fnContract.pre s₀) : PF s₀ := by
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords,
    ← wordsOf_eq] at hpl
  have hk8 : ck s₀ ≤ (s₀.gpr .a1).toNat * 8 := by
    show (s₀.gpr .a3).toNat ≤ _; rw [hpl]; have := wordsOf_ge (l := (s₀.gpr .a5).toNat); omega_arith
  have dPS' : (⟨s₀.gpr .a0, (s₀.gpr .a1).toNat * 8⟩ : Region).Disjoint ⟨cS s₀, cZ s₀⟩ := dPS
  refine ⟨hk, hk', hp1, hpk, hq1, hqk, ?_, nwS, alS, hpl,
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..) nwPre alPre,
    Pub.sep_of_disjoint dPS',
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_self ..) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dNS (Nat.le_of_lt (BitVec.isLt _)),
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dpS (Nat.le_of_lt (BitVec.isLt _)),
    Crt.rd_of_mem (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (Nat.le_refl _) (BitVec.isLt _),
    Pub.ne_of_disjoint dqS (Nat.le_of_lt (BitVec.isLt _)),
    fun i hi => ⟨preR s₀, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => Pub.ne_of_disjoint dPS' (by omega_arith) i (by omega_arith), fun r hr => ?_⟩
  · show slot (2 * (((s₀.gpr .a3).toNat + 7) / 8)) 8 + slot (wordsOf (s₀.gpr .a5).toNat) 24 +
      slot (wordsOf (s₀.gpr .a7).toNat) 24 ≤ (stackArg s₀ 1).toNat * 8
    have := wordsOf_le (l := (s₀.gpr .a5).toNat)
    have := wordsOf_le (l := (s₀.gpr .a7).toNat)
    unfold slot hdrBytes; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dPN.symm
    · exact dNS

/-- The registers written up to `setupX`. -/
def a0Regs : List Reg := [.t0, .s6, .t3, .s0, .t5, .t2, .t4, .a7, .ra, .s5, .s11]

/-- What holds after `setupX`, from the entry state `s₀`. -/
structure A0 (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hIn : Mont.word s.mem (cS s₀) oIn = s₀.gpr .a0
  hP : Mont.word s.mem (cS s₀) oP = s₀.gpr .a4
  hPL : Mont.word s.mem (cS s₀) oPLen = s₀.gpr .a5
  hQ : Mont.word s.mem (cS s₀) oQ = s₀.gpr .a6
  hQL : Mont.word s.mem (cS s₀) oQLen = s₀.gpr .a7
  hQI : Mont.word s.mem (cS s₀) oQInv = s₀.gpr .a0
  hBP : Mont.word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ =
    Mont.off (cS s₀) (slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)))
  s6 : s.gpr .s6 = cS s₀
  a7 : s.gpr .a7 = off (cS s₀) (slot (cwX s₀) 0)
  ra : s.gpr .ra = off (cS s₀) (slot (cwX s₀) 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 (cwX s₀)
  keep : Keep a0Regs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem
  wz : ∀ i < cw s₀, Mont.word s.mem (s₀.gpr .a0) (8 * i) = 0

/-- From the entry to `setupX`. -/
theorem partA0_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ x, A0 s₀ x → WP isa c x Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX) c))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  have hP := pre_facts hpre0
  have room := hP.room
  have hscr : Scr s₀ (cS s₀) (cZ s₀) :=
    Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS alS
  have hn := hscr.nowrap
  have hZ : 256 + 112 ≤ cZ s₀ := by unfold slot hdrBytes at room; omega_arith
  have hZ' : 368 ≤ (stackArg s₀ 1).toNat * 8 := hZ
  have hargs : argsR s₀ ∈ s₀.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 :=
    ⟨_, List.mem_append_left _ hargs, by
      have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  have esav : ∀ i, off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := fun i => by
    simp only [off, savW]; rw [Offset.add_add]
  have hsavR : ∀ i < 13, (scrR s₀).Contains (off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [esav]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hsavA : ∀ i < 13, (off (savW (cS s₀)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [esav]; exact hscr.al8 (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ rfl hst (by omega_arith)
    (fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), hsavR i hi⟩) hsavA)
    fun t hSv => ?_
  have kt := hSv.keep
  refine WP.mono (args_ok (hscr.congr kt.2.2) (by omega_arith) (by rw [hSv.s6]; exact (BitVec.add_zero _).symm))
    fun u ⟨⟨hA, Ou⟩, ku⟩ => ?_
  have ktu := kt.trans ku
  have g : ∀ r, r ∉ [Reg.t0, .s6] → t.gpr r = s₀.gpr r := fun r hr => kt.gpr hr
  -- Changes within the working space or `pre`, as frames.
  have frS : ∀ {m m' : Mem} {o n : Nat}, Outside (cS s₀) o n m m' → o + n ≤ cZ s₀ →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
    omega_arith
  have frP : ∀ {m m' : Mem} {o n : Nat}, Outside (s₀.gpr .a0) o n m m' → o + n ≤ (s₀.gpr .a1).toNat * 8 →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (preR s₀) (List.mem_cons_self ..)
    simp only [Region.Contains, ofs] at this ⊢
    omega_arith
  have F1 : Frame [preR s₀, scrR s₀] s₀.mem u.mem := by
    refine (hSv.frame.sub fun r hr => ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (frS Ou (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Crt.savR, savW]
    rw [show cS s₀ + BitVec.ofNat 64 112 = off (cS s₀) 112 from rfl]
    exact Offset.sub_base _ (by omega_arith)
  -- `zeroIn`.
  have hw1 : 1 ≤ cw s₀ := by simp only [cw, ck]; omega_arith
  have hcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have u0 : u.gpr .a0 = s₀.gpr .a0 := (ku.gpr (by decide)).trans (g _ (by decide))
  have u3 : u.gpr .a3 = BitVec.ofNat 64 (ck s₀) := by
    rw [ku.gpr (by decide), g _ (by decide)]; exact (Pre.ofNat_toNat64 _).symm
  obtain ⟨K, hK⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  rw [hK] at u3
  have hK' : (s₀.gpr .a3).toNat = K := hK
  refine WP.seq ?_
  unfold PrivPre.zeroIn
  refine WP.seq (WP.mono (WP.keep [.t3, .t0] (Q := fun v => v.gpr .t3 = off (s₀.gpr .a0) 0 ∧
      v.gpr .t0 = BitVec.ofNat 64 (2 * cw s₀) ∧ v.mem = u.mem) (by
        brun [u0, u3, BitVec.ofNat_add_ofNat, Pre.ofNat_add7_shr3 K (by omega_arith),
          Crt.ofNat_shl _ _ (show 1 < 64 by decide), Nat.reducePow]
        rw [Crt.ofNat_shr3 (K + 7) (by omega_arith), Crt.ofNat_shl _ _ (show 1 < 64 by decide)]
        exact congrArg _ (by simp only [cw, hK])) (by rfl) (by rfl)) fun v₁ ⟨⟨z3, z0, zm⟩, zk⟩ => ?_)
  refine WP.mono (zeroWords_ok (hP.pre.congr (ktu.trans zk).2.2) z3 z0 (by omega_arith) (by omega_arith)
    (by decide) (by rw [hP.preLen]; omega_arith))
    fun v ⟨⟨_, vz, vo⟩, vk⟩ => ?_
  rw [zm] at vo
  have kv := (ktu.trans zk).trans vk
  have hPS : ∀ x, ofs (cS s₀) x < cZ s₀ → (s₀.gpr .a1).toNat * 8 ≤ ofs (s₀.gpr .a0) x := fun x hx => by
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [ofs, cS, cZ] at hx; omega_arith)
  have hhv : ∀ d, d + 8 ≤ cZ s₀ → Mont.word v.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd =>
    Mem.readW_congr fun i hi => vo _ (Or.inr (by
      have := hPS (off (cS s₀) d + BitVec.ofNat 64 i) (by rw [ofs_off _ (by omega_arith)]; omega_arith)
      rw [hP.preLen] at this
      exact Nat.le_trans (by omega_arith) this))
  have F2 : Frame [preR s₀, scrR s₀] s₀.mem v.mem := F1.trans (frP vo (by rw [hP.preLen]; omega_arith))
  -- `setupX`.
  have v6 : v.gpr .s6 = cS s₀ := by
    rw [vk.gpr (by decide), zk.gpr (by decide), ku.gpr (by decide)]; exact hSv.s6
  refine WP.seq (WP.mono (setupX_ok (k := ck s₀) (pl := cpL s₀) (hscr.congr kv.2.2) (by omega_arith)
    (by rw [v6]; exact (BitVec.add_zero _).symm)
    (by rw [kv.gpr (by decide)]; exact (Pre.ofNat_toNat64 _).symm) (by omega_arith) hk'
    (by rw [hhv _ (by unfold oPLen; omega_arith), hA.pLen, g _ (by decide)]; exact (Pre.ofNat_toNat64 _).symm)
    hp1 (by show (s₀.gpr .a5).toNat ≤ 1024; omega_arith))
    fun x ⟨⟨x7, xra, x5, x11, x0, xBP, xBQ, Ox⟩, kx⟩ => ?_)
  have kx' := kv.trans kx
  have F3 : Frame [preR s₀, scrR s₀] s₀.mem x.mem := F2.trans (frS Ox (by unfold oBP; omega_arith))
  have hx : ∀ d, d + 8 ≤ 96 → Mont.word x.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd => by
    rw [Ox.word (Or.inl (by unfold oBP; omega_arith)) (by omega_arith), hhv d (by omega_arith)]
  refine hc x ⟨hscr.congr kx'.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, xBP, xBQ,
    (kx.gpr (by decide)).trans v6, x7, xra, x5, x11, x0, kx'.mono (by decide), fun i hi => ?_, F3, fun i hi => ?_⟩
  · rw [hx _ (by decide), hA.out, g _ (by decide)]
  · rw [hx _ (by decide), hA.n, g _ (by decide)]
  · rw [hx _ (by decide), hA.nLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.inp, g _ (by decide)]
  · rw [hx _ (by decide), hA.p, g _ (by decide)]
  · rw [hx _ (by decide), hA.pLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.q, g _ (by decide)]
  · rw [hx _ (by decide), hA.qLen, g _ (by decide)]
  · rw [hx _ (by decide), hA.qinv, g _ (by decide)]
  · have h1 := hSv.saved i hi
    change x.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _
    change t.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _ at h1
    rw [esav] at h1 ⊢
    change Mont.word x.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [Ox.word (Or.inr (by unfold oBP; omega_arith)) (by omega_arith), hhv _ (by omega_arith),
      Ou.word (Or.inr (by omega_arith)) (by omega_arith)]
    exact h1
  · rw [← vz i (by omega_arith), Nat.zero_add]
    refine Mem.readW_congr fun j hj => Ox _ (Or.inr ?_)
    have := hP.sepPre (off (s₀.gpr .a0) (8 * i) + BitVec.ofNat 64 j) (by
      rw [ofs_off _ (by omega_arith), hP.preLen]; omega_arith)
    exact Nat.le_trans (by unfold oBP; omega_arith) this

/-- A buffer apart from what changed is as it was. -/
theorem bytes_frame {m m' : Mem} {rs : List Region} (F : Frame rs m m') {A : Addr} {L : Nat}
    (hd : ∀ r ∈ rs, (⟨A, L⟩ : Region).Disjoint r) (hL : L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A L = Spec.Rsa.bytesAt m A L := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => F.bytes (R := ⟨A, L⟩) hd hL (List.mem_range.mp hi)

/-- Changes within the working space, as a frame. -/
theorem frame_of_frm {s₀ : State} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (cS s₀) rs m m')
    (hZ : ∀ r ∈ rs, r.1 + r.2 ≤ cZ s₀) : Frame [preR s₀, scrR s₀] m m' := fun x hx =>
  h x fun r hr => Or.inr (by
    have h1 := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have h2 := hZ r hr
    simp only [Region.Contains, ofs, cS, cZ] at h1 h2 ⊢
    omega_arith)

theorem frame_of_outside {s₀ : State} {o n : Nat} {m m' : Mem} (h : Outside (cS s₀) o n m m')
    (hZ : o + n ≤ cZ s₀) : Frame [preR s₀, scrR s₀] m m' :=
  frame_of_frm (rs := [(o, n)]) (Frm.of_outside h (List.mem_singleton_self _))
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hZ

/-- The registers written up to the checks. -/
def aRegs : List Reg := a0Regs ++ loadXRegs ++ [.a3, .t1] ++ chkRegs

/-- What holds after the checks, from the entry state `s₀`. -/
structure A (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : Mont.word s.mem (cS s₀) oOut = s₀.gpr .a0
  hN : Mont.word s.mem (cS s₀) oN = s₀.gpr .a2
  hNL : Mont.word s.mem (cS s₀) oNLen = s₀.gpr .a3
  hPL : Mont.word s.mem (cS s₀) oPLen = s₀.gpr .a5
  hQL : Mont.word s.mem (cS s₀) oQLen = s₀.gpr .a7
  hBP : Mont.word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : Mont.word s.mem (cS s₀) oBQ =
    Mont.off (cS s₀) (slot (2 * ((ck s₀ + 7) / 8)) 8 + hdrBytes + 24 * (8 * (wordsOf (cpL s₀) + 2)))
  hMask : Mont.word s.mem (cS s₀) oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  s6 : s.gpr .s6 = cS s₀
  s11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 4) (cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : wordsVal s.mem (cS s₀) (slot (cwX s₀) 5) (cwX s₀) = if cb s₀ then cQ s₀ else 3
  keep : Keep aRegs s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

/-- From the entry to the checks. -/
theorem partA_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, A s₀ t → WP isa c t Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX)
      (.seq Crt.loadX (.seq (.block PrivPre.pqLens) (.seq (Crt.checksWith PrivPre.checkPQs) c)))))) s₀ Q := by
  have hpre0 := h
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl, alPre, alS, alSp⟩ := h
  have hP := pre_facts hpre0
  have hn := hP.nw
  have room := hP.room
  refine partA0_ok hpre0 fun x X => ?_
  have dck : ck s₀ = (s₀.gpr .a3).toNat := rfl
  have dcpL : cpL s₀ = (s₀.gpr .a5).toNat := rfl
  have dcqL : cqL s₀ = (s₀.gpr .a7).toNat := rfl
  have dcw : cw s₀ = ((s₀.gpr .a3).toNat + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  have eX2 := e (cwX s₀) 2
  have hcw : cwX s₀ = 2 * (((s₀.gpr .a3).toNat + 7) / 8) := rfl
  have hwP := wordsOf_ge (l := cpL s₀)
  have hwQ := wordsOf_ge (l := cqL s₀)
  have hZ8 : slot (cwX s₀) 8 ≤ cZ s₀ := by omega_arith
  have hwX : cwX s₀ < 2 ^ 31 := by omega_arith
  have rd0 : x.rd ++ x.wr = s₀.rd ++ s₀.wr := by rw [X.keep.2.1, X.keep.2.2]
  have z : ∀ a : Addr, a = off a 0 := fun a => (BitVec.add_zero a).symm
  have dis : ∀ {A : Addr} {L : Nat}, (preR s₀).Disjoint ⟨A, L⟩ → (⟨A, L⟩ : Region).Disjoint (scrR s₀) →
      ∀ r ∈ [preR s₀, scrR s₀], (⟨A, L⟩ : Region).Disjoint r := fun h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h1.symm
    · exact h2
  have bN : Spec.Rsa.bytesAt x.mem (s₀.gpr .a2) (ck s₀) = nB s₀ :=
    bytes_frame X.frame (dis dPN dNS) (Nat.le_of_lt (BitVec.isLt _))
  have bP : Spec.Rsa.bytesAt x.mem (s₀.gpr .a4) (cpL s₀) = pB s₀ :=
    bytes_frame X.frame (dis dPP dpS) (Nat.le_of_lt (BitVec.isLt _))
  have bQ : Spec.Rsa.bytesAt x.mem (s₀.gpr .a6) (cqL s₀) = qB s₀ :=
    bytes_frame X.frame (dis dPQ dqS) (Nat.le_of_lt (BitVec.isLt _))
  have bI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .a0) (ck s₀)) = 0 :=
    os2ip_zero_words X.wz (by simp only [cw]; omega_arith)
  have bQI : Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (s₀.gpr .a0) (cpL s₀)) = 0 :=
    os2ip_zero_words X.wz (by simp only [cw]; omega_arith)
  -- `X`'s arrays.
  refine WP.seq (WP.mono (loadX_ok (Na := s₀.gpr .a2) (Pa := s₀.gpr .a4) (Qa := s₀.gpr .a6) (Ia := s₀.gpr .a0)
    (QIa := s₀.gpr .a0) (k := ck s₀) (pL := cpL s₀) (qL := cqL s₀) X.scr hZ8 (by omega_arith) hwX
    (by rw [X.s6]; exact z _) X.a7 X.ra X.s5 X.t0 (by rw [X.hN]; exact z _)
    (by rw [X.hNL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hP]; exact z _)
    (by rw [X.hPL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hQ]; exact z _)
    (by rw [X.hQL]; exact (Pre.ofNat_toNat64 _).symm) (by rw [X.hIn]; exact z _) (by rw [X.hQI]; exact z _)
    (by omega_arith) (by omega_arith) hp1 (by omega_arith) hq1 (by omega_arith)
    ⟨by rw [rd0]; exact hP.rN, hP.sN⟩ ⟨by rw [rd0]; exact hP.rP, hP.sP⟩ ⟨by rw [rd0]; exact hP.rQ, hP.sQ⟩
    ⟨by rw [rd0]; exact hP.rPre, hP.sPre⟩
    ⟨fun i hi => by rw [rd0]; exact hP.rPre i (by omega_arith), fun i hi => hP.sPre i (by omega_arith)⟩)
    fun t₁ ⟨⟨v0, w0, v1, v4, v5, v6, v7, t1, t4, t5, t6, t7, O1, a7₁⟩, k1⟩ => ?_)
  rw [bN] at v1
  rw [bP] at v4
  rw [bQ] at v5
  rw [bI] at v6
  rw [bQI] at v7
  have F1 : Frame [preR s₀, scrR s₀] s₀.mem t₁.mem := X.frame.trans (frame_of_outside O1 (by omega_arith))
  have hQb := Crt.os2ip_lt' (qB s₀) (VG.Proof.Bignum.bytesAt_length _ _ _)
  have hPb := Crt.os2ip_lt' (pB s₀) (VG.Proof.Bignum.bytesAt_length _ _ _)
  have hw16 : 16 * ck s₀ ≤ 64 * cwX s₀ := by omega_arith
  have hd1 : ∀ d, d + 8 ≤ 256 → Mont.word t₁.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd =>
    O1.word (Or.inl hd) (by omega_arith)
  -- The factors' widths.
  have hs₁ := X.scr.congr k1.2.2
  have r6 : t₁.gpr .s6 = cS s₀ := (k1.gpr (by decide)).trans X.s6
  have rPL : t₁.mem.readW (off (cS s₀) oPLen) 64 = BitVec.ofNat 64 (cpL s₀) := by
    rw [show t₁.mem.readW (off (cS s₀) oPLen) 64 = Mont.word t₁.mem (cS s₀) oPLen from rfl,
      hd1 _ (by unfold oPLen; omega_arith), X.hPL]; exact (Pre.ofNat_toNat64 _).symm
  have rQL : t₁.mem.readW (off (cS s₀) oQLen) 64 = BitVec.ofNat 64 (cqL s₀) := by
    rw [show t₁.mem.readW (off (cS s₀) oQLen) 64 = Mont.word t₁.mem (cS s₀) oQLen from rfl,
      hd1 _ (by unfold oQLen; omega_arith), X.hQL]; exact (Pre.ofNat_toNat64 _).symm
  refine WP.seq (WP.mono (WP.keep [.a3, .t1] (Q := fun t => t.gpr .a3 = BitVec.ofNat 64 ((cpL s₀ + 7) / 8) ∧
      t.gpr .t1 = BitVec.ofNat 64 ((cqL s₀ + 7) / 8) ∧ t.mem = t₁.mem) (by
    unfold PrivPre.pqLens
    have rPL' : t₁.mem.readW (off (cS s₀) 40) 64 = BitVec.ofNat 64 (cpL s₀) := rPL
    have rQL' : t₁.mem.readW (off (cS s₀) 56) 64 = BitVec.ofNat 64 (cqL s₀) := rQL
    brun [oPLen, oQLen, r6, rPL', rQL', len_words (cpL s₀) (by omega_arith), len_words (cqL s₀) (by omega_arith),
      hs₁.ld (show 40 + 8 ≤ cZ s₀ by omega_arith), hs₁.al8 (show 40 + 8 ≤ cZ s₀ by omega_arith) (by decide),
      hs₁.ld (show 56 + 8 ≤ cZ s₀ by omega_arith), hs₁.al8 (show 56 + 8 ≤ cZ s₀ by omega_arith) (by decide)])
    (by rfl) (by rfl))
    fun t₁' ⟨⟨l3, l1, lm⟩, kl⟩ => ?_)
  have k1' := k1.trans kl
  rw [← lm] at v0 w0 v1 v4 v5 v6 v7 t1 t6 t7
  have hd1' : ∀ d, d + 8 ≤ 256 → Mont.word t₁'.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd => by
    rw [lm]; exact hd1 d hd
  -- `p` and `q` fit in their widths.
  have fit : ∀ {j L : Nat} {bs : List Byte}, bs.length = L → 1 ≤ L → L < ck s₀ →
      wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) = Spec.Rsa.os2ip bs →
      wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) (cwX s₀) =
        wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j) ((L + 7) / 8) := fun {j L bs} hl hL1 hLk hv => by
    have hlt : Spec.Rsa.os2ip bs < 2 ^ (64 * ((L + 7) / 8)) := by
      refine Nat.lt_of_lt_of_le (Crt.os2ip_lt' bs hl) ?_
      rw [VG.Proof.Bignum.pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
    have a := wordsVal_app t₁'.mem (cS s₀) (slot (cwX s₀) j) ((L + 7) / 8) (cwX s₀ - (L + 7) / 8)
    rw [show (L + 7) / 8 + (cwX s₀ - (L + 7) / 8) = cwX s₀ by omega_arith] at a
    rw [a] at hv ⊢
    have hpos := Nat.two_pow_pos (64 * ((L + 7) / 8))
    rcases Nat.eq_zero_or_pos (wordsVal t₁'.mem (cS s₀) (slot (cwX s₀) j + 8 * ((L + 7) / 8))
      (cwX s₀ - (L + 7) / 8)) with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero]
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * ((L + 7) / 8))) h; omega_arith
  -- The checks.
  refine WP.seq (WP.mono (checksWith_ok (pq := PrivPre.checkPQs) (Na := s₀.gpr .a2) (k := ck s₀) (nb := nB s₀)
    (hs₁.congr kl.2.2) hZ8 (by omega_arith) hwX ((k1'.gpr (by decide)).trans X.s6)
    ((kl.gpr (by decide)).trans a7₁)
    ((k1'.gpr (by decide)).trans X.ra) ((k1'.gpr (by decide)).trans X.s5) ((k1'.gpr (by decide)).trans X.t0)
    (by rw [hd1' _ (by unfold oN; omega_arith), X.hN]; exact z _)
    (by rw [hd1' _ (by unfold oNLen; omega_arith), X.hNL]; exact (Pre.ofNat_toNat64 _).symm) hk hk'
    (VG.Proof.Bignum.bytesAt_length _ _ _) (fun i hi => by rw [k1'.2.1, k1'.2.2, rd0]; exact hP.rN i hi)
    (fun i hi => by
      rw [lm, F1.bytes (R := ⟨s₀.gpr .a2, ck s₀⟩) (dis dPN dNS) (Nat.le_of_lt (BitVec.isLt _)) hi]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range])
    v1 t6 t7
    (checkPQs_ok (hs₁.congr kl.2.2) hZ8 hwX l3 l1 (by omega_arith) (by omega_arith) (by omega_arith)
      (fit (VG.Proof.Bignum.bytesAt_length _ _ _) hp1 hpk v4) (fit (VG.Proof.Bignum.bytesAt_length _ _ _) hq1 hqk v5)
      t6 t1))
    fun t₂ ⟨X2, k2⟩ => ?_)
  rw [v6, v4, v5, v7, crtMask_zero] at X2
  have k12 := k1'.trans k2
  have Xfr : Frm (cS s₀) (Crt.chkR (cwX s₀)) t₁.mem t₂.mem := lm ▸ X2.fr
  have F2 : Frame [preR s₀, scrR s₀] s₀.mem t₂.mem := F1.trans (frame_of_frm Xfr fun r hr => by
    simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [oMask] <;> omega_arith)
  have hd2 : ∀ d, d + 8 ≤ oMask → Mont.word t₂.mem (cS s₀) d = Mont.word x.mem (cS s₀) d := fun d hd => by
    exact (Frm.word_eq Xfr (fun r hr => by
      simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [oMask] at hd ⊢ <;> omega_arith) (by unfold oMask at hd; omega_arith)).trans
      (hd1 d (by unfold oMask at hd; omega_arith))
  have hd3 : ∀ d, oMask + 8 ≤ d → d + 8 ≤ 256 → Mont.word t₂.mem (cS s₀) d = Mont.word x.mem (cS s₀) d :=
    fun d hd hd' => by
      exact (Frm.word_eq Xfr (fun r hr => by
        simp only [Crt.chkR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only [oMask] at hd ⊢ <;> omega_arith) (by omega_arith)).trans (hd1 d hd')
  refine hc t₂ ⟨X.scr.congr k12.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, X2.msk,
    (k12.gpr (by decide)).trans X.s6, (k12.gpr (by decide)).trans X.s11, by rw [X2.v4, v4], by rw [X2.v5, v5], (X.keep.trans k12).mono (by decide), fun i hi => ?_, F2⟩
  · rw [hd2 _ (by decide), X.hOut]
  · rw [hd2 _ (by decide), X.hN]
  · rw [hd2 _ (by decide), X.hNL]
  · rw [hd2 _ (by decide), X.hPL]
  · rw [hd2 _ (by decide), X.hQL]
  · rw [hd3 _ (by decide) (by decide), X.hBP]
  · rw [hd3 _ (by decide) (by decide), X.hBQ]
  · have esav : off (savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := by
      simp only [off, savW]; rw [Offset.add_add]
    have h1 := X.sav i hi
    change x.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _ at h1
    change t₂.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = _
    rw [esav] at h1 ⊢
    change Mont.word t₂.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word x.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [hd3 _ (by unfold oMask; omega_arith) (by omega_arith)]
    exact h1

end VG.Proof.Bignum.RISCV64.PrivPre
