module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreFront
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFront
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the checks

`partA_ok`: from the entry, `save`, `args`, `zeroIn`, `setupX` and
`vg_rsa_private_crt`'s `loadX` and `checks`, with `pre` (its first words
zero) as the input and `qInv`: the mask of `n` valid and `p q = n`
(`privMask`, `crtMask_zero`) in `r26`, and `p` and `q` (or 3) in `X`'s arrays
4 and 5 (`A`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The mask of `vg_rsa_private_precompute`: `n` valid and `p q = n`. -/
def privMask (N k P Q : Nat) : Bool := Spec.Rsa.modulusValid N k && decide (P * Q = N)

/-- With the input and `qInv` zero, the CRT's checks are `n` valid and
`p q = n`. -/
theorem crtMask_zero (N k P Q : Nat) : Crt.crtMask N k 0 P Q 0 = privMask N k P Q := by
  unfold Crt.crtMask privMask
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
theorem os2ip_zero_words {m : Mem} {P : Addr} {w k : Nat} (hz : ∀ i < w, word m P (8 * i) = 0)
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


/-- `X`'s words. -/
abbrev cwX (s : State) : Nat := 2 * cw s
/-- `p`'s and `q`'s lengths. -/
abbrev cpL (s : State) : Nat := (s.gpr .r8).toNat
abbrev cqL (s : State) : Nat := (s.gpr .r10).toNat
/-- `n`, `p` and `q` as numbers. -/
abbrev cN (s : State) : Nat := Spec.Rsa.os2ip (nB s)
abbrev cP (s : State) : Nat := Spec.Rsa.os2ip (pB s)
abbrev cQ (s : State) : Nat := Spec.Rsa.os2ip (qB s)
/-- The mask. -/
abbrev cb (s : State) : Bool := privMask (cN s) (ck s) (cP s) (cQ s)

/-- The registers written up to the checks. -/
def aRegs : List Reg :=
  [.r11, .r23] ++ [.r0, .r14, .r17, .r11] ++ [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r27, .r28, .r29] ++
    (Crt.loadXRegs ++ Crt.checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg))

/-- What holds after the checks, from the entry state `s₀`. -/
structure A (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = s₀.gpr .r3
  hN : word s.mem (cS s₀) oN = s₀.gpr .r5
  hNL : word s.mem (cS s₀) oNLen = s₀.gpr .r6
  hPL : word s.mem (cS s₀) oPLen = s₀.gpr .r8
  hQL : word s.mem (cS s₀) oQLen = s₀.gpr .r10
  hBP : word s.mem (cS s₀) oBP = off (cS s₀) (slot (cwX s₀) 8)
  hBQ : word s.mem (cS s₀) oBQ = off (cS s₀) (slot (cwX s₀) 8 + slot (wsWords (cpL s₀)) 24)
  r23 : s.gpr .r23 = cS s₀
  r26 : s.gpr .r26 = Crt.bmask (cb s₀)
  r27 : s.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0)
  r28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2))
  x4 : val32 s.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = if cb s₀ then cP s₀ else 3
  x5 : val32 s.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = if cb s₀ then cQ s₀ else 3
  keep : Keep aRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

theorem saved_ne11 : ∀ i < 18, Crt.saved i ≠ .r11 := by decide

/-- From the entry to the checks. -/
theorem partA_ok {s₀ : State} (h : fnContract.pre s₀) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, A s₀ t → WP isa c t Q) :
    WP isa (.seq (.block (PrivPre.save ++ PrivPre.args)) (.seq PrivPre.zeroIn (.seq (.block setupX)
      (.seq Crt.loadX (.seq Crt.checks c))))) s₀ Q := by
  obtain ⟨hsp, hrd, hwr, dPN, dPP, dPQ, dPS, dPA, dNS, dpS, dqS, dSA, nwPre, nwN, nwP, nwQ, nwS, ⟨hk, hk'⟩,
    hp1, hpk, hq1, hqk, hpl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] at hpl
  have hscr : Scr s₀ (cS s₀) (cZ s₀) := Scr.of_mem (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) nwS
  have hpre : Scr s₀ (s₀.gpr .r3) ((s₀.gpr .r4).toNat * 8) := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..) nwPre
  have hn := hscr.nowrap
  have hZ : 128 * ck s₀ + 256 ≤ cZ s₀ := by
    show 128 * (s₀.gpr .r6).toNat + 256 ≤ (stackArg s₀ 1).toNat * 8; omega_arith
  have hargs : argsR s₀ ∈ s₀.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8 :=
    ⟨_, List.mem_append_left _ hargs, by
      have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  have hsavR : ∀ i < 18, (⟨cS s₀, cZ s₀⟩ : Region).Contains (off (Crt.savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s₀ hst fun i hi => ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), hsavR i hi⟩)
    fun t ⟨s₁, a11, m1, k1, hSv⟩ => ?_
  have kt := k1.trans hSv.keep
  have t23 : t.gpr .r23 = cS s₀ := hSv.r23.trans a11
  have fr : Frame [Crt.savR (Crt.savW (cS s₀))] s₀.mem t.mem := by
    have := hSv.frame; rw [a11, m1] at this; exact this
  refine WP.mono (args_ok (hscr.congr kt.wr) (by omega_arith) t23)
    fun u ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, Ou⟩, ku⟩ => ?_
  have ktu := kt.trans ku
  -- Changes within the working space or `pre`, as frames.
  have frS : ∀ {m m' : Mem} {o n : Nat}, Outside (cS s₀) o n m m' → o + n ≤ cZ s₀ →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (scrR s₀) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only [Region.Contains, ofs, cS, cZ] at this hon ⊢
    omega_arith
  have frP : ∀ {m m' : Mem} {o n : Nat}, Outside (s₀.gpr .r3) o n m m' → o + n ≤ (s₀.gpr .r4).toNat * 8 →
      Frame [preR s₀, scrR s₀] m m' := fun {m m' o n} h hon x hx => by
    refine h x ?_
    have := hx (preR s₀) (List.mem_cons_self ..)
    simp only [Region.Contains, ofs] at this ⊢
    omega_arith
  -- The working space's addresses are apart from `pre`'s.
  have hPS : ∀ x, Mont.ofs (cS s₀) x < cZ s₀ → (s₀.gpr .r4).toNat * 8 ≤ Mont.ofs (s₀.gpr .r3) x := fun x hx => by
    by_contra hc
    exact dPS x (by simp only [Region.Contains]; simp only [Mont.ofs] at hc; omega_arith)
      (by simp only [Region.Contains]; simp only [Mont.ofs, cS, cZ] at hx; omega_arith)
  have F1 : Frame [preR s₀, scrR s₀] s₀.mem u.mem := by
    refine (fr.sub fun r hr => ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩).trans
      (frS Ou (by omega_arith))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Crt.savR, Crt.savW]
    rw [show cS s₀ + BitVec.ofNat 64 112 = off (cS s₀) 112 from rfl]
    exact Offset.sub_base _ (by omega_arith)
  -- `zeroIn`.
  have hw1 : 1 ≤ cw s₀ := by simp only [cw, ck]; omega_arith
  have hcw : cw s₀ = ((s₀.gpr .r6).toNat + 7) / 8 := rfl
  have hcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  refine WP.seq ?_
  have u6 : u.gpr .r6 = BitVec.ofNat 64 (ck s₀) := by
    rw [ktu.gpr .r6 (by decide)]; exact (ofNat_toNat64 _).symm
  obtain ⟨K, hK⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  rw [hK] at u6
  have hK' : (s₀.gpr .r6).toNat = K := hK
  refine WP.seq (WP.mono (WP.keep [.r14, .r11] (Q := fun v => v.gpr .r14 = off (s₀.gpr .r3) 0 ∧
      v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧ v.mem = u.mem) (by
        prun [ktu.gpr .r3 (by decide), u6, BitVec.add_zero,
          Pre.ofNat_add7_shr3 K (show K < 2 ^ 32 by omega_using [hK', hk']), Pre.ofNat_shl1]
        rw [hcw, hK']) rfl) fun v₁ ⟨⟨z14, z11, zm⟩, zk⟩ => ?_)
  refine WP.mono (zeroWords_ok (hpre.congr (ktu.trans zk).wr) z14 z11 hw1 (by omega_arith) (by omega_arith))
    fun v ⟨⟨_, vz, vo⟩, vk⟩ => ?_
  rw [zm] at vo
  have kv := (ktu.trans zk).trans vk
  have hhv : ∀ d, d + 8 ≤ cZ s₀ → word v.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd =>
    Mem.readW_congr fun i hi => vo _ (Or.inr (by
      have := hPS (off (cS s₀) d + BitVec.ofNat 64 i) (by rw [Mont.ofs_off _ (by omega_arith)]; omega_arith)
      omega_arith))
  have F2 : Frame [preR s₀, scrR s₀] s₀.mem v.mem := F1.trans (frP vo (by omega_arith))
  -- `setupX`.
  refine WP.seq (WP.mono (Crt.setupX_ok (k := ck s₀) (pL := cpL s₀) (hscr.congr kv.wr) (by omega_arith)
    (((zk.trans vk).gpr _ (by decide)).trans ((ku.gpr _ (by decide)).trans t23))
    (by rw [kv.gpr _ (by decide)]; exact (ofNat_toNat64 _).symm) hk'
    (by rw [hhv _ (by simp only [oPLen]; omega_arith), w5, kt.gpr _ (by decide)]; exact (ofNat_toNat64 _).symm) hp1
    (by show (s₀.gpr .r8).toNat < 2 ^ 60; omega_arith))
    fun x ⟨⟨x10, x21, x29, x11, x27, x28, xBP, xBQ, Ox⟩, kx⟩ => ?_)
  have kx' := kv.trans kx
  have F3 : Frame [preR s₀, scrR s₀] s₀.mem x.mem := F2.trans (frS Ox (by omega_arith))
  sorry

end VG.Proof.Bignum.PPC64LE.PrivPre
