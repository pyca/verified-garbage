module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMmul
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: Montgomery multiplication's working space

`mont_ok`: 1, `n` in Montgomery array 0 and `-n⁻¹ mod 2³²` in `r12`,
`R² mod n`, `R mod n` and `n - R mod n` for `R = 2^(64 wm)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (mont mpre mpost r2Set mBase mR2 mXm aN aOne aZ aO aNg nArr iXm iR2 wM)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- A range apart from the arrays and slots a step writes. -/
theorem keep_apart {B : Addr} {v : Nat} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B v js ds m m') {d n : Nat}
    (hj : ∀ j ∈ js, arr v j + S v ≤ d ∨ d + 4 * n ≤ arr v j) (hd : ∀ e ∈ ds, e + 4 ≤ d ∨ d + 4 * n ≤ e)
    (hd2 : d + 4 * n ≤ 2 ^ 64) : val32 m' B d n = val32 m B d n := by
  refine Outs.val32 k (fun r hr => ?_) hd2
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨e, he, rfl⟩
  · have := hj j hj'; dsimp only; omega_arith
  · have := hd e he; dsimp only; omega_arith

/-- A change within three consecutive arrays. -/
theorem keep_of_outside3 {B : Addr} {v j : Nat} {js ds : List Nat} {m m' : Mem}
    (o : Outside B (arr v j) (3 * S v) m m') (h0 : j ∈ js) (h1 : j + 1 ∈ js) (h2 : j + 2 ∈ js) :
    KeyWorkspace.Keep B v js ds m m' := by
  intro x hx
  have a0 := hx _ (by simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map]; exact .inl ⟨j, h0, rfl⟩)
  have a1 := hx _ (by simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map]; exact .inl ⟨j + 1, h1, rfl⟩)
  have a2 := hx _ (by simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map]; exact .inl ⟨j + 2, h2, rfl⟩)
  rw [VG.Proof.Rsa.KeyWorkspace.arr_succ, VG.Proof.Rsa.KeyWorkspace.arr_succ] at a2
  rw [VG.Proof.Rsa.KeyWorkspace.arr_succ] at a1
  refine o x ?_
  dsimp only at a0 a1 a2
  generalize arr v j = A at *
  generalize S v = T at *
  generalize ofs B x = X at *
  omega_arith

/-- The low `2 wm` digits of a number below `2^(64 wm)`: all of it. -/
theorem low_eq {m : Mem} {s0 : State} {j : Nat}
    (h : num m (rvB s0) (ww (kK s0)) j < 2 ^ (32 * (2 * wm (kK s0)))) :
    lowV m s0 j = num m (rvB s0) (ww (kK s0)) j := by
  have e := val32_append m (rvB s0) (arr (ww (kK s0)) j) (2 * wm (kK s0)) 2
  change val32 m (rvB s0) (arr (ww (kK s0)) j) (2 * wm (kK s0) + 2) < _ at h
  change _ = val32 m (rvB s0) (arr (ww (kK s0)) j) (2 * wm (kK s0) + 2)
  rw [e] at h ⊢
  have : val32 m (rvB s0) (arr (ww (kK s0)) j + 4 * (2 * wm (kK s0))) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m (rvB s0) (arr (ww (kK s0)) j + 4 * (2 * wm (kK s0))) 2) with z | z
    · exact z
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * (2 * wm (kK s0)))) z; omega_arith
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- `R = 2^(64 wm)`. -/
abbrev RR (s0 : State) : Nat := 2 ^ (64 * wm (kK s0))

/-- After the Montgomery setup. -/
structure MontS (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem (rvB s0) (arr (ww (kK s0)) mBase) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vMN : lowV t.mem s0 mBase = nV s0
  vR2 : lowV t.mem s0 mR2 = RR s0 * RR s0 % nV s0
  vO : num t.mem (rvB s0) (ww (kK s0)) aO = RR s0 % nV s0
  vNg : num t.mem (rvB s0) (ww (kK s0)) aNg = nV s0 - RR s0 % nV s0
  vOne : num t.mem (rvB s0) (ww (kK s0)) aOne = 1
  zZ : ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) aZ + 4 * i) = 0
  vM : num t.mem (rvB s0) (wW (kK s0)) wM = mV s0
  odd : dV s0 * eV s0 % 2 = 1
  two : 2 ≤ dV s0 * eV s0

theorem nV_lt {s0 : State} : nV s0 < 2 ^ (32 * (2 * wm (kK s0))) := by
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
  rw [VG.Proof.Bignum.bytesAt_length] at this
  refine Nat.lt_of_lt_of_le this ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simp only [wm]; omega_arith)

theorem val32_mod2 (m : Mem) (B : Addr) (d k : Nat) (hk : 0 < k) : val32 m B d k % 2 = w32 m B d % 2 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  simp only [val32]; omega_arith

theorem val32_zeros {m : Mem} {B : Addr} : ∀ {d n : Nat}, (∀ i < n, w32 m B (d + 4 * i) = 0) → val32 m B d n = 0
  | _, 0, _ => rfl
  | d, n + 1, h => by
    have h0 := h 0 (by omega_arith)
    rw [val32, val32_zeros (d := d + 4) (n := n) fun i hi => by
      have := h (i + 1) (by omega_arith); rwa [show d + 4 * (i + 1) = d + 4 + 4 * i by omega_arith] at this]
    simp only [Nat.mul_zero, Nat.add_zero] at h0 ⊢; exact h0

/-- Digits of one array, kept by a step on others. -/
theorem keep_in {B : Addr} {v : Nat} {js : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B v js [] m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) {i n : Nat} (hin : i + n ≤ v + 2)
    (fit : arr v j + S v ≤ 2 ^ 64) : val32 m' B (arr v j + 4 * i) n = val32 m B (arr v j + 4 * i) n := by
  have hS : S v = 4 * (v + 2) := rfl
  refine keep_apart k (fun l hl => ?_) (by simp) (by omega_arith)
  rcases Nat.lt_or_gt_of_ne (hj l hl) with h | h
  · have := VG.Proof.Rsa.KeyWorkspace.arr_end (w := v) h; omega_arith
  · have := VG.Proof.Rsa.KeyWorkspace.arr_end (w := v) h; omega_arith

theorem arr_apart {v j a b : Nat} (h : j < a ∨ b ≤ j) {d n : Nat} (hd : arr v a ≤ d)
    (hn : d + 4 * n ≤ arr v b) : arr v j + S v ≤ d ∨ d + 4 * n ≤ arr v j := by
  rcases h with h | h
  · exact .inl (Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end h) hd)
  · exact .inr (Nat.le_trans hn (VG.Proof.Rsa.KeyWorkspace.arr_mono h))

theorem arrW3 (w : Nat) : arr (2 * w + 2) 3 = arr w 6 := by
  simp only [arr, S, KeyWorkspace.hdr]; omega_arith

theorem arrW3_end (w : Nat) : arr w 6 + 4 * (2 * w + 2) ≤ arr w 8 := by
  simp only [arr, S, KeyWorkspace.hdr]; omega_arith

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The registers `mont` changes after `minv`. -/
abbrev mtRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r29]

/-- `mont`: the Montgomery constants of `n`. -/
theorem mont_ok {s0 t : State} (h : NumS s0 t) (hgo : t.gpr .r0 = 0)
    (hmv : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) : WP isa mont t (MontS s0) := by
  obtain ⟨odd, two⟩ := h.go.mp hgo
  have z := h.base.sz
  have w1 := z.w1; have w2 := z.w2; have svZ := z.svZ; have nw := z.nw; have svw := z.svw
  have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
  have hSw : S (ww (kK s0)) = 8 * (wm (kK s0) + 2) := by simp only [S, hww]; omega_arith
  have hsl : ∀ j, VG.Proof.Bignum.slot (wm (kK s0)) j = 256 + j * (8 * (wm (kK s0) + 2)) := fun j => rfl
  have am := arr_mont (kK s0)
  have aM0 : arr (ww (kK s0)) mBase = oM (kK s0) + VG.Proof.Bignum.slot (wm (kK s0)) 0 := by
    have := am 0; simpa using this
  have fM : oM (kK s0) + VG.Proof.Bignum.slot (wm (kK s0)) 8 ≤ rvZ s0 := by
    rw [← am 8]
    have := VG.Proof.Rsa.KeyWorkspace.arr_mono (w := ww (kK s0)) (show mBase + 8 ≤ nArr by decide)
    rw [← svw] at this; omega_arith
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmv
  obtain ⟨⟨⟨nodd, n511⟩, -⟩, -⟩ := hmv
  have n2 : 2 ≤ nV s0 := Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 511 by decide)) n511
  clear n511
  have nlt := nV_lt (s0 := s0)
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  unfold mont
  rw [List.append_assoc]; simp only [List.cons_append, List.nil_append]
  -- 1.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (VG.Impl.Rsa.PPC64LE.Keys.setOne aOne)]
  refine setOne_ok h.ws (j := aOne) (by decide) (by decide) fun t1 ws1 kk1 v1 k1 => WP.block_nil ?_
  have one1 : num t1.mem (rvB s0) (ww (kK s0)) aOne = 1 := by
    rw [v1, show num t.mem (rvB s0) (ww (kK s0)) aOne = 0 from
      val32_zeros fun i hi => h.zK aOne (by simp) i (by omega_arith)]
  -- 2.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws1 (o := mBase) (a := aN) (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨ws2, kk2, v2, k2, _⟩ => ?_
  have nN2 : num t2.mem (rvB s0) (ww (kK s0)) mBase = nV s0 := by
    rw [v2, kk1.num (by decide) (by simp) (fit aN (by decide))]; exact h.vN
  -- 3.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), mpre, List.append_assoc]
  refine ptr_ok ws2 (r := .r10) (by decide) (by decide) (by decide) (show mBase < 2 ^ 15 by decide) ?_
  change WP isa (.block (([.subi .r11 .r29 2, .addi .r29 .r30 0] : List Instr) ++
    (VG.Impl.Bignum.PPC64LE.PublicChecked.minv ++ r2Set))) _ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r29] (Q := fun x => x.gpr .r11 = BitVec.ofNat 64 (2 * wm (kK s0)) ∧
    x.gpr .r29 = BitVec.ofNat 64 (8 * (wm (kK s0) + 2)) ∧ x.mem = t2.mem)
    (by
      have := ws2.r29; have := ws2.r30
      prun [ws2.r29, ws2.r30, hww, sub2_val, hSw, BitVec.add_zero]) (by decide))
    fun s1 ⟨⟨a11, a29, m1⟩, ks1⟩ => ?_
  have K1 : Keep [.r10, .r11, .r29] t2 s1 := ((Keep.write _ _ _).trans ks1).mono
  have a10 : s1.gpr .r10 = off (rvB s0) (arr (ww (kK s0)) mBase) := by
    rw [ks1.gpr _ (by decide)]; simp [gpr_write]
  rw [WP.block_append_iff]
  have hodd : (word s1.mem (rvB s0) (arr (ww (kK s0)) mBase)).toNat % 2 = 1 := by
    have := val32_mod2 t2.mem (rvB s0) (arr (ww (kK s0)) mBase) (ww (kK s0)) (by omega_arith)
    change num t2.mem (rvB s0) (ww (kK s0)) mBase % 2 = _ at this
    rw [word_eq_w32, m1]; rw [nN2] at this; omega_arith
  have hs1 : Scr s1 (rvB s0) (rvZ s0) := ws2.scr.congr K1.wr
  have hdM : arr (ww (kK s0)) mBase + 8 ≤ rvZ s0 := by
    have := ws2.arr_fit (j := mBase) (by decide); simp only [S] at this; omega_arith
  refine WP.mono (Pub.minv_ok hs1 a10 hdM hodd) fun s2 ⟨⟨r12lt, inv2, m2⟩, k2'⟩ => ?_
  have lowN : lowV t2.mem s0 mBase = nV s0 := by rw [low_eq (by rw [nN2]; exact nlt), nN2]
  -- `r5`, `r8`, `r9`: arrays 1–3.
  refine WP.mono (WP.keep [.r5, .r8, .r9] (Q := fun x => x.gpr .r5 = s2.gpr .r10 + s2.gpr .r29 ∧
    x.gpr .r8 = s2.gpr .r10 + s2.gpr .r29 + s2.gpr .r29 ∧
    x.gpr .r9 = s2.gpr .r10 + s2.gpr .r29 + s2.gpr .r29 + s2.gpr .r29 ∧ x.mem = s2.mem)
    (by prun [r2Set]) (by decide)) fun s3 ⟨⟨a5, a8, a9, m3⟩, k3'⟩ => ?_
  have K3 : Keep [.r0, .r3, .r4, .r5, .r8, .r9, .r10, .r11, .r12, .r29] t2 s3 := ((K1.trans k2').trans k3').mono
  have b10 : s2.gpr .r10 = off (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) 0) := by
    rw [k2'.gpr _ (by decide), a10, off_off, ← aM0]
  have b29 : s2.gpr .r29 = BitVec.ofNat 64 (8 * (wm (kK s0) + 2)) := by rw [k2'.gpr _ (by decide)]; exact a29
  have hstep : ∀ j, off (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) j) +
      BitVec.ofNat 64 (8 * (wm (kK s0) + 2)) = off (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) (j + 1)) :=
    fun j => by rw [off_add]; congr 1; simp only [hsl]; grind
  rw [b10, b29] at a5 a8 a9
  simp only [hstep] at a5 a8 a9
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hsM : Scr s3 (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) 8) :=
    Scr.sub (hs1.congr (k2'.trans k3').wr) fM (by rw [hsl]; omega_arith)
  refine WP.mono (r2_ok hsM a8 a9 (by rw [k3'.gpr _ (by decide)]; exact b10) a5
    (by rw [k3'.gpr _ (by decide), k2'.gpr _ (by decide)]; exact a11) (by omega_arith) (by omega_arith)
    (by simp only [hsl]; omega_arith)
    (by rw [val32_rebase, ← aM0, m3, m2, m1]; change 2 ≤ lowV t2.mem s0 mBase; rw [lowN]; omega_arith))
    fun s4 ⟨v4, o4, k4⟩ => ?_
  have kk4 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mR2, mR2 + 1, mR2 + 2] [] s3.mem s4.mem := by
    refine keep_of_outside3 (j := mR2) (fun x hx => ?_) (by simp) (by simp) (by simp)
    have o4' := Outs.rebase (rs := [(VG.Proof.Bignum.slot (wm (kK s0)) 1, 24 * (wm (kK s0) + 2))])
      (Outs.of_outside o4 (by simp)) (by rw [hsl] at fM; omega_arith) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        have := fit (mBase + 4) (by decide); rw [am, hSw, hsl] at this; rw [hsl]; omega_arith)
    refine o4' x fun r hr => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    dsimp only
    rw [show mR2 = mBase + 1 from rfl, am 1, hSw] at hx; omega_arith
  have hr2 : lowV s4.mem s0 mR2 = RR s0 * RR s0 % nV s0 := by
    have := v4; rw [val32_rebase, val32_rebase, ← aM0, m3, m2, m1, ← am 1] at this
    change lowV s4.mem s0 (mBase + 1) = 2 ^ (128 * wm (kK s0)) % lowV t2.mem s0 mBase at this
    rw [lowN] at this
    rw [show mR2 = mBase + 1 from rfl, this, RR, ← Nat.pow_add, show 64 * wm (kK s0) + 64 * wm (kK s0) =
      128 * wm (kK s0) by omega_arith]
  -- 5.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff]
  have e11 : s4.gpr .r11 = BitVec.ofNat 64 (2 * wm (kK s0)) := by
    rw [k4.gpr _ (by decide), k3'.gpr _ (by decide), k2'.gpr _ (by decide)]; exact a11
  refine WP.mono (WP.keep [.r29] (Q := fun x => x.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) ∧ x.mem = s4.mem)
    (by prun [mpost, e11, add2_val, ← hww]) (by decide)) fun s5 ⟨⟨a29', m5⟩, k5'⟩ => ?_
  -- From `s2` on, `r12` stays.
  have L5 : Keep mtRegs s2 s5 := ((k3'.trans k4).trans k5').mono
  have K5 : Keep (.r12 :: mtRegs) t2 s5 := ((K1.trans k2').trans L5).mono
  have ws5 : Ws s5 (rvB s0) (rvZ s0) (ww (kK s0)) nArr :=
    ⟨ws2.scr.congr K5.wr, ws2.fits, ws2.wpos, ws2.wle, a29', (K5.gpr _ (by decide)).trans ws2.r30,
      (K5.gpr _ (by decide)).trans ws2.r31⟩
  refine clrTop_ok ws5 (j := mR2) (by decide) (by decide) (by omega_arith)
    fun t5 ws5' kk5 _ v5 k5 => WP.block_nil ?_
  have R2 : num t5.mem (rvB s0) (ww (kK s0)) mR2 = RR s0 * RR s0 % nV s0 := by
    rw [v5, m5, show ww (kK s0) - 2 = 2 * wm (kK s0) by omega_arith]; exact hr2
  -- 6.
  rw [wp_seqs_cons (by simp [VG.Impl.Rsa.PPC64LE.Recover.mmul])]
  refine WP.mono (copy_ok ws5' (o := mXm) (a := aOne) (by decide) (by decide) (by decide) (by decide))
    fun t6 ⟨ws6, kk6, v6, k6, _⟩ => ?_
  have L6 : Keep mtRegs s2 t6 := ((L5.trans k5).trans k6).mono
  -- The arrays so far.
  have KA : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase, mR2, mR2 + 1, mR2 + 2, mXm] [] t1.mem t5.mem := by
    have a4 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase, mR2, mR2 + 1, mR2 + 2, mXm] [] t2.mem s4.mem := by
      rw [← m1, ← m2, ← m3]; exact KeyWorkspace.Keep.mono kk4
    have a5 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase, mR2, mR2 + 1, mR2 + 2, mXm] [] s4.mem t5.mem := by
      rw [← m5]; exact KeyWorkspace.Keep.mono kk5
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk2) (KeyWorkspace.Keep.trans a4 a5)
  have one6 : num t6.mem (rvB s0) (ww (kK s0)) mXm = 1 := by
    rw [v6, KA.num (by decide) (by simp) (fit aOne (by decide))]; exact one1
  -- 7.
  have KA6 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase, mR2, mR2 + 1, mR2 + 2, mXm] [] t1.mem t6.mem :=
    KeyWorkspace.Keep.trans KA (KeyWorkspace.Keep.mono kk6)
  have KT6 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [aOne, mBase, mR2, mR2 + 1, mR2 + 2, mXm] [] t.mem t6.mem :=
    KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk1) (KeyWorkspace.Keep.mono KA6)
  have fitM : arr (ww (kK s0)) mBase + S (ww (kK s0)) ≤ 2 ^ 64 := fit mBase (by decide)
  have KM : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mR2, mR2 + 1, mR2 + 2, mXm] [] t2.mem t6.mem := by
    have a4 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mR2, mR2 + 1, mR2 + 2, mXm] [] t2.mem s4.mem := by
      rw [← m1, ← m2, ← m3]; exact KeyWorkspace.Keep.mono kk4
    have a5 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mR2, mR2 + 1, mR2 + 2, mXm] [] s4.mem t5.mem := by
      rw [← m5]; exact KeyWorkspace.Keep.mono kk5
    exact KeyWorkspace.Keep.trans a4 (KeyWorkspace.Keep.trans a5 (KeyWorkspace.Keep.mono kk6))
  have lowN6 : lowV t6.mem s0 mBase = nV s0 := by
    rw [← lowN]
    have := keep_in KM (j := mBase) (i := 0) (n := 2 * wm (kK s0)) (by decide) (by omega_arith) fitM
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  have inv6 : w32 t6.mem (rvB s0) (arr (ww (kK s0)) mBase) = w32 s1.mem (rvB s0) (arr (ww (kK s0)) mBase) := by
    rw [m1]
    have := keep_in KM (j := mBase) (i := 0) (n := 1) (by decide) (by omega_arith) fitM
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  have r12' : t6.gpr .r12 = s2.gpr .r12 := L6.gpr _ (by decide)
  have fitR : arr (ww (kK s0)) mR2 + S (ww (kK s0)) ≤ 2 ^ 64 := fit mR2 (by decide)
  have nlt2 : RR s0 * RR s0 % nV s0 < nV s0 := Nat.mod_lt _ (by omega_arith)
  have R26 : lowV t6.mem s0 mR2 = RR s0 * RR s0 % nV s0 := by
    have := keep_in kk6 (j := mR2) (i := 0) (n := 2 * wm (kK s0)) (by decide) (by omega_arith) fitR
    simp only [Nat.mul_zero, Nat.add_zero] at this
    change lowV t6.mem s0 mR2 = lowV t5.mem s0 mR2 at this
    rw [this, low_eq (by rw [R2]; omega_arith), R2]
  have one6' : lowV t6.mem s0 mXm = 1 := by rw [low_eq (by rw [one6]; exact Nat.one_lt_two_pow (by omega_arith)), one6]
  have KR6 : Keep (.r12 :: mtRegs) t t6 := ((((k1.trans k2).trans K5).trans k5).trans k6).mono
  have b6 : RBase s0 t6 := h.base.of_keep KT6 (fun j hj => ?_) (by simp) KR6
  rotate_left
  · have : j < nArr := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                          rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end this
  rw [wp_seqs_append (by simp [VG.Impl.Rsa.PPC64LE.Recover.mmul]) (List.cons_ne_nil _ _)]
  refine WP.mono (mmul_ok b6 ws6 (o := iXm) (a := iXm) (b := iR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r12']; exact r12lt) (by rw [r12', inv6]; exact inv2)
    (by rw [lowN6]; exact (show lowV t6.mem s0 mR2 < nV s0 by rw [R26]; exact nlt2)))
    fun t7 ⟨b7, ws7, kk7, lt7, eq7, k7⟩ => ?_
  change num t7.mem (rvB s0) (ww (kK s0)) mXm < lowV t6.mem s0 mBase at lt7
  change num t7.mem (rvB s0) (ww (kK s0)) mXm * RR s0 % lowV t6.mem s0 mBase =
    lowV t6.mem s0 mXm * lowV t6.mem s0 mR2 % lowV t6.mem s0 mBase at eq7
  rw [lowN6, one6', R26, Nat.one_mul, Nat.mod_mod] at eq7
  rw [lowN6] at lt7
  have X7 : num t7.mem (rvB s0) (ww (kK s0)) mXm = RR s0 % nV s0 := by
    have := VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 nodd _) eq7
    rwa [Nat.mod_eq_of_lt lt7] at this
  -- 8.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws7 (o := aO) (a := mXm) (by decide) (by decide) (by decide) (by decide))
    fun t8 ⟨ws8, kk8, v8, k8, _⟩ => ?_
  -- 9.
  rw [show seqs [VG.Impl.Rsa.PPC64LE.Keys.sub3 aNg aN aO] = VG.Impl.Rsa.PPC64LE.Keys.sub3 aNg aN aO from rfl]
  refine WP.mono (sub3_ok ws8 (o := aNg) (a := aN) (b := aO) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t9 ⟨ws9, kk9, v9, b9, k9⟩ => ?_
  have KL : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mR2 + 1, mR2 + 2, mXm, aO, aNg] [] t6.mem t9.mem :=
    KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk7 (by decide))
      (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk8) (KeyWorkspace.Keep.mono kk9))
  have KK : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [aOne, mBase, mR2, mR2 + 1, mR2 + 2, mXm, aO, aNg] []
      t.mem t9.mem := KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono KT6) (KeyWorkspace.Keep.mono KL)
  have K1L : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase, mR2, mR2 + 1, mR2 + 2, mXm, aO, aNg] []
      t1.mem t9.mem := KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono KA6) (KeyWorkspace.Keep.mono KL)
  have KR9 : Keep (.r12 :: mtRegs) t t9 := (((KR6.trans k7).trans k8).trans k9).mono
  have L9 : Keep mtRegs s2 t9 := (((L6.trans k7).trans k8).trans k9).mono
  have O8 : num t8.mem (rvB s0) (ww (kK s0)) aO = RR s0 % nV s0 := by rw [v8, X7]
  have N8 : num t8.mem (rvB s0) (ww (kK s0)) aN = nV s0 := by
    have a7 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [aOne, mBase, mR2, mR2 + 1, mR2 + 2, mXm, aO] [] t6.mem t7.mem :=
      KeyWorkspace.Keep.mono kk7 (by decide)
    have a8 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [aOne, mBase, mR2, mR2 + 1, mR2 + 2, mXm, aO] [] t7.mem t8.mem :=
      KeyWorkspace.Keep.mono kk8 (by decide)
    rw [(KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono KT6 (by decide)) (KeyWorkspace.Keep.trans a7 a8)).num
      (by decide) (by simp) (fit aN (by decide))]
    exact h.vN
  have hO9 : num t9.mem (rvB s0) (ww (kK s0)) aO = RR s0 % nV s0 := by
    rw [kk9.num (by decide) (by simp) (fit aO (by decide))]; exact O8
  have rO : RR s0 % nV s0 < nV s0 := Nat.mod_lt _ (by omega_arith)
  have lt9 := val32_lt t9.mem (rvB s0) (arr (ww (kK s0)) aNg) (ww (kK s0))
  change num t9.mem (rvB s0) (ww (kK s0)) aNg < _ at lt9
  have nb : nV s0 < 2 ^ (32 * ww (kK s0)) :=
    Nat.lt_of_lt_of_le nlt (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have r90 : (t9.gpr .r9).toNat = 0 := by
    rw [O8, N8] at v9
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b9 with e | e
    · exact e
    · rw [e] at v9; omega_arith
  rw [r90, Nat.mul_zero, Nat.add_zero, O8, N8] at v9
  have lowK : ∀ j, j ∉ [mR2 + 1, mR2 + 2, mXm, aO, aNg] → j < nArr →
      lowV t9.mem s0 j = lowV t6.mem s0 j := fun j hj hn => by
    have := keep_in KL (j := j) (i := 0) (n := 2 * wm (kK s0)) (fun k hk e => hj (e ▸ hk)) (by omega_arith) (fit j hn)
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  refine ⟨h.base.of_keep KK (fun j hj => ?_) (by simp) KR9, ws9, by rw [KR9.gpr _ (by decide)]; exact h.r21,
    by rw [KR9.gpr _ (by decide)]; exact h.r23, by rw [KR9.gpr _ (by decide)]; exact h.r24,
    by rw [KR9.gpr _ (by decide)]; exact h.r25, by rw [KR9.gpr _ (by decide)]; exact h.r26,
    by rw [L9.gpr _ (by decide)]; exact r12lt, ?_,
    by rw [KK.num (by decide) (by simp) (fit aN (by decide))]; exact h.vN,
    by rw [lowK mBase (by decide) (by decide)]; exact lowN6,
    by rw [lowK mR2 (by decide) (by decide)]; exact R26, hO9, by omega_arith,
    by rw [K1L.num (by decide) (by simp) (fit aOne (by decide))]; exact one1, fun i hi => ?_, ?_, odd, two⟩
  · have : j < nArr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end this
  · rw [L9.gpr _ (by decide)]
    have := keep_in KL (j := mBase) (i := 0) (n := 1) (by decide) (by omega_arith) fitM
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this, inv6]; exact inv2
  · have := keep_in KK (j := aZ) (i := i) (n := 1) (by decide) (by omega_arith) (fit aZ (by decide))
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h.zK aZ (by simp) i hi
  · have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
    have e1 := arrW3 (ww (kK s0)); have e2 := arrW3_end (ww (kK s0))
    change val32 t9.mem (rvB s0) (arr (wW (kK s0)) 3) (wW (kK s0)) = _
    rw [hW, e1]
    have f8 := VG.Proof.Rsa.KeyWorkspace.arr_mono (w := ww (kK s0)) (show 8 ≤ aN by decide)
    have fN := fit aN (by decide)
    have hjs : ∀ j ∈ [aOne, mBase, mR2, mR2 + 1, mR2 + 2, mXm, aO, aNg], j < 6 ∨ 8 ≤ j := by decide
    rw [keep_apart KK (fun j hj => arr_apart (hjs j hj) (Nat.le_refl _) e2) (by simp)
      (Nat.le_trans e2 (Nat.le_trans f8 (Nat.le_trans (Nat.le_add_right _ _) fN)))]
    rw [← e1, ← hW]; exact h.vM

end VG.Proof.Rsa.PPC64LE.Recover
