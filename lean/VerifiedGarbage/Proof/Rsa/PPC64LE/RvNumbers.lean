module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvLoads
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Rsa.PPC64LE.MulMod
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.RecoverProduct
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: `M = d e`, and whether to try candidates

`numbers_ok`: after the numbers are read, `M = d e` by `mulMod` modulo
`2^(32 W - 1)`, its low bit cleared (`m = M - 1` when `M` is odd), and `r0`
0 iff `M` is odd and above 1.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (numbers loads prod prodSet skipBits skipTest nArr aN aOne aZ wZ wE wD wM wMod wT
  sBit)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- `m = d e - 1`, when `d e` is odd. -/
abbrev mV (s0 : State) : Nat := 2 * (dV s0 * eV s0 / 2)

/-- After `numbers`. -/
structure NumS (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vM : num t.mem (rvB s0) (wW (kK s0)) wM = mV s0
  zK : ∀ j ∈ [aOne, aZ], ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) j + 4 * i) = 0
  go : t.gpr .r0 = 0 ↔ (dV s0 * eV s0 % 2 = 1 ∧ 2 ≤ dV s0 * eV s0)

/-- A step on arrays below `J` (of `v` digits) keeps what is from array `J` on. -/
theorem keep_far {B : Addr} {v J : Nat} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep B v js ds m m') (hj : ∀ j ∈ js, j < J)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) {d n : Nat} (hd1 : arr v J ≤ d) (hd2 : d + 4 * n ≤ 2 ^ 64) :
    val32 m' B d n = val32 m B d n := by
  refine Outs.val32 k (fun r hr => ?_) hd2
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨j, hj', rfl⟩ | ⟨e, he, rfl⟩
  · right
    have := VG.Proof.Rsa.KeyWorkspace.arr_mono (w := v) (show j + 1 ≤ J by have := hj j hj'; omega_arith)
    rw [VG.Proof.Rsa.KeyWorkspace.arr_succ] at this
    dsimp only; omega_arith
  · right; have := hd e he; have : 160 ≤ arr v J := Nat.le_add_right _ _; dsimp only; omega_arith

/-- A step on the `W` view's arrays up to 8 keeps the key arrays from 18 on. -/
theorem keepW_far {s0 : State} {js ds : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep (rvB s0) (wW (kK s0)) js ds m m') (hj : ∀ j ∈ js, j ≤ 8)
    (hd : ∀ d ∈ ds, d + 4 ≤ 160) {d n : Nat} (hd1 : arr (wW (kK s0)) 9 ≤ d) (hd2 : d + 4 * n ≤ 2 ^ 64) :
    val32 m' (rvB s0) d n = val32 m (rvB s0) d n :=
  keep_far k (fun j h => Nat.lt_succ_of_le (hj j h)) hd hd1 hd2

theorem arrW9 (w : Nat) : arr (2 * w + 2) 9 = arr w 18 := by
  simp only [arr, S, KeyWorkspace.hdr]; omega_arith

theorem arrW16 (w : Nat) : arr (2 * w + 2) 16 = arr w 32 := by
  simp only [arr, S, KeyWorkspace.hdr]; omega_arith

theorem shl3 (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem skip_val (a b : BitVec 64) (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1) :
    (a &&& b) ^^^ BitVec.ofNat 64 1 = 0 ↔ a.toNat = 1 ∧ b.toNat = 1 := by
  have ea : a = 0 ∨ a = 1 := by
    rcases (show a.toNat = 0 ∨ a.toNat = 1 by omega_arith) with e | e
    · exact .inl (BitVec.eq_of_toNat_eq e)
    · exact .inr (BitVec.eq_of_toNat_eq e)
  have eb : b = 0 ∨ b = 1 := by
    rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega_arith) with e | e
    · exact .inl (BitVec.eq_of_toNat_eq e)
    · exact .inr (BitVec.eq_of_toNat_eq e)
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> decide

theorem os2ip_lt8 (bs : List Byte) : Spec.Rsa.os2ip bs < 2 ^ (8 * bs.length) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this

/-- `prod`: `M = d e` in the array `wM` of the `W` view. -/
theorem prod_ok {s0 t : State} (h : LdD s0 t) :
    WP isa prod t fun u => Ws u (rvB s0) (rvZ s0) (wW (kK s0)) 16 ∧
      KeyWorkspace.Keep (rvB s0) (wW (kK s0)) [wMod, wE, wD, wM, wT, wT + 1, wT + 2, wT + 3]
        [VG.Impl.Rsa.PPC64LE.Keys.sB, VG.Impl.Rsa.PPC64LE.Keys.sC] t.mem u.mem ∧
      num u.mem (rvB s0) (wW (kK s0)) wM = dV s0 * eV s0 ∧
      num u.mem (rvB s0) (wW (kK s0)) wZ = 0 ∧ Keep (.r4 :: opRegs) t u := by
  have z := h.base.sz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id h.base.pre
  have w1 := z.w1; have w2 := z.w2; have kw := z.kw
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  unfold prod prodSet
  refine WP.seq ?_
  refine setTop_ok h.ws (j := wMod) (by decide) (by decide) (fun i hi => h.zW wMod (by decide) i (by omega_arith))
    fun t1 w1' k1 v1 kr1 => ?_
  have e4 : t1.gpr .r27 = s0.gpr .r10 := (kr1.gpr _ (by decide)).trans h.r27
  refine WP.mono (WP.keep [.r4] (Q := fun u => u.gpr .r4 = BitVec.ofNat 64 (8 * (s0.gpr .r10).toNat) ∧
    u.mem = t1.mem) (by prun [e4, shl3]) (by decide)) fun t2 ⟨⟨a4, m2⟩, k2⟩ => ?_
  have w2' := w1'.of_keep k2
  have fit : ∀ j < 16, arr (wW (kK s0)) j + S (wW (kK s0)) ≤ 2 ^ 64 := fun j hj => w2'.fit64 hj
  -- The values before the product.
  have n0 : ∀ j ∈ [wZ, wM], num t2.mem (rvB s0) (wW (kK s0)) j = 0 := fun j hj => by
    have hj' : j = 0 ∨ j = 3 := by simpa [wZ, wM] using hj
    rw [m2, k1.num (fun k hk => by simp only [List.mem_singleton] at hk; subst hk; simp only [wMod]; omega_arith)
      (by simp) (fit j (by omega_arith))]
    exact CrtValues.val32_of_zero fun i hi => h.zW j (by rcases hj' with rfl | rfl <;> decide) i (by omega_arith)
  have nE : num t2.mem (rvB s0) (wW (kK s0)) wE = eV s0 := by
    rw [m2, k1.num (by decide) (by simp) (fit wE (by decide))]; exact h.vE
  have nD : num t2.mem (rvB s0) (wW (kK s0)) wD = dV s0 := by
    rw [m2, k1.num (by decide) (by simp) (fit wD (by decide))]; exact h.vD
  have hM : num t2.mem (rvB s0) (wW (kK s0)) wMod = 2 ^ (32 * wW (kK s0) - 1) := by rw [m2]; exact v1
  have bD : dV s0 < 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) := by
    have := os2ip_lt8 (dB s0); simp only [dB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have bE : eV s0 < 2 ^ (8 * (s0.gpr .r10).toNat) := by
    have := os2ip_lt8 (eB s0); simp only [eB, Spec.Rsa.bytesAt, List.length_map, List.length_range] at this
    exact this
  have fitT : 8 * (PPC64LE.stackArg s0 1).toNat + 8 * (s0.gpr .r10).toNat ≤ 32 * wW (kK s0) - 1 := by
    rw [hW]; omega_arith
  have p1 : 2 ^ (8 * (PPC64LE.stackArg s0 1).toNat) ≤ 2 ^ (32 * wW (kK s0) - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine WP.mono (mulMod_ok w2' (by decide) (show MulIdx 16 wZ wE wD wM wMod wT by decide)
    (k := 8 * (s0.gpr .r10).toNat) (by omega_arith) (by omega_arith) a4) fun u ⟨wu, ku, kru, val⟩ => ?_
  have hm2 : 2 * 2 ^ (32 * wW (kK s0) - 1) ≤ 2 ^ (32 * wW (kK s0)) := by
    rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hv := val (n0 wZ (by simp)) (by rw [n0 wM (by simp), hM]; exact Nat.two_pow_pos _)
    (by rw [nD, hM]; omega_arith) (by rw [hM]; exact hm2)
  rw [n0 wM (by simp), nE, nD, hM] at hv
  refine ⟨wu, ?_, ?_, ?_, ((kr1.trans k2).trans kru).mono⟩
  · rw [m2] at ku
    exact KeyWorkspace.Keep.join k1 ku
  · rw [hv]; exact VG.Proof.Rsa.recover_product_exact bD bE fitT
  · rw [ku.num (by decide) (by simp [VG.Impl.Rsa.PPC64LE.Keys.sB, VG.Impl.Rsa.PPC64LE.Keys.sC, KeyWorkspace.hdr]) (fit wZ (by decide))]; exact n0 wZ (by simp)

theorem slot_le_one {m : Mem} {B : Addr} {d : Nat} (h : w32 m B d ≤ 1) :
    ((m.readW (off B d) 32).setWidth 64).toNat ≤ 1 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.readW (off B d) 32).isLt; omega_arith)]; exact h

/-- `numbers`: the numbers read, `M = d e`, its low bit cleared, and whether to try candidates. -/
theorem numbers_ok {s0 t : State} (e : REnt s0 t) : WP isa numbers t (NumS s0) := by
  have z := e.base.sz
  have w1 := z.w1; have w2 := z.w2; have svW := z.svW; have nw := z.nw; have svZ := z.svZ
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  have hSW : S (wW (kK s0)) = 4 * (wW (kK s0) + 2) := rfl
  unfold numbers
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok e) fun t1 ⟨h1, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (prod_ok h1) fun t2 ⟨w2', kk2, vM2, vZ2, k2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil skipBits]
  unfold skipBits
  rw [List.append_assoc]
  refine bitOf_ok w2' (j := wM) (sl := sBit) (by decide) (by decide) (by decide) fun t3 w3 kk3 sl3 k3 => ?_
  refine clrLow_ok w3 (j := wM) (by decide) (by decide) fun t4 w4 kk4 vM4 k4 _ => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok w4 (o := wT) (a := wZ) (b := wM) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t5 ⟨w5, kk5, v5, b5, k5⟩ => ?_
  rw [show seqs [.block skipTest] = .block skipTest from rfl, skipTest, ← List.append_nil (VG.Impl.Rsa.PPC64LE.Recover.ctxw),
    WP.block_append_iff]
  have fit : ∀ j < 16, arr (wW (kK s0)) j + S (wW (kK s0)) ≤ 2 ^ 64 := fun j hj => w5.fit64 hj
  have slot5 : w32 t5.mem (rvB s0) sBit = dV s0 * eV s0 % 2 := by
    show KeyWorkspace.slot t5.mem (rvB s0) sBit = _
    rw [KeyWorkspace.Keep.slot (e := sBit) kk5 (by decide) (by simp), KeyWorkspace.Keep.slot (e := sBit) kk4 (by decide)
      (by simp)]
    exact sl3.trans (by rw [vM2])
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun u => u.gpr .r0 = (((t5.mem.readW (off (rvB s0) sBit) 32).setWidth 64)
    &&& t5.gpr .r9) ^^^ BitVec.ofNat 64 1 ∧ u.mem = t5.mem ∧ u.gpr .r9 = t5.gpr .r9)
    (by prun [w5.r31, exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sBit < 2 ^ 15 by decide),
      w5.scr.ld (show sBit + 4 ≤ rvZ s0 by have := w5.hdr_le; simp only [sBit, KeyWorkspace.hdr] at this ⊢; omega_arith)])
    (by decide))
    fun t6 ⟨⟨a0, m6, a9⟩, k6⟩ => ?_
  refine ctxw_ok (w5.of_keep k6) (by omega_arith) (by rw [← z.svw]; omega_arith) fun t7 w7 m7 k7 => WP.block_nil ?_
  -- What the steps kept.
  have K : Keep (.r4 :: .r29 :: .r30 :: opRegs) t1 t7 :=
    ((((k2.trans k3).trans k4).trans k5).trans (k6.trans k7)).mono
  have KK : KeyWorkspace.Keep (rvB s0) (wW (kK s0)) [wMod, wE, wD, wM, wT, wT + 1, wT + 2, wT + 3]
      [VG.Impl.Rsa.PPC64LE.Keys.sB, VG.Impl.Rsa.PPC64LE.Keys.sC, sBit] t1.mem t7.mem := by
    rw [m7, m6]
    exact KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk2) (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk3)
      (KeyWorkspace.Keep.trans (KeyWorkspace.Keep.mono kk4) (KeyWorkspace.Keep.mono kk5)))
  have far : ∀ d n, arr (wW (kK s0)) 9 ≤ d → d + 4 * n ≤ 2 ^ 64 → val32 t7.mem (rvB s0) d n = val32 t1.mem (rvB s0) d n :=
    fun d n h1 h2 => keepW_far KK (by decide) (by simp [VG.Impl.Rsa.PPC64LE.Keys.sB, VG.Impl.Rsa.PPC64LE.Keys.sC, sBit])
      h1 h2
  have hA9 : arr (wW (kK s0)) 9 = arr (ww (kK s0)) 18 := arrW9 _
  have hAw : ∀ j i, arr (ww (kK s0)) j + 4 * i = 160 + j * (4 * (ww (kK s0) + 2)) + 4 * i := fun j i => rfl
  -- The test.
  have r9b : (t5.gpr .r9).toNat = 1 ↔ 2 ≤ dV s0 * eV s0 := by
    have lt := val32_lt t5.mem (rvB s0) (arr (wW (kK s0)) wT) (wW (kK s0))
    have lt' := val32_lt t3.mem (rvB s0) (arr (wW (kK s0)) wM) (wW (kK s0))
    have z0 : num t4.mem (rvB s0) (wW (kK s0)) wZ = 0 := by
      rw [kk4.num (by decide) (by simp) (fit wZ (by decide)), kk3.num (by simp) (by simp [sBit, KeyWorkspace.hdr])
        (fit wZ (by decide))]
      exact vZ2
    have v3 : num t3.mem (rvB s0) (wW (kK s0)) wM = dV s0 * eV s0 := by
      rw [kk3.num (by simp) (by simp [sBit, KeyWorkspace.hdr]) (fit wM (by decide))]; exact vM2
    rw [z0, vM4, v3, Nat.zero_add] at v5
    simp only [num] at v5 lt
    constructor
    · intro h
      rw [h, Nat.mul_one] at v5
      have : 1 ≤ dV s0 * eV s0 / 2 := by omega_arith
      omega_arith
    · intro h
      rcases (show (t5.gpr .r9).toNat = 0 ∨ (t5.gpr .r9).toNat = 1 by omega_arith) with h0 | h1
      · rw [h0, Nat.mul_zero] at v5; omega_arith
      · exact h1
  refine ⟨h1.base.of_keep (w := wW (kK s0)) KK (fun j hj => ?_) (fun d hd => ?_) K,
    w7, by rw [K.gpr _ (by decide)]; exact h1.r21, by rw [K.gpr _ (by decide)]; exact h1.r23,
    by rw [K.gpr _ (by decide)]; exact h1.r24, by rw [K.gpr _ (by decide)]; exact h1.r25,
    by rw [K.gpr _ (by decide)]; exact h1.r26, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have : j < 16 := by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end this) svW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  · simp only [num]
    rw [far _ _ (by rw [hA9]; exact VG.Proof.Rsa.KeyWorkspace.arr_mono (by decide))
      (Nat.le_trans (Nat.add_le_add_left (by simp only [S]; omega_arith) _) (w7.fit64 (j := aN) (by decide)))]
    exact h1.vN
  · rw [m7, m6, kk5.num (by decide) (by simp) (fit wM (by decide)), vM4,
      kk3.num (by simp) (by simp [sBit, KeyWorkspace.hdr]) (fit wM (by decide)), vM2]
  · intro j hj i hi
    have hj' : j = 33 ∨ j = 34 := by simpa [aOne, aZ] using hj
    have f64 := w7.fit64 (j := j) (by simp only [nArr]; omega_arith)
    have := far (arr (ww (kK s0)) j + 4 * i) 1
      (by rw [hA9]; exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_mono (by omega_arith)) (Nat.le_add_right _ _))
      (by simp only [S] at f64; omega_arith)
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact h1.zK j hj i hi
  · rw [k7.gpr _ (by decide), a0, skip_val _ _ (slot_le_one (by rw [slot5]; omega_arith)) (by omega_arith)]
    rw [show ((t5.mem.readW (off (rvB s0) sBit) 32).setWidth 64).toNat = w32 t5.mem (rvB s0) sBit by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (t5.mem.readW (off (rvB s0) sBit) 32).isLt; omega_arith)],
      slot5, r9b]

end VG.Proof.Rsa.PPC64LE.Recover
