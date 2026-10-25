module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCF
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots
public import VerifiedGarbage.Proof.Rsa.RecoverFusedBounds
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCtx
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.RecoverExp

/-!
# `vg_rsa_recover_primes` on PPC64LE: a candidate set up

`BI`: the fused pass of a candidate at a state of the shared model.
`cand0_ok`, `candSet` and the product after it: for the candidate `j`
(`g = j + 2`), `y = R mod n` (1 in Montgomery form), the root 0, `done`,
not `ok`, `g R mod n`, and the count of `m`'s digits: the pass's start.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (candSet mmul mBase mR2 mY mG aN aOne aZ aO aRoot nArr iG iR2 sOk sDone)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `t` and `r` of `m = 2^t r`. -/
abbrev tT (s0 : State) : Nat := (Spec.Rsa.splitTwos (mV s0)).1
abbrev rR (s0 : State) : Nat := (Spec.Rsa.splitTwos (mV s0)).2

/-- The modulus is odd and at least 2. -/
structure NOk (s0 : State) : Prop where
  odd : nV s0 % 2 = 1
  big : 128 ≤ nV s0

theorem NOk.of_valid {s0 : State} (h : Spec.Rsa.modulusValid (nV s0) (kK s0) = true) : NOk s0 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, Nat.le_trans (Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ 511 by decide)) h.1.1.2⟩

theorem NOk.coprime {s0 : State} (h : NOk s0) : Nat.Coprime (RR s0) (nV s0) :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

/-- A number below `n` is its low digits. -/
theorem low_of_lt {m : Mem} {s0 : State} {j : Nat} (h : num m (rvB s0) (ww (kK s0)) j < nV s0) :
    lowV m s0 j = num m (rvB s0) (ww (kK s0)) j :=
  low_eq (Nat.lt_trans h nV_lt)

theorem ofNat_add2 (j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 2).setWidth 32 = BitVec.ofNat 32 (j + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

theorem arrW (w j : Nat) : arr (2 * w + 2) j = arr w (2 * j) := by
  simp only [arr, S]; grind

theorem arrW_end (w j : Nat) : arr w (2 * j) + 4 * (2 * w + 2) ≤ arr w (2 * j + 2) := by
  simp only [arr, S]; grind

/-- A number of the `W` view kept by a step on other key arrays. -/
theorem keepW_num {s0 : State} {js : List Nat} {m m' : Mem}
    (k : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js [] m m') {j : Nat} (hj : ∀ i ∈ js, i < 2 * j ∨ 2 * j + 2 ≤ i)
    (hf : arr (ww (kK s0)) (2 * j + 2) ≤ 2 ^ 64) :
    num m' (rvB s0) (wW (kK s0)) j = num m (rvB s0) (wW (kK s0)) j := by
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  have e2 := arrW_end (ww (kK s0)) j
  change val32 m' (rvB s0) (arr (wW (kK s0)) j) (wW (kK s0)) = val32 m (rvB s0) (arr (wW (kK s0)) j) (wW (kK s0))
  rw [hW, arrW]
  exact keep_apart k (fun i hi => arr_apart (hj i hi) (Nat.le_refl _) e2) (by simp) (Nat.le_trans e2 hf)

/-- The pass of the candidate `j` at the state `st` of the shared model
(`Proof/Rsa/RecoverFused.lean`), in Montgomery form: `y`, the root if there
is one (the array is some number below `n` regardless), `ok` (whether there
is one) and `done`; and `g R mod n`. -/
structure BI (s0 : State) (j : Nat) (st : Fused.State) (u : State) : Prop where
  cf : CF s0 u
  r24 : u.gpr .r24 = BitVec.ofNat 64 j
  vY : num u.mem (rvB s0) (ww (kK s0)) mY = st.value * RR s0 % nV s0
  vG : num u.mem (rvB s0) (ww (kK s0)) mG = (j + 2) * RR s0 % nV s0
  vRoot : ∀ y, st.root = some y → num u.mem (rvB s0) (ww (kK s0)) aRoot = y * RR s0 % nV s0
  rootLt : num u.mem (rvB s0) (ww (kK s0)) aRoot < nV s0
  ok : slot u.mem (rvB s0) sOk = b2n st.root.isSome
  done : slot u.mem (rvB s0) sDone = b2n st.done
  bnd : Fused.Bounded (nV s0) st

/-- The digits of `m` the pass reads, `⌈c / 32⌉`. -/
abbrev dD (s0 : State) : Nat := (cB s0 + 31) / 32

/-- The sizes the candidates need: `c > 0` bits for `m = d e - 1`, which is
even and positive, and its digits a number of the `W` view. -/
structure Par (s0 : State) : Prop where
  c0 : 0 < cB s0
  c31 : cB s0 < 2 ^ 31
  m0 : 0 < mV s0
  mc : mV s0 < 2 ^ cB s0
  me : mV s0 % 2 = 0
  dW : dD s0 ≤ wW (kK s0)

/-- A step on other arrays and slots keeps `BI`. -/
theorem BI.of_keep {s0 u v : State} {j : Nat} {st : Fused.State} (h : BI s0 j st u) {js ds : List Nat}
    (kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) js ds u.mem v.mem) (hj : ∀ j ∈ js, j ∈ wrJ)
    (hd : ∀ d ∈ ds, d ∈ wrD) (hjY : ∀ k ∈ js, k ≠ mY ∧ k ≠ mG ∧ k ≠ aRoot)
    (hdO : ∀ d ∈ ds, (sOk + 4 ≤ d ∨ d + 4 ≤ sOk) ∧ (sDone + 4 ≤ d ∨ d + 4 ≤ sDone)) {rs : List Reg}
    (k : Keep rs u v) (hw : Ws v (rvB s0) (rvZ s0) (ww (kK s0)) nArr)
    (hr : ∀ r ∈ rs, r ∉ [.r12, .r21, .r23, .r24, .r25, .r26, .r31] := by decide) : BI s0 j st v := by
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.cf.ws.fit64 hj
  have hd4 : ∀ d ∈ ds, d + 4 ≤ 160 := fun d hd' => by
    have := hd d hd'; simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨h.cf.of_keep kk hj hd k hw (fun r hr' hm => hr r hr' (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.bnd⟩
  · rw [k.gpr _ fun hm => hr _ hm (by simp)]; exact h.r24
  · rw [kk.num (fun k hk => (hjY k hk).1) hd4 (fit mY (by decide))]; exact h.vY
  · rw [kk.num (fun k hk => (hjY k hk).2.1) hd4 (fit mG (by decide))]; exact h.vG
  · intro y hy; rw [kk.num (fun k hk => (hjY k hk).2.2) hd4 (fit aRoot (by decide))]; exact h.vRoot y hy
  · rw [kk.num (fun k hk => (hjY k hk).2.2) hd4 (fit aRoot (by decide))]; exact h.rootLt
  · rw [kk.slot (e := sOk) (by decide) fun d hd' => (hdO d hd').1]; exact h.ok
  · rw [kk.slot (e := sDone) (by decide) fun d hd' => (hdO d hd').2]; exact h.done

theorem digits_eq {c : Nat} (hc : c < 2 ^ 31) :
    (BitVec.ofNat 64 c + BitVec.ofNat 64 31) >>> 5 = BitVec.ofNat 64 ((c + 31) / 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- `candSet` and `g := g R² R⁻¹`: the pass of the candidate `j` at its
start, and the digits to go. -/
theorem cand0_ok {s0 u : State} (h : CF s0 u) (hn : NOk s0) {j : Nat} (hj : j < 100)
    (h24 : u.gpr .r24 = BitVec.ofNat 64 j) (hc : cB s0 < 2 ^ 31) :
    WP isa (seqs ([candSet] ++ mmul iG iG iR2)) u fun t =>
      BI s0 j (Fused.eval (nV s0) (j + 2) 0) t ∧ t.gpr .r27 = BitVec.ofNat 64 (dD s0) := by
  have z := h.base.sz
  have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => h.ws.fit64 hj
  have hn0 : 0 < nV s0 := by have := hn.big; omega_arith
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  rw [wp_seqs_append (List.cons_ne_nil _ _) (by simp [mmul]), show seqs [candSet] = candSet from rfl]
  unfold candSet
  -- `[mG] := 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := mG) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u1 ⟨ws1, kk1, v1, k1, _⟩ => ?_
  have c1 := h.of_keep kk1 (by decide) (by simp) k1 ws1
  have z1 : num u1.mem (rvB s0) (ww (kK s0)) mG = 0 := by
    rw [v1]; exact val32_zeros fun i hi => h.zZ i (by omega_arith)
  -- Its low digit `:= g`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil ([Instr.addi .r0 .r24 2, .store .w .r0 .r5 0]),
    ← List.append_assoc]
  refine lowOp_ok (f := fun _ => BitVec.ofNat 32 (j + 2)) ws1 (j := mG) (by decide) (by decide)
    (fun v v5 vm kv => ?_) fun u2 ws2 kk2 v2 k2 _ => WP.block_nil ?_
  · refine WP.mono (WP.keep [.r0] ?_ (by decide)) fun u' ⟨m, k⟩ => ⟨m, k.mono⟩
    have e24 : v.gpr .r24 = BitVec.ofNat 64 j := by rw [kv.gpr _ (by decide), k1.gpr _ (by decide)]; exact h24
    prun [v5, vm, e24, (ws1.scr.congr kv.wr).st (show arr (ww (kK s0)) mG + 4 ≤ rvZ s0 by
      have := ws1.arr_fit (j := mG) (by decide); simp only [S] at this; omega_arith), ofNat_add2 j]
  have c2 := c1.of_keep kk2 (by decide) (by simp) k2 ws2
  have g2 : num u2.mem (rvB s0) (ww (kK s0)) mG = j + 2 := by
    rw [v2, z1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  -- `y := 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws2 (o := mY) (a := aO) (by decide) (by decide) (by decide) (by decide))
    fun u3 ⟨ws3, kk3, v3, k3, _⟩ => ?_
  have c3 := c2.of_keep kk3 (by decide) (by simp) k3 ws3
  -- The root `:= 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok ws3 (o := aRoot) (a := aZ) (by decide) (by decide) (by decide) (by decide))
    fun u4 ⟨ws4, kk4, v4, k4, _⟩ => ?_
  have c4 := c3.of_keep kk4 (by decide) (by simp) k4 ws4
  have R4 : num u4.mem (rvB s0) (ww (kK s0)) aRoot = 0 := by
    rw [v4]; exact val32_zeros fun i hi => c3.zZ i (by omega_arith)
  -- `done`, `ok` and the count.
  rw [show seqs [Code.block [.li .r0 1, .store .w .r0 .r31 sDone, .li .r0 0, .store .w .r0 .r31 sOk,
    .addi .r27 .r26 31, .lsr .d .r27 .r27 5]] = .block [.li .r0 1, .store .w .r0 .r31 sDone, .li .r0 0,
    .store .w .r0 .r31 sOk, .addi .r27 .r26 31, .lsr .d .r27 .r27 5] from rfl]
  have hz : 160 ≤ rvZ s0 := ws4.hdr_le
  refine WP.mono (WP.keep [.r0, .r27] (Q := fun x =>
    x.mem = (u4.mem.writeW (off (rvB s0) sDone) ((BitVec.ofNat 64 1).setWidth 32)).writeW (off (rvB s0) sOk)
      ((BitVec.ofNat 64 0).setWidth 32) ∧
    x.gpr .r27 = (u4.gpr .r26 + BitVec.ofNat 64 31) >>> 5) ?_ (by decide)) fun u5 ⟨⟨m5, a27⟩, k5⟩ => ?_
  · prun [ws4.r31, ws4.scr.st (show sDone + 4 ≤ rvZ s0 by simp only [sDone]; omega_arith),
      ws4.scr.st (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega_arith),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sDone < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide)]
  have kk5 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sDone, sOk] u4.mem u5.mem := by
    rw [m5]
    exact KeyWorkspace.Keep.trans (keep_slot _ _ (by simp) (by decide)) (keep_slot _ _ (by simp) (by decide))
  have c5 := c4.of_keep kk5 (by simp) (by decide) k5 (ws4.of_keep k5)
  have R24 : u5.gpr .r24 = BitVec.ofNat 64 j := by
    rw [k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide),
      k1.gpr _ (by decide)]; exact h24
  have R27 : u5.gpr .r27 = BitVec.ofNat 64 (dD s0) := by
    rw [a27, c4.r26, digits_eq hc]
  have G5 : num u5.mem (rvB s0) (ww (kK s0)) mG = j + 2 := by
    rw [kk5.num (by simp) (by decide) (fit mG (by decide)), kk4.num (by decide) (by simp) (fit mG (by decide)),
      kk3.num (by decide) (by simp) (fit mG (by decide))]
    exact g2
  -- `g R mod n`.
  refine WP.mono (mmul_ok c5.base c5.ws (o := iG) (a := iG) (b := iR2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c5.r12 c5.inv
    (by rw [c5.vMN]; exact (show lowV u5.mem s0 mR2 < nV s0 by rw [c5.vR2]; exact Nat.mod_lt _ hn0)))
    fun t ⟨_, ws8, kk8, lt8, eq8, k8⟩ => ?_
  have c8 := c5.of_keep kk8 (by decide) (by simp) k8 ws8
  change num t.mem (rvB s0) (ww (kK s0)) mG < lowV u5.mem s0 mBase at lt8
  change num t.mem (rvB s0) (ww (kK s0)) mG * RR s0 % lowV u5.mem s0 mBase =
    lowV u5.mem s0 mG * lowV u5.mem s0 mR2 % lowV u5.mem s0 mBase at eq8
  rw [c5.vMN, c5.vR2, low_of_lt (by rw [G5]; have := hn.big; omega_arith), G5, Nat.mul_mod_mod, ← Nat.mul_assoc] at eq8
  rw [c5.vMN] at lt8
  have G8 := VG.Proof.Bignum.mont_cancel hn.coprime eq8
  rw [Nat.mod_eq_of_lt lt8] at G8
  have e0 : Fused.eval (nV s0) (j + 2) 0 = ⟨1, none, true⟩ := by
    rw [Fused.eval_zero]; simp [Fused.start]
  rw [e0]
  refine ⟨⟨c8, by rw [k8.gpr _ (by decide)]; exact R24, ?_, G8, fun y hy => (by cases hy), ?_, ?_, ?_,
    ⟨hn1, fun y hy => (by cases hy)⟩⟩, by rw [k8.gpr _ (by decide)]; exact R27⟩
  · rw [kk8.num (by decide) (by simp) (fit mY (by decide)), kk5.num (by simp) (by decide) (fit mY (by decide)),
      kk4.num (by decide) (by simp) (fit mY (by decide)), v3, c2.vO, Nat.one_mul]
  · rw [kk8.num (by decide) (by simp) (fit aRoot (by decide)), kk5.num (by simp) (by decide) (fit aRoot (by decide)),
      R4]; exact hn0
  · rw [kk8.slot (e := sOk) (by decide) (by simp), m5, slot_write_self]; rfl
  · rw [kk8.slot (e := sDone) (by decide) (by simp), m5, slot_wne _ _ _ (by decide) (by decide) (by decide),
      slot_write_self]; rfl

end VG.Proof.Rsa.PPC64LE.Recover
