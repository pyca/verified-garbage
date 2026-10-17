module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.TrialP
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: trial division by the table (`trialLoop_ok`)

`TO … k`: after `k` words of the table (`2 k` primes), `r11` holds whether
one of them divides `c` (`tr`), `r12` points at word `k` and `lr` counts the
words left.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Impl.RsaKeyGen VG.Proof.RsaKeyGen
open VG.Proof.Rsa (b2n)

/-- Whether one of the first `n` entries of the table divides `c`. -/
def tr (n c : Nat) : Bool := (List.range n).any fun i => c % tabEntry i == 0

theorem tr_succ (n c : Nat) : tr (n + 1) c = (tr n c || decide (c % tabEntry n = 0)) := by
  simp only [tr, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  congr 1

theorem trialStep_eq : trialStep =
    .seq (.block [.ldr .r10 .r12 0, .dp .add .r12 .r12 (.imm 4)])
      (.seq (.block ([.mov .r3 (.shifted .r10 .lsl 16), .mov .r3 (.shifted .r3 .lsr 16)] ++ entryS))
        (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag)
          (.seq (.block ([.mov .r3 (.shifted .r10 .lsr 16)] ++ entryS))
            (.seq (.loop (.block trialWord) .ne) (.seq (.block trialFlag) (.block [.subs .lr .lr (.imm 1)]))))))) :=
  rfl

/-- After `k` words of the table in `m`, for `c` the `W − 2` words at the key
array `aC`. -/
structure TO (B : BitVec 32) (Z W : Nat) (m : Mem) (u₀ : State) (k : Nat) (u : State) : Prop where
  ws : Ws u B Z W nArr
  mem : u.mem = m
  rest : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u₀ u
  r12 : u.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * k)
  lr : u.gpr .lr = BitVec.ofNat 32 (nT W - k)
  r11 : u.gpr .r11 = BitVec.ofNat 32 (b2n (tr (2 * k) (val32 m (State.addr B) (arr W aC) (W - 2))))

theorem w32_ofNat {m : Mem} {a : Addr} {x : Nat} (h : (m.readW a 32).toNat = x) : m.readW a 32 = BitVec.ofNat 32 x :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, ← h, Nat.mod_eq_of_lt (m.readW a 32).isLt])

/-- Word `k` of the table: its two primes. -/
theorem trialStep_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State} {k : Nat}
    (h : TO B Z W m u₀ k u) (hk : k < nT W) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa trialStep u fun u' => TO B Z W m u₀ (k + 1) u' ∧ u'.z = decide (nT W - (k + 1) = 0) := by
  obtain ⟨hw, mem, rest, r12, lr, r11⟩ := h
  have hn := hw.nowrap
  have hWl := hw.wle
  have hk512 : k < 512 := by simp only [nT] at hk; split at hk <;> omega
  have hz : arr W aTab + 4 * nT W ≤ Z := by
    have := nT_le hW; simp only [arr, S, nArr, aTab] at *; omega
  have hzc : arr W aC + 4 * W ≤ Z := by simp only [arr, S, nArr, aC] at *; omega
  set c := val32 m (State.addr B) (arr W aC) (W - 2) with ec
  have ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 0) = off (State.addr B) (arr W aTab + 4 * k) := by
    rw [r12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hw.addr (by omega)
  have rd : InRegions (u.rd ++ u.wr) (off (State.addr B) (arr W aTab + 4 * k)) 4 := hw.read (by omega)
  have tk : u.mem.readW (off (State.addr B) (arr W aTab + 4 * k)) 32 = BitVec.ofNat 32 (tabWord32 k) :=
    w32_ofNat (by rw [mem]; exact tab k hk)
  have e0 := tabEntry_facts (i := 2 * k) (by omega)
  have e1 := tabEntry_facts (i := 2 * k + 1) (by omega)
  rw [trialStep_eq]
  refine WP.seq (wp_ldr (by decide) ea rd fun u1 v1 => wp_dp (op2_imm (by decide)) fun u2 v2 => WP.block_nil ?_)
  have k2 : Rest [.r10, .r12] u u2 := (v1.rest (by simp)).trans (v2.rest (by simp))
  have r10 : u2.gpr .r10 = BitVec.ofNat 32 (tabWord32 k) := by rw [v2.other _ (by decide), v1.gpr, tk]
  have r12' : u2.gpr .r12 = B + BitVec.ofNat 32 (arr W aTab + 4 * (k + 1)) := by
    rw [v2.gpr, dpVal, v1.other _ (by decide), r12, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      ← BitVec.ofNat_add]
    congr 2
  have hw2 := hw.rest k2
  -- The first prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsl (by decide)) fun u3 v3 => wp_mov (op2_lsr (by decide)) fun u4 v4 =>
    WP.block_nil ?_)
  have k4 : Rest [.r3] u2 u4 := (v3.rest (by simp)).trans (v4.rest (by simp))
  have r34 : u4.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v4.gpr, v3.gpr, lo16, r10, ofNat_toNat_lt (tabWord32_lt hk512), tabWord32_lo hk512,
      ofNat_toNat_lt (by omega)]
  refine prime_ok (f := tr (2 * k) c) (hw2.rest k4) (by omega) hWe hzc (by rw [v4.mem, v3.mem, v2.mem, v1.mem, mem]) r34
    ⟨e0.1, e0.2.1, e0.2.2⟩ (ninv_tab (by omega)) (by rw [k4.gpr _ (by decide), k2.gpr _ (by decide), r11])
    fun u5 k5 m5 r115 => ?_
  -- The second prime.
  refine WP.seq ?_
  refine WP.block_append (wp_mov (op2_lsr (by decide)) fun u6 v6 => WP.block_nil ?_)
  have k6 : Rest [.r3] u5 u6 := v6.rest (by simp)
  have r36 : u6.gpr .r3 = BitVec.ofNat 32 (tabEntry (2 * k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [v6.gpr, hi16, k5.gpr _ (by decide), k4.gpr _ (by decide), r10, ofNat_toNat_lt (tabWord32_lt hk512),
      tabWord32_hi hk512, ofNat_toNat_lt (by omega)]
  have hw5 : Ws u5 B Z W nArr := (hw2.rest k4).rest k5
  refine prime_ok (f := tr (2 * k) c || decide (c % tabEntry (2 * k) = 0)) (hw5.rest k6) (by omega) hWe hzc
    (by rw [v6.mem, m5]) r36 ⟨e1.1, e1.2.1, e1.2.2⟩ (ninv_tab (by omega)) (by rw [k6.gpr _ (by decide), r115])
    fun u7 k7 m7 r117 => ?_
  -- The count.
  refine wp_subs (op2_imm (by decide)) fun u8 v8 z8 => WP.block_nil ?_
  have kall : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] u u8 :=
    (k2.mono (by simp)).trans ((k4.mono (by simp)).trans ((k5.mono (by simp)).trans ((k6.mono (by simp)).trans
      ((k7.mono (by simp)).trans (v8.rest (by simp))))))
  have lr8 : u8.gpr .lr = BitVec.ofNat 32 (nT W - (k + 1)) := by
    rw [v8.gpr, k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide),
      k2.gpr _ (by decide), lr]
    apply BitVec.eq_of_toNat_eq
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine ⟨⟨hw.rest kall, by rw [v8.mem, m7], rest.trans kall, ?_, lr8, ?_⟩, ?_⟩
  · rw [v8.other _ (by decide), k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide),
      k4.gpr _ (by decide), r12']
  · rw [v8.other _ (by decide), r117, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, tr_succ, tr_succ]
  · rw [z8, ← v8.gpr, lr8]
    have : nT W ≤ 512 := by simp only [nT]; split <;> omega
    by_cases h0 : nT W - (k + 1) = 0
    · simp [h0]
    · have : (BitVec.ofNat 32 (nT W - (k + 1))) ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [ofNat_toNat_lt (by omega)] at this; simpa using this)
      simpa [h0] using this

/-- All the words of the table. -/
theorem trialLoop_ok {B : BitVec 32} {Z W : Nat} {m : Mem} {u₀ u : State}
    (h : TO B Z W m u₀ 0 u) (hW : 10 ≤ W) (hWe : W % 2 = 0) (hZ : arr W nArr ≤ Z)
    (tab : ∀ j < nT W, w32 m (State.addr B) (arr W aTab + 4 * j) = tabWord32 j) :
    WP isa (.loop trialStep .ne) u (TO B Z W m u₀ (nT W)) := by
  have hT : 0 < nT W := by simp only [nT]; split <;> omega
  refine WP.loop (M := isa) (fun n v => 0 < n ∧ n ≤ nT W ∧ TO B Z W m u₀ (nT W - n) v)
    (fun n v ⟨hn, hn2, hu⟩ => ?_) (nT W) u ⟨hT, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  refine WP.mono (trialStep_ok hu (by omega) hW hWe hZ tab) fun u' ⟨hu', z⟩ => ?_
  rw [isa_ne, z]
  by_cases h0 : n = 1
  · subst h0
    refine .inl ⟨by simp; omega, ?_⟩
    rwa [show nT W - 1 + 1 = nT W by omega] at hu'
  · refine .inr ⟨by simp; omega, n - 1, by omega, by omega, by omega, ?_⟩
    rwa [show nT W - n + 1 = nT W - (n - 1) by omega] at hu'

end VG.Proof.RsaKeyGen.Arm.Cand
