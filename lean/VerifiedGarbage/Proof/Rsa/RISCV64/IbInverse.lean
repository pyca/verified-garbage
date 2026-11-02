module
-- separate module: it imports the reduction's Mathlib algebra and `InvResult`, which only the registration's `Instances` reaches

public import VerifiedGarbage.Proof.Rsa.RISCV64.IbBatch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw

/-!
# The batched inverse on RISC-V: the batches

`loop_ok`: `3 (n + 1)` batches from the start of the inversion, counted in
`s7`; `loopG_ok`: as many batches of `f` and `g` alone.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.Divstep (oddInput)

theorem Ctx.of_keep7 {s t : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n)
    (k : Keep (.s7 :: kRegs) s t) : Ctx t B Z w N n :=
  ⟨h.ws.of_keep k, (k.gpr (by decide)).trans h.s8, h.npos, h.nw, h.room, h.wbig⟩

/-- After `k` batches. -/
def LoopAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1) - k) ∧
    StateAt t B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) k) ∧
    Keys.Frame B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

theorem loop_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1)))
    (hst : StateAt s B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) 0))
    (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) :
    WP isa (.loop batch (.nonzero .s7)) s (LoopAt s B Z w N n p iv x (3 * (n + 1))) := by
  have hn := h.nw
  have hw := h.ws.wle
  have cap : p + x < 2 ^ (32 * n + 1) := by rw [Nat.pow_succ]; omega
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  refine count_loop (by omega) (LoopAt s B Z w N n p iv x) (fun k hk t ⟨Ht, t7, It, Kt, kt⟩ => ?_)
    ⟨h, by simpa using h7, hst, Keys.Frame.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, a0, a1, b0, b1⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x)
    odd large hinv (by omega) ox k
  rw [show 3 * (n + 1) - k = (3 * (n + 1) - k - 1) + 1 by omega] at t7
  refine WP.mono (batch_ok Ht t7 It hN (cap := p + x) (by push_cast at bd ⊢; omega) fo fb gb cap a0 a1 b0 b1 pc
    (by omega) hinv) fun u ⟨Hu, Iu, u7, Ku, ku⟩ => ?_
  refine ⟨⟨Hu, by rw [u7]; congr 1, Iu, Kt.trans Ku, Keep.trans' kt ku⟩, ?_⟩
  rw [u7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- After `k` batches of `f` and `g`. -/
def LoopG (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1) - k) ∧
    StateG t B w n (Divstep.W32.invRun 30 p iv (oddInput p x) k) ∧
    Keys.Frame B w [aF, aG, aT1, aT2, aW] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

theorem loopG_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n) (h7 : s.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1)))
    (hst : StateG s B w n (Divstep.W32.invRun 30 p iv (oddInput p x) 0))
    (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) :
    WP isa (.loop batchG (.nonzero .s7)) s (LoopG s B Z w N n p iv x (3 * (n + 1))) := by
  have hn := h.nw
  have hw := h.ws.wle
  have cap : p + x < 2 ^ (32 * n + 1) := by rw [Nat.pow_succ]; omega
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  refine count_loop (by omega) (LoopG s B Z w N n p iv x) (fun k hk t ⟨Ht, t7, It, Kt, kt⟩ => ?_)
    ⟨h, by simpa using h7, hst, Keys.Frame.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, -, -, -, -⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x)
    odd large hinv (by omega) ox k
  rw [show 3 * (n + 1) - k = (3 * (n + 1) - k - 1) + 1 by omega] at t7
  refine WP.mono (batchG_ok (p := p) (iv := iv) Ht t7 It hN (cap := p + x) (by push_cast at bd ⊢; omega) fo fb gb
    cap) fun u ⟨Hu, Iu, u7, Ku, ku⟩ => ?_
  refine ⟨⟨Hu, by rw [u7]; congr 1, Iu, Kt.trans Ku, Keep.trans' kt ku⟩, ?_⟩
  rw [u7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: the end

`normalize_ok`: `a := (p - a) mod p` if `f < 0`; `doublings_ok`: `a 2^(6 (n + 1))
mod p`; `finishG_ok`, `finishY_ok`: `|f|` and `a` into arrays 1 and 3, `w`
words each.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.RISCV64.RegUpd

theorem sign31 (x : BitVec 32) : x.setWidth 64 >>> 31 = BitVec.ofNat 64 (if 2 ^ 31 ≤ x.toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ext32, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem shl2 (n : Nat) : BitVec.ofNat 64 n <<< 2 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The mask of a bit. -/
theorem mask01 (c : Bool) :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0) = if c then BitVec.allOnes 64 else 0 := by
  cases c <;> rfl

/-- The sign of a signed number is its top digit's. -/
theorem sv_neg (m : Mem) (B : Addr) (d n : Nat) :
    sv m B d n < 0 ↔ 2 ^ 31 ≤ w32 m B (d + 4 * n) := by
  have hv := val32_lt m B d n
  have ht := toInt_cond (m.readW (off B (d + 4 * n)) 32)
  have hl := (m.readW (off B (d + 4 * n)) 32).isLt
  unfold sv
  rw [ht]
  have hP : (0 : Int) < 2 ^ (32 * n) := by exact_mod_cast Nat.two_pow_pos _
  have hv' : (val32 m B d n : Int) < 2 ^ (32 * n) := by exact_mod_cast hv
  simp only [w32]
  generalize (m.readW (off B (d + 4 * n)) 32).toNat = T at hl ⊢
  generalize (2 : Int) ^ (32 * n) = P at hP hv' ⊢
  split
  · have : (T : Int) - 2 ^ 32 ≤ -1 := by omega
    have := Int.mul_le_mul_of_nonneg_left this (Int.le_of_lt hP)
    constructor <;> intro <;> omega
  · have : (0 : Int) ≤ T - 0 := by omega
    have := Int.mul_nonneg (Int.le_of_lt hP) this
    constructor <;> intro <;> omega

/-- `signF`: the mask of `f < 0` into `t4`. -/
theorem signF_ok {t : State} {B : Addr} {Z w N n : Nat} (h : Ctx t B Z w N n) :
    WP isa (.block signF) t fun u => (u.mem = t.mem ∧
      u.gpr .t4 = if decide (2 ^ 31 ≤ w32 t.mem B (arr w aF + 4 * n)) then BitVec.allOnes 64 else 0) ∧
      Keep [.t1, .t3, .t4, .t5] t u := by
  have nF : aF < N := by have := h.room; unfold aF; omega
  have fF := h.ws.arr_fit nF
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have := arr_al4 w aF
  have hs := h.ws.scr
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [exec_li, signF, runBlock_ptr B w, (show aF < 2048 by decide), h.ws.s10, h.ws.s11, h.s8, shl2,
    exec_load_w, fin64_exec_li_zero, hs.ld (show arr w aF + 4 * n + 4 ≤ Z by omega),
    Scr.al4 hs (show arr w aF + 4 * n + 4 ≤ Z by omega) (by omega), sign31]
  rw [← mask01]
  simp only [decide_eq_true_eq]

/-- `[o] := mask ? [b] : [a]` for the mask in `t4` of `f < 0`, the pointers
and the count of `n + 1` set after `signF`. -/
theorem signSel_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {o a b : Nat}
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (signSel o a b) s
      fun t => Ctx t B Z w N n ∧ Keys.Frame B w [o] [] s.mem t.mem ∧
        val32 t.mem B (arr w o) (n + 1) = (if sv s.mem B (arr w aF) n < 0 then val32 s.mem B (arr w b) (n + 1)
          else val32 s.mem B (arr w a) (n + 1)) ∧ Outside B (arr w o) (4 * (n + 1)) s.mem t.mem ∧
        Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have := arr_al4 w o
  have := arr_al4 w a
  have := arr_al4 w b
  rw [signSel, WP.seq_iff, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (signF_ok h) fun t1 ⟨⟨m1, r4⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [← List.append_assoc, ← List.append_assoc]
  refine ptrs_ok h1.ws (by omega) (by omega) (by omega) fun t2 p0 p1 p2 k2 m2 => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (cntN1_ok h2) fun t3 ⟨⟨p3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have q4 : t3.gpr .t4 = t1.gpr .t4 := (k3.gpr (by decide)).trans (k2.gpr (by decide))
  refine WP.mono (selLoop_ok (b := decide (2 ^ 31 ≤ w32 s.mem B (arr w aF + 4 * n))) h3.ws.scr
    (by rw [k3.gpr (by decide)]; exact p0) (by rw [k3.gpr (by decide)]; exact p1)
    (by rw [k3.gpr (by decide)]; exact p2) p3 (by rw [q4, r4]) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (ahead_any w o a (n + 1) (by omega)) (ahead_k hob (by omega)))
    fun t4 ⟨v4, out4, k4, _⟩ => ?_
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide)))
    (k3.mono (by decide))) (k4.mono (by decide))
  rw [m3, m2, m1] at v4 out4
  refine ⟨h.of_keep k, Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega)
    (by simp), ?_, out4, k⟩
  rw [v4]
  simp only [sv_neg, decide_eq_true_eq]

/-- `normalize`: `[a] = normal p a f`, for `a < p`. -/
theorem normalize_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p) :
    WP isa normalize s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aA, aT3, aT1] [] s.mem t.mem ∧
      val32 t.mem B (arr w aA) (n + 1) = Divstep.normal p a (sv s.mem B (arr w aF) n) ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have f3 := fitZ _ n3
  have fM := fitZ _ nM
  have fA := fitZ _ nA
  have := arr_al4 w aT3
  have := arr_al4 w aMz
  have := arr_al4 w aA
  rw [normalize]; simp only [seqs]; rw [WP.seq_iff]
  -- `[aT3] = p - a`.
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, m1, p0, p1, p2, p3, p4, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subLoop_ok h1.ws.scr p0 p1 p2 p3 (by rw [p4]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t2 ⟨b2, v2, out2, k2⟩ => ?_
  rw [m1, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, hp, ha] at v2
  rw [m1] at out2
  have K2 : Keys.Frame B w [aT3] [] s.mem t2.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega) (by simp)
  have h2 := h1.of_keep (k2.mono (by decide))
  have hR := val32_lt t2.mem B (arr w aT3) (n + 1)
  have hpR : p < 2 ^ (32 * (n + 1)) := by rw [← hp]; exact val32_lt _ _ _ _
  have v2' : val32 t2.mem B (arr w aT3) (n + 1) = p - a := by
    generalize 2 ^ (32 * (n + 1)) = R at hR hpR v2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b2 with e | e <;> rw [e] at v2 <;> omega
  -- `[aA] = f < 0 ? p - a : a`.
  rw [WP.seq_iff]
  refine WP.mono (signSel_ok h2 nA nA n3 hN (by decide)) fun t3 ⟨h3, K3, v3, _, k3⟩ => ?_
  rw [v2', keep_sv K2 (by omega) (by decide) (by simp) (fit _ nF),
    keep_val K2 (by omega) (by decide) (by simp) (fit _ nA), ha] at v3
  refine WP.mono (csub_ok (p := p) h3 nA nA n1 nM hN (by decide) (by decide) (by decide)
    (by rw [keep_val K3 (by omega) (by decide) (by simp) (fit _ nM), keep_val K2 (by omega) (by decide) (by simp)
      (fit _ nM), hp]) v3) fun t4 ⟨h4, K4, v4, k4⟩ => ?_
  refine ⟨h4, (K2.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp))), ?_,
    Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))) (Keep.trans' k3 k4)⟩
  rw [v4]
  unfold Divstep.normal
  by_cases f : sv s.mem B (arr w aF) n < 0
  · simp only [f, ↓reduceIte]
    rcases Nat.eq_zero_or_pos a with a0 | a0
    · subst a0; simp
    · rw [Nat.mod_eq_of_lt (by omega)]
      simp only [show ¬ p ≤ p - a by omega, ↓reduceIte]
  · simp only [f, ↓reduceIte, show ¬ p ≤ a by omega]

/-- `double`: `[a] = 2 a mod p`, for `a < p`. -/
theorem double_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p)
    (hpA : p < 2 ^ (32 * n)) :
    WP isa double s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aA, aT3, aT1] [] s.mem t.mem ∧
      val32 t.mem B (arr w aA) (n + 1) = (2 * a) % p ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have n1 : aT1 < N := by unfold aT1; omega
  rw [double]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (WP.keep [.a5] (Q := fun u => u.gpr .a5 = 1#64 ∧ u.mem = s.mem) (by brun [exec_li]; try rfl)
    (by rfl) (by rfl)) fun t1 ⟨⟨r5, m1⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := n + 1) (by omega) (by omega) n3 nA nA hN
    (by rw [r5]; decide)) fun t2 ⟨h2, K2, v2, c2, _, _, _, k2⟩ => ?_
  rw [m1, ha, r5, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul] at v2
  have hR : 2 * a < 2 ^ (32 * (n + 1)) := by
    have : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by rw [← Nat.pow_add]; congr 1; omega
    omega
  have v2' : val32 t2.mem B (arr w aT3) (n + 1) = 2 * a := by
    have := val32_lt t2.mem B (arr w aT3) (n + 1)
    generalize 2 ^ (32 * (n + 1)) = R at hR this v2
    rcases Nat.eq_zero_or_pos (t2.gpr .t4).toNat with e | e
    · rw [e] at v2; omega
    · have : R ≤ R * (t2.gpr .t4).toNat := Nat.le_mul_of_pos_right _ e
      omega
  rw [m1] at K2
  refine WP.mono (csub_ok (p := p) h2 nA n3 n1 nM hN (by decide) (by decide) (by decide)
    (by rw [keep_val K2 (by omega) (by decide) (by simp) (fit _ nM), hp]) v2') fun t3 ⟨h3, K3, v3, k3⟩ => ?_
  refine ⟨h3, (K2.mono (by simp)).trans (K3.mono (by simp)), ?_,
    Keep.trans' (Keep.trans' (k1.mono (by decide)) k2) k3⟩
  rw [v3]
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- After `k` doublings. -/
def DoubleAt (s₀ : State) (B : Addr) (Z w N n p a₀ : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (6 * (n + 1) - k) ∧
    val32 t.mem B (arr w aA) (n + 1) = Divstep.doubled p a₀ k ∧
    Keys.Frame B w [aA, aT3, aT1] [] s₀.mem t.mem ∧ Keep (.s7 :: kRegs) s₀ t

/-- `doublings`: `[a] = a 2^(6 (n + 1)) mod p`. -/
theorem doublings_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p)
    (hpA : p < 2 ^ (32 * n)) :
    WP isa doublings s (DoubleAt s B Z w N n p a (6 * (n + 1))) := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nM : aMz < N := by unfold aMz; omega
  rw [doublings, WP.seq_iff]
  refine WP.mono (WP.keep [.t5, .s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 (6 * (n + 1)) ∧
    u.mem = s.mem) ?_ (by rfl) (by rfl)) fun t0 ⟨⟨r7, m0⟩, k0⟩ => ?_
  · brun [exec_li, h.s8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h0 : Ctx t0 B Z w N n := h.of_keep7 (k0.mono (by decide))
  refine count_loop (by omega) (DoubleAt s B Z w N n p a) (fun k hk t ⟨Ht, t7, vt, Kt, kt⟩ => ?_)
    ⟨h0, by simpa using r7, by rw [m0, ha, Divstep.doubled_zero hap], by rw [m0]; exact Keys.Frame.refl _ _ _ _ _,
      k0.mono (by decide)⟩
  have pt : val32 t.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val Kt (by omega) (by decide) (by simp) (fit _ nM), hp]
  rw [WP.seq_iff]
  refine WP.mono (double_ok Ht hN pt vt (Divstep.doubled_lt (by omega)) hpA) fun u ⟨Hu, Ku, vu, ku⟩ => ?_
  rw [show 6 * (n + 1) - k = (6 * (n + 1) - k - 1) + 1 by omega] at t7
  have u7 : u.gpr .s7 = BitVec.ofNat 64 (6 * (n + 1) - k - 1 + 1) := (ku.gpr (by decide)).trans t7
  refine WP.mono (dec_ok u7) fun y ⟨⟨y7, ym⟩, ky⟩ => ?_
  refine ⟨⟨Hu.of_keep7 (ky.mono (by decide)), by rw [y7]; congr 1, by rw [ym, vu, Divstep.doubled_next],
    Kt.trans (by rw [ym]; exact Ku), Keep.trans' kt (Keep.trans' (ku.mono (by decide)) (ky.mono (by decide)))⟩, ?_⟩
  rw [y7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The end -/

/-- `k ≤ W + 1` digits holding `v < 2^(32 W)`, the digits after them zero to
digit `W`: the `W` digits are `v`. -/
theorem num_tail {m : Mem} {B : Addr} {d W k v : Nat} (hk : k ≤ W + 1) (hv : val32 m B d k = v)
    (hz : ∀ i, k ≤ i → i < W + 1 → w32 m B (d + 4 * i) = 0) (hvw : v < 2 ^ (32 * W)) : val32 m B d W = v := by
  have e1 := val32_append m B d k (W + 1 - k)
  have z : val32 m B (d + 4 * k) (W + 1 - k) = 0 := val32_zero (fun i hi => by
    rw [show d + 4 * k + 4 * i = d + 4 * (k + i) by omega]; exact hz _ (by omega) (by omega))
  rw [show k + (W + 1 - k) = W + 1 by omega, hv, z, Nat.mul_zero, Nat.add_zero, val32_succ] at e1
  have := val32_lt m B d W
  rcases Nat.eq_zero_or_pos (w32 m B (d + 4 * W)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero] at e1; exact e1
  · have : 2 ^ (32 * W) ≤ 2 ^ (32 * W) * w32 m B (d + 4 * W) := Nat.le_mul_of_pos_right _ e
    omega

/-- `finishG`: `[1] = |f|`, `w` words. -/
theorem finishG_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {f : Int}
    (hf : sv s.mem B (arr w aF) n = f) (hfr : f.natAbs < 2 ^ (32 * n)) :
    WP isa finishG s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aGcd, aT1] [] s.mem t.mem ∧
      num t.mem B w aGcd = f.natAbs ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nG : aGcd < N := by unfold aGcd; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have fG := fitZ _ nG
  have fF := fitZ _ nF
  have f1 := fitZ _ n1
  have := arr_al4 w aGcd
  have := arr_al4 w aF
  have := arr_al4 w aT1
  have hnw : 2 ^ (32 * n) ≤ 2 ^ (32 * (2 * w)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk1 : 4 * (n + 1) ≤ S w := by omega
  rw [finishG]; simp only [seqs]; rw [WP.seq_iff]
  -- `[1] = 0`.
  refine WP.mono (zeroW_ok h nG hN) fun t1 ⟨h1, K1, out1, z1, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (setup_ok h1 (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, m2, p0, p1, p2, p3, p4, k2⟩ => ?_
  rw [WP.seq_iff]
  -- `[aT1] = -f`.
  refine WP.mono (subLoop_ok h2.ws.scr p0 p1 p2 p3 (by rw [p4]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t3 ⟨b3, v3, out3, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have zG : val32 t1.mem B (arr w aGcd) (n + 1) = 0 := val32_zero (fun i hi => z1 i (by omega))
  rw [m2, p4, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, zG,
    keep_val K1 hk1 (by decide) (by simp) (fit _ nF)] at v3
  rw [m2] at out3
  have K3 : Keys.Frame B w [aT1] [] t1.mem t3.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out3) (by omega) (by simp)
  have hnw' := h.ws.nowrap
  refine WP.mono (signSel_ok h3 nG nF n1 hN (by decide)) fun t4 ⟨h4, K4, v4, out4, k4⟩ => ?_
  have sF : sv t3.mem B (arr w aF) n = f := by
    rw [keep_sv K3 hk1 (by decide) (by simp) (fit _ nF), keep_sv K1 hk1 (by decide) (by simp) (fit _ nF), hf]
  have vF : val32 t3.mem B (arr w aF) (n + 1) = val32 s.mem B (arr w aF) (n + 1) := by
    rw [out3.val32 (by have := arr_disj (w := w) (show aF ≠ aT1 by decide); omega) (by omega),
      keep_val K1 hk1 (by decide) (by simp) (fit _ nF)]
  rw [sF, vF] at v4
  have gcd1 : val32 t4.mem B (arr w aGcd) (n + 1) = f.natAbs := by
    rw [v4]
    have e := val_sv s.mem B (arr w aF) n
    rw [hf] at e
    have neg := sv_neg s.mem B (arr w aF) n
    rw [hf] at neg
    have hR := val32_lt t3.mem B (arr w aT1) (n + 1)
    have hFR := val32_lt s.mem B (arr w aF) (n + 1)
    split
    · have : 2 ^ 31 ≤ w32 s.mem B (arr w aF + 4 * n) := neg.mp (by assumption)
      simp only [this, ↓reduceIte] at e
      have eR : (2 : Int) ^ (32 * (n + 1)) = ((2 ^ (32 * (n + 1)) : Nat) : Int) := by push_cast; rfl
      rw [eR, Int.mul_one] at e
      have hRn : 2 ^ (32 * n) < 2 ^ (32 * (n + 1)) := Nat.pow_lt_pow_right (by decide) (by omega)
      generalize 2 ^ (32 * (n + 1)) = R at hR hFR v3 e hRn
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b3 with b | b <;> rw [b] at v3 <;> omega
    · have hn : ¬ f < 0 := by assumption
      have : ¬ 2 ^ 31 ≤ w32 s.mem B (arr w aF + 4 * n) := fun x => hn (neg.mpr x)
      simp only [this, ↓reduceIte] at e
      omega
  have k : Keep kRegs s t4 := Keep.trans' (Keep.trans' (Keep.trans' k1 (k2.mono (by decide)))
    (k3.mono (by decide))) k4
  refine ⟨h4, (K1.mono (by simp)).trans ((K3.mono (by simp)).trans (K4.mono (by simp))), ?_, k⟩
  rw [num_eq]
  refine num_tail (k := n + 1) (by omega) gcd1 (fun i hi1 hi2 => ?_) (by omega)
  rw [out4.w32 (by omega) (by omega), out3.w32 (by have := arr_disj (w := w) (show aGcd ≠ aT1 by decide); omega)
    (by omega)]
  exact z1 i (by omega)

/-- `finishY`: `[3] = y`, `w` words. -/
theorem finishY_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {y : Nat}
    (hy : val32 s.mem B (arr w aA) (n + 1) = y) (hyr : y < 2 ^ (32 * n)) :
    WP isa finishY s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aY] [] s.mem t.mem ∧
      num t.mem B w aY = y ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nY : aY < N := by unfold aY; omega
  have nA : aA < N := by unfold aA; omega
  have fY := fitZ _ nY
  have fA := fitZ _ nA
  have := arr_al4 w aY
  have := arr_al4 w aA
  have hnw : 2 ^ (32 * n) ≤ 2 ^ (32 * (2 * w)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk1 : 4 * (n + 1) ≤ S w := by omega
  have hnw' := h.ws.nowrap
  rw [finishY]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (zeroW_ok h nY hN) fun t5 ⟨h5, K5, out5, z5, k5⟩ => ?_
  rw [WP.seq_iff]
  have hb6 : WP isa (.block (ptr .t0 aY ++ ptr .t1 aA ++ cntN1)) t5 fun u => Ctx u B Z w N n ∧ u.mem = t5.mem ∧
      u.gpr .t0 = off B (arr w aY) ∧ u.gpr .t1 = off B (arr w aA) ∧ u.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧
      Keep kRegs t5 u := by
    refine ptr2_ok h5.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) fun t p0 p1 kt mt => ?_
    have ht := h5.of_keep (kt.mono (by decide))
    refine WP.mono (cntN1_ok ht) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs t5 x := (kt.trans kx).mono (by decide)
    refine ⟨h5.of_keep k0, xm.trans mt, ?_, ?_, x3, k0⟩
    · rw [kx.gpr (by decide)]; exact p0
    · rw [kx.gpr (by decide)]; exact p1
  refine WP.mono hb6 fun t6 ⟨h6, m6, q0, q1, q3, k6⟩ => ?_
  refine WP.mono (copyLoop_ok h6.ws.scr q0 q1 q3 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (ahead_k (by decide) (by omega))) fun t7 ⟨v7, out7, k7⟩ => ?_
  rw [m6] at v7 out7
  have K57 : Keys.Frame B w [aY] [] s.mem t7.mem := K5.trans
    (Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out7) (by omega) (by simp))
  have yA : val32 t5.mem B (arr w aA) (n + 1) = y := by
    rw [keep_val K5 hk1 (by decide) (by simp) (fit _ nA), hy]
  have k : Keep kRegs s t7 := Keep.trans' (Keep.trans' k5 k6) (k7.mono (by decide))
  refine ⟨h.of_keep k, K57, ?_, k⟩
  rw [num_eq]
  refine num_tail (k := n + 1) (by omega) (by rw [v7, yA]) (fun i hi1 hi2 => ?_) (by omega)
  rw [out7.w32 (by omega) (by omega)]
  exact z5 i (by omega)

end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V: the start

`init_ok`: from `x` in array 0 and the odd `m` in array 8, both below
`2^(32 n)`, the start of the inversion modulo `p = vmod m` (`m`, or 3 for
`m = 1`): `f = p`, `g = oddInput p x`, `a = 0`, `b = 1`, `d = 1`, with
`-p⁻¹ mod 2^32` in the window and `3 (n + 1)` batches to run.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys VG.Impl.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (ptr seqs mov)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.RISCV64.RegUpd
open VG.Proof.Rsa.Divstep (oddInput)

/-- `ptr r j` alone, run. -/
theorem runBlock_ptr_nil (B : Addr) (w : Nat) {s : State} {r : Reg} {j : Nat}
    (h10 : s.gpr .s10 = BitVec.ofNat 64 (S w)) (h11 : s.gpr .s11 = B) (hr10 : r ≠ .s10) (hr11 : r ≠ .s11)
    (hj : j < 2048) : runBlock isa (ptr r j) s = some (s.write r (off B (arr w j))) := by
  have := runBlock_ptr B w (s := s) (r := r) (j := j) [] h10 h11 hr10 hr11 hj
  rw [List.append_nil] at this
  rw [this, runBlock_nil]

/-- The modulus of the batches: `m`, or 3 for `m = 1`. -/
def vmod (m : Nat) : Nat := if m = 1 then 3 else m

/-- `k` digits of a number below `2^(32 k)` stored in `W ≥ k` digits. -/
theorem val_low {m : Mem} {B : Addr} {d W k v : Nat} (hk : k ≤ W) (hv : val32 m B d W = v)
    (hvk : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have e := val32_append m B d k (W - k)
  rw [show k + (W - k) = W by omega, hv] at e
  have := val32_lt m B d k
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (W - k)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * val32 m B (d + 4 * k) (W - k) := Nat.le_mul_of_pos_right _ z
    omega

/-- The virtualization's mask: 2 where `t4` is zero. -/
theorem virt_mask (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    (((BitVec.ofNat 64 0 - r) >>> 63 ^^^ BitVec.ofNat 64 1) <<< 1) = if r = 0#64 then 2#64 else 0#64 := by
  split
  · next e => subst e; decide
  · next e =>
    have : r.toNat ≠ 0 := fun h => e (BitVec.eq_of_toNat_eq h)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h1 : (2 ^ 64 - r.toNat + (BitVec.ofNat 64 0).toNat) % 2 ^ 64 / 2 ^ 63 = 1 := by
      rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl]; omega
    rw [h1]
    rfl

/-- The new low digit of the modulus: `d₀ | 2` where it is `1` (the modulus 1). -/
theorem virt_digit (d : BitVec 32) (b : Bool) :
    ((d.setWidth 64 ||| (if b then 2#64 else 0#64)).setWidth 32).toNat =
      if b ∧ d.toNat = 1 then 3 else if b then (d.toNat ||| 2) else d.toNat := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, BitVec.or_zero]
    rw [BitVec.toNat_setWidth, toNat_ext32]; exact Nat.mod_eq_of_lt d.isLt
  · simp only [↓reduceIte, true_and]
    rw [BitVec.toNat_setWidth, BitVec.toNat_or, toNat_ext32, show (2#64).toNat = 2 from rfl]
    have : d.toNat ||| 2 < 2 ^ 32 := Nat.or_lt_two_pow d.isLt (by decide)
    split
    · next e => rw [e]; rfl
    · exact Nat.mod_eq_of_lt this

/-- `m` of `k + 1` digits, its top digit replaced by zero. -/
theorem val_top0 {mm : Mem} {B : Addr} {d k : Nat} (h : d + 4 * k + 4 ≤ 2 ^ 64) :
    val32 (mm.writeW (off B (d + 4 * k)) (0 : BitVec 32)) B d (k + 1) = val32 mm B d k := by
  rw [val32_write_top _ _ _ _ _ h]; simp

/-- Bit 0 of a digit, inverted. -/
theorem even_bit (x : BitVec 32) :
    (((x.setWidth 64 &&& BitVec.ofNat 64 1) ^^^ BitVec.ofNat 64 1)).toNat = (if x.toNat % 2 = 0 then 1 else 0) := by
  rw [BitVec.toNat_xor, BitVec.toNat_and, toNat_ext32, BitVec.toNat_ofNat, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> rfl

/-- The registers `init` changes. -/
abbrev initRegs : List Reg := .s7 :: kRegs

/-- `init`: the start of the inversion modulo `vmod m`. -/
theorem initA_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {m : Nat}
    (hm : val32 s.mem B (arr w aMin) n = m) :
    WP isa initA s fun t => Ctx t B Z w N n ∧ Keys.Frame B w [aMz, aB] [] s.mem t.mem ∧
      val32 t.mem B (arr w aMz) (n + 1) = vmod m ∧ val32 t.mem B (arr w aB) (n + 1) = 1 ∧ Keep kRegs s t := by
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := h.nw
  have hn1 := h.npos
  have := h.wbig
  have hnw' := h.ws.nowrap
  have hs := h.ws.scr
  have room := h.room
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nB : aB < N := by unfold aB; omega
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nX : aX < N := by unfold aX; omega
  have nI : aMin < N := by unfold aMin; omega
  have fM := fitZ _ nM
  have fB := fitZ _ nB
  have fW := fitZ _ nW
  have fF := fitZ _ nF
  have fG := fitZ _ nG
  have fA := fitZ _ nA
  have fX := fitZ _ nX
  have fI := fitZ _ nI
  have := arr_al4 w aMz
  have := arr_al4 w aB
  have := arr_al4 w aF
  have := arr_al4 w aG
  have := arr_al4 w aA
  have := arr_al4 w aX
  have := arr_al4 w aMin
  have aW8 := arr_al w aW
  have aM8 := arr_al w aMz
  have hk1 : 4 * (n + 1) ≤ S w := by omega
  simp only [initA, seqs]
  -- 1: `[2] = m`.
  rw [WP.seq_iff, WP.seq_iff]
  refine ptr2_ok h.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u p0 p1 ku mu => ?_
  refine WP.mono (cntN_ok (h.of_keep (ku.mono (by decide)))) fun u' ⟨⟨u3, um'⟩, ku'⟩ => ?_
  have k1a : Keep kRegs s u' := (ku.trans ku').mono (by decide)
  refine WP.mono (copyLoop_ok (dO := arr w aMz) (dA := arr w aMin) (h.of_keep k1a).ws.scr
    (by rw [ku'.gpr (by decide)]; exact p0) (by rw [ku'.gpr (by decide)]; exact p1) u3 hn1
    (by omega) (by omega) (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega))) fun t1 ⟨v1, out1, kt1⟩ => ?_
  rw [um', mu] at v1 out1
  have k1 : Keep kRegs s t1 := Keep.trans' k1a (kt1.mono (by decide))
  have h1 := h.of_keep k1
  have K1 : Keys.Frame B w [aMz] [] s.mem t1.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out1) (by omega) (by simp)
  rw [hm] at v1
  -- 2: its digit `n` zero, `[b] = 0`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (WP.keep [.t0, .t1, .t3, .t5] (Q := fun u => u.mem = t1.mem.writeW (off B (arr w aMz + 4 * n))
      (0 : BitVec 32) ∧ u.gpr .t0 = off B (arr w aB) ∧ u.gpr .t3 = BitVec.ofNat 64 (n + 1)) ?_ (by rfl) (by rfl))
    fun t2 ⟨⟨m2, q0, q3⟩, k2⟩ => ?_
  · brun [exec_li, setTop, cntN1, List.append_assoc, runBlock_ptr B w, (show aMz < 2048 by decide),
      (show aB < 2048 by decide), h1.ws.s10, h1.ws.s11, h1.s8, shl2, ofNat_succ, exec_store_w,
      fin64_exec_li_zero, h1.ws.scr.st (show arr w aMz + 4 * n + 4 ≤ Z by omega),
      Scr.al4 h1.ws.scr (show arr w aMz + 4 * n + 4 ≤ Z by omega) (by omega)]
    try rfl
  have h2 := h1.of_keep (k2.mono (by decide))
  rw [zeros, WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun y => y.gpr .t5 = 0 ∧ y.mem = t2.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y ⟨⟨y5, ym⟩, ky⟩ => ?_
  refine WP.mono (zeroLoop_ok (h2.of_keep (ky.mono (by decide))).ws.scr (dO := arr w aB) (n := n + 1)
    (by rw [ky.gpr (by decide)]; exact q0) (by rw [ky.gpr (by decide)]; exact q3) y5 (by omega) (by omega)
    (by omega) (by omega)) fun t4 ⟨z4, out4, k4⟩ => ?_
  rw [ym, m2] at out4
  have k24 : Keep kRegs t1 t4 := Keep.trans' (Keep.trans' (k2.mono (by decide)) (ky.mono (by decide)))
    (k4.mono (by decide))
  have h4 := h1.of_keep k24
  have vM4 : val32 t4.mem B (arr w aMz) (n + 1) = m := by
    rw [out4.val32 (by have := arr_disj (w := w) (show aMz ≠ aB by decide); omega) (by omega),
      val_top0 (by omega), v1]
  have zB : ∀ i < n + 1, w32 t4.mem B (arr w aB + 4 * i) = 0 := z4
  -- 3: `[b] = 1`, and whether `m = 1`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (WP.keep [.t0, .t1, .t2, .t3, .t4, .t5] (Q := fun u =>
      u.mem = t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32) ∧
      u.gpr .t1 = off B (arr w aMz) ∧ u.gpr .t2 = off B (arr w aB) ∧ u.gpr .t3 = BitVec.ofNat 64 (n + 1) ∧
      u.gpr .t4 = 0) ?_ (by rfl) (by rfl)) fun t5 ⟨⟨m5, p1', p2', q3', p4'⟩, k5⟩ => ?_
  · brun [exec_li, cntN1, List.append_assoc, runBlock_ptr B w, (show aMz < 2048 by decide),
      (show aB < 2048 by decide), h4.ws.s10, h4.ws.s11, h4.s8, ofNat_succ, exec_store_w,
      fin64_exec_li_zero, h4.ws.scr.st (show arr w aB + 4 ≤ Z by omega),
      Scr.al4 h4.ws.scr (show arr w aB + 4 ≤ Z by omega) (by omega)]
    try rfl
  have h5 := h4.of_keep (k5.mono (by decide))
  have o5 := writeW32_outside t4.mem B (d := arr w aB) ((BitVec.ofNat 64 1).setWidth 32) (by omega)
  have vB5 : val32 t5.mem B (arr w aB) (n + 1) = 1 := by
    rw [m5]
    have e : val32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB) (n + 1) =
        w32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB) +
        2 ^ 32 * val32 (t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32)) B (arr w aB + 4) n := rfl
    rw [e, w32_write_self, o5.val32 (by omega) (by omega),
      val32_zero (fun i hi => by rw [show arr w aB + 4 + 4 * i = arr w aB + 4 * (i + 1) by omega]; exact zB _ (by omega))]
    rfl
  have vM5 : val32 t5.mem B (arr w aMz) (n + 1) = m := by
    rw [m5, o5.val32 (by have := arr_disj (w := w) (show aMz ≠ aB by decide); omega) (by omega), vM4]
  refine WP.mono (eqLoop_ok h5.ws.scr p1' p2' q3' p4' (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)) fun t6 ⟨e6, l6, m6, k6⟩ => ?_
  have h6 := h5.of_keep (k6.mono (by decide))
  rw [vM5, vB5] at e6
  -- 4: `p = vmod m` in `[2]`.
  refine WP.mono (WP.keep [.t0, .t5, .t6] (Q := fun u =>
      u.mem = t6.mem.writeW (off B (arr w aMz)) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .t4 = 0#64 then 2#64 else 0#64)).setWidth 32)) ?_ (by rfl) (by rfl)) fun t7 ⟨m7, k7⟩ => ?_
  · brun [exec_li, List.append_assoc, runBlock_ptr B w, (show aMz < 2048 by decide), h6.ws.s10, h6.ws.s11,
      exec_load_w, exec_store_w, fin64_exec_li_zero, h6.ws.scr.ld (show arr w aMz + 4 ≤ Z by omega),
      h6.ws.scr.st (show arr w aMz + 4 ≤ Z by omega),
      Scr.al4 h6.ws.scr (show arr w aMz + 4 ≤ Z by omega) (by omega)]
    rw [← virt_mask _ l6]
  have h7 := h6.of_keep (k7.mono (by decide))
  have pv : val32 t7.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [m6] at m7
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n := rfl
    have em : val32 t5.mem B (arr w aMz) (n + 1) = w32 t5.mem B (arr w aMz) + 2 ^ 32 * val32 t5.mem B (arr w aMz + 4) n :=
      rfl
    rw [vM5] at em
    have o7 := writeW32_outside t5.mem B (d := arr w aMz) (((t5.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .t4 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [e, m7, w32_write_self, o7.val32 (by omega) (by omega)]
    have vd := virt_digit (t5.mem.readW (off B (arr w aMz)) 32) (decide (t6.gpr .t4 = 0#64))
    simp only [decide_eq_true_eq] at vd
    rw [vd]
    unfold vmod
    by_cases e1 : m = 1
    · have z : t6.gpr .t4 = 0#64 := e6.mpr (by rw [e1])
      have : w32 t5.mem B (arr w aMz) = 1 ∧ val32 t5.mem B (arr w aMz + 4) n = 0 := by
        simp only [w32] at em ⊢; omega
      simp only [z, true_and, ↓reduceIte, e1]
      rw [show (t5.mem.readW (off B (arr w aMz)) 32).toNat = 1 from this.1, this.2]
      rfl
    · have z : ¬ t6.gpr .t4 = 0#64 := fun x => e1 (by have := e6.mp x; omega)
      simp only [z, false_and, ↓reduceIte, e1]
      simp only [w32] at em
      omega
  have a2 : Keys.Frame B w [aMz] [] t1.mem t2.mem := by
    rw [m2]; exact Keys.Frame.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a4 : Keys.Frame B w [aB] [] t2.mem t4.mem := by
    rw [m2]; exact Keys.Frame.of_arr (o := aB) (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega) (by simp)
  have a5 : Keys.Frame B w [aB] [] t4.mem t5.mem := by
    rw [m5]; exact Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using o5) (by omega) (by simp)
  have a7 : Keys.Frame B w [aMz] [] t6.mem t7.mem := by
    have o := writeW32_outside t6.mem B (d := arr w aMz) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
      (if t6.gpr .t4 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [m7]; exact Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using o) (by omega) (by simp)
  refine ⟨h7, (K1.mono (by simp)).trans ((a2.mono (by simp)).trans ((a4.mono (by simp)).trans ((a5.mono (by simp)).trans
      ((show Keys.Frame B w [aMz, aB] [] t5.mem t6.mem by rw [m6]; exact Keys.Frame.refl _ _ _ _ _).trans
        (a7.mono (by simp)))))), pv, ?_,
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' k1 k24) (k5.mono (by decide))) (k6.mono (by decide)))
      (k7.mono (by decide))⟩
  rw [keep_val a7 hk1 (by decide) (by simp) (fit _ nB), m6, vB5]

/-- A Newton step on `t5` (`m`) and `t6` (`x`): `m x ≡ 1 (mod 2^(2 j))` from
`m x ≡ 1 (mod 2^j)`. -/
theorem newton_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .t5).toNat : Int) * (t.gpr .t6).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .t5).toNat : Int) * (t'.gpr .t6).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
        t'.gpr .t5 = t.gpr .t5 ∧ t'.mem = t.mem) ∧ Keep [.t6, .a5, .t4] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold newton
  brun [r2_exec_li_two]
  exact VG.Proof.Bignum.newton_step hj h (newton_val _ _)

/-- `-x mod 2⁶⁴` is an inverse of `-a` modulo `2^32` when `x` is one of `a`. -/
theorem neg_inv32 {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 32 : Int) = 0) :
    (a * ((2 ^ 64 - x % 2 ^ 64) % 2 ^ 64) + 1) % 2 ^ 32 = 0 := by
  generalize hy : (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 = y
  have hxy : (x + y) % 2 ^ 32 = 0 := by omega
  have h1 : (2 ^ 32 : Int) ∣ (a : Int) * x - 1 := Int.dvd_of_emod_eq_zero h
  have h2 : (2 ^ 32 : Int) ∣ ((x + y : Nat) : Int) :=
    Int.dvd_of_emod_eq_zero (show ((x + y : Nat) : Int) % (2 ^ 32 : Int) = 0 by omega)
  have h3 : (2 ^ 32 : Int) ∣ ((a * y + 1 : Nat) : Int) := by
    have e : ((a * y + 1 : Nat) : Int) = (a : Int) * ((x + y : Nat) : Int) - ((a : Int) * x - 1) := by
      push_cast; grind
    rw [e]
    exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h2) h1
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp (by exact_mod_cast h3))

theorem initB_ok {t7 : State} {B : Addr} {Z w N n : Nat} (h7 : Ctx t7 B Z w N n) {m : Nat}
    (pv : val32 t7.mem B (arr w aMz) (n + 1) = vmod m) (hodd : m % 2 = 1) :
    WP isa initB t7 fun t9 => Ctx t9 B Z w N n ∧ Keys.Frame B w [aW] [] t7.mem t9.mem ∧
      (∃ iv, (vmod m * iv + 1) % 2 ^ 32 = 0 ∧ (t9.mem.readW (off B (arr w aW + 40)) 64).toNat = iv) ∧
      Keep kRegs t7 t9 := by
  have h := h7
  have hS : S w = 8 * (w + 2) := rfl
  have := h.ws.wle
  have := h.nw
  have hn1 := h.npos
  have := h.wbig
  have hnw' := h.ws.nowrap
  have room := h.room
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nW : aW < N := by unfold aW; omega
  have fM := fitZ _ nM
  have fW := fitZ _ nW
  have aW8 := arr_al w aW
  have := arr_al4 w aMz
  have hs := h.ws.scr
  have vodd : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have d0p : w32 t7.mem B (arr w aMz) % 2 ^ 32 = vmod m % 2 ^ 32 := by
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n :=
      rfl
    rw [pv] at e; omega
  have hd := (t7.mem.readW (off B (arr w aMz)) 32).isLt
  rw [initB, show ptr .a4 aMz ++ ([.load .w .t5 .a4 0, mov .t6 .t5] : List Instr) ++ newton ++ newton ++ newton ++
      newton ++ ([.li .a5 0, .sub .t1 .a5 .t6] : List Instr) ++ ptr .a4 aW ++ ([.store .d .t1 .a4 wIv] : List Instr) =
    (ptr .a4 aMz ++ ([.load .w .t5 .a4 0, mov .t6 .t5] : List Instr)) ++ (newton ++ (newton ++ (newton ++ (newton ++
      (([.li .a5 0, .sub .t1 .a5 .t6] : List Instr) ++ ptr .a4 aW ++ ([.store .d .t1 .a4 wIv] : List Instr)))))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.a4, .t5, .t6] (Q := fun u => u.gpr .t5 = (t7.mem.readW (off B (arr w aMz)) 32).setWidth 64 ∧
      u.gpr .t6 = (t7.mem.readW (off B (arr w aMz)) 32).setWidth 64 ∧ u.mem = t7.mem) ?_ (by rfl) (by rfl))
    fun u0 ⟨⟨u5, u6, um⟩, k0⟩ => ?_
  · brun [exec_li, List.append_assoc, runBlock_ptr B w, runBlock_ptr_nil B w, (show aMz < 2048 by decide),
      h.ws.s10, h.ws.s11, exec_load_w, mov, add_ofNat_zero', hs.ld (show arr w aMz + 4 ≤ Z by omega),
      Scr.al4 hs (show arr w aMz + 4 ≤ Z by omega) (by omega)]
  have e₀ : (((u0.gpr .t5).toNat : Int) * (u0.gpr .t6).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [u5, u6, toNat_ext32]
    have h1 := VG.Proof.Bignum.odd_sq _ (show (t7.mem.readW (off B (arr w aMz)) 32).toNat % 2 = 1 by simp only [w32] at d0p; omega)
    have h2 : (((t7.mem.readW (off B (arr w aMz)) 32).toNat : Int) * (t7.mem.readW (off B (arr w aMz)) 32).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((t7.mem.readW (off B (arr w aMz)) 32).toNat : Int) * (t7.mem.readW (off B (arr w aMz)) 32).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u0 (j := 3) (by decide) e₀) fun u1 ⟨⟨e₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u1 (j := 6) (by decide) e₁) fun u2 ⟨⟨e₂, b₂, m₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u2 (j := 12) (by decide) e₂) fun u3 ⟨⟨e₃, b₃, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_ok u3 (j := 24) (by decide) e₃) fun u4 ⟨⟨e₄, b₄, m₄⟩, k₄⟩ => ?_
  have k04 : Keep kRegs t7 u4 := ((((k0.trans k₁).trans k₂).trans k₃).trans k₄).mono (by decide)
  have h4 := h.of_keep k04
  have m04 : u4.mem = t7.mem := by rw [m₄, m₃, m₂, m₁, um]
  refine WP.mono (WP.keep [.a4, .a5, .t1] (Q := fun u => u.mem = u4.mem.writeW (off B (arr w aW + 40))
      (BitVec.ofNat 64 0 - u4.gpr .t6)) ?_ (by rfl) (by rfl)) fun t9 ⟨m9, k9⟩ => ?_
  · brun [exec_li, wIv, List.append_assoc, runBlock_ptr B w, (show aW < 2048 by decide), h4.ws.s10, h4.ws.s11,
      exec_store_d, fin64_exec_li_zero, h4.ws.scr.st (show arr w aW + 40 + 8 ≤ Z by omega),
      h4.ws.scr.al8 (show arr w aW + 40 + 8 ≤ Z by omega) (by omega)]
  have h9 := h4.of_keep (k9.mono (by decide))
  have o9 := writeW64_outside u4.mem B (d := arr w aW + 40) (BitVec.ofNat 64 0 - u4.gpr .t6) (by omega)
  have b5 : u4.gpr .t5 = (t7.mem.readW (off B (arr w aMz)) 32).setWidth 64 := by rw [b₄, b₃, b₂, b₁, u5]
  have e48 := VG.Proof.Bignum.emod_pow_weaken (show 32 ≤ 2 * 24 by decide) e₄
  rw [b5, toNat_ext32] at e48
  have F9 : Keys.Frame B w [aW] [] t7.mem t9.mem := by
    rw [m9, ← m04]; exact Keys.Frame.of_arr (o := aW) (d := 40) o9 (by omega) (by simp)
  refine ⟨h9, F9, ⟨(BitVec.ofNat 64 0 - u4.gpr .t6).toNat, ?_, by rw [m9, Mem.readW_writeW_self64]⟩,
    Keep.trans' k04 (k9.mono (by decide))⟩
  have nv := neg_inv32 e48
  have e2 : (BitVec.ofNat 64 0 - u4.gpr .t6).toNat = (2 ^ 64 - (u4.gpr .t6).toNat % 2 ^ 64) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e2, Nat.add_mod, Nat.mul_mod, ← d0p]
  simp only [w32] at nv ⊢
  rw [← Nat.mul_mod, ← Nat.add_mod]; exact nv

theorem initC_ok {t9 : State} {B : Addr} {Z w N n : Nat} (h9 : Ctx t9 B Z w N n) (hN : N ≤ 256)
    {x m iv : Nat} (hx : val32 t9.mem B (arr w aX) n = x) (hxn : x < 2 ^ (32 * n)) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) (pv9 : val32 t9.mem B (arr w aMz) (n + 1) = vmod m)
    (vB9 : val32 t9.mem B (arr w aB) (n + 1) = 1) (hivw : (t9.mem.readW (off B (arr w aW + 40)) 64).toNat = iv) :
    WP isa initC t9 fun t => Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1)) ∧
      StateAt t B w n (vmod m) iv (Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) 0) ∧
      Keys.Frame B w [aW, aF, aG, aA] [] t9.mem t.mem ∧ Keep initRegs t9 t := by
  have hS : S w = 8 * (w + 2) := rfl
  have h := h9
  have := h.ws.wle
  have := h.nw
  have hn1 := h.npos
  have := h.wbig
  have hnw' := h.ws.nowrap
  have hs := h.ws.scr
  have room := h.room
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nM : aMz < N := by unfold aMz; omega
  have nB : aB < N := by unfold aB; omega
  have nW : aW < N := by unfold aW; omega
  have nF : aF < N := by unfold aF; omega
  have nG : aG < N := by unfold aG; omega
  have nA : aA < N := by unfold aA; omega
  have nX : aX < N := by unfold aX; omega
  have nI : aMin < N := by unfold aMin; omega
  have fM := fitZ _ nM
  have fB := fitZ _ nB
  have fW := fitZ _ nW
  have fF := fitZ _ nF
  have fG := fitZ _ nG
  have fA := fitZ _ nA
  have fX := fitZ _ nX
  have fI := fitZ _ nI
  have := arr_al4 w aMz
  have := arr_al4 w aB
  have := arr_al4 w aF
  have := arr_al4 w aG
  have := arr_al4 w aA
  have := arr_al4 w aX
  have := arr_al4 w aMin
  have aW8 := arr_al w aW
  have aM8 := arr_al w aMz
  have hk1 : 4 * (n + 1) ≤ S w := by omega
  have vodd : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have vlt : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hmn
  simp only [initC, seqs]
  -- 6: `f = p`.
  rw [WP.seq_iff, WP.seq_iff]
  refine ptr2_ok h9.ws (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun x10 p0' p1'' kx mx => ?_
  refine WP.mono (cntN1_ok (h9.of_keep (kx.mono (by decide)))) fun x10' ⟨⟨q3'', xm⟩, kx'⟩ => ?_
  have k10a : Keep kRegs t9 x10' := (kx.trans kx').mono (by decide)
  have h10a := h9.of_keep k10a
  refine WP.mono (copyLoop_ok (dO := arr w aF) (dA := arr w aMz) h10a.ws.scr
    (by rw [kx'.gpr (by decide)]; exact p0') (by rw [kx'.gpr (by decide)]; exact p1'') q3''
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega)))
    fun t10 ⟨vF, out10, k10⟩ => ?_
  rw [xm, mx] at vF out10
  rw [pv9] at vF
  have h10 := h10a.of_keep (k10.mono (by decide))
  -- 7: `k = 1` for an even `x`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.t0, .a5] (Q := fun u => (u.gpr .a5).toNat =
      (if (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = 0 then 1 else 0) ∧ u.mem = t10.mem) ?_ (by rfl) (by rfl))
    fun t11 ⟨⟨r11k, m11⟩, k11⟩ => ?_
  · brun [exec_li, List.append_assoc, runBlock_ptr B w, (show aX < 2048 by decide), h10.ws.s10, h10.ws.s11,
      exec_load_w, h10.ws.scr.ld (show arr w aX + 4 ≤ Z by omega),
      Scr.al4 h10.ws.scr (show arr w aX + 4 ≤ Z by omega) (by omega)]
    exact even_bit _
  have h11' := h10.of_keep (k11.mono (by decide))
  -- The frame so far.
  have a10 : Keys.Frame B w [aF] [] t9.mem t10.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by omega) (by simp)
  have xX : val32 t11.mem B (arr w aX) n = x := by
    rw [m11, keep_val a10 (by omega) (by decide) (by simp) (fit _ nX), hx]
  have x0 : (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = x % 2 := by
    rw [← m11, ← xX]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk]; simp only [val32, w32]; omega
  have pM10 : val32 t10.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [keep_val a10 (k := n + 1) (by omega) (by decide) (by simp) (fit _ nM), pv9]
  have pM : val32 t11.mem B (arr w aMz) n = vmod m := by
    rw [m11]; exact val_low (by omega) pM10 vlt
  -- 8: `g = x + k p`, its carry the digit `n`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h11' (fun u hu => cntN_ok hu) (K := n) hn1 (by omega) nG nX nM hN
    (by rw [r11k]; split <;> decide)) fun t12 ⟨h12, K12, v12, c12, p12, _, out12, k12⟩ => ?_
  rw [xX, pM, r11k, x0] at v12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t12.mem.writeW (off B (arr w aG + 4 * n))
      ((t12.gpr .t4).setWidth 32)) ?_ (by rfl) (by rfl)) fun t13 ⟨m13, k13⟩ => ?_
  · brun [p12, exec_store_w, h12.ws.scr.st (show arr w aG + 4 * n + 4 ≤ Z by omega),
      Scr.al4 h12.ws.scr (show arr w aG + 4 * n + 4 ≤ Z by omega) (by omega)]
  have h13 := h12.of_keep (k13.mono (by decide))
  have vG : val32 t13.mem B (arr w aG) (n + 1) = oddInput (vmod m) x := by
    rw [m13, val32_write_top _ _ _ _ _ (by omega), BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt c12]
    unfold oddInput
    by_cases e : x % 2 = 0 <;> simp only [e, ↓reduceIte] at v12 ⊢ <;> omega
  -- 9: `a = 0`.
  rw [WP.seq_iff, WP.seq_iff]
  refine ptr_ok h13.ws (by decide) (by decide) (by decide) ?_
  refine WP.mono (cntN1_ok (h13.of_keep ((Keep.write _ .t0 _).mono (by decide)))) fun x14 ⟨⟨q3', xm'⟩, kx'⟩ => ?_
  (try rw [zeros]); rw [WP.seq_iff]
  refine WP.mono (WP.keep [.t5] (Q := fun u => u.gpr .t5 = 0 ∧ u.mem = x14.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun y14 ⟨⟨y0, ym'⟩, ky'⟩ => ?_
  have k14a : Keep kRegs t13 y14 := (((Keep.write _ .t0 _).trans kx').trans ky').mono (by decide)
  refine WP.mono (zeroLoop_ok (dO := arr w aA) (n := n + 1) (h13.of_keep k14a).ws.scr
    (by rw [ky'.gpr (by decide), kx'.gpr (by decide)]; simp [gpr_write])
    (by rw [ky'.gpr (by decide)]; exact q3') y0 (by omega) (by omega) (by omega) (by omega))
    fun t14 ⟨z14, out14, k14⟩ => ?_
  rw [ym', xm', mem_write] at out14
  have h14 := (h13.of_keep k14a).of_keep (k14.mono (by decide))
  -- 10: `d = 1` and `3 (n + 1)` batches.
  refine WP.mono (WP.keep [.t0, .t5, .s7] (Q := fun u => u.mem = t14.mem.writeW (off B (arr w aW))
      (BitVec.ofNat 64 1) ∧ u.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1))) ?_ (by rfl) (by rfl))
    fun t15 ⟨⟨m15, r15⟩, k15⟩ => ?_
  · brun [exec_li, wD, List.append_assoc, runBlock_ptr B w, (show aW < 2048 by decide), h14.ws.s10, h14.ws.s11,
      exec_store_d, h14.s8, h14.ws.scr.st (show arr w aW + 8 ≤ Z by omega),
      h14.ws.scr.al8 (show arr w aW + 8 ≤ Z by omega) (by omega)]
    first | (refine ⟨rfl, ?_⟩) | skip
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  -- The result.
  have a13 : Keys.Frame B w [aG] [] t12.mem t13.mem := by
    rw [m13]; exact Keys.Frame.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a14 : Keys.Frame B w [aA] [] t13.mem t14.mem :=
    Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using out14) (by omega) (by simp)
  have o15 := writeW64_outside t14.mem B (d := arr w aW) (BitVec.ofNat 64 1) (by omega)
  have a15 : Keys.Frame B w [aW] [] t14.mem t15.mem := by
    rw [m15]; exact Keys.Frame.of_arr (d := 0) (by simpa only [Nat.add_zero] using o15) (by omega) (by simp)
  have K15 : Keys.Frame B w [aG, aA, aW] [] t10.mem t15.mem :=
    (show Keys.Frame B w [aG, aA, aW] [] t10.mem t11.mem by rw [m11]; exact Keys.Frame.refl _ _ _ _ _).trans
      ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans ((a14.mono (by simp)).trans (a15.mono (by simp)))))
  have K5 : Keys.Frame B w [aW, aF, aG, aA] [] t9.mem t15.mem := (a10.mono (by simp)).trans (K15.mono (by simp))
  have m7' : ∀ {a b : State} {rs : List Reg}, Keep rs a b → (∀ r ∈ rs, r ∈ initRegs) →
      Keep initRegs a b := fun h hr => h.mono hr
  have k : Keep initRegs t9 t15 :=
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (m7' (k10a.trans k10) (by decide)) (m7' k11 (by decide)))
      (m7' (k12.trans k13) (by decide))) (m7' (k14a.trans k14) (by decide))) (m7' k15 (by decide))
  refine ⟨h14.of_keep7 (k15.mono (by decide)), r15, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    (a10.mono (by simp)).trans (K15.mono (by simp)), k⟩
  · show sv t15.mem B (arr w aF) n = (vmod m : Int)
    refine sv_of_val ?_ (by exact_mod_cast vlt)
    rw [keep_val K15 hk1 (by decide) (by simp) (fit _ nF), vF]
  · show sv t15.mem B (arr w aG) n = (oddInput (vmod m) x : Int)
    refine sv_of_eq (q := 0) ?_ ?_ ?_
    · rw [keep_val a15 hk1 (by decide) (by simp) (fit _ nG), keep_val a14 hk1 (by decide) (by simp) (fit _ nG), vG]
      simp
    · have : (0 : Int) ≤ 2 ^ (32 * n + 31) := by exact_mod_cast Nat.zero_le _
      have : (0 : Int) ≤ (oddInput (vmod m) x : Int) := Int.natCast_nonneg _
      omega
    · have h1 : oddInput (vmod m) x < 2 ^ (32 * n + 31) := by
        have : oddInput (vmod m) x ≤ vmod m + x := by unfold oddInput; split <;> omega
        have : 2 * 2 ^ (32 * n) ≤ 2 ^ (32 * n + 31) := by
          rw [show 32 * n + 31 = 32 * n + 1 + 30 by omega, Nat.pow_add, Nat.pow_succ]
          have := Nat.one_le_two_pow (n := 30)
          calc 2 * 2 ^ (32 * n) = 2 ^ (32 * n) * 2 * 1 := by omega
            _ ≤ 2 ^ (32 * n) * 2 * 2 ^ 30 := Nat.mul_le_mul_left _ this
        omega
      exact_mod_cast h1
  · show (val32 t15.mem B (arr w aA) (n + 1) : Int) = 0
    rw [keep_val a15 hk1 (by decide) (by simp) (fit _ nA), val32_zero z14]; rfl
  · show (val32 t15.mem B (arr w aB) (n + 1) : Int) = 1
    rw [keep_val K5 hk1 (by decide) (by simp) (fit _ nB), vB9]; rfl
  · show t15.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 1
    rw [show arr w aW + wD = arr w aW from rfl, m15, Mem.readW_writeW_self64]; rfl
  · show (t15.mem.readW (off B (arr w aW + wIv)) 64).toNat = iv
    have w40 : 40 + 64 / 8 ≤ S w := by omega
    rw [show arr w aW + wIv = arr w aW + 40 from rfl, m15, Outside.readW64 o15 (by omega) (by omega),
      keep_word a14 w40 (by decide) (by simp) (fit _ nW), keep_word a13 w40 (by decide) (by simp) (fit _ nW),
      keep_word K12 w40 (by decide) (by simp) (fit _ nW), m11, keep_word a10 w40 (by decide) (by simp) (fit _ nW)]
    exact hivw
  · rw [keep_val K15 hk1 (by decide) (by simp) (fit _ nM), pM10]

theorem init_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : val32 s.mem B (arr w aX) n = x) (hxn : x < 2 ^ (32 * n))
    (hm : val32 s.mem B (arr w aMin) n = m) (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa init s fun t => Ctx t B Z w N n ∧ t.gpr .s7 = BitVec.ofNat 64 (3 * (n + 1)) ∧
      (∃ iv, (vmod m * iv + 1) % 2 ^ 32 = 0 ∧
        StateAt t B w n (vmod m) iv (Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) 0)) ∧
      Keys.Frame B w [aMz, aB, aW, aF, aG, aA] [] s.mem t.mem ∧ Keep initRegs s t := by
  have room := h.room
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have hS : S w = 8 * (w + 2) := rfl
  have := h.nw
  have hk1 : 4 * (n + 1) ≤ S w := by omega
  have nX : aX < N := by unfold aX; omega
  have nM : aMz < N := by unfold aMz; omega
  have nB : aB < N := by unfold aB; omega
  rw [init, WP.seq_iff]
  refine WP.mono (initA_ok h hN hm) fun t7 ⟨h7, K7, pv, vB, k7⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (initB_ok h7 pv hodd) fun t9 ⟨h9, K9, ⟨iv, hiv, hivw⟩, k9⟩ => ?_
  have K79 : Keys.Frame B w [aMz, aB, aW] [] s.mem t9.mem := (K7.mono (by simp)).trans (K9.mono (by simp))
  refine WP.mono (initC_ok h9 hN (x := x) (by rw [keep_val K79 (by omega) (by decide) (by simp) (fit _ nX), hx])
    hxn hmn hodd (by rw [keep_val K9 hk1 (by decide) (by simp) (fit _ nM), pv])
    (by rw [keep_val K9 hk1 (by decide) (by simp) (fit _ nB), vB]) hivw) fun t ⟨ht, r7, st, K, kt⟩ => ?_
  exact ⟨ht, r7, ⟨iv, hiv, st⟩, (K79.mono (by simp)).trans (K.mono (by simp)),
    Keep.trans' (Keep.trans' (k7.mono (by decide)) (k9.mono (by decide))) kt⟩


end VG.Proof.Rsa.RISCV64.InvBatch

/-!
# The batched inverse on RISC-V

`inverse_ok`: from `x` in array 0 and an odd `m` in array 8, both below
`2^(32 n)` for `n` in `s8` (`1 ≤ n ≤ 2 w`), `inverse` leaves `gcd(x, m)` in
array 1 and, for `m > 1`, `y < m` with `y x ≡ gcd(x, m) (mod m)` in array 3,
`w` words each; it writes only arrays 1–7, 9 and 11–13 and the registers
`s7`, `t0`–`t6`, `a4`, `a5` and `a7`. `gcd_ok`: `gcd` leaves `gcd(x, m)` in
array 1 alone, writing fewer arrays.
-/

namespace VG.Proof.Rsa.RISCV64.InvBatch

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs)
open VG.Impl.Rsa.RISCV64.InvBatch
open VG.Proof.Rsa.Divstep (oddInput)

/-- The inputs of the inversion, as digits. -/
theorem inputs {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m)
    (hmn : m < 2 ^ (32 * n)) :
    val32 s.mem B (arr w aX) n = x ∧ val32 s.mem B (arr w aMin) n = m :=
  ⟨val_low h.nw (by rw [← num_eq]; exact hx) hxn, val_low h.nw (by rw [← num_eq]; exact hm) hmn⟩

theorem inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa inverse s fun t => Ws t B Z w N ∧ Keys.Frame B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.ws.wle
  have := h.nw
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have room := h.room
  obtain ⟨hx', hm'⟩ := inputs h hx hxn hm hmn
  have p1 : 1 < vmod m := by unfold vmod; split <;> omega
  have po : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have pA : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by have := h.npos; omega)
      omega
    · exact hmn
  have hk1 : 4 * (n + 1) ≤ S w := by simp only [S]; omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  simp only [inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN hx' hxn hm' hmn hodd) fun t0 ⟨h0, r0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 r0 st0 po p1 hiv pA hxn) fun t1 ⟨h1, _, st1, K1, k1⟩ => ?_
  generalize hst : Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) (3 * (n + 1)) = st at st1
  have ox : oddInput (vmod m) x ≤ vmod m + x := by
    unfold oddInput; generalize vmod m = P; split <;> omega
  obtain ⟨-, -, -, -, a0, a1, -, -⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := vmod m + x) po p1 hiv
    (by omega) ox (3 * (n + 1))
  rw [hst] at a0 a1
  have ea : val32 t1.mem B (arr w aA) (n + 1) = st.a.toNat := by have := st1.a; omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.p ea (by omega)) fun t2 ⟨h2, K2, v2, k2⟩ => ?_
  rw [st1.f] at v2
  rw [WP.seq_iff]
  refine WP.mono (doublings_ok h2 hN (by rw [keep_val K2 hk1 (by decide) (by simp) (fit _ nM)]; exact st1.p) v2
    (Divstep.normal_range _ (by omega) (by omega)) pA) fun t3 ⟨h3, _, v3, K3, k3⟩ => ?_
  have res := VG.Proof.Rsa.Divstep.invRun_result' (iv := iv) po p1 hiv pA hxn
  simp only at res
  rw [hst] at res
  obtain ⟨gf, gd, gl⟩ := res
  have hf3 : sv t3.mem B (arr w aF) n = st.f := by
    rw [keep_sv K3 hk1 (by decide) (by simp) (fit _ nF), keep_sv K2 hk1 (by decide) (by simp) (fit _ nF), st1.f]
  have gle : Nat.gcd (vmod m) x ≤ vmod m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have ce := VG.Proof.Rsa.Divstep.correction_eq' (p := vmod m) (st := st) (n := n) (a := st.a.toNat) (by omega) (by omega)
  have hfr : st.f.natAbs < 2 ^ (32 * n) := by rw [gf]; omega
  have hyr : Divstep.doubled (vmod m) (Divstep.normal (vmod m) st.a.toNat st.f) (6 * (n + 1)) < 2 ^ (32 * n) := by
    have := Divstep.doubled_lt (p := vmod m) (a := Divstep.normal (vmod m) st.a.toNat st.f) (k := 6 * (n + 1))
      (by omega)
    omega
  rw [finish, WP.seq_iff]
  refine WP.mono (finishG_ok h3 hN hf3 hfr) fun t4 ⟨h4, K4, g4, k4⟩ => ?_
  refine WP.mono (finishY_ok h4 hN (by rw [keep_val K4 hk1 (by decide) (by simp) (fit _ nA)]; exact v3) hyr)
    fun t5 ⟨h5, K5, y5, k5⟩ => ?_
  refine ⟨h5.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K3.mono (by decide)).trans ((K4.mono (by decide)).trans (K5.mono (by decide))))))),
    Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' k0 k1) (k2.mono (by decide))) k3)
      (k4.mono (by decide))) (k5.mono (by decide)), fun hm1 => ?_⟩
  have pm : vmod m = m := by unfold vmod; split <;> omega
  rw [pm] at gf gd gl ce
  have g5 : num t5.mem B w 1 = st.f.natAbs := by
    rw [show (1 : Nat) = aGcd from rfl, ← g4]; exact Keys.Frame.num K5 (by decide) (by simp) (fit _ (by unfold aGcd; omega))
  rw [show aY = 3 from rfl] at y5
  rw [g5, y5, pm, ce, gf]
  exact ⟨Nat.gcd_comm _ _, gd, gl⟩

theorem gcd_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ctx s B Z w N n) (hN : N ≤ 256) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa gcd s fun t => Ws t B Z w N ∧ Keys.Frame B w gcdArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m) := by
  have := h.ws.wle
  have := h.nw
  have room := h.room
  obtain ⟨hx', hm'⟩ := inputs h hx hxn hm hmn
  have p1 : 1 < vmod m := by unfold vmod; split <;> omega
  have po : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have pA : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by have := h.npos; omega)
      omega
    · exact hmn
  simp only [gcd, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN hx' hxn hm' hmn hodd) fun t0 ⟨h0, r0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loopG_ok hN h0 r0 st0.stG po p1 hiv pA hxn) fun t1 ⟨h1, _, st1, K1, k1⟩ => ?_
  have res := VG.Proof.Rsa.Divstep.invRun_result' (iv := iv) po p1 hiv pA hxn
  simp only at res
  obtain ⟨gf, -, -⟩ := res
  have gle : Nat.gcd (vmod m) x ≤ vmod m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  refine WP.mono (finishG_ok h1 hN st1.f (by rw [gf]; omega)) fun t2 ⟨h2, K2, g2, k2⟩ => ?_
  refine ⟨h2.ws, (K0.mono (by decide)).trans ((K1.mono (by decide)).trans (K2.mono (by decide))),
    Keep.trans' (Keep.trans' k0 k1) (k2.mono (by decide)), fun hm1 => ?_⟩
  have pm : vmod m = m := by unfold vmod; split <;> omega
  rw [show (1 : Nat) = aGcd from rfl, g2, gf, pm, Nat.gcd_comm]

end VG.Proof.Rsa.RISCV64.InvBatch
