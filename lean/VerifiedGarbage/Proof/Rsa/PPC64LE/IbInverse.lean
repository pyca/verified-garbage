module
-- separate module: it imports the reduction's Mathlib algebra, kept out of the callers' imports by `Instances`, its one importer

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbBatch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps

/-!
# The batched inverse on PPC64LE: the batches

`loop_ok`: `3 (n + 1)` batches from the start of the inversion, counted in
`r10`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S)
open VG.Proof.Rsa.Divstep (oddInput)

/-- After `k` batches. -/
def LoopAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (3 * (n + 1) - k) ∧ StateAt t B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) k) ∧
    KeyWorkspace.Keep B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

theorem loop_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n (3 * (n + 1)))
    (hst : StateAt s B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) 0))
    (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) :
    WP isa (.loop batch (.nonzero .d .r3)) s (LoopAt s B Z w N n p iv x (3 * (n + 1))) := by
  have hn := h.nw
  have hw := h.ws.wle
  have cap : p + x < 2 ^ (32 * n + 1) := by rw [Nat.pow_succ]; omega
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  refine count_loop (by omega) (LoopAt s B Z w N n p iv x) (fun k hk t ⟨Ht, It, Kt, kt⟩ => ?_)
    ⟨by simpa using h, hst, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, a0, a1, b0, b1⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x)
    odd large hinv (by omega) ox k
  rw [show 3 * (n + 1) - k = (3 * (n + 1) - k - 1) + 1 by omega] at Ht
  refine WP.mono (batch_ok Ht It hN (cap := p + x) (by push_cast at bd ⊢; omega) fo fb gb cap a0 a1 b0 b1 pc
    (by omega) hinv) fun u ⟨Hu, Iu, ru, Ku, ku⟩ => ?_
  rw [show 3 * (n + 1) - k - 1 = 3 * (n + 1) - (k + 1) by omega] at Hu
  exact ⟨⟨Hu, Iu, Kt.trans Ku, kt.trans' ku⟩, by rw [ru]; omega⟩

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: the end

`normalize_ok`: `a := (p - a) mod p` if `f < 0`; `doublings_ok`: `a 2^(6 (n + 1))
mod p`; `finish_ok`: `|f|` and `a` into arrays 1 and 3, `w` digits each.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs subBody selBody copyBody)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (subLoop_ok selLoop_ok copyLoop_ok zeroLoop_ok)

theorem sign31 (x : BitVec 32) : x.setWidth 64 >>> 31 = BitVec.ofNat 64 (if 2 ^ 31 ≤ x.toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ext32, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem shl2 (n : Nat) : BitVec.ofNat 64 n <<< 2 = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

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

/-- `signF`: the mask of `f < 0` into `r9`. -/
theorem signF_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block signF) t fun u => (u.mem = t.mem ∧
      u.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64
        (if decide (2 ^ 31 ≤ w32 t.mem B (arr w aF + 4 * n)) then 1 else 0)) ∧ Keep [.r0, .r6, .r8, .r9] t u := by
  have nF : aF < N := by have := h.room; unfold aF; omega
  have fF := h.ws.arr_fit nF
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  refine WP.keep _ ?_ (by decide)
  prun [signF, ptr, cntN, exec_li (imm := aF) (by decide),
    exec_addi (n := .r6) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h.ptr aF, h.cnt,
    shl2 n, h.ws.scr.ld (show arr w aF + 4 * n + 4 ≤ Z by omega), sign31]
  simp only [decide_eq_true_eq]

/-- `[o] := mask ? [b] : [a]` for the mask in `r9` of `f < 0`, the pointers
and the count of `n + 1` set after `signF`. -/
theorem signSel_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a b : Nat}
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (signSel o a b) s
      fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
        val32 t.mem B (arr w o) (n + 1) = (if sv s.mem B (arr w aF) n < 0 then val32 s.mem B (arr w b) (n + 1)
          else val32 s.mem B (arr w a) (n + 1)) ∧ Outside B (arr w o) (4 * (n + 1)) s.mem t.mem ∧
        Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  rw [signSel, WP.seq_iff, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (signF_ok h) fun t1 ⟨⟨m1, r9⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [← List.append_assoc, ← List.append_assoc]
  refine ptr3_ok h1.ws (by omega) (by omega) (by omega) fun t2 p5 p6 p7 k2 m2 => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (cntN1_ok h2) fun t3 ⟨⟨p8, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have q9 : t3.gpr .r9 = t1.gpr .r9 := (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  refine WP.mono (selLoop_ok (b := decide (2 ^ 31 ≤ w32 s.mem B (arr w aF + 4 * n))) h3.ws.scr
    (by rw [k3.gpr _ (by decide)]; exact p5) (by rw [k3.gpr _ (by decide)]; exact p6)
    (by rw [k3.gpr _ (by decide)]; exact p7) p8 (by rw [q9, r9]) (by omega) (by omega) (by omega) (by omega)
    (by have := h.ws.arr_fit hb; omega) (ahead_any w o a (n + 1) (by omega)) (ahead_k hob (by omega)))
    fun t4 ⟨v4, out4, k4⟩ => ?_
  have k : Keep kRegs s t4 := (((k1.mono (by decide)).trans' (k2.mono (by decide))).trans'
    (k3.mono (by decide))).trans' (k4.mono (by decide))
  rw [m3, m2, m1] at v4 out4
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega)
    (by simp), ?_, out4, k⟩
  rw [v4]
  simp only [sv_neg, decide_eq_true_eq]

/-- `normalize`: `[a] = normal p a f`, for `a < p`. -/
theorem normalize_ok {s : State} {B : Addr} {Z w N n c p a : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p) :
    WP isa normalize s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aT3, aT1] [] s.mem t.mem ∧
      val32 t.mem B (arr w aA) (n + 1) = Divstep.normal p a (sv s.mem B (arr w aF) n) ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
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
  rw [normalize]; simp only [seqs]; rw [WP.seq_iff]
  -- `[aT3] = p - a`.
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (subLoop_ok h1.ws.scr p5 p6 p7 p8 (by rw [p9]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t2 ⟨b2, v2, out2, k2⟩ => ?_
  rw [m1, p9, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, hp, ha] at v2
  rw [m1] at out2
  have K2 : KeyWorkspace.Keep B w [aT3] [] s.mem t2.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega) (by simp)
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
    ((k1.mono (by decide)).trans' (k2.mono (by decide))).trans' (k3.trans' k4)⟩
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
theorem double_ok {s : State} {B : Addr} {Z w N n c p a : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p)
    (hpA : p < 2 ^ (32 * n)) :
    WP isa double s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aA, aT3, aT1] [] s.mem t.mem ∧
      val32 t.mem B (arr w aA) (n + 1) = (2 * a) % p ∧ Keep kRegs s t := by
  have room := h.room
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have n3 : aT3 < N := by unfold aT3; omega
  have nM : aMz < N := by unfold aMz; omega
  have nA : aA < N := by unfold aA; omega
  have n1 : aT1 < N := by unfold aT1; omega
  rw [double]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = 1#64 ∧ u.mem = s.mem) (by prun) (by decide))
    fun t1 ⟨⟨r11, m1⟩, k1⟩ => ?_
  have h1 := h.of_keep (k1.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h1 (fun u hu => cntN1_ok hu) (K := n + 1) (by omega) (by omega) n3 nA nA hN
    (by rw [r11]; decide)) fun t2 ⟨h2, K2, v2, c2, _, _, _, k2⟩ => ?_
  rw [m1, ha, r11, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul] at v2
  have hR : 2 * a < 2 ^ (32 * (n + 1)) := by
    have : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by rw [← Nat.pow_add]; congr 1; omega
    omega
  have v2' : val32 t2.mem B (arr w aT3) (n + 1) = 2 * a := by
    have := val32_lt t2.mem B (arr w aT3) (n + 1)
    generalize 2 ^ (32 * (n + 1)) = R at hR this v2
    rcases Nat.eq_zero_or_pos (t2.gpr .r9).toNat with e | e
    · rw [e] at v2; omega
    · have : R ≤ R * (t2.gpr .r9).toNat := Nat.le_mul_of_pos_right _ e
      omega
  rw [m1] at K2
  refine WP.mono (csub_ok (p := p) h2 nA n3 n1 nM hN (by decide) (by decide) (by decide)
    (by rw [keep_val K2 (by omega) (by decide) (by simp) (fit _ nM), hp]) v2') fun t3 ⟨h3, K3, v3, k3⟩ => ?_
  refine ⟨h3, (K2.mono (by simp)).trans (K3.mono (by simp)), ?_,
    ((k1.mono (by decide)).trans' k2).trans' k3⟩
  rw [v3]
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- After `k` doublings. -/
def DoubleAt (s₀ : State) (B : Addr) (Z w N n p a₀ : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (6 * (n + 1) - k) ∧ val32 t.mem B (arr w aA) (n + 1) = Divstep.doubled p a₀ k ∧
    KeyWorkspace.Keep B w [aA, aT3, aT1] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

/-- `doublings`: `[a] = a 2^(6 (n + 1)) mod p`. -/
theorem doublings_ok {s : State} {B : Addr} {Z w N n p a : Nat} (h : Ctx s B Z w N n 0) (hN : N ≤ 256)
    (hp : val32 s.mem B (arr w aMz) (n + 1) = p) (ha : val32 s.mem B (arr w aA) (n + 1) = a) (hap : a < p)
    (hpA : p < 2 ^ (32 * n)) :
    WP isa doublings s (DoubleAt s B Z w N n p a (6 * (n + 1))) := by
  have room := h.room
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have nM : aMz < N := by unfold aMz; omega
  rw [doublings, WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r10] (Q := fun u => u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (6 * (n + 1))) ∧
    u.mem = s.mem) ?_ (by decide)) fun t0 ⟨⟨r10, m0⟩, k0⟩ => ?_
  · have e := h.r10
    simp only [Nat.mul_zero, Nat.add_zero] at e
    prun [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have h0 : Ctx t0 B Z w N n (6 * (n + 1)) :=
    ⟨h.ws.of_keep k0, r10, h.npos, h.nw, h.room, by omega, h.wbig⟩
  refine count_loop (by omega) (DoubleAt s B Z w N n p a) (fun k hk t ⟨Ht, vt, Kt, kt⟩ => ?_)
    ⟨by simpa using h0, by rw [m0, ha, Divstep.doubled_zero hap], by rw [m0]; exact KeyWorkspace.Keep.refl _ _ _ _ _,
      k0.mono (by decide)⟩
  have pt : val32 t.mem B (arr w aMz) (n + 1) = p := by
    rw [keep_val Kt (by omega) (by decide) (by simp) (fit _ nM), hp]
  rw [WP.seq_iff]
  refine WP.mono (double_ok Ht hN pt vt (Divstep.doubled_lt (by omega)) hpA) fun u ⟨Hu, Ku, vu, ku⟩ => ?_
  rw [show 6 * (n + 1) - k = (6 * (n + 1) - k - 1) + 1 by omega] at Hu
  refine WP.mono (WP.keep [.r3, .r10] (Q := fun y => y.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (6 * (n + 1) - k - 1)) ∧
      (y.gpr .r3).toNat = 6 * (n + 1) - k - 1 ∧ y.mem = u.mem) ?_ (by decide)) fun y ⟨⟨y10, y3, ym⟩, ky⟩ => ?_
  · have e := dec_eq (c := 6 * (n + 1) - k - 1) Hu.nlt (by omega)
    prun [Hu.r10]
    rw [e.1]
    exact ⟨rfl, e.2⟩
  refine ⟨⟨⟨Hu.ws.of_keep ky, by rw [y10]; congr 2, h.npos, h.nw, h.room, by omega, h.wbig⟩,
    by rw [ym, vu, Divstep.doubled_next], Kt.trans (by rw [ym]; exact Ku),
    kt.trans' ((ku.mono (by decide)).trans' (ky.mono (by decide)))⟩, by rw [y3]; omega⟩

/-! ## The end -/

theorem val32_zero {m : Mem} {B : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ i < k, w32 m B (d + 4 * i) = 0) → val32 m B d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zero (fun i hi => h i (by omega)), h k (by omega), Nat.mul_zero]

/-- `zeroW j`: `[j]`'s `w + 1` digits zeroed. -/
theorem zeroW_ok {s : State} {B : Addr} {Z w N n c j : Nat} (h : Ctx s B Z w N n c) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (4 * (w + 1)) s.mem t.mem ∧ (∀ i < w + 1, w32 t.mem B (arr w j + 4 * i) = 0) ∧
      Keep kRegs s t := by
  have fj := h.ws.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have := h.ws.wle
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h.ws (by decide) (by decide) (by decide) (by omega) ?_
  refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.ofNat 64 (w + 1) ∧
    u.gpr .r5 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u0, u8, u5, um⟩, ku⟩ => ?_
  · prun [h.ws.r29, ofNat_succ]
    rfl
  have k1 : Keep kRegs s u := ((Keep.write _ .r5 _).trans ku).mono (by decide)
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok (h.of_keep k1).ws.scr u5 u8 u0 (by omega) (by omega)
    (by omega)) fun t ⟨z, out, kt⟩ => ?_
  rw [um] at out
  exact ⟨h.of_keep (k1.trans' (kt.mono (by decide))), KeyWorkspace.Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega) (by simp), out, z, k1.trans' (kt.mono (by decide))⟩

/-- `k ≤ w + 1` digits holding `v < 2^(32 w)`, the digits after them zero to
digit `w`: the `w` digits are `v`. -/
theorem num_tail {m : Mem} {B : Addr} {d w k v : Nat} (hk : k ≤ w + 1) (hv : val32 m B d k = v)
    (hz : ∀ i, k ≤ i → i < w + 1 → w32 m B (d + 4 * i) = 0) (hvw : v < 2 ^ (32 * w)) : val32 m B d w = v := by
  have e1 := val32_append m B d k (w + 1 - k)
  have z : val32 m B (d + 4 * k) (w + 1 - k) = 0 := val32_zero (fun i hi => by
    rw [show d + 4 * k + 4 * i = d + 4 * (k + i) by omega]; exact hz _ (by omega) (by omega))
  rw [show k + (w + 1 - k) = w + 1 by omega, hv, z, Nat.mul_zero, Nat.add_zero, val32_succ] at e1
  have := val32_lt m B d w
  rcases Nat.eq_zero_or_pos (w32 m B (d + 4 * w)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero] at e1; exact e1
  · have : 2 ^ (32 * w) ≤ 2 ^ (32 * w) * w32 m B (d + 4 * w) := Nat.le_mul_of_pos_right _ e
    omega

/-- `finish`: `[1] = |f|` and `[3] = y`, `w` digits each. -/
theorem finish_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256) {f : Int} {y : Nat}
    (hf : sv s.mem B (arr w aF) n = f) (hfr : f.natAbs < 2 ^ (32 * n))
    (hy : val32 s.mem B (arr w aA) (n + 1) = y) (hyr : y < 2 ^ (32 * n)) :
    WP isa finish s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [aGcd, aT1, aY] [] s.mem t.mem ∧
      num t.mem B w aGcd = f.natAbs ∧ num t.mem B w aY = y ∧ Keep kRegs s t := by
  have room := h.room
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.ws.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.ws.arr_fit hj
  have nG : aGcd < N := by unfold aGcd; omega
  have nY : aY < N := by unfold aY; omega
  have nA : aA < N := by unfold aA; omega
  have nF : aF < N := by unfold aF; omega
  have n1 : aT1 < N := by unfold aT1; omega
  have fG := fitZ _ nG
  have fF := fitZ _ nF
  have f1 := fitZ _ n1
  have fY := fitZ _ nY
  have fA := fitZ _ nA
  have hnw : 2 ^ (32 * n) ≤ 2 ^ (32 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk1 : n + 1 ≤ w + 2 := by omega
  have hk0 : n ≤ w + 2 := by omega
  rw [finish]; simp only [seqs]; rw [WP.seq_iff]
  -- `[1] = 0`.
  refine WP.mono (zeroW_ok h nG hN) fun t1 ⟨h1, K1, out1, z1, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (setup_ok h1 (fun t ht => cntN1_ok ht) (by decide) (by decide) (by decide))
    fun t2 ⟨h2, m2, p5, p6, p7, p8, p9, k2⟩ => ?_
  rw [WP.seq_iff]
  -- `[aT1] = -f`.
  refine WP.mono (subLoop_ok h2.ws.scr p5 p6 p7 p8 (by rw [p9]; decide) (by omega) (by omega) (by omega)
    (by omega) (by omega) (ahead_k (by decide) (by omega)) (ahead_k (by decide) (by omega)))
    fun t3 ⟨b3, v3, out3, k3⟩ => ?_
  have h3 := h2.of_keep (k3.mono (by decide))
  have zG : val32 t1.mem B (arr w aGcd) (n + 1) = 0 := val32_zero (fun i hi => z1 i (by omega))
  rw [m2, p9, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, zG,
    keep_val K1 hk1 (by decide) (by simp) (fit _ nF)] at v3
  rw [m2] at out3
  have K3 : KeyWorkspace.Keep B w [aT1] [] t1.mem t3.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out3) (by omega) (by simp)
  have hnw' := h.ws.nowrap
  rw [WP.seq_iff]
  refine WP.mono (signSel_ok h3 nG nF n1 hN (by decide)) fun t4 ⟨h4, K4, v4, out4, k4⟩ => ?_
  have sF : sv t3.mem B (arr w aF) n = f := by
    rw [keep_sv K3 hk1 (by decide) (by simp) (fit _ nF), keep_sv K1 hk1 (by decide) (by simp) (fit _ nF), hf]
  have vF : val32 t3.mem B (arr w aF) (n + 1) = val32 s.mem B (arr w aF) (n + 1) := by
    rw [out3.val32 (by have := arr_disj (w := w) (show aF ≠ aT1 by decide); omega) (by omega),
      keep_val K1 hk1 (by decide) (by simp) (fit _ nF)]
  have vT : val32 t3.mem B (arr w aT1) (n + 1) = val32 t3.mem B (arr w aT1) (n + 1) := rfl
  rw [sF, vF] at v4
  -- `[1] = |f|`.
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
  have numG : num t4.mem B w aGcd = f.natAbs := by
    refine num_tail (k := n + 1) (by omega) gcd1 (fun i hi1 hi2 => ?_) (by omega)
    rw [out4.w32 (by omega) (by omega), out3.w32 (by have := arr_disj (w := w) (show aGcd ≠ aT1 by decide); omega)
      (by omega)]
    exact z1 i hi2
  -- `[3] = y`.
  rw [WP.seq_iff]
  refine WP.mono (zeroW_ok h4 nY hN) fun t5 ⟨h5, K5, out5, z5, k5⟩ => ?_
  rw [WP.seq_iff]
  have hb6 : WP isa (.block (ptr .r5 aY ++ ptr .r6 aA ++ cntN1)) t5 fun u => Ctx u B Z w N n c ∧ u.mem = t5.mem ∧
      u.gpr .r5 = off B (arr w aY) ∧ u.gpr .r6 = off B (arr w aA) ∧ u.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧
      Keep kRegs t5 u := by
    rw [List.append_assoc]
    refine ptr_ok h5.ws (by decide) (by decide) (by decide) (by decide) ?_
    refine ptr_ok (h5.ws.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
    refine WP.mono (cntN1_ok (h5.of_keep (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).mono (by decide))))
      fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
    have k0 : Keep kRegs t5 x := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans kx).mono (by decide)
    refine ⟨h5.of_keep k0, xm, ?_, ?_, x8, k0⟩
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte]
  refine WP.mono hb6 fun t6 ⟨h6, m6, q5, q6, q8, k6⟩ => ?_
  refine WP.mono (copyLoop_ok h6.ws.scr q5 q6 q8 (by omega) (by omega) (by omega) (by omega)
    (ahead_k (by decide) (by omega))) fun t7 ⟨v7, out7, k7⟩ => ?_
  rw [m6] at v7 out7
  have K47 : KeyWorkspace.Keep B w [aY] [] t4.mem t7.mem := K5.trans
    (KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out7) (by omega) (by simp))
  have yA : val32 t5.mem B (arr w aA) (n + 1) = y := by
    rw [keep_val K5 hk1 (by decide) (by simp) (fit _ nA), keep_val K4 hk1 (by decide) (by simp)
      (fit _ nA), keep_val K3 hk1 (by decide) (by simp) (fit _ nA), keep_val K1 hk1 (by decide)
        (by simp) (fit _ nA), hy]
  have k : Keep kRegs s t7 := ((((((k1.trans' (k2.mono (by decide))).trans' (k3.mono (by decide))).trans' k4).trans'
    k5).trans' k6).trans' (k7.mono (by decide)))
  refine ⟨h.of_keep k, ?_, ?_, ?_, k⟩
  · exact (K1.mono (by simp)).trans ((K3.mono (by simp)).trans ((K4.mono (by simp)).trans (K47.mono (by simp))))
  · rw [show num t7.mem B w aGcd = num t4.mem B w aGcd from keep_val K47 (k := w) (by omega) (by decide) (by simp)
      (fit _ nG), numG]
  · refine num_tail (k := n + 1) (by omega) (by rw [v7, yA]) (fun i hi1 hi2 => ?_) (by omega)
    rw [out7.w32 (by omega) (by omega)]
    exact z5 i hi2

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: the start

`init_ok`: from `x` in array 0 and the odd `m` in array 8, both below
`2^(32 n)`, the start of the inversion modulo `p = vmod m` (`m`, or 3 for
`m = 1`): `f = p`, `g = oddInput p x`, `a = 0`, `b = 1`, `d = 1`, with
`-p⁻¹ mod 2^32` in the window and `3 (n + 1)` batches to run.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop seqs subBody selBody copyBody eqBody)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (copyLoop_ok zeroLoop_ok eqLoop_ok)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The modulus of the batches: `m`, or 3 for `m = 1`. -/
def vmod (m : Nat) : Nat := if m = 1 then 3 else m

/-- `k` digits of a number below `2^(32 k)` stored in `w ≥ k` digits. -/
theorem val_low {m : Mem} {B : Addr} {d w k v : Nat} (hk : k ≤ w) (hv : val32 m B d w = v)
    (hvk : v < 2 ^ (32 * k)) : val32 m B d k = v := by
  have e := val32_append m B d k (w - k)
  rw [show k + (w - k) = w by omega, hv] at e
  have := val32_lt m B d k
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (w - k)) with z | z
  · rw [z, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have : 2 ^ (32 * k) ≤ 2 ^ (32 * k) * val32 m B (d + 4 * k) (w - k) := Nat.le_mul_of_pos_right _ z
    omega

/-- `init`, its first part: `[2] = m` with a zero digit `n`, `r10 = n`. -/
theorem init1_ok {s : State} {B : Addr} {Z w N n m : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w)
    (hm : val32 s.mem B (arr w aMin) n = m) :
    WP isa (.seq (.block (ptr .r5 aMz ++ ptr .r6 aMin ++ ([.addi .r10 .r11 0] : List Instr) ++ cntN)) (countLoop .r8 copyBody)) s
      fun t => Ctx t B Z w N n 0 ∧ KeyWorkspace.Keep B w [aMz] [] s.mem t.mem ∧
        val32 t.mem B (arr w aMz) n = m ∧ t.gpr .r11 = s.gpr .r11 ∧
        Outside B (arr w aMz) (4 * n) s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have fM := h.arr_fit (j := aMz) (by unfold aMz; omega)
  have fI := h.arr_fit (j := aMin) (by unfold aMin; omega)
  rw [WP.seq_iff, List.append_assoc, List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (WP.keep [.r8, .r10] (Q := fun u => u.gpr .r10 = BitVec.ofNat 64 n ∧ u.gpr .r8 = BitVec.ofNat 64 n ∧
    u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u10, u8, um⟩, ku⟩ => ?_
  · have e := cnt_eq (n := n) (c := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at e
    prun [cntN, h11, BitVec.add_zero, e]
  have k1 : Keep (.r10 :: kRegs) s u := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans ku).mono (by decide)
  have h1 : Ctx u B Z w N n 0 := ⟨h.of_keep k1, by rw [u10]; simp, hn1, hnw, hN15, by decide, hw⟩
  refine WP.mono (copyLoop_ok (dO := arr w aMz) (dA := arr w aMin) h1.ws.scr
    (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) (by rw [ku.gpr _ (by decide)]; simp [gpr_write]) u8 hn1
    (by omega) (by omega) (by omega) (ahead_k (by decide) (by omega))) fun t ⟨v, out, kt⟩ => ?_
  rw [um] at v out
  have k : Keep (.r10 :: kRegs) s t := k1.trans' (kt.mono (by decide))
  refine ⟨h1.of_keep (kt.mono (by decide)), KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out)
    (by omega) (by simp), by rw [v, hm],
    (((((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans ku).trans kt).gpr _ (by decide)), out, k⟩

/-- `setTop aMz 0`: digit `n` of `[2]` := 0. -/
theorem setTop_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (hN : N ≤ 256) :
    WP isa (.block (setTop aMz 0)) s fun t => (t.mem = s.mem.writeW (off B (arr w aMz + 4 * n)) (0 : BitVec 32) ∧
      t.gpr .r0 = 0) ∧ Keep [.r0, .r6, .r8] s t := by
  have fj := h.ws.arr_fit (j := aMz) (by have := h.room; unfold aMz; omega)
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  refine WP.keep _ ?_ (by decide)
  prun [setTop, ptr, cntN, exec_li (imm := aMz) (by decide),
    exec_addi (n := .r6) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h.ptr aMz, h.cnt, shl2,
    h.ws.scr.st (show arr w aMz + 4 * n + 4 ≤ Z by omega)]
  exact ⟨rfl, rfl⟩

/-- The virtualization's mask: 2 where `r9` is zero. -/
theorem virt_mask (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    (((0#64 - r) >>> 63 ^^^ 1#64) <<< 1) = if r = 0#64 then 2#64 else 0#64 := by
  split
  · next e => subst e; decide
  · next e =>
    have : r.toNat ≠ 0 := fun h => e (BitVec.eq_of_toNat_eq h)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h1 : (2 ^ 64 - r.toNat + (0#64).toNat) % 2 ^ 64 / 2 ^ 63 = 1 := by
      rw [show (0#64).toNat = 0 from rfl]; omega
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
    (((x.setWidth 64 <<< 63) >>> 63) ^^^ BitVec.ofNat 64 1).toNat = (if x.toNat % 2 = 0 then 1 else 0) := by
  rw [low_bit, BitVec.toNat_xor, BitVec.toNat_and, toNat_ext32, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with e | e <;> rw [e] <;> rfl

/-- `init`: the start of the inversion modulo `vmod m`. -/
theorem init_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) {x m : Nat}
    (hx : val32 s.mem B (arr w aX) n = x) (hxn : x < 2 ^ (32 * n))
    (hm : val32 s.mem B (arr w aMin) n = m) (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa init s fun t => Ctx t B Z w N n (3 * (n + 1)) ∧
      (∃ iv, (vmod m * iv + 1) % 2 ^ 32 = 0 ∧
        StateAt t B w n (vmod m) iv (Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) 0)) ∧
      KeyWorkspace.Keep B w [aMz, aB, aW, aF, aG, aA] [] s.mem t.mem ∧ Keep (.r10 :: kRegs) s t := by
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  have hnw' := h.nowrap
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have fitZ : ∀ j < N, arr w j + S w ≤ Z := fun j hj => h.arr_fit hj
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
  have hk1 : n + 1 ≤ w + 2 := by omega
  simp only [init, seqs]
  -- 1: `[2] = m`.
  rw [WP.seq_iff]
  refine WP.mono (init1_ok h hN15 hN hw h11 hn1 hnw hm) fun t1 ⟨h1, K1, v1, r11a, out1, k1⟩ => ?_
  -- 2: its digit `n` zero, `[b] = 0`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setTop_ok h1 hN) fun t2 ⟨⟨m2, r0⟩, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine ptr_ok h2.ws (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (cntN1_ok (h2.of_keep ((Keep.write _ .r5 _).mono (by decide)))) fun t3 ⟨⟨p8, m3⟩, k3⟩ => ?_
  have h3 := (h2.of_keep ((Keep.write _ .r5 _).mono (by decide))).of_keep (k3.mono (by decide))
  refine WP.mono (zeroLoop_ok h3.ws.scr (dO := arr w aB) (by rw [k3.gpr _ (by decide)]; simp [gpr_write]) p8
    (by rw [k3.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact r0) (by omega) (by omega)
    (by omega)) fun t4 ⟨z4, out4, k4⟩ => ?_
  have h4 := h3.of_keep (k4.mono (by decide))
  rw [mem_write] at m3
  rw [m3] at out4
  have vM4 : val32 t4.mem B (arr w aMz) (n + 1) = m := by
    rw [out4.val32 (by have := arr_disj (w := w) (show aMz ≠ aB by decide); omega) (by omega), m2,
      val_top0 (by omega), v1]
  have zB : ∀ i < n + 1, w32 t4.mem B (arr w aB + 4 * i) = 0 := z4
  -- 3: `[b] = 1`, and whether `m = 1`.
  rw [WP.seq_iff, WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r5, .r6, .r7, .r8, .r9] (Q := fun u =>
      u.mem = t4.mem.writeW (off B (arr w aB)) ((BitVec.ofNat 64 1).setWidth 32) ∧
      u.gpr .r6 = off B (arr w aMz) ∧ u.gpr .r7 = off B (arr w aB) ∧ u.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧
      u.gpr .r9 = 0) ?_ (by decide)) fun t5 ⟨⟨m5, p6, p7, q8, p9⟩, k5⟩ => ?_
  · prun [ptr, cntN1, cntN, exec_li (imm := aB) (by decide), exec_li (imm := aMz) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r6) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      exec_addi (n := .r7) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h4.ptr aB, h4.ptr aMz,
      h4.cnt, ofNat_succ, h4.ws.scr.st (show arr w aB + 4 ≤ Z by omega)]
    rfl
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
  refine WP.mono (eqLoop_ok h5.ws.scr p6 p7 q8 p9 (by omega) (by omega) (by omega) (by omega))
    fun t6 ⟨e6, l6, m6, k6⟩ => ?_
  have h6 := h5.of_keep (k6.mono (by decide))
  rw [vM5, vB5] at e6
  -- 4: `p = vmod m` in `[2]`.
  rw [WP.seq_iff]
  have d0 := (t6.mem.readW (off B (arr w aMz)) 32).isLt
  refine WP.mono (WP.keep [.r0, .r3, .r5] (Q := fun u =>
      u.mem = t6.mem.writeW (off B (arr w aMz)) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32)) ?_ (by decide)) fun t7 ⟨m7, k7⟩ => ?_
  · prun [ptr, exec_li (imm := aMz) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, h6.ptr aMz,
      h6.ws.scr.ld (show arr w aMz + 4 ≤ Z by omega), h6.ws.scr.st (show arr w aMz + 4 ≤ Z by omega)]
    rw [← virt_mask _ l6]
  have h7 := h6.of_keep (k7.mono (by decide))
  have pv : val32 t7.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [m6] at m7
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n := rfl
    have em : val32 t5.mem B (arr w aMz) (n + 1) = w32 t5.mem B (arr w aMz) + 2 ^ 32 * val32 t5.mem B (arr w aMz + 4) n :=
      rfl
    rw [vM5] at em
    have o7 := writeW32_outside t5.mem B (d := arr w aMz) (((t5.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
        (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [e, m7, w32_write_self, o7.val32 (by omega) (by omega)]
    have vd := virt_digit (t5.mem.readW (off B (arr w aMz)) 32) (decide (t6.gpr .r9 = 0#64))
    simp only [decide_eq_true_eq] at vd
    rw [vd]
    unfold vmod
    by_cases e1 : m = 1
    · have z : t6.gpr .r9 = 0#64 := e6.mpr (by rw [e1])
      have : w32 t5.mem B (arr w aMz) = 1 ∧ val32 t5.mem B (arr w aMz + 4) n = 0 := by
        simp only [w32] at em ⊢; omega
      simp only [z, true_and, ↓reduceIte, e1]
      rw [show (t5.mem.readW (off B (arr w aMz)) 32).toNat = 1 from this.1, this.2]
      rfl
    · have z : ¬ t6.gpr .r9 = 0#64 := fun x => e1 (by have := e6.mp x; omega)
      simp only [z, false_and, ↓reduceIte, e1]
      simp only [w32] at em
      omega
  have vodd : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have vlt : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hmn
  have d0p : w32 t7.mem B (arr w aMz) % 2 ^ 32 = vmod m % 2 ^ 32 := by
    have e : val32 t7.mem B (arr w aMz) (n + 1) = w32 t7.mem B (arr w aMz) + 2 ^ 32 * val32 t7.mem B (arr w aMz + 4) n :=
      rfl
    rw [pv] at e; omega
  -- 5: `-p⁻¹ mod 2^32` into `r12`.
  rw [WP.seq_iff]
  rw [← List.append_nil (ptr .r10 aMz ++ _), List.append_assoc]
  refine ptr_ok h7.ws (by decide) (by decide) (by decide) (by decide) ?_
  rw [List.append_nil]
  have wodd : (word (t7.write .r10 (off B (arr w aMz))).mem B (arr w aMz)).toNat % 2 = 1 := by
    rw [mem_write, word_eq_w32]; omega
  refine WP.mono (Pub.minv_ok (h7.ws.scr.congr rfl) (by simp [gpr_write]) (by omega) wodd)
    fun t8 ⟨⟨i8, inv8, m8⟩, k8⟩ => ?_
  rw [mem_write] at m8 inv8
  have hiv : (vmod m * (t8.gpr .r12).toNat + 1) % 2 ^ 32 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod, ← d0p, ← Nat.mul_mod, ← Nat.add_mod]; exact inv8
  have r11b : t8.gpr .r11 = BitVec.ofNat 64 n := by
    rw [k8.gpr _ (by decide)]
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [k7.gpr _ (by decide), k6.gpr _ (by decide), k5.gpr _ (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]
    simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    rw [k2.gpr _ (by decide), r11a, h11]
  have kk8 : Keep (.r10 :: kRegs) t7 t8 := ((Keep.write _ .r10 _).trans k8).mono (by decide)
  have w8 : Ws t8 B Z w N := h7.ws.of_keep kk8
  have pw : ∀ j, BitVec.ofNat 64 j * t8.gpr .r30 + t8.gpr .r31 + BitVec.ofNat 64 KeyWorkspace.hdr = off B (arr w j) :=
    fun j => by rw [w8.r30, w8.r31]; exact ptr_val _ _ _
  -- 6: the inverse to the window, `r10 = n`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r5, .r10] (Q := fun u => u.mem = t8.mem.writeW (off B (arr w aW + 40)) (t8.gpr .r12) ∧
      u.gpr .r10 = BitVec.ofNat 64 n) ?_ (by decide)) fun t9 ⟨⟨m9, r10⟩, k9⟩ => ?_
  · prun [ptr, wIv, exec_li (imm := aW) (by decide),
      exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide), hdr_eq, pw aW, r11b,
      w8.scr.st (show arr w aW + 40 + 8 ≤ Z by omega), BitVec.add_zero]
  have kk9 : Keep (.r10 :: kRegs) t8 t9 := k9.mono (by decide)
  have h9 : Ctx t9 B Z w N n 0 := ⟨w8.of_keep k9, by rw [r10]; simp, hn1, hnw, hN15, by decide, hw⟩
  have o9 := writeW64_outside t8.mem B (d := arr w aW + 40) (t8.gpr .r12) (by omega)
  have pv9 : val32 t9.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [m9, o9.val32 (by have := arr_disj (w := w) (show aMz ≠ aW by decide); omega) (by omega), m8, pv]
  -- 7: `f = p`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc]
  refine ptr_ok h9.ws (by decide) (by decide) (by decide) (by decide) ?_
  refine ptr_ok (h9.ws.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by decide) ?_
  refine WP.mono (cntN1_ok (h9.of_keep (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).mono (by decide))))
    fun x10 ⟨⟨q8, xm⟩, kx⟩ => ?_
  have k10a : Keep kRegs t9 x10 := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans kx).mono (by decide)
  have h10a := h9.of_keep k10a
  refine WP.mono (copyLoop_ok (dO := arr w aF) (dA := arr w aMz) h10a.ws.scr
    (by rw [kx.gpr _ (by decide)]; simp [gpr_write]) (by rw [kx.gpr _ (by decide)]; simp [gpr_write]) q8
    (by omega) (by omega) (by have := fitZ _ nF; omega) (by omega) (ahead_k (by decide) (by omega)))
    fun t10 ⟨vF, out10, k10⟩ => ?_
  rw [xm, mem_write, mem_write] at vF out10
  rw [pv9] at vF
  have h10 := h10a.of_keep (k10.mono (by decide))
  -- 8: `k = 1` for an even `x`.
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r5, .r11] (Q := fun u => (u.gpr .r11).toNat =
      (if (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = 0 then 1 else 0) ∧ u.mem = t10.mem) ?_ (by decide))
    fun t11 ⟨⟨r11k, m11⟩, k11⟩ => ?_
  · prun [ptr, exec_li (imm := aX) (by decide), exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide) (by decide),
      hdr_eq, h10.ptr aX, h10.ws.scr.ld (show arr w aX + 4 ≤ Z by have := fitZ _ nX; omega)]
    exact even_bit _
  have h11' := h10.of_keep (k11.mono (by decide))
  -- The frame so far.
  have a2 : KeyWorkspace.Keep B w [aMz] [] t1.mem t2.mem := by
    rw [m2]; exact KeyWorkspace.Keep.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a4 : KeyWorkspace.Keep B w [aB] [] t2.mem t4.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out4) (by omega) (by simp)
  have a5 : KeyWorkspace.Keep B w [aB] [] t4.mem t5.mem := by
    rw [m5]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o5) (by omega) (by simp)
  have a7 : KeyWorkspace.Keep B w [aMz] [] t6.mem t7.mem := by
    have o := writeW32_outside t6.mem B (d := arr w aMz) (((t6.mem.readW (off B (arr w aMz)) 32).setWidth 64 |||
      (if t6.gpr .r9 = 0#64 then 2#64 else 0#64)).setWidth 32) (by omega)
    rw [m7]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o) (by omega) (by simp)
  have a9 : KeyWorkspace.Keep B w [aW] [] t8.mem t9.mem := by
    rw [m9]; exact KeyWorkspace.Keep.of_arr (d := 40) o9 (by omega) (by simp)
  have a10 : KeyWorkspace.Keep B w [aF] [] t9.mem t10.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by have := fitZ _ nF; omega)
      (by simp)
  have K10 : KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] s.mem t10.mem :=
    (K1.mono (by simp)).trans ((a2.mono (by simp)).trans ((a4.mono (by simp)).trans ((a5.mono (by simp)).trans
      ((show KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] t5.mem t6.mem by rw [m6]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
        ((a7.mono (by simp)).trans ((show KeyWorkspace.Keep B w [aMz, aB, aW, aF] [] t7.mem t8.mem by
          rw [m8]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans ((a9.mono (by simp)).trans
            (a10.mono (by simp)))))))))
  have xX : val32 t11.mem B (arr w aX) n = x := by
    rw [m11, keep_val K10 (by omega) (by decide) (by simp) (fit _ nX), hx]
  have x0 : (t10.mem.readW (off B (arr w aX)) 32).toNat % 2 = x % 2 := by
    rw [← m11, ← xX]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk]; simp only [val32, w32]; omega
  have a10' : KeyWorkspace.Keep B w [aF] [] t9.mem t10.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out10) (by have := fitZ _ nF; omega)
      (by simp)
  have pM10 : val32 t10.mem B (arr w aMz) (n + 1) = vmod m := by
    rw [keep_val a10' (k := n + 1) (by omega) (by decide) (by simp) (fit _ nM), pv9]
  have pM : val32 t11.mem B (arr w aMz) n = vmod m := by
    rw [m11]; exact val_low (by omega) pM10 vlt
  -- 9: `g = x + k p`, its carry the digit `n`.
  rw [WP.seq_iff]
  refine WP.mono (mac_ok h11' (fun u hu => cntN_ok hu) (K := n) hn1 (by omega) nG nX nM hN
    (by rw [r11k]; split <;> decide)) fun t12 ⟨h12, K12, v12, c12, p12, _, out12, k12⟩ => ?_
  rw [xX, pM, r11k, x0] at v12
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = t12.mem.writeW (off B (arr w aG + 4 * n))
      ((t12.gpr .r9).setWidth 32)) ?_ (by decide)) fun t13 ⟨m13, k13⟩ => ?_
  · prun [p12, h12.ws.scr.st (show arr w aG + 4 * n + 4 ≤ Z by have := fitZ _ nG; omega)]
  have h13 := h12.of_keep (k13.mono (by decide))
  have vG : val32 t13.mem B (arr w aG) (n + 1) = oddInput (vmod m) x := by
    rw [m13, val32_write_top _ _ _ _ _ (by have := fit _ nG; omega), BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt c12]
    unfold oddInput
    by_cases e : x % 2 = 0 <;> simp only [e, ↓reduceIte] at v12 ⊢ <;> omega
  -- 10: `a = 0`.
  rw [WP.seq_iff, WP.seq_iff, List.append_assoc]
  refine ptr_ok h13.ws (by decide) (by decide) (by decide) (by decide) ?_
  rw [WP.block_append_iff]
  refine WP.mono (cntN1_ok (h13.of_keep ((Keep.write _ .r5 _).mono (by decide)))) fun x14 ⟨⟨q8', xm'⟩, kx'⟩ => ?_
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.gpr .r0 = 0 ∧ u.mem = x14.mem) (by prun; rfl) (by decide))
    fun y14 ⟨⟨y0, ym⟩, ky⟩ => ?_
  have k14a : Keep kRegs t13 y14 := (((Keep.write _ .r5 _).trans kx').trans ky).mono (by decide)
  refine WP.mono (zeroLoop_ok (dO := arr w aA) (n := n + 1) (h13.of_keep k14a).ws.scr
    (by rw [ky.gpr _ (by decide), kx'.gpr _ (by decide)]; simp [gpr_write])
    (by rw [ky.gpr _ (by decide)]; exact q8') y0 (by omega) (by omega) (by have := fitZ _ nA; omega))
    fun t14 ⟨z14, out14, k14⟩ => ?_
  rw [ym, xm', mem_write] at out14
  have h14 := (h13.of_keep k14a).of_keep (k14.mono (by decide))
  -- 11: `d = 1` and `3 (n + 1)` batches.
  refine WP.mono (WP.keep [.r0, .r3, .r5, .r10] (Q := fun u => u.mem = t14.mem.writeW (off B (arr w aW))
      (BitVec.ofNat 64 1) ∧ u.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * (3 * (n + 1)))) ?_ (by decide))
    fun t15 ⟨⟨m15, r15⟩, k15⟩ => ?_
  · have e := h14.r10
    simp only [Nat.mul_zero, Nat.add_zero] at e
    prun [ptr, wD, exec_li (imm := aW) (by decide), exec_addi (n := .r5) (imm := KeyWorkspace.hdr) (by decide)
      (by decide), hdr_eq, h14.ptr aW, h14.ws.scr.st (show arr w aW + 8 ≤ Z by omega), e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  -- The result.
  have a13 : KeyWorkspace.Keep B w [aG] [] t12.mem t13.mem := by
    have := fit _ nG
    rw [m13]; exact KeyWorkspace.Keep.of_arr (d := 4 * n) (writeW32_outside _ B _ (by omega)) (by omega) (by simp)
  have a14 : KeyWorkspace.Keep B w [aA] [] t13.mem t14.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out14) (by have := fitZ _ nA; omega)
      (by simp)
  have o15 := writeW64_outside t14.mem B (d := arr w aW) (BitVec.ofNat 64 1) (by omega)
  have a15 : KeyWorkspace.Keep B w [aW] [] t14.mem t15.mem := by
    rw [m15]; exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o15) (by omega) (by simp)
  have K15 : KeyWorkspace.Keep B w [aG, aA, aW] [] t10.mem t15.mem :=
    (show KeyWorkspace.Keep B w [aG, aA, aW] [] t10.mem t11.mem by rw [m11]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
      ((K12.mono (by simp)).trans ((a13.mono (by simp)).trans ((a14.mono (by simp)).trans (a15.mono (by simp)))))
  have K5 : KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t5.mem t15.mem :=
    (show KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t5.mem t6.mem by rw [m6]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans
      ((a7.mono (by simp)).trans ((show KeyWorkspace.Keep B w [aMz, aW, aF, aG, aA] [] t7.mem t8.mem by
        rw [m8]; exact KeyWorkspace.Keep.refl _ _ _ _ _).trans ((a9.mono (by simp)).trans ((a10'.mono (by simp)).trans
          (K15.mono (by simp))))))
  have hk2 : n + 1 ≤ w + 2 := by omega
  have m10 : ∀ {a b : State} {rs : List Reg}, Keep rs a b → (∀ r ∈ rs, r ∈ (.r10 :: kRegs)) →
      Keep (.r10 :: kRegs) a b := fun h hr => h.mono hr
  have k : Keep (.r10 :: kRegs) s t15 :=
    (((((((((((((k1.trans' (m10 k2 (by decide))).trans' (m10 ((Keep.write _ .r5 _).trans k3) (by decide))).trans'
      (m10 k4 (by decide))).trans' (m10 k5 (by decide))).trans' (m10 k6 (by decide))).trans' (m10 k7 (by decide))).trans'
      kk8).trans' kk9).trans' (m10 (k10a.trans k10) (by decide))).trans' (m10 k11 (by decide))).trans'
      (m10 (k12.trans k13) (by decide))).trans' (m10 (k14a.trans k14) (by decide))).trans' (m10 k15 (by decide)))
  refine ⟨⟨h14.ws.of_keep k15, r15, hn1, hnw, hN15, by omega, hw⟩, ⟨(t8.gpr .r12).toNat, hiv, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    (K10.mono (by simp)).trans (K15.mono (by simp)), k⟩
  · show sv t15.mem B (arr w aF) n = (vmod m : Int)
    refine sv_of_val ?_ (by exact_mod_cast vlt)
    rw [keep_val K15 hk2 (by decide) (by simp) (fit _ nF), vF]
  · show sv t15.mem B (arr w aG) n = (oddInput (vmod m) x : Int)
    refine sv_of_eq (q := 0) ?_ ?_ ?_
    · rw [keep_val a15 hk2 (by decide) (by simp) (fit _ nG), keep_val a14 hk2 (by decide) (by simp) (fit _ nG), vG]
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
    rw [keep_val a15 hk2 (by decide) (by simp) (fit _ nA), val32_zero z14]; rfl
  · show (val32 t15.mem B (arr w aB) (n + 1) : Int) = 1
    rw [keep_val K5 hk2 (by decide) (by simp) (fit _ nB), vB5]; rfl
  · show t15.mem.readW (off B (arr w aW + wD)) 64 = BitVec.ofInt 64 1
    rw [show arr w aW + wD = arr w aW from rfl, m15, Mem.readW_writeW_self64]; rfl
  · show (t15.mem.readW (off B (arr w aW + wIv)) 64).toNat = (t8.gpr .r12).toNat
    have w40 : 40 + 64 / 8 ≤ S w := by omega
    rw [show arr w aW + wIv = arr w aW + 40 from rfl, m15, Outside.readW64 o15 (by omega) (by omega),
      keep_word a14 w40 (by decide) (by simp) (fit _ nW), keep_word a13 w40 (by decide) (by simp) (fit _ nW),
      keep_word K12 w40 (by decide) (by simp) (fit _ nW), m11, keep_word a10' w40 (by decide) (by simp) (fit _ nW),
      m9, Mem.readW_writeW_self64]
  · rw [keep_val K15 hk2 (by decide) (by simp) (fit _ nM), pM10]

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE

`inverse_ok`: from `x` in array 0 and an odd `m` in array 8, both below
`2^(32 n)` for `n` in `r11` (`1 ≤ n ≤ w`), `inverse` leaves `gcd(x, m)` in
array 1 and, for `m > 1`, `y < m` with `y x ≡ gcd(x, m) (mod m)` in array 3,
`w` digits each; it writes only arrays 1–7 and 11–14 and the registers
`r0`, `r3`–`r12`.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The arrays `inverse` writes. -/
abbrev invArrs : List Nat := [1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14]

/-- The registers `inverse` changes. -/
abbrev invRegs : List Reg := .r10 :: kRegs

theorem inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa inverse s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hx' : val32 s.mem B (arr w aX) n = x := val_low hnw hx hxn
  have hm' : val32 s.mem B (arr w aMin) n = m := val_low hnw hm hmn
  have p1 : 1 < vmod m := by unfold vmod; split <;> omega
  have po : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have pA : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hmn
  have hk1 : n + 1 ≤ w + 2 := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  simp only [inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hw h11 hn1 hnw hx' hxn hm' hmn hodd) fun t0 ⟨h0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 st0 po p1 hiv pA hxn) fun t1 ⟨h1, st1, K1, k1⟩ => ?_
  rw [Nat.sub_self] at h1
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
    (Divstep.normal_range _ (by omega) (by omega)) pA) fun t3 ⟨h3, v3, K3, k3⟩ => ?_
  rw [Nat.sub_self] at h3
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
  refine WP.mono (finish_ok h3 hN hf3 hfr v3 hyr) fun t4 ⟨h4, K4, g4, y4, k4⟩ => ?_
  refine ⟨h4.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K3.mono (by decide)).trans (K4.mono (by decide)))))), ((k0.trans' k1).trans' (k2.mono (by decide))).trans'
    (k3.trans' (k4.mono (by decide))), fun hm1 => ?_⟩
  have pm : vmod m = m := by unfold vmod; split <;> omega
  rw [pm] at gf gd gl ce
  rw [show aGcd = 1 from rfl] at g4
  rw [show aY = 3 from rfl] at y4
  rw [g4, y4, pm, ce, gf]
  exact ⟨Nat.gcd_comm _ _, gd, gl⟩

end VG.Proof.Rsa.PPC64LE.InvBatch
