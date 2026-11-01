module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbBatch
public import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The batched inverse on PPC64LE: the end

`normalize_ok`: `a := (p - a) mod p` if `f < 0`; `doublings_ok`: `a 2^(6 (n + 1))
mod p`; `finish_ok`: `|f|` and `a` into arrays 1 and 3, `w` digits each.
-/

@[expose] public section

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
          else val32 s.mem B (arr w a) (n + 1)) ∧ Keep kRegs s t := by
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
    (by simp), ?_, k⟩
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
  refine WP.mono (signSel_ok h2 nA nA n3 hN (by decide)) fun t3 ⟨h3, K3, v3, k3⟩ => ?_
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

end VG.Proof.Rsa.PPC64LE.InvBatch
