module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.Framework.Omega

/-! # `WordModRt` on i686: the guard

`balanced_ok`: the header word `sl` zero exactly when `n_len` is a multiple
of 8 and at least 128, `p_len = q_len = n_len / 2`, and the top bit of `n`'s
word `w - 1` is set (`Bal`), from public arguments and `n`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)

/-- The guard: a balanced key whose modulus fills its words and has its top bit set. -/
def Bal (nl pl ql top : Nat) : Prop :=
  nl % 8 = 0 ∧ 2 * pl = nl ∧ 2 * ql = nl ∧ 128 ≤ nl ∧ 2 ^ 31 ≤ top

theorem and7 (x : BitVec 32) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 32).toNat = 7 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 3]

theorem dbl_sub {p n : Nat} (hp : p < 2 ^ 30) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 32 p + BitVec.ofNat 32 p - BitVec.ofNat 32 n = 0) ↔ 2 * p = n := by
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at this; omega
  · intro e; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (0 : BitVec 32).toNat = 0 from rfl]; omega

theorem top_clear (x : BitVec 32) : (x ^^^ -1) >>> 31 = 0 ↔ 2 ^ 31 ≤ x.toNat := by
  rw [show (-1 : BitVec 32) = BitVec.allOnes 32 from rfl, BitVec.xor_allOnes]
  constructor
  · intro e; have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_not, Nat.shiftRight_eq_div_pow,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    have := x.isLt; omega
  · intro e; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_not, Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    have := x.isLt; omega

theorem or_zero (a b : BitVec 32) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  change a ||| b = 0#32 ↔ a = 0#32 ∧ b = 0#32
  exact BitVec.or_eq_zero_iff

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `balanced nl pl ql n sl`: the header word `sl` zero exactly when `Bal` holds of the lengths
`n_len`, `p_len`, `q_len` (arguments `nl`, `pl`, `ql`) and `n`'s word `w - 1`. -/
theorem balanced_ok {s : State} (h : RtWs L s B Z len N) {nl pl ql n sl an ap aq : Nat}
    (cn : CallArgument s B Z nl (BitVec.ofNat 32 an)) (cp : CallArgument s B Z pl (BitVec.ofNat 32 ap))
    (cq : CallArgument s B Z ql (BitVec.ofNat 32 aq)) (han : an ≤ 1024) (hap : ap ≤ 1024) (haq : aq ≤ 1024)
    (hn : n < N) (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.balanced L nl pl ql n sl)) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [] [sl] s.mem v.mem ∧
      (slot v.mem B sl = 0 ↔ Bal an ap aq (mw s.mem B (kw len) n (kw len - 1))) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s v := by
  have fn := h.ws.arr_fit hn
  have nw := h.ws.workspace.nowrap
  have wpos := h.kw_pos
  have hkw := VG.Proof.Rsa.X86.KeyRt.kw_bound h.lenLe
  simp only [S] at fn
  unfold VG.Impl.Rsa.X86.WordModRt.balanced
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS cn.readSrc fun t1 U1 _ => wp_movS rfl fun t2 U2 _ => wp_logicS (Or.inl rfl) rfl fun t3 U3 => ?_
  have K3 : Keeps [.eax, .ecx] s t3 := ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans
    (U3.keeps.mono (by decide))
  have m3 : t3.mem = s.mem := by rw [U3.mem, U2.mem, U1.mem]
  refine wp_movS (cp.keep K3 (by decide) (by rw [m3]; exact Outside.refl _ _ _ _)).readSrc fun t4 U4 _ =>
    wp_addS rfl fun t5 U5 _ => wp_subS rfl fun t6 U6 _ => wp_orS rfl fun t7 U7 => ?_
  have K7 : Keeps [.eax, .ecx, .edx] s t7 := (K3.mono (by decide)).trans
    (((U4.keeps.mono (by decide)).trans (U5.keeps.mono (by decide))).trans
      ((U6.keeps.mono (by decide)).trans (U7.keeps.mono (by decide))))
  have m7 : t7.mem = s.mem := by rw [U7.mem, U6.mem, U5.mem, U4.mem, m3]
  refine wp_movS (cq.keep K7 (by decide) (by rw [m7]; exact Outside.refl _ _ _ _)).readSrc fun t8 U8 _ =>
    wp_addS rfl fun t9 U9 _ => wp_subS rfl fun t10 U10 _ => wp_orS rfl fun t11 U11 => ?_
  refine wp_cmpi fun t12 F12 c12 _ => wp_sbbS rfl c12 fun t13 U13 _ => wp_orS rfl fun t14 U14 => ?_
  have K14 : Keeps [.eax, .ecx, .edx] s t14 := (K7.mono (by decide)).trans
    ((((U8.keeps.mono (by decide)).trans (U9.keeps.mono (by decide))).trans
      ((U10.keeps.mono (by decide)).trans (U11.keeps.mono (by decide)))).trans
      ((Keeps.mono (⟨fun r _ => by rw [F12.gpr], F12.rd, F12.wr⟩ : Keeps [] t11 t12) (by simp)).trans
        ((U13.keeps.mono (by decide)).trans (U14.keeps.mono (by decide)))))
  have m14 : t14.mem = s.mem := by rw [U14.mem, U13.mem, F12.mem, U11.mem, U10.mem, U9.mem, U8.mem, m7]
  have h14 := h.keep K14 (by decide) (by decide) (by rw [m14]; exact Outside.refl _ _ _ _)
  -- The bits so far.
  have ecx14 : t14.gpr .ecx =
      (((BitVec.ofNat 32 an &&& 7) ||| (BitVec.ofNat 32 ap + BitVec.ofNat 32 ap - BitVec.ofNat 32 an)) |||
        (BitVec.ofNat 32 aq + BitVec.ofNat 32 aq - BitVec.ofNat 32 an)) |||
        (t12.gpr .edx - t12.gpr .edx - (BitVec.ofBool (decide (an < 128))).setWidth 32) := by
    rw [U14.gpr, U13.other .ecx (by decide), U13.gpr, F12.gpr, U11.gpr, U10.other .ecx (by decide),
      U9.other .ecx (by decide), U8.other .ecx (by decide), U7.gpr, U6.other .ecx (by decide),
      U5.other .ecx (by decide), U4.other .ecx (by decide), U3.gpr, ite_eq_left rfl, U2.gpr, U10.gpr, U9.gpr, U8.gpr,
      U6.gpr, U5.gpr, U4.gpr, U9.other .eax (by decide), U8.other .eax (by decide), U7.other .eax (by decide),
      U6.other .eax (by decide), U5.other .eax (by decide), U4.other .eax (by decide), U3.other .eax (by decide),
      U2.other .eax (by decide), U1.gpr]
    have eax11 : (t11.gpr .eax).toNat = an := by
      rw [U11.other .eax (by decide), U10.other .eax (by decide), U9.other .eax (by decide),
        U8.other .eax (by decide), U7.other .eax (by decide), U6.other .eax (by decide), U5.other .eax (by decide),
        U4.other .eax (by decide), U3.other .eax (by decide), U2.other .eax (by decide), U1.gpr, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    rw [eax11, show (128 : BitVec 32).toNat = 128 from rfl]
  -- `n`'s top word.
  refine arrPtr_ok (lenSrc h14) h14.lenLe h14.edi (r := .ebx) (t := .edx) (j := n) (by decide) (by decide)
    (by omega) fun u1 K1 m1 p1 _ => ?_
  refine bytesB_ok (r := .eax) ((lenSrc h14).keep K1 (by decide) m1) h.lenLe fun u2 K2 m2 e2 =>
    wp_addS rfl fun u3 V3 _ => wp_subS rfl fun u4 V4 _ => ?_
  have K4 : Keeps [.eax, .ebx, .ecx, .edx] s u4 := (K14.mono (by decide)).trans
    (((K1.mono (by decide)).trans (K2.mono (by decide))).trans ((V3.keeps.mono (by decide)).trans
      (V4.keeps.mono (by decide))))
  have m4 : u4.mem = s.mem := by rw [V4.mem, V3.mem, m2, m1, m14]
  have p4 : PtrAt u4 B .ebx (arr (kw len) n + 4 * (kw len - 1)) := by
    rw [PtrAt, V4.gpr, BitVec.toNat_sub, V3.gpr, BitVec.toNat_add, K2.1 .ebx (by decide), p1, e2,
      show (4 : BitVec 32).toNat = 4 from rfl]
    have := B.isLt; omega
  refine wp_movS (readSrc_ptr (h.rt.of_keeps K4) p4 (d := 0) (by omega)) fun u5 V5 _ =>
    wp_logicS (Or.inr rfl) rfl fun u6 V6 => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u7 V7 =>
      wp_orS rfl fun u8 V8 => ?_
  have K8 : Keeps [.eax, .ebx, .ecx, .edx] s u8 := K4.trans
    (((V5.keeps.mono (by decide)).trans (V6.keeps.mono (by decide))).trans
      ((V7.keeps.mono (by decide)).trans (V8.keeps.mono (by decide))))
  have m8 : u8.mem = s.mem := by rw [V8.mem, V7.mem, V6.mem, V5.mem, m4]
  have h8 := h.keep K8 (by decide) (by decide) (by rw [m8]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h8 hsl .ecx) fun v ⟨hv, kv, ev, Kv⟩ => ?_
  refine ⟨hv, by rw [← m8]; exact kv, ?_, K8.trans (Kv.mono (by simp))⟩
  have ecx8 : u8.gpr .ecx = t14.gpr .ecx |||
      ((s.mem.readW (off B (arr (kw len) n + 4 * (kw len - 1))) 32 ^^^ -1) >>> 31) := by
    rw [V8.gpr, V7.other .ecx (by decide), V6.other .ecx (by decide), V5.other .ecx (by decide),
      V4.other .ecx (by decide), V3.other .ecx (by decide), K2.1 .ecx (by decide), K1.1 .ecx (by decide), V7.gpr,
      V6.gpr, ite_eq_right (by decide), V5.gpr, m4, Nat.add_zero]
  have eslot : slot v.mem B sl = 0 ↔ u8.gpr .ecx = 0 := by
    rw [ev]; constructor
    · intro e; exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    · intro e; rw [e]; rfl
  rw [eslot, ecx8, ecx14, or_zero, or_zero, or_zero, or_zero, top_clear]
  have hm : (t12.gpr .edx - t12.gpr .edx - (BitVec.ofBool (decide (an < 128))).setWidth 32 = 0) ↔ ¬ an < 128 := by
    constructor
    · intro e hc; have := congrArg BitVec.toNat e
      rw [VG.Proof.Bignum.X86.R2Words.sbb_self, show (0 : BitVec 32).toNat = 0 from rfl] at this
      simp [hc] at this
    · intro hc; apply BitVec.eq_of_toNat_eq
      rw [VG.Proof.Bignum.X86.R2Words.sbb_self, show (0 : BitVec 32).toNat = 0 from rfl]; simp [hc]
  have key7 : (BitVec.ofNat 32 an &&& 7).toNat = an % 8 := by
    rw [and7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show an < 2 ^ 32 by omega)]
  have h7 : (BitVec.ofNat 32 an &&& 7 = 0) ↔ an % 8 = 0 := by
    constructor
    · intro e; have := congrArg BitVec.toNat e
      rw [key7] at this; simpa using this
    · intro e; apply BitVec.eq_of_toNat_eq; rw [key7, e]; rfl
  rw [hm, h7, dbl_sub (by omega) (by omega), dbl_sub (by omega) (by omega)]
  simp only [Bal, mw, w32, Nat.not_lt]
  constructor
  · rintro ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩; exact ⟨a, b, c, d, e⟩
  · rintro ⟨a, b, c, d, e⟩; exact ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩


/-! ## What the guard gives -/

/-- A factor of a number of `2 K` bits, the other below `2^K`, is above `2^(K - 1)`. -/
theorem factor_top {K p q n : Nat} (hn : 2 ^ (2 * K - 1) ≤ n) (hq : q < 2 ^ K)
    (hpq : p * q = n) : 2 ^ (K - 1) < p := by
  refine Nat.lt_of_not_le fun hle => ?_
  have e : 2 ^ (2 * K - 1) = 2 ^ (K - 1) * 2 ^ K := by rw [← Nat.pow_add]; congr 1; omega
  have : p * q < 2 ^ (K - 1) * 2 ^ K :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right q hle) (Nat.mul_lt_mul_of_pos_left hq (Nat.two_pow_pos _))
  omega

theorem top_factor {K p : Nat} (lo : 2 ^ (K - 1) < p) (hi : p < 2 ^ K) :
    (2 ^ (K - 1) ≤ p ∧ p < 2 ^ K) ∧ (2 ^ (K - 1) ≤ 2 * (p / 2) ∧ 2 * (p / 2) < 2 ^ K) :=
  ⟨⟨Nat.le_of_lt lo, hi⟩, ⟨by omega, by omega⟩⟩

/-- Under the guard: `p`'s width is a sound divisor's, and where `p q = n`, `p`, `p - 1` and
`q - 1` have their top bits set. -/
theorem bal_top {an ap aq top w P Q N : Nat} (bal : Bal an ap aq top) (hkw : kw an = w)
    (htop : 2 ^ 31 ≤ top ↔ 2 ^ (32 * w - 1) ≤ N) (hp : P < 2 ^ (8 * ap)) (hq : Q < 2 ^ (8 * aq)) :
    4 ≤ wq ap ∧ wq ap + 2 ≤ w ∧
      (P * Q = N → Top (wq ap) P ∧ Top (wq ap) (2 * (P / 2)) ∧ Top (wq ap) (2 * (Q / 2))) := by
  obtain ⟨h8, hpa, hqa, h128, ht⟩ := bal
  have hw : w = an / 4 := by
    rw [← hkw]; simp only [kw, Spec.Rsa.modulusWords]; omega
  have hwq : wq ap = ap / 4 := by simp only [wq]; omega
  have hK : 32 * wq ap = 8 * ap := by rw [hwq]; omega
  have hn : 2 ^ (2 * (8 * ap) - 1) ≤ N := by
    have := htop.mp ht
    rwa [show 32 * w = 2 * (8 * ap) by rw [hw]; omega] at this
  have hq' : Q < 2 ^ (8 * ap) := by rwa [show 8 * aq = 8 * ap by omega] at hq
  refine ⟨by omega, by omega, fun hpq => ?_⟩
  simp only [Top, hK]
  have pt := top_factor (factor_top hn hq' hpq) hp
  have qt := top_factor (factor_top hn hp (by rw [Nat.mul_comm]; exact hpq)) hq'
  exact ⟨pt.1, pt.2, qt.2⟩

theorem sub0_beq (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_sub]
  have := x.isLt
  show (2 ^ 32 - 0 + x.toNat) % 2 ^ 32 = 0 ↔ _
  constructor <;> intro h <;> omega

/-- `ifBalanced sl word other`: `word` where `sl` is zero, else `other`, each from a state that only
`eax` and the flags tell apart. -/
theorem ifBalanced_ok {s : State} (h : RtWs L s B Z len N) {sl : Nat} (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    {P : Prop} (hg : slot s.mem B sl = 0 ↔ P) {W O : Prog isa} {Q : State → Prop}
    (hW : P → ∀ u, RtWs L u B Z len N → Keeps [.eax] s u → u.mem = s.mem → WP isa W u Q)
    (hO : ¬P → ∀ u, RtWs L u B Z len N → Keeps [.eax] s u → u.mem = s.mem → WP isa O u Q) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.ifBalanced sl W O) s Q := by
  unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
  have hz := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hsl hz
  refine WP.seq (wp_movS (readSrc_sc h.ws.workspace (by omega))
    fun u U _ => wp_cmpi fun t T _ z => WP.block_nil ?_)
  have K : Keeps [.eax] s t := U.keeps.trans (T.keeps [.eax])
  have M : t.mem = s.mem := T.mem.trans U.mem
  have ht := h.keep K (by decide) (by decide) (by rw [M]; exact Outside.refl _ _ _ _)
  have ev : u.gpr .eax = s.mem.readW (off B sl) 32 := U.gpr
  have sv : slot s.mem B sl = (s.mem.readW (off B sl) 32).toNat := rfl
  refine WP.ite _ (by change t.zf = _; exact z) (fun hb => hW (hg.mp ?_) t ht K M) (fun hb => hO (fun p => ?_) t ht K M)
  · rw [ev, sub0_beq, decide_eq_true_iff] at hb
    rw [sv, hb]
  · rw [ev, sub0_beq, decide_eq_false_iff_not] at hb
    exact hb (by rw [← sv]; exact hg.mpr p)

end VG.Proof.Rsa.X86.WordRt
