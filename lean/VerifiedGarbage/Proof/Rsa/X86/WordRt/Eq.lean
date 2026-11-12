module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

/-! # `WordModRt` on i686: a product compared with the modulus

`eqWide_ok`: the header word `sl` one exactly when the `2 w` words at `o`
are `[n]`, by `KeyRt`'s `eqLoop` on the low `w` words and an or of the
high `w` (`orLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

theorem val32_zero_iff (m : Mem) (W : Addr) (x N : Nat) :
    val32 m W x N = 0 ↔ ∀ i < N, m.readW (off W (x + 4 * i)) 32 = 0 := by
  induction N generalizing x with
  | zero => simp [val32]
  | succ N ih =>
    have split : val32 m W x (N + 1) = 0 ↔ w32 m W x = 0 ∧ val32 m W (x + 4) N = 0 := by
      simp only [val32]; constructor
      · intro h; constructor <;> omega
      · rintro ⟨a, b⟩; rw [a, b]
    rw [split, ih]
    constructor
    · rintro ⟨lo, hi⟩ i hiN
      cases i with
      | zero => simpa using BitVec.eq_of_toNat_eq lo
      | succ i => simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi i (by omega)
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have := congrArg BitVec.toNat (h 0 (by omega))
        simpa [w32] using this
      · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (i + 1) (by omega)

/-- The loop or'ing `N` words at `ebp` into `ecx`. -/
abbrev orLoop : Prog isa :=
  .loop (.block [.alu .or .ecx (.mem (at_ .ebp 0)), .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne

theorem orLoop_ok {s : State} {W : Addr} {Z x N : Nat} (hw : Ws s W Z) (hN : 0 < N) (hx : x + 4 * N ≤ Z)
    (hp : PtrAt s W .ebp x) (hn : (s.gpr .edx).toNat = 4 * N) :
    WP isa orLoop s fun u => u.mem = s.mem ∧
      (u.gpr .ecx = 0 ↔ s.gpr .ecx = 0 ∧ val32 s.mem W x N = 0) ∧ Keeps [.ecx, .edx, .ebp] s u := by
  refine WP.mono (countLoop hN (fun j t => Keeps [.ecx, .edx, .ebp] s t ∧ t.mem = s.mem ∧
      PtrAt t W .ebp (x + 4 * j) ∧ (t.gpr .edx).toNat = 4 * (N - j) ∧
      (t.gpr .ecx = 0 ↔ s.gpr .ecx = 0 ∧ ∀ i < j, s.mem.readW (off W (x + 4 * i)) 32 = 0)) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using hp, by simpa using hn, by simp⟩)
    fun u ⟨K, m, _, _, e⟩ => ⟨m, e.trans (and_congr_right fun _ => (val32_zero_iff _ _ _ _).symm), K⟩
  rintro j t hj ⟨K, m, p, n, e⟩
  have ht := hw.of_keeps K
  refine wp_orS (readSrc_ptr ht p (d := 0) (by omega)) fun s1 U1 => wp_addS rfl fun s2 U2 _ =>
    wp_subZ rfl fun s3 U3 z3 => WP.block_nil ?_
  have K3 : Keeps [.ecx, .edx, .ebp] t s3 :=
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))
  have m3 : s3.mem = t.mem := by rw [U3.mem, U2.mem, U1.mem]
  obtain ⟨cn, cz⟩ := count_zf n hj
  refine ⟨⟨K.trans K3, m3.trans m, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, U3.other _ (by decide), U2.gpr, U1.other _ (by decide)]; exact ptr4 p
  · rw [U3.gpr, U2.other _ (by decide), U1.other _ (by decide)]; exact cn
  · rw [U3.other _ (by decide), U2.other _ (by decide), U1.gpr, m, Nat.add_zero]
    change (_ ||| _) = 0#32 ↔ _
    rw [BitVec.or_eq_zero_iff]
    change t.gpr .ecx = 0 ∧ _ ↔ _
    rw [e]
    constructor
    · rintro ⟨⟨c0, old⟩, last⟩; refine ⟨c0, fun i hi => ?_⟩
      by_cases eq : i = j
      · subst eq; exact last
      · exact old i (by omega)
    · rintro ⟨c0, all⟩; exact ⟨⟨c0, fun i hi => all i (by omega)⟩, all j (by omega)⟩
  · rw [z3, U2.other _ (by decide), U1.other _ (by decide), cz]

/-- `(x | -x) >> 31` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 32) : (0 - x ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (0 - x).toNat = 2 ^ 32 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 31 ≤ (0 - x ||| x).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 31) with h2 | h2
      · exact Nat.le_trans (by omega) (Nat.left_le_or (n := (0 - x).toNat))
      · exact Nat.le_trans h2 Nat.right_le_or
    have h2 := (0 - x ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega

/-- A number of `2 w` words is one of `w` exactly when its low `w` words are it and its high zero. -/
theorem wide_eq_iff {m : Mem} {W : Addr} {x w n : Nat} (hn : n < 2 ^ (32 * w)) :
    val32 m W x (2 * w) = n ↔ val32 m W x w = n ∧ val32 m W (x + 4 * w) w = 0 := by
  rw [show 2 * w = w + w by omega, val32_append]
  have hl := val32_lt m W x w
  constructor
  · intro e
    have h0 : val32 m W (x + 4 * w) w = 0 := by
      by_contra hc
      have := Nat.mul_le_mul_left (2 ^ (32 * w)) (Nat.one_le_iff_ne_zero.mpr hc)
      omega
    refine ⟨?_, h0⟩; rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e
  · rintro ⟨a, b⟩; rw [a, b, Nat.mul_zero, Nat.add_zero]

/-- `eqWide sl o n`: the header word `sl` one exactly when the `2 w` words at `o` (across arrays
`o` and `o + 1`) are `[n]`. -/
theorem eqWide_ok {L : Lay} {s : State} {B : Addr} {Z len N : Nat} (h : RtWs L s B Z len N) {sl o n : Nat}
    (ho : o + 1 < N) (hn : n < N) (hsl : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.eqWide L sl o n) s fun v => RtWs L v B Z len N ∧
      Keep B (kw len) [] [sl] s.mem v.mem ∧
      slot v.mem B sl = (if val32 s.mem B (arr (kw len) o) (2 * kw len) = num s.mem B (kw len) n then 1 else 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s v := by
  have fo := h.ws.arr_fit ho
  have fn := h.ws.arr_fit hn
  have nw := h.ws.workspace.nowrap
  have wpos := h.kw_pos
  simp only [S] at fo fn
  rw [VG.Proof.Rsa.X86.Keys.arr_succ] at fo
  simp only [S] at fo
  unfold VG.Impl.Rsa.X86.WordModRt.eqWide
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs, List.append_assoc]
  refine WP.seq (arrPtr_ok (lenSrc h) h.lenLe h.edi (r := .ebp) (t := .edx) (j := o) (by decide) (by decide)
    (by omega) fun s1 K1 m1 p1 _ => ?_)
  have h1 := h.keep K1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h1) h1.lenLe h1.edi (r := .ebx) (t := .edx) (j := n) (by decide) (by decide) (by omega)
    fun s2 K2 m2 p2 _ => ?_
  have h2 := h1.keep K2 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _)
  refine bytesB_ok (r := .edx) (lenSrc h2) h2.lenLe fun s3 K3 m3 n3 => wp_movS rfl fun s4 U4 _ => WP.block_nil ?_
  have K4 : Keeps [.ebx, .ecx, .edx, .ebp] s s4 :=
    (((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans (U4.keeps.mono (by decide))
  have m4 : s4.mem = s.mem := by rw [U4.mem, m3, m2, m1]
  have h4 := h.keep K4 (by decide) (by decide) (by rw [m4]; exact Outside.refl _ _ _ _)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.eqLoop_ok h4.rt (x := arr (kw len) o) (y := arr (kw len) n)
    wpos (by omega) (by omega)
    (by rw [PtrAt, U4.other _ (by decide), K3.1 _ (by decide), K2.1 _ (by decide)]; exact p1)
    (by rw [PtrAt, U4.other _ (by decide), K3.1 _ (by decide)]; exact p2)
    U4.gpr (by rw [U4.other _ (by decide)]; exact n3)) fun u ⟨mu, eu, Ku, pu⟩ => ?_)
  have hu := h4.keep Ku (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _)
  rw [← List.append_nil (bytesB L .edx)]
  refine WP.seq (bytesB_ok (r := .edx) (lenSrc hu) hu.lenLe fun u1 Ku1 mu1 nu1 => WP.block_nil ?_)
  refine WP.seq (WP.mono (orLoop_ok (hu.rt.of_keeps Ku1) wpos (x := arr (kw len) o + 4 * kw len) (by omega)
    (by rw [PtrAt, Ku1.1 _ (by decide)]; exact pu) nu1) fun v ⟨mv, ev, Kv⟩ => ?_)
  have Kv' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s v :=
    ((K4.mono (by decide)).trans Ku).trans ((Ku1.mono (by decide)).trans (Kv.mono (by decide)))
  have mv' : v.mem = s.mem := by rw [mv, mu1, mu, m4]
  have hv := h.keep Kv' (by decide) (by decide) (by rw [mv']; exact Outside.refl _ _ _ _)
  refine wp_movS rfl fun v1 V1 _ => wp_subS rfl fun v2 V2 _ => wp_orS rfl fun v3 V3 =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun v4 V4 => wp_logicS (Or.inr rfl) rfl fun v5 V5 => ?_
  have K5 : Keeps [.eax] v v5 := (((V1.keeps.trans V2.keeps).trans V3.keeps).trans V4.keeps).trans V5.keeps
  have h5 := hv.keep K5 (by decide) (by decide) (by rw [V5.mem, V4.mem, V3.mem, V2.mem, V1.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h5 hsl .eax) fun t ⟨ht, kt, et, Kt⟩ => ?_
  have m5 : v5.mem = s.mem := by rw [V5.mem, V4.mem, V3.mem, V2.mem, V1.mem, mv']
  refine ⟨ht, by rw [← m5]; exact kt, ?_, (Kv'.mono (by decide)).trans ((K5.mono (by decide)).trans (Kt.mono (by simp)))⟩
  have ecx : v4.gpr .ecx = v.gpr .ecx := by
    rw [V4.other _ (by decide), V3.other _ (by decide), V2.other _ (by decide), V1.other _ (by decide)]
  have eax : v5.gpr .eax = ((0 - v.gpr .ecx ||| v.gpr .ecx) >>> 31) ^^^ 1 := by
    rw [V5.gpr, ite_eq_right (by decide), V4.gpr, V3.gpr, V2.gpr, V2.other .ecx (by decide), V1.gpr,
      V1.other .ecx (by decide)]
  rw [et, eax, nz_bit]
  have key : v.gpr .ecx = 0 ↔ val32 s.mem B (arr (kw len) o) (2 * kw len) = num s.mem B (kw len) n := by
    rw [ev, Ku1.1 .ecx (by decide), eu, mu1, mu, m4, wide_eq_iff (val32_lt _ _ _ _)]
  by_cases e : v.gpr .ecx = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true e), ite_eq_left_of_eq_true _ _ (eq_true (key.mp e))]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => e (key.mpr h')))]; rfl

end VG.Proof.Rsa.X86.WordRt
