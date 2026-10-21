module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant-schedule equality of arrays at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (arr num S slot Keep)
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

theorem val32_eq_iff (m : Mem) (W : Addr) (x y N : Nat) :
    val32 m W x N = val32 m W y N ↔
      ∀ i < N, m.readW (off W (x + 4 * i)) 32 = m.readW (off W (y + 4 * i)) 32 := by
  induction N generalizing x y with
  | zero => simp [val32]
  | succ N ih =>
    have hx := (m.readW (off W x) 32).isLt
    have hy := (m.readW (off W y) 32).isLt
    have split : val32 m W x (N + 1) = val32 m W y (N + 1) ↔
        w32 m W x = w32 m W y ∧ val32 m W (x + 4) N = val32 m W (y + 4) N := by
      simp only [val32]
      change _ at hx hy
      unfold w32 at *
      omega
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

theorem eqLoop_ok {s : State} {W : Addr} {Z x y N : Nat} (hw : Ws s W Z)
    (hN : 0 < N) (hx : x + 4 * N ≤ Z) (hy : y + 4 * N ≤ Z)
    (hp : PtrAt s W .ebp x) (hb : PtrAt s W .ebx y)
    (hc : s.gpr .ecx = 0) (hn : (s.gpr .edx).toNat = 4 * N) :
    WP isa eqLoop s fun u => u.mem = s.mem ∧
      (u.gpr .ecx = 0 ↔ val32 s.mem W x N = val32 s.mem W y N) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  unfold eqLoop
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      t.mem = s.mem ∧ PtrAt t W .ebp (x + 4 * j) ∧ PtrAt t W .ebx (y + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧
      (t.gpr .ecx = 0 ↔ ∀ i < j, s.mem.readW (off W (x + 4 * i)) 32 =
        s.mem.readW (off W (y + 4 * i)) 32)) ?_
    ⟨Keeps.refl _ _, rfl, by simpa using hp, by simpa using hb, by simpa using hn,
      by simp [hc]⟩) fun u ⟨K, m, _, _, _, e⟩ => ⟨m, e.trans (val32_eq_iff _ _ _ _ _).symm, K⟩
  rintro j t hj ⟨K, m, p, b, n, e⟩
  have ht := hw.of_keeps K
  refine wp_movS (readSrc_ptr ht p (d := 0) (by omega)) fun s1 U1 _ => ?_
  have ht1 := ht.of_keeps U1.keeps
  have b1 : PtrAt s1 W .ebx (y + 4 * j) := by rw [PtrAt, U1.other _ (by decide)]; exact b
  refine wp_logicS (.inr rfl) (readSrc_ptr ht1 b1 (d := 0) (by omega)) fun s2 U2 => ?_
  refine wp_orS rfl fun s3 U3 => wp_addS rfl fun s4 U4 _ => wp_addS rfl fun s5 U5 _ =>
    wp_subZ rfl fun s6 U6 z6 => WP.block_nil ?_
  have K3 : Keeps [.eax, .ecx] t s3 :=
    ((U1.keeps.mono (by decide)).trans (U2.keeps.mono (by decide))).trans (U3.keeps.mono (by decide))
  have K6 : Keeps [.eax, .ebx, .ecx, .edx, .ebp] t s6 :=
    (((K3.mono (by decide)).widen U4.keeps).widen U5.keeps).widen U6.keeps
  have m6 : s6.mem = t.mem := by rw [U6.mem, U5.mem, U4.mem, U3.mem, U2.mem, U1.mem]
  obtain ⟨cn, cz⟩ := count_zf n hj
  refine ⟨⟨K.trans K6, m6.trans m, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, U6.other _ (by decide), U5.other _ (by decide), U4.gpr, K3.1 _ (by decide)]
    exact ptr4 p
  · rw [PtrAt, U6.other _ (by decide), U5.gpr, U4.other _ (by decide), K3.1 _ (by decide)]
    exact ptr4 b
  · rw [U6.gpr, U5.other _ (by decide), U4.other _ (by decide), K3.1 _ (by decide)]
    exact cn
  · rw [U6.other _ (by decide), U5.other _ (by decide), U4.other _ (by decide), U3.gpr,
      U2.other _ (by decide), U1.other _ (by decide), U2.gpr, ite_eq_right (by decide), U1.gpr,
      U1.mem, m, Nat.add_zero, Nat.add_zero]
    change (_ ||| _) = 0#32 ↔ _
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
    change (t.gpr .ecx = 0) ∧ _ ↔ _
    rw [e]
    constructor
    · rintro ⟨old, last⟩ i hi
      by_cases eq : i = j
      · simpa [eq] using last
      · exact old i (by omega)
    · intro all
      exact ⟨fun i hi => all i (by omega), all j (by omega)⟩
  · rw [z6, U5.other _ (by decide), U4.other _ (by decide), K3.1 _ (by decide), cz]

theorem eqArrays_ok {L : Lay} {s : State} {W : Addr} {Z len N a b : Nat}
    (h : RtWs L s W Z len N) (ha : a < N) (hb : b < N) :
    WP isa (eqArrays L a b) s fun u => RtWs L u W Z len N ∧ u.mem = s.mem ∧
      (u.gpr .ecx = 0 ↔ num s.mem W (kw len) a = num s.mem W (kw len) b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have nw := h.ws.workspace.nowrap
  simp only [S] at fa fb
  unfold eqArrays
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi (by decide) (by decide) (by omega) fun s1 K1 m1 p1 _ => ?_
  have h1 := h.keep K1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc h1) h1.lenLe h1.edi (by decide) (by decide) (by omega) fun s2 K2 m2 p2 _ => ?_
  have h2 := h1.keep K2 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _)
  refine bytesB_ok (r := .edx) (lenSrc h2) h2.lenLe fun s3 K3 m3 n3 => ?_
  refine wp_movS rfl fun s4 U4 _ => WP.block_nil ?_
  have K4 : Keeps [.ebx, .ecx, .edx, .ebp] s s4 :=
    (((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans
      (U4.keeps.mono (by decide))
  have m4 : s4.mem = s.mem := by rw [U4.mem, m3, m2, m1]
  have h4 := h.keep K4 (by decide) (by decide) (by rw [m4]; exact Outside.refl _ _ _ _)
  refine WP.mono (eqLoop_ok h4.rt (x := arr (kw len) a) (y := arr (kw len) b)
    h.kw_pos (by omega) (by omega)
    (by rw [PtrAt, U4.other _ (by decide), K3.1 _ (by decide), K2.1 _ (by decide)]; exact p1)
    (by rw [PtrAt, U4.other _ (by decide), K3.1 _ (by decide)]; exact p2)
    U4.gpr (by rw [U4.other _ (by decide)]; exact n3)) fun u ⟨m, e, K⟩ => ?_
  have mem := m.trans m4
  have KK : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := (K4.mono (by decide)).trans K
  refine ⟨h.keep KK (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _), mem, ?_, KK⟩
  simpa only [m4, num] using e

theorem eqSFast_ok {L : Lay} {B : Addr} {Z len N : Nat} {s : State} (h : RtWs L s B Z len N) {d a b : Nat}
    (ha : a < N) (hb : b < N) (hd : d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.eqSFast L d a b) s fun u => RtWs L u B Z len N ∧
      Keep B (kw len) [] [d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B (kw len) a = num s.mem B (kw len) b then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s u := by
  unfold VG.Impl.Rsa.X86.KeyRt.eqSFast
  refine WP.seq (WP.mono (eqArrays_ok h ha hb) fun u ⟨hu, mem, e, K⟩ => ?_)
  refine wp_movS rfl fun s1 U1 _ => wp_subS rfl fun s2 U2 _ => wp_orS rfl fun s3 U3 =>
    wp_shr (by decide) fun s4 U4 _ => wp_logicS (.inr rfl) rfl fun s5 U5 => ?_
  have K5 : Keeps [.eax] u s5 := (((U1.keeps.trans U2.keeps).trans U3.keeps).trans U4.keeps).trans U5.keeps
  have mem5 : s5.mem = u.mem := by rw [U5.mem, U4.mem, U3.mem, U2.mem, U1.mem]
  have h5 := hu.keep K5 (by decide) (by decide) (by rw [mem5]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok h5 hd .eax) fun v ⟨hv, F, V, R⟩ => ?_
  rw [mem5, mem] at F
  refine ⟨hv, F, ?_,
    ((K.trans (K5.mono (by decide))).trans (R.mono (by decide))).mono (by decide)⟩
  have ex : s5.gpr .eax = ((((0 : BitVec 32) - u.gpr .ecx) ||| u.gpr .ecx) >>> 31) ^^^ 1 := by
    rw [U5.gpr, ite_eq_right (by decide), U4.gpr, U3.gpr, U2.gpr, U1.gpr,
      U2.other .ecx (by decide), U1.other .ecx (by decide)]
  rw [V, ex, VG.Proof.Rsa.zero_test32, BitVec.toNat_ofNat]
  change (decide (u.gpr .ecx = (0 : BitVec 32))).toNat % 2 ^ 32 = _
  by_cases he : u.gpr .ecx = 0
  · simp [he, e.mp he]
  · have ne := fun p => he (e.mpr p)
    rw [decide_eq_false he, ite_eq_right ne]
    rfl

end VG.Proof.Rsa.X86.KeyRt
