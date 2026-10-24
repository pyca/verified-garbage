module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.KeyArrays
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The checks of an RSA key on PPC64LE: the arrays set up

`setup_ok`: `w = ⌈n_len / 4⌉` (`n_len` in `r15`) and the stride into `r29`
and `r30`, and every array zeroed. `LdS`: what the reading of the numbers
keeps: `KBase`, the working space, every array's value (`A`) and its extra
digit 0. `eArr_ok`, `ldStep_ok`: `e` from `r24`, and a number from its bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck (setup eArr loadR nArr aE)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

/-- `w = ⌈K / 4⌉`. -/
abbrev kw (K : Nat) : Nat := (K + 3) / 4

theorem KPre.ws {s0 : State} {B : Addr} {Z K oS na : Nat} (h : KPre s0 B Z K oS na) :
    arr (kw K) nArr ≤ Z ∧ 16 ≤ kw K ∧ kw K ≤ 256 ∧ K ≤ 4 * kw K := by
  have := h.zk; have := h.k64; have := h.k1024
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr, kw]
  omega

theorem ofNat_digits24 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 24 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (24 * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S]
  rw [Nat.mod_eq_of_lt (show 24 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 24 * (w + 2) < 2 ^ 64 by omega)]
  omega

/-- `setup`: `w` and the stride, and every digit of the arrays 0. -/
theorem setup_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (h : KBase B Z s0 s)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 K) :
    WP isa setup s fun t => KBase B Z s0 t ∧ Ws t B Z (kw K) nArr ∧
      (∀ j < nArr, ∀ i < kw K + 2, w32 t.mem B (arr (kw K) j + 4 * i) = 0) ∧
      Keep (.r29 :: .r30 :: opRegs) s t := by
  obtain ⟨fits, hw16, hw, -⟩ := hp.ws
  have nw := hp.nowrap
  have hs : Scr s B Z := Scr.of_mem (by rw [h.wr]; exact hp.wr) nw
  have hkv : (BitVec.ofNat 64 K).toNat ≤ 1024 := by rw [BitVec.toNat_ofNat]; have := hp.k1024; omega
  rw [setup, WP.seq_iff]
  have hb : WP isa (.block ([.addi .r29 .r15 3, .lsr .d .r29 .r29 2] ++
      VG.Impl.Rsa.PPC64LE.Keys.stride ++ [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])) s fun u =>
        (u.gpr .r29 = BitVec.ofNat 64 (kw K) ∧ u.gpr .r30 = BitVec.ofNat 64 (S (kw K)) ∧
          u.gpr .r8 = BitVec.ofNat 64 (nArr * (kw K + 2)) ∧ u.mem = s.mem) ∧ Keep [.r8, .r29, .r30] s u := by
    refine WP.keep _ ?_ (by decide)
    have e3 := CrtValues.ofNat_add3_shr2 _ hkv
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.k1024; omega)] at e3
    prun [VG.Impl.Rsa.PPC64LE.Keys.stride, h15, e3, CrtValues.ofNat_stride, ofNat_digits24 _ hw, nArr]
  refine WP.mono hb fun u ⟨⟨u29, u30, u8, um⟩, ku⟩ => ?_
  have hu : Ws u B Z (kw K) nArr :=
    ⟨hs.congr ku.wr, fits, by omega, by omega, u29, u30, (ku.gpr _ (by decide)).trans h.r31⟩
  have hn : 160 + 4 * (nArr * (kw K + 2)) ≤ Z := by
    simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr] at fits ⊢; omega
  refine WP.mono (zeroArrays_ok hu u8 (by simp only [nArr]; omega) (by simp only [nArr]; omega) hn)
    fun t ⟨ht, z, out, kt⟩ => ⟨?_, ht, fun j hj i hi => ?_, (ku.trans kt).mono⟩
  · exact h.of_outside (by rw [← um]; exact out) hn (ku.trans kt)
  · have hb : j * (kw K + 2) + i < nArr * (kw K + 2) := by
      have := Nat.mul_le_mul_right (kw K + 2) (show j + 1 ≤ nArr by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have := z (j * (kw K + 2) + i) hb
    rw [show 160 + 4 * (j * (kw K + 2) + i) = arr (kw K) j + 4 * i by
      simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
    exact this

/-- What the reading of the numbers keeps. -/
structure LdS (B : Addr) (Z K : Nat) (s0 : State) (A : Nat → Nat) (t : State) : Prop where
  base : KBase B Z s0 t
  ws : Ws t B Z (kw K) nArr
  arrs : Arrs t.mem B (kw K) A (List.range nArr)
  top : ∀ j < nArr, w32 t.mem B (arr (kw K) j + 4 * kw K) = 0

/-- `setup`'s arrays: every one 0. -/
theorem LdS.of_setup {B : Addr} {Z K : Nat} {s0 t : State} (b : KBase B Z s0 t) (w : Ws t B Z (kw K) nArr)
    (z : ∀ j < nArr, ∀ i < kw K + 2, w32 t.mem B (arr (kw K) j + 4 * i) = 0) :
    LdS B Z K s0 (fun _ => 0) t :=
  ⟨b, w, fun j hj => CrtValues.val32_of_zero fun i hi => z j (List.mem_range.mp hj) i (by omega),
    fun j hj => z j hj _ (by omega)⟩

/-- `loadR rP rL j`: array `j`, 0, := the `L` bytes at `P`. -/
theorem ldStep_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t) {j : Nat}
    (hj : j < nArr) (hA : A j = 0) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL6 : rL ≠ .r6)
    {P : Addr} {L : Nat} (hP : t.gpr rP = P) (hL : t.gpr rL = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * kw K) (hrd : (⟨P, L⟩ : Region) ∈ s0.rd) (hd : (⟨P, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hPw : P.toNat + L ≤ 2 ^ 64) :
    WP isa (seqs (loadR rP rL j)) t fun u =>
      LdS B Z K s0 (upd A j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L))) u ∧ Keep [.r0, .r5, .r6, .r8] t u := by
  have h := hI.ws
  have fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  rw [loadR, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (CrtValues.mv2_ok (s := t) (d₁ := .r6) (d₂ := .r8) hrP hrL hrL6 (by decide))
    fun u ⟨⟨u6, u8, um⟩, ku⟩ => ?_
  rw [show seqs [VG.Impl.Rsa.PPC64LE.CrtValues.load j] = VG.Impl.Rsa.PPC64LE.CrtValues.load j from rfl]
  have hu := h.of_keep ku
  have b1 := hI.base.of_regs ku um
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have hz : val32 u.mem B (arr (kw K) j) (kw K) = 0 := by
    rw [um]; exact (hI.arrs.get (List.mem_range.mpr hj)).trans hA
  refine WP.mono (load_ok hu hj (by decide) (u6.trans hP) (u8.trans hL) hL1 hLw
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [ku.rd, hI.base.rd]; exact hrd), hc i hi⟩)
    (fun i hi x hx e => by have := CrtValues.past_of_disjoint hd (hc i hi); rw [e] at this; omega)
    (fun p hp => by rw [← off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 hz hp))
    fun v ⟨hv, k, val, kv, o⟩ => ⟨⟨b1.of_keep k hI.ws.nowrap (by simp; exact h.arr_fit hj) (by simp)
      h.hdr_le kv, hv, fun i hi => ?_, fun i hi => ?_⟩, (ku.trans kv).mono⟩
  · by_cases e : i = j
    · subst e
      rw [upd_self, val]
      congr 1
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun c hc' => ?_
      rw [um]
      exact hI.base.frame _ (CrtValues.past_of_disjoint hd (hc c (List.mem_range.mp hc')))
    · rw [upd_ne _ _ e, CrtValues.num_out o (Ne.symm e) (fit _ (List.mem_range.mp hi)), um]
      exact hI.arrs.get hi
  · rw [CrtValues.top_out o (fit _ hi), um]; exact hI.top i hi

theorem shl_shr31 {E : Nat} (hE : E < 2 ^ 33) : (BitVec.ofNat 64 E <<< 31) >>> 31 = BitVec.ofNat 64 E := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show E * 2 ^ 31 < 2 ^ 64 by omega), Nat.mul_div_cancel _ (by decide)]

/-- A number whose two low digits are written and whose others are kept from 0. -/
theorem val32_two {m m' : Mem} {B : Addr} {d w : Nat} (hw : 2 ≤ w) (hz : val32 m B d w = 0)
    (o : ∀ i, 2 ≤ i → i < w → w32 m' B (d + 4 * i) = w32 m B (d + 4 * i)) :
    val32 m' B d w = w32 m' B d + 2 ^ 32 * w32 m' B (d + 4) := by
  obtain ⟨n, rfl⟩ : ∃ n, w = 2 + n := ⟨w - 2, by omega⟩
  have e := val32_append m B d 2 n
  have e' := val32_append m' B d 2 n
  rw [hz] at e
  have rest : val32 m B (d + 4 * 2) n = 0 := by
    have : 0 ≤ val32 m B d 2 := Nat.zero_le _
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * 2) n) with h | h
    · exact h
    · have : 2 ^ (32 * 2) ≤ 2 ^ (32 * 2) * val32 m B (d + 4 * 2) n := Nat.le_mul_of_pos_right _ h
      omega
  have rest' : val32 m' B (d + 4 * 2) n = 0 := by
    rw [← rest]
    refine val32_congr fun i hi => ?_
    rw [show d + 4 * 2 + 4 * i = d + 4 * (i + 2) by omega]
    exact o (i + 2) (by omega) (by omega)
  rw [e', rest', Nat.mul_zero, Nat.add_zero]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

/-- `eArr`: `e`, below `2^33`, from `r24 = e · 2^31` into its array, which is 0. -/
theorem eArr_ok {B : Addr} {Z K : Nat} {s0 t : State} {A : Nat → Nat} (hI : LdS B Z K s0 A t)
    (hw2 : 2 ≤ kw K) (hA : A aE = 0) {E : Nat} (h24 : t.gpr .r24 = BitVec.ofNat 64 E <<< 31)
    (hE : E < 2 ^ 33) :
    WP isa (.block eArr) t fun u => LdS B Z K s0 (upd A aE E) u ∧ Keep [.r0, .r5] t u := by
  have h := hI.ws
  have fit : ∀ i < nArr, arr (kw K) i + S (kw K) ≤ 2 ^ 64 := fun i hi => h.fit64 hi
  have fE := h.arr_fit (j := aE) (by decide)
  have fE' := fit aE (by decide)
  have hS : S (kw K) = 4 * (kw K + 2) := rfl
  have hs := h.scr
  unfold eArr
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show aE < 2 ^ 15 by decide) ?_
  let d := arr (kw K) aE
  let lo : BitVec 32 := (BitVec.ofNat 64 E).setWidth 32
  let hi : BitVec 32 := (BitVec.ofNat 64 E >>> 32).setWidth 32
  have hb : WP isa (.block [.lsr .d .r0 .r24 31, .store .w .r0 .r5 0, .lsr .d .r0 .r0 32, .store .w .r0 .r5 4])
      (t.write .r5 (off B d)) fun u =>
        u.mem = (t.mem.writeW (off B d) lo).writeW (off B (d + 4)) hi ∧ Keep [.r0, .r5] t u := by
    refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = (t.mem.writeW (off B d) lo).writeW (off B (d + 4)) hi)
      ?_ (by decide)) fun u ⟨m, k⟩ => ⟨m, ((Keep.write _ _ _).trans k).mono⟩
    prun [h24, shl_shr31 hE, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 4 < 2 ^ 15 by decide),
      hs.st (d := d) (n := 4) (by omega), hs.st (d := d + 4) (n := 4) (by omega), off_add]
    rfl
  refine WP.mono hb fun u ⟨um, ku⟩ => ?_
  have o1 : Outside B d 4 t.mem (t.mem.writeW (off B d) lo) := writeW32_outside _ _ _ (by omega)
  have o2 : Outside B (d + 4) 4 (t.mem.writeW (off B d) lo) u.mem := by
    rw [um]; exact writeW32_outside _ _ _ (by omega)
  have o : Outside B d 8 t.mem u.mem := (o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))
  have k : KeyWorkspace.Keep B (kw K) [aE] [] t.mem u.mem :=
    KeyWorkspace.Keep.of_arr (d := 0) (by simpa using o) (by omega) (by simp)
  refine ⟨⟨hI.base.of_keep k hI.ws.nowrap (by simp; exact fE) (by simp) h.hdr_le ku, h.of_keep ku,
    fun j hj => ?_, fun j hj => ?_⟩, ku⟩
  · by_cases e : j = aE
    · subst e
      rw [upd_self]
      have hz : val32 t.mem B d (kw K) = 0 := (hI.arrs.get (List.mem_range.mpr (by decide))).trans hA
      change val32 u.mem B d (kw K) = E
      rw [val32_two hw2 hz fun i hi hi' => o.w32 (by omega) (by omega)]
      have w0 : w32 u.mem B d = lo.toNat := by
        rw [o2.w32 (by omega) (by omega)]; exact w32_write_self _ _ _ _
      have w1 : w32 u.mem B (d + 4) = hi.toNat := by rw [um]; exact w32_write_self _ _ _ _
      rw [w0, w1]
      simp only [lo, hi, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show E / 2 ^ 32 < 2 ^ 32 by omega)]
      omega
    · rw [upd_ne _ _ e]
      have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := kw K) e
      have fj := fit j (List.mem_range.mp hj)
      rw [show num u.mem B (kw K) j = num t.mem B (kw K) j from o.val32 (by omega) (by omega)]
      exact hI.arrs.get hj
  · have fj := fit j hj
    by_cases e : j = aE
    · subst e; rw [o.w32 (by omega) (by omega)]; exact hI.top _ hj
    · have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := kw K) e
      rw [o.w32 (by omega) (by omega)]; exact hI.top _ hj

end VG.Proof.Rsa.PPC64LE.KeyCheck
