module

import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.CallOf
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env
public import VerifiedGarbage.Spec.Rsa

/-!
# `vg_rsa_keygen_key` on PPC64LE: the inverse and the loads as values

`invOfE`: `invOf a m k` (the batched inverse, through `InvLaw`, at the
width `n` that `k` sets: `nP_width`, `nTwo_width`, `nW_width`): array 1
holds `gcd(a, m)` and array 3 an `x < m` with `m ∣ x a - gcd(a, m)`, for an
odd `m > 1` and `a`, `m < 2^(32 n)`. `loadE`: `load j` reads bytes into a zero array.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs copy sub3 aM aNM aZero aT1 aT3 aT4 sOdd sB sC)
open VG.Impl.Rsa.PPC64LE.CrtValues (load)
open VG.Impl.RsaKeyGen.PPC64LE.Key (nArr aDv aOne invOf invCall)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa.PPC64LE (InvLaw invBatchArrs invBatchRegs)

/-- The arrays `invOf` writes. -/
abbrev invOfArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aM, aNM, aT1, VG.Impl.Rsa.PPC64LE.Keys.aT2, aT3, aT4]

section
variable {s : State} {B : Addr} {Z w : Nat} {V F : Nat → Nat}

theorem invOf_eq (a m : Nat) (k : List Instr) : invOf a m k =
    .seq (copy aM m) (.seq (copy 0 a) (.seq (.block k) invCall)) := rfl

/-- The address of `aNM`'s first doubleword, where `invCall` keeps the link register. -/
abbrev lrAt (B : Addr) (w : Nat) : Addr := off B (arr w aNM)

/-- Memory outside the arrays `js` at `aNM`'s first doubleword. -/
theorem keep_lrAt {js : List Nat} {m m' : Mem} (hk : KeyWorkspace.Keep B w js [] m m') (hj : aNM ∉ js)
    (fit : arr w aNM + S w ≤ 2 ^ 64) : m'.readW (lrAt B w) 64 = m.readW (lrAt B w) 64 := by
  have hS : 8 ≤ S w := by simp only [S]; omega_using []
  refine (Mem.readW_congr fun i hi => (hk _ fun r hr => ?_).symm).symm
  simp only [KeyWorkspace.ranges, List.map_nil, List.append_nil, List.mem_map] at hr
  obtain ⟨k, hk', rfl⟩ := hr
  have hne : k ≠ aNM := fun e => hj (e ▸ hk')
  have := VG.Proof.Rsa.KeyWorkspace.arr_disj (w := w) hne
  rw [ofs_off B (by omega_using [fit, hi, hS])]
  dsimp only; omega_using [this, hi, hS]

/-- `invCall`: the inverse (`InvLaw.inverse_ok`) as a call of
`vg_rsa_inv_batch`, the link register kept in `aNM` around it, which it
writes too. -/
theorem invCall_ok [InvLaw] (h : Ws s B Z w nArr) (hw : 10 ≤ w) {n : Nat}
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w 0 = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w 8 = m)
    (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa invCall s fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w (aNM :: invBatchArrs) [] s.mem t.mem ∧ Keep invBatchRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have fit := fit_of h aNM (by decide)
  have hS : 8 ≤ S w := by simp only [S]; omega_using []
  have hZ : arr w aNM + 8 ≤ Z := by
    have e1 := VG.Proof.Rsa.KeyWorkspace.arr_end (w := w) (show aNM < nArr by decide)
    have e2 := h.fits; omega_using [e1, e2, hS]
  -- The link register into `aNM`, `n` into `r10`.
  have b1 : WP isa (.block (.mflr .r0 :: VG.Impl.Rsa.PPC64LE.Keys.ptr .r5 aNM ++
      [.store .d .r0 .r5 0, .addi .r10 .r11 0])) s fun u =>
      u.mem = s.mem.writeW (lrAt B w) s.lr ∧ u.gpr .r10 = s.gpr .r11 ∧ Keep [.r0, .r5, .r10] s u := by
    refine WP.block_cons_iff.mpr ⟨_, exec_mflr, ?_⟩
    have h0 : Ws (s.write .r0 s.lr) B Z w nArr := h.of_keep (Keep.write s .r0 s.lr)
    refine ptr_ok h0 (by decide) (by decide) (by decide) (by decide) ?_
    have hst : InRegions ((s.write .r0 s.lr).write .r5 (off B (arr w aNM))).wr
        (((s.write .r0 s.lr).write .r5 (off B (arr w aNM))).gpr .r5 + BitVec.ofNat 64 0) 8 := by
      simp only [gpr_write, ite_true, wr_write, BitVec.add_zero]
      exact h.scr.st (d := arr w aNM) hZ
    prun [exec_store_d (show Reg.r5 ≠ .r0 by decide) (by decide) hst]
    refine ⟨BitVec.add_zero _, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2]
  simp only [invCall, seqs]
  refine WP.seq (WP.mono b1 fun u ⟨um, u10, uk⟩ => ?_)
  have hu : Ws u B Z w nArr := h.of_keep uk
  have O1 : KeyWorkspace.Keep B w [aNM] [] s.mem u.mem := by
    rw [um]
    refine KeyWorkspace.Keep.of_arr (o := aNM) (d := 0) (n := 8) ?_ hS List.mem_cons_self
    rw [Nat.add_zero]; exact writeW_outside _ _ _ (by omega_using [fit, hS])
  have v0 : num u.mem B w 0 = x := by
    rw [O1.num (by decide) (by decide) (fit_of h 0 (by decide))]; exact hx
  have v8 : num u.mem B w 8 = m := by
    rw [O1.num (by decide) (by decide) (fit_of h 8 (by decide))]; exact hm
  -- The call: `n` back into `r11`, then the inverse.
  have he : Ws (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)) B Z w nArr :=
    ⟨hu.scr.congr rfl, hu.fits, hu.wpos, hu.wle,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r29,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r30,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r31⟩
  have e11 : (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)).gpr .r11 = BitVec.ofNat 64 n := by
    simp only [gpr_write, ite_true, BitVec.add_zero]; rw [State.callEntry_gpr _ (by decide), u10, h11]
  refine WP.seq (WP.mono (WP.callOf (s := u) (Q := fun t => Ws t B Z w nArr ∧
      KeyWorkspace.Keep B w invBatchArrs [] u.mem t.mem ∧
      Keep invBatchRegs (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)) t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m)) ?_) fun t ht => ?_)
  · rw [VG.Impl.Rsa.PPC64LE.InvBatch.inverseFn]
    refine WP.seq (WP.block_cons_iff.mpr ⟨_, exec_addi (d := .r11) (n := .r10) (imm := 0) (by decide) (by decide),
      WP.block_nil ?_⟩)
    refine WP.mono (InvLaw.inverse_ok he (by decide) nArr_le hw e11 hn1 hnw hfit v0 hxn v8 hmn hodd)
      fun t ⟨ht, kt, rt, vt⟩ => ⟨?_, ht, kt, rt, vt⟩
    rw [rt.lr]; rfl
  obtain ⟨ht, kt, rt, vt⟩ := ht
  -- The link register back from `aNM`.
  have hl : t.mem.readW (lrAt B w) 64 = s.lr := by
    rw [keep_lrAt kt (by decide) fit, um, Mem.readW_writeW_self64]
  refine ptr_ok ht (by decide) (by decide) (by decide) (by decide) ?_
  have hrd : InRegions ((t.write .r5 (off B (arr w aNM))).rd ++ (t.write .r5 (off B (arr w aNM))).wr)
      ((t.write .r5 (off B (arr w aNM))).gpr .r5 + BitVec.ofNat 64 0) 8 := by
    simp only [gpr_write, ite_true, rd_write, wr_write, BitVec.add_zero]
    exact ht.scr.ld (d := arr w aNM) hZ
  prun [exec_load_d (show Reg.r5 ≠ .r0 by decide) (by decide) hrd, exec_mtlr]
  have hl' : t.mem.readW (off B (arr w aNM)) 64 = s.lr := hl
  have hlink : ∀ r, r ∉ invBatchRegs → r ∉ linkRegs := fun r hr h' => hr (by
    simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl | rfl <;> decide)
  refine ⟨⟨ht.scr.congr rfl, ht.fits, ht.wpos, ht.wle, by simp [gpr_write, ht.r29], by simp [gpr_write, ht.r30],
      by simp [gpr_write, ht.r31]⟩, O1.join kt (by simp) (by simp) (by simp) (by simp),
    ⟨fun r hr => ?_, ?_, ?_, ?_, hl'⟩, vt⟩
  · have h0 : r ≠ .r0 := fun e => hr (by rw [e]; decide)
    have h5 : r ≠ .r5 := fun e => hr (by rw [e]; decide)
    have h11 : r ≠ .r11 := fun e => hr (by rw [e]; decide)
    have h10 : r ∉ [Reg.r0, Reg.r5, Reg.r10] := fun e => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at e
      rcases e with rfl | rfl | rfl <;> decide)
    show ((t.write .r5 _).write .r0 _).gpr r = s.gpr r
    simp only [gpr_write, h0, h5, ite_false]
    rw [rt.gpr r hr]
    simp only [gpr_write, h11, ite_false]
    rw [State.callEntry_gpr _ (hlink r hr), uk.gpr r h10]
  · show t.rd = s.rd; rw [rt.rd]; simp only [rd_write, State.callEntry_rd]; exact uk.rd
  · show t.wr = s.wr; rw [rt.wr]; simp only [wr_write, State.callEntry_wr]; exact uk.wr
  · show t.sp = s.sp; rw [rt.sp]; simp only [sp_write, State.callEntry_sp]; exact uk.sp

/-- What a width block does: `r11 := n`, and nothing else. -/
def Width (k : List Instr) (s : State) (n : Nat) : Prop :=
  ∀ u : State, Keep opsRegs s u →
    WP isa (.block k) u fun u' => (u'.gpr .r11 = BitVec.ofNat 64 n ∧ u'.mem = u.mem) ∧ Keep [.r11] u u'

/-- `invOf a m k`, at the width `n` that `k` sets. -/
theorem invOfE [InvLaw] (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) (hw : 10 ≤ w) {a m : Nat}
    (ha : a < nArr := by decide) (hm : m < nArr := by decide) (hma : a ∉ invOfArrs := by decide)
    (hmm : m ≠ aM := by decide) {k : List Instr} {n : Nat} (hk : Width k s n) (hn1 : 1 ≤ n)
    (hnw : n ≤ w) (hfit : n + n % 2 ≤ w) (han : V a < 2 ^ (32 * n)) (hmn : V m < 2 ^ (32 * n))
    (odd : V m % 2 = 1) (gt : 1 < V m) :
    WP isa (invOf a m k) s fun u => Ws u B Z w nArr ∧
      (∃ V', KS u.mem B w V' F ∧ (∀ j < nArr, j ∉ invOfArrs → V' j = V j) ∧
        V' 1 = Nat.gcd (V a) (V m) ∧ ((V m : Nat) : Int) ∣ (V' 3 : Int) * V a - V' 1 ∧ V' 3 < V m) ∧
      KK B w s.mem u.mem ∧ Keep bodyRegs s u := by
  have ham : a ≠ aM := fun e => hma (by rw [e]; decide)
  have ha0 : a ≠ 0 := fun e => hma (by rw [e]; decide)
  rw [invOf_eq]
  refine WP.seq (WP.mono (copyE h ks (o := aM) (a := m) (by decide) hm (Ne.symm hmm)) fun t1 ⟨h1, k1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (copyE h1 k1 (o := 0) (a := a) (by decide) ha (Ne.symm ha0)) fun t2 ⟨h2, k2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (hk t2 (r1.trans' r2)) fun t3 ⟨⟨e11, m3⟩, r3⟩ => ?_)
  have h3 : Ws t3 B Z w nArr := h2.of_keep r3
  have k3 : KS t3.mem B w (upd (upd V aM (V m)) 0 (upd V aM (V m) a)) F := m3 ▸ k2
  -- The values before the inverse.
  have ham' : a ≠ 8 := ham
  have v0 : num t3.mem B w 0 = V a := by rw [k3.arrs 0 (by decide)]; simp [upd, aM, ham']
  have vM : num t3.mem B w aM = V m := by rw [k3.arrs aM (by decide)]; simp [upd, aM]
  have vO : ∀ j < nArr, j ∉ invOfArrs → num t3.mem B w j = V j := by
    intro j hj hn
    simp only [invOfArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n0, -, -, -, -, -, -, -, nM, -⟩ := hn
    rw [k3.arrs j hj]; simp [upd, n0, nM]
  refine WP.mono (invCall_ok h3 hw e11 hn1 hnw hfit v0 han vM hmn odd) fun u ⟨hu, ku, kr, v⟩ => ⟨hu, ?_, ?_, ?_⟩
  · obtain ⟨g, dv, lt⟩ := v gt
    refine ⟨fun j => num u.mem B w j, ?_, fun j hj hn => ?_, g, dv, lt⟩
    · refine k3.step ku (fit_of h3) (V' := fun j => num u.mem B w j) (fun j hj hn => ?_) (fun j _ => rfl)
        (fun _ _ _ => rfl) (fun d hd => by simp at hd) (fun hj => absurd hj (by decide))
      rw [← k3.arrs j hj]
      exact ku.num (fun x hx e => hn (e ▸ hx)) (by decide) (fit_of h3 j hj)
    · have sub : ∀ x ∈ aNM :: invBatchArrs, x ∈ invOfArrs := by decide
      have hn' : j ∉ aNM :: invBatchArrs := fun hm' => hn (sub j hm')
      show num u.mem B w j = V j
      rw [ku.num (fun x hx e => hn' (by rw [← e]; exact hx)) (by decide) (fit_of h3 j hj), vO j hj hn]
  · exact ((f1.trans f2).trans (m3 ▸ KK.refl B w t2.mem)).trans (KK.of ku (by decide) (by decide))
  · exact (((r1.trans' r2).mono.trans' r3.mono).trans' kr.mono)

/-- `nP`: the primes' width, `p_len / 4` digits, for `p_len` in `r22`. -/
theorem nP_width {L : Nat} (h22 : s.gpr .r22 = BitVec.ofNat 64 L) (hL : L < 2 ^ 64) :
    Width VG.Impl.RsaKeyGen.PPC64LE.Key.nP s (L / 4) := fun u k => by
  have e : u.gpr .r22 = BitVec.ofNat 64 L := (k.gpr .r22 (by decide)).trans h22
  unfold VG.Impl.RsaKeyGen.PPC64LE.Key.nP
  refine WP.keep _ ?_ (by decide)
  have v : BitVec.ofNat 64 L >>> 2 = BitVec.ofNat 64 (L / 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt (by omega_arith)]
  prun [e, v]

/-- `nTwo`: two digits. -/
theorem nTwo_width : Width VG.Impl.RsaKeyGen.PPC64LE.Key.nTwo s 2 := fun u _ => by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Key.nTwo
  refine WP.keep _ ?_ (by decide)
  prun

/-- `nW`: `w` digits, for `w` in `r29`. -/
theorem nW_width (h : Ws s B Z w nArr) : Width VG.Impl.RsaKeyGen.PPC64LE.Key.nW s w := fun u k => by
  have e : u.gpr .r29 = BitVec.ofNat 64 w := (k.gpr .r29 (by decide)).trans h.r29
  unfold VG.Impl.RsaKeyGen.PPC64LE.Key.nW
  refine WP.keep _ ?_ (by decide)
  prun [e, BitVec.add_zero]

/-- `load j` from `L` bytes at `P`, readable and apart from the working space, into a zero array. -/
theorem loadE (h : Ws s B Z w nArr) (ks : KS s.mem B w V F) {j : Nat} (hj : j < nArr := by decide)
    (hjdv : j ≠ aDv := by decide) {P : Addr} {L : Nat} (h6 : s.gpr .r6 = P)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hLw : L ≤ 4 * w)
    (hP : ∀ i < L, InRegions (s.rd ++ s.wr) (off P i) 1) (hsep : ∀ i < L, ∀ x, ofs B x < Z → off P i ≠ x)
    (hz : V j = 0) :
    WP isa (load j) s fun t => Ws t B Z w nArr ∧
      KS t.mem B w (upd V j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P L))) F ∧ KK B w s.mem t.mem ∧
      Keep opsRegs s t := by
  have hv : val32 s.mem B (arr w j) w = 0 := by rw [← hz, ← ks.arrs j hj]
  refine WP.mono (load_ok h hj nArr_le h6 h8 hL hLw hP hsep
    (fun p hp => by rw [← off_add]; exact byte_zero_of_val32 hv hp)) fun t ⟨ht, kt, v, kr, _⟩ =>
      ⟨ht, ?_, KK.of kt (arr_mem hj) (by simp), kr.mono⟩
  refine ks.step kt (fit_of h) (fun i hi hn => ?_) (fun i hi => ?_) (fun _ _ _ => rfl)
    (fun d hd => by simp at hd) (fun hd => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, upd_self, v]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    exact absurd hd.symm hjdv

end

end VG.Proof.RsaKeyGen.PPC64LE.Key
