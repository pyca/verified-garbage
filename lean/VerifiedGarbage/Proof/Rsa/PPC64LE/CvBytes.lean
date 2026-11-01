module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_crt_values` on PPC64LE: the bytes in and out

`load_ok`: `load j` reads `L` bytes, most significant first, into array
`j`, which is zero, so that it holds their number.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop)
open VG.Impl.Rsa.PPC64LE.CrtValues (load storeBytes zeroBytes)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- `load j`: the `L` bytes at `P` (outside the working space), most
significant first, into array `j`, whose first `4 w` bytes are zero. -/
theorem load_ok {s : State} {B P : Addr} {Z w N j L : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (h6 : s.gpr .r6 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw : L ≤ 4 * w) (hP : ∀ i < L, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off P i ≠ x)
    (hz : ∀ p < 4 * w, s.mem (off B (arr w j + p)) = 0) :
    WP isa (load j) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P L) ∧ Keep [.r0, .r5, .r6, .r8] s t ∧
      Outside B (arr w j) (4 * w) s.mem t.mem := by
  have fit := h.arr_fit hj
  have hnw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [load, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have hb : WP isa (.block [.add .r5 .r5 .r8, .subi .r5 .r5 1]) (s.write .r5 (off B (arr w j))) fun u =>
      (u.gpr .r5 = off B (arr w j + L - 1) ∧ u.gpr .r6 = off P 0 ∧ u.gpr .r8 = BitVec.ofNat 64 L ∧
        u.mem = s.mem) ∧ Keep [.r5] (s.write .r5 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h6, h8, off_add]
    refine ⟨off_sub1 _ (by omega_arith), by simp [off]⟩
  refine WP.mono hb fun s₃ ⟨⟨j5, j6, j8, jm⟩, k₃⟩ => ?_
  have k₀ : Keep [.r5] s s₃ := ((Keep.write _ _ _).trans k₃).mono
  have hs₃ := h.scr.congr k₀.wr
  -- The bytes stored so far.
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (arr w j + L - 1 - i) ∧ t.gpr .r6 = off P i ∧
      Outside B (arr w j) (4 * w) s.mem t.mem ∧
      (∀ c < i, t.mem (off B (arr w j + (L - 1 - c))) = s.mem (off P c)) ∧
      (∀ p, L ≤ p → p < 4 * w → t.mem (off B (arr w j + p)) = 0) ∧
      Keep [.r0, .r5, .r6, .r8] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r6 0, .stb .r0 .r5 0, .addi .r6 .r6 1,
      .subi .r5 .r5 1] ++ ([.subi .r8 .r8 1] : List Instr))) (cnt := .r8) (N := L) (by omega_arith)
    (by omega_arith) Inv (fun i hi t ⟨t5, t6, tout, tb, tz, tk⟩ _ => ?_)
    ⟨by rw [j5]; rfl, j6, by rw [jm]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      fun p _ hp => by rw [jm]; exact hz p hp, k₀.mono⟩ j8)
    fun t ⟨_, _, tout, tb, tz, tk⟩ => ⟨h.of_keep tk, ?_, ?_, tk, tout⟩
  · have hst : WP isa (.block [.lbz .r0 .r6 0, .stb .r0 .r5 0, .addi .r6 .r6 1, .subi .r5 .r5 1,
        .subi .r8 .r8 1]) t fun t' => t' = ((({ (t.write .r0 ((t.mem.read (off P i) 1).setWidth 64)) with
          mem := t.mem.write (off B (arr w j + L - 1 - i)) 1
            (((t.mem.read (off P i) 1).setWidth 64).setWidth 8) } : State).write .r6 (off P (i + 1))).write .r5
              (off B (arr w j + L - 1 - i) - BitVec.ofNat 64 1)).write .r8 (t.gpr .r8 - BitVec.ofNat 64 1) := by
      prun [t5, t6, exec_lbz' (show Reg.r6 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        (by rw [tk.rd, tk.wr]; exact hP i (by omega_arith) : InRegions (t.rd ++ t.wr) (off P i) 1),
        (h.scr.congr tk.wr).st (d := arr w j + L - 1 - i) (n := 1) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have ha : arr w j + L - 1 - i = arr w j + (L - 1 - i) := by omega_arith
    have hw1 := write1_outside t.mem B (d := arr w j + L - 1 - i)
      (((t.mem.read (off P i) 1).setWidth 64).setWidth 8) (by omega_arith)
    have hPi : t.mem (off P i) = s.mem (off P i) := by
      refine tout _ (Or.inr ?_)
      have := (off P i - B).isLt
      by_contra hc
      exact hsep i (by omega) (off P i) (by simp only [ofs] at hc ⊢; omega) rfl
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_, ?_⟩, by gsimp⟩
    · have h160 : 160 ≤ arr w j := Nat.le_add_right _ _
      gsimp; rw [off_sub1 (a := arr w j + L - 1 - i) _ (by omega_arith),
        show arr w j + L - 1 - i - 1 = arr w j + L - 1 - (i + 1) by omega_arith]
    · gsimp; exact tout.trans (hw1.mono (o' := arr w j) (n' := 4 * w) (by omega_arith) (by omega_arith))
    · intro c hc
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
      · rw [hw1 _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith)]; exact tb c hc
      · rw [← ha, write1_self, read_one', hPi]
    · intro p hp hp'
      gsimp
      rw [hw1 _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith)]; exact tz p hp hp'
    · exact tk.trans' (((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _))).mono)
  · exact KeyWorkspace.Keep.of_arr (d := 0) (by simpa using tout) (by omega_arith) (by simp)
  · change val32 _ _ _ _ = _
    rw [← val32_off, val32_zero_extension t.mem (off B (arr w j)) (k := L) (by omega_arith) fun p hp hp' => by
        rw [off_add]; exact tz p hp (by omega_arith),
      reversed_read s.mem t.mem P (off B (arr w j)) L fun c hc => by
        rw [off_add, show arr w j + c = arr w j + (L - 1 - (L - 1 - c)) by omega_arith, tb _ (by omega_arith)]]

/-- A byte under a mask of all ones or zero. -/
theorem mask_byte (x : BitVec (8 * 1)) (b : Bool) :
    ((x.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) =
      if b then x else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, BitVec.sub_zero, BitVec.and_zero]; rfl
  · simp only [ite_true, show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have := x.isLt
    omega_arith

/-- `storeBytes j`: array `j`'s low `L` bytes to the `L` bytes at `O`, most
significant first, masked by `r9` (the mask of `b`). -/
theorem storeBytes_ok {s : State} {B O : Addr} {Z w N j L : Nat} (h : Ws s B Z w N) (hj : j < N)
    (hN : N ≤ 256) (h5 : s.gpr .r5 = O) (h8 : s.gpr .r8 = BitVec.ofNat 64 L) {b : Bool}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) (hL : 1 ≤ L)
    (hLw : L ≤ 4 * w) (hO : ∀ i < L, InRegions s.wr (off O i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off O i ≠ x) (hOw : O.toNat + L ≤ 2 ^ 64) :
    WP isa (storeBytes j) s fun t => Ws t B Z w N ∧
      (∀ c < L, t.mem (off O c) = if b then s.mem (off B (arr w j + (L - 1 - c))) else 0) ∧
      Outside O 0 L s.mem t.mem ∧ Keep [.r0, .r5, .r6, .r8] s t := by
  have fit := h.arr_fit hj
  have hnw := h.nowrap
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [storeBytes, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega_arith) ?_
  have hb : WP isa (.block [.add .r6 .r6 .r8, .subi .r6 .r6 1]) (s.write .r6 (off B (arr w j))) fun u =>
      (u.gpr .r6 = off B (arr w j + L - 1) ∧ u.gpr .r5 = off O 0 ∧ u.gpr .r8 = BitVec.ofNat 64 L ∧
        u.gpr .r9 = s.gpr .r9 ∧ u.mem = s.mem) ∧ Keep [.r6] (s.write .r6 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by decide)
    prun [h5, h8, off_add]
    refine ⟨off_sub1 _ (by have : 160 ≤ arr w j := Nat.le_add_right _ _; omega_arith), by simp [off]⟩
  refine WP.mono hb fun s₃ ⟨⟨j6, j5, j8, j9, jm⟩, k₃⟩ => ?_
  have k₀ : Keep [.r6] s s₃ := ((Keep.write _ _ _).trans k₃).mono
  have h160 : 160 ≤ arr w j := Nat.le_add_right _ _
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r6 = off B (arr w j + L - 1 - i) ∧ t.gpr .r5 = off O i ∧
      Outside O 0 i s.mem t.mem ∧
      (∀ c < i, t.mem (off O c) = if b then s.mem (off B (arr w j + (L - 1 - c))) else 0) ∧
      Keep [.r0, .r5, .r6, .r8] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r6 0, .logic .and .r0 .r0 .r9, .stb .r0 .r5 0,
      .addi .r5 .r5 1, .subi .r6 .r6 1] ++ ([.subi .r8 .r8 1] : List Instr))) (cnt := .r8) (N := L)
    (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨t6, t5, tout, tb, tk⟩ _ => ?_)
    ⟨by rw [j6]; rfl, j5, by rw [jm]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₀.mono⟩ j8)
    fun t ⟨_, _, tout, tb, tk⟩ => ⟨h.of_keep tk, tb, tout, tk⟩
  have t9 : t.gpr .r9 = s.gpr .r9 := tk.gpr _ (by decide)
  have hst : WP isa (.block [.lbz .r0 .r6 0, .logic .and .r0 .r0 .r9, .stb .r0 .r5 0, .addi .r5 .r5 1,
      .subi .r6 .r6 1, .subi .r8 .r8 1]) t fun t' =>
        (t'.gpr .r6 = off B (arr w j + L - 1 - i) - BitVec.ofNat 64 1 ∧ t'.gpr .r5 = off O (i + 1) ∧
          t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off O i) 1 (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)) ∧
        Keep [.r0, .r5, .r6, .r8] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t6, t5, t9, h9, exec_lbz' (show Reg.r6 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_stb (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (h.scr.congr tk.wr).ld (d := arr w j + L - 1 - i) (n := 1) (by omega_arith),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1), mask_byte]
  refine WP.mono hst fun t' ⟨⟨l6, l5, l8, lm⟩, lk⟩ => ⟨⟨?_, l5, ?_, ?_, tk.trans' lk⟩, l8⟩
  · rw [l6, off_sub1 _ (by omega_arith), show arr w j + L - 1 - i - 1 = arr w j + L - 1 - (i + 1) by omega_arith]
  · have hw1 := write1_outside t.mem O (d := i) (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)
      (by omega_arith)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
  · have hw1 := write1_outside t.mem O (d := i) (if b then t.mem.read (off B (arr w j + L - 1 - i)) 1 else 0)
      (by omega_arith)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb c hc
    · rw [write1_self]
      -- The byte read is the array's, which no output byte overlaps.
      have ha : t.mem (off B (arr w j + L - 1 - c)) = s.mem (off B (arr w j + L - 1 - c)) := by
        refine tout _ (Or.inr ?_)
        by_contra hlt
        have hx : off O (ofs O (off B (arr w j + L - 1 - c))) = off B (arr w j + L - 1 - c) := by
          simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
        exact hsep _ (by omega_arith) _ (by rw [Mont.ofs_off0 B (by omega_arith)]; omega_arith) hx
      have r1 : ∀ (m : Mem) (a : Addr), m.read a 1 = m a := fun m a =>
        BitVec.eq_of_toNat_eq (by rw [read_toNat_succ]; simp [Mem.read])
      cases b
      · rfl
      · simp only [ite_true]
        rw [show arr w j + (L - 1 - c) = arr w j + L - 1 - c by omega_arith, ← ha, r1]

/-- `zeroBytes`: the `L` bytes at `O` := 0. -/
theorem zeroBytes_ok {s : State} {O : Addr} {L : Nat} (h5 : s.gpr .r5 = O)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hO : ∀ i < L, InRegions s.wr (off O i) 1) (hOw : O.toNat + L ≤ 2 ^ 64) :
    WP isa zeroBytes s fun t => (∀ c < L, t.mem (off O c) = 0) ∧ Outside O 0 L s.mem t.mem ∧
      Keep [.r0, .r5, .r8] s t := by
  rw [zeroBytes, WP.seq_iff]
  have hb : WP isa (.block [.li .r0 0]) s fun u =>
      (u.gpr .r0 = 0 ∧ u.gpr .r5 = off O 0 ∧ u.gpr .r8 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
        Keep [.r0] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [h5, h8]
    simp [off]
  refine WP.mono hb fun u ⟨⟨u0, u5, u8, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off O i ∧ t.gpr .r0 = 0 ∧ Outside O 0 i s.mem t.mem ∧ (∀ c < i, t.mem (off O c) = 0) ∧
      Keep [.r0, .r5, .r8] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r5 0, .addi .r5 .r5 1] ++
      ([.subi .r8 .r8 1] : List Instr))) (cnt := .r8) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t5, t0, tout, tz, tk⟩ _ => ?_)
    ⟨u5, u0, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), ku.mono⟩ u8)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, tk⟩
  have hst : WP isa (.block [.stb .r0 .r5 0, .addi .r5 .r5 1, .subi .r8 .r8 1]) t fun t' =>
      (t'.gpr .r5 = off O (i + 1) ∧ t'.gpr .r0 = 0 ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.write (off O i) 1 0) ∧ Keep [.r5, .r8] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [t5, t0, exec_stb (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (by rw [tk.wr]; exact hO i hi : InRegions t.wr (off O i) 1)]
    rfl
  refine WP.mono hst fun t' ⟨⟨l5, l0, l8, lm⟩, lk⟩ => ⟨⟨l5, l0, ?_, ?_, tk.trans' lk.mono⟩, l8⟩
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
  · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [Mont.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tz c hc
    · rw [write1_self]

/-- The `L` bytes at `O` reversed from array `j`'s low bytes: its number modulo
`256^L`, most significant first. -/
theorem bytes_of_store {m m' : Mem} {B O : Addr} {w j L : Nat} (hL : L ≤ 4 * w)
    (hb : ∀ c < L, m' (off O c) = m (off B (arr w j + (L - 1 - c)))) :
    Spec.Rsa.bytesAt m' O L = Spec.Rsa.i2osp (num m B w j % 256 ^ L) L := by
  have hr := reversed_read m' m O (off B (arr w j)) L fun c hc => by
    rw [off_add]
    have := hb (L - 1 - c) (by omega_arith)
    rw [show L - 1 - (L - 1 - c) = c by omega_arith] at this
    rw [← this]
  have e := read_toNat_add m (4 * w - L) L (off B (arr w j))
  rw [show 4 * w - L + L = 4 * w by omega_arith, read_eq_val32] at e
  have hlt := (m.read (off B (arr w j)) L).isLt
  have hval : num m B w j % 256 ^ L = (m.read (off B (arr w j)) L).toNat := by
    change val32 _ _ _ _ % _ = _
    rw [e, show (256 : Nat) ^ L = 2 ^ (8 * L) by rw [Nat.pow_mul], Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt]
  rw [hval, hr]
  have hl : (Spec.Rsa.bytesAt m' O L).length = L := by simp [Spec.Rsa.bytesAt]
  have e2 := i2osp_os2ip (Spec.Rsa.bytesAt m' O L)
  rw [hl] at e2
  exact e2.symm


/-- A number of `L` bytes is below `2^(8 L)`. -/
theorem os2ip_bytes_lt (m : Mem) (p : Addr) (L : Nat) : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p L) < 2 ^ (8 * L) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (Spec.Rsa.bytesAt m p L)
  rwa [show (Spec.Rsa.bytesAt m p L).length = L by simp [Spec.Rsa.bytesAt], show (256 : Nat) = 2 ^ 8 from rfl,
    ← Nat.pow_mul] at h

end VG.Proof.Rsa.PPC64LE.Keys
