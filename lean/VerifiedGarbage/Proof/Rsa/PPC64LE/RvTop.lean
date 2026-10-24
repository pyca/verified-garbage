module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Recover
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: the top digits of an array

`setTop_ok`: the top digit of a zero array := `2^31`; `clrTop_ok`: the two
top digits of an array := 0; `clrW_ok`: the digit after the top := 0.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (setTop clrTop clrW)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) :
    off p a - BitVec.ofNat 64 b = off p (a - b) := by
  simp only [off]
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [BitVec.ofNat_add_ofNat]; congr 1; omega, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem w32_sep (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) : w32 (m.writeW (off B e) v) B d = w32 m B d := by
  unfold w32; rw [Mem.readW_writeW_sep (Offset.sep B h hd he) (by decide)]

/-- `setTop j`: the top digit of the zero array `j` := `2^31`. -/
theorem setTop_ok {s : State} {B : Addr} {Z v N j : Nat} (h : Ws s B Z v N) (hj : j < N) (hN : N ≤ 256)
    (hz : ∀ i < v, w32 s.mem B (arr v j + 4 * i) = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z v N → KeyWorkspace.Keep B v [j] [] s.mem t.mem → num t.mem B v j = 2 ^ (32 * v - 1) →
      Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (setTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S v = 4 * (v + 2) := rfl
  have hv := h.wpos
  have := h.wle
  have hs := h.scr
  rw [setTop, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  let d := arr v j + 4 * (v - 1)
  have ea : off B (arr v j + 4 * v) - 4#64 = off B d := by
    rw [off_sub _ (by omega)]; congr 1; omega
  have ev : (1#64 <<< 31).setWidth 32 = BitVec.ofNat 32 (2 ^ 31) := by decide
  refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.mem = s.mem.writeW (off B d) (BitVec.ofNat 32 (2 ^ 31)))
    ?_ (by decide)) fun t ⟨m, kt⟩ => ?_
  · prun [h.r29, shl2_ofNat, ea, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      hs.st (d := d) (n := 4) (by omega), BitVec.add_zero, ev]
  · have o : Outside B d 4 s.mem t.mem := by rw [m]; exact writeW32_outside _ _ _ (by omega)
    have K : Keep [.r0, .r5] s t := ((Keep.write _ _ _).trans kt).mono
    refine k t (h.of_keep K) (KeyWorkspace.Keep.of_arr (o := j) (d := 4 * (v - 1)) o (by omega) (by simp)) ?_ K
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    simp only [num]
    rw [val32_append t.mem B (arr (u + 1) j) u 1]
    have lo : val32 t.mem B (arr (u + 1) j) u = 0 := by
      rw [← CrtValues.val32_of_zero (m := s.mem) (B := B) (d := arr (u + 1) j) (n := u) (fun i hi => hz i (by omega))]
      refine val32_congr fun i hi => congrArg BitVec.toNat (Mem.readW_congr fun b hb => o _ ?_)
      rw [ofs_off B (by omega)]; omega
    have hi : val32 t.mem B (arr (u + 1) j + 4 * u) 1 = 2 ^ 31 := by
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      rw [m, show arr (u + 1) j + 4 * u = d by omega, w32_write_self]
      rfl
    rw [lo, hi, Nat.zero_add, ← Nat.pow_add]
    congr 1

/-- `clrTop j`: the two top digits of array `j` := 0. -/
theorem clrTop_ok {s : State} {B : Addr} {Z v N j : Nat} (h : Ws s B Z v N) (hj : j < N) (hN : N ≤ 256)
    (hv : 2 ≤ v) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z v N → KeyWorkspace.Keep B v [j] [] s.mem t.mem →
      Outside B (arr v j + 4 * (v - 2)) 8 s.mem t.mem →
      num t.mem B v j = val32 s.mem B (arr v j) (v - 2) → Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrTop j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S v = 4 * (v + 2) := rfl
  have := h.wle
  have hs := h.scr
  rw [clrTop, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  let d := arr v j + 4 * (v - 2)
  have ea : off B (arr v j + 4 * v) - 8#64 = off B d := by
    rw [off_sub _ (by omega)]; congr 1; omega
  refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.mem =
    (s.mem.writeW (off B d) (0 : BitVec 32)).writeW (off B (d + 4)) (0 : BitVec 32)) ?_ (by decide))
    fun t ⟨m, kt⟩ => ?_
  · prun [h.r29, shl2_ofNat, ea, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 4 < 2 ^ 15 by decide),
      hs.st (d := d) (n := 4) (by omega), hs.st (d := d + 4) (n := 4) (by omega), BitVec.add_zero, off_add]
    rfl
  · have o1 : Outside B d 4 s.mem (s.mem.writeW (off B d) (0 : BitVec 32)) := writeW32_outside _ _ _ (by omega)
    have o2 : Outside B (d + 4) 4 (s.mem.writeW (off B d) (0 : BitVec 32)) t.mem := by
      rw [m]; exact writeW32_outside _ _ _ (by omega)
    have o : Outside B d 8 s.mem t.mem := (o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))
    have K : Keep [.r0, .r5] s t := ((Keep.write _ _ _).trans kt).mono
    refine k t (h.of_keep K) (KeyWorkspace.Keep.of_arr (o := j) (d := 4 * (v - 2)) o (by omega) (by simp)) o ?_ K
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 2 := ⟨v - 2, by omega⟩
    simp only [num, Nat.add_sub_cancel]
    rw [val32_append t.mem B (arr (u + 2) j) u 2]
    have lo : val32 t.mem B (arr (u + 2) j) u = val32 s.mem B (arr (u + 2) j) u :=
      val32_congr fun i hi => congrArg BitVec.toNat (Mem.readW_congr fun b hb => o _ (by
        rw [ofs_off B (by omega)]; omega))
    have z1 : w32 t.mem B (arr (u + 2) j + 4 * u) = 0 := by
      rw [show arr (u + 2) j + 4 * u = d by simp only [d]; omega, m, w32_sep _ _ _ (by omega) (by omega) (by omega),
        w32_write_self]
      rfl
    have z2 : w32 t.mem B (arr (u + 2) j + 4 * u + 4) = 0 := by
      rw [show arr (u + 2) j + 4 * u + 4 = d + 4 by simp only [d]; omega, m, w32_write_self]
      rfl
    have hi : val32 t.mem B (arr (u + 2) j + 4 * u) 2 = 0 := by
      simp only [val32, z1, z2, Nat.mul_zero, Nat.add_zero]
    rw [lo, hi, Nat.mul_zero, Nat.add_zero]

/-- `clrW j`: the digit after the top of array `j` := 0. -/
theorem clrW_ok {s : State} {B : Addr} {Z v N j : Nat} (h : Ws s B Z v N) (hj : j < N) (hN : N ≤ 256)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z v N → KeyWorkspace.Keep B v [j] [] s.mem t.mem →
      Outside B (arr v j + 4 * v) 4 s.mem t.mem → w32 t.mem B (arr v j + 4 * v) = 0 →
      Keep [.r0, .r5] s t → WP isa (.block rest) t Q) :
    WP isa (.block (clrW j ++ rest)) s Q := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S v = 4 * (v + 2) := rfl
  have := h.wle
  have hs := h.scr
  rw [clrW, List.append_assoc]
  refine ptr_ok h (r := .r5) (by decide) (by decide) (by decide) (show j < 2 ^ 15 by omega) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.mem = s.mem.writeW (off B (arr v j + 4 * v)) (0 : BitVec 32))
    ?_ (by decide))
    fun t ⟨m, kt⟩ => ?_
  · prun [h.r29, shl2_ofNat, exec_store_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      hs.st (d := arr v j + 4 * v) (n := 4) (by omega), BitVec.add_zero, off_add]
    rfl
  · have o : Outside B (arr v j + 4 * v) 4 s.mem t.mem := by rw [m]; exact writeW32_outside _ _ _ (by omega)
    have K : Keep [.r0, .r5] s t := ((Keep.write _ _ _).trans kt).mono
    refine k t (h.of_keep K) (KeyWorkspace.Keep.of_arr (o := j) (d := 4 * v) o (by omega) (by simp)) o ?_ K
    rw [m, w32_write_self]
    rfl

end VG.Proof.Rsa.PPC64LE.Keys
