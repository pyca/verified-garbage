module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Seqs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.CallOf
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# The batched inverse as a call on PPC64LE

`invCall_ok`: `CrtValues.invCall`, the call of `vg_rsa_inv_batch`
(`InvBatch.inverseFn`) with the link register kept in array `aNM`, does what
`InvLaw.inverse_ok` says the inverse does, and writes `aNM` too, in a key
working space of any `N` arrays: `vg_rsa_crt_values` and key generation call
it.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.CrtValues

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (aNM seqs)
open VG.Impl.Rsa.PPC64LE.CrtValues (invCall)
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.PPC64LE (InvLaw invBatchArrs invBatchRegs)

section
variable {s : State} {B : Addr} {Z w N : Nat}

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
theorem invCall_ok [InvLaw] (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256) (hw : 10 ≤ w) {n : Nat}
    (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hfit : n + n % 2 ≤ w)
    {x m : Nat} (hx : num s.mem B w 0 = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w 8 = m)
    (hmn : m < 2 ^ (32 * n)) (hodd : m % 2 = 1) :
    WP isa invCall s fun t => Ws t B Z w N ∧
      KeyWorkspace.Keep B w (aNM :: invBatchArrs) [] s.mem t.mem ∧ Keep invBatchRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have fit : arr w aNM + S w ≤ 2 ^ 64 := h.fit64 (by unfold aNM; omega_using [hN15])
  have hS : 8 ≤ S w := by simp only [S]; omega_using []
  have hZ : arr w aNM + 8 ≤ Z := by
    have e1 := VG.Proof.Rsa.KeyWorkspace.arr_end (w := w) (show aNM < N by unfold aNM; omega_using [hN15])
    have e2 := h.fits; omega_using [e1, e2, hS]
  -- The link register into `aNM`, `n` into `r10`.
  have b1 : WP isa (.block (.mflr .r0 :: VG.Impl.Rsa.PPC64LE.Keys.ptr .r5 aNM ++
      [.store .d .r0 .r5 0, .addi .r10 .r11 0])) s fun u =>
      u.mem = s.mem.writeW (lrAt B w) s.lr ∧ u.gpr .r10 = s.gpr .r11 ∧ Keep [.r0, .r5, .r10] s u := by
    refine WP.block_cons_iff.mpr ⟨_, exec_mflr, ?_⟩
    have h0 : Ws (s.write .r0 s.lr) B Z w N := h.of_keep (Keep.write s .r0 s.lr)
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
  have hu : Ws u B Z w N := h.of_keep uk
  have O1 : KeyWorkspace.Keep B w [aNM] [] s.mem u.mem := by
    rw [um]
    refine KeyWorkspace.Keep.of_arr (o := aNM) (d := 0) (n := 8) ?_ hS List.mem_cons_self
    rw [Nat.add_zero]; exact writeW_outside _ _ _ (by omega_using [fit, hS])
  have v0 : num u.mem B w 0 = x := by
    rw [O1.num (by decide) (by decide) (h.fit64 (by omega_using [hN15]))]; exact hx
  have v8 : num u.mem B w 8 = m := by
    rw [O1.num (by decide) (by decide) (h.fit64 (by omega_using [hN15]))]; exact hm
  -- The call: `n` back into `r11`, then the inverse.
  have he : Ws (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)) B Z w N :=
    ⟨hu.scr.congr rfl, hu.fits, hu.wpos, hu.wle,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r29,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r30,
      by simp only [gpr_write]; rw [State.callEntry_gpr _ (by decide)]; exact hu.r31⟩
  have e11 : (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)).gpr .r11 = BitVec.ofNat 64 n := by
    simp only [gpr_write, ite_true, BitVec.add_zero]; rw [State.callEntry_gpr _ (by decide), u10, h11]
  refine WP.seq (WP.mono (WP.callOf (s := u) (Q := fun t => Ws t B Z w N ∧
      KeyWorkspace.Keep B w invBatchArrs [] u.mem t.mem ∧
      Keep invBatchRegs (u.callEntry.write .r11 (u.callEntry.gpr .r10 + BitVec.ofNat 64 0)) t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m)) ?_) fun t ht => ?_)
  · rw [VG.Impl.Rsa.PPC64LE.InvBatch.inverseFn]
    refine WP.seq (WP.block_cons_iff.mpr ⟨_, exec_addi (d := .r11) (n := .r10) (imm := 0) (by decide) (by decide),
      WP.block_nil ?_⟩)
    refine WP.mono (InvLaw.inverse_ok he hN15 hN hw e11 hn1 hnw hfit v0 hxn v8 hmn hodd)
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

end

end VG.Proof.Rsa.PPC64LE.CrtValues
