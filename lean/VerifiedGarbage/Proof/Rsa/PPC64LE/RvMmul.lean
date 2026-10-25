module

import VerifiedGarbage.Proof.Rsa.PPC64LE.RvNumbers
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame

/-!
# `vg_rsa_recover_primes` on PPC64LE: Montgomery products on the key arrays

Montgomery multiplication's working space for `⌈n_len / 8⌉ = wm` words lies
in the key working space, its array `i` the key array `mBase + i` (its base
at `oM = arr w mBase - 256`). `mmul_ok`: a Montgomery product of the low `2 wm`
digits of two key arrays, with the result's top digits cleared.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (mmul mpre mpost mBase nArr)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- The words of Montgomery multiplication. -/
abbrev wm (k : Nat) : Nat := (k + 7) / 8

/-- The offset of Montgomery multiplication's working space. -/
abbrev oM (k : Nat) : Nat := arr (ww k) mBase - 256

theorem arr_mont (k j : Nat) : arr (ww k) (mBase + j) = oM k + VG.Proof.Bignum.slot (wm k) j := by
  simp only [oM, arr, S, ww, wm, mBase, VG.Proof.Bignum.slot, VG.Impl.Bignum.hdrBytes, KeyWorkspace.hdr]
  generalize (k + 7) / 8 = q
  have : 256 ≤ 160 + 20 * (4 * (2 * q + 2 + 2)) := by omega_arith
  grind

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem val32_rebase (m : Mem) (B : Addr) (o : Nat) : ∀ d n, val32 m (off B o) d n = val32 m B (o + d) n
  | _, 0 => rfl
  | d, n + 1 => by
    rw [val32, val32, val32_rebase m B o (d + 4) n, show o + (d + 4) = o + d + 4 by omega_arith]
    simp only [w32, off_off]

theorem w32_rebase (m : Mem) (B : Addr) (o d : Nat) : w32 m (off B o) d = w32 m B (o + d) := by
  simp only [w32, off_off]

/-- A working space at an offset of one. -/
theorem Scr.sub {s : State} {B : Addr} {Z : Nat} (h : Scr s B Z) {o n : Nat} (hn : o + n ≤ Z) (hn0 : 0 < n) :
    Scr s (off B o) n := by
  obtain ⟨⟨B₀, o', L, hm, hb, hL, hL'⟩, nw⟩ := h
  refine ⟨⟨B₀, o' + o, L, hm, by rw [hb, off_off], by omega_arith, hL'⟩, ?_⟩
  simp only [off]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- What changes in a working space at `off B o`, at `B`. -/
theorem Outs.rebase {B : Addr} {o : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs (off B o) rs m m')
    (ho : o < 2 ^ 64) (hr : ∀ r ∈ rs, o + r.1 + r.2 ≤ 2 ^ 64) :
    Outs B (rs.map fun r => (o + r.1, r.2)) m m' :=
  VG.Proof.Bignum.Frm.rebase (B := B) (o := o) (rs := rs) h ho hr

theorem sub2_val (q : Nat) : BitVec.ofNat 64 (2 * q + 2) - BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem add2_val (q : Nat) : BitVec.ofNat 64 (2 * q) + BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * q + 2) := by
  rw [BitVec.ofNat_add_ofNat]

/-- The registers a Montgomery product changes. -/
abbrev mmRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r29]

/-- The low `2 wm` digits of a key array. -/
abbrev lowV (m : Mem) (s0 : State) (j : Nat) : Nat := val32 m (rvB s0) (arr (ww (kK s0)) j) (2 * wm (kK s0))

/-- `mmul o a b`: `[mBase + o] := [mBase + a] [mBase + b] R⁻¹ mod n`, on the low `2 wm` digits. -/
theorem mmul_ok {s0 s : State} (b0 : RBase s0 s) (h : Ws s (rvB s0) (rvZ s0) (ww (kK s0)) nArr) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (rvB s0) (arr (ww (kK s0)) mBase) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : lowV s.mem s0 (mBase + b) < lowV s.mem s0 mBase) :
    WP isa (seqs (mmul o a b)) s fun t => RBase s0 t ∧ Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr ∧
      KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase + 2, mBase + 3, mBase + o] [] s.mem t.mem ∧
      num t.mem (rvB s0) (ww (kK s0)) (mBase + o) < lowV s.mem s0 mBase ∧
      num t.mem (rvB s0) (ww (kK s0)) (mBase + o) * 2 ^ (64 * wm (kK s0)) % lowV s.mem s0 mBase =
        lowV s.mem s0 (mBase + a) * lowV s.mem s0 (mBase + b) % lowV s.mem s0 mBase ∧
      Keep mmRegs s t := by
  have z := b0.sz
  have w1 := z.w1; have w2 := z.w2; have svZ := z.svZ; have nw := z.nw
  have hww : ww (kK s0) = 2 * wm (kK s0) + 2 := rfl
  have hSw : S (ww (kK s0)) = 8 * (wm (kK s0) + 2) := by simp only [S, hww]; omega_arith
  have hsl : ∀ j, VG.Proof.Bignum.slot (wm (kK s0)) j = 256 + j * (8 * (wm (kK s0) + 2)) := fun j => rfl
  have am := arr_mont (kK s0)
  have aM0 : arr (ww (kK s0)) mBase = oM (kK s0) + VG.Proof.Bignum.slot (wm (kK s0)) 0 := by
    have := am 0; simpa using this
  have svw := z.svw
  have fM : oM (kK s0) + VG.Proof.Bignum.slot (wm (kK s0)) 8 ≤ rvZ s0 := by
    rw [← am 8]
    have := VG.Proof.Rsa.KeyWorkspace.arr_mono (w := ww (kK s0)) (show mBase + 8 ≤ nArr by decide)
    rw [← svw] at this; omega_arith
  have hs := h.scr
  have hsM : Scr s (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) 8) :=
    Scr.sub hs fM (by rw [hsl]; omega_arith)
  unfold mmul
  rw [wp_seqs_cons (List.cons_ne_nil _ _), mpre, ← List.append_nil [Instr.subi .r11 .r29 2,
    .addi .r29 .r30 0]]
  refine ptr_ok h (r := .r10) (by decide) (by decide) (by decide) (show mBase < 2 ^ 15 by decide) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r29] (Q := fun x => x.gpr .r11 = BitVec.ofNat 64 (2 * wm (kK s0)) ∧
    x.gpr .r29 = BitVec.ofNat 64 (8 * (wm (kK s0) + 2)) ∧ x.mem = s.mem)
    (by
      have := h.r29; have := h.r30
      prun [h.r29, h.r30, hww, sub2_val, hSw, BitVec.add_zero]) (by decide))
    fun s1 ⟨⟨a11, a29, m1⟩, k1⟩ => WP.block_nil ?_
  have K1 : Keep [.r10, .r11, .r29] s s1 := ((Keep.write _ _ _).trans k1).mono
  have a10 : s1.gpr .r10 = off (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) 0) := by
    rw [k1.gpr _ (by decide), off_off, ← aM0]; simp [gpr_write]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have ev : ∀ (m : Mem) j, val32 m (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) j) (2 * wm (kK s0)) =
      lowV m s0 (mBase + j) := fun m j => by rw [val32_rebase, ← am j]
  have ev0 : ∀ (m : Mem), val32 m (off (rvB s0) (oM (kK s0))) (VG.Proof.Bignum.slot (wm (kK s0)) 0) (2 * wm (kK s0)) =
      lowV m s0 mBase := fun m => by rw [ev]; rfl
  refine WP.mono (Pub.montOp_ok (hsM.congr K1.wr) ho ha hb ho2 ho3 ha2 hb2 (by omega_arith) (by omega_arith) (Nat.le_refl _) a10
    a29 a11 (by rw [K1.gpr _ (by decide)]; exact h12)
    (by rw [K1.gpr _ (by decide), m1, w32_rebase, ← aM0]; exact hinv)
    (by rw [m1, ev, ev0]; exact hB)) fun t1 ⟨⟨lt, eq, out⟩, k2⟩ => ?_
  rw [m1, ev, ev0] at lt eq
  rw [ev, ev] at eq
  rw [show seqs [.block (mpost ++ VG.Impl.Rsa.PPC64LE.Recover.clrTop (mBase + o))] =
    .block (mpost ++ VG.Impl.Rsa.PPC64LE.Recover.clrTop (mBase + o)) from rfl, WP.block_append_iff]
  have e11 : t1.gpr .r11 = BitVec.ofNat 64 (2 * wm (kK s0)) := by rw [k2.gpr _ (by decide)]; exact a11
  refine WP.mono (WP.keep [.r29] (Q := fun x => x.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) ∧ x.mem = t1.mem)
    (by prun [mpost, e11, add2_val, ← hww]) (by decide)) fun t2 ⟨⟨a29', m2⟩, k3⟩ => ?_
  have K : Keep (.r10 :: .r11 :: .r29 :: VG.Proof.Bignum.PPC64LE.Pub.montRegs) s t2 := ((K1.trans k2).trans k3).mono
  have w2' : Ws t2 (rvB s0) (rvZ s0) (ww (kK s0)) nArr :=
    ⟨hs.congr K.wr, h.fits, h.wpos, h.wle, a29', (K.gpr _ (by decide)).trans h.r30,
      (K.gpr _ (by decide)).trans h.r31⟩
  refine clrTop_ok w2' (j := mBase + o) (by simp only [mBase, nArr]; omega_arith) (by decide) (by omega_arith)
    fun t3 w3 kk3 o3 v3 k4 => WP.block_nil ?_
  -- The frame.
  have O : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase + 2, mBase + 3, mBase + o] [] s1.mem t1.mem := by
    have fitM : ∀ j < 8, oM (kK s0) + VG.Proof.Bignum.slot (wm (kK s0)) j + 8 * (wm (kK s0) + 2) ≤ 2 ^ 64 :=
      fun j hj => by rw [← am j, ← hSw]; exact h.fit64 (by simp only [mBase, nArr]; omega_arith)
    have := Outs.rebase out (by have := fM; rw [hsl] at this; omega_arith) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fitM 2 (by decide)
      · exact fitM 3 (by decide)
      · exact fitM o ho)
    refine Outs.cover this fun r hr => ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨r, ?_, Nat.le_refl _, Nat.le_refl _⟩
    simp only [KeyWorkspace.ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    rcases hr with rfl | rfl | rfl <;> simp only [← am, hSw, Prod.mk.injEq, and_true] <;> simp
  have KK : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [mBase + 2, mBase + 3, mBase + o] [] s.mem t3.mem := by
    rw [← m1]
    exact KeyWorkspace.Keep.trans O (by rw [← m2]; exact KeyWorkspace.Keep.mono kk3)
  have hv : num t3.mem (rvB s0) (ww (kK s0)) (mBase + o) = lowV t1.mem s0 (mBase + o) := by
    rw [v3, m2, show ww (kK s0) - 2 = 2 * wm (kK s0) by omega_arith]
  have K' : Keep mmRegs s t3 := (K.trans k4).mono
  refine ⟨b0.of_keep KK (fun j hj => ?_) (by simp) K', w3, KK, by rw [hv]; exact lt, by rw [hv]; exact eq, K'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  have : j < nArr := by rcases hj with rfl | rfl | rfl <;> simp only [mBase, nArr] <;> omega_arith
  rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end this

end VG.Proof.Rsa.PPC64LE.Recover
