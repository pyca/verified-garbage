module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Absorb
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Poly1305 on PPC64LE: the state, and `setup`

As on AArch64 (`Proof/Poly1305/AArch64/Blocks.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Proof.Poly1305.Radix26
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := Offset.contains_base base h hd

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := Offset.sep p h (by omega_using [hd, hn]) (by omega_using [he, hk])

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by decide) (by decide) h) (by decide)

theorem readW32_writeW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  Mem.readW_writeW_sep (sep_off p hd he (by decide) (by decide) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) :=
  Offset.sub_base st h

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint_base st (by decide) (by decide)
  · exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp only [Nat.reducePow, Nat.reduceLeDiff]) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 :=
  contains_off h (by omega_using [h])

/-! ## The accumulator and the key as numbers -/

theorem add_ofNat_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = w64 m st 0 + 2 ^ 64 * w64 m st 8 + 2 ^ 128 * w64 m st 16 := by
  rw [Poly1305.leNum_bytesAt_24, w64, add_ofNat_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _),
    List.take_of_length_le (by rw [Poly1305.length_bytesAt])]
  congr 1
  simp only [off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w64 m p 0 + 2 ^ 64 * w64 m p 8 := by
  rw [Poly1305.leNum_bytesAt_16, w64, add_ofNat_zero]
  rfl

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The clamped `r` of the key in the state. -/
abbrev Rk (m : Mem) (st : Addr) : Nat :=
  (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) = Rk m st := by
  rw [key_take, leNum_key, w64, w64, off, add_ofNat_zero, add_ofNat_add, Poly1305.clamp_words]

theorem Rk_lt (m : Mem) (st : Addr) : Rk m st < 2 ^ 128 := by
  have := (m.readW (off st 24) 64 &&& M0).isLt
  have := (m.readW (off st 32) 64 &&& M1).isLt
  simp only [Rk]
  omega

/-! ## The coefficients and the accumulator on entry -/

set_option simprocs false in
/-- `r` clamped. -/
theorem clampR_ok (s : State) :
    WP isa (.block clampR) s fun s' =>
      s'.gpr .r18 = s.gpr .r18 &&& M0 ∧ s'.gpr .r19 = s.gpr .r19 &&& M1 ∧
      Keeps [.r18, .r19, .r0] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [clampR, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec_lis, exec_ori, exec_oris, exec_logic,
    exec_lsl (show 32 < 64 by decide), write_gpr, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨congrArg (s.gpr .r18 &&& ·) (by decide), congrArg (s.gpr .r19 &&& ·) (by decide),
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

set_option simprocs false in
/-- `sj = 5 rj`. -/
theorem times5_ok (s : State) :
    WP isa (.block times5) s fun s' =>
      v s' .r7 = (v s .r14 * 2 ^ 2 % 2 ^ 64 + v s .r14) % 2 ^ 64 ∧
      v s' .r8 = (v s .r15 * 2 ^ 2 % 2 ^ 64 + v s .r15) % 2 ^ 64 ∧
      v s' .r9 = (v s .r16 * 2 ^ 2 % 2 ^ 64 + v s .r16) % 2 ^ 64 ∧
      v s' .r10 = (v s .r17 * 2 ^ 2 % 2 ^ 64 + v s .r17) % 2 ^ 64 ∧
      Keeps [.r7, .r8, .r9, .r10] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [times5, runBlock_cons, runStep_some, runBlock_nil,
    exec_lsl (show 2 < 64 by decide), exec_add, v, write_gpr, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩ <;> try rw [add_toNat, lsl_toNat]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.2.2.2, hr.2.2.1, hr.2.1, hr.1, ite_false, write_gpr]

/-- The memory after the coefficients are stored: `r j` at `rOff j`, `s j` at `sOff j`. -/
def coefMem (m : Mem) (st : Addr) (r s : Nat → BitVec 64) : Mem :=
  ((((((((m.writeW (off st (rOff 0)) ((r 0).setWidth 32)).writeW (off st (rOff 1))
    ((r 1).setWidth 32)).writeW (off st (rOff 2)) ((r 2).setWidth 32)).writeW (off st (rOff 3))
    ((r 3).setWidth 32)).writeW (off st (rOff 4)) ((r 4).setWidth 32)).writeW (off st (sOff 1))
    ((s 1).setWidth 32)).writeW (off st (sOff 2)) ((s 2).setWidth 32)).writeW (off st (sOff 3))
    ((s 3).setWidth 32)).writeW (off st (sOff 4)) ((s 4).setWidth 32)

/-- The registers holding `rj` and `sj` when they are stored. -/
def rv (s : State) (j : Nat) : BitVec 64 := s.gpr (D.getD j .r12)
def sv (s : State) (j : Nat) : BitVec 64 := s.gpr (H.getD (j - 1) .r7)

set_option simprocs false in
theorem storeCoefs_ok (s : State)
    (hw : ∀ d, 72 ≤ d → d + 4 ≤ 108 → InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 d) 4) :
    WP isa (.block storeCoefs) s fun s' =>
      s'.mem = coefMem s.mem (s.gpr .r3) (rv s) (sv s) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have o0 := hw (72 + 4 * 0) (by decide) (by decide); have o1 := hw (72 + 4 * 1) (by decide) (by decide)
  have o2 := hw (72 + 4 * 2) (by decide) (by decide); have o3 := hw (72 + 4 * 3) (by decide) (by decide)
  have o4 := hw (72 + 4 * 4) (by decide) (by decide); have o5 := hw (88 + 4 * 1) (by decide) (by decide)
  have o6 := hw (88 + 4 * 2) (by decide) (by decide); have o7 := hw (88 + 4 * 3) (by decide) (by decide)
  have o8 := hw (88 + 4 * 4) (by decide) (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeCoefs, rOff, sOff, runBlock_cons, runStep_some,
    runBlock_nil, exec_store_w, o0, o1, o2, o3, o4, o5, o6, o7, o8, Option.some.injEq,
    exists_eq_left']
  trivial

set_option simprocs false in
theorem coefMem_r (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj : j < 5) :
    (coefMem m st r s).readW (off st (rOff j)) 32 = (r j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj]
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

set_option simprocs false in
theorem coefMem_s (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {j : Nat} (hj₁ : 1 ≤ j) (hj : j < 5) :
    (coefMem m st r s).readW (off st (sOff j)) 32 = (s j).setWidth 32 := by
  obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [hj₁, hj]
  all_goals simp (config := {decide := true}) only [coefMem, rOff, sOff, Mem.readW_writeW_self32,
    readW32_writeW32_off]

/-- The coefficients' region. -/
abbrev cR (st : Addr) : Region := ⟨off st 72, 36⟩

theorem coefMem_frame (m : Mem) (st : Addr) (r s : Nat → BitVec 64) :
    Frame [cR st] m (coefMem m st r s) := by
  have c : ∀ d, 72 ≤ d → d + 4 ≤ 108 → (cR st).Contains (off st d) (32 / 8) := fun d h₁ h₂ => by
    exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)
  simp only [coefMem]
  refine (((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c (rOff 0) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (rOff 2) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (rOff 3) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (rOff 4) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 1) ?_ ?_)).writeW (List.mem_singleton_self _) _ (c (sOff 2) ?_ ?_)).writeW
    (List.mem_singleton_self _) _ (c (sOff 3) ?_ ?_)).writeW (List.mem_singleton_self _) _
    (c (sOff 4) ?_ ?_)
  all_goals decide

/-- The coefficients read back. -/
theorem coefMem_coefs (m : Mem) (st : Addr) (r s : Nat → BitVec 64) (R : Nat)
    (hr : ∀ j < 5, ((r j).setWidth 32).toNat = lim R j)
    (hs : ∀ j, 1 ≤ j → j < 5 → ((s j).setWidth 32).toNat = 5 * lim R j) :
    Coefs (coefMem m st r s) st R := by
  intro k hk i hi
  by_cases h : i ≤ k
  · have e : coef k i = rOff (k - i) := ite_eq_left h
    have e' : cval R k i = lim R (k - i) := ite_eq_left h
    rw [e, e', ← hr (k - i) (by omega_using [hk, hi, h])]
    exact congrArg BitVec.toNat (coefMem_r m st r s (by omega_using [hk, hi, h]))
  · have e : coef k i = sOff (k + 5 - i) := ite_eq_right h
    have e' : cval R k i = 5 * lim R (k + 5 - i) := ite_eq_right h
    rw [e, e', ← hs (k + 5 - i) (by omega_using [hk, hi]) (by omega_using [h])]
    exact congrArg BitVec.toNat (coefMem_s m st r s (by omega_using [hk, hi]) (by omega_using [h]))

set_option simprocs false in
/-- The limbs of the stored `h` into `r7`–`r11`, from those of its low 128 bits in `r12`–`r17`. -/
theorem moveH_ok (s : State) (h16 : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 16) 8) :
    WP isa (.block moveH) s fun s' =>
      v s' .r7 = v s .r12 ∧ v s' .r8 = v s .r14 ∧ v s' .r9 = v s .r15 ∧ v s' .r10 = v s .r16 ∧
      v s' .r11 = (v s .r17 + w64 s.mem (s.gpr .r3) 16 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 ∧
      Keeps [.r7, .r8, .r9, .r10, .r11, .r0] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [moveH, runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r3 ≠ .r0 by decide) (show 16 < 2 ^ 15 ∧ 16 % 4 = 0 by decide) h16,
    exec_lsl (show 24 < 64 by decide), exec_addi (show Reg.r12 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_addi (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_addi (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    exec_addi (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), exec_add, v, write_gpr,
    add_ofNat_zero, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_, fun r hr => ?_, rfl, rfl,
    rfl⟩
  · rw [add_toNat, lsl_toNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.2.2.2.2.1, hr.2.2.2.1, hr.2.2.1, hr.2.1, hr.1, hr.2.2.2.2.2, ite_false, write_gpr]

/-! ## `setup` -/

/-- The registers `setup` writes. -/
abbrev setupRegs : List Reg :=
  [.r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r0, .r20]

/-- The state after `setup`, from `s₀`. -/
structure Setup (s₀ s : State) : Prop where
  gpr : ∀ r, r ∉ setupRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mask : s.gpr .r20 = M26
  frame : Frame [cR (s₀.gpr .r3)] s₀.mem s.mem
  coefs : Coefs s.mem (s₀.gpr .r3) (Rk s₀.mem (s₀.gpr .r3))
  acc : leNum (bytesAt s₀.mem (s₀.gpr .r3) 24) < P →
    hv s = leNum (bytesAt s₀.mem (s₀.gpr .r3) 24) ∧ Bounds s

theorem times5_eq {N : Nat} (h : N < 2 ^ 26) : (N * 2 ^ 2 % 2 ^ 64 + N) % 2 ^ 64 = 5 * N := by
  omega_using [h]

theorem lt5_cases {j : Nat} (h : j < 5) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [h]
theorem lt5_cases' {j : Nat} (h₁ : 1 ≤ j) (h : j < 5) : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega_using [h₁, h]

/-- The limbs of `h = W0 + 2⁶⁴ W1 + 2¹²⁸ W2 < p`, as `loadH` computes them. -/
theorem loadH_arith {W0 W1 W2 : Nat} (h0 : W0 < 2 ^ 64) (h1 : W1 < 2 ^ 64)
    (hP : W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 < P) :
    val5 (lim (W0 + 2 ^ 64 * W1) 0) (lim (W0 + 2 ^ 64 * W1) 1) (lim (W0 + 2 ^ 64 * W1) 2)
        (lim (W0 + 2 ^ 64 * W1) 3) ((lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64) =
      W0 + 2 ^ 64 * W1 + 2 ^ 128 * W2 ∧
    lim (W0 + 2 ^ 64 * W1) 0 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 1 < 2 ^ 27 ∧
    lim (W0 + 2 ^ 64 * W1) 2 < 2 ^ 26 ∧ lim (W0 + 2 ^ 64 * W1) 3 < 2 ^ 26 ∧
    (lim (W0 + 2 ^ 64 * W1) 4 + W2 * 2 ^ 24 % 2 ^ 64) % 2 ^ 64 < 2 ^ 26 := by
  have e := val5_lim (W0 + 2 ^ 64 * W1)
  have b0 := lim_lt (W0 + 2 ^ 64 * W1) (j := 0) (by decide)
  have b1 := lim_lt (W0 + 2 ^ 64 * W1) (j := 1) (by decide)
  have b2 := lim_lt (W0 + 2 ^ 64 * W1) (j := 2) (by decide)
  have b3 := lim_lt (W0 + 2 ^ 64 * W1) (j := 3) (by decide)
  have b4 := lim4_lt (N := W0 + 2 ^ 64 * W1) (by omega_using [h0, h1, e])
  have hW2 : W2 ≤ 3 := by simp only [P] at hP; omega_using [hP, e]
  generalize lim (W0 + 2 ^ 64 * W1) 0 = a0, lim (W0 + 2 ^ 64 * W1) 1 = a1,
    lim (W0 + 2 ^ 64 * W1) 2 = a2, lim (W0 + 2 ^ 64 * W1) 3 = a3,
    lim (W0 + 2 ^ 64 * W1) 4 = a4 at *
  simp only [val5] at e ⊢
  omega_using [hW2, e, b0, b1, b2, b3, b4]

theorem lt32 {N : Nat} (h : N < 2 ^ 26) : N < 2 ^ 32 := by omega_using [h]

theorem times5_lt {N : Nat} (h : N < 2 ^ 26) : 5 * N < 2 ^ 32 := by omega_using [h]

/-- A coefficient in a register, stored as a 32-bit word. -/
theorem coef_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 32) :
    (x.setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, h, Nat.mod_eq_of_lt hn]

theorem coefMem_readW_low (m : Mem) (st : Addr) (r s : Nat → BitVec 64) {d : Nat} (hd : d + 8 ≤ 56) :
    (coefMem m st r s).readW (off st d) 64 = m.readW (off st d) 64 := by
  refine (coefMem_frame m st r s).readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint st (by omega_using [hd]) (by omega_using [hd]) (by decide)

theorem setup_ok (s₀ : State) (hw : sR (s₀.gpr .r3) ∈ s₀.wr) :
    WP isa (.block setup) s₀ (Setup s₀) := by
  have i : ∀ d n, d + n ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r3) d) n :=
    fun d n h => ⟨_, List.mem_append_right _ hw, contains_off h (by omega_using [h])⟩
  rw [setup, coeffs, loadH]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (mask_ok s₀) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .r3 = s₀.gpr .r3 := k₁.gpr'
  refine WP.block_append (WP.mono (load2_ok s₁ (n := .r3) (off := 24) (by decide) (by decide)
    (by decide) (by decide) (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i 24 8 (by decide))
    (by rw [k₁.2.2.1, k₁.2.2.2, x0₁]; exact i (24 + 8) 8 (by decide))) fun s₂ ⟨l₁, l₂, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (clampR_ok s₂) fun s₃ ⟨c₁, c₂, k₃⟩ => ?_)
  have k₁₃ := (k₁.trans k₂).trans k₃
  refine WP.block_append (WP.mono (split_ok s₃ (by rw [(k₂.trans k₃).gpr']; exact m₁))
    fun s₄ ⟨r0, r1, r2, r3, r4, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (times5_ok s₄) fun s₅ ⟨t1, t2, t3, t4, k₅⟩ => ?_)
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  have x0₅ : s₅.gpr .r3 = s₀.gpr .r3 := k₁₅.gpr'
  have m₅ : s₅.gpr .r20 = M26 := by rw [(((k₂.trans k₃).trans k₄).trans k₅).gpr']; exact m₁
  refine WP.block_append (WP.mono (storeCoefs_ok s₅ fun d h₁ h₂ => by
    rw [k₁₅.2.2.2, x0₅]; exact ⟨_, hw, contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩)
    fun s₆ ⟨mm₆, g₆, rd₆, wr₆⟩ => ?_)
  have x0₆ : s₆.gpr .r3 = s₀.gpr .r3 := by rw [g₆, x0₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₁₅.2.2.1]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₁₅.2.2.2]
  refine WP.block_append (WP.mono (load2_ok s₆ (n := .r3) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (by rw [rd₆', wr₆', x0₆]; exact i 0 8 (by decide))
    (by rw [rd₆', wr₆', x0₆]; exact i (0 + 8) 8 (by decide))) fun s₇ ⟨l₃, l₄, k₇⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₇ (by
    rw [k₇.gpr', g₆]; exact m₅))
    fun s₈ ⟨h0, h1, h2, h3, h4, k₈⟩ => ?_)
  have k₇₈ := k₇.trans k₈
  refine WP.mono (moveH_ok s₈ (by
    rw [k₇₈.2.2.1, k₇₈.2.2.2, k₇₈.gpr', rd₆', wr₆', x0₆]; exact i 16 8 (by decide)))
    fun s₉ ⟨e0, e1, e2, e3, e4, k₉⟩ => ?_
  have k₇₉ := k₇₈.trans k₉
  have sub : ∀ r, r ∉ setupRegs → ∀ l : List Reg, (∀ x ∈ l, x ∈ setupRegs) → r ∉ l :=
    fun r hr l hl h => hr (hl r h)
  have mem₉ : s₉.mem = coefMem s₀.mem (s₀.gpr .r3) (rv s₅) (sv s₅) := by
    rw [k₇₉.2.1, mm₆, k₁₅.2.1, x0₅]
  have R_eq : v s₃ .r18 + 2 ^ 64 * v s₃ .r19 = Rk s₀.mem (s₀.gpr .r3) := by
    simp only [v, c₁, c₂, l₁, l₂, x0₁, k₁.2.1]
  have b : ∀ j < 4, lim (Rk s₀.mem (s₀.gpr .r3)) j < 2 ^ 26 := fun j hj => lim_lt _ hj
  have b4 := lim4_lt (Rk_lt s₀.mem (s₀.gpr .r3))
  have v5 : ∀ r ∈ [Reg.r12, .r14, .r15, .r16, .r17], v s₅ r = v s₄ r := fun r hr => by
    simp only [v]; rw [k₅.1 r (by revert hr; decide +revert)]
  have q0 : v s₅ .r12 = lim (Rk s₀.mem (s₀.gpr .r3)) 0 := by rw [v5 .r12 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false]), r0, R_eq]
  have q1 : v s₅ .r14 = lim (Rk s₀.mem (s₀.gpr .r3)) 1 := by rw [v5 .r14 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r1, R_eq]
  have q2 : v s₅ .r15 = lim (Rk s₀.mem (s₀.gpr .r3)) 2 := by rw [v5 .r15 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r2, R_eq]
  have q3 : v s₅ .r16 = lim (Rk s₀.mem (s₀.gpr .r3)) 3 := by rw [v5 .r16 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), r3, R_eq]
  have q4 : v s₅ .r17 = lim (Rk s₀.mem (s₀.gpr .r3)) 4 := by rw [v5 .r17 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), r4, R_eq]
  have p1 : v s₅ .r7 = 5 * lim (Rk s₀.mem (s₀.gpr .r3)) 1 := by
    rw [t1, ← v5 .r14 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q1, times5_eq (b 1 (by decide))]
  have p2 : v s₅ .r8 = 5 * lim (Rk s₀.mem (s₀.gpr .r3)) 2 := by
    rw [t2, ← v5 .r15 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q2, times5_eq (b 2 (by decide))]
  have p3 : v s₅ .r9 = 5 * lim (Rk s₀.mem (s₀.gpr .r3)) 3 := by
    rw [t3, ← v5 .r16 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, or_true]), q3, times5_eq (b 3 (by decide))]
  have p4 : v s₅ .r10 = 5 * lim (Rk s₀.mem (s₀.gpr .r3)) 4 := by
    rw [t4, ← v5 .r17 (by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, or_true]), q4, times5_eq (Nat.lt_trans b4 (by decide))]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun hlt => ?_⟩
  · rw [k₇₉.1 r (sub r hr _ (by decide)), g₆, k₁₅.1 r (sub r hr _ (by decide))]
  · rw [k₇₉.2.2.1, rd₆']
  · rw [k₇₉.2.2.2, wr₆']
  · rw [k₇₉.gpr', g₆]; exact m₅
  · rw [mem₉]; exact coefMem_frame _ _ _ _
  · rw [mem₉]
    refine coefMem_coefs _ _ _ _ _ (fun j hj => ?_) (fun j hj₁ hj => ?_)
    · obtain rfl | rfl | rfl | rfl | rfl := lt5_cases hj
      · exact coef_toNat q0 (lt32 (b 0 (by decide)))
      · exact coef_toNat q1 (lt32 (b 1 (by decide)))
      · exact coef_toNat q2 (lt32 (b 2 (by decide)))
      · exact coef_toNat q3 (lt32 (b 3 (by decide)))
      · exact coef_toNat q4 (lt32 (Nat.lt_trans b4 (by decide)))
    · obtain rfl | rfl | rfl | rfl := lt5_cases' hj₁ hj
      · exact coef_toNat p1 (times5_lt (b 1 (by decide)))
      · exact coef_toNat p2 (times5_lt (b 2 (by decide)))
      · exact coef_toNat p3 (times5_lt (b 3 (by decide)))
      · exact coef_toNat p4 (times5_lt (Nat.lt_trans b4 (by decide)))
  · have hs : ∀ d, d + 8 ≤ 56 → w64 s₈.mem (s₈.gpr .r3) d = w64 s₀.mem (s₀.gpr .r3) d := fun d hd => by
      simp only [w64]
      rw [k₇₈.2.1, k₇₈.gpr', mm₆, k₁₅.2.1, x0₆, x0₅]
      exact congrArg BitVec.toNat (coefMem_readW_low _ _ _ _ hd)
    have w0 : v s₇ .r18 = w64 s₀.mem (s₀.gpr .r3) 0 := by
      simp only [v, l₃]; rw [← hs 0 (by decide), k₇₈.2.1, k₇₈.gpr']
    have w1 : v s₇ .r19 = w64 s₀.mem (s₀.gpr .r3) 8 := by
      simp only [v, l₄]; rw [← hs 8 (by decide), k₇₈.2.1, k₇₈.gpr']
    rw [leNum_acc] at hlt ⊢
    rw [h4, w0, w1] at e4
    rw [hs 16 (by decide)] at e4
    rw [h0, w0, w1] at e0; rw [h1, w0, w1] at e1; rw [h2, w0, w1] at e2; rw [h3, w0, w1] at e3
    simp only [hv, Bounds, e0, e1, e2, e3, e4]
    exact loadH_arith (BitVec.isLt _) (BitVec.isLt _) hlt

end VG.Proof.Poly1305.PPC64LE
