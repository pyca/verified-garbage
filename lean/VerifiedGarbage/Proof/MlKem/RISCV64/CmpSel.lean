module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
public import VerifiedGarbage.Proof.MlKem.RISCV64.KemLay
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: as on PPC64LE, the comparison and selection loops are proven once here, so that
-- a change to the proof of decapsulation, the largest module, does not re-prove them

/-!
# ML-KEM on RISC-V: comparing `c` with `c'`, and selecting the key

As on PPC64LE (`Proof/MlKem/PPC64LE/CmpSel.lean`): `compare` ORs the XORs of
the bytes of two buffers into `t2` (`compare_ok`: 0 exactly when they are
equal); `selSetup` turns it into a mask, all ones exactly when it is 0
(`selSetup_ok`); and the loop of `selBody` writes, byte by byte, the first
source under the mask and the second one otherwise (`select_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-! ## Bytes zero-extended -/

/-- A byte, zero-extended, as `lbz` loads it. -/
theorem setWidth64_toNat (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  have := b.isLt
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]

theorem setWidth64_inj {a b : Byte} (h : a.setWidth 64 = b.setWidth 64) : a = b := by
  have := congrArg (BitVec.setWidth 8) h
  rwa [setWidth_byte, setWidth_byte] at this

/-! ## `compare` -/

section
variable {s : State} {x y c a : BitVec 64}

theorem cmpBody_ok (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h26 : s.gpr .s6 = c)
    (h12 : s.gpr .t2 = a) (ir3 : InRegions (s.rd ++ s.wr) x 1) (ir4 : InRegions (s.rd ++ s.wr) y 1) :
    WP isa (.block cmpBody) s fun s' =>
      s'.gpr .a0 = x + BitVec.ofNat 64 1 ∧ s'.gpr .a1 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .s6 = c - BitVec.ofNat 64 1 ∧
      s'.gpr .t2 = a ||| ((s.mem x).setWidth 64 ^^^ (s.mem y).setWidth 64) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r := by
  refine wp_lbu (a := x) (by decide) (by rw [h3]; simp) ir3 fun s₁ h₁ =>
    wp_lbu (a := y) (by decide) (by rw [h₁.other _ (by decide), h4]; simp) (by rw [h₁.rd, h₁.wr]; exact ir4)
      fun s₂ h₂ => wp_xor fun s₃ h₃ => wp_or fun s₄ h₄ => wp_addi (by decide) fun s₅ h₅ =>
      wp_addi (by decide) fun s₆ h₆ => wp_subi (by decide) fun s₇ h₇ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, by rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
        by rw [h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
        by rw [h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
        by rw [h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], fun r hr hs => ?_⟩
  · simp only [h₇.gpr_eq, h₆.gpr_eq, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq,
      reduceCtorEq, ↓reduceIte, h3]
  · simp only [h₇.gpr_eq, h₆.gpr_eq, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq,
      reduceCtorEq, ↓reduceIte, h4]
  · simp only [h₇.gpr_eq, ↓reduceIte, h₆.other _ (by decide : Reg.s6 ≠ .a1), h₅.other _ (by decide : Reg.s6 ≠ .a0),
      h₄.other _ (by decide : Reg.s6 ≠ .t2), h₃.other _ (by decide : Reg.s6 ≠ .a2),
      h₂.other _ (by decide : Reg.s6 ≠ .a3), h₁.other _ (by decide : Reg.s6 ≠ .a2), h26]
  · simp only [h₇.gpr_eq, h₆.gpr_eq, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq,
      reduceCtorEq, ↓reduceIte, h12, h₁.mem]
  · obtain ⟨n0, n1, n2, n3, n4, -⟩ := pres_ne hr
    have n5 : r ≠ .t2 := fun e => by subst e; exact absurd hr (by decide)
    rw [h₇.other _ hs, h₆.other _ n2, h₅.other _ n1, h₄.other _ n5, h₃.other _ n3, h₂.other _ n4,
      h₁.other _ n3]

end

/-- After comparing `k` bytes of `S` and `D`. -/
structure CmpInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = S + BitVec.ofNat 64 (1 * k)
  a1 : s.gpr .a1 = D + BitVec.ofNat 64 (1 * k)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len - k)
  cs : ∀ r ∈ preserved, r ≠ .s6 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lt : (s.gpr .t2).toNat < 256
  eq : s.gpr .t2 = 0 ↔ ∀ t < k, s₀.mem (S + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 t)

theorem cmp_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (cr : Covers [⟨S, len⟩, ⟨D, len⟩] (s₀.rd ++ s₀.wr)) {k : Nat} (hk : k < len) {s : State}
    (h : CmpInv S D len s₀ k s) :
    WP isa (.block cmpBody) s fun s' =>
      CmpInv S D len s₀ (k + 1) s' ∧ (s'.gpr .s6 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have h3 := h.a0; have h4 := h.a1
  rw [Nat.one_mul] at h3 h4
  refine WP.mono (cmpBody_ok h3 h4 h.s6 rfl
    (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cS⟩)
    (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cD⟩))
    fun s' ⟨r3, r4, r26, r12, m, rd, wr, sp, cs⟩ =>
    ⟨⟨?_, ?_, ?_, fun r hr hs => (cs r hr hs).trans (h.cs r hr hs), m.trans h.mem, rd.trans h.rd,
      wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r3]; simpa using ptr_succ S 1 k
  · rw [r4]; simpa using ptr_succ D 1 k
  · rw [r26]; exact count_sub hk
  · rw [r12, BitVec.toNat_or, BitVec.toNat_xor, setWidth64_toNat, setWidth64_toNat]
    have ha := h.lt
    have hx := (s.mem (S + BitVec.ofNat 64 k)).isLt
    have hy := (s.mem (D + BitVec.ofNat 64 k)).isLt
    exact Nat.or_lt_two_pow (n := 8) ha (Nat.xor_lt_two_pow (n := 8) hx hy)
  · rw [r12, show s.mem (S + BitVec.ofNat 64 k) = s₀.mem (S + BitVec.ofNat 64 k) by rw [h.mem],
      show s.mem (D + BitVec.ofNat 64 k) = s₀.mem (D + BitVec.ofNat 64 k) by rw [h.mem]]
    constructor
    · intro h₀ t ht
      obtain ⟨h₁, h₂⟩ := BitVec.or_eq_zero_iff.mp h₀
      by_cases e : t = k
      · subst e; exact setWidth64_inj (BitVec.xor_eq_zero_iff.mp h₂)
      · exact h.eq.mp h₁ t (by omega_arith)
    · intro h₁
      exact BitVec.or_eq_zero_iff.mpr ⟨h.eq.mpr fun t ht => h₁ t (by omega_arith),
        BitVec.xor_eq_zero_iff.mpr (congrArg _ (h₁ k (by omega_arith)))⟩
  · rw [r26, count_sub hk]; exact count_nz hk hlen

theorem cmpArgs_ok {K : KemLay} (hK : K.WF) {s : State} {C D : Addr} (h8 : s.gpr .s8 = C)
    (h7 : s.gpr .s7 = D) :
    WP isa (.block [mov .a0 .s8, mov .a1 .s7, .li .t2 0, .li .s6 K.ctLen]) s fun s' =>
      s'.gpr .a0 = C ∧ s'.gpr .a1 = D ∧ s'.gpr .t2 = 0 ∧
      s'.gpr .s6 = BitVec.ofNat 64 K.ctLen ∧ (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hK.ct
  have hi := hK.cin
  have e2 : K.ctLen < 2048 := by
    have h1 : K.du * K.k ≤ 11 * 4 := Nat.mul_le_mul hK.du hK.k4
    have h2 := hK.dv
    simp only [KemLay.ctLen, KemLay.uLen, KemLay.vLen, Nat.mul_assoc]; omega
  refine wp_mv fun s₁ h₁ => wp_mv fun s₂ h₂ => wp_li (by decide) fun s₃ h₃ => wp_li e2 fun s₄ h₄ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr hs => ?_, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem],
      by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  all_goals simp only [h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, h7, h8]
  · rfl
  · obtain ⟨-, n1, n2, -, -, -⟩ := pres_ne hr
    have n5 : r ≠ .t2 := fun e => by subst e; exact absurd hr (by decide)
    simp only [hs, n1, n2, n5, ↓reduceIte]

/-- `compare`: `t2` is 0 exactly when the `K.ctLen` bytes at `C` (in `s8`)
and at `D` (in `s7`) are equal. -/
theorem compare_ok {K : KemLay} (hK : K.WF) {s : State} {C D : Addr} (h8 : s.gpr .s8 = C)
    (h7 : s.gpr .s7 = D)
    (cr : Covers [⟨C, K.ctLen⟩, ⟨D, K.ctLen⟩] (s.rd ++ s.wr)) :
    WP isa K.compare s fun s' => (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (s'.gpr .t2).toNat < 256 ∧
      (s'.gpr .t2 = 0 ↔ bytesAt s.mem C K.ctLen = bytesAt s.mem D K.ctLen) := by
  have c1 : 0 < K.ctLen := by
    have h1 := hK.du1
    have h2 := hK.k1
    have : 0 < K.uLen * K.k := Nat.mul_pos (by simp only [KemLay.uLen]; omega_arith) (by omega_arith)
    simp only [KemLay.ctLen]; omega_arith
  have c2 : K.ctLen < 2 ^ 64 := by have := hK.cin; simp only [oCin] at this; omega_arith
  refine WP.seq (WP.mono (cmpArgs_ok hK h8 h7) fun s₁ ⟨g3, g4, g12, g26, cs, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (CmpInv C D K.ctLen s₁) (N := K.ctLen) c1
    (fun k hk s h => cmp_step c2 (by rw [rd, wr]; exact cr) hk h)
    (fun s' h => ⟨fun r hr hs => (h.cs r hr hs).trans (cs r hr hs), h.mem.trans m, h.rd.trans rd,
      h.wr.trans wr, h.sp.trans sp, h.lt, ?_⟩)
    ⟨by rw [g3]; simp, by rw [g4]; simp, by rw [g26, Nat.sub_zero], fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  rw [h.eq, ← m]
  constructor
  · intro he
    exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by rw [he t ht, bytesAt_getElem]
  · intro he t ht
    have := congrArg (fun L : List Byte => L[t]!) he
    simp only [bytesAt_getElem! _ _ ht] at this
    exact this

/-! ## The mask -/

theorem mask_eq : ∀ n < 256, (0 : BitVec 64) - (BitVec.ofNat 64 n - 1) >>> 63 =
    if n = 0 then BitVec.allOnes 64 else 0 := by
  decide +kernel

theorem mask_of {v : BitVec 64} (h : v.toNat < 256) :
    (0 : BitVec 64) - (v - 1) >>> 63 = if v = 0 then BitVec.allOnes 64 else 0 := by
  have hv := mask_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
  rw [hv]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem selSetup_ok {s : State} {P KP : Addr} (h11 : s.gpr .s11 = P) (hlt : (s.gpr .t2).toNat < 256)
    (h3 : s.gpr .s3 = KP) :
    WP isa (.block selSetup) s fun s' =>
      s'.gpr .t2 = (if s.gpr .t2 = 0 then BitVec.allOnes 64 else 0) ∧
      s'.gpr .a0 = P + BitVec.ofNat 64 oG ∧ s'.gpr .a1 = P + BitVec.ofNat 64 oKbar ∧
      s'.gpr .a2 = KP ∧ s'.gpr .s6 = BitVec.ofNat 64 32 ∧
      (∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine wp_subi (by decide) fun s₁ h₁ => wp_srli (by decide) fun s₂ h₂ => wp_li (by decide) fun s₃ h₃ =>
    wp_sub fun s₄ h₄ => wp_addi (by decide) fun s₅ h₅ => wp_addi (by decide) fun s₆ h₆ => wp_mv fun s₇ h₇ =>
    wp_li (by decide) fun s₈ h₈ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr hs => ?_,
      by rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem],
      by rw [h₈.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
      by rw [h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
      by rw [h₈.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  all_goals simp only [h₈.gpr_eq, h₇.gpr_eq, h₆.gpr_eq, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq,
    h₁.gpr_eq, reduceCtorEq, ↓reduceIte, h11, h3]
  · exact mask_of hlt
  · obtain ⟨-, n1, n2, n3, -, -⟩ := pres_ne hr
    have n5 : r ≠ .t2 := fun e => by subst e; exact absurd hr (by decide)
    simp only [hs, n1, n2, n3, n5, ↓reduceIte]

/-! ## `select` -/

section
variable {s : State} {x y z c m : BitVec 64}

theorem selBody_ok (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y) (h5 : s.gpr .a2 = z)
    (h26 : s.gpr .s6 = c) (h12 : s.gpr .t2 = m)
    (ir3 : InRegions (s.rd ++ s.wr) x 1) (ir4 : InRegions (s.rd ++ s.wr) y 1)
    (iw : InRegions s.wr z 1) :
    WP isa (.block selBody) s fun s' =>
      s'.gpr .a0 = x + BitVec.ofNat 64 1 ∧ s'.gpr .a1 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .a2 = z + BitVec.ofNat 64 1 ∧ s'.gpr .s6 = c - BitVec.ofNat 64 1 ∧
      s'.gpr .t2 = m ∧
      s'.mem = s.mem.writeW z
        ((((((s.mem x).setWidth 64 ^^^ (s.mem y).setWidth 64) &&& m) ^^^
          (s.mem y).setWidth 64).setWidth 8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .s6 → s'.gpr r = s.gpr r := by
  refine wp_lbu (a := x) (by decide) (by rw [h3]; simp) ir3 fun s₁ h₁ =>
    wp_lbu (a := y) (by decide) (by rw [h₁.other _ (by decide), h4]; simp) (by rw [h₁.rd, h₁.wr]; exact ir4)
      fun s₂ h₂ => wp_xor fun s₃ h₃ => wp_and fun s₄ h₄ => wp_xor fun s₅ h₅ =>
      wp_sb (a := z) (by decide)
        (by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, h5]; simp)
        (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact iw) fun s₆ m₆ =>
      wp_addi (by decide) fun s₇ h₇ => wp_addi (by decide) fun s₈ h₈ => wp_addi (by decide) fun s₉ h₉ =>
      wp_subi (by decide) fun s₁₀ h₁₀ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_,
        by rw [h₁₀.rd, h₉.rd, h₈.rd, h₇.rd, m₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
        by rw [h₁₀.wr, h₉.wr, h₈.wr, h₇.wr, m₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
        by rw [h₁₀.sp, h₉.sp, h₈.sp, h₇.sp, m₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], fun r hr hs => ?_⟩
  rotate_left 5
  · rw [h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, m₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, h12, h₁.mem]
  all_goals simp only [h₁₀.gpr_eq, h₉.gpr_eq, h₈.gpr_eq, h₇.gpr_eq, m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq,
    h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, h3, h4, h5, h26, h12]
  obtain ⟨-, n1, n2, n3, n4, n6⟩ := pres_ne hr
  simp only [hs, n1, n2, n3, n4, n6, ↓reduceIte]

end

theorem sel_byte (a b : Byte) (e : Bool) :
    ((((a.setWidth 64 ^^^ b.setWidth 64) &&& (if e then BitVec.allOnes 64 else 0)) ^^^
      b.setWidth 64).setWidth 8) = if e then a else b := by
  cases e
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
      setWidth_byte]

/-- After selecting `k` bytes of `X` or `Y` into `Z`. -/
structure SelInv (X Y Z : Addr) (e : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = X + BitVec.ofNat 64 (1 * k)
  a1 : s.gpr .a1 = Y + BitVec.ofNat 64 (1 * k)
  a2 : s.gpr .a2 = Z + BitVec.ofNat 64 (1 * k)
  s6 : s.gpr .s6 = BitVec.ofNat 64 (32 - k)
  t2 : s.gpr .t2 = if e then BitVec.allOnes 64 else 0
  cs : ∀ r ∈ preserved, r ≠ .s6 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨Z, 32⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (Z + BitVec.ofNat 64 t) =
    if e then s₀.mem (X + BitVec.ofNat 64 t) else s₀.mem (Y + BitVec.ofNat 64 t)

theorem sel_step {X Y Z : Addr} {e : Bool} {s₀ : State}
    (dX : (⟨X, 32⟩ : Region).Disjoint ⟨Z, 32⟩) (dY : (⟨Y, 32⟩ : Region).Disjoint ⟨Z, 32⟩)
    (cr : Covers [⟨X, 32⟩, ⟨Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨Z, 32⟩] s₀.wr)
    {k : Nat} (hk : k < 32) {s : State} (h : SelInv X Y Z e s₀ k s) :
    WP isa (.block selBody) s fun s' =>
      SelInv X Y Z e s₀ (k + 1) s' ∧ (s'.gpr .s6 != 0) = decide (k + 1 ≠ 32) := by
  have cX : (⟨X, 32⟩ : Region).Contains (X + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have cY : (⟨Y, 32⟩ : Region).Contains (Y + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have cZ : (⟨Z, 32⟩ : Region).Contains (Z + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have h3 := h.a0; have h4 := h.a1; have h5 := h.a2
  rw [Nat.one_mul] at h3 h4 h5
  refine WP.mono (selBody_ok h3 h4 h5 h.s6 h.t2
    (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_self .., cX⟩)
    (by rw [h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), cY⟩)
    (by rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cZ⟩))
    fun s' ⟨r3, r4, r5, r26, r12, m, rd, wr, sp, cs⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, r12, fun r hr hs => (cs r hr hs).trans (h.cs r hr hs),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r3]; simpa using ptr_succ X 1 k
  · rw [r4]; simpa using ptr_succ Y 1 k
  · rw [r5]; simpa using ptr_succ Z 1 k
  · rw [r26]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cZ
  · have hX : s.mem (X + BitVec.ofNat 64 k) = s₀.mem (X + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dX _ cX
    have hY : s.mem (Y + BitVec.ofNat 64 k) = s₀.mem (Y + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dY _ cY
    rw [m, byte_writeW8 _ _ (by omega_arith) (by omega_arith), sel_byte, hX, hY]
    by_cases et : t = k
    · subst et; rw [ite_eq_left rfl]
    · rw [ite_eq_right et]; exact h.bytes t (by omega_arith)
  · rw [r26, count_sub hk]; exact count_nz hk (by decide)

/-- The loop of `selBody`: the 32 bytes at `X` if `e`, and at `Y` otherwise, into `Z`. -/
theorem select_ok {X Y Z : Addr} {e : Bool} {s₀ : State}
    (dX : (⟨X, 32⟩ : Region).Disjoint ⟨Z, 32⟩) (dY : (⟨Y, 32⟩ : Region).Disjoint ⟨Z, 32⟩)
    (cr : Covers [⟨X, 32⟩, ⟨Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨Z, 32⟩] s₀.wr)
    (h3 : s₀.gpr .a0 = X) (h4 : s₀.gpr .a1 = Y) (h5 : s₀.gpr .a2 = Z)
    (h26 : s₀.gpr .s6 = BitVec.ofNat 64 32) (h12 : s₀.gpr .t2 = if e then BitVec.allOnes 64 else 0) :
    WP isa (.loop (.block selBody) (.nonzero .s6)) s₀ fun s =>
      (∀ r ∈ preserved, r ≠ .s6 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨Z, 32⟩] s₀.mem s.mem ∧
      bytesAt s.mem Z 32 = if e then bytesAt s₀.mem X 32 else bytesAt s₀.mem Y 32 :=
  wp_loop_nz (SelInv X Y Z e s₀) (N := 32) (by decide)
    (fun k hk s h => sel_step dX dY cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, by
      cases e
      · show bytesAt s.mem Z 32 = bytesAt s₀.mem Y 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
          rw [h.bytes t ht, bytesAt_getElem]; rfl
      · show bytesAt s.mem Z 32 = bytesAt s₀.mem X 32
        exact bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
          rw [h.bytes t ht, bytesAt_getElem]; rfl⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, by rw [h26], h12, fun _ _ _ => rfl, rfl, rfl,
      rfl, Frame.refl _ _, fun t ht => absurd ht (Nat.not_lt_zero t)⟩

end VG.Proof.MlKem.RISCV64
