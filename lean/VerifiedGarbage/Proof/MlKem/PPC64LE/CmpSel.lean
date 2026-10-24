module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Proof.MlKem.PPC64LE.KemLay
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: comparing `c` with `c'`, and selecting the key

As on 32-bit ARM (`Proof/MlKem/Arm/CmpSel.lean`): `compare` ORs the XORs of
the bytes of two buffers into `r12` (`compare_ok`: 0 exactly when they are
equal); `selSetup` turns it into a mask, all ones exactly when it is 0
(`selSetup_ok`); and the loop of `selBody` writes, byte by byte, the first
source under the mask and the second one otherwise (`select_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-! ## Bytes zero-extended -/

/-- A byte, zero-extended, as `lbz` loads it. -/
theorem setWidth64_toNat (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  have := b.isLt
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

theorem setWidth64_inj {a b : Byte} (h : a.setWidth 64 = b.setWidth 64) : a = b := by
  have := congrArg (BitVec.setWidth 8) h
  rwa [setWidth_byte, setWidth_byte] at this

/-! ## `compare` -/

section
variable {s : State} {x y c a : BitVec 64}

theorem cmpBody_ok (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h26 : s.gpr .r26 = c)
    (h12 : s.gpr .r12 = a) (ir3 : InRegions (s.rd ++ s.wr) x 1) (ir4 : InRegions (s.rd ++ s.wr) y 1) :
    WP isa (.block cmpBody) s fun s' =>
      s'.gpr .r3 = x + BitVec.ofNat 64 1 ∧ s'.gpr .r4 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .r26 = c - BitVec.ofNat 64 1 ∧
      s'.gpr .r12 = a ||| ((s.mem x).setWidth 64 ^^^ (s.mem y).setWidth 64) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r := by
  prun [cmpBody, exec_lbz, Sample.read_one, h3, h4, h26, h12, ir3, ir4]
  and_intros
  all_goals first
    | exact trivial
    | rfl
    | (intro r hr hs
       simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr])

end

/-- After comparing `k` bytes of `S` and `D`. -/
structure CmpInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = S + BitVec.ofNat 64 (1 * k)
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 (1 * k)
  r26 : s.gpr .r26 = BitVec.ofNat 64 (len - k)
  cs : ∀ r ∈ preserved, r ≠ .r26 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lt : (s.gpr .r12).toNat < 256
  eq : s.gpr .r12 = 0 ↔ ∀ t < k, s₀.mem (S + BitVec.ofNat 64 t) = s₀.mem (D + BitVec.ofNat 64 t)

theorem cmp_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (cr : Covers [⟨S, len⟩, ⟨D, len⟩] (s₀.rd ++ s₀.wr)) {k : Nat} (hk : k < len) {s : State}
    (h : CmpInv S D len s₀ k s) :
    WP isa (.block cmpBody) s fun s' =>
      CmpInv S D len s₀ (k + 1) s' ∧ (s'.gpr .r26 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have h3 := h.r3; have h4 := h.r4
  rw [Nat.one_mul] at h3 h4
  refine WP.mono (cmpBody_ok h3 h4 h.r26 rfl
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
      · exact h.eq.mp h₁ t (by omega)
    · intro h₁
      exact BitVec.or_eq_zero_iff.mpr ⟨h.eq.mpr fun t ht => h₁ t (by omega),
        BitVec.xor_eq_zero_iff.mpr (congrArg _ (h₁ k (by omega)))⟩
  · rw [r26, count_sub hk]; exact count_nz hk hlen

theorem cmpArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P C : Addr} (h31 : s.gpr .r31 = P)
    (h28 : s.gpr .r28 = C) :
    WP isa (.block [mov .r3 .r28, .addi .r4 .r31 K.oCt, .li .r12 0, .li .r26 K.ctLen]) s fun s' =>
      s'.gpr .r3 = C ∧ s'.gpr .r4 = P + BitVec.ofNat 64 K.oCt ∧ s'.gpr .r12 = 0 ∧
      s'.gpr .r26 = BitVec.ofNat 64 K.ctLen ∧ (∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hc := hK.ct
  have hi := hK.cin
  have e1 : K.oCt < 32768 := by simp only [oCin] at hc hi; omega
  have e2 : K.ctLen < 32768 := by simp only [oCin] at hi; omega
  prun [e1, e2, h31, h28]
  and_intros
  all_goals first
    | exact trivial
    | rfl
    | (intro r hr hs
       simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr])

/-- `compare`: `r12` is 0 exactly when the `K.ctLen` bytes at `C` (in `r28`)
and at `P + K.oCt` (`r31 = P`) are equal. -/
theorem compare_ok {K : KemLay} (hK : K.WF) {s : State} {P C : Addr} (h31 : s.gpr .r31 = P)
    (h28 : s.gpr .r28 = C)
    (cr : Covers [⟨C, K.ctLen⟩, ⟨P + BitVec.ofNat 64 K.oCt, K.ctLen⟩] (s.rd ++ s.wr)) :
    WP isa K.compare s fun s' => (∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (s'.gpr .r12).toNat < 256 ∧
      (s'.gpr .r12 = 0 ↔
        bytesAt s.mem C K.ctLen = bytesAt s.mem (P + BitVec.ofNat 64 K.oCt) K.ctLen) := by
  have c1 : 0 < K.ctLen := by
    have h1 := hK.du1
    have h2 := hK.k1
    have : 0 < K.uLen * K.k := Nat.mul_pos (by simp only [KemLay.uLen]; omega) (by omega)
    simp only [KemLay.ctLen]; omega
  have c2 : K.ctLen < 2 ^ 64 := by have := hK.cin; simp only [oCin] at this; omega
  refine WP.seq (WP.mono (cmpArgs_ok hK h31 h28) fun s₁ ⟨g3, g4, g12, g26, cs, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (CmpInv C (P + BitVec.ofNat 64 K.oCt) K.ctLen s₁) (N := K.ctLen) c1
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

theorem selSetup_ok {s : State} {P KP : Addr} (h31 : s.gpr .r31 = P) (hlt : (s.gpr .r12).toNat < 256)
    (hk : s.mem.readW (P + BitVec.ofNat 64 oExtra) 64 = KP)
    (ik : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 oExtra) 8) :
    WP isa (.block selSetup) s fun s' =>
      s'.gpr .r12 = (if s.gpr .r12 = 0 then BitVec.allOnes 64 else 0) ∧
      s'.gpr .r3 = P + BitVec.ofNat 64 oG ∧ s'.gpr .r4 = P + BitVec.ofNat 64 oKbar ∧
      s'.gpr .r5 = KP ∧ s'.gpr .r26 = BitVec.ofNat 64 32 ∧
      (∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o1 : oExtra % 8 = 0 ∧ oExtra < 32768 := by decide
  have o2 : oG < 32768 := by decide
  have o3 : oKbar < 32768 := by decide
  prun [selSetup, exec_ld, o1, o2, o3, h31, hk, ik]
  and_intros
  all_goals first
    | exact trivial
    | rfl
    | exact mask_of hlt
    | (intro r hr hs
       simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr])

/-! ## `select` -/

section
variable {s : State} {x y z c m : BitVec 64}

theorem selBody_ok (h3 : s.gpr .r3 = x) (h4 : s.gpr .r4 = y) (h5 : s.gpr .r5 = z)
    (h26 : s.gpr .r26 = c) (h12 : s.gpr .r12 = m)
    (ir3 : InRegions (s.rd ++ s.wr) x 1) (ir4 : InRegions (s.rd ++ s.wr) y 1)
    (iw : InRegions s.wr z 1) :
    WP isa (.block selBody) s fun s' =>
      s'.gpr .r3 = x + BitVec.ofNat 64 1 ∧ s'.gpr .r4 = y + BitVec.ofNat 64 1 ∧
      s'.gpr .r5 = z + BitVec.ofNat 64 1 ∧ s'.gpr .r26 = c - BitVec.ofNat 64 1 ∧
      s'.gpr .r12 = m ∧
      s'.mem = s.mem.writeW z
        ((((((s.mem x).setWidth 64 ^^^ (s.mem y).setWidth 64) &&& m) ^^^
          (s.mem y).setWidth 64).setWidth 8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r := by
  prun [selBody, exec_lbz, exec_stb, Sample.read_one, h3, h4, h5, h26, h12, ir3, ir4, iw]
  and_intros
  all_goals first
    | exact trivial
    | rfl
    | (intro r hr hs
       simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr])

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
  r3 : s.gpr .r3 = X + BitVec.ofNat 64 (1 * k)
  r4 : s.gpr .r4 = Y + BitVec.ofNat 64 (1 * k)
  r5 : s.gpr .r5 = Z + BitVec.ofNat 64 (1 * k)
  r26 : s.gpr .r26 = BitVec.ofNat 64 (32 - k)
  r12 : s.gpr .r12 = if e then BitVec.allOnes 64 else 0
  cs : ∀ r ∈ preserved, r ≠ .r26 → s.gpr r = s₀.gpr r
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
      SelInv X Y Z e s₀ (k + 1) s' ∧ (s'.gpr .r26 != 0) = decide (k + 1 ≠ 32) := by
  have cX : (⟨X, 32⟩ : Region).Contains (X + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have cY : (⟨Y, 32⟩ : Region).Contains (Y + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have cZ : (⟨Z, 32⟩ : Region).Contains (Z + BitVec.ofNat 64 k) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have h3 := h.r3; have h4 := h.r4; have h5 := h.r5
  rw [Nat.one_mul] at h3 h4 h5
  refine WP.mono (selBody_ok h3 h4 h5 h.r26 h.r12
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
    rw [m, byte_writeW8 _ _ (by omega) (by omega), sel_byte, hX, hY]
    by_cases et : t = k
    · subst et; rw [ite_eq_left rfl]
    · rw [ite_eq_right et]; exact h.bytes t (by omega)
  · rw [r26, count_sub hk]; exact count_nz hk (by decide)

/-- The loop of `selBody`: the 32 bytes at `X` if `e`, and at `Y` otherwise, into `Z`. -/
theorem select_ok {X Y Z : Addr} {e : Bool} {s₀ : State}
    (dX : (⟨X, 32⟩ : Region).Disjoint ⟨Z, 32⟩) (dY : (⟨Y, 32⟩ : Region).Disjoint ⟨Z, 32⟩)
    (cr : Covers [⟨X, 32⟩, ⟨Y, 32⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨Z, 32⟩] s₀.wr)
    (h3 : s₀.gpr .r3 = X) (h4 : s₀.gpr .r4 = Y) (h5 : s₀.gpr .r5 = Z)
    (h26 : s₀.gpr .r26 = BitVec.ofNat 64 32) (h12 : s₀.gpr .r12 = if e then BitVec.allOnes 64 else 0) :
    WP isa (.loop (.block selBody) (.nonzero .d .r26)) s₀ fun s =>
      (∀ r ∈ preserved, r ≠ .r26 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
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

end VG.Proof.MlKem.PPC64LE
