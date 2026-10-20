module

public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# ML-KEM on AArch64: buffers, copies and saves

What the top-level functions need besides the primitives, kept apart from
them so that other algorithms (ML-DSA) can use it without importing ML-KEM's
proofs.

The top-level functions use buffers at offsets of their arguments: bytes `[o,
o + l)` of argument `b` (`R A b o l`, with `A b` its pointer and `L b` its
length). Two such buffers are disjoint if they are in different arguments,
which are disjoint, or apart in the same one (`R.disj`); each lies within its
argument (`R.sub`), and so apart from the stack below the stack pointer
(`R.stk`). These reduce the region facts the calls need to arithmetic on the
offsets.

Then the stores of saved registers (`KeyGen.saves_ok`), copies of 32 bytes
(`KeyGen.copy_ok`), and two facts for comparing bytes (`Decaps.xor_zero_iff`,
`Decaps.bytesAt_succ'`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64

/-- Bytes `[o, o + l)` of argument `b`. -/
abbrev R (A : Nat → Addr) (b o l : Nat) : Region := ⟨A b + BitVec.ofNat 64 o, l⟩

/-- The arguments' regions `⟨A b, L b⟩` (for `b < nb`) are pairwise
disjoint, at most 32 KiB, and apart from the 16 bytes below `sp`. -/
structure ArgsOk (A : Nat → Addr) (L : Nat → Nat) (nb : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → Region.Disjoint ⟨A b, L b⟩ ⟨A c, L c⟩
  len : ∀ b < nb, L b ≤ 32768
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, L b⟩

theorem R.sub {A : Nat → Addr} {b o l len : Nat} (h : o + l ≤ len) :
    Region.Sub (R A b o l) ⟨A b, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - A b).toNat ≤ (x - (A b + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - A b = (x - (A b + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by bv_omega, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem sub_offset' {p : Addr} {k n len : Nat} (h : k + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 k, n⟩ ⟨p, len⟩ :=
  R.sub (A := fun _ => p) (b := 0) h

theorem R.sub2 {A : Nat → Addr} {b o l o' l' : Nat} (h₁ : o' ≤ o) (h₂ : o + l ≤ o' + l') :
    Region.Sub (R A b o l) (R A b o' l') := by
  have e : R A b o l = ⟨A b + BitVec.ofNat 64 o' + BitVec.ofNat 64 (o - o'), l⟩ := by
    simp only [R, ptr_add, Nat.add_sub_cancel' h₁]
  rw [e]; exact sub_offset' (by omega)

theorem R.disj {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : ArgsOk A L nb sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ L b₁)
    (f₂ : o₂ + l₂ ≤ L b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem R.stk {A : Nat → Addr} {L : Nat → Nat} {nb : Nat} {sp : Addr} (h : ArgsOk A L nb sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ L b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

theorem R.cov {A : Nat → Addr} {b o l len : Nat} {X : List Region} (hm : (⟨A b, len⟩ : Region) ∈ X)
    (f : o + l ≤ len) : Covers [R A b o l] X :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, hm, o, rfl, f⟩

theorem in_R {A : Nat → Addr} {b o l : Nat} {X : List Region} (hc : Covers [R A b o l] X) {k n : Nat}
    (hk : k + n ≤ l) (hl : l < 2 ^ 64) : InRegions X (A b + BitVec.ofNat 64 (o + k)) n :=
  hc _ _ ⟨_, List.mem_singleton_self _, by rw [← ptr_add]; exact contains_off hk hl⟩

theorem R.contains {A : Nat → Addr} {b o l k n : Nat} (hk : k + n ≤ l) (hl : l < 2 ^ 64) :
    (R A b o l).Contains (A b + BitVec.ofNat 64 (o + k)) n := by
  rw [← ptr_add]; exact contains_off hk hl

end VG.Proof.MlKem.AArch64

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (bytesAt)

/-- Stores of the registers `rs` at `B + off + 8k`. -/
theorem saves_ok (B : Addr) (base : Reg) (off : Nat) (rs : List Reg) (hoff : off + 8 * rs.length ≤ 32768)
    (h8 : off % 8 = 0) :
    ∀ n ≤ rs.length, ∀ {s : State}, s.gpr base = B →
      (∀ k < rs.length, InRegions s.wr (B + BitVec.ofNat 64 (off + 8 * k)) 8) →
      WP isa (.block ((List.range n).map fun k => .str .x (rs.getD k .x0) base (off + 8 * k))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        (∀ k < n, s'.mem.readW (B + BitVec.ofNat 64 (off + 8 * k)) 64 = s.gpr (rs.getD k .x0)) ∧
        Frame [⟨B + BitVec.ofNat 64 off, 8 * rs.length⟩] s.mem s'.mem := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | succ n ih =>
    intro hn s hb hin
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) hb hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := B + BitVec.ofNat 64 (off + 8 * n)) (by constructor <;> omega) (by rw [g₁, hb])
      (by rw [w₁]; exact hin n (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [show B + BitVec.ofNat 64 (off + 8 * n) = B + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * n) by
        rw [ptr_add]]
      exact contains_off (by omega) (by omega)

/-! ## Copies of 32 bytes -/

theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    (m.readW a 64).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

theorem writeW64_byte (m : Mem) (a : Addr) (v : BitVec 64) {i : Nat} (hi : i < 8) :
    m.writeW a v (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega),
    show i < 64 / 8 by omega, ite_true]
  rfl

theorem writeW64_off (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    m.writeW a v x = m x := Mem.write_apply h

/-- The 32 bytes at `S + so` copied to `D + dO`, through `x9`. -/
theorem copy_ok {S D : Addr} {sb db : Reg} {so dO : Nat} (hs9 : sb ≠ .x9) (hd9 : db ≠ .x9)
    (hso : so % 8 = 0 ∧ so + 32 ≤ 32768) (hdo : dO % 8 = 0 ∧ dO + 32 ≤ 32768)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 32⟩ ⟨D + BitVec.ofNat 64 dO, 32⟩)
    {s : State} (hS : s.gpr sb = S) (hD : s.gpr db = D)
    (hin : Covers [⟨S + BitVec.ofNat 64 so, 32⟩] (s.rd ++ s.wr))
    (hout : Covers [⟨D + BitVec.ofNat 64 dO, 32⟩] s.wr) :
    WP isa (.block (copy32 sb so db dO)) s fun s' => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      bytesAt s'.mem (D + BitVec.ofNat 64 dO) 32 = bytesAt s.mem (S + BitVec.ofNat 64 so) 32 := by
  have n9s : sb ∉ [Reg.x9] := by simpa using hs9
  have n9d : db ∉ [Reg.x9] := by simpa using hd9
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k (s' : State) => Keep [.x9] s s' ∧
      Frame [⟨D + BitVec.ofNat 64 dO, 32⟩] s.mem s'.mem ∧
      ∀ i < 8 * k, s'.mem (D + BitVec.ofNat 64 (dO + i)) = s.mem (S + BitVec.ofNat 64 (so + i)))
    (fun k s₁ hk ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ =>
      ⟨k', f', ?_⟩
  · refine wp_ldrx (a := S + BitVec.ofNat 64 (so + 8 * k)) ⟨by omega, by omega⟩ (by rw [k₁.get sb n9s, hS])
      (by rw [k₁.rd, k₁.wr]; exact in_R (A := fun _ => S) (b := 0) hin (k := 8 * k) (by omega) (by decide))
      fun s₂ h₂ e₂ => wp_strx (a := D + BitVec.ofNat 64 (dO + 8 * k)) ⟨by omega, by omega⟩
      (by rw [h₂.get db n9d, k₁.get db n9d, hD])
      (by rw [h₂.wr, k₁.wr]; exact in_R (A := fun _ => D) (b := 0) hout (k := 8 * k) (by omega) (by decide))
      fun s₃ h₃ => wp_nil ?_
    have m₃ : s₃.mem = s₁.mem.writeW (D + BitVec.ofNat 64 (dO + 8 * k))
        (s₁.mem.readW (S + BitVec.ofNat 64 (so + 8 * k)) 64) := by
      rw [h₃.mem, e₂, h₂.mem]
    refine ⟨((k₁.trans h₂.keep).trans h₃.keep).mono, ?_, fun i hi => ?_⟩
    · rw [m₃]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [← ptr_add]; exact contains_off (by omega) (by decide))
    · rw [m₃]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (sep_off D (a := dO + i) (n := 1) (b := dO + 8 * k) (k := 8) (by omega)
          (by omega) (by omega) _ (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · rw [show D + BitVec.ofNat 64 (dO + i) = D + BitVec.ofNat 64 (dO + 8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show dO + 8 * k + (i - 8 * k) = dO + i by omega], writeW64_byte _ _ _ (by omega),
          readW64_byte _ _ (by omega), ptr_add, show so + 8 * k + (i - 8 * k) = so + i by omega]
        refine f₁ _ fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact hsep _ (R.contains (A := fun _ => S) (b := 0) (k := i) (n := 1) (by omega) (by decide)) hc
  · refine List.ext_getElem (by simp only [bytesAt_length]) fun i h₁ _ => ?_
    rw [bytesAt_length] at h₁
    rw [bytesAt_getElem, bytesAt_getElem, ptr_add, ptr_add]
    exact b' i (by omega)

end VG.Proof.MlKem.AArch64.KeyGen

namespace VG.Proof.MlKem.AArch64.Decaps

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (bytesAt)

theorem xor_zero_iff (a b : BitVec 8) : (a.setWidth 64 ^^^ b.setWidth 64 = 0) ↔ a = b := by
  constructor
  · intro h
    have h' := BitVec.xor_eq_zero_iff.mp h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
    exact this
  · intro h; rw [h]; exact BitVec.xor_self

theorem bytesAt_succ' (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add]
  refine congrArg (bytesAt m p k ++ ·) (bytesAt_eq rfl fun i hi => ?_)
  have : i = 0 := by omega
  subst this
  rw [ptr_zero]; rfl

end VG.Proof.MlKem.AArch64.Decaps
