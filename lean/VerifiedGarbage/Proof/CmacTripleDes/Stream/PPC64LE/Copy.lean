module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming TDEA-CMAC on PPC64LE: the byte copy

`copyLoop_wp`: `copyLoop` copies the `n` bytes at `src` (`r10`) to `dst`
(`r11`), where `r12 = n`, when the two do not overlap, and changes no other
memory and no register but `r0` and `r10`–`r12`, leaving `r10` and `r11`
past the bytes.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

theorem sub_lt_one {x a : Addr} : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by show _ = 0; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; simp
  · rintro rfl; simp

theorem ofNat_succ (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- After `j` of the `n` bytes. -/
structure CopyInv (s : State) (src dst : Addr) (n j : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = src + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = dst + BitVec.ofNat 64 j
  r12 : t.gpr .r12 = BitVec.ofNat 64 (n - j)
  regs : ∀ r, r ≠ .r0 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  copied : ∀ i < j, t.mem (dst + BitVec.ofNat 64 i) = s.mem (src + BitVec.ofNat 64 i)
  rest : ∀ x, (∀ i < j, x ≠ dst + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copy_step {s : State} {src dst : Addr} {n j : Nat} (hj : j < n) (hn : n < 2 ^ 64)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hwr : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ i' < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 i')
    {t : State} (hI : CopyInv s src dst n j t) :
    WP isa (.block [.lbz .r0 .r10 0, .stb .r0 .r11 0, .addi .r10 .r10 1, .addi .r11 .r11 1,
      .subi .r12 .r12 1]) t (CopyInv s src dst n (j + 1)) := by
  refine wp_lbz (a := src + BitVec.ofNat 64 j) (by decide) (by decide) (by rw [hI.r10]; simp)
    (by rw [hI.rd, hI.wr]; exact hrd j hj) fun t₁ u₁ => ?_
  refine wp_stb (a := dst + BitVec.ofNat 64 j) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), hI.r11]; simp) (by rw [u₁.wr, hI.wr]; exact hwr j hj) fun t₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ u₃ => wp_addi (by decide) (by decide) fun t₄ u₄ =>
    wp_subi (by decide) (by decide) fun t₅ u₅ => wp_nil ?_
  have src_j : t.mem (src + BitVec.ofNat 64 j) = s.mem (src + BitVec.ofNat 64 j) :=
    hI.rest _ fun i hi => hsep j hj i (by omega)
  have m₅ : t₅.mem = t.mem.writeW (dst + BitVec.ofNat 64 j) (s.mem (src + BitVec.ofNat 64 j)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem, setWidth8_64, src_j]
  refine ⟨?_, ?_, ?_, fun r h0 h10 h11 h12 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr], fun i hi => ?_, fun x hx => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.r10,
      ofNat_succ]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r11,
      ofNat_succ]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r12]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [u₅.other r h12, u₄.other r h11, u₃.other r h10, u₂.gpr, u₁.other r h0, hI.regs r h0 h10 h11 h12]
  · rw [m₅, write1_apply]
    by_cases e : i = j
    · subst e; rw [ite_eq_left (sub_lt_one.mpr rfl)]
    · have hne : dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j := by
        intro h
        have := congrArg (fun y => BitVec.toNat (y - dst)) h
        simp only [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact e this
      rw [ite_eq_right (fun h => hne (sub_lt_one.mp h)), hI.copied i (by omega)]
  · rw [m₅, write1_apply, ite_eq_right (fun h => hx j (by omega) (sub_lt_one.mp h)),
      hI.rest x fun i hi => hx i (by omega)]

theorem copyLoop_wp {s : State} {src dst : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h10 : s.gpr .r10 = src) (h11 : s.gpr .r11 = dst) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hwr : ∀ i < n, InRegions s.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ i' < n, src + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 i')
    {Q : State → Prop} (k : ∀ t, CopyInv s src dst n n t → Q t) :
    WP isa copyLoop s Q := by
  have h0 : CopyInv s src dst n 0 s := ⟨by rw [h10]; simp, by rw [h11]; simp, by rw [h12, Nat.sub_zero], fun _ _ _ _ _ => rfl,
    rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩
  by_cases hz : n = 0
  · subst hz
    exact WP.ite true (by rw [eval_zero_ofNat s .r12 (by decide) h12]; rfl) (fun _ => wp_nil (k s h0))
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .r12 hn h12]; simp [hz]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (Q := Q)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ CopyInv s src dst n j t) ?_ n s ⟨0, by omega, by omega, h0⟩
  rintro _ t ⟨j, rfl, hj, hI⟩
  refine WP.mono (copy_step hj hn hrd hwr hsep hI) fun t' h' => ?_
  have e := eval_nonzero_ofNat' t' .r12 (k := n - (j + 1)) (by omega) h'.r12
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], k t' (he ▸ h')⟩
  · right; exact ⟨by rw [e]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

end VG.Proof.CmacTripleDes.Stream.PPC64LE
