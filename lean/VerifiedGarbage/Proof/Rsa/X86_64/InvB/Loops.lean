module
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA's inverse by divsteps on x86-64: the loops over the words

The bases of the inverse's arrays from its window (`wa_ok`), and its loops at
the width read at run time: a copy (`cp_ok`), the arithmetic shift by 59
(`shr_ok`) and the signed linear combination (`lin_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A sequence of two nonempty sequences. -/
theorem seqs_append_iff : ∀ (cs ds : List (Prog isa)), cs ≠ [] → ds ≠ [] → ∀ (s : State) (Q : State → Prop),
    WP isa (seqs (cs ++ ds)) s Q ↔ WP isa (seqs cs) s fun t => WP isa (seqs ds) t Q
  | [], _, h, _, _, _ => absurd rfl h
  | [c], d :: ds, _, _, s, Q => by
    show WP isa (.seq c (seqs (d :: ds))) s Q ↔ _
    rw [WP.seq_iff]; rfl
  | c :: c' :: cs, ds, _, hd, s, Q => by
    show WP isa (.seq c (seqs (c' :: cs ++ ds))) s Q ↔ WP isa (.seq c (seqs (c' :: cs))) s _
    rw [WP.seq_iff, WP.seq_iff]
    exact ⟨fun h => WP.mono h fun t ht => (seqs_append_iff (c' :: cs) ds (by simp) hd t Q).mp ht,
      fun h => WP.mono h fun t ht => (seqs_append_iff (c' :: cs) ds (by simp) hd t Q).mpr ht⟩
  | [_], [], _, hd, _, _ => absurd rfl hd

/-- `wa k r`: `r := rdi + k · r9`, from `rdi` at array `j`'s base: array `j + k`'s. -/
theorem wa_ok {s : State} {B : Addr} {w j : Nat} (k : Nat) {r : Reg} (hr' : r ≠ .r9)
    (hdi : s.gpr .rdi = off B (slot w j)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (wa k r)) s fun t =>
      t.gpr r = off B (slot w (j + k)) ∧ t.mem = s.mem ∧ Keep [r] s t := by
  unfold wa
  rw [WP.block_append_iff]
  have e₀ : WP isa (.block [.mov r (.reg .rdi)]) s
      fun (t₁ : State) => t₁.gpr r = off B (slot w (j + 0)) ∧ t₁.mem = s.mem ∧ Keep [r] s t₁ := by
    xrun [hdi]
    exact ⟨rfl, only_of (fun r' h => by simp [setReg_gpr, h]) rfl rfl⟩
  refine WP.mono e₀ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
  have h9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr (by simp [hr'.symm])).trans h9
  suffices ∀ n, ∀ t, t.gpr r = off B (slot w (j + (k - n))) → t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) →
      n ≤ k → WP isa (.block (List.replicate n (.alu .add r (.reg .r9)))) t fun t' =>
        t'.gpr r = off B (slot w (j + k)) ∧ t'.mem = t.mem ∧ Keep [r] t t' by
    refine WP.mono (this k t₁ (by rw [Nat.sub_self]; exact h₁) h9₁ (Nat.le_refl _))
      fun t ⟨h, m, k'⟩ => ⟨h, m.trans m₁, (k₁.trans k').mono (by simp)⟩
  intro n
  induction n with
  | zero => intro t h _ _; exact WP.block_nil ⟨by rwa [Nat.sub_zero] at h, rfl, Keep.refl _ _⟩
  | succ n ih =>
    intro t h h9t hn
    rw [List.replicate_succ, show (Instr.alu .add r (.reg .r9) :: List.replicate n (.alu .add r (.reg .r9))) =
      [.alu .add r (.reg .r9)] ++ List.replicate n (.alu .add r (.reg .r9)) from rfl, WP.block_append_iff]
    have e₁ : WP isa (.block [.alu .add r (.reg .r9)]) t
        fun (t₁ : State) => t₁.gpr r = off B (slot w (j + (k - n))) ∧ t₁.mem = t.mem ∧ Keep [r] t t₁ := by
      xrun [h, h9t]
      refine ⟨?_, only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
      rw [add_r9 _ B w (j + (k - (n + 1))) rfl, show j + (k - (n + 1)) + 1 = j + (k - n) by omega_using [hn]]
    refine WP.mono e₁ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
    refine WP.mono (ih t₁ h₁ ((k₁.gpr (by simp [hr'.symm])).trans h9t) (by omega_using [hn]))
      fun t' ⟨h', m', k'⟩ => ⟨h', m'.trans m₁, (k₁.trans k').mono (by simp)⟩

/-! ## A copy -/

/-- After `j` words of a copy from `eS` to `eD`. -/
structure CpInv (s₀ : State) (B : Addr) (Z eS eD : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eD (8 * j) s₀.mem t.mem
  val : wv t.mem B eD j = wv s₀.mem B eS j

theorem addrD {b i p : Addr} {e j d : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (Int.ofNat d) = off p (e + d + 8 * j) := by
  subst hb hi
  rw [ofNat_mul8, ofInt_ofNat, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2
  omega

theorem cpStep_ok {s₀ : State} {B : Addr} {Z w eS eD d : Nat} {a b : Reg}
    (ha : s₀.gpr a = off B eS) (hb : s₀.gpr b = off B eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (har : a ∉ [Reg.rax, .r14]) (hbr : b ∉ [Reg.rax, .r14]) (_hw : w < 2 ^ 32)
    (hS : eS + d + 8 * w ≤ Z) (hD : eD + 8 * w ≤ Z) (sp : eD + 8 * w ≤ eS + d ∨ eS + d + 8 * w ≤ eD)
    {j : Nat} (hj : j < w) {t : State} (hI : CpInv s₀ B Z (eS + d) eD j t) :
    WP isa (.block (([.mov .rax (.mem (ix a .r14 (Int.ofNat d))), .store (ix b .r14) .rax] : List Instr) ++
      ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ CpInv s₀ B Z (eS + d) eD (j + 1) t' := by
  have hn := hI.scr.nowrap
  have ta : t.gpr a = off B eS := (hI.keep.gpr har).trans ha
  have tb : t.gpr b = off B eD := (hI.keep.gpr hbr).trans hb
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eS + d + 8 * j) = word s₀.mem B (eS + d + 8 * j) :=
    hI.out.word (by omega_using [sp, hj]) (by omega_using [hS, hj, hn])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eD + 8 * j)) (word t.mem B (eS + d + 8 * j))) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · have hbA : ¬ b = .rax := fun h => hbr (by simp [h])
    xrun [State.ea, ix, hbA, addrD ta hI.r14, addr0 tb hI.r14,
      hI.scr.ld (show eS + d + 8 * j + 8 ≤ Z by omega_using [hS, hj]),
      hI.scr.st (show eD + 8 * j + 8 ≤ Z by omega_using [hD, hj])]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_using [hD, hj, hn]) (by omega_using [hD, hn]))
    fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [hD, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [hD, hj, hn]), hI.val, hx]
    rfl

/-- `wordLoop 0` of a copy: the `N` words at `eS + d` to `eD`. -/
theorem cp_ok {s : State} {B : Addr} {Z N eS eD d : Nat} {a b : Reg} (hs : Scr s B Z)
    (ha : s.gpr a = off B eS) (hb : s.gpr b = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (har : a ∉ [Reg.rax, .r14]) (hbr : b ∉ [Reg.rax, .r14]) (hN : 1 ≤ N) (hN' : N < 2 ^ 31)
    (hS : eS + d + 8 * N ≤ Z) (hD : eD + 8 * N ≤ Z) (sp : eD + 8 * N ≤ eS + d ∨ eS + d + 8 * N ≤ eD) :
    WP isa (wordLoop 0 [.mov .rax (.mem (ix a .r14 (Int.ofNat d))), .store (ix b .r14) .rax]) s fun t =>
      wv t.mem B eD N = wv s.mem B (eS + d) N ∧ Outside B eD (8 * N) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      CpInv s B Z (eS + d) eD 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, rfl⟩
  exact WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_using [hN]) hN' (CpInv s B Z (eS + d) eD) h0
    (fun j _ hj t hI => cpStep_ok ha hb h12 har hbr (by omega_using [hN']) hS hD sp hj hI))
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## The shift by 59 -/

theorem shr59_word (x y : BitVec 64) :
    (x >>> 59 + y <<< 5).toNat = x.toNat / 2 ^ 59 + y.toNat % 2 ^ 59 * 32 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have e : y.toNat * 2 ^ 5 % 2 ^ 64 = y.toNat % 2 ^ 59 * 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 32 from rfl, show (2 : Nat) ^ 5 = 32 from rfl, Nat.mul_mod_mul_right]
  rw [e]
  have : x.toNat / 2 ^ 59 < 32 := by omega
  have : y.toNat % 2 ^ 59 < 2 ^ 59 := Nat.mod_lt _ (by decide)
  omega

/-- After `j` words of `shrBody`: `D_j + 2^(64 j) (T_j / 2^59) = T_{j+1} / 2^59`. -/
structure ShrInv (s₀ : State) (B : Addr) (Z eT eD : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .r8, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eD (8 * j) s₀.mem t.mem
  val : wv t.mem B eD j + 2 ^ (64 * j) * ((word s₀.mem B (eT + 8 * j)).toNat / 2 ^ 59) =
    wv s₀.mem B eT (j + 1) / 2 ^ 59

theorem pow59 (j : Nat) : 2 ^ (64 * (j + 1)) = 2 ^ 59 * (2 ^ (64 * j) * 32) := by
  rw [pow64_succ, show (2 : Nat) ^ 64 = 2 ^ 59 * 32 from rfl]; grind

theorem shrStep_ok {s₀ : State} {B : Addr} {Z w eT eD : Nat}
    (hbx : s₀.gpr .rbx = off B eT) (h10 : s₀.gpr .r10 = off B eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (_hw : w < 2 ^ 32) (hT : eT + 8 * (w + 1) ≤ Z) (hD : eD + 8 * w ≤ Z)
    (sp : eD + 8 * w ≤ eT ∨ eT + 8 * (w + 1) ≤ eD) {j : Nat} (hj : j < w) {t : State}
    (hI : ShrInv s₀ B Z eT eD j t) :
    WP isa (.block (Inv.shrBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ ShrInv s₀ B Z eT eD (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eT := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eD := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hx : word t.mem B (eT + 8 * j) = word s₀.mem B (eT + 8 * j) :=
    hI.out.word (by omega_using [sp, hj]) (by omega_using [hT, hj, hn])
  have hy : word t.mem B (eT + 8 * j + 8) = word s₀.mem B (eT + 8 * j + 8) :=
    hI.out.word (by omega_using [sp, hj]) (by omega_using [hT, hj, hn])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eD + 8 * j))
        (word t.mem B (eT + 8 * j) >>> 59 + word t.mem B (eT + 8 * j + 8) <<< 5)) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · unfold Inv.shrBody
    xrun [State.ea, ix, addr0 tbx hI.r14, addr8 tbx hI.r14, addr0 t10 hI.r14,
      hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega_using [hT, hj]),
      hI.scr.ld (show eT + 8 * j + 8 + 8 ≤ Z by omega_using [hT, hj]),
      hI.scr.st (show eD + 8 * j + 8 ≤ Z by omega_using [hD, hj])]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_using [hD, hj, hn]) (by omega_using [hD, hn]))
    fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [hD, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [hD, hj, hn]), hx, hy, shr59_word]
    have hv := hI.val
    have e1 : wv s₀.mem B eT (j + 1 + 1) = wv s₀.mem B eT (j + 1) +
        2 ^ (64 * (j + 1)) * (word s₀.mem B (eT + 8 * j + 8)).toNat := by
      rw [wv, show eT + 8 * (j + 1) = eT + 8 * j + 8 by omega]
    rw [e1, show eT + 8 * (j + 1) = eT + 8 * j + 8 by omega, pow59 j,
      Nat.mul_assoc (2 ^ 59) (2 ^ (64 * j) * 32) (word s₀.mem B (eT + 8 * j + 8)).toNat,
      Nat.add_mul_div_left _ _ (show 0 < 2 ^ 59 by decide), ← hv]
    have hy' := Nat.div_add_mod (word s₀.mem B (eT + 8 * j + 8)).toNat (2 ^ 59)
    grind

theorem shrLoop_ok {s : State} {B : Addr} {Z N eT eD : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eT) (h10 : s.gpr .r10 = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hT : eT + 8 * (N + 1) ≤ Z) (hD : eD + 8 * N ≤ Z)
    (sp : eD + 8 * N ≤ eT ∨ eT + 8 * (N + 1) ≤ eD) :
    WP isa (wordLoop 0 Inv.shrBody) s fun t =>
      wv t.mem B eD N + 2 ^ (64 * N) * ((word s.mem B (eT + 8 * N)).toNat / 2 ^ 59) =
        wv s.mem B eT (N + 1) / 2 ^ 59 ∧ t.gpr .r14 = BitVec.ofNat 64 N ∧
      Outside B eD (8 * N) s.mem t.mem ∧ Keep [.rax, .r8, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      ShrInv s B Z eT eD 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      simp [wv]⟩
  exact WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_using [hN]) hN' (ShrInv s B Z eT eD) h0
    (fun j _ hj t hI => shrStep_ok hbx h10 h12 (by omega_using [hN']) hT hD sp hj hI))
    fun t hI => ⟨hI.val, hI.r14, hI.out, hI.keep⟩

/-- The sign word of a number whose top word is `x`. -/
def signW (x : BitVec 64) : Nat := if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0

theorem maskOf_toNat (x : BitVec 64) :
    (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63).toNat = signW x := by
  unfold signW
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 from rfl]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [h, ↓reduceIte, show x.toNat / 2 ^ 63 = 1 by omega]
  · simp only [h, ↓reduceIte, show x.toNat / 2 ^ 63 = 0 by omega]

theorem shr_top {V S n : Nat} (hV : V < 2 ^ (64 * (n + 1))) :
    (V + 2 ^ (64 * (n + 1)) * S) / 2 ^ 59 % 2 ^ (64 * (n + 1)) = V / 2 ^ 59 + 2 ^ (64 * n) * (S % 2 ^ 59 * 32) := by
  have e : 2 ^ (64 * (n + 1)) * S = 2 ^ 59 * (2 ^ (64 * n) * 32 * (S % 2 ^ 59)) +
      2 ^ 59 * (2 ^ (64 * (n + 1)) * (S / 2 ^ 59)) := by
    have := Nat.div_add_mod S (2 ^ 59)
    rw [pow59]
    grind
  rw [e, ← Nat.add_assoc, Nat.add_mul_div_left _ _ (show 0 < 2 ^ 59 by decide),
    Nat.add_mul_div_left _ _ (show 0 < 2 ^ 59 by decide), Nat.add_mul_mod_self_left]
  have h1 : V / 2 ^ 59 < 2 ^ (64 * n) * 32 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [pow59] at hV; grind
  have h2 : S % 2 ^ 59 < 2 ^ 59 := Nat.mod_lt _ (by decide)
  have h3 : 2 ^ (64 * n) * 32 * (S % 2 ^ 59) ≤ 2 ^ (64 * n) * 32 * (2 ^ 59 - 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mod_eq_of_lt (by rw [pow64_succ]; grind)]
  grind

/-- `shr kD`: `[16 + kD] = ([t] + 2^(64 (n + 1)) S) / 2^59` modulo `2^(64 (n + 1))`,
for `[t]`'s sign word `S`. -/
theorem shrP_ok {s : State} {B : Addr} {Z w n kD : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hnw : n ≤ w) (hw : w < 2 ^ 24)
    (hT : slot w 23 + 8 * (w + 2) ≤ Z) (hD : slot w (16 + kD) + 8 * (w + 2) ≤ Z)
    (sp : slot w (16 + kD) + 8 * (w + 2) ≤ slot w 23 ∨ slot w 23 + 8 * (w + 2) ≤ slot w (16 + kD)) :
    WP isa (seqs (Inv.shr kD)) s fun t =>
      wv t.mem B (slot w (16 + kD)) (n + 1) =
        (wv s.mem B (slot w 23) (n + 1) + 2 ^ (64 * (n + 1)) * signW (word s.mem B (slot w 23 + 8 * n))) /
          2 ^ 59 % 2 ^ (64 * (n + 1)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Outside B (slot w (16 + kD)) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.rax, .rbx, .rdx, .r8, .r10, .r12, .r14] s t := by
  have hN := hs.nowrap
  simp only [Inv.shr, seqs]
  -- The bases and the count.
  have hb : WP isa (.block (wa 7 .rbx ++ wa kD .r10 ++ ([.mov .r12 (.reg .r15)] : List Instr))) s fun s₃ =>
      s₃.gpr .rbx = off B (slot w 23) ∧ s₃.gpr .r10 = off B (slot w (16 + kD)) ∧
        s₃.gpr .r12 = BitVec.ofNat 64 n ∧ s₃.mem = s.mem ∧ Keep [.rbx, .r10, .r12] s s₃ := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (wa_ok 7 (r := .rbx) (by decide) hdi h9) fun s₁ ⟨b₁, m₁, k₁⟩ => ?_
    refine WP.mono (wa_ok kD (r := .r10) (by decide) ((k₁.gpr (by decide)).trans hdi)
      ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
    have h15₂ : s₂.gpr .r15 = BitVec.ofNat 64 n := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h15)
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 n ∧ t.mem = s₂.mem)
      (by xrun [h15₂]) rfl) fun s₃ ⟨⟨h12₃, m₃⟩, k₃⟩ => ?_
    exact ⟨((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans b₁)), (k₃.gpr (by decide)).trans b₂, h12₃,
      by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₃ ⟨bx₃, b10₃, h12₃, m₃, k₃⟩ => ?_)
  have hs₃ := hs.congr k₃.2.2
  have hw2 : 8 * (n + 1) ≤ 8 * (w + 2) := by omega
  refine WP.seq (WP.mono (shrLoop_ok hs₃ bx₃ b10₃ h12₃ hn (by omega) (by omega_using [hT, hw2])
    (by omega_using [hD, hw2]) (by omega_using [sp, hw2])) fun s₄ ⟨v₄, r14₄, o₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have bx₄ : s₄.gpr .rbx = off B (slot w 23) := (k₄.gpr (by decide)).trans bx₃
  have b10₄ : s₄.gpr .r10 = off B (slot w (16 + kD)) := (k₄.gpr (by decide)).trans b10₃
  have h12₄ : s₄.gpr .r12 = BitVec.ofNat 64 n := (k₄.gpr (by decide)).trans h12₃
  have xT : word s₄.mem B (slot w 23 + 8 * n) = word s.mem B (slot w 23 + 8 * n) := by
    rw [o₄.word (by omega_using [sp, hw2]) (by omega_using [hT, hw2, hN]), m₃]
  refine WP.mono (WP.keep [.rax, .rdx, .r8, .r12] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (slot w (16 + kD) + 8 * n))
        (word s₄.mem B (slot w 23 + 8 * n) >>> 59 +
          (BitVec.setWidth 64 (0 : BitVec 32) - word s₄.mem B (slot w 23 + 8 * n) >>> 63) <<< 5) ∧
      t.gpr .r12 = BitVec.ofNat 64 (n + 1)) ?_ rfl) fun t ⟨⟨mt, h12t⟩, kt⟩ => ?_
  · xrun [State.ea, ix, addr0 bx₄ r14₄, addr0 b10₄ r14₄, h12₄,
      hs₄.ld (show slot w 23 + 8 * n + 8 ≤ Z by omega_using [hT, hw2]),
      hs₄.st (show slot w (16 + kD) + 8 * n + 8 ≤ Z by omega_using [hD, hw2])]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
  refine ⟨?_, h12t, ?_, (((k₃.trans k₄).trans kt).mono (by decide))⟩
  · have hV := wv_lt s.mem B (slot w 23) (n + 1)
    rw [shr_top hV,
      mt, wv_writeW_top _ _ _ _ _ (by omega_using [hD, hw2, hN]), shr59_word, maskOf_toNat, xT, Nat.mul_add]
    rw [m₃] at v₄
    omega
  · rw [mt, ← m₃]
    exact (o₄.mono (by omega) (by omega)).trans ((writeW_outside s₄.mem B (d := slot w (16 + kD) + 8 * n) _ (by omega_using [hD, hw2, hN])).mono (by omega) (by omega))

/-! ## The signed linear combination -/

theorem offD (p : Addr) (e d : Nat) : off p e + BitVec.ofInt 64 (d : Int) = off p (e + d) := by
  simp only [off]
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

/-- `add a, lo; adc h, hi` of a product `P = hi:lo`, as numbers, if the sum fits. -/
theorem acc_step (a h : BitVec 64) (P : Nat) (hsum : a.toNat + 2 ^ 64 * h.toNat + P < 2 ^ 128) :
    (a + BitVec.ofNat 64 P).toNat + 2 ^ 64 * (h + BitVec.ofNat 64 (P / 2 ^ 64) +
      BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + (BitVec.ofNat 64 P).toNat)))).toNat =
    a.toNat + 2 ^ 64 * h.toNat + P := by
  have ha := a.isLt
  have hh := h.isLt
  have hd := Nat.div_add_mod P (2 ^ 64)
  have hm : P % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hq : P / 2 ^ 64 < 2 ^ 64 := by omega
  have hc : (BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + P % 2 ^ 64)))).toNat =
      if 2 ^ 64 ≤ a.toNat + P % 2 ^ 64 then 1 else 0 := by split <;> simp [*]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hc,
    Nat.mod_eq_of_lt hq]
  split <;> omega

/-- The `n` words at `d`, each `⊕ k`. -/
def wvM (m : Mem) (p : Addr) (d : Nat) (k : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => wvM m p d k n + 2 ^ (64 * n) * (word m p (d + 8 * n) ^^^ k).toNat

theorem wvM_congr {m m' : Mem} {p : Addr} {d n : Nat} {k : BitVec 64}
    (h : ∀ i < n, word m' p (d + 8 * i) = word m p (d + 8 * i)) : wvM m' p d k n = wvM m p d k n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wvM]; rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- After `j` columns: the stored words and the accumulator `r8` hold
`|u| X' + |v| Y' + A₀` over `j` words, `X'`, `Y'` the words complemented under the masks. -/
structure LinInv (s₀ : State) (B : Addr) (Z eX eY eT eW : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r8, .r13, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  r13 : t.gpr .r13 = 0
  out : Outside B eT (8 * j) s₀.mem t.mem
  val : wv t.mem B eT j + 2 ^ (64 * j) * (t.gpr .r8).toNat =
    (s₀.gpr .rcx).toNat * wvM s₀.mem B eX (word s₀.mem B (eW + oMu)) j +
      (s₀.gpr .rbp).toNat * wvM s₀.mem B eY (word s₀.mem B (eW + oMv)) j + (s₀.gpr .r8).toNat

theorem linStep_ok {s₀ : State} {B : Addr} {Z w eX eY eT eW : Nat}
    (hdi : s₀.gpr .rdi = off B eW) (hbx : s₀.gpr .rbx = off B eX) (h10 : s₀.gpr .r10 = off B eY)
    (h11 : s₀.gpr .r11 = off B eT) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (_hw : w < 2 ^ 32)
    (hcc : (s₀.gpr .rcx).toNat + (s₀.gpr .rbp).toNat ≤ 2 ^ 63)
    (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (hW : eW + 80 ≤ Z)
    (sX : eT + 8 * w ≤ eX ∨ eX + 8 * w ≤ eT) (sY : eT + 8 * w ≤ eY ∨ eY + 8 * w ≤ eT)
    (sW : eT + 8 * w ≤ eW ∨ eW + 80 ≤ eT)
    {j : Nat} (hj : j < w) {t : State} (hI : LinInv s₀ B Z eX eY eT eW j t) :
    WP isa (.block (Inv.linBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ LinInv s₀ B Z eX eY eT eW (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tdi : t.gpr .rdi = off B eW := (hI.keep.gpr (by decide)).trans hdi
  have tbx : t.gpr .rbx = off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eY := (hI.keep.gpr (by decide)).trans h10
  have t11 : t.gpr .r11 = off B eT := (hI.keep.gpr (by decide)).trans h11
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₀.gpr .rcx := hI.keep.gpr (by decide)
  have tbp : t.gpr .rbp = s₀.gpr .rbp := hI.keep.gpr (by decide)
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) :=
    hI.out.word (by omega_using [sX, hj]) (by omega_using [hX, hj, hn])
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) :=
    hI.out.word (by omega_using [sY, hj]) (by omega_using [hY, hj, hn])
  have hmu : word t.mem B (eW + oMu) = word s₀.mem B (eW + oMu) :=
    hI.out.word (by unfold oMu; omega_using [sW, hj]) (by unfold oMu; omega_using [hW, hn])
  have hmv : word t.mem B (eW + oMv) = word s₀.mem B (eW + oMv) :=
    hI.out.word (by unfold oMv; omega_using [sW, hj]) (by unfold oMv; omega_using [hW, hn])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .r8, .r13] (Q := fun t₁ =>
      t₁.gpr .r13 = 0 ∧ ∃ lo : BitVec 64, t₁.mem = t.mem.writeW (off B (eT + 8 * j)) lo ∧
        lo.toNat + 2 ^ 64 * (t₁.gpr .r8).toNat = (t.gpr .r8).toNat +
          (s₀.gpr .rcx).toNat * (word s₀.mem B (eX + 8 * j) ^^^ word s₀.mem B (eW + oMu)).toNat +
          (s₀.gpr .rbp).toNat * (word s₀.mem B (eY + 8 * j) ^^^ word s₀.mem B (eW + oMv)).toNat) ?_ rfl)
    fun t₁ ⟨⟨r13₁, lo, hm, hv⟩, k₁⟩ => ?_
  · unfold Inv.linBody Inv.wm
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, addr0 t11 hI.r14, tdi, hI.r13, tcx, tbp,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
      hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj]),
      hI.scr.st (show eT + 8 * j + 8 ≤ Z by omega_using [hT, hj]), offD,
      hI.scr.ld (show eW + oMu + 8 ≤ Z by unfold oMu; omega_using [hW]),
      hI.scr.ld (show eW + oMv + 8 ≤ Z by unfold oMv; omega_using [hW]), hx, hy, hmu, hmv]
    refine ⟨_, rfl, ?_⟩
    have hr8 := (t.gpr .r8).isLt
    have l1 := (word s₀.mem B (eX + 8 * j) ^^^ word s₀.mem B (eW + oMu)).isLt
    have l2 := (word s₀.mem B (eY + 8 * j) ^^^ word s₀.mem B (eW + oMv)).isLt
    generalize (word s₀.mem B (eX + 8 * j) ^^^ word s₀.mem B (eW + oMu)).toNat = x1 at l1 ⊢
    generalize (word s₀.mem B (eY + 8 * j) ^^^ word s₀.mem B (eW + oMv)).toNat = x2 at l2 ⊢
    have b1 : x1 * (s₀.gpr .rcx).toNat ≤ (2 ^ 64 - 1) * (s₀.gpr .rcx).toNat := Nat.mul_le_mul_right _ (by omega)
    have b2 : x2 * (s₀.gpr .rbp).toNat ≤ (2 ^ 64 - 1) * (s₀.gpr .rbp).toNat := Nat.mul_le_mul_right _ (by omega)
    have e1 := acc_step (t.gpr .r8) 0 (x1 * (s₀.gpr .rcx).toNat) (by
      rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
    have e2 := acc_step (t.gpr .r8 + BitVec.ofNat 64 (x1 * (s₀.gpr .rcx).toNat))
      (0 + BitVec.ofNat 64 (x1 * (s₀.gpr .rcx).toNat / 2 ^ 64) + BitVec.setWidth 64 (BitVec.ofBool
        (decide (2 ^ 64 ≤ (t.gpr .r8).toNat + (BitVec.ofNat 64 (x1 * (s₀.gpr .rcx).toNat)).toNat))))
      (x2 * (s₀.gpr .rbp).toNat) (by rw [e1, show (0 : BitVec 64).toNat = 0 from rfl]; omega)
    rw [e2, e1, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_comm x1, Nat.mul_comm x2]
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_using [hT, hj, hn]) (by omega_using [hT, hn]))
    fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    (k'.gpr (by decide)).trans r13₁, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [hT, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [hT, hj, hn]), (k'.gpr (by decide) : t'.gpr .r8 = _)]
    simp only [wvM]
    have hv0 := hI.val
    rw [pow64_succ]
    have e : 2 ^ (64 * j) * (lo.toNat + 2 ^ 64 * (t₁.gpr .r8).toNat) = 2 ^ (64 * j) * ((t.gpr .r8).toNat +
        (s₀.gpr .rcx).toNat * (word s₀.mem B (eX + 8 * j) ^^^ word s₀.mem B (eW + oMu)).toNat +
        (s₀.gpr .rbp).toNat * (word s₀.mem B (eY + 8 * j) ^^^ word s₀.mem B (eW + oMv)).toNat) := by rw [hv]
    grind

/-- `wordLoop 0 linBody` over `N` columns. -/
theorem linLoop_ok {s : State} {B : Addr} {Z N eX eY eT eW : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B eW) (hbx : s.gpr .rbx = off B eX) (h10 : s.gpr .r10 = off B eY)
    (h11 : s.gpr .r11 = off B eT) (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (h13 : s.gpr .r13 = 0)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hcc : (s.gpr .rcx).toNat + (s.gpr .rbp).toNat ≤ 2 ^ 63)
    (hX : eX + 8 * N ≤ Z) (hY : eY + 8 * N ≤ Z) (hT : eT + 8 * N ≤ Z) (hW : eW + 80 ≤ Z)
    (sX : eT + 8 * N ≤ eX ∨ eX + 8 * N ≤ eT) (sY : eT + 8 * N ≤ eY ∨ eY + 8 * N ≤ eT)
    (sW : eT + 8 * N ≤ eW ∨ eW + 80 ≤ eT) :
    WP isa (wordLoop 0 Inv.linBody) s fun t =>
      wv t.mem B eT N + 2 ^ (64 * N) * (t.gpr .r8).toNat =
        (s.gpr .rcx).toNat * wvM s.mem B eX (word s.mem B (eW + oMu)) N +
          (s.gpr .rbp).toNat * wvM s.mem B eY (word s.mem B (eW + oMv)) N + (s.gpr .r8).toNat ∧
      Outside B eT (8 * N) s.mem t.mem ∧ Keep [.rax, .rdx, .r8, .r13, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      LinInv s B Z eX eY eT eW 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, (k.gpr (by decide)).trans h13,
      by rw [hm]; exact Outside.refl _ _ _ _, by simp [wv, wvM, (k.gpr (by decide) : t.gpr .r8 = _)]⟩
  exact WP.mono (wordLoop_ok (start := 0) (N := N) (by omega_using [hN]) hN' (LinInv s B Z eX eY eT eW) h0
    (fun j _ hj t hI => linStep_ok hdi hbx h10 h11 h12 (by omega_using [hN']) hcc hX hY hT hW sX sY sW hj hI))
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ### Absolute values and masks -/

theorem abs_word (x : BitVec 64) :
    (x ^^^ (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63)) - (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63) =
      BitVec.ofNat 64 x.toInt.natAbs ∧
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (x.toInt < 0)) := by
  have hx := x.isLt
  have hm := maskOf_toNat x
  unfold signW at hm
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; simp only [h, ↓reduceIte]; rfl
    have ht : x.toInt = (x.toNat : Int) - 2 ^ 64 := by
      rw [BitVec.toInt_eq_toNat_cond]; simp only [show ¬ (2 * x.toNat < 2 ^ 64) by omega, ↓reduceIte]; omega
    have hn : x.toInt.natAbs = 2 ^ 64 - x.toNat := by rw [ht]; omega
    rw [e, hn, show decide (x.toInt < 0) = true by rw [ht]; simp; omega, mask_true]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    omega
  · have e : BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; simp only [h, ↓reduceIte]; rfl
    have ht : x.toInt = (x.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; simp only [show 2 * x.toNat < 2 ^ 64 by omega, ↓reduceIte]
    rw [e, ht, show decide ((x.toNat : Int) < 0) = false by simp, mask_false]
    refine ⟨?_, rfl⟩
    show (x ^^^ 0#64) - 0#64 = _
    rw [BitVec.xor_zero, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Int.natAbs_natCast, Nat.mod_eq_of_lt hx]

/-- `absM c m a`: `a = |[c]|` (the word as a signed number), the mask of its sign into `[m]`. -/
theorem absM_ok {s : State} {B : Addr} {Z eW c m : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (hc : eW + c + 8 ≤ Z) (hm : eW + m + 8 ≤ Z) {a : Reg} (ha : a = .rcx ∨ a = .rbp) :
    WP isa (.block (Inv.absM c m a)) s fun t =>
      t.gpr a = BitVec.ofNat 64 (word s.mem B (eW + c)).toInt.natAbs ∧
      t.mem = s.mem.writeW (off B (eW + m)) (mask (decide ((word s.mem B (eW + c)).toInt < 0))) ∧
      Keep [.rax, .rdx, a] s t := by
  obtain ⟨e1, e2⟩ := abs_word (word s.mem B (eW + c))
  rcases ha with rfl | rfl
  · refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t =>
      t.gpr .rcx = BitVec.ofNat 64 (word s.mem B (eW + c)).toInt.natAbs ∧
      t.mem = s.mem.writeW (off B (eW + m)) (mask (decide ((word s.mem B (eW + c)).toInt < 0)))) ?_ rfl)
      fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
    unfold Inv.absM Inv.wm
    xrun [State.ea, hdi, offD, hs.ld hc, hs.st hm, e1, e2]
    rw [← e2]; exact e1
  · refine WP.mono (WP.keep [.rax, .rdx, .rbp] (Q := fun t =>
      t.gpr .rbp = BitVec.ofNat 64 (word s.mem B (eW + c)).toInt.natAbs ∧
      t.mem = s.mem.writeW (off B (eW + m)) (mask (decide ((word s.mem B (eW + c)).toInt < 0)))) ?_ rfl)
      fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
    unfold Inv.absM Inv.wm
    xrun [State.ea, hdi, offD, hs.ld hc, hs.st hm, e1, e2]
    rw [← e2]; exact e1

/-! ### The combination as signed numbers -/

theorem wvM_mask (m : Mem) (p : Addr) (d : Nat) (c : Bool) :
    ∀ N, wvM m p d (mask c) N = if c then 2 ^ (64 * N) - 1 - wv m p d N else wv m p d N
  | 0 => by cases c <;> rfl
  | N + 1 => by
    have ih := wvM_mask m p d c N
    have hl := wv_lt m p d N
    have hx := (word m p (d + 8 * N)).isLt
    cases c
    · have ih' : wvM m p d (mask false) N = wv m p d N := by rw [ih]; rfl
      show wvM m p d (mask false) N + 2 ^ (64 * N) * (word m p (d + 8 * N) ^^^ mask false).toNat =
        wv m p d N + 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat
      rw [ih', mask_false, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_zero]
    · have ih' : wvM m p d (mask true) N = 2 ^ (64 * N) - 1 - wv m p d N := by rw [ih]; rfl
      show wvM m p d (mask true) N + 2 ^ (64 * N) * (word m p (d + 8 * N) ^^^ mask true).toNat =
        2 ^ (64 * (N + 1)) - 1 - (wv m p d N + 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat)
      rw [ih', mask_true, BitVec.xor_allOnes, BitVec.toNat_not, pow64_succ, Nat.mul_sub, Nat.mul_sub,
        Nat.mul_one]
      have h1 : 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat ≤ 2 ^ (64 * N) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hq : 2 ^ (64 * N) * (2 ^ 64 - 1) = 2 ^ (64 * N) * 2 ^ 64 - 2 ^ (64 * N) := Nat.mul_sub_one _ _
      have h2 : 1 ≤ 2 ^ (64 * N) := Nat.one_le_two_pow
      have := Nat.mul_le_mul_left (2 ^ (64 * N)) (show 1 ≤ 2 ^ 64 by decide)
      omega

/-- `|u| X' + (|u| if u < 0)` for `X'` the words of `X` complemented under the mask of
`u < 0`: `u X` modulo `2^(64 N)`. -/
theorem lin_term (m : Mem) (p : Addr) (d N : Nat) (u : Int) :
    ((u.natAbs * wvM m p d (mask (decide (u < 0))) N + (if u < 0 then u.natAbs else 0) : Nat) : Int) %
        2 ^ (64 * N) = (u * wv m p d N) % 2 ^ (64 * N) := by
  rw [wvM_mask]
  have hl := wv_lt m p d N
  by_cases h : u < 0
  · simp only [h, decide_true, ↓reduceIte]
    have e : u.natAbs * (2 ^ (64 * N) - 1 - wv m p d N) + u.natAbs + u.natAbs * wv m p d N =
        u.natAbs * 2 ^ (64 * N) := by
      rw [← Nat.mul_add_one, ← Nat.mul_add]; congr 1; omega
    have e' := congrArg (fun z : Nat => (z : Int)) e
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e' ⊢
    have hu : (u.natAbs : Int) = -u := by omega
    rw [hu] at e' ⊢
    rw [show -u * ((2 ^ (64 * N) - 1 - wv m p d N : Nat) : Int) + -u = u * wv m p d N + 2 ^ (64 * N) * (-u) by
      grind, Int.add_mul_emod_self_left]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Int.natCast_mul]
    rw [show (u.natAbs : Int) = u by omega]

/-- The window's masks and the accumulator's start: `r8 = (|u| & mu) + (|v| & mv)`, `r13 = 0`. -/
theorem linInit_ok {s : State} {B : Addr} {Z eW : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (hW : eW + 80 ≤ Z) :
    WP isa (.block ([.mov .r8 (.reg .rcx), .alu .and .r8 (.mem (Inv.wm oMu)), .mov .rax (.reg .rbp),
      .alu .and .rax (.mem (Inv.wm oMv)), .alu .add .r8 (.reg .rax), .mov32 .r13 (.imm 0)] : List Instr)) s fun t =>
      t.gpr .r8 = (s.gpr .rcx &&& word s.mem B (eW + oMu)) + (s.gpr .rbp &&& word s.mem B (eW + oMv)) ∧
      t.gpr .r13 = 0 ∧ t.mem = s.mem ∧ Keep [.rax, .r8, .r13] s t := by
  refine WP.mono (WP.keep [.rax, .r8, .r13] (Q := fun t =>
      t.gpr .r8 = (s.gpr .rcx &&& word s.mem B (eW + oMu)) + (s.gpr .rbp &&& word s.mem B (eW + oMv)) ∧
      t.gpr .r13 = 0 ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold Inv.wm
  xrun [State.ea, hdi, offD, hs.ld (show eW + oMu + 8 ≤ Z by unfold oMu; omega),
    hs.ld (show eW + oMv + 8 ≤ Z by unfold oMv; omega)]
  done

/-- `lin cu cv kX kY`: `[t] ≡ u X + v Y` modulo `2^(64 (n + 1))` for the coefficients
`u`, `v` at the window's `cu`, `cv` and `X`, `Y` the arrays `16 + kX`, `16 + kY`. -/
theorem linP_ok {s : State} {B : Addr} {Z w n cu cv kX kY : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (n + 1)) (hnw : n ≤ w) (hw : w < 2 ^ 24)
    (hcu : cu + 8 ≤ oMu) (hcv : cv + 8 ≤ oMu) (hW : slot w 16 + 80 ≤ slot w 19)
    (hX : slot w (16 + kX) + 8 * (w + 2) ≤ Z) (hY : slot w (16 + kY) + 8 * (w + 2) ≤ Z)
    (hT : slot w 23 + 8 * (w + 2) ≤ Z)
    (sX : slot w 23 + 8 * (w + 2) ≤ slot w (16 + kX) ∨ slot w (16 + kX) + 8 * (w + 2) ≤ slot w 23)
    (sY : slot w 23 + 8 * (w + 2) ≤ slot w (16 + kY) ∨ slot w (16 + kY) + 8 * (w + 2) ≤ slot w 23)
    (wX : slot w 19 ≤ slot w (16 + kX)) (wY : slot w 19 ≤ slot w (16 + kY)) (wT : slot w 19 ≤ slot w 23)
    (hcc : (word s.mem B (slot w 16 + cu)).toInt.natAbs + (word s.mem B (slot w 16 + cv)).toInt.natAbs ≤ 2 ^ 63) :
    WP isa (seqs (Inv.lin cu cv kX kY)) s fun t =>
      (wv t.mem B (slot w 23) (n + 1) : Int) % 2 ^ (64 * (n + 1)) =
        ((word s.mem B (slot w 16 + cu)).toInt * wv s.mem B (slot w (16 + kX)) (n + 1) +
          (word s.mem B (slot w 16 + cv)).toInt * wv s.mem B (slot w (16 + kY)) (n + 1)) % 2 ^ (64 * (n + 1)) ∧
      Frm B [(slot w 23, 8 * (n + 1)), (slot w 16 + oMu, 16)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r10, .r11, .r13, .r14] s t := by
  have hN := hs.nowrap
  have hw2 : 8 * (n + 1) ≤ 8 * (w + 2) := by omega
  have hZW : slot w 16 + 80 ≤ Z := by omega
  generalize hU : word s.mem B (slot w 16 + cu) = U at hcc ⊢
  generalize hV : word s.mem B (slot w 16 + cv) = V at hcc ⊢
  have hu63 : U.toInt.natAbs ≤ 2 ^ 63 := by omega
  have hv63 : V.toInt.natAbs ≤ 2 ^ 63 := by omega
  -- Words of `m₁` and `m₂`.
  have o₁ : Outside B (slot w 16 + oMu) 8 s.mem (s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))) :=
    writeW_outside _ _ _ (by unfold oMu; omega)
  have o₂ : Outside B (slot w 16 + oMv) 8 (s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))) ((s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))).writeW (off B (slot w 16 + oMv)) (mask (decide (V.toInt < 0)))) :=
    writeW_outside _ _ _ (by unfold oMv; omega)
  have wV : word (s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))) B (slot w 16 + cv) = V := by
    rw [o₁.word (by unfold oMu at hcv ⊢; omega) (by unfold oMu at hcv; omega), hV]
  have wMu : word ((s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))).writeW (off B (slot w 16 + oMv)) (mask (decide (V.toInt < 0)))) B (slot w 16 + oMu) = (mask (decide (U.toInt < 0))) := by
    rw [o₂.word (by unfold oMu oMv; omega) (by unfold oMu; omega)]; exact word_writeW_self _ _ _ _
  have wMv : word ((s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))).writeW (off B (slot w 16 + oMv)) (mask (decide (V.toInt < 0)))) B (slot w 16 + oMv) = (mask (decide (V.toInt < 0))) := word_writeW_self _ _ _ _
  have arrW : ∀ e, slot w 19 ≤ e → e + 8 * (w + 2) ≤ Z → ∀ i < n + 1,
      word ((s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))).writeW (off B (slot w 16 + oMv)) (mask (decide (V.toInt < 0)))) B (e + 8 * i) = word s.mem B (e + 8 * i) := fun e he hz i hi => by
    have : e + 8 * i + 8 ≤ Z := by omega
    rw [o₂.word (by unfold oMv; omega) (by omega), o₁.word (by unfold oMu; omega) (by omega)]
  simp only [Inv.lin, seqs]
  have hb : WP isa (.block (Inv.absM cu oMu .rcx ++ Inv.absM cv oMv .rbp ++
      ([.mov .r8 (.reg .rcx), .alu .and .r8 (.mem (Inv.wm oMu)), .mov .rax (.reg .rbp),
        .alu .and .rax (.mem (Inv.wm oMv)), .alu .add .r8 (.reg .rax), .mov32 .r13 (.imm 0)] : List Instr) ++
      wa kX .rbx ++ wa kY .r10 ++ wa 7 .r11)) s fun s₄ =>
      s₄.gpr .rcx = BitVec.ofNat 64 U.toInt.natAbs ∧ s₄.gpr .rbp = BitVec.ofNat 64 V.toInt.natAbs ∧
      s₄.gpr .r8 = (BitVec.ofNat 64 U.toInt.natAbs &&& (mask (decide (U.toInt < 0)))) + (BitVec.ofNat 64 V.toInt.natAbs &&& (mask (decide (V.toInt < 0)))) ∧
      s₄.gpr .r13 = 0 ∧ s₄.gpr .rbx = off B (slot w (16 + kX)) ∧ s₄.gpr .r10 = off B (slot w (16 + kY)) ∧
      s₄.gpr .r11 = off B (slot w (16 + 7)) ∧ s₄.gpr .rdi = off B (slot w 16) ∧ s₄.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      s₄.mem = ((s.mem.writeW (off B (slot w 16 + oMu)) (mask (decide (U.toInt < 0)))).writeW (off B (slot w 16 + oMv)) (mask (decide (V.toInt < 0)))) ∧ Keep [.rax, .rbx, .rcx, .rdx, .rbp, .r8, .r10, .r11, .r13] s s₄ := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (absM_ok hs hdi (by unfold oMu at hcu; omega) (by unfold oMu; omega) (a := .rcx) (.inl rfl))
      fun s₁ ⟨cx₁, mm₁, k₁⟩ => ?_
    rw [hU] at cx₁ mm₁
    have hdi₁ : s₁.gpr .rdi = off B (slot w 16) := (k₁.gpr (by decide)).trans hdi
    rw [WP.block_append_iff]
    refine WP.mono (absM_ok (hs.congr k₁.2.2) hdi₁ (by unfold oMu at hcv; omega) (by unfold oMv; omega)
      (a := .rbp) (.inr rfl)) fun s₂ ⟨bp₂, mm₂, k₂⟩ => ?_
    rw [mm₁, wV] at bp₂ mm₂
    have hdi₂ : s₂.gpr .rdi = off B (slot w 16) := (k₂.gpr (by decide)).trans hdi₁
    rw [WP.block_append_iff]
    refine WP.mono (linInit_ok (hs.congr (k₂.2.2.trans k₁.2.2)) hdi₂ (by omega)) fun s₃ ⟨r8₃, r13₃, mm₃, k₃⟩ => ?_
    rw [mm₂, wMu, wMv, (k₂.gpr (by decide) : s₂.gpr .rcx = _), cx₁, bp₂] at r8₃
    have h9₃ : s₃.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) :=
      (((k₁.trans k₂).trans k₃).gpr (by decide)).trans h9
    have hdi₃ : s₃.gpr .rdi = off B (slot w 16) := (k₃.gpr (by decide)).trans hdi₂
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok kX (r := .rbx) (by decide) hdi₃ h9₃) fun s₄ ⟨bx₄, mm₄, k₄⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok kY (r := .r10) (by decide) ((k₄.gpr (by decide)).trans hdi₃)
      ((k₄.gpr (by decide)).trans h9₃)) fun s₅ ⟨b10₅, mm₅, k₅⟩ => ?_
    refine WP.mono (wa_ok 7 (r := .r11) (by decide) (((k₄.trans k₅).gpr (by decide)).trans hdi₃)
      (((k₄.trans k₅).gpr (by decide)).trans h9₃)) fun s₆ ⟨b11₆, mm₆, k₆⟩ => ?_
    have k36 := (k₄.trans k₅).trans k₆
    refine ⟨(k36.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans cx₁)),
      (k36.gpr (by decide)).trans ((k₃.gpr (by decide)).trans bp₂), (k36.gpr (by decide)).trans r8₃,
      (k36.gpr (by decide)).trans r13₃, ((k₅.trans k₆).gpr (by decide)).trans bx₄,
      (k₆.gpr (by decide)).trans b10₅, b11₆, (k36.gpr (by decide)).trans hdi₃,
      ((((k₁.trans k₂).trans k₃).trans k36).gpr (by decide)).trans h12, ?_,
      ((((k₁.trans k₂).trans k₃).trans k36)).mono (by decide)⟩
    rw [mm₆, mm₅, mm₄, mm₃, mm₂]
  refine WP.seq (WP.mono hb fun s₄ ⟨cx₄, bp₄, r8₄, r13₄, bx₄, b10₄, b11₄, di₄, h12₄, mm₄, k₄⟩ => ?_)
  rw [show 16 + 7 = 23 from rfl] at b11₄
  have hcc' : (s₄.gpr .rcx).toNat + (s₄.gpr .rbp).toNat ≤ 2 ^ 63 := by
    rw [cx₄, bp₄, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  refine WP.mono (linLoop_ok (hs.congr k₄.2.2) di₄ bx₄ b10₄ b11₄ h12₄ r13₄ (by omega) (by omega) hcc'
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, ho, kt⟩ => ⟨?_, ?_, (k₄.trans kt).mono (by decide)⟩
  · rw [mm₄, wMu, wMv, wvM_congr (arrW _ (by omega) (by omega)), wvM_congr (arrW _ (by omega) (by omega)),
      cx₄, bp₄, r8₄, BitVec.toNat_add, and_mask_toNat, and_mask_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show U.toInt.natAbs < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show V.toInt.natAbs < 2 ^ 64 by omega)] at hv
    have hlt : (if decide (U.toInt < 0) = true then U.toInt.natAbs else 0) +
        (if decide (V.toInt < 0) = true then V.toInt.natAbs else 0) < 2 ^ 64 := by split <;> split <;> omega
    rw [Nat.mod_eq_of_lt hlt] at hv
    have e1 := lin_term s.mem B (slot w (16 + kX)) (n + 1) U.toInt
    have e2 := lin_term s.mem B (slot w (16 + kY)) (n + 1) V.toInt
    simp only [decide_eq_true_eq] at hv
    have hv' := congrArg (fun z : Nat => (z : Int) % 2 ^ (64 * (n + 1))) hv
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int] at hv' e1 e2
    rw [Int.add_mul_emod_self_left] at hv'
    have key : ((↑U.toInt.natAbs * ↑(wvM s.mem B (slot w (16 + kX)) (mask (decide (U.toInt < 0))) (n + 1)) +
        ↑(if U.toInt < 0 then U.toInt.natAbs else 0)) + (↑V.toInt.natAbs * ↑(wvM s.mem B (slot w (16 + kY))
        (mask (decide (V.toInt < 0))) (n + 1)) + ↑(if V.toInt < 0 then V.toInt.natAbs else 0)) : Int) %
        2 ^ (64 * (n + 1)) = (U.toInt * ↑(wv s.mem B (slot w (16 + kX)) (n + 1)) +
          V.toInt * ↑(wv s.mem B (slot w (16 + kY)) (n + 1))) % 2 ^ (64 * (n + 1)) := by
      rw [Int.add_emod, e1, e2, ← Int.add_emod]
    rw [hv', ← key]
    congr 1
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [ho x (by rw [mm₄] at *; exact hx.1), mm₄, o₂ x (by unfold oMu oMv at *; omega),
      o₁ x (by unfold oMu at *; omega)]

/-! ## The Montgomery reduction by a word -/

/-- `N + 1` words: the lowest and the `N` above it. -/
theorem wv_succ_low (m : Mem) (p : Addr) (e : Nat) :
    ∀ N, wv m p e (N + 1) = (word m p e).toNat + 2 ^ 64 * wv m p (e + 8) N
  | 0 => by simp [wv]
  | N + 1 => by
    rw [wv, wv_succ_low m p e N, wv, show e + 8 * (N + 1) = e + 8 + 8 * N by omega, pow64_succ]
    grind

theorem wv_div64 (m : Mem) (p : Addr) (e N : Nat) : wv m p e (N + 1) / 2 ^ 64 = wv m p (e + 8) N := by
  rw [wv_succ_low, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (word m p e).isLt, Nat.zero_add]

/-- A top word plus `S`, modulo its word. -/
theorem top_add {L Q a S : Nat} (hL : L < Q) :
    L + Q * ((a + S) % 2 ^ 64) = (L + Q * a + Q * S) % (Q * 2 ^ 64) := by
  have hQ : 0 < Q := by omega
  rw [Nat.add_assoc, ← Nat.mul_add]
  have h1 : (L + Q * (a + S)) % (Q * 2 ^ 64) = L + Q * ((a + S) % 2 ^ 64) := by
    rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt (show L < Q * 2 ^ 64 by
      have := Nat.mul_le_mul_left Q (show 1 ≤ 2 ^ 64 by decide); omega)]
    rw [Nat.mod_eq_of_lt]
    have : (a + S) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have : Q * ((a + S) % 2 ^ 64) ≤ Q * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : Q * (2 ^ 64 - 1) = Q * 2 ^ 64 - Q := Nat.mul_sub_one _ _
    have := Nat.mul_le_mul_left Q (show 1 ≤ 2 ^ 64 by decide)
    omega
  exact h1.symm

/-- `mred`'s start (after the bases): `rcx = k`, the sign mask to `oMu`, `[t]`'s word
`n + 1` zeroed, the stride to `r13`, `m`'s base to `r9`, `r12 := n`. -/
theorem mredHead_ok {s : State} {B : Addr} {Z eW eT eP n S : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = off B eW)
    (h8 : s.gpr .r8 = off B eT) (h10 : s.gpr .r10 = off B eP) (h9 : s.gpr .r9 = BitVec.ofNat 64 S)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hW : eW + 88 ≤ Z) (hT : eT + 8 * n + 16 ≤ Z) :
    WP isa (.block ([.mov .rax (.mem (at0 .r8)), .mov .rcx (.mem (Inv.wm oMi)), .mul .rcx, .mov .rcx (.reg .rax),
      .mov .rax (.mem (ix .r8 .r15)), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .store (Inv.wm oMu) .rdx, .mov32 .rax (.imm 0), .store (ix .r8 .r15 8) .rax, .mov .r13 (.reg .r9),
      .mov .r9 (.reg .r10), .mov .r12 (.reg .r15)] : List Instr)) s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 ((word s.mem B eT).toNat * (word s.mem B (eW + oMi)).toNat) ∧
      t.mem = (s.mem.writeW (off B (eW + oMu)) (BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (eT + 8 * n) >>> 63)).writeW
        (off B (eT + 8 * n + 8)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      t.gpr .r13 = BitVec.ofNat 64 S ∧ t.gpr .r9 = off B eP ∧ t.gpr .r12 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rcx, .rdx, .r9, .r12, .r13] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .r9, .r12, .r13] (Q := fun t =>
      t.gpr .rcx = BitVec.ofNat 64 ((word s.mem B eT).toNat * (word s.mem B (eW + oMi)).toNat) ∧
      t.mem = (s.mem.writeW (off B (eW + oMu)) (BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (eT + 8 * n) >>> 63)).writeW
        (off B (eT + 8 * n + 8)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      t.gpr .r13 = BitVec.ofNat 64 S ∧ t.gpr .r9 = off B eP ∧ t.gpr .r12 = BitVec.ofNat 64 n) ?_ rfl)
    fun t ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, d, e, k⟩
  unfold Inv.wm
  xrun [State.ea, ix, at0, hdi, offD, addr0 (b := off B eT) (i := BitVec.ofNat 64 n) rfl rfl,
    addr8 (b := off B eT) (i := BitVec.ofNat 64 n) rfl rfl, h9, h10, h15,
    h8, show off B eT + BitVec.ofInt 64 0 = off B eT by rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
    hs.ld (show eT + 8 ≤ Z by omega), hs.ld (show eW + oMi + 8 ≤ Z by unfold oMi; omega),
    hs.ld (show eT + 8 * n + 8 ≤ Z by omega), hs.st (show eW + oMu + 8 ≤ Z by unfold oMu; omega),
    hs.st (show eT + 8 * n + 8 + 8 ≤ Z by omega)]
  done

/-- `mred kD`: `[16 + kD] = ([t] + 2^(64 (n + 1)) S + k m) / 2^64` (modulo `2^(64 (n + 2))`
before the division) for `[t]`'s sign word `S`, `m = [aP]` and `k = [t]₀ (-m⁻¹) mod 2^64`. -/
theorem mredP_ok {s : State} {B : Addr} {Z w n kD : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h15 : s.gpr .r15 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hnw : n ≤ w) (hw : w < 2 ^ 24) (hw1 : 2 ≤ w)
    (hZ : slot w 26 ≤ Z) (hk : kD = 5 ∨ kD = 6 ∨ kD = 8) :
    WP isa (seqs (Inv.mred kD)) s fun t =>
      wv t.mem B (slot w (16 + kD)) (n + 1) =
        (wv s.mem B (slot w 23) (n + 1) + 2 ^ (64 * (n + 1)) * signW (word s.mem B (slot w 23 + 8 * n)) +
          (word s.mem B (slot w 23)).toNat * (word s.mem B (slot w 16 + oMi)).toNat % 2 ^ 64 *
            wv s.mem B (slot w 25) n) % 2 ^ (64 * (n + 2)) / 2 ^ 64 ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      Frm B [(slot w 23, 8 * (w + 2)), (slot w 16 + oMu, 8), (slot w (16 + kD), 8 * (n + 1))] s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s t := by
  have e16 : slot w 16 = 256 + 16 * (8 * (w + 2)) := by unfold slot hdrBytes; rfl
  have e19 : slot w 19 = 256 + 19 * (8 * (w + 2)) := by unfold slot hdrBytes; rfl
  have e23 : slot w 23 = 256 + 23 * (8 * (w + 2)) := by unfold slot hdrBytes; rfl
  have e25 : slot w 25 = 256 + 25 * (8 * (w + 2)) := by unfold slot hdrBytes; rfl
  have e26 : slot w 26 = 256 + 26 * (8 * (w + 2)) := by unfold slot hdrBytes; rfl
  have hN := hs.nowrap
  have sl : ∀ j, slot w (j + 1) = slot w j + 8 * (w + 2) := fun j => by unfold slot; grind
  have hT : slot w 23 + 8 * (w + 2) ≤ slot w 25 := by rw [sl 24, sl 23]; omega
  have hP : slot w 25 + 8 * (w + 2) ≤ Z := by rw [← sl 25]; exact hZ
  have hW : slot w 16 + 88 ≤ slot w 19 := by rw [sl 18, sl 17, sl 16]; omega
  have fD : (slot w (16 + kD) + 8 * (w + 2) ≤ slot w 23 ∨ slot w 23 + 8 * (w + 2) ≤ slot w (16 + kD)) ∧
      slot w (16 + kD) + 8 * (w + 2) ≤ slot w 25 := by
    rcases hk with rfl | rfl | rfl <;> unfold slot hdrBytes <;> omega
  have fD2 : slot w 19 ≤ slot w (16 + kD) ∧ slot w (16 + kD) + 8 * (w + 2) ≤ Z := by
    rcases hk with rfl | rfl | rfl <;> unfold slot hdrBytes at * <;> omega
  have hw2 : 8 * (n + 2) ≤ 8 * (w + 2) := by omega
  obtain ⟨fDT, fDP⟩ := fD
  obtain ⟨fD19, fDZ⟩ := fD2
  simp only [Inv.mred, seqs]
  -- The bases and the head.
  have hb : WP isa (.block (wa 7 .r8 ++ wa 9 .r10 ++ wa kD .r11 ++
      ([.mov .rax (.mem (at0 .r8)), .mov .rcx (.mem (Inv.wm oMi)), .mul .rcx, .mov .rcx (.reg .rax),
      .mov .rax (.mem (ix .r8 .r15)), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
      .store (Inv.wm oMu) .rdx, .mov32 .rax (.imm 0), .store (ix .r8 .r15 8) .rax, .mov .r13 (.reg .r9),
      .mov .r9 (.reg .r10), .mov .r12 (.reg .r15)] : List Instr))) s fun t =>
      t.gpr .r8 = off B (slot w 23) ∧ t.gpr .r11 = off B (slot w (16 + kD)) ∧
      t.gpr .rcx = BitVec.ofNat 64 ((word s.mem B (slot w 23)).toNat * (word s.mem B (slot w 16 + oMi)).toNat) ∧
      t.mem = (s.mem.writeW (off B (slot w 16 + oMu)) (BitVec.setWidth 64 (0 : BitVec 32) -
        word s.mem B (slot w 23 + 8 * n) >>> 63)).writeW (off B (slot w 23 + 8 * n + 8)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      t.gpr .r13 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r9 = off B (slot w 25) ∧ t.gpr .r12 = BitVec.ofNat 64 n ∧
      t.gpr .rdi = off B (slot w 16) ∧ t.gpr .r15 = BitVec.ofNat 64 n ∧
      Keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok 7 (r := .r8) (by decide) hdi h9) fun s₁ ⟨b₁, m₁, k₁⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok 9 (r := .r10) (by decide) ((k₁.gpr (by decide)).trans hdi)
      ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok kD (r := .r11) (by decide) (((k₁.trans k₂).gpr (by decide)).trans hdi)
      (((k₁.trans k₂).gpr (by decide)).trans h9)) fun s₃ ⟨b₃, m₃, k₃⟩ => ?_
    have k13 := (k₁.trans k₂).trans k₃
    rw [show 16 + 7 = 23 from rfl] at b₁
    rw [show 16 + 9 = 25 from rfl] at b₂
    refine WP.mono (mredHead_ok (hs.congr k13.2.2) (k13.gpr (by decide) |>.trans hdi)
      ((k₃.gpr (by decide) |>.trans (k₂.gpr (by decide))).trans b₁) ((k₃.gpr (by decide)).trans b₂)
      ((k13.gpr (by decide)).trans h9) ((k13.gpr (by decide)).trans h15) (by omega) (by omega))
      fun t ⟨cx, mm, r13, r9, r12, kt⟩ => ?_
    rw [m₃, m₂, m₁] at cx mm
    exact ⟨(kt.gpr (by decide)).trans ((k₃.gpr (by decide) |>.trans (k₂.gpr (by decide))).trans b₁),
      (kt.gpr (by decide)).trans b₃, cx, mm, r13, r9, r12, ((k13.trans kt).gpr (by decide)).trans hdi,
      ((k13.trans kt).gpr (by decide)).trans h15, (k13.trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨r8₁, r11₁, cx₁, mm₁, r13₁, r9₁, r12₁, di₁, h15₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- The sum before the row.
  have oW : Outside B (slot w 16 + oMu) 8 s.mem (s.mem.writeW (off B (slot w 16 + oMu))
      (BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 23 + 8 * n) >>> 63)) :=
    writeW_outside _ _ _ (by unfold oMu; omega)
  have oZ := writeW_outside (s.mem.writeW (off B (slot w 16 + oMu))
      (BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 23 + 8 * n) >>> 63)) B
      (BitVec.setWidth 64 (0 : BitVec 32)) (d := slot w 23 + 8 * n + 8) (by omega)
  have v₁ : wv s₁.mem B (slot w 23) (n + 2) = wv s.mem B (slot w 23) (n + 1) := by
    rw [mm₁, show n + 2 = n + 1 + 1 from rfl, wv, show slot w 23 + 8 * (n + 1) = slot w 23 + 8 * n + 8 by omega,
      word_writeW_self, oZ.wv (Or.inl (by omega)) (by omega), oW.wv (Or.inr (by unfold oMu; omega)) (by omega)]
    rfl
  have p₁ : wv s₁.mem B (slot w 25) n = wv s.mem B (slot w 25) n := by
    rw [mm₁, oZ.wv (Or.inr (by omega)) (by omega), oW.wv (Or.inr (by unfold oMu; omega)) (by omega)]
  have k64 : (s₁.gpr .rcx).toNat = (word s.mem B (slot w 23)).toNat * (word s.mem B (slot w 16 + oMi)).toNat % 2 ^ 64 := by
    rw [cx₁, BitVec.toNat_ofNat]
  have hW1 := wv_lt s.mem B (slot w 23) (n + 1)
  have hp1 := wv_lt s.mem B (slot w 25) n
  have hk1 : (s₁.gpr .rcx).toNat < 2 ^ 64 := (s₁.gpr .rcx).isLt
  have hkp : (s₁.gpr .rcx).toNat * wv s.mem B (slot w 25) n < 2 ^ (64 * (n + 1)) := by
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add, Nat.mul_comm (2 ^ (64 * n))]
    exact Nat.mul_lt_mul_of_lt_of_lt hk1 hp1
  have hQ : 2 ^ (64 * (n + 2)) = 2 ^ (64 * (n + 1)) * 2 ^ 64 := pow64_succ (n + 1)
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ r8₁ r9₁ r12₁ hn (by omega) (by omega) (by omega) (by omega) (by
    rw [v₁, p₁, hQ]
    have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) (show 2 ≤ 2 ^ 64 by decide)
    omega)) fun s₂ ⟨v₂, o₂, k₂⟩ => ?_)
  rw [v₁, p₁] at v₂
  have hs₂ := hs₁.congr k₂.2.2
  have r8₂ : s₂.gpr .r8 = off B (slot w 23) := (k₂.gpr (by decide)).trans r8₁
  have r15₂ : s₂.gpr .r15 = BitVec.ofNat 64 n := (k₂.gpr (by decide)).trans h15₁
  have di₂ : s₂.gpr .rdi = off B (slot w 16) := (k₂.gpr (by decide)).trans di₁
  have r13₂ : s₂.gpr .r13 = BitVec.ofNat 64 (8 * (w + 2)) := (k₂.gpr (by decide)).trans r13₁
  have r12₂ : s₂.gpr .r12 = BitVec.ofNat 64 n := (k₂.gpr (by decide)).trans r12₁
  have wS : word s₂.mem B (slot w 16 + oMu) =
      BitVec.setWidth 64 (0 : BitVec 32) - word s.mem B (slot w 23 + 8 * n) >>> 63 := by
    rw [o₂.word (Or.inl (by unfold oMu; omega)) (by unfold oMu; omega), mm₁,
      oZ.word (Or.inl (by unfold oMu; omega)) (by unfold oMu; omega)]
    exact word_writeW_self _ _ _ _
  -- The sign word added at the top.
  refine WP.seq (WP.mono (WP.keep [.rax, .r9, .r12] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w 23 + 8 * n + 8)) (word s₂.mem B (slot w 23 + 8 * n + 8) +
        word s₂.mem B (slot w 16 + oMu)) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r12 = BitVec.ofNat 64 (n + 1)) (by
        unfold Inv.wm
        xrun [State.ea, ix, di₂, offD, addr8 r8₂ r15₂, r13₂, r12₂,
          hs₂.ld (show slot w 23 + 8 * n + 8 + 8 ≤ Z by omega), hs₂.st (show slot w 23 + 8 * n + 8 + 8 ≤ Z by omega),
          hs₂.ld (show slot w 16 + oMu + 8 ≤ Z by unfold oMu; omega)]
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]) rfl)
    fun s₃ ⟨⟨mm₃, r9₃, r12₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have k23 := k₂.trans k₃
  refine WP.mono (cp_ok (d := 8) hs₃ ((k23.gpr (by decide)).trans r8₁) ((k23.gpr (by decide)).trans r11₁) r12₃
    (by decide) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t ⟨vt, ot, kt⟩ => ⟨?_, (kt.gpr (by decide)).trans r9₃, (kt.gpr (by decide)).trans r12₃, ?_,
      (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩
  · have oT := writeW_outside s₂.mem B (word s₂.mem B (slot w 23 + 8 * n + 8) + word s₂.mem B (slot w 16 + oMu))
      (d := slot w 23 + 8 * n + 8) (by omega)
    have h3 : wv s₃.mem B (slot w 23) (n + 1 + 1) = wv s₂.mem B (slot w 23) (n + 1) +
        2 ^ (64 * (n + 1)) * (((word s₂.mem B (slot w 23 + 8 * n + 8)).toNat +
          signW (word s.mem B (slot w 23 + 8 * n))) % 2 ^ 64) := by
      rw [wv, show slot w 23 + 8 * (n + 1) = slot w 23 + 8 * n + 8 by omega, mm₃, word_writeW_self,
        oT.wv (Or.inl (by omega)) (by omega), BitVec.toNat_add, wS, maskOf_toNat]
    have h2 : wv s₂.mem B (slot w 23) (n + 2) = wv s₂.mem B (slot w 23) (n + 1) +
        2 ^ (64 * (n + 1)) * (word s₂.mem B (slot w 23 + 8 * n + 8)).toNat := by
      rw [show n + 2 = n + 1 + 1 from rfl, wv, show slot w 23 + 8 * (n + 1) = slot w 23 + 8 * n + 8 by omega]
    rw [vt, ← wv_div64, h3, top_add (wv_lt _ _ _ _), ← h2, v₂, k64, ← hQ,
      Nat.add_right_comm (wv s.mem B (slot w 23) (n + 1))]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    obtain ⟨xT, xW, xD⟩ := hx
    rw [ot x xD, mm₃, writeW_outside s₂.mem B _ (d := slot w 23 + 8 * n + 8) (by omega) x (by omega),
      o₂ x (by omega), mm₁, oZ x (by omega), oW x (by unfold oMu at *; omega)]

/-- `copyW kS kD`: `n + 1` words from array `16 + kS` to `16 + kD`. -/
theorem copyWP_ok {s : State} {B : Addr} {Z w n kS kD : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = off B (slot w 16)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (n + 1)) (hnw : n ≤ w) (hw : w < 2 ^ 24)
    (hS : slot w (16 + kS) + 8 * (w + 2) ≤ Z) (hD : slot w (16 + kD) + 8 * (w + 2) ≤ Z)
    (sp : slot w (16 + kD) + 8 * (w + 2) ≤ slot w (16 + kS) ∨ slot w (16 + kS) + 8 * (w + 2) ≤ slot w (16 + kD)) :
    WP isa (seqs (Inv.copyW kS kD)) s fun t =>
      wv t.mem B (slot w (16 + kD)) (n + 1) = wv s.mem B (slot w (16 + kS)) (n + 1) ∧
      Outside B (slot w (16 + kD)) (8 * (n + 1)) s.mem t.mem ∧ Keep [.rax, .rbx, .r10, .r14] s t := by
  simp only [Inv.copyW, seqs]
  have hb : WP isa (.block (wa kS .rbx ++ wa kD .r10)) s fun t =>
      t.gpr .rbx = off B (slot w (16 + kS)) ∧ t.gpr .r10 = off B (slot w (16 + kD)) ∧ t.mem = s.mem ∧
        Keep [.rbx, .r10] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (wa_ok kS (r := .rbx) (by decide) hdi h9) fun s₁ ⟨b₁, m₁, k₁⟩ => ?_
    refine WP.mono (wa_ok kD (r := .r10) (by decide) ((k₁.gpr (by decide)).trans hdi)
      ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
    exact ⟨(k₂.gpr (by decide)).trans b₁, b₂, by rw [m₂, m₁], (k₁.trans k₂).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨b₁, b10₁, m₁, k₁⟩ => ?_)
  have hw2 : 8 * (n + 1) ≤ 8 * (w + 2) := by omega
  refine WP.mono (cp_ok (d := 0) (hs.congr k₁.2.2) b₁ b10₁ ((k₁.gpr (by decide)).trans h12) (by decide) (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨v, o, k⟩ => ⟨?_, ?_, (k₁.trans k).mono (by decide)⟩
  · rw [v, m₁]; rfl
  · rw [← m₁]; exact o

end VG.Proof.Rsa.X86_64.InvB
