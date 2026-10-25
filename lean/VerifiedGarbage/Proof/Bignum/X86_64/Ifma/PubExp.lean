module

import VerifiedGarbage.Proof.Framework.OmegaNear
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.PubVec
public import VerifiedGarbage.Proof.Bignum.PdRanges
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Ws
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Win
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# The public operation with AVX512_IFMA on x86-64: the numbers into and out of the area

`setup` (`setup_ok`): from the workspace at `P` (`rdi`), the modulus' limbs
and `k₀` at `B`, the accumulator's array, and `R² mod m`'s limbs into `A`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off writeW_outside slot Frm word_off wv_off)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Rsa.X86_64.PubIfma
open VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem word_stMem_other limbN se_ofNat)
open VG.Proof.Bignum.X86_64 (Scr hdrOff)
open VG.Impl.Bignum (sArr sMinv sW)
open VG.Impl.Bignum.Public (aX aN aAcc aR2 aY aTmp aXm aOne)
open VG.Impl.Bignum.X86_64 (hdr)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- Stores of `rax` at offsets of the base register `b`. -/
theorem stR_ok {b : Reg} {C : Addr} {v : BitVec 64} :
    ∀ (ds : List Nat) (s : State), s.gpr b = C → s.gpr .rax = v →
      (∀ d ∈ ds, InRegions s.wr (C + BitVec.ofNat 64 d) 8) →
      WP isa (.block (ds.map fun d => .store (at_ b d) .rax)) s
        fun s' => s' = { s with mem := stMem s.mem C v ds }
  | [], s, _, _, _ => WP.block_nil rfl
  | d :: rest, s, hC, hv, hw => by
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off C d) v }, ?_, ?_⟩
    · simp only [exec, eaG', hC, hv, State.store64, hw d (List.mem_cons_self ..), ite_true, off]
    · exact WP.mono (stR_ok rest _ hC hv fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => h

/-- The area within the workspace: `k₀` below `R² mod m`'s array. -/
theorem PubOk.area2 (hl : PubOk l) : l.NB + 32 ≤ 16 * (l.W + 2) ∧ 32 ≤ l.W := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- Words of the workspace below `B` through a change from `B + d` on. -/
theorem low_word {P : Addr} {W d n e : Nat} {m m' : Mem} (h : Outside (off P (slot W aAcc)) d n m m')
    (hn : P.toNat + slot W 8 ≤ 2 ^ 64) (hd : d + n ≤ 48 * (W + 2)) (he : e + 8 ≤ slot W aAcc) :
    word m' P e = word m P e := by
  simp only [slot, aAcc, VG.Impl.Bignum.hdrBytes] at *
  have f := Frm.of_outside_off (B := P) h (by omega_near) (by omega_near)
  exact f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_near)) (by omega_near)

/-- `setup`. -/
theorem setup_ok (hl : PubOk l) {a : State} {P : Addr} {Z : Nat} {minv : BitVec 64}
    (hg : VG.Proof.Bignum.X86_64.Good a P Z l.W minv) (hZ : slot l.W 8 ≤ Z) :
    WP isa (.block (setup l)) a fun t =>
      t.gpr .rbx = off P (slot l.W aAcc) ∧ t.gpr .r12 = mask52 ∧
      (∀ j < l.L, word t.mem (off P (slot l.W aAcc)) (0 + l.off j) =
        BitVec.ofNat 64 (limbN (wv a.mem P (slot l.W aN) l.W) j)) ∧
      (∀ i < 4, word t.mem (off P (slot l.W aAcc)) (l.NB + 8 * i) = BitVec.ofNat 64 (minv.toNat % 2 ^ 52)) ∧
      (∀ j < l.L, word t.mem (off P (slot l.W aAcc)) (oA l + l.off j) =
        BitVec.ofNat 64 (limbN (wv a.mem P (slot l.W aR2) l.W) j)) ∧
      Frm P [(slot l.W aAcc, l.NB + 32), (slot l.W aAcc + oA l, l.NB)] a.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rbx, .r12, .rsi, .r11, .rax, .rcx, .rbp] a t ∧ t.mxcsr = a.mxcsr := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  obtain ⟨b1, b2⟩ := hl.area2
  have hoA : oA l = 24 * (l.W + 2) := rfl
  have hs := hg.scr
  have hn : P.toNat + slot l.W 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_near
  have hS8 : slot l.W 8 = slot l.W aAcc + 48 * (l.W + 2) := by unfold slot aAcc; omega_near
  have hSN : slot l.W aN + 8 * (l.W + 2) ≤ slot l.W aAcc := by unfold slot aN aAcc; omega_near
  have hSR : slot l.W aR2 = slot l.W aAcc + 16 * (l.W + 2) := by unfold slot aR2 aAcc; omega_near
  have hHdr : ∀ i < 32, 8 * i + 8 ≤ slot l.W aAcc := fun i hi => VG.Proof.Bignum.hdr_lt_slot l.W aAcc hi
  have hF : ∀ j < l.L, l.off j + 8 ≤ l.NB := fun j hj => off_ltN hl.amm hj
  generalize hB : off P (slot l.W aAcc) = B
  have hBo : ∀ d, off B d = off P (slot l.W aAcc + d) := fun d => by rw [← hB, off_off]
  have hwB : ∀ d, d + 8 ≤ 48 * (l.W + 2) → InRegions a.wr (off B d) 8 := fun d hd => by
    rw [hBo]; exact hs.st (by omega_near)
  have hnB : (oA l + l.NB) ≤ 48 * (l.W + 2) := by omega_near
  have harr : ∀ j, arr l j = slot l.W j := fun _ => rfl
  have hj : ∀ j < 8, arr l j < 2 ^ 31 := fun j hj => by
    have := VG.Proof.Bignum.slot_le (w := l.W) hj
    rw [harr]; unfold slot VG.Impl.Bignum.hdrBytes at *; omega_near
  unfold setup
  simp only [List.append_assoc]
  -- The base and the mask.
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rbx, .r12] (Q := fun t =>
    t.gpr .rbx = B ∧ t.gpr .r12 = mask52 ∧ t.mem = a.mem ∧ t.mxcsr = a.mxcsr) (by
      unfold base
      simp only [List.cons_append, List.nil_append]
      xrun [hg.rdi, se_ofNat (hj aAcc (by decide))]
      and_intros
      all_goals first | rfl | (rw [← hB]; rfl)) rfl) fun t₁ ⟨⟨b₁, r12₁, m₁, x₁⟩, k₁⟩ => ?_
  -- The modulus' limbs.
  rw [WP.block_append_iff]
  have hdi₁ : t₁.gpr .rdi = P := (k₁.gpr (by decide)).trans hg.rdi
  refine WP.mono (ld52_ok hl (s := t₁) (B := B) (H := P) (j := aN) (o := 0) b₁ hdi₁ r12₁ (hj aN (by decide))
    (fun i hi => by rw [k₁.2.1, k₁.2.2, AmmSym.off_add, harr]; exact hs.ld (by omega_near))
    (fun q hq => by rw [k₁.2.2]; exact hwB _ (by have := hF q hq; omega_near)) (by omega_near)
    (fun m m' f i hi => by
      rw [harr, word_off, word_off]
      rw [← hB] at f
      exact low_word f hn (by omega_near) (by omega_near))) fun t₂ ⟨v₂, o₂, k₂, x₂⟩ => ?_
  rw [harr] at v₂
  rw [m₁, VG.Proof.Bignum.wv_off, Nat.add_zero] at v₂
  -- `k₀`.
  rw [WP.block_append_iff]
  have hm₂ : word t₂.mem P (8 * sMinv) = minv := by
    rw [← hB] at o₂
    rw [low_word o₂ hn (by omega_near) (hHdr sMinv (by decide)), m₁]; exact hg.hdr.hminv
  have hdi₂ : t₂.gpr .rdi = P := (k₂.gpr (by decide)).trans hdi₁
  have hl₂ : InRegions (t₂.rd ++ t₂.wr) (off P (8 * sMinv)) 8 := by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hs.ld (by have := hHdr _ (show sMinv < 32 by decide); omega_near)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 (minv.toNat % 2 ^ 52) ∧ t.mem = t₂.mem ∧ t.mxcsr = t₂.mxcsr) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hl₂, hm₂, (k₂.gpr (by decide)).trans r12₁, AmmSym.and_mask']
      all_goals rfl) rfl) fun t₃ ⟨⟨a₃, m₃, x₃⟩, k₃⟩ => ?_
  -- `k₀` into its four quadwords.
  rw [WP.block_append_iff]
  have hb₃ : t₃.gpr .rbx = B := by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact b₁
  have hds : (List.range 4).map (fun i => Instr.store (at_ .rbx (l.NB + 8 * i)) .rax) =
      ((List.range 4).map fun i => l.NB + 8 * i).map fun d => .store (at_ .rbx d) .rax := by
    simp only [List.map_map, Function.comp_def]
  rw [hds]
  refine WP.mono (stR_ok (b := .rbx) _ t₃ hb₃ a₃ fun d hd => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi
    rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hwB _ (by omega_near)) fun t₄ h₄ => ?_
  subst h₄
  generalize hM₄ : stMem t₃.mem B (BitVec.ofNat 64 (minv.toNat % 2 ^ 52))
    ((List.range 4).map fun i => l.NB + 8 * i) = M₄
  have o₄ : Outside B l.NB 32 t₃.mem M₄ := by
    rw [← hM₄]
    refine stMem_outside _ B _ (by omega_near) _ fun d hd => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    rw [List.mem_range] at hi
    omega_near
  have hm₄ : ∀ e, e + 8 ≤ slot l.W aAcc → word M₄ P e = word a.mem P e := fun e he => by
    rw [← hB] at o₄ o₂
    rw [low_word o₄ hn (by omega_near) he, m₃, low_word o₂ hn (by omega_near) he, m₁]
  have hdi₄ : t₃.gpr .rdi = P := (k₃.gpr (by decide)).trans hdi₂
  -- `R² mod m` into `A`.
  refine WP.mono (ld52_ok hl (s := { t₃ with mem := M₄ }) (B := B) (H := P) (j := aR2)
    (o := oA l) hb₃ hdi₄ (by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact r12₁) (hj aR2 (by decide))
    (fun i hi => by
      show InRegions (t₃.rd ++ t₃.wr) _ 8
      rw [k₃.2.1, k₃.2.2, k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2, AmmSym.off_add, harr]; exact hs.ld (by omega_near))
    (fun q hq => by
      show InRegions t₃.wr _ 8
      rw [k₃.2.2, k₂.2.2, k₁.2.2]; exact hwB _ (by have := hF q hq; omega_near)) (by omega_near)
    (fun m m' f i hi => by
      rw [harr, word_off, word_off]
      rw [← hB] at f
      have f' := Frm.of_outside_off (B := P) f (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
      exact f'.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by simp only; omega_near))
        (by unfold slot at *; omega_near))) fun t₅ ⟨v₅, o₅, k₅, x₅⟩ => ?_
  have hR₄ : VG.Proof.Bignum.wv M₄ (off P (arr l aR2)) 0 l.W = VG.Proof.Bignum.wv a.mem P (slot l.W aR2) l.W := by
    rw [wv_off, Nat.add_zero, harr]
    rw [← hB] at o₄ o₂
    have f₄ := Frm.of_outside_off (B := P) o₄ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    have f₂ := Frm.of_outside_off (B := P) o₂ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    rw [f₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only; omega_near))
        (by unfold slot at *; omega_near), m₃,
      f₂.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only; omega_near))
        (by unfold slot at *; omega_near), m₁]
  rw [hR₄] at v₅
  have hlow : ∀ e, e + 8 ≤ oA l → word t₅.mem B e = word M₄ B e := fun e he => o₅.word (.inl he) (by omega_near)
  refine ⟨by rw [k₅.gpr (by decide)]; exact hb₃, by rw [k₅.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact r12₁,
    fun j hj => ?_, fun i hi => ?_, v₅, ?_, ?_, by rw [x₅]; show t₃.mxcsr = _; rw [x₃, x₂, x₁]⟩
  · have := hF j hj
    rw [hlow _ (by omega_near), ← hM₄, word_stMem_other B _ (by omega_near) _ _ (fun d hd => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd; omega_near) (fun d hd => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd; rw [List.mem_range] at hi; omega_near), m₃]
    exact v₂ j hj
  · rw [hlow _ (by omega_near), ← hM₄]
    refine word_stMem B _ _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩) (fun d hd => ?_) (fun d hd => ?_)
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hd
      rw [List.mem_range] at hi'
      by_cases e : i' = i
      · exact .inl (by rw [e])
      · omega_near
    · obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hd; rw [List.mem_range] at hi'; omega_near
  · rw [← hB] at o₂ o₄ o₅
    have f₂ := Frm.of_outside_off (B := P) o₂ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    have f₄ := Frm.of_outside_off (B := P) o₄ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    have f₅ := Frm.of_outside_off (B := P) o₅ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    rw [m₁] at f₂
    rw [m₃] at f₄
    refine ((f₂.append f₄).append f₅).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨_, List.mem_cons_self .., by simp only; omega_near⟩
    · exact ⟨_, List.mem_cons_self .., by simp only; omega_near⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_near⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k₅.gpr (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
        show ({ t₃ with mem := M₄ } : State).gpr r = t₃.gpr r from rfl, k₃.gpr (by simp [hr.2.2.2.2.1]),
        k₂.gpr (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
        k₁.gpr (by simp [hr.1, hr.2.1])]
    · rw [k₅.2.1]; show t₃.rd = _; rw [k₃.2.1, k₂.2.1, k₁.2.1]
    · rw [k₅.2.2]; show t₃.wr = _; rw [k₃.2.2, k₂.2.2, k₁.2.2]

/-! ## Back to words -/

/-- `fin`'s block: `A` into `W + 1` words at the accumulator, and the bases
for the subtraction. -/
theorem finBlock_ok (hl : PubOk l) {s : State} {P : Addr} {Z : Nat} (hs : Scr s P Z)
    (hZ : slot l.W 8 ≤ Z) (hdi : s.gpr .rdi = P)
    (hB : s.gpr .rbx = off P (slot l.W aAcc))
    (hL : ∀ j < l.L, limb l s.mem (off P (slot l.W aAcc)) (oA l) j < 2 ^ 52) :
    WP isa (.block (([.mov .r11 (.reg .rbx), .alu .add .r11 (.imm (BitVec.ofNat 32 (oA l))), .mov .r8 (.reg .rbx)] :
        List Instr) ++ to64 l ++ base l .rbx aY ++ base l .r10 aN ++
      ([.mov32 .r12 (.imm (BitVec.ofNat 32 l.W))] : List Instr) ++ base l .rsi aTmp)) s fun t =>
      (val52 l s.mem (off P (slot l.W aAcc)) (oA l) < 2 * VG.Proof.Bignum.wv s.mem P (slot l.W aN) l.W →
        VG.Proof.Bignum.wv t.mem P (slot l.W aAcc) (l.W + 1) = val52 l s.mem (off P (slot l.W aAcc)) (oA l)) ∧
      Outside P (slot l.W aAcc) (8 * (l.W + 1)) s.mem t.mem ∧
      t.gpr .r8 = off P (slot l.W aAcc) ∧ t.gpr .rbx = off P (slot l.W aY) ∧
      t.gpr .r10 = off P (slot l.W aN) ∧ t.gpr .r12 = BitVec.ofNat 64 l.W ∧
      t.gpr .rsi = off P (slot l.W aTmp) ∧
      VG.Proof.MlKem.X86_64.Keep [.r11, .r8, .rax, .rcx, .rbp, .rbx, .r10, .r12, .rsi] s t := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  have hoA : oA l = 24 * (l.W + 2) := rfl
  have hn : P.toNat + slot l.W 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_near
  have hS8 : slot l.W 8 = slot l.W aAcc + 48 * (l.W + 2) := by unfold slot aAcc; omega_near
  have hHdr : ∀ i < 32, 8 * i + 8 ≤ slot l.W aAcc := fun i hi => VG.Proof.Bignum.hdr_lt_slot l.W aAcc hi
  have hF : ∀ j < l.L, l.off j + 8 ≤ l.NB := fun j hj => off_ltN hl.amm hj
  have hH' : ∀ i < 32, InRegions (s.rd ++ s.wr) (off P (8 * i)) 8 := fun i hi => hs.ld (by have := hHdr i hi; omega_near)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11, .r8] (Q := fun t =>
    t.gpr .r11 = off (off P (slot l.W aAcc)) (oA l) ∧ t.gpr .r8 = off P (slot l.W aAcc) ∧ t.mem = s.mem) (by
    xrun [hB, se_ofNat (show oA l < 2 ^ 31 by omega_near)]
    all_goals rfl) rfl) fun s₁ ⟨⟨r11, r8, me⟩, k₁⟩ => ?_
  have hsep : ∀ m m' : Mem, Outside (off P (slot l.W aAcc)) 0 (8 * (l.W + 1)) m m' → ∀ j < l.L,
      word m' (off (off P (slot l.W aAcc)) (oA l)) (l.off j) = word m (off (off P (slot l.W aAcc)) (oA l)) (l.off j) :=
    fun m m' ho j hj => by
    rw [word_off m' (off P (slot l.W aAcc)) (oA l) (l.off j), word_off m (off P (slot l.W aAcc)) (oA l) (l.off j)]
    have := hF j hj
    exact ho.word (.inr (by omega_near)) (by unfold slot at *; omega_near)
  rw [WP.block_append_iff]
  refine WP.mono (to64_ok r11 r8 (fun j hj => by
      have := hF j hj
      rw [k₁.2.1, k₁.2.2, off_off, AmmSym.off_add]; exact hs.ld (by omega_near))
    (fun w hw => by rw [k₁.2.2, AmmSym.off_add]; exact hs.st (by omega_near))
    (fun j hj => by rw [me, word_off]; exact hL j hj) (by omega_near) hsep) fun s₂ ⟨hw₂, ho₂, k₂, _⟩ => ?_
  have hlv : VG.Proof.Bignum.Amm52.lval (fun j => (limbsAt l s₁.mem (off (off P (slot l.W aAcc)) (oA l)) j).toNat) l.L =
      val52 l s.mem (off P (slot l.W aAcc)) (oA l) := VG.Proof.Bignum.Amm52.lval_congr fun j hj => by
    simp only [limbsAt, hj, ↓reduceIte]
    rw [me, word_off]
  rw [hlv] at hw₂
  rw [me] at ho₂
  have ho₂' : Outside P (slot l.W aAcc) (8 * (l.W + 1)) s.mem s₂.mem :=
    AmmSym.Outside.rebase ho₂ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
  have hh : ∀ i < 32, word s₂.mem P (8 * i) = word s.mem P (8 * i) := fun i hi =>
    ho₂'.word (.inl (hHdr i hi)) (by have := hHdr i hi; omega_near)
  have hdi₂ : s₂.gpr .rdi = P := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact hdi
  have hj : ∀ j < 8, arr l j < 2 ^ 31 := fun j hj => by
    have := VG.Proof.Bignum.slot_le (w := l.W) hj
    show slot l.W j < 2 ^ 31; unfold slot VG.Impl.Bignum.hdrBytes at *; omega_near
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rbx, .r10, .r12, .rsi] (Q := fun t =>
    t.gpr .rbx = off P (slot l.W aY) ∧ t.gpr .r10 = off P (slot l.W aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 l.W ∧ t.gpr .rsi = off P (slot l.W aTmp) ∧ t.mem = s₂.mem) (by
    unfold base
    simp only [List.cons_append, List.nil_append]
    xrun [hdi₂, se_ofNat (hj aY (by decide)), se_ofNat (hj aN (by decide)), se_ofNat (hj aTmp (by decide))]
    and_intros
    all_goals first | rfl | (apply BitVec.eq_of_toNat_eq
                             simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                             have := hl.area.2.2.2.2.2.2.2.2.2.2.2
                             rw [Nat.mod_eq_of_lt (a := l.W) (by omega_near), Nat.mod_eq_of_lt (a := l.W) (by omega_near)])) rfl)
    fun t ⟨⟨bx, r10, r12, si, me₃⟩, k₃⟩ => ?_
  refine ⟨fun hV => ?_, by rw [me₃]; exact ho₂', by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact r8,
    bx, r10, r12, si, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have hacc := wv_to64_lt hV hw₂
  rw [me₃, ← hacc, VG.Proof.Bignum.wv_off]
  rfl


/-- `fin`: `aY := A mod m` for `A < 2 m`. -/
theorem fin_ok (hl : PubOk l) {s : State} {P : Addr} {Z N : Nat} (hs : Scr s P Z)
    (hZ : slot l.W 8 ≤ Z) (hdi : s.gpr .rdi = P)
    (hB : s.gpr .rbx = off P (slot l.W aAcc))
    (hL : ∀ j < l.L, limb l s.mem (off P (slot l.W aAcc)) (oA l) j < 2 ^ 52)
    (hN : VG.Proof.Bignum.wv s.mem P (slot l.W aN) l.W = N) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (fin l)) s fun t =>
      (val52 l s.mem (off P (slot l.W aAcc)) (oA l) < 2 * N →
        VG.Proof.Bignum.wv t.mem P (slot l.W aY) l.W = val52 l s.mem (off P (slot l.W aAcc)) (oA l) % N) ∧
      Frm P [(slot l.W aAcc, 8 * (l.W + 2)), (slot l.W aTmp, 8 * (l.W + 2)), (slot l.W aY, 8 * (l.W + 2))]
        s.mem t.mem ∧ t.gpr .rdi = P ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s t := by
  obtain ⟨b1, b2⟩ := hl.area2
  have a12 := hl.area.2.2.2.2.2.2.2.2.2.2.2
  have hn : P.toNat + slot l.W 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_near
  have lA := VG.Proof.Bignum.slot_le (w := l.W) (show aAcc < 8 by decide)
  have lT := VG.Proof.Bignum.slot_le (w := l.W) (show aTmp < 8 by decide)
  have lY := VG.Proof.Bignum.slot_le (w := l.W) (show aY < 8 by decide)
  have lN := VG.Proof.Bignum.slot_le (w := l.W) (show aN < 8 by decide)
  have sAT := VG.Proof.Bignum.slot_sep (w := l.W) (show aAcc ≠ aTmp by decide)
  have sAY := VG.Proof.Bignum.slot_sep (w := l.W) (show aAcc ≠ aY by decide)
  have sTY := VG.Proof.Bignum.slot_sep (w := l.W) (show aTmp ≠ aY by decide)
  have sTN := VG.Proof.Bignum.slot_sep (w := l.W) (show aTmp ≠ aN by decide)
  have sAN := VG.Proof.Bignum.slot_sep (w := l.W) (show aAcc ≠ aN by decide)
  have hsW : Scr s P (slot l.W 8) := AmmSym.Scr.mono hs hZ
  unfold fin
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (finBlock_ok hl hs hZ hdi hB hL)
    fun s₁ ⟨hacc, ho₁, r8, bx, r10, r12, si, k₁⟩ => ?_)
  have hsW₁ : Scr s₁ P (slot l.W 8) := hsW.congr k₁.2.2
  have hN₁ : VG.Proof.Bignum.wv s₁.mem P (slot l.W aN) l.W = N := by
    rw [ho₁.wv (by rcases sAN with h | h <;> omega_near) (by omega_near)]; exact hN
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.subMod_ok hsW₁ r8 r10 si r12 (by omega_near) (by omega_near)
      (by omega_near) (by omega_near) (by omega_near) (by omega_near) (by omega_near)) fun s₂ ⟨c, lt, hbp, hlt, hD₂, ho₂, k₂⟩ => ?_)
  have hsW₂ := hsW₁.congr k₂.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.selectAcc_ok hsW₂ ((k₂.gpr (by decide)).trans r8)
    ((k₂.gpr (by decide)).trans si) ((k₂.gpr (by decide)).trans bx) ((k₂.gpr (by decide)).trans r12) hbp
    (by omega_near) (by omega_near) (eo := slot l.W aY) (by omega_near) (by omega_near) (by omega_near) (by omega_near) (by omega_near))
    fun t ⟨hv, ho₃, k₃⟩ => ?_
  refine ⟨fun hV => ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · have hacc := hacc (by rw [hN]; exact hV)
    have hA₂ : VG.Proof.Bignum.wv s₂.mem P (slot l.W aAcc) l.W = VG.Proof.Bignum.wv s₁.mem P (slot l.W aAcc) l.W :=
      ho₂.wv (by omega_near) (by omega_near)
    rw [VG.Proof.Bignum.wv] at hacc
    rw [hN₁] at hD₂
    have hX := VG.Proof.Bignum.wv_lt s.mem P (slot l.W aN) l.W
    rw [hN] at hX
    have hDl := VG.Proof.Bignum.wv_lt s₂.mem P (slot l.W aTmp) l.W
    have hTl := VG.Proof.Bignum.wv_lt s₁.mem P (slot l.W aAcc) l.W
    generalize @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) 2 (64 * l.W) = R
      at hacc hD₂ hX hDl hTl
    have hres := VG.Proof.Bignum.X86_64.csub_fin hX hDl hTl (Bool.toNat_le c) hacc hV hD₂
    rw [hv, hA₂, hlt, ← hres]
    by_cases h : (word s₁.mem P (slot l.W aAcc + 8 * l.W)).toNat < c.toNat <;> simp [h]
  · refine ((Frm.of_outside ho₁ (List.mem_singleton_self _)).append ((Frm.of_outside ho₂
      (List.mem_singleton_self _)).append (Frm.of_outside ho₃ (List.mem_singleton_self _)))).widen fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simp only; omega_near⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_near⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp only; omega_near⟩
  · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]; exact hdi

/-! ## The exponentiation by 65537 -/

/-- The modulus' limbs and `k₀` as `setup` leaves them. -/
theorem mod_of (hl : PubOk l) {m : Mem} {B : Addr} {N : Nat} {minv : BitVec 64}
    (hN : ∀ j < l.L, word m B (0 + l.off j) = BitVec.ofNat 64 (limbN N j)) (hNlt : N < 2 ^ (64 * l.W))
    (hk : ∀ i < 4, word m B (l.NB + 8 * i) = BitVec.ofNat 64 (minv.toNat % 2 ^ 52))
    (hinv : (N % 2 ^ 64 * minv.toNat + 1) % 2 ^ 64 = 0) : Mod l m B N (minv.toNat % 2 ^ 52) := by
  obtain ⟨-, -, -, -, -, -, a7, a8, -, -, a11, -⟩ := hl.area
  have hL := (conv_boundsN hl.amm).2.1
  have hNL : N < 2 ^ (52 * l.L) := Nat.lt_of_lt_of_le hNlt (AmmSym.pow2_le hL)
  refine ⟨fun j hj => by simp only [limb]; rw [hN j hj]; exact limbN_lt64 _ _, val52_of hN hNL,
    fun t ht => hk t ht, Nat.mod_lt _ (by decide), ?_, ?_⟩
  · simp only [limb]
    have hl0 : limbN N 0 < 2 ^ 52 := Nat.mod_lt _ (by decide)
    rw [hN 0 (by omega_near), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hl0 (by decide))]
    have h1 : (N % 2 ^ 64 * minv.toNat + 1) % 2 ^ 52 = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide : 52 ≤ 64)) (Nat.dvd_of_mod_eq_zero hinv))
    have e1 : N % 2 ^ 64 % 2 ^ 52 = N % 2 ^ 52 := Nat.mod_mod_of_dvd _ (by decide)
    have e2 : limbN N 0 = N % 2 ^ 52 := by simp [limbN]
    have key : ∀ x y : Nat, (x * y + 1) % 2 ^ 52 = (x % 2 ^ 52 * (y % 2 ^ 52) + 1) % 2 ^ 52 := fun x y => by
      rw [Nat.add_mod, Nat.mul_mod]
      conv => rhs; rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod]
    rw [key, e1] at h1
    rw [e2, key, Nat.mod_mod, Nat.mod_mod]
    exact h1
  · have : 4 * 2 ^ (64 * l.W) ≤ 2 ^ (52 * l.S) := by
      rw [show 4 * 2 ^ (64 * l.W) = 2 ^ (64 * l.W + 2) by rw [Nat.pow_add]; omega_near]
      exact AmmSym.pow2_le (by omega_near)
    omega_near

/-- A change within ranges that a list of ranges covers. -/
theorem Frm.cover {P : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm P rs m m')
    (hc : ∀ x : Nat, (∀ r ∈ rs', x < r.1 ∨ r.1 + r.2 ≤ x) → ∀ r ∈ rs, x < r.1 ∨ r.1 + r.2 ≤ x) :
    Frm P rs' m m' := fun x hx => h x (hc _ hx)

/-- Outside `expAll`: outside arrays 2–3 and 5–7. -/
theorem expAll_blocks {W x : Nat} (hx : ∀ r ∈ VG.Proof.Bignum.expAll W, x < r.1 ∨ r.1 + r.2 ≤ x) :
    (x < slot W aAcc ∨ slot W aAcc + 16 * (W + 2) ≤ x) ∧ (x < slot W aXm ∨ slot W aXm + 24 * (W + 2) ≤ x) := by
  have mem : ∀ j, j = aAcc ∨ j = aTmp ∨ j = aXm ∨ j = aY ∨ j = aOne →
      (slot W j, 8 * (W + 2)) ∈ VG.Proof.Bignum.expAll W := fun j hj => by
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      simp [VG.Proof.Bignum.expAll, VG.Proof.Bignum.pExpRanges, VG.Proof.Bignum.pBitRanges, VG.Proof.Bignum.bitRanges]
  have h2 := hx _ (mem aAcc (by simp))
  have h3 := hx _ (mem aTmp (by simp))
  have h5 := hx _ (mem aXm (by simp))
  have h6 := hx _ (mem aY (by simp))
  have h7 := hx _ (mem aOne (by simp))
  simp only [slot, aAcc, aTmp, aXm, aY, aOne] at *
  omega_near

/-- `exp65537`: `aY := x^65537 mod m` (as `x^(2^16) x`) for the input `x < m`, when `R2 = R² mod m`. -/
theorem exp65537_ok (hl : PubOk l) {a : State} {P : Addr} {Z N X R : Nat} {minv : BitVec 64}
    (hg : VG.Proof.Bignum.X86_64.Good a P Z l.W minv) (hNa : VG.Proof.Bignum.wv a.mem P (slot l.W aN) l.W = N)
    (hinv : ((word a.mem P (slot l.W aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hXa : VG.Proof.Bignum.wv a.mem P (slot l.W aX) l.W = X) (hZ : slot l.W 8 ≤ Z)
    (hR : VG.Proof.Bignum.wv a.mem P (slot l.W aR2) l.W = R) (hRN : R < N) (hodd : N % 2 = 1)
    (hbig : 2 ^ (64 * (l.W - 1)) ≤ N) {ex : Nat} (hex : ex = 65537) :
    WP isa (exp65537 l) a fun d =>
      VG.Proof.Bignum.X86_64.Good d P Z l.W minv ∧
      (X < N → R % N = 2 ^ (64 * l.W) * 2 ^ (64 * l.W) % N →
        VG.Proof.Bignum.wv d.mem P (slot l.W aY) l.W = X ^ ex % N) ∧
      Frm P (VG.Proof.Bignum.expAll l.W) a.mem d.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs a d ∧
      d.mxcsr.extractLsb' 6 10 = a.mxcsr.extractLsb' 6 10 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  obtain ⟨b1, b2⟩ := hl.area2
  have hoA : oA l = 24 * (l.W + 2) := rfl
  have hs := hg.scr
  have hn : P.toNat + slot l.W 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_near
  have hS8 : slot l.W 8 = slot l.W aAcc + 48 * (l.W + 2) := by unfold slot aAcc; omega_near
  have hSX : slot l.W aX + 8 * (l.W + 2) ≤ slot l.W aAcc := by unfold slot aX aAcc; omega_near
  have hSN : slot l.W aN + 8 * (l.W + 2) ≤ slot l.W aAcc := by unfold slot aN aAcc; omega_near
  have hHdr : ∀ i < 32, 8 * i + 8 ≤ slot l.W aAcc := fun i hi => VG.Proof.Bignum.hdr_lt_slot l.W aAcc hi
  have hL := (conv_boundsN hl.amm).2.1
  have hNlt : N < 2 ^ (64 * l.W) := by rw [← hNa]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  have hNL : N < 2 ^ (52 * l.L) := Nat.lt_of_lt_of_le hNlt (AmmSym.pow2_le hL)
  unfold exp65537
  refine AmmSym.wp_seqs_app (a := [.block (setup l), VG.Impl.Rsa.X86_64.PubIfma.vec l]) (b := fin l) (by simp) (by simp [fin]) ?_
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (setup_ok hl hg hZ) fun s₁ ⟨b₁, r12₁, vN, vK, vA, f₁, k₁, x₁⟩ => ?_)
  rw [hNa] at vN
  rw [hR] at vA
  -- Words of the workspace below the area.
  have lo₁ : ∀ e, e + 8 ≤ slot l.W aAcc → word s₁.mem P e = word a.mem P e := fun e he =>
    f₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact .inl (by simp only; omega_near)) (by omega_near)
  have hdi₁ : s₁.gpr .rdi = P := (k₁.gpr (by decide)).trans hg.rdi
  have hxv : VG.Proof.Bignum.wv s₁.mem (off P (slot l.W aX)) 0 l.W = X := by
    rw [wv_off, Nat.add_zero, ← hXa]
    exact VG.Proof.Bignum.wv_congr fun i hi => lo₁ _ (by omega_near)
  have sep : ∀ e, e + 8 ≤ slot l.W aAcc → ∀ m m' : Mem,
      Outside (off P (slot l.W aAcc)) (oA l) (2 * l.NB + 8) m m' → word m' P e = word m P e :=
    fun e he m m' f => low_word f hn (by omega_near) he
  have e : Env l s₁ (off P (slot l.W aAcc)) P (off P (slot l.W aX)) N (minv.toNat % 2 ^ 52) :=
    ⟨(hs.congr k₁.2.2).sub (by omega_near) (by omega_near),
      mod_of hl vN hNlt vK (by
        have := hinv
        rw [← VG.Proof.Bignum.wv_mod64 a.mem P (slot l.W aN) (n := l.W) (by omega_near), hNa] at this
        exact this),
      hodd, by
        have : 2 ^ kb l ≤ 2 ^ (64 * (l.W - 1)) := AmmSym.pow2_le (by omega_near)
        have : 2 ^ kb l < 2 ^ kb l * 2 := by have := Nat.two_pow_pos (kb l); omega_near
        omega_near,
      rfl, by
        have := VG.Proof.Bignum.slot_le (w := l.W) (show aX < 8 by decide)
        show slot l.W aX < 2 ^ 31; unfold slot VG.Impl.Bignum.hdrBytes at *; omega_near,
      fun i hi => by rw [k₁.2.1, k₁.2.2, AmmSym.off_add]; exact hs.ld (by omega_near),
      fun m m' f i hi => by rw [word_off, word_off]; exact sep _ (by omega_near) m m' f⟩
  have hA : ∀ j < l.L, limb l s₁.mem (off P (slot l.W aAcc)) (oA l) j < 2 ^ 52 := fun j hj => by
    simp only [limb]; rw [vA j hj]; exact limbN_lt64 _ _
  have hAv : val52 l s₁.mem (off P (slot l.W aAcc)) (oA l) = R := val52_of vA (by omega_near)
  refine WP.mono (vec_ok hl e b₁ hdi₁ r12₁ hA (by omega_near)) fun s₂ ⟨la₂, vv₂, o₂, k₂, x₂⟩ => ?_
  -- Back to words.
  have lo₂ : ∀ e, e + 8 ≤ slot l.W aAcc → word s₂.mem P e = word a.mem P e := fun e he => by
    rw [sep e he _ _ o₂, lo₁ e he]
  have hN₂ : VG.Proof.Bignum.wv s₂.mem P (slot l.W aN) l.W = N := by
    rw [← hNa]; exact VG.Proof.Bignum.wv_congr fun i hi => lo₂ _ (by omega_near)
  have kk := k₁.trans k₂
  have hfmx : (VG.Impl.Bignum.X86_64.seqs (fin l)).allInstrs (fun i => !loadsMxcsr i) = true := by
    rcases hl with rfl | rfl | rfl <;> decide +kernel
  refine WP.mono_mx hfmx (fin_ok hl (hs.congr kk.2.2) hZ ((k₂.gpr (by decide)).trans hdi₁) ((k₂.gpr (by decide)).trans b₁)
    la₂ hN₂) fun d ⟨vd, fd, rdid, kd⟩ mxd => ?_
  have lod : ∀ e, e + 8 ≤ slot l.W aAcc → word d.mem P e = word a.mem P e := fun e he => by
    rw [fd.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := VG.Proof.Bignum.slot_le (w := l.W) (show aAcc < 8 by decide)
      rcases hr with rfl | rfl | rfl <;> exact .inl (by simp only [slot, aAcc, aTmp, aY] at *; omega_near)) (by omega_near), lo₂ e he]
  refine ⟨⟨hs.congr (kk.trans kd).2.2, rdid, ⟨by rw [lod _ (hHdr _ (by decide))]; exact hg.hdr.hw,
      by rw [lod _ (hHdr _ (by decide))]; exact hg.hdr.hminv,
      fun j hj => by rw [lod _ (hHdr _ (by unfold sArr; omega_near))]; exact hg.hdr.harr j hj⟩⟩, fun hX hq => ?_, ?_,
    (kk.trans kd).mono (by decide), by rw [mxd, x₂, VG.Proof.Bignum.X86_64.mx_ffff, x₁]⟩
  · obtain ⟨lt, cg⟩ := vv₂ (by rw [hxv]; exact hX)
    rw [vd lt, cg (by rw [hAv]; exact hq), hxv]
    have he' : ex = 2 ^ 16 + 1 := hex.trans (by decide)
    generalize (2 : Nat) ^ 16 = E at he' ⊢
    rw [he', Nat.pow_succ]
  · have f₂ := Frm.of_outside_off (B := P) o₂ (by unfold slot at *; omega_near) (by unfold slot at *; omega_near)
    refine ((Frm.cover f₁ fun x hx r hr => ?_).trans (Frm.cover f₂ fun x hx r hr => ?_)).trans
      (Frm.cover fd fun x hx r hr => ?_) <;>
    · have hb := expAll_blocks hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := VG.Proof.Bignum.slot_le (w := l.W) (show aAcc < 8 by decide)
      simp only [slot, aAcc, aTmp, aXm, aY] at *
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_near

end VG.Proof.Bignum.X86_64.Ifma.Pub
