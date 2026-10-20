module

public import VerifiedGarbage.Impl.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.MontBase

/-! # Correct masks for arbitrary-width DSA components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Impl.Dsa.X86

theorem or_eq_zero32 (x y : BitVec 32) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun z => z.getLsbD i) h <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

theorem nonzero_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) :
    WP isa (nonzero n a) s fun s' =>
      s'.gpr .edx = mask32 (wordsVal s.mem base a n ≠ 0) ∧ Keeps [.ecx, .edx, .ebp] s s' ∧ s'.mem = s.mem := by
  have hsz := hs.size_lt
  unfold nonzero
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => WP.block_nil ?_)
  refine WP.seq (wordLoop_ok (fun j t => Keeps [.ecx, .edx, .ebp] s t ∧ t.mem = s.mem ∧
      (t.gpr .ecx = 0 ↔ val32 s.mem base a j = 0)) (by omega) (by omega)
    (fun j u u' ⟨K, m, e⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm.trans m, by rw [hg _ (by decide) (by decide)]; exact e⟩)
    ⟨u₀.keeps.mono (by decide), u₀.mem, by rw [u₀.gpr]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
    (fun j hj t ⟨K, m, e⟩ ej => ?_) ?_)
  · have ht := hs.of_keeps K (by decide)
    refine wp_orS (readSrc_at' ht ej (d := a) (by omega)) fun u uu => WP.block_nil
      ⟨⟨K.widen uu.keeps, by rw [uu.mem, m], ?_⟩, uu.other _ (by decide), uu.other _ (by decide)⟩
    rw [uu.gpr, or_eq_zero32, e, val32_succ, m]
    have hp : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
    have hw : (s.mem.readW (off base (a + 4 * j)) 32 = 0) ↔ w32 s.mem base (a + 4 * j) = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]; rfl
    · intro h
      have h₂ : w32 s.mem base (a + 4 * j) = 0 := by
        rcases Nat.eq_zero_or_pos (w32 s.mem base (a + 4 * j)) with h' | h'
        · exact h'
        · have := Nat.mul_le_mul_left (2 ^ (32 * j)) h'; omega
      exact ⟨by omega, h₂⟩
  · intro t ⟨K, m, e⟩
    refine wp_movS rfl fun s₃ u₃ _ => wp_movS rfl fun s₄ u₄ _ => wp_subS rfl fun s₅ u₅ c₅ => ?_
    refine wp_sbbS rfl c₅ fun s₆ u₆ _ => WP.block_nil ⟨?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m]⟩
    · rw [u₆.gpr, sbb_mask, u₄.gpr, u₄.other .edx (by decide), u₃.gpr]
      have : ((0 : BitVec 32).toNat < (t.gpr .ecx).toNat) ↔ t.gpr .ecx ≠ 0 :=
        ⟨fun h e => by rw [e] at h; exact Nat.lt_irrefl _ h,
          fun h => Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq e)⟩
      simp only [mask32, decide_eq_true_eq, this, ne_eq, e, wordsVal_eq_val32]
    · exact (((K.widen u₃.keeps).widen u₄.keeps).widen u₅.keeps).widen u₆.keeps

theorem lessThan_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hm : m + 8 * n ≤ size) :
    WP isa (lessThan n a m) s fun s' =>
      s'.gpr .eax = mask32 (wordsVal s.mem base a n < wordsVal s.mem base m n) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s s' ∧ s'.mem = s.mem := by
  have hsz := hs.size_lt
  unfold lessThan
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => WP.block_nil ?_)
  refine WP.seq (wordLoop_ok (fun j t => Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem ∧
      t.gpr .ecx = cmask (decide (val32 s.mem base a j < val32 s.mem base m j))) (by omega) (by omega)
    (fun j u u' ⟨K, mm, e⟩ ⟨hm', hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm'.trans mm, by rw [hg _ (by decide) (by decide)]; exact e⟩)
    ⟨u₀.keeps.mono (by decide), u₀.mem, by rw [u₀.gpr]; rfl⟩
    (fun j hj t ⟨K, mm, e⟩ ej => ?_) ?_)
  · have ht := hs.of_keeps K (by decide)
    simp only [List.singleton_append]
    refine wp_movS (readSrc_at' ht ej (d := a) (by omega)) fun s₁ u₁ _ => ?_
    refine wp_restore (by rw [u₁.other _ (by decide), e]) fun s₂ u₂ c₂ => ?_
    have K₂ : Keeps [.eax, .edx] t s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
    have hs₂ := ht.of_keeps K₂ (by decide)
    have ej₂ : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * j) := by
      rw [K₂.1 _ (by decide), K₂.1 _ (by decide)]; exact ej
    refine wp_sbbS (readSrc_at' hs₂ ej₂ (d := m) (by omega)) c₂ fun s₃ u₃ c₃ => ?_
    refine wp_sbb_self c₃ fun s₄ u₄ => WP.block_nil ⟨⟨K.trans (((K₂.mono (rs' := [.eax, .ecx, .edx, .ebp])
      (by decide)).widen u₃.keeps).widen u₄.keeps), by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, mm], ?_⟩,
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide)],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide)]⟩
    have eA : (s₂.gpr .eax).toNat = w32 s.mem base (a + 4 * j) := by rw [u₂.other _ (by decide), u₁.gpr, mm]
    have eM : (s₂.mem.readW (off base (m + 4 * j)) 32).toNat = w32 s.mem base (m + 4 * j) := by
      rw [u₂.mem, u₁.mem, mm]
    have hb : decide ((s₂.gpr .eax).toNat < (s₂.mem.readW (off base (m + 4 * j)) 32).toNat +
        (decide (val32 s.mem base a j < val32 s.mem base m j)).toNat) =
        decide (val32 s.mem base a (j + 1) < val32 s.mem base m (j + 1)) := by
      refine decide_eq_decide.mpr ?_
      rw [eA, eM, val32_succ s.mem base a, val32_succ s.mem base m]
      exact (VG.Proof.Weierstrass.lt_top (val32_lt _ _ _ _) (val32_lt _ _ _ _)).symm
    rw [u₄.gpr, hb]
  · intro t ⟨K, mm, e⟩
    refine wp_movS rfl fun s₁ u₁ _ => WP.block_nil ⟨?_, K.widen u₁.keeps, by rw [u₁.mem, mm]⟩
    rw [u₁.gpr, e, wordsVal_eq_val32, wordsVal_eq_val32]
    by_cases h : val32 s.mem base a (2 * n) < val32 s.mem base m (2 * n) <;> simp [h, mask32, cmask]

theorem equal_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a b : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hb : b + 8 * n ≤ size) :
    WP isa (equal n a b) s fun t =>
      t.gpr .edx = mask32 (wordsVal s.mem base a n = wordsVal s.mem base b n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem := by
  unfold equal
  refine WP.seq (WP.mono (lessThan_ok n hs hn ha hb) fun u ⟨eu, ku, mu⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v uv _ => WP.block_nil ?_)
  have kv : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s v := (ku.mono (by decide)).widen uv.keeps
  refine WP.seq (WP.mono (lessThan_ok n (hs.of_keeps kv (by decide)) hn hb ha)
    fun w ⟨ew, kw, mw⟩ => ?_)
  refine wp_orS rfl fun x ux => ?_
  refine wp_logicS (.inr rfl) rfl fun y uy => ?_
  refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ((((kv.widen kw).widen ux.keeps).widen uy.keeps).widen ut.keeps),
    by rw [ut.mem, uy.mem, ux.mem, mw, uv.mem, mu]⟩
  rw [ut.gpr, uy.gpr, ux.gpr, ew, kw.1 _ (by decide), uv.gpr, eu, uv.mem, mu]
  by_cases hab : wordsVal s.mem base a n < wordsVal s.mem base b n
  · have hba : ¬ wordsVal s.mem base b n < wordsVal s.mem base a n := by omega
    have he : wordsVal s.mem base a n ≠ wordsVal s.mem base b n := by omega
    simp only [mask32, hab, hba, he, ite_true, ite_false]
    decide
  · by_cases hba : wordsVal s.mem base b n < wordsVal s.mem base a n
    · have he : wordsVal s.mem base a n ≠ wordsVal s.mem base b n := by omega
      simp only [mask32, hab, hba, he, ite_true, ite_false]
      decide
    · have he : wordsVal s.mem base a n = wordsVal s.mem base b n := by omega
      simp only [mask32, he, Nat.lt_irrefl, ite_true, ite_false]
      decide

abbrev flagW (base : Addr) (flag : Nat) (s : State) : BitVec 32 :=
  s.mem.readW (off base flag) 32

theorem andFlag_ok (flag : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : flag + 4 ≤ size) :
    WP isa (.block (andFlag flag)) s fun s' =>
      flagW base flag s' = flagW base flag s &&& s.gpr .edx ∧
      Keeps [.eax] s s' ∧ Outside base (flag) 4 s.mem s'.mem := by
  simp only [andFlag]
  refine wp_movS (readSrc_sc hs (d := flag) hf) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.trans u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine wp_storeS (hs₂.ea (d := flag) (by omega)) (hs₂.write hf) fun s₃ m₃ => WP.block_nil
    ⟨?_, k₂.trans (m₃.keeps _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr, u₁.other _ (by decide)]
    simp only [ite_true]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (n flag : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hm : m + 8 * n ≤ size) (hf : flag + 4 ≤ size) :
    WP isa (checkRange n a m flag) s fun s' =>
      flagW base flag s' = flagW base flag s &&&
        mask32 (0 < wordsVal s.mem base a n ∧ wordsVal s.mem base a n < wordsVal s.mem base (m) n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s s' ∧ Outside base (flag) 4 s.mem s'.mem := by
  unfold checkRange
  refine WP.seq (WP.mono (lessThan_ok n hs hn ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.seq (wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have k₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s s₂ := (k₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine WP.seq (WP.mono (nonzero_ok n hs₂ hn ha) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have k₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s s₄ := (k₂.widen k₃).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  refine WP.mono (andFlag_ok flag hs₄ hf) fun s₅ ⟨e₅, k₅, O₅⟩ => ⟨?_, k₄.widen k₅, by rw [← mem₄]; exact O₅⟩
  rw [e₅, flagW, flagW, mem₄, u₄.gpr, e₃, k₃.1 _ (by decide), u₂.gpr, e₁, u₂.mem, m₁]
  simp only [ite_true]
  rw [mask32_and]
  simp only [Nat.pos_iff_ne_zero]

end VG.Proof.Dsa.X86
