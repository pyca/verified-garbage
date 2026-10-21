module

public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs

/-!
# ML-KEM on AArch64: `decaps`, the comparison and the key

`c = c'` as the OR of the words of `c ⊕ c'` being 0 (`cmp_ok`), without
branching, then a mask of ones exactly when they are equal, and `K'` or `K̄`
into `key` through it (`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Decaps

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem.AArch64.KeyGen (readW64_byte writeW64_byte writeW64_off)

variable {P : KemLay}

theorem sel_val (a b : BitVec 64) (e : Bool) :
    ((a ^^^ b) &&& (if e then (0 : BitVec 64) - 1 else 0)) ^^^ b = if e then a else b := by
  cases e
  · simp
  · simp only [ite_true]
    rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

/-- `((x ∨ -x) >> 63) - 1`: all ones exactly when `x = 0`. -/
theorem mask_val (x : BitVec 64) :
    ((x ||| ((0 : BitVec 64) - x)) >>> 63) - BitVec.ofNat 64 1 = if x = 0 then (0 : BitVec 64) - 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have h1 : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hx
      · exact h0
    have hx' := x.isLt
    have hn : ((0 : BitVec 64) - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    have hge : 2 ^ 63 ≤ (x ||| ((0 : BitVec 64) - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases (by omega : 2 ^ 63 ≤ x.toNat ∨ 2 ^ 63 ≤ ((0 : BitVec 64) - x).toNat) with h | h
      · exact Nat.le_trans h Nat.left_le_or
      · exact Nat.le_trans h Nat.right_le_or
    have hlt := (x ||| ((0 : BitVec 64) - x)).isLt
    have : (x ||| ((0 : BitVec 64) - x)) >>> 63 = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_lsr, BitVec.toNat_ofNat]
      show _ / 2 ^ 63 = 1 % 2 ^ 64
      omega
    rw [this, BitVec.sub_self]; rfl

/-- Two words of memory are equal exactly when their eight bytes are. -/
theorem readW64_eq_iff (m : Mem) (a b : Addr) :
    m.readW a 64 = m.readW b 64 ↔ bytesAt m a 8 = bytesAt m b 8 := by
  constructor
  · intro h
    refine bytesAt_eq rfl fun i hi => ?_
    rw [← KeyGen.readW64_byte m a hi, h, KeyGen.readW64_byte m b hi, bytesAt_getElem]
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    have e : ∀ c : Addr, (m.readW c 64).getLsbD j = ((m.readW c 64).extractLsb' (8 * (j / 8)) 8).getLsbD (j % 8) := by
      intro c; simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
        Bool.true_and]; congr 1; omega
    have hb := congrArg (fun l => l[j / 8]?) h
    simp only [List.getElem?_eq_getElem (show j / 8 < (bytesAt m a 8).length by rw [bytesAt_length]; omega),
      List.getElem?_eq_getElem (show j / 8 < (bytesAt m b 8).length by rw [bytesAt_length]; omega),
      Option.some.injEq, bytesAt_getElem] at hb
    rw [e a, e b, KeyGen.readW64_byte m a (show j / 8 < 8 by omega), KeyGen.readW64_byte m b (show j / 8 < 8 by omega),
      hb]

/-! ## `c = c'` -/

/-- After `k` words of `c` (at `kA s₀ 1`) and `c'` (at `CB`). -/
structure CInv (P : KemLay) (s₀ s : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x0, .x1, .x2, .x9, .x10, .x11] s u
  mem : u.mem = s.mem
  x0 : u.gpr .x0 = kA s₀ 1 + BitVec.ofNat 64 (8 * k)
  x1 : u.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 (CB P + 8 * k)
  x2 : (u.gpr .x2).toNat = P.ctLen / 8 - k
  eq : u.gpr .x10 = 0 ↔
    bytesAt s.mem (kA s₀ 1) (8 * k) = bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P)) (8 * k)

theorem cstep {s₀ : State} (hp : Pre P (deL P) s₀) {s : State} (hk : KB P (deL P) s₀ s) {k : Nat}
    (hk' : k < P.ctLen / 8) {u : State} (h : CInv P s₀ s k u) :
    WP isa (.block deCmpBody) u fun u' => CInv P s₀ s (k + 1) u' ∧
      ((u'.gpr .x2).toNat ≠ 0 ↔ k + 1 ≠ P.ctLen / 8) := by
  have hw := hp.wf
  have hcr := cov_r hp hk (b := 1) (o := 0) (l := P.ctLen) (by dek) (by dek)
  have hsr := cov_sr hp hk (o := CB P) (l := P.ctLen) (by kom)
  have h8 : 8 * k + 8 ≤ P.ctLen := by
    have : P.ctLen = 32 * (P.du * P.k + P.dv) := rfl
    omega
  have in₁ : InRegions (u.rd ++ u.wr) (kA s₀ 1 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.keep.rd, h.keep.wr]
    have := in_R hcr (k := 8 * k) (n := 8) h8 (by kom)
    rwa [Nat.zero_add] at this
  have in₂ : InRegions (u.rd ++ u.wr) (kA s₀ 3 + BitVec.ofNat 64 (CB P + 8 * k)) 8 := by
    rw [h.keep.rd, h.keep.wr]
    exact in_R hsr (k := 8 * k) (n := 8) h8 (by kom)
  refine wp_ldrx (a := kA s₀ 1 + BitVec.ofNat 64 (8 * k)) (by decide) (by rw [h.x0, ptr_zero]) in₁
    fun u₁ g₁ v₁ => ?_
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (CB P + 8 * k)) (by decide)
    (by rw [g₁.get .x1, h.x1, ptr_zero]) (by rw [g₁.rd, g₁.wr]; exact in₂) fun u₂ g₂ v₂ => ?_
  refine wp_eor fun u₃ g₃ v₃ => wp_orr fun u₄ g₄ v₄ => wp_addImm (by decide) fun u₅ g₅ v₅ =>
    wp_addImm (by decide) fun u₆ g₆ v₆ => wp_subImm (by decide) fun u₇ g₇ v₇ => wp_nil ?_
  have o₇ : Only [.x0, .x1, .x2, .x9, .x10, .x11] u u₇ :=
    ((((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).trans g₆).trans g₇).mono
  have m₁ : u₁.mem = s.mem := by rw [g₁.mem, h.mem]
  have x9 : u₃.gpr .x9 = s.mem.readW (kA s₀ 1 + BitVec.ofNat 64 (8 * k)) 64 ^^^
      s.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (CB P + 8 * k)) 64 := by
    rw [v₃, g₂.get .x9, v₁, v₂, m₁, h.mem]
  have x10 : u₇.gpr .x10 = u.gpr .x10 ||| u₃.gpr .x9 := by
    rw [g₇.get .x10, g₆.get .x10, g₅.get .x10, v₄, g₃.get .x10, g₂.get .x10, g₁.get .x10]
  have x2 : u₇.gpr .x2 = u.gpr .x2 - BitVec.ofNat 64 1 := by
    rw [v₇, g₆.get .x2, g₅.get .x2, g₄.get .x2, g₃.get .x2, g₂.get .x2, g₁.get .x2]
  have hx2 : (u₇.gpr .x2).toNat = P.ctLen / 8 - (k + 1) := by
    rw [x2, toNat_sub_n (show (BitVec.ofNat 64 1).toNat ≤ (u.gpr .x2).toNat by
      rw [h.x2, BitVec.toNat_ofNat]; omega), h.x2, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨h.keep.trans o₇.keep |>.mono, by rw [o₇.mem, h.mem], ?_, ?_, hx2, ?_⟩, by rw [hx2]; omega⟩
  · rw [g₇.get .x0, g₆.get .x0, v₅, g₄.get .x0, g₃.get .x0, g₂.get .x0, g₁.get .x0, h.x0, ptr_add,
      Nat.mul_succ]
  · rw [g₇.get .x1, v₆, g₅.get .x1, g₄.get .x1, g₃.get .x1, g₂.get .x1, g₁.get .x1, h.x1, ptr_add,
      Nat.add_assoc, Nat.mul_succ]
  · have e1 : u.gpr .x10 ||| u₃.gpr .x9 = 0 ↔ u.gpr .x10 = 0 ∧ u₃.gpr .x9 = 0 := BitVec.or_eq_zero_iff
    have xz : ∀ a b : BitVec 64, a ^^^ b = 0 ↔ a = b := fun _ _ => BitVec.xor_eq_zero_iff
    rw [x10, e1, h.eq, x9, xz, readW64_eq_iff, show 8 * (k + 1) = 8 * k + 8 by omega,
      bytesAt_add, bytesAt_add, ptr_add]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro e
      exact List.append_inj e (by rw [bytesAt_length, bytesAt_length])

theorem cmp_ok {s₀ : State} (hp : Pre P (deL P) s₀) {s : State} (hk : KB P (deL P) s₀ s) {c' : List Byte}
    (hc : bytesAt s.mem (sA (deL P) s₀ (CB P)) P.ctLen = c') :
    WP isa P.deCmp s fun s' => Keep [.x0, .x1, .x2, .x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .x10 = if cD P s₀ = c' then (0 : BitVec 64) - 1 else 0 := by
  have hw := hp.wf
  have h8 : P.ctLen % 8 = 0 := by
    have : P.ctLen = 32 * (P.du * P.k + P.dv) := rfl
    omega
  refine WP.seq ?_
  rw [List.append_assoc]
  refine wp_ptrTo (by decide) (by decide) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by kom)
    fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have o₄ : Only [.x0, .x1, .x2, .x9, .x10, .x11] s s₄ := (((h₁.trans h₂).trans h₃).trans h₄).mono
  have z : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 := by simp
  have c₀ : CInv P s₀ s 0 s₄ :=
    ⟨o₄.keep, o₄.mem, by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.x26]; rfl,
      by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, hk.x28]; rfl,
      by rw [h₄.get .x2, e₃, Nat.sub_zero]; exact imm16 (by kom),
      by rw [e₄, z]; exact ⟨fun _ => (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).trans
        (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).symm, fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (count_loop (n := P.ctLen / 8) (by kom) (CInv P s₀ s)
    (fun k hk' u h => cstep hp hk hk' h) c₀) fun s₅ h₅ => ?_)
  refine wp_movz fun s₆ h₆ e₆ => wp_sub fun s₇ h₇ e₇ => wp_orr fun s₈ h₈ e₈ =>
    wp_lsr (by decide) fun s₉ h₉ e₉ => wp_subImm (by decide) fun s₁₀ h₁₀ e₁₀ => wp_nil ?_
  have o₁₀ : Only [.x10, .x11] s₅ s₁₀ := ((((h₆.trans h₇).trans h₈).trans h₉).trans h₁₀).mono
  refine ⟨h₅.keep.trans o₁₀.keep |>.mono, by rw [o₁₀.mem, h₅.mem], ?_⟩
  have ex : ((s₅.gpr .x10 ||| ((0 : BitVec 64) - s₅.gpr .x10)) >>> 63) - BitVec.ofNat 64 1 = s₁₀.gpr .x10 := by
    rw [e₁₀, e₉, e₈, e₇, h₇.get .x10, h₆.get .x10, e₆, z]
  rw [← ex, mask_val]
  have hcD : bytesAt s.mem (kA s₀ 1) P.ctLen = cD P s₀ := hk.ro (b := 1) (by dek)
  have he := h₅.eq
  rw [show 8 * (P.ctLen / 8) = P.ctLen by omega, hcD,
    show kA s₀ 3 + BitVec.ofNat 64 (CB P) = sA (deL P) s₀ (CB P) from rfl, hc] at he
  by_cases e : cD P s₀ = c'
  · rw [ite_eq_left (he.mpr e), ite_eq_left e]
  · rw [ite_eq_right (fun h => e (he.mp h)), ite_eq_right e]

/-! ## The key -/

/-- `K'` (at `KP`) or `K̄` (at `JB`) into `key`. -/
theorem sel_ok {s₀ : State} (hp : Pre P (deL P) s₀) {s : State} (hk : KB P (deL P) s₀ s) {e : Bool}
    (hm : s.gpr .x10 = if e then (0 : BitVec 64) - 1 else 0) :
    WP isa (.block deSel) s fun s' => Keep [.x12, .x13] s s' ∧
      Frame [R (kA s₀) 2 0 32] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ 2) 32 =
        if e then bytesAt s.mem (sA (deL P) s₀ KP) 32 else bytesAt s.mem (sA (deL P) s₀ JB) 32 := by
  have hwf := hp.wf
  have hkr := cov_sr hp hk (o := KP) (l := 32) (by kom)
  have hjr := cov_sr hp hk (o := JB) (l := 32) (by kom)
  have hw := cov_w hp hk (b := 2) (o := 0) (l := 32) (by dek) (by dek)
  have sk : ∀ {o : Nat}, o + 32 ≤ SV P + 48 → ∀ r ∈ [R (kA s₀) 2 0 32],
      (R (kA s₀) (deL P).sc o 32).Disjoint r := fun f r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by dek) (by dek) (hp.fs f) (by dek) (by dek)
      (.inl (by dek))
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4) (fun k (u : State) => Keep [.x12, .x13] s u ∧
      Frame [R (kA s₀) 2 0 32] s.mem u.mem ∧
      ∀ i < 8 * k, u.mem (kA s₀ 2 + BitVec.ofNat 64 i) =
        if e then s.mem (sA (deL P) s₀ KP + BitVec.ofNat 64 i) else s.mem (sA (deL P) s₀ JB + BitVec.ofNat 64 i))
    (fun k u hk' ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ => ⟨k', f', ?_⟩
  · have r₁ : ∀ {o : Nat}, o + 32 ≤ SV P + 48 → ∀ {j : Nat}, j < 32 →
        u.mem (sA (deL P) s₀ o + BitVec.ofNat 64 j) = s.mem (sA (deL P) s₀ o + BitVec.ofNat 64 j) :=
      fun {o} f {j} hj => f₁.bytes (R := R (kA s₀) (deL P).sc o 32) (sk f) (show 32 ≤ 2 ^ 64 by decide) hj
    refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) ⟨by simp only [KP]; omega, by simp only [KP]; omega⟩
      (by rw [k₁.get .x28, hk.x28]; rfl) (by rw [k₁.rd, k₁.wr]; exact in_R hkr (k := 8 * k) (by omega) (by decide))
      fun u₁ g₁ v₁ => ?_
    refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) ⟨by simp only [JB]; omega, by simp only [JB]; omega⟩
      (by rw [g₁.get .x28, k₁.get .x28, hk.x28]; rfl)
      (by rw [g₁.rd, g₁.wr, k₁.rd, k₁.wr]; exact in_R hjr (k := 8 * k) (by omega) (by decide))
      fun u₂ g₂ v₂ => ?_
    refine wp_eor fun u₃ g₃ v₃ => wp_and fun u₄ g₄ v₄ => wp_eor fun u₅ g₅ v₅ => ?_
    have o₅ : Only [.x12, .x13] u u₅ := ((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).mono
    refine wp_strx (a := kA s₀ 2 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩
      (by rw [o₅.get .x27, k₁.get .x27, hk.x27]; rfl)
      (by
        rw [o₅.wr, k₁.wr]
        have := in_R hw (k := 8 * k) (n := 8) (by omega) (by decide)
        rwa [Nat.zero_add] at this) fun u₆ g₆ => wp_nil ?_
    have mk : u₃.gpr .x10 = if e then (0 : BitVec 64) - 1 else 0 := by
      rw [g₃.get .x10, g₂.get .x10, g₁.get .x10, k₁.get .x10, hm]
    have a12 : u₂.gpr .x12 = u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) 64 := by
      rw [g₂.get .x12, v₁]
    have a13 : u₂.gpr .x13 = u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) 64 := by
      rw [v₂, g₁.mem]
    have val : u₅.gpr .x12 = if e then u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (KP + 8 * k)) 64
        else u.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (JB + 8 * k)) 64 := by
      rw [v₅, g₄.get .x13, g₃.get .x13, v₄, v₃, a12, a13, mk, sel_val]
    have m₆ : u₆.mem = u.mem.writeW (kA s₀ 2 + BitVec.ofNat 64 (8 * k)) (u₅.gpr .x12) := by
      rw [g₆.mem, o₅.mem]
    refine ⟨(k₁.trans (o₅.keep.trans g₆.keep)).mono, ?_, fun i hi => ?_⟩
    · rw [m₆]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        rw [show kA s₀ 2 + BitVec.ofNat 64 (8 * k) = kA s₀ 2 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * k) by
          rw [ptr_add, Nat.zero_add]]
        exact contains_off (by omega) (by decide))
    · rw [m₆]
      rcases (by omega : i < 8 * k ∨ 8 * k ≤ i) with hi' | hi'
      · rw [writeW64_off _ _ _ _ (by
          rw [show kA s₀ 2 = kA s₀ 2 + BitVec.ofNat 64 0 from (ptr_zero _).symm, ptr_add, ptr_add]
          exact sep_off _ (a := 0 + i) (n := 1) (b := 0 + 8 * k) (k := 8) (by omega) (by omega) (by omega) _
            (by rw [BitVec.sub_self]; decide))]
        exact b₁ i hi'
      · have hj : i - 8 * k < 8 := by omega
        rw [show kA s₀ 2 + BitVec.ofNat 64 i = kA s₀ 2 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (i - 8 * k) by
          rw [ptr_add, show 8 * k + (i - 8 * k) = i by omega], writeW64_byte _ _ _ hj, val]
        have e₁ : ∀ o, o + 32 ≤ SV P + 48 → kA s₀ 3 + BitVec.ofNat 64 (o + 8 * k) + BitVec.ofNat 64 (i - 8 * k) =
            sA (deL P) s₀ o + BitVec.ofNat 64 i := fun o _ => by
          rw [ptr_add, show sA (deL P) s₀ o = kA s₀ 3 + BitVec.ofNat 64 o from rfl, ptr_add,
            show o + 8 * k + (i - 8 * k) = o + i by omega]
        cases e
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [readW64_byte _ _ hj, e₁ JB (by kom), r₁ (by kom) (by omega)]
        · simp only [↓reduceIte]
          rw [readW64_byte _ _ hj, e₁ KP (by kom), r₁ (by kom) (by omega)]
  · cases e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine bytesAt_eq (bytesAt_length _ _ _) fun i hi => ?_
      rw [bytesAt_getElem, b' i (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      refine bytesAt_eq (bytesAt_length _ _ _) fun i hi => ?_
      rw [bytesAt_getElem, b' i (by omega)]
      simp only [↓reduceIte]

end VG.Proof.MlKem.AArch64.Decaps
