import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp`. -/
section

/-!
# ML-KEM on AArch64: `decaps`, the comparison and the key

`c = c'` as the OR of the bytes of `c ⊕ c'` being 0 (`cmp_ok`), without
branching, then a mask of ones exactly when they are equal, and `K'` or `K̄`
into `key` through it (`sel_ok`).
-/

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

theorem mask_val (x : BitVec 64) (h : x.toNat < 256) :
    (0 : BitVec 64) - ((x - 1) >>> 63) = if x = 0 then (0 : BitVec 64) - 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have h1 : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hx
      · exact h0
    have : (x - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_lsr, toNat_sub_n (show (1 : BitVec 64).toNat ≤ x.toNat from h1)]
      show (x.toNat - 1) / 2 ^ 63 = 0
      omega
    rw [this]; rfl

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

/-! ## `c = c'` -/

/-- After `k` bytes of `c` (at `kA s₀ 1`) and `c'` (at `CB`). -/
structure CInv (P : KemLay) (s₀ s : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x0, .x1, .x2, .x9, .x10, .x11] s u
  mem : u.mem = s.mem
  x0 : u.gpr .x0 = kA s₀ 1 + BitVec.ofNat 64 k
  x1 : u.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 (CB P + k)
  x2 : (u.gpr .x2).toNat = P.ctLen - k
  x10 : (u.gpr .x10).toNat < 256
  eq : u.gpr .x10 = 0 ↔ bytesAt s.mem (kA s₀ 1) k = bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P)) k

theorem cstep {s₀ : State} (hp : Pre P (deL P) s₀) {s : State} (hk : KB P (deL P) s₀ s) {k : Nat}
    (hk' : k < P.ctLen) {u : State} (h : VG.Proof.MlKem.AArch64.Decaps.CInv P s₀ s k u) :
    WP isa (.block deCmpBody) u fun u' => VG.Proof.MlKem.AArch64.Decaps.CInv P s₀ s (k + 1) u' ∧ ((u'.gpr .x2).toNat ≠ 0 ↔ k + 1 ≠ P.ctLen) := by
  have hw := hp.wf
  have hcr := cov_r hp hk (b := 1) (o := 0) (l := P.ctLen) (by dek) (by dek)
  have hsr := cov_sr hp hk (o := CB P) (l := P.ctLen) (by kom)
  have in₁ : InRegions (u.rd ++ u.wr) (kA s₀ 1 + BitVec.ofNat 64 k) 1 := by
    rw [h.keep.rd, h.keep.wr]
    have := in_R hcr (k := k) (n := 1) (by omega) (by kom)
    rwa [Nat.zero_add] at this
  have in₂ : InRegions (u.rd ++ u.wr) (kA s₀ 3 + BitVec.ofNat 64 (CB P + k)) 1 := by
    rw [h.keep.rd, h.keep.wr]
    exact in_R hsr (k := k) (n := 1) (by omega) (by kom)
  refine wp_ldrb (a := kA s₀ 1 + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, ptr_zero]) in₁
    fun u₁ g₁ v₁ => ?_
  refine wp_ldrb (a := kA s₀ 3 + BitVec.ofNat 64 (CB P + k)) (by decide)
    (by rw [g₁.get .x1, h.x1, ptr_zero]) (by rw [g₁.rd, g₁.wr]; exact in₂) fun u₂ g₂ v₂ => ?_
  refine wp_eor fun u₃ g₃ v₃ => wp_orr fun u₄ g₄ v₄ => wp_addImm (by decide) fun u₅ g₅ v₅ =>
    wp_addImm (by decide) fun u₆ g₆ v₆ => wp_subImm (by decide) fun u₇ g₇ v₇ => wp_nil ?_
  have o₇ : Only [.x0, .x1, .x2, .x9, .x10, .x11] u u₇ :=
    ((((((g₁.trans g₂).trans g₃).trans g₄).trans g₅).trans g₆).trans g₇).mono
  have m₁ : u₁.mem = s.mem := by rw [g₁.mem, h.mem]
  have x9 : u₃.gpr .x9 = (s.mem (kA s₀ 1 + BitVec.ofNat 64 k)).setWidth 64 ^^^
      (s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P + k))).setWidth 64 := by
    rw [v₃, g₂.get .x9, v₁, v₂, m₁, h.mem]
  have x10 : u₇.gpr .x10 = u.gpr .x10 ||| u₃.gpr .x9 := by
    rw [g₇.get .x10, g₆.get .x10, g₅.get .x10, v₄, g₃.get .x10, g₂.get .x10, g₁.get .x10]
  have x2 : u₇.gpr .x2 = u.gpr .x2 - BitVec.ofNat 64 1 := by
    rw [v₇, g₆.get .x2, g₅.get .x2, g₄.get .x2, g₃.get .x2, g₂.get .x2, g₁.get .x2]
  have hx2 : (u₇.gpr .x2).toNat = P.ctLen - (k + 1) := by
    rw [x2, toNat_sub_n (show (BitVec.ofNat 64 1).toNat ≤ (u.gpr .x2).toNat by
      rw [h.x2, BitVec.toNat_ofNat]; omega), h.x2, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨h.keep.trans o₇.keep |>.mono, by rw [o₇.mem, h.mem], ?_, ?_, hx2, ?_, ?_⟩, by rw [hx2]; omega⟩
  · rw [g₇.get .x0, g₆.get .x0, v₅, g₄.get .x0, g₃.get .x0, g₂.get .x0, g₁.get .x0, h.x0, ptr_add]
  · rw [g₇.get .x1, v₆, g₅.get .x1, g₄.get .x1, g₃.get .x1, g₂.get .x1, g₁.get .x1, h.x1, ptr_add,
      Nat.add_assoc]
  · rw [x10, BitVec.toNat_or, x9, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    have a := (s.mem (kA s₀ 1 + BitVec.ofNat 64 k)).isLt
    have b := (s.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P + k))).isLt
    have c := h.x10
    exact Nat.or_lt_two_pow (n := 8) c (Nat.xor_lt_two_pow (by omega) (by omega))
  · have e1 : u.gpr .x10 ||| u₃.gpr .x9 = 0 ↔ u.gpr .x10 = 0 ∧ u₃.gpr .x9 = 0 := BitVec.or_eq_zero_iff
    rw [x10, e1, h.eq, x9, VG.Proof.MlKem.AArch64.Decaps.xor_zero_iff, VG.Proof.MlKem.AArch64.Decaps.bytesAt_succ', VG.Proof.MlKem.AArch64.Decaps.bytesAt_succ', ptr_add]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro e
      obtain ⟨h1, h2⟩ := List.append_inj e (by rw [bytesAt_length, bytesAt_length])
      exact ⟨h1, List.head_eq_of_cons_eq h2⟩

theorem cmp_ok {s₀ : State} (hp : Pre P (deL P) s₀) {s : State} (hk : KB P (deL P) s₀ s) {c' : List Byte}
    (hc : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ (CB P)) P.ctLen = c') :
    WP isa P.deCmp s fun s' => Keep [.x0, .x1, .x2, .x9, .x10, .x11] s s' ∧ s'.mem = s.mem ∧
      s'.gpr .x10 = if cD P s₀ = c' then (0 : BitVec 64) - 1 else 0 := by
  have hw := hp.wf
  refine WP.seq ?_
  rw [List.append_assoc]
  refine wp_ptrTo (by decide) (by decide) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by kom)
    fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have o₄ : Only [.x0, .x1, .x2, .x9, .x10, .x11] s s₄ := (((h₁.trans h₂).trans h₃).trans h₄).mono
  have z : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 := by simp
  have c₀ : VG.Proof.MlKem.AArch64.Decaps.CInv P s₀ s 0 s₄ :=
    ⟨o₄.keep, o₄.mem, by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.x26]; rfl,
      by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, hk.x28]; rfl,
      by rw [h₄.get .x2, e₃, Nat.sub_zero]; exact imm16 (by kom), by rw [e₄, z]; decide,
      by rw [e₄, z]; exact ⟨fun _ => (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).trans
        (List.eq_nil_of_length_eq_zero (bytesAt_length _ _ _)).symm, fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (count_loop (n := P.ctLen) (by kom) (VG.Proof.MlKem.AArch64.Decaps.CInv P s₀ s) (fun k hk' u h => VG.Proof.MlKem.AArch64.Decaps.cstep hp hk hk' h)
    c₀) fun s₅ h₅ => ?_)
  refine wp_subImm (by decide) fun s₆ h₆ e₆ => wp_lsr (by decide) fun s₇ h₇ e₇ => wp_movz fun s₈ h₈ e₈ =>
    wp_sub fun s₉ h₉ e₉ => wp_nil ?_
  have o₉ : Only [.x10, .x11] s₅ s₉ := (((h₆.trans h₇).trans h₈).trans h₉).mono
  refine ⟨h₅.keep.trans o₉.keep |>.mono, by rw [o₉.mem, h₅.mem], ?_⟩
  have ex : (0 : BitVec 64) - ((s₅.gpr .x10 - 1) >>> 63) = s₉.gpr .x10 := by
    rw [e₉, h₈.get .x10, e₈, e₇, e₆]; rfl
  rw [← ex, VG.Proof.MlKem.AArch64.Decaps.mask_val _ h₅.x10]
  have hcD : bytesAt s.mem (kA s₀ 1) P.ctLen = cD P s₀ := hk.ro (b := 1) (by dek)
  have he := h₅.eq
  rw [hcD, show kA s₀ 3 + BitVec.ofNat 64 (CB P) = VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ (CB P) from rfl, hc] at he
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
        if e then bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ KP) 32 else bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ JB) 32 := by
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
        if e then s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ KP + BitVec.ofNat 64 i) else s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ JB + BitVec.ofNat 64 i))
    (fun k u hk' ⟨k₁, f₁, b₁⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩) fun s' ⟨k', f', b'⟩ => ⟨k', f', ?_⟩
  · have r₁ : ∀ {o : Nat}, o + 32 ≤ SV P + 48 → ∀ {j : Nat}, j < 32 →
        u.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o + BitVec.ofNat 64 j) :=
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
      rw [v₅, g₄.get .x13, g₃.get .x13, v₄, v₃, a12, a13, mk, VG.Proof.MlKem.AArch64.Decaps.sel_val]
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
            VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o + BitVec.ofNat 64 i := fun o _ => by
          rw [ptr_add, show VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o = kA s₀ 3 + BitVec.ofNat 64 o from rfl, ptr_add,
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Decaps`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem768_decaps` and `vg_mlkem1024_decaps`

Correctness is the first phase (`a_ok`: `m'`, `G(m' ‖ h)`, `ρ`), the matrix
(`matrix_ok`), then `c'` (`encrypt_ok`), `K̄`, the comparison, the key and the
epilogue (`c_ok`).

Constant time up to `ρ`, relating two runs from states that agree on the
pointers and on `ρ`: the first and last phases by the taint analysis (which
the comparison and the choice of the key pass: they do not branch), the
matrix by `matrix_rct`.

The proof is stated once for a well-formed parameter set, with the taint
analyses of its code (`DeTaints`) decided on each; the end of this file is
ML-KEM-768's instance (and `Proof/MlKem1024/AArch64/Decaps.lean` ML-KEM-1024's).
-/

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

theorem encArgs (hP : P.Wf) : EncArgs P (deL P) 0 (384 * P.k) 3 (CB P) :=
  ⟨by decide, by dek, by simp only [deL, List.getD_cons_zero]; lom, by decide, by dek,
    by simp only [deL, List.getD_cons_succ, List.getD_cons_zero]; lom, .inr rfl⟩

theorem drop_take_slice (L : List Byte) {a n b c : Nat} (h : b + c ≤ n) :
    (((L.drop a).take n).drop b).take c = (L.drop (a + b)).take c := by
  rw [slice_take _ h, List.drop_drop]

theorem ekT_eq (s₀ : State) : ∀ j < P.k,
    decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0) + BitVec.ofNat 64 (384 * P.k + 384 * j)) 384) =
      ekT (KPke.dkEk P.params (dkD P s₀)) j := fun j hj => by
  have := mul_succ_le (a := 384) hj
  rw [ekT, KPke.dkEk, VG.Proof.MlKem.AArch64.Decaps.drop_take_slice _ (show 384 * j + 384 ≤ 384 * P.params.k + 32 by
      show _ ≤ 384 * P.k + 32; omega), show 384 * P.params.k = 384 * P.k from rfl,
    bytesAt_slice _ _ (show 384 * P.k + 384 * j + 384 ≤ P.dkLen by simp only [KemLay.dkLen]; omega)]
  rfl

/-- `c'`. -/
abbrev cpr (P : KemLay) (s₀ : State) (mB : Mem) : List Byte :=
  KPke.ct P.params (aM P (deL P) s₀ mB) (KPke.dkEk P.params (dkD P s₀)) (mD P s₀) (gD P s₀).2

/-- `K̄ = J(z ‖ c)`. -/
abbrev jD (P : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀)

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (kA s₀ 2) 32 = if cD P s₀ = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ mB then (gD P s₀).1 else VG.Proof.MlKem.AArch64.Decaps.jD P s₀

/-- A buffer of `scratch` below `ŷ` apart from what `K-PKE.Encrypt` writes. -/
theorem far_encW {s₀ : State} (hp : Pre P (deL P) s₀) {o l : Nat} (h1 : 840 ≤ o)
    (h2 : o + l ≤ RB + 32 ∨ RB + 33 ≤ o) (h3 : o + l ≤ PB) :
    ∀ r ∈ encW P (deL P) s₀ 3 (CB P), (R (kA s₀) (deL P).sc o l).Disjoint r := by
  have hw := hp.wf
  have f : o + l ≤ SV P + 48 := by lom
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact sdisj hp f (by lom) (.inr (by omega))
  · exact sdisj hp f (by lom) (by simp only [RB] at h2 ⊢; omega)
  · exact sdisj hp f (by lom) (.inl h3)
  · exact below_R hp hp.scb (hp.fs f)
  · exact sdisj hp f (by lom) (.inl (by lom))

theorem c_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hc : Calls P) {uA sB : State} (hA : AfterA P s₀ uA)
    (hB : BInv P (deL P) s₀ uA.mem (rhoD P s₀) (P.k * P.k) sB) :
    WP isa (P.deCWith keccak.callee) sB (VG.Proof.MlKem.AArch64.Decaps.Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have fbw : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ bW P (deL P) s₀, (R (kA s₀) (deL P).sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact sdisj hp f (by lom) h1
      · exact sdisj hp f (by lom) (.inl h2)
      · exact sdisj hp f (by lom) h3
      · exact below_R hp hp.scb (hp.fs f)
  have r₀ : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ RB) 32 = (gD P s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m₀ : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ MB) 32 = mD P s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have kp₀ : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame hB.fr (fbw (o := KP) (l := 32) (by dek) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.kp
  have e0 : EInv P (deL P) s₀ 3 (CB P) sB.mem sB.mem (sB.gpr .x24) (gD P s₀).2 (mD P s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r₀, m₀, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  -- `c'`
  refine WP.seq (WP.mono (encrypt_ok hp hc (VG.Proof.MlKem.AArch64.Decaps.encArgs hw) (T := ekT (KPke.dkEk P.params (dkD P s₀))) (VG.Proof.MlKem.AArch64.Decaps.ekT_eq s₀) e0)
    fun s₁ ⟨e₁, v₁⟩ => ?_)
  have kb₁ := e₁.kb
  have c₁ : bytesAt s₁.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ (CB P)) P.ctLen = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem :=
    ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (aM P (deL P) s₀ sB.mem) (gD P s₀).2 i))
      (fun i hi => by rw [ptr_add]; exact e₁.u i hi) (by rw [ptr_add]; exact v₁)
  have kp₁ : bytesAt s₁.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [bytesAt_frame e₁.fr (VG.Proof.MlKem.AArch64.Decaps.far_encW hp (by decide) (by decide) (by decide)) (by decide)]; exact kp₀
  -- `K̄ = J(z ‖ c)`
  refine WP.seq (WP.mono (hashWith_ok keccak (hsetup hp kb₁ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x25, 768 * P.k + 64, 32⟩, ⟨.x26, 0, P.ctLen⟩]) (outs := [⟨.x28, JB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact pieceOk (k := 0) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek)
      · exact pieceOk (k := 1) hp kb₁ (by decide) (by dek) (.inl (by dek)) (by dek) (by dek))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₁ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (List.pairwise_singleton _ _)) fun s₂ ⟨k₂, o₂⟩ => ?_)
  have kb₂ := kb₁.hash hp k₂ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, JB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by dek))⟩
  have msg : (List.map (pbytes s₁) [⟨.x25, 768 * P.k + 64, 32⟩, ⟨.x26, 0, P.ctLen⟩]).flatten =
      KPke.dkZ P.params (dkD P s₀) ++ cD P s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb₁.x25, kb₁.x26]
    have hc : bytesAt s₁.mem (kA s₀ ((deL P).slot 1)) P.ctLen = cD P s₀ := kb₁.ro (b := 1) (by dek)
    rw [slice_eq kb₁ (b := 0) (by decide) (by dek), ptr_zero, hc]
    rfl
  have jb₂ : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ JB) 32 = VG.Proof.MlKem.AArch64.Decaps.jD P s₀ := by
    obtain ⟨o, -⟩ := o₂
    rw [msg, e28 kb₁] at o
    rw [o]; show _ = J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀); rw [J_eq]; rfl
  have k₂' := k₂
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₁.x28, kb₁.sp] at k₂'
  have far₂ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 840 ≤ o → (o + l ≤ JB ∨ JB + 32 ≤ o) →
      bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o) l = bytesAt s₁.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ o) l := fun f h1 h2 => by
    refine bytesAt_frame k₂'.frame (fun r hr => ?_) (by lom)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.ST]; omega))
    · exact sdisj hp f (by lom) (.inr (by simp only [KEM.WK]; omega))
    · exact below_R hp hp.scb (hp.fs f)
    · exact sdisj hp f (by lom) h2
  have c₂ : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ (CB P)) P.ctLen = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem := by
    rw [far₂ (by lom) (by lom) (by lom)]; exact c₁
  have kp₂ : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (deL P) s₀ KP) 32 = (gD P s₀).1 := by
    rw [far₂ (by lom) (by decide) (by decide)]; exact kp₁
  have x24₂ : s₂.gpr .x24 = sB.gpr .x24 := by rw [k₂.cs _ (by decide) (by decide), e₁.x24]
  -- `c = c'`
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Decaps.cmp_ok hp kb₂ c₂) fun s₃ ⟨k₃, m₃, x₃⟩ => ?_)
  have kb₃ := kb₂.block k₃ m₃ (by decide)
  -- the key
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.AArch64.Decaps.sel_ok hp kb₃ (e := decide (cD P s₀ = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem)) (by
    rw [x₃]; by_cases h : cD P s₀ = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem <;> simp [h])) fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact safe_R hp (b := 2) ⟨by dek, by dek⟩ (by dek) (.inl (by dek))
  refine WP.mono (epilogue_ok hp kb₄) fun s' ⟨abi, x0, hm⟩ => ⟨abi, ?_, ?_⟩
  · rw [x0, k₄.get .x24, k₃.get .x24, x24₂]
  · rw [hm, b₄, m₃, kp₂, jb₂]
    by_cases h : cD P s₀ = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem <;> simp [h]

/-! ## Correctness -/

theorem post_of {s₀ sB s' : State} {mA : Mem} (hB : BInv P (deL P) s₀ mA (rhoD P s₀) (P.k * P.k) sB)
    (hD : VG.Proof.MlKem.AArch64.Decaps.Done P s₀ sB.mem (sB.gpr .x24) s') : (decapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => decapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.dkLen)
    (bytesAt s₀.mem (s₀.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s₀.gpr .x2) 32)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 =
      if cD P s₀ = VG.Proof.MlKem.AArch64.Decaps.cpr P s₀ sB.mem then (gD P s₀).1 else VG.Proof.MlKem.AArch64.Decaps.jD P s₀ := hD.key
  rw [key, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩ (a := aM P (deL P) s₀ sB.mem)
      fun i hi j hj => by rw [KPke.ekRho_dkEk]; exact hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show decapsInternal P.params 280 (dkD P s₀) (cD P s₀) = none
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj (by rw [KPke.ekRho_dkEk]; exact hn)]
    rfl

theorem correct (hP : P.Wf) (hc : Calls P) {s₀ : State} (hs : (decapsAArch64 P).pre s₀) :
    WP isa (P.decapsWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ (decapsAArch64 P).post s₀ s' := by
  have hp := pre_of hP hs
  exact WP.seq (WP.mono (a_ok hp hc) fun _ hA => WP.seq (WP.mono
    (matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho)) fun _ hB =>
    WP.mono (VG.Proof.MlKem.AArch64.Decaps.c_ok hp hc hA hB) fun _ hD => ⟨hD.abi, VG.Proof.MlKem.AArch64.Decaps.post_of hB hD⟩))

/-! ## Constant time -/

/-- The taint analyses of `P`'s code, decided for each parameter set: the
code before and after the matrix (with the Keccak functions `keccak`), and
the arguments of each `sample_ntt`. -/
structure DeTaints (P : KemLay) (keccak : VG.Proof.Sha3.AArch64.Permutation) : Prop where
  a : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (P.deAWith keccak.callee) h).isSome = true
  c : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (P.deCWith keccak.callee) h).isSome = true
  setup : SetupTaint P

/-- Two runs from states the contract relates. -/
abbrev Pub3 (P : KemLay) (σ₁ σ₂ : State) : Prop :=
  (decapsAArch64 P).pre σ₁ ∧ (decapsAArch64 P).pre σ₂ ∧ (decapsAArch64 P).pub σ₁ σ₂

theorem Pub3.two (hP : P.Wf) {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.Decaps.Pub3 P σ₁ σ₂) : Two P (deL P) σ₁ σ₂ :=
  ⟨pre_of hP h.1, pre_of hP h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem Pub3.rho {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.Decaps.Pub3 P σ₁ σ₂) : rhoD P σ₁ = rhoD P σ₂ :=
  map_toNat_inj h.2.2.2.2.2.2.2

theorem b_rct (hP : P.Wf) (ht : VG.Proof.MlKem.AArch64.Decaps.DeTaints P keccak) :
    RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, VG.Proof.MlKem.AArch64.Decaps.Pub3 P σ₁ σ₂ ∧ AfterA P σ₁ s₁ ∧ AfterA P σ₂ s₂)
      (P.kemMatrixWith keccak.callee)
    fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, VG.Proof.MlKem.AArch64.Decaps.Pub3 P σ₁ σ₂ ∧ BInv P (deL P) σ₁ m₁ (rhoD P σ₁) (P.k * P.k) s₁ ∧
      BInv P (deL P) σ₂ m₂ (rhoD P σ₁) (P.k * P.k) s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State × Mem × Mem) s₁ s₂ =>
      VG.Proof.MlKem.AArch64.Decaps.Pub3 P x.1 x.2.1 ∧ BInv P (deL P) x.1 x.2.2.1 (rhoD P x.1) 0 s₁ ∧
        BInv P (deL P) x.2.1 x.2.2.2 (rhoD P x.1) 0 s₂)
      fun x => ?_)
    (fun s₁ s₂ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂, s₁.mem, s₂.mem), hpub, BInv.zero a₁.kb a₁.x24 a₁.rho,
      BInv.zero a₂.kb a₂.x24 (by rw [a₂.rho, hpub.rho])⟩) fun _ _ h => h
  by_cases hpub : VG.Proof.MlKem.AArch64.Decaps.Pub3 P x.1 x.2.1
  · exact RelCT.mono (matrix_rct ht.setup (hpub.two hP)) (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hpub, h⟩
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct (hP : P.Wf) (ht : VG.Proof.MlKem.AArch64.Decaps.DeTaints P keccak) :
    RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, VG.Proof.MlKem.AArch64.Decaps.Pub3 P σ₁ σ₂ ∧ BInv P (deL P) σ₁ m₁ (rhoD P σ₁) (P.k * P.k) s₁ ∧
      BInv P (deL P) σ₂ m₂ (rhoD P σ₁) (P.k * P.k) s₂) (P.deCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (fun s₁ s₂ ⟨σ₁, σ₂, m₁, m₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, (hpub.two hP).sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25]; exact hpub.2.2.1
      · rw [b₁.kb.x26, b₂.kb.x26]; exact hpub.2.2.2.1
      · rw [b₁.kb.x27, b₂.kb.x27]; exact hpub.2.2.2.2.1
      · rw [b₁.kb.x28, b₂.kb.x28]; exact hpub.2.2.2.2.2.1) ht.c.choose_spec

theorem ct (hP : P.Wf) (hc : Calls P) (ht : VG.Proof.MlKem.AArch64.Decaps.DeTaints P keccak) :
    ConstantTime isa (decapsAArch64 P).pre (decapsAArch64 P).pub (P.decapsWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, -, -⟩ := h
        simp [e0, e1, e2, e3])) ht.a.choose_spec).wpDep (F := fun σ s => AfterA P σ s)
      fun _ _ h => ⟨a_ok (pre_of hP h.1) hc, a_ok (pre_of hP h.2.1) hc⟩)
    (RelCT.seq (VG.Proof.MlKem.AArch64.Decaps.b_rct hP ht) (VG.Proof.MlKem.AArch64.Decaps.c_rct hP ht)))

theorem decaps_correct (hP : P.Wf) (hc : Calls P) {s : State} (hs : (decapsAArch64 P).pre s) :
    ∃ t s', Exec isa (P.decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (decapsAArch64 P).post s s' :=
  VG.Proof.MlKem.AArch64.Decaps.correct hP hc hs

/-! ## ML-KEM-768 -/

theorem taints768 : VG.Proof.MlKem.AArch64.Decaps.DeTaints lay768 keccak :=
  ⟨keccak.mlkemDeATaint, keccak.mlkemDeCTaint, Encaps.setupTaint768⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem decaps_correctWith (s : State) (hs : (decapsAArch64 lay768).pre s) :
    ∃ t s', Exec isa (decapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (decapsAArch64 lay768).post s s' :=
  VG.Proof.MlKem.AArch64.Decaps.decaps_correct KeyGen.wf768 Encaps.calls768 hs

theorem decaps_verifiedWith :
    Verified AArch64.target (decapsWith keccak.callee) (Spec.MlKem.decapsContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.MlKem.AArch64.Decaps.decaps_correctWith (keccak := keccak)) (VG.Proof.MlKem.AArch64.Decaps.ct KeyGen.wf768 Encaps.calls768 VG.Proof.MlKem.AArch64.Decaps.taints768) (by
    mlkem_implies [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, decapsAArch64, lay768, KemLay.params,
      Spec.MlKem.mlKem768, KemLay.dkLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat] using VG.Proof.MlKem.AArch64.Decaps.sat)

theorem decaps_verified :
    Verified AArch64.target decaps (Spec.MlKem.decapsContract AArch64.abi 16) :=
  VG.Proof.MlKem.AArch64.Decaps.decaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.Decaps

end
