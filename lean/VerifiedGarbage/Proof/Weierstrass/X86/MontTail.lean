import VerifiedGarbage.Proof.Weierstrass.X86.MontMul
import VerifiedGarbage.Proof.Mont.X86.Csub

/-!
# Montgomery arithmetic as functions on x86 (32-bit): chains and the result

Chains of additions and subtractions word by word through one register `r`
(`chainK`): `[dst j] = x j op y j`, for words `x j` and `y j` from any source
that the chain's own stores leave alone (`SrcOk`), and stores at offsets
`D + 4j` of the working space (`DstOk`): `chainKAdd_ok`, `chainKSub_ok`.
The functions' chains are such chains: the sum or difference of `[a]` and
`[b]` through pointers (`chainP`), the difference with `m` (`diffsI`), and
the sum into `[o]` through a pointer (`addOut`). Then the mask of the
conditional subtraction (`maskTop_ok`), the selection into `[o]`
(`selectsP_ok`), and the masked modulus (`maskedI_ok`).
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The first `k` words of a chain through `r`: `[dst j] = x j op y j`, with
`op` on the first word and `op'` on the others. -/
def chainK (r : Reg) (x : Nat → Src) (op op' : AluOp) (y : Nat → Src) (dst : Nat → MemOp) (k : Nat) :
    List Instr :=
  (List.range k).flatMap fun j => [.mov r (x j), .alu (if j = 0 then op else op') r (y j), .store (dst j) r]

theorem chainK_succ (r : Reg) (x : Nat → Src) (op op' : AluOp) (y : Nat → Src) (dst : Nat → MemOp) (k : Nat) :
    chainK r x op op' y dst (k + 1) = chainK r x op op' y dst k ++
      ([.mov r (x k), .alu (if k = 0 then op else op') r (y k), .store (dst k) r] : List Instr) := by
  simp only [chainK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The words `x j` (`j < N`) read `X j` in any state with the registers
but `r`, the regions, and the memory but the chain's `N` words at `D`. -/
def SrcOk (x : Nat → Src) (X : Nat → BitVec 32) (r : Reg) (base : Addr) (D N : Nat) (s : State) : Prop :=
  ∀ j < N, ∀ t : State, (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.rd = s.rd → t.wr = s.wr →
    Outside base D (4 * N) s.mem t.mem → readSrc t (x j) = some (X j)

/-- The stores `dst j` (`j < N`) are at `D + 4j`, writable, in any state with the
registers but `r` and the regions. -/
def DstOk (dst : Nat → MemOp) (r : Reg) (base : Addr) (D N : Nat) (s : State) : Prop :=
  ∀ j < N, ∀ t : State, (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.wr = s.wr →
    t.ea (dst j) = off base (D + 4 * j) ∧ InRegions t.wr (off base (D + 4 * j)) 4

variable {s : State} {base : Addr} {size : Nat}

/-- A word of an addition, with the carry in `cin` (none for `add`). -/
theorem wordAdd_ok {r : Reg} {xs ys : Src} {X Y : BitVec 32} {op : AluOp} {cin : Bool} {dst : MemOp} {D : Nat}
    (hop : (op = .add ∧ cin = false) ∨ (op = .adc ∧ s.cf = some cin))
    (hx : readSrc s xs = some X) (hy : ∀ t, Upd s t r X → readSrc t ys = some Y)
    (hd : ∀ t : State, (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.wr = s.wr → t.ea dst = off base D)
    (hw : InRegions s.wr (off base D) 4) (hD : D + 4 ≤ 2 ^ 64) :
    WP isa (.block [.mov r xs, .alu op r ys, .store dst r]) s fun u =>
      Outside base D 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base D + 2 ^ 32 * c.toNat = X.toNat + Y.toNat + cin.toNat) ∧
      Keeps [r] s u := by
  refine wp_movS hx fun s₁ u₁ cf₁ => ?_
  have hy₁ := hy s₁ u₁
  have hX := X.isLt
  have hY := Y.isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_addS hy₁ fun s₂ u₂ c₂ => ?_
    refine wp_storeS (hd s₂ (fun q hq => by rw [u₂.other _ hq, u₁.other _ hq]) (by rw [u₂.wr, u₁.wr]))
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ =>
      WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ hD
    · rw [m₃.mem, w32_write_self, u₂.gpr, BitVec.toNat_add, u₁.gpr]
      by_cases h : 2 ^ 32 ≤ X.toNat + Y.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_adcS hy₁ (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    refine wp_storeS (hd s₂ (fun q hq => by rw [u₂.other _ hq, u₁.other _ hq]) (by rw [u₂.wr, u₁.wr]))
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ =>
      WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ hD
    · rw [m₃.mem, w32_write_self, u₂.gpr, add3_toNat, u₁.gpr]
      have := Bool.toNat_le cin
      by_cases h : 2 ^ 32 ≤ X.toNat + Y.toNat + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A word of a subtraction, with the borrow in `cin` (none for `sub`). -/
theorem wordSub_ok {r : Reg} {xs ys : Src} {X Y : BitVec 32} {op : AluOp} {cin : Bool} {dst : MemOp} {D : Nat}
    (hop : (op = .sub ∧ cin = false) ∨ (op = .sbb ∧ s.cf = some cin))
    (hx : readSrc s xs = some X) (hy : ∀ t, Upd s t r X → readSrc t ys = some Y)
    (hd : ∀ t : State, (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.wr = s.wr → t.ea dst = off base D)
    (hw : InRegions s.wr (off base D) 4) (hD : D + 4 ≤ 2 ^ 64) :
    WP isa (.block [.mov r xs, .alu op r ys, .store dst r]) s fun u =>
      Outside base D 4 s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ w32 u.mem base D + Y.toNat + cin.toNat = X.toNat + 2 ^ 32 * c.toNat) ∧
      Keeps [r] s u := by
  refine wp_movS hx fun s₁ u₁ cf₁ => ?_
  have hy₁ := hy s₁ u₁
  have hX := X.isLt
  have hY := Y.isLt
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · refine wp_subS hy₁ fun s₂ u₂ c₂ => ?_
    refine wp_storeS (hd s₂ (fun q hq => by rw [u₂.other _ hq, u₁.other _ hq]) (by rw [u₂.wr, u₁.wr]))
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ =>
      WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ hD
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub_toNat, u₁.gpr]
      by_cases h : X.toNat < Y.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega
  · refine wp_sbbS hy₁ (by rw [cf₁]; exact hc) fun s₂ u₂ c₂ => ?_
    refine wp_storeS (hd s₂ (fun q hq => by rw [u₂.other _ hq, u₁.other _ hq]) (by rw [u₂.wr, u₁.wr]))
      (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ =>
      WP.block_nil ⟨?_, ⟨_, by rw [m₃.cf, c₂], ?_⟩, (u₁.keeps.trans (u₂.keeps)).trans (m₃.keeps _)⟩
    · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ hD
    · rw [m₃.mem, w32_write_self, u₂.gpr, sub3_toNat, u₁.gpr]
      have := Bool.toNat_le cin
      by_cases h : X.toNat < Y.toNat + cin.toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `[dst] = x + y` (`k + 1` words at `D`), and the carry. -/
theorem chainKAdd_ok {r : Reg} {x y : Nat → Src} {X Y : Nat → BitVec 32} {dst : Nat → MemOp} {D N : Nat}
    (hX : SrcOk x X r base D N s) (hY : SrcOk y Y r base D N s) (hDst : DstOk dst r base D N s)
    (hDN : D + 4 * N ≤ 2 ^ 64) :
    ∀ k, k + 1 ≤ N →
    WP isa (.block (chainK r x .add .adc y dst (k + 1))) s fun u =>
      Outside base D (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base D (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat =
        yVal X (k + 1) + yVal Y (k + 1)) ∧
      Keeps [r] s u
  | 0, hk => by
    rw [show chainK r x .add .adc y dst (0 + 1) = [.mov r (x 0), .alu .add r (y 0), .store (dst 0) r] from rfl]
    have hd := hDst 0 (by omega) s (fun _ _ => rfl) rfl
    refine WP.mono (wordAdd_ok (D := D) (.inl ⟨rfl, rfl⟩)
      (hX 0 (by omega) s (fun _ _ => rfl) rfl rfl (Outside.refl _ _ _ _))
      (fun t u => hY 0 (by omega) t u.other u.rd u.wr (by rw [u.mem]; exact Outside.refl _ _ _ _))
      (fun t ht hw => (hDst 0 (by omega) t ht hw).1.trans (by simp))
      (by simpa using hd.2) (by omega)) fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false, yVal, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add] at V ⊢
    exact V
  | k + 1, hk => by
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainKAdd_ok hX hY hDst hDN k (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have O₁' : Outside base D (4 * N) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega)
    have K₁r : ∀ q, q ≠ r → s₁.gpr q = s.gpr q := fun q hq => K₁.1 q (fun h => hq (List.mem_singleton.mp h))
    have hd := hDst (k + 1) (by omega) s₁ K₁r K₁.2.2
    refine WP.mono (wordAdd_ok (D := D + 4 * (k + 1)) (.inr ⟨rfl, hc₁⟩)
      (hX (k + 1) (by omega) s₁ K₁r K₁.2.1 K₁.2.2 O₁')
      (fun t u => hY (k + 1) (by omega) t (fun q hq => by
          by_cases h : q = r
          · subst h; exact absurd rfl hq
          · rw [u.other _ h, K₁r _ hq]) (by rw [u.rd, K₁.2.1]) (by rw [u.wr, K₁.2.2])
        (by rw [u.mem]; exact O₁'))
      (fun t ht hw => (hDst (k + 1) (by omega) t (fun q hq => by rw [ht _ hq, K₁r _ hq])
        (by rw [hw, K₁.2.2])).1) hd.2 (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
        ⟨c, hc, ?_⟩, K₁.trans K⟩
    have eX : yVal X (k + 1 + 1) = yVal X (k + 1) + 2 ^ (32 * (k + 1)) * (X (k + 1)).toNat := rfl
    have eY : yVal Y (k + 1 + 1) = yVal Y (k + 1) + 2 ^ (32 * (k + 1)) * (Y (k + 1)).toNat := rfl
    rw [val32_succ u.mem base D (k + 1), O.val32 (by omega) (by omega), pow32_succ (k + 1), eX, eY]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

/-- `[dst] = x - y` (`k + 1` words at `D`), and the borrow. -/
theorem chainKSub_ok {r : Reg} {x y : Nat → Src} {X Y : Nat → BitVec 32} {dst : Nat → MemOp} {D N : Nat}
    (hX : SrcOk x X r base D N s) (hY : SrcOk y Y r base D N s) (hDst : DstOk dst r base D N s)
    (hDN : D + 4 * N ≤ 2 ^ 64) :
    ∀ k, k + 1 ≤ N →
    WP isa (.block (chainK r x .sub .sbb y dst (k + 1))) s fun u =>
      Outside base D (4 * (k + 1)) s.mem u.mem ∧
      (∃ c, u.cf = some c ∧ val32 u.mem base D (k + 1) + yVal Y (k + 1) =
        yVal X (k + 1) + 2 ^ (32 * (k + 1)) * c.toNat) ∧
      Keeps [r] s u
  | 0, hk => by
    rw [show chainK r x .sub .sbb y dst (0 + 1) = [.mov r (x 0), .alu .sub r (y 0), .store (dst 0) r] from rfl]
    have hd := hDst 0 (by omega) s (fun _ _ => rfl) rfl
    refine WP.mono (wordSub_ok (D := D) (.inl ⟨rfl, rfl⟩)
      (hX 0 (by omega) s (fun _ _ => rfl) rfl rfl (Outside.refl _ _ _ _))
      (fun t u => hY 0 (by omega) t u.other u.rd u.wr (by rw [u.mem]; exact Outside.refl _ _ _ _))
      (fun t ht hw => (hDst 0 (by omega) t ht hw).1.trans (by simp))
      (by simpa using hd.2) (by omega)) fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨O, ⟨c, hc, ?_⟩, K⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Bool.toNat_false, yVal, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add] at V ⊢
    exact V
  | k + 1, hk => by
    rw [chainK_succ, ite_eq_right_of_eq_false _ _ (eq_false (Nat.add_one_ne_zero k))]
    refine WP.block_append (WP.mono (chainKSub_ok hX hY hDst hDN k (by omega))
      fun s₁ ⟨O₁, ⟨c₁, hc₁, V₁⟩, K₁⟩ => ?_)
    have O₁' : Outside base D (4 * N) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega)
    have K₁r : ∀ q, q ≠ r → s₁.gpr q = s.gpr q := fun q hq => K₁.1 q (fun h => hq (List.mem_singleton.mp h))
    have hd := hDst (k + 1) (by omega) s₁ K₁r K₁.2.2
    refine WP.mono (wordSub_ok (D := D + 4 * (k + 1)) (.inr ⟨rfl, hc₁⟩)
      (hX (k + 1) (by omega) s₁ K₁r K₁.2.1 K₁.2.2 O₁')
      (fun t u => hY (k + 1) (by omega) t (fun q hq => by
          by_cases h : q = r
          · subst h; exact absurd rfl hq
          · rw [u.other _ h, K₁r _ hq]) (by rw [u.rd, K₁.2.1]) (by rw [u.wr, K₁.2.2])
        (by rw [u.mem]; exact O₁'))
      (fun t ht hw => (hDst (k + 1) (by omega) t (fun q hq => by rw [ht _ hq, K₁r _ hq])
        (by rw [hw, K₁.2.2])).1) hd.2 (by omega))
      fun u ⟨O, ⟨c, hc, V⟩, K⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O.mono (by omega) (by omega)),
        ⟨c, hc, ?_⟩, K₁.trans K⟩
    have eX : yVal X (k + 1 + 1) = yVal X (k + 1) + 2 ^ (32 * (k + 1)) * (X (k + 1)).toNat := rfl
    have eY : yVal Y (k + 1 + 1) = yVal Y (k + 1) + 2 ^ (32 * (k + 1)) * (Y (k + 1)).toNat := rfl
    rw [val32_succ u.mem base D (k + 1), O.val32 (by omega) (by omega), pow32_succ (k + 1), eX, eY]
    generalize 2 ^ (32 * (k + 1)) = P at *
    grind

/-! ## The conditional subtraction -/

/-- The mask of `maskTop`: the top word minus the borrow `c`, whose own
borrow makes `eax` all ones if it does not borrow. -/
theorem maskTop_ok (hb : Bx s base size) {src N : Nat} {c : Bool} (hc : s.cf = some c)
    (hd : src + 4 * N + 4 ≤ size) :
    WP isa (.block (maskTop src N)) s fun u =>
      u.gpr .eax = (if !decide (w32 s.mem base (src + 4 * N) < c.toNat) then BitVec.allOnes 32 else 0) ∧
      u.mem = s.mem ∧ Keeps [.eax] s u := by
  simp only [maskTop]
  refine wp_movS (readSrc_bp hb hd) fun s₂ u₂ cf₂ => ?_
  refine wp_sbbS rfl (by rw [cf₂]; exact hc) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mask := u₅.gpr
    simp only [reduceCtorEq, ite_false] at mask
    rw [mask, u₄.gpr, mask_val]
    have z : (0 : BitVec 32).toNat = 0 := rfl
    rw [u₂.gpr, z, Nat.zero_add]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  · exact ((u₂.keeps.widen u₃.keeps).widen u₄.keeps).widen u₅.keeps

/-- The first `k` words of `selectsP`. -/
def selP (src tmp k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .edx (.mem (bp (src + 4 * j))), .alu .xor .edx (.mem (bp (tmp + 4 * j))), .alu .and .edx (.reg .eax),
      .alu .xor .edx (.mem (bp (src + 4 * j))), .store (at_ .ecx (4 * j)) .edx]

theorem selP_succ (src tmp k : Nat) : selP src tmp (k + 1) = selP src tmp k ++
    ([.mov .edx (.mem (bp (src + 4 * k))), .alu .xor .edx (.mem (bp (tmp + 4 * k))), .alu .and .edx (.reg .eax),
      .alu .xor .edx (.mem (bp (src + 4 * k))), .store (at_ .ecx (4 * k)) .edx] : List Instr) := by
  simp only [selP, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `[ecx] = [tmp]` if `k`, else `[src]`, under the mask `eax`, `ecx` pointing to
`po`, apart from both. -/
theorem selP_ok (hb : Bx s base size) {src tmp po : Nat} (hpo : Ptr s .ecx po) (k : Bool)
    (hm : s.gpr .eax = if k then BitVec.allOnes 32 else 0) :
    ∀ n, src + 4 * n ≤ size → tmp + 4 * n ≤ size → po + 4 * n ≤ size →
    (po + 4 * n ≤ src ∨ src + 4 * n ≤ po) → (po + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ po) →
    WP isa (.block (selP src tmp n)) s fun u =>
      Outside base po (4 * n) s.mem u.mem ∧
      val32 u.mem base po n = val32 s.mem base (if k then tmp else src) n ∧
      Keeps [.edx] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | n + 1, hsrc, htmp, ho, hso, hto => by
    have hn := hb.nowrap
    rw [selP_succ]
    refine WP.block_append (WP.mono (selP_ok hb hpo k hm n (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    refine wp_movS (readSrc_bp hb₁ (d := src + 4 * n) (by omega)) fun s₂ u₂ _ => ?_
    have hb₂ := hb₁.of_keeps u₂.keeps (by decide)
    refine wp_logicS (.inr rfl) (readSrc_bp hb₂ (d := tmp + 4 * n) (by omega)) fun s₃ u₃ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
    have hb₄ := hb₂.of_keeps (u₃.keeps.widen u₄.keeps) (by decide)
    refine wp_logicS (.inr rfl) (readSrc_bp hb₄ (d := src + 4 * n) (by omega)) fun s₅ u₅ => ?_
    have k₅ : Keeps [.edx] s s₅ := (((K₁.widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
    have hb₅ := hb.of_keeps k₅ (by decide)
    have hpo₅ : Ptr s₅ .ecx po := hpo.of_keeps k₅ (by decide) (by decide)
    refine wp_storeS (hb₅.ea_ptr hpo₅ (d := 4 * n) (by omega)) (hb₅.write (d := po + 4 * n) (n := 4) (by omega))
      fun s₆ m₆ => WP.block_nil ?_
    have mem₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have W : Outside base (po + 4 * n) 4 s₁.mem s₆.mem := by
      rw [m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O₁.mono (o' := po) (n' := 4 * (n + 1)) (Nat.le_refl _) (by omega)).trans
      (W.mono (o' := po) (n' := 4 * (n + 1)) (by omega) (by omega)), ?_, k₅.trans (m₆.keeps _)⟩
    have eax₃ : s₃.gpr .eax = s.gpr .eax := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), K₁.1 _ (by decide)]
    have g₃ : s₃.gpr .edx = s₁.mem.readW (off base (src + 4 * n)) 32 ^^^ s₁.mem.readW (off base (tmp + 4 * n)) 32 := by
      rw [u₃.gpr]; simp only [reduceCtorEq, ite_false]; rw [u₂.gpr, u₂.mem]
    have g₄ : s₄.gpr .edx = s₃.gpr .edx &&& s.gpr .eax := by
      rw [u₄.gpr]; simp only [ite_true]; rw [eax₃]
    have g₅ : s₅.gpr .edx = s₄.gpr .edx ^^^ s₁.mem.readW (off base (src + 4 * n)) 32 := by
      rw [u₅.gpr]; simp only [reduceCtorEq, ite_false]; rw [u₄.mem, u₃.mem, u₂.mem]
    have xr : ∀ a b c : BitVec 32, (a ^^^ b) &&& c ^^^ a = a ^^^ ((b ^^^ a) &&& c) := by
      intro a b c; rw [BitVec.xor_comm a b, BitVec.xor_comm _ a]
    have edx₅ : s₅.gpr .edx = s₁.mem.readW (off base (src + 4 * n)) 32 ^^^
        ((s₁.mem.readW (off base (tmp + 4 * n)) 32 ^^^ s₁.mem.readW (off base (src + 4 * n)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [g₅, g₄, g₃, hm, xr]
    rw [select_val] at edx₅
    rw [val32_succ, val32_succ, ← V₁, m₆.mem, mem₅,
      (writeW32_outside s₁.mem base (d := po + 4 * n) (s₅.gpr .edx) (by omega)).val32 (by omega) (by omega),
      w32_write_self, edx₅]
    congr 1
    cases k
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))

/-- The first `k` words of `maskedI`. -/
def maskIK (m tmp k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .edx (.imm (mw m j)), .alu .and .edx (.reg .eax), .store (bp (tmp + 4 * j)) .edx]

theorem maskIK_succ (m tmp k : Nat) : maskIK m tmp (k + 1) = maskIK m tmp k ++
    ([.mov .edx (.imm (mw m k)), .alu .and .edx (.reg .eax), .store (bp (tmp + 4 * k)) .edx] : List Instr) := by
  simp only [maskIK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `[tmp] = m` if `c`, else zero, under the mask `eax`. -/
theorem maskIK_ok (hb : Bx s base size) (m tmp : Nat) (c : Bool)
    (hm : s.gpr .eax = if c then BitVec.allOnes 32 else 0) :
    ∀ k, tmp + 4 * k ≤ size →
    WP isa (.block (maskIK m tmp k)) s fun u =>
      Outside base tmp (4 * k) s.mem u.mem ∧
      val32 u.mem base tmp k = (if c then yVal (mw m) k else 0) ∧ Keeps [.edx] s u
  | 0, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by cases c <;> rfl, Keeps.refl _ _⟩
  | k + 1, htmp => by
    have hn := hb.nowrap
    rw [maskIK_succ]
    refine WP.block_append (WP.mono (maskIK_ok hb m tmp c hm k (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    refine wp_movS rfl fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    have k₃ : Keeps [.edx] s s₃ := (K₁.widen u₂.keeps).widen u₃.keeps
    have hb₃ := hb.of_keeps k₃ (by decide)
    refine wp_storeS (hb₃.ea (d := tmp + 4 * k) (by omega)) (hb₃.write (d := tmp + 4 * k) (n := 4) (by omega))
      fun s₄ m₄ => WP.block_nil ⟨?_, ?_, k₃.trans (m₄.keeps _)⟩
    · rw [m₄.mem, u₃.mem, u₂.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
    · have heax : s₂.gpr .eax = s.gpr .eax := by rw [u₂.other _ (by decide), K₁.1 _ (by decide)]
      rw [val32_succ, m₄.mem, u₃.mem, u₂.mem, (writeW32_outside _ _ _ (by omega)).val32 (by omega) (by omega),
        w32_write_self, V₁, u₃.gpr, u₂.gpr, heax, hm]
      cases c
      · simp only [Bool.false_eq_true, ite_false]
        rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero]; rfl
      · simp only [ite_true, BitVec.and_allOnes, yVal]

end VG.Proof.Weierstrass.X86.Mont
