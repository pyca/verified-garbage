import VerifiedGarbage.Proof.Mont.X86.Chain

/-!
# Montgomery arithmetic on x86 (32-bit): the conditional subtraction

`csub M src o` reduces the number `T < 2m` at `[src]` (`N` words and a top
word) below `m` into `[o]` (`csub_ok`): `[tmp] = [src] - [mo]` with its
borrow (`diffs`, a chain), then the top word minus the borrow, whose own
borrow makes the mask `eax` (all ones if `T ≥ m`, `mask_ok`), which
selects `[tmp]` or `[src]` word by word (`selects_ok`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The first `k` words of `selects`. -/
def selK (src o tmp k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    [.mov .ebx (.mem (sc (src + 4 * j))), .mov .edx (.mem (sc (tmp + 4 * j))), .alu .xor .edx (.reg .ebx),
      .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc (o + 4 * j)) .ebx]

theorem selects_eq (M : Mod) (src o : Nat) : selects M src o = selK src o M.tmp (words M) := rfl

theorem selK_succ (src o tmp k : Nat) : selK src o tmp (k + 1) = selK src o tmp k ++
    [.mov .ebx (.mem (sc (src + 4 * k))), .mov .edx (.mem (sc (tmp + 4 * k))), .alu .xor .edx (.reg .ebx),
      .alu .and .edx (.reg .eax), .alu .xor .ebx (.reg .edx), .store (sc (o + 4 * k)) .ebx] := by
  simp only [selK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The selection of a word by a mask. -/
theorem select_val (b d : BitVec 32) (k : Bool) :
    b ^^^ ((d ^^^ b) &&& (if k then BitVec.allOnes 32 else 0)) = if k then d else b := by
  cases k
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm d b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `[o] = [tmp]` if `k`, else `[src]`, under the mask `eax` (`k + 1` words). -/
theorem selects_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src o tmp : Nat} (k : Bool)
    (hm : s.gpr .eax = if k then BitVec.allOnes 32 else 0) :
    ∀ n, src + 4 * n ≤ size → tmp + 4 * n ≤ size → o + 4 * n ≤ size →
    (o + 4 * n ≤ src ∨ src + 4 * n ≤ o) → (o + 4 * n ≤ tmp ∨ tmp + 4 * n ≤ o) →
    WP isa (.block (selK src o tmp n)) s fun u =>
      Outside base o (4 * n) s.mem u.mem ∧
      val32 u.mem base o n = val32 s.mem base (if k then tmp else src) n ∧
      Keeps [.ebx, .edx] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | n + 1, hsrc, htmp, ho, hso, hto => by
    have hn := hs.nowrap
    rw [selK_succ]
    refine WP.block_append (WP.mono (selects_ok hs k hm n (by omega) (by omega) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine wp_movS (readSrc_sc hs₁ (d := src + 4 * n) (by omega)) fun s₂ u₂ _ => ?_
    have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
    refine wp_movS (readSrc_sc hs₂ (d := tmp + 4 * n) (by omega)) fun s₃ u₃ _ => ?_
    have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
    refine wp_logicS (.inr rfl) rfl fun s₄ u₄ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
    refine wp_logicS (.inr rfl) rfl fun s₆ u₆ => ?_
    have k₆ : Keeps [.ebx, .edx] s s₆ := (((K₁.widen u₂.keeps).widen u₃.keeps).widen u₄.keeps |>.widen
      u₅.keeps).widen u₆.keeps
    have hs₆ := hs.of_keeps k₆ (by decide)
    refine wp_storeS (hs₆.ea (d := o + 4 * n) (by omega)) (hs₆.write (d := o + 4 * n) (n := 4) (by omega))
      fun s₇ m₇ => WP.block_nil ?_
    have mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    have W : Outside base (o + 4 * n) 4 s₁.mem s₇.mem := by
      rw [m₇.mem, mem₆]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨(O₁.mono (o' := o) (n' := 4 * (n + 1)) (Nat.le_refl _) (by omega)).trans
      (W.mono (o' := o) (n' := 4 * (n + 1)) (by omega) (by omega)), ?_,
      k₆.trans (m₇.keeps _)⟩
    have eax₄ : s₄.gpr .eax = s.gpr .eax := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), K₁.1 _ (by decide)]
    have ebx₆ : s₆.gpr .ebx = s₁.mem.readW (off base (src + 4 * n)) 32 ^^^
        ((s₁.mem.readW (off base (tmp + 4 * n)) 32 ^^^ s₁.mem.readW (off base (src + 4 * n)) 32) &&&
          (if k then BitVec.allOnes 32 else 0)) := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₄.gpr, eax₄, hm,
        u₃.other _ (by decide), u₃.gpr, u₂.gpr, u₂.mem]
      rfl
    rw [select_val] at ebx₆
    rw [val32_succ, val32_succ, ← V₁, m₇.mem, mem₆,
      (writeW32_outside s₁.mem base (d := o + 4 * n) (s₆.gpr .ebx) (by omega)).val32 (by omega) (by omega),
      w32_write_self, ebx₆]
    congr 1
    cases k
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))
    · exact congrArg (2 ^ (32 * n) * ·) (O₁.w32 (by omega) (by omega))

/-- The mask from a borrow: `sbb eax, eax`, then `xor eax, -1`. -/
theorem mask_val (x : BitVec 32) (b : Bool) :
    (x - x - (BitVec.ofBool b).setWidth 32) ^^^ (-1) = if !b then BitVec.allOnes 32 else 0 := by
  rw [BitVec.sub_self]
  cases b <;> decide

/-- `[o] = T mod m` for the number `T < 2m` at `[src]` (`N` words and the
top word), through `[tmp]`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {N src o m : Nat}
    (hNw : words M = N) (hN : 0 < N) (hsrc : src + 4 * (N + 1) ≤ size) (ho : o + 4 * N ≤ size)
    (htmp : M.tmp + 4 * N ≤ size) (hmo : M.mo + 4 * N ≤ size)
    (hts : M.tmp + 4 * N ≤ src ∨ src + 4 * (N + 1) ≤ M.tmp) (htm : M.tmp + 4 * N ≤ M.mo ∨ M.mo + 4 * N ≤ M.tmp)
    (hos : o + 4 * N ≤ src ∨ src + 4 * N ≤ o) (hot : o + 4 * N ≤ M.tmp ∨ M.tmp + 4 * N ≤ o)
    (hm : val32 s.mem base M.mo N = m) (hV : val32 s.mem base src (N + 1) < 2 * m) :
    WP isa (.block (csub M src o)) s fun u =>
      Outs base [(M.tmp, 4 * N), (o, 4 * N)] s.mem u.mem ∧
      val32 u.mem base o N = val32 s.mem base src (N + 1) % m ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hn := hs.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [csub, diffs_eq, selects_eq, hNw, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (chainSub_ok hs k (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨O₁, ⟨c, hc, V₁⟩, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS (readSrc_sc hs₁ (d := src + 4 * (k + 1)) (by omega)) fun s₂ u₂ cf₂ => ?_
  refine wp_sbbS rfl (by rw [cf₂]; exact hc) fun s₃ u₃ c₃ => ?_
  refine wp_sbbS rfl c₃ fun s₄ u₄ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  have k₅ : Keeps [.eax, .ebx, .edx] s s₅ :=
    (((K₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps |>.widen u₄.keeps).widen u₅.keeps
  have hs₅ := hs.of_keeps k₅ (by decide)
  have mask := u₅.gpr
  simp only [reduceCtorEq, ite_false] at mask
  rw [u₄.gpr, mask_val] at mask
  have mem₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have z : (0 : BitVec 32).toNat = 0 := rfl
  have top : (s₂.gpr .eax).toNat = w32 s.mem base (src + 4 * (k + 1)) := by
    rw [u₂.gpr, ← O₁.w32 (by omega) (by omega)]
  rw [top, z, Nat.zero_add] at mask
  have hsrcN : val32 s₁.mem base src (k + 1) = val32 s.mem base src (k + 1) := O₁.val32 (by omega) (by omega)
  refine WP.mono (selects_ok hs₅ _ mask (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun u ⟨O, V, K⟩ => ⟨(Outs.of_outside O₁ (by simp)).trans (Outs.of_outside (mem₅ ▸ O) (by simp)), ?_,
      k₅.trans (K.mono (by decide))⟩
  rw [V, mem₅]
  have hmX : m < 2 ^ (32 * (k + 1)) := hm ▸ val32_lt _ _ _ _
  have := csub_arith (T := val32 s.mem base src (k + 1)) (D := val32 s₁.mem base M.tmp (k + 1))
    (top := w32 s.mem base (src + 4 * (k + 1))) (b := c) hmX (val32_lt _ _ _ _)
    (by rw [← val32_succ]; exact hV) (by rw [← hm]; exact V₁)
  rw [val32_succ s.mem base src (k + 1), ← this]
  by_cases h : w32 s.mem base (src + 4 * (k + 1)) < c.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hsrcN]
  · simp only [h, decide_false, Bool.not_false, ite_true, ite_false]

end VG.Proof.Mont.X86
