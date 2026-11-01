module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Call
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Weierstrass.Slots
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Short Weierstrass curves on RISC-V: copies, selections, the bit mask

`copy k o a` writes `[a]` to `[o]` (`copy_ok`, `k` 64-bit words), `sel k o a
b` writes `[a]` or `[b]` to `[o]` by the mask `a7` (`sel_ok`; `o` may be `a`
or `b`), `selPt` does so for the three coordinates of a point
(`selPt_ok`), as on PPC64LE (`Proof/Weierstrass/PPC64LE/Copy.lean`). Each
changes only `[o]` and caller-saved registers (`Kp`). `bitMask src` sets
`a7` to the mask of bit `s1` of the number at `src` (`bitMask_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Proof.Mont
open VG.Proof.X25519.RISCV64 (Rest wp_and)

/-- What writes only caller-saved registers keeps. -/
theorem Kp.of_rest {ws : List Reg} {s s' : State} (h : Rest ws s s') (hws : ∀ r ∈ ws, r ∉ preserved := by decide) :
    Kp s s' :=
  ⟨fun r hr => h.gpr r fun h' => hws r h' hr, h.rd, h.wr, h.sp⟩

theorem WsReg.of_rest {ws : List Reg} {s s' : State} {base : Addr} (h : WsReg s base) (k : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∉ preserved := by decide) : WsReg s' base := h.of_kp (Kp.of_rest k hws)

section
variable {s : State} {base : Addr} {is : List Instr} {Q : State → Prop}

/-- `ld t, d(s0)` in the working space. -/
theorem ld_ws (hw : WsReg s base) {t : Reg} {d : Nat} (hd : d < 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Upd s s' t (word s.mem base d) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t .s0 d :: is)) s Q := by
  have := hw.nowrap
  refine wp_ld hd (by rw [hw.s0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hw.al; omega)
    ⟨_, List.mem_append_right _ hw.wr, Offset.contains_base base (by omega) (by omega)⟩ k

/-- `sd t, d(s0)` in the working space. -/
theorem sd_ws (hw : WsReg s base) {t : Reg} {d : Nat} (hd : d < 2048) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t .s0 d :: is)) s Q := by
  have := hw.nowrap
  exact wp_sd hd (by rw [hw.s0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hw.al; omega)
    ⟨_, hw.wr, Offset.contains_base base (by omega) (by omega)⟩ k

end

/-- A word of `[a]` to `[o]`. -/
theorem copyWord_ok {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat} (ho : o < 2048) (ha : a < 2048)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) :
    WP isa (.block [.load .d .t0 wb a, .store .d .t0 wb o]) s fun u =>
      u.mem = s.mem.writeW (off base o) (word s.mem base a) ∧ Rest [.t0] s u := by
  refine ld_ws hw ha ha8 fun s₁ u₁ => ?_
  have K₁ := u₁.rest (ws := [.t0]) (by decide)
  refine sd_ws (hw.of_rest K₁) ho ho8 fun s₂ u₂ => WP.block_nil ⟨?_, K₁.trans (u₂.rest _)⟩
  rw [u₂.mem, u₁.mem, u₁.gpr]

/-- `[o] = [a]`, for `o` at or below `a` or apart from it. -/
theorem copy_ok : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    WsReg s base → o % 8 = 0 → a % 8 = 0 → o + 8 * k ≤ 2048 → a + 8 * k ≤ 2048 →
    (o ≤ a ∨ a + 8 * k ≤ o) →
    WP isa (.block (copy k o a)) s fun s' =>
      wordsVal s'.mem base o k = wordsVal s.mem base a k ∧ Rest [.t0] s s' ∧
      Outside base o (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hw, ho8, ha8, ho, ha, hsep => by
    have hn := hw.nowrap
    rw [copy, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x, y] ++ l from fun _ _ _ => rfl]
    refine WP.block_append (WP.mono (copyWord_ok hw (by omega) (by omega) ho8 ha8) fun s₁ ⟨m₁, K₁⟩ => ?_)
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (copy_ok k (hw.of_rest K₁) (o := o + 8) (a := a + 8) (by omega) (by omega)
      (by omega) (by omega) (by omega)) fun s₂ ⟨e₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rw [wordsVal, wordsVal, O₂.word (by omega) (by omega), e₂, O₁.wordsVal (by omega) (by omega), m₁,
      word_writeW_self]

/-- The selection by a mask. -/
theorem sel_mask' (x e : BitVec 64) (c : Bool) :
    x ^^^ ((e ^^^ x) &&& (if c then BitVec.allOnes 64 else 0)) = if c then e else x := by
  cases c
  · simp
  · simp only [↓reduceIte, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A word of `[a]` or `[b]` to `[o]` by the mask `a7`. -/
theorem selWord_ok {s : State} {base : Addr} (hw : WsReg s base) {o a b : Nat} (ho : o < 2048) (ha : a < 2048)
    (hb : b < 2048) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) :
    WP isa (.block [.load .d .t0 wb a, .load .d .t1 wb b, .logic .xor .t1 .t1 .t0, .logic .and .t1 .t1 .a7,
      .logic .xor .t0 .t0 .t1, .store .d .t0 wb o]) s fun u =>
      u.mem = s.mem.writeW (off base o) (word s.mem base a ^^^
        ((word s.mem base b ^^^ word s.mem base a) &&& s.gpr .a7)) ∧ Rest [.t0, .t1] s u := by
  refine ld_ws hw ha ha8 fun s₁ u₁ => ?_
  refine ld_ws (hw.of_rest (u₁.rest (ws := [.t0]) (by decide))) hb hb8 fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => wp_and fun s₄ u₄ => wp_xor fun s₅ u₅ => ?_
  have K₅ : Rest [.t0, .t1] s s₅ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans (u₅.rest (by decide)))))
  refine sd_ws (hw.of_rest K₅) ho ho8 fun s₆ u₆ => WP.block_nil ⟨?_, K₅.trans (u₆.rest _)⟩
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
  simp only [u₅.gpr, u₄.other .t0 (by decide), u₄.gpr, u₃.other .t0 (by decide), u₃.other .a7 (by decide),
    u₃.gpr, u₂.other .t0 (by decide), u₂.other .a7 (by decide), u₂.gpr, u₁.other .a7 (by decide), u₁.gpr,
    u₁.mem]

/-- `[o] = [b]` if the mask `a7` is all ones (`c`), `[a]` if it is zero; `o`
at or below `a` and `b`, or apart from them. -/
theorem sel_ok (c : Bool) : ∀ (k : Nat) {s : State} {base : Addr} {o a b : Nat},
    WsReg s base → s.gpr .a7 = (if c then BitVec.allOnes 64 else 0) →
    o % 8 = 0 → a % 8 = 0 → b % 8 = 0 → o + 8 * k ≤ 2048 → a + 8 * k ≤ 2048 → b + 8 * k ≤ 2048 →
    (o ≤ a ∨ a + 8 * k ≤ o) → (o ≤ b ∨ b + 8 * k ≤ o) →
    WP isa (.block (sel k o a b)) s fun s' =>
      wordsVal s'.mem base o k = (if c then wordsVal s.mem base b k else wordsVal s.mem base a k) ∧
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, Rest.refl _ _,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, b, hw, hc, ho8, ha8, hb8, ho, ha, hb, hsa, hsb => by
    have hn := hw.nowrap
    rw [sel, show ∀ (x₁ x₂ x₃ x₄ x₅ x₆ : Instr) (l : List Instr), [x₁, x₂, x₃, x₄, x₅, x₆] ++ l =
      [x₁, x₂, x₃, x₄, x₅, x₆] ++ l from fun _ _ _ _ _ _ _ => rfl]
    refine WP.block_append (WP.mono (selWord_ok hw (by omega) (by omega) (by omega) ho8 ha8 hb8)
      fun s₁ ⟨m₁, K₁⟩ => ?_)
    rw [hc, sel_mask'] at m₁
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (sel_ok c k (hw.of_rest K₁) (by rw [K₁.gpr _ (by decide)]; exact hc) (o := o + 8) (a := a + 8)
      (b := b + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) fun s₂ ⟨e₂, K₂, O₂⟩ => ⟨?_, K₁.trans K₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    have ea : wordsVal s₁.mem base (a + 8) k = wordsVal s.mem base (a + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have eb : wordsVal s₁.mem base (b + 8) k = wordsVal s.mem base (b + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    rw [wordsVal, O₂.word (by omega) (by omega), e₂, ea, eb, m₁, word_writeW_self]
    cases c <;> simp [wordsVal]

/-- `o = b` if the mask `a7` is all ones (`c`), `a` if it is zero, for points
whose slots (`n` 64-bit words, at multiples of 8) are in the first 2048 bytes
of the working space, with `o`'s apart from each other and from `a`'s and
`b`'s. -/
theorem selPt_ok {s : State} {base : Addr} (hw : WsReg s base)
    (c : Bool) (hc : s.gpr .a7 = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o a b : Pt}
    (h4 : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d % 8 = 0)
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ 2048)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base a.z n) ∧
      Rest [.t0, .t1] s s' ∧
      Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hw.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab h4
  obtain ⟨iox, ioy, ioz, iax, iay, iaz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xax, xay, xaz, xbx, xby, xbz⟩, ⟨yax, yay, yaz, ybx, yby, ybz⟩, ⟨zax, zay, zaz, zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  obtain ⟨fox, foy, foz, fax, fay, faz, fbx, fby, fbz⟩ := h4
  -- `omega` would split every disjunction of the context: give it the facts it needs.
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hw hc fox fax fbx iox iax ibx (by omega_using [xax]) (by omega_using [xbx]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n (hw.of_rest k₁) (by rw [k₁.gpr _ (by decide), hc]) foy fay fby ioy iay iby
    (by omega_using [yay]) (by omega_using [yby])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (sel_ok c n ((hw.of_rest k₁).of_rest k₂) (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc])
    foz faz fbz ioz iaz ibz (by omega_using [zaz]) (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

end VG.Proof.Weierstrass.RISCV64
