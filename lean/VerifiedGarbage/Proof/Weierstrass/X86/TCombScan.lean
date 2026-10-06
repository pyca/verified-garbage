import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Weierstrass.X86.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# The comb from tables in memory on x86 (32-bit): the selection

The entry of table `j` for the magnitude `a` in `ebx`, in constant time
(`selPass_ok`): the accumulators `selAcc c` cleared, then for every entry
`m = 1 … H` the mask of `a = m` in both quadwords of `xmm7` (`dup_bmask`)
keeps the entry's 16-byte pieces (`selStep_ok`), so that after entry `m`
accumulator `c` holds piece `c` of entry `a` if `1 ≤ a ≤ m`, else zero
(`accVal`, `selEntry_ok`); they are stored to `E`'s `x` and `y`, which are
adjacent. `selOne_ok` then sets `y = R` for `a = 0` and `Z = R` unless
`a = 0`.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- All ones in both quadwords if `b`, else zero. -/
abbrev bmask128 (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

/-- The mask in both quadwords: `punpcklqdq` of `movq`. -/
theorem dup_bmask (b : Bool) :
    shufDwords ((0 : BitVec 96) ++ bmask b) 0 = bmask128 b := by
  cases b <;> rfl

theorem selAcc_ne : ∀ c < 6, selAcc c ≠ .xmm6 ∧ selAcc c ≠ .xmm7 := by decide

theorem selAcc_inj : ∀ c < 6, ∀ d < 6, selAcc c = selAcc d → c = d := by decide

theorem ea_tblAt {s : State} {X : Addr} (hx : (s.gpr .edx).setWidth 64 = X) {d : Nat}
    (hd : X.toNat + d < 2 ^ 32) : s.ea (TCombCfg.tblAt d) = X + BitVec.ofNat 64 d := by
  change addr (s.gpr .edx) d = _
  have hnat : (s.gpr .edx).toNat = X.toNat := by
    rw [← hx, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (s.gpr .edx).isLt; omega)]
  rw [addr_eq (by omega), hx]

abbrev KeepRegs := VG.Proof.Mont.X86.Keeps

theorem _root_.VG.Proof.Mont.X86.Keeps.gpr {rs : List Reg} {s t : State} (h : KeepRegs rs s t)
    (r : Reg) (hr : r ∉ rs) : t.gpr r = s.gpr r := h.1 r hr

theorem _root_.VG.Proof.Mont.X86.Scr.of_keepRegs {rs : List Reg} {s t : State} {base : Addr} {size : Nat}
    (h : Scr s base size) (k : KeepRegs rs s t) (hr : .edi ∉ rs) : Scr t base size := h.of_keeps k hr

theorem _root_.VG.Proof.Mont.X86.Keeps.rd {rs : List Reg} {s t : State} (h : KeepRegs rs s t) : t.rd = s.rd := h.2.1

theorem _root_.VG.Proof.Mont.X86.Keeps.wr {rs : List Reg} {s t : State} (h : KeepRegs rs s t) : t.wr = s.wr := h.2.2

theorem CKeeps.regs {rs : List Reg} {s t : State} (h : CKeeps rs s t) : KeepRegs rs s t := h.keeps

/-- What the selection leaves of the other registers: the general-purpose
registers but `rs`, the memory and the regions, and the `xmm` registers but
those of `xs`. -/
structure XKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : ∀ r, ¬ xs r → t.xmm r = s.xmm r

theorem XKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : XKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : XKeep rs xs s₁ s₂)
    (h₂ : XKeep rs xs s₂ s₃) : XKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr => (h₂.xmm r hr).trans (h₁.xmm r hr)⟩

theorem XKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : XKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : XKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr, fun r h' => h.xmm r fun h'' => h' (hx r h'')⟩

/-- Piece `c` of entry `m` of the table at `edx = X`, kept under the mask
`xmm7` in accumulator `c`. -/
theorem selStep_ok (s : State) {X : Addr} (hx : (s.gpr .edx).setWidth 64 = X) {d c : Nat} (hc : c < 6)
    (hX : X.toNat + d + 16 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 16) :
    WP isa (.block [.movdquLoad .xmm6 (TCombCfg.tblAt d), .xop (.bin .pand .xmm6 .xmm7),
        .xop (.bin .por (selAcc c) .xmm6)]) s fun t =>
      t.xmm (selAcc c) = s.xmm (selAcc c) ||| (s.mem.readW (X + BitVec.ofNat 64 d) 128 &&& s.xmm .xmm7) ∧
      XKeep [] (fun r => r = selAcc c ∨ r = .xmm6) s t := by
  have h14 := (selAcc_ne c hc).1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_tblAt hx (d := d) (by omega), State.load128, hr,
    ite_true, Option.map_some, XOp.exec, XBinOp.eval, RegUpd.xmm_setXmm_self,
    RegUpd.xmm_setXmm_of_ne _ _ h14, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setXmm_of_ne _ _ (show XReg.xmm7 ≠ XReg.xmm6 from by decide)]
  refine ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [not_or] at hr
  rw [RegUpd.xmm_setXmm_of_ne _ _ hr.1, RegUpd.xmm_setXmm_of_ne _ _ hr.2, RegUpd.xmm_setXmm_of_ne _ _ hr.2]

/-- The pieces `c < k` of entry `m` of the table at `edx = X` kept under the
mask `xmm7` in their accumulators. -/
theorem selSteps_ok {n m : Nat} (hn : n ≤ 6) {X : Addr} (hX : X.toNat + 16 * n * (m - 1) + 16 * n ≤ 2 ^ 32) : ∀ k ≤ n, ∀ (s : State), (s.gpr .edx).setWidth 64 = X →
    (∀ c < n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * n * (m - 1) + 16 * c)) 16) →
    WP isa (.block ((List.range k).flatMap fun c =>
        [.movdquLoad .xmm6 (TCombCfg.tblAt (16 * n * (m - 1) + 16 * c)), .xop (.bin .pand .xmm6 .xmm7),
          .xop (.bin .por (selAcc c) .xmm6)])) s fun t =>
      (∀ c < 6, t.xmm (selAcc c) = if c < k then s.xmm (selAcc c) |||
          (s.mem.readW (X + BitVec.ofNat 64 (16 * n * (m - 1) + 16 * c)) 128 &&& s.xmm .xmm7)
        else s.xmm (selAcc c)) ∧
      XKeep [] (fun r => (∃ c < n, r = selAcc c) ∨ r = .xmm6) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun c _ => by simp, XKeep.refl _ _ _⟩
  | k + 1, hk, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selSteps_ok hn hX k (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : s₁.xmm .xmm7 = s.xmm .xmm7 := k₁.xmm _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_ne c (by omega)).2 h.symm
      · exact absurd h (by decide))
    refine WP.mono (selStep_ok s₁ (X := X) (by rw [k₁.gpr _ List.not_mem_nil]; exact hx) (c := k) (by omega)
      (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega))) fun t ⟨a₂, k₂⟩ => ⟨fun c hc => ?_, ?_⟩
    · by_cases hck : c = k
      · subst hck
        rw [a₂, a₁ c hc, h15, k₁.mem]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · rw [k₂.xmm _ (by
          rintro (h | h)
          · exact hck (selAcc_inj c hc k (by omega) h)
          · exact (selAcc_ne c hc).1 h), a₁ c hc]
        by_cases hlt : c < k
        · simp only [hlt, show c < k + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < k + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl ⟨k, by omega, h⟩
        · exact Or.inr h)

/-- `xmm7` = the mask `ecx` in both quadwords. -/
theorem dupMask_ok (s : State) {b : Bool} (hc : s.gpr .ecx = bmask b) :
    WP isa (.block [.xop (.movd .xmm7 .ecx), .xop (.pshufd .xmm7 .xmm7 0)]) s fun t =>
      t.xmm .xmm7 = bmask128 b ∧ XKeep [] (· = .xmm7) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.xmm_setXmm_self, hc,
    dup_bmask, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
    rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]⟩

/-- Accumulator `c` after the entries `1 … m` for the magnitude `a`: piece
`c` of entry `a` of the table at `X` if `1 ≤ a ≤ m`, else zero. -/
def accVal (mem : Mem) (X : Addr) (n a m c : Nat) : BitVec 128 :=
  if 1 ≤ a ∧ a ≤ m then mem.readW (X + BitVec.ofNat 64 (16 * n * (a - 1) + 16 * c)) 128 else 0

theorem accVal_step (mem : Mem) (X : Addr) (n a m c : Nat) (hm : 1 ≤ m) :
    accVal mem X n a (m - 1) c |||
      (mem.readW (X + BitVec.ofNat 64 (16 * n * (m - 1) + 16 * c)) 128 &&& bmask128 (decide (a = m))) =
      accVal mem X n a m c := by
  unfold accVal
  by_cases h : a = m
  · subst h
    rw [decide_eq_true rfl, show bmask128 true = BitVec.allOnes 128 from rfl, BitVec.and_allOnes,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hm, Nat.le_refl _⟩)]
    simp
  · rw [decide_eq_false h, show bmask128 false = 0 from rfl]
    have e : ∀ x y : BitVec 128, x ||| (y &&& 0) = x := fun x y => by simp
    rw [e]
    by_cases h' : 1 ≤ a ∧ a ≤ m - 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- Entry `m` of the table at `edx = X` kept in the accumulators under the
mask of `ebx = a`. -/
theorem selEntry_ok (K : TCombCfg) {s : State} {X : Addr} {a m : Nat} (hn : K.M.n ≤ 6) (hm1 : 1 ≤ m)
    (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (h8 : s.gpr .ebx = BitVec.ofNat 32 a) (hx : (s.gpr .edx).setWidth 64 = X)
    (hr : ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.M.n * (m - 1) + 16 * c)) 16)
    (hX : X.toNat + 16 * K.M.n * (m - 1) + 16 * K.M.n ≤ 2 ^ 32)
    (hacc : ∀ c < K.M.n, s.xmm (selAcc c) = accVal s.mem X K.M.n a (m - 1) c) :
    WP isa (.block (K.selEntry m)) s fun t =>
      (∀ c < K.M.n, t.xmm (selAcc c) = accVal s.mem X K.M.n a m c) ∧
      XKeep [.ecx] (fun r => (∃ c < K.M.n, r = selAcc c) ∨ r = .xmm6 ∨ r = .xmm7) s t := by
  rw [TCombCfg.selEntry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (eqMask_ok s hm ha h8) fun s₁ ⟨c₁, k₁, x₁⟩ => ?_
  refine WP.mono (dupMask_ok s₁ c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hx₂ : (s₂.gpr .edx).setWidth 64 = X := by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), hx]
  have hm₂ : s₂.mem = s.mem := k₂.mem.trans k₁.2.1
  refine WP.mono (selSteps_ok hn hX K.M.n (Nat.le_refl _) s₂ hx₂ (by
      rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun c hc => ?_, ?_⟩
  · rw [a₃ c (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc), x₂, hm₂,
      k₂.xmm _ (fun h => (selAcc_ne c (by omega)).2 h), x₁, hacc c hc]
    exact accVal_step _ _ _ _ _ _ hm1
  · refine ⟨fun r hr => ?_, k₃.mem.trans hm₂, by rw [k₃.rd, k₂.rd, k₁.2.2.1],
      by rw [k₃.wr, k₂.wr, k₁.2.2.2], fun r hr => ?_⟩
    · rw [k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁.1 r hr]
    · simp only [not_or] at hr
      rw [k₃.xmm r (by rintro (h | h); exacts [hr.1 h, hr.2.1 h]), k₂.xmm r hr.2.2, x₁]

/-- The entries `1 … h` of the table at `edx = X` kept in the cleared
accumulators under the masks of `ebx = a`. -/
theorem selEntries_ok (K : TCombCfg) {X : Addr} {a : Nat} (hn : K.M.n ≤ 6) (ha : a < 2 ^ 31) :
    ∀ h, h < 2 ^ 31 → ∀ (s : State), s.gpr .ebx = BitVec.ofNat 32 a → (s.gpr .edx).setWidth 64 = X →
    (∀ e < h, ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16) →
    X.toNat + 16 * K.M.n * h ≤ 2 ^ 32 →
    (∀ c < K.M.n, s.xmm (selAcc c) = 0) →
    WP isa (.block ((List.range h).flatMap fun m => K.selEntry (m + 1))) s fun t =>
      (∀ c < K.M.n, t.xmm (selAcc c) = accVal s.mem X K.M.n a h c) ∧
      XKeep [.ecx] (fun r => (∃ c < K.M.n, r = selAcc c) ∨ r = .xmm6 ∨ r = .xmm7) s t
  | 0, _, s, _, _, _, _, h0 => WP.block_nil ⟨fun c hc => by
      rw [h0 c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], XKeep.refl _ _ _⟩
  | h + 1, hh, s, h8, hx, hr, hX, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    have hX' := hX
    rw [Nat.mul_add, Nat.mul_one] at hX'
    refine WP.mono (selEntries_ok K hn ha h (by omega) s h8 hx (fun e he => hr e (by omega)) (by omega) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (selEntry_ok K (X := X) (m := h + 1) hn (by omega) hh ha
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega) c hc)
      (by simpa only [Nat.add_sub_cancel, Nat.add_assoc] using hX')
      (fun c hc => by rw [a₁ c hc, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun c hc => by rw [a₂ c hc, k₁.mem], k₁.trans k₂⟩

/-- The accumulators `c < k` cleared. -/
theorem clearAcc_ok : ∀ k ≤ 6, ∀ (s : State),
    WP isa (.block ((List.range k).map fun c => .xop (.bin .pxor (selAcc c) (selAcc c)))) s fun t =>
      (∀ c < k, t.xmm (selAcc c) = 0) ∧ XKeep [] (fun r => ∃ c < k, r = selAcc c) s t
  | 0, _, s => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), XKeep.refl _ _ _⟩
  | k + 1, hk, s => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (clearAcc_ok k (by omega) s) fun s₁ ⟨a₁, k₁⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, XBinOp.eval, BitVec.xor_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun c hc => ?_, ⟨fun r hr => k₁.gpr r hr, k₁.mem, k₁.rd, k₁.wr, fun r hr => ?_⟩⟩
    · by_cases hck : c = k
      · subst hck; exact RegUpd.xmm_setXmm_self _ _ _
      · rw [RegUpd.xmm_setXmm_of_ne _ _ fun h => hck (selAcc_inj c (by omega) k (by omega) h), a₁ c (by omega)]
    · rw [RegUpd.xmm_setXmm_of_ne _ _ fun h => hr ⟨k, by omega, h⟩, k₁.xmm r fun ⟨c, hc, h⟩ => hr ⟨c, by omega, h⟩]

/-- The accumulators `c < k` stored to the 16 bytes at `o + 16 c`. -/
theorem storeAcc_ok {base : Addr} {size o : Nat} : ∀ k, ∀ (s : State), Scr s base size → o + 16 * k ≤ size →
    WP isa (.block ((List.range k).map fun c => .movdquStore (sc (o + 16 * c)) (selAcc c))) s fun t =>
      (∀ c < k, t.mem.readW (off base (o + 16 * c)) 128 = s.xmm (selAcc c)) ∧
      Outside base o (16 * k) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm = s.xmm
  | 0, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl,
      rfl, rfl⟩
  | k + 1, s, hs, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (storeAcc_ok k s hs (by omega)) fun s₁ ⟨a₁, O₁, g₁, r₁, w₁, x₁⟩ => ?_
    have hw : InRegions s₁.wr (off base (o + 16 * k)) 16 := by
      rw [w₁]; exact ⟨_, hs.wr, Scr.contains hs.nowrap (by omega)⟩
    have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.edi, w₁ ▸ hs.wr, hs.nowrap⟩
    have hea : s₁.ea (sc (o + 16 * k)) = off base (o + 16 * k) := hs₁.ea (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.store128, hw,
      ite_true, Option.some.injEq, exists_eq_left']
    have O₂ := writeW128_out s₁.mem base (s₁.xmm (selAcc k)) (d := o + 16 * k) (by omega)
    refine ⟨fun c hc => ?_, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)),
      g₁, r₁, w₁, x₁⟩
    by_cases hck : c = k
    · subst hck
      rw [x₁]; exact Mem.readW_writeW_self (n := 16) _ _ _ (by decide)
    · rw [O₂.read128 (by omega) (by omega), a₁ c (by omega)]

/-- The accumulators cleared, entries `1 … H` of the table at `edx = X` kept
under the masks of `ebx = a`, and stored to the `16 n` bytes at `E.x`. -/
theorem selPass_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {X : Addr} {a : Nat} (hn : K.M.n ≤ 6) (hH : K.H < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .ebx = BitVec.ofNat 32 a) (hx : (s.gpr .edx).setWidth 64 = X)
    (hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16)
    (hX : X.toNat + 16 * K.M.n * K.H ≤ 2 ^ 32)
    (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block K.selPass) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 = accVal s.mem X K.M.n a K.H c) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [.ecx] s t := by
  unfold TCombCfg.selPass
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearAcc_ok K.M.n hn s) fun s₁ ⟨a₁, k₁⟩ => ?_
  refine WP.mono (selEntries_ok K (X := X) hn ha K.H hH s₁ (by rw [k₁.gpr _ List.not_mem_nil, h8])
    (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.rd, k₁.wr]; exact hr) hX a₁) fun s₂ ⟨a₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base size :=
    ⟨by rw [k₂.gpr _ (by decide), k₁.gpr _ List.not_mem_nil, hs.edi], by rw [k₂.wr, k₁.wr]; exact hs.wr,
      hs.nowrap⟩
  refine WP.mono (storeAcc_ok (o := K.E.x) K.M.n s₂ hs₂ hE) fun t ⟨a₃, O₃, g₃, r₃, w₃, _⟩ =>
    ⟨fun c hc => by rw [a₃ c hc, a₂ c hc, k₁.mem], by rw [k₂.mem, k₁.mem] at O₃; exact O₃,
      ⟨fun r hr => by rw [g₃, k₂.gpr r hr, k₁.gpr r List.not_mem_nil], by rw [r₃, k₂.rd, k₁.rd],
        by rw [w₃, k₂.wr, k₁.wr]⟩⟩

end VG.Proof.Weierstrass.X86
