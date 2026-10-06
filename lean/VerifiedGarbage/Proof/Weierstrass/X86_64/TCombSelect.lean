import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# The comb from tables in memory on x86-64: the selection

The entry of table `j` for the magnitude `a` in `r8`, in constant time
(`selPass_ok`): the accumulators `selAcc c` cleared, then for every entry
`m = 1 … H` the mask of `a = m` in both quadwords of `xmm15` (`dup_bmask`)
keeps the entry's 16-byte pieces (`selStep_ok`), so that after entry `m`
accumulator `c` holds piece `c` of entry `a` if `1 ≤ a ≤ m`, else zero
(`accVal`, `selEntry_ok`); they are stored to `E`'s `x` and `y`, which are
adjacent. `selOne_ok` then sets `y = R` for `a = 0` and `Z = R` unless
`a = 0`.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- All ones in both quadwords if `b`, else zero. -/
abbrev bmask128 (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

/-- The mask in both quadwords: `punpcklqdq` of `movq`. -/
theorem dup_bmask (b : Bool) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ bmask b) ((0 : BitVec 64) ++ bmask b) = bmask128 b := by
  cases b <;> rfl

theorem selAcc_ne : ∀ c < 14, selAcc c ≠ .xmm14 ∧ selAcc c ≠ .xmm15 := by decide

theorem selAcc_inj : ∀ c < 14, ∀ d < 14, selAcc c = selAcc d → c = d := by decide

theorem ea_tblAt (s : State) (d : Nat) : s.ea (tblAt d) = s.gpr .rdx + BitVec.ofNat 64 d := by
  simp only [State.ea, tblAt, BitVec.ofInt_natCast]

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

/-- Piece `c` of entry `m` of the table at `rdx = X`, kept under the mask
`xmm15` in accumulator `c`. -/
theorem selStep_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 14)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 16) :
    WP isa (.block [.movdquLoad .xmm14 (tblAt d), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (selAcc c) .xmm14)]) s fun t =>
      t.xmm (selAcc c) = s.xmm (selAcc c) ||| (s.mem.readW (X + BitVec.ofNat 64 d) 128 &&& s.xmm .xmm15) ∧
      XKeep [] (fun r => r = selAcc c ∨ r = .xmm14) s t := by
  have h14 := (selAcc_ne c hc).1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_tblAt, hx, State.load128, hr,
    ite_true, Option.map_some, XOp.exec, XBinOp.eval, RegUpd.xmm_setXmm_self,
    RegUpd.xmm_setXmm_of_ne _ _ h14, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setXmm_of_ne _ _ (show XReg.xmm15 ≠ XReg.xmm14 from by decide)]
  refine ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [not_or] at hr
  rw [RegUpd.xmm_setXmm_of_ne _ _ hr.1, RegUpd.xmm_setXmm_of_ne _ _ hr.2, RegUpd.xmm_setXmm_of_ne _ _ hr.2]

/-- The pieces `c < k` of entry `m` of the table at `rdx = X` (entries `st`
bytes apart, piece `c` at `po c` bytes into its entry) kept under the mask
`xmm15` in their accumulators. -/
theorem selSteps_ok {np st m : Nat} {po : Nat → Nat} (hn : np ≤ 14) {X : Addr} :
    ∀ k ≤ np, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + po c)) 16) →
    WP isa (.block ((List.range k).flatMap fun c =>
        [.movdquLoad .xmm14 (tblAt (st * (m - 1) + po c)), .xop (.bin .pand .xmm14 .xmm15),
          .xop (.bin .por (selAcc c) .xmm14)])) s fun t =>
      (∀ c < 14, t.xmm (selAcc c) = if c < k then s.xmm (selAcc c) |||
          (s.mem.readW (X + BitVec.ofNat 64 (st * (m - 1) + po c)) 128 &&& s.xmm .xmm15)
        else s.xmm (selAcc c)) ∧
      XKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm14) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun c _ => by simp, XKeep.refl _ _ _⟩
  | k + 1, hk, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selSteps_ok hn k (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : s₁.xmm .xmm15 = s.xmm .xmm15 := k₁.xmm _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_ne c (by omega)).2 h.symm
      · exact absurd h (by decide))
    refine WP.mono (selStep_ok s₁ ((k₁.gpr _ (List.not_mem_nil)).trans hx) (c := k) (by omega)
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

/-- `xmm15` = the mask `rcx` in both quadwords. -/
theorem dupMask_ok (s : State) {b : Bool} (hc : s.gpr .rcx = bmask b) :
    WP isa (.block [.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)]) s fun t =>
      t.xmm .xmm15 = bmask128 b ∧ XKeep [] (· = .xmm15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.xmm_setXmm_self, hc,
    dup_bmask, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
    rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]⟩

/-- Accumulator `c` after the entries `1 … m` for the magnitude `a`: piece
`c` of entry `a` of the table at `X` if `1 ≤ a ≤ m`, else zero. -/
def accVal (mem : Mem) (X : Addr) (st : Nat) (po : Nat → Nat) (a m c : Nat) : BitVec 128 :=
  if 1 ≤ a ∧ a ≤ m then mem.readW (X + BitVec.ofNat 64 (st * (a - 1) + po c)) 128 else 0

theorem accVal_step (mem : Mem) (X : Addr) (st : Nat) (po : Nat → Nat) (a m c : Nat) (hm : 1 ≤ m) :
    accVal mem X st po a (m - 1) c |||
      (mem.readW (X + BitVec.ofNat 64 (st * (m - 1) + po c)) 128 &&& bmask128 (decide (a = m))) =
      accVal mem X st po a m c := by
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

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the
mask of `r8 = a`. -/
theorem selEntry_ok {st np : Nat} {po : Nat → Nat} {s : State} {X : Addr} {a m : Nat} (hn : np ≤ 14)
    (hm1 : 1 ≤ m) (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (hx : s.gpr .rdx = X)
    (hr : ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + po c)) 16)
    (hacc : ∀ c < np, s.xmm (selAcc c) = accVal s.mem X st po a (m - 1) c) :
    WP isa (.block (selEntryAt st np po m)) s fun t =>
      (∀ c < np, t.xmm (selAcc c) = accVal s.mem X st po a m c) ∧
      XKeep [.rcx] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm14 ∨ r = .xmm15) s t := by
  rw [selEntryAt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (eqMask_ok s hm ha h8) fun s₁ ⟨c₁, k₁, x₁⟩ => ?_
  refine WP.mono (dupMask_ok s₁ c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hx₂ : s₂.gpr .rdx = X := by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), hx]
  have hm₂ : s₂.mem = s.mem := k₂.mem.trans k₁.2.1
  refine WP.mono (selSteps_ok hn np (Nat.le_refl _) s₂ hx₂ (by
      rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun c hc => ?_, ?_⟩
  · rw [a₃ c (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc), x₂, hm₂,
      k₂.xmm _ (fun h => (selAcc_ne c (by omega)).2 h), x₁, hacc c hc]
    exact accVal_step _ _ _ _ _ _ _ hm1
  · refine ⟨fun r hr => ?_, k₃.mem.trans hm₂, by rw [k₃.rd, k₂.rd, k₁.2.2.1],
      by rw [k₃.wr, k₂.wr, k₁.2.2.2], fun r hr => ?_⟩
    · rw [k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁.1 r hr]
    · simp only [not_or] at hr
      rw [k₃.xmm r (by rintro (h | h); exacts [hr.1 h, hr.2.1 h]), k₂.xmm r hr.2.2, x₁]

/-- The entries `1 … h` of the table at `rdx = X` kept in the cleared
accumulators under the masks of `r8 = a`. -/
theorem selEntries_ok {st np : Nat} {po : Nat → Nat} {X : Addr} {a : Nat} (hn : np ≤ 14) (ha : a < 2 ^ 31) :
    ∀ h, h < 2 ^ 31 → ∀ (s : State), s.gpr .r8 = BitVec.ofNat 64 a → s.gpr .rdx = X →
    (∀ e < h, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * e + po c)) 16) →
    (∀ c < np, s.xmm (selAcc c) = 0) →
    WP isa (.block ((List.range h).flatMap fun m => selEntryAt st np po (m + 1))) s fun t =>
      (∀ c < np, t.xmm (selAcc c) = accVal s.mem X st po a h c) ∧
      XKeep [.rcx] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h0 => WP.block_nil ⟨fun c hc => by
      rw [h0 c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], XKeep.refl _ _ _⟩
  | h + 1, hh, s, h8, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selEntries_ok hn ha h (by omega) s h8 hx (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (selEntry_ok (X := X) (m := h + 1) hn (by omega) hh ha
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega) c hc)
      (fun c hc => by rw [a₁ c hc, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun c hc => by rw [a₂ c hc, k₁.mem], k₁.trans k₂⟩
/-- The accumulators `c < k` cleared. -/
theorem clearAcc_ok : ∀ k ≤ 14, ∀ (s : State),
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
      rw [w₁]; exact ⟨_, hs.wr, hs.contains (by omega) (by decide)⟩
    have hd₁ : s₁.gpr .rdi = base := by rw [g₁]; exact hs.rdi
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hd₁, State.store128, hw,
      ite_true, Option.some.injEq, exists_eq_left']
    have O₂ := writeW128_out s₁.mem base (s₁.xmm (selAcc k)) (d := o + 16 * k) (by omega)
    refine ⟨fun c hc => ?_, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)),
      g₁, r₁, w₁, x₁⟩
    by_cases hck : c = k
    · subst hck
      rw [x₁]; exact Mem.readW_writeW_self (n := 16) _ _ _ (by decide)
    · rw [O₂.read128 (by omega) (by omega), a₁ c (by omega)]

/-- An accumulator stored to the 16 bytes at `d`. -/
theorem store128_ok {base : Addr} {size d : Nat} (s : State) (hs : Scr s base size) (hd : d + 16 ≤ size)
    (r : XReg) :
    WP isa (.block [.movdquStore (sc d) r]) s fun t =>
      t.mem.readW (off base d) 128 = s.xmm r ∧ Outside base d 16 s.mem t.mem ∧ t.gpr = s.gpr ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm = s.xmm := by
  have hn := hs.nowrap
  have hw : InRegions s.wr (off base d) 16 := ⟨_, hs.wr, hs.contains (by omega) (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi, State.store128, hw,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨Mem.readW_writeW_self (n := 16) _ _ _ (by decide),
    writeW128_out s.mem base (s.xmm r) (by omega), trivial, trivial, trivial, trivial⟩

/-- `rdx` = the address of table `rbx = j`, `T + j · tblBytes`, through `rax`
and `rcx`. -/
theorem selSetup_ok (K : TCombCfg) (s : State) {j : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j)
    (hT : s.syms K.tsym = T) (htb : K.tblBytes < 2 ^ 31) :
    WP isa (.block K.selSetup) s fun t => t.gpr .rdx = T + BitVec.ofNat 64 (j * K.tblBytes) ∧
      Keeps [.rax, .rcx, .rdx] s t ∧ t.xmm = s.xmm ∧ t.syms = s.syms := by
  subst hT
  apply WP.of_runBlock
  simp only [TCombCfg.selSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, execMul, State.setReg32, imm32_eq htb, hb, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show K.tblBytes < 2 ^ 64 by omega), Nat.mod_mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- The accumulators `c < np` cleared, then entries `1 … H` of the table at
`rdx = X` kept under the masks of `r8 = a`. -/
theorem selLoad_ok {st np H : Nat} {po : Nat → Nat} {s : State} {X : Addr} {a : Nat} (hn : np ≤ 14)
    (hH : H < 2 ^ 31) (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ e < H, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * e + po c)) 16) :
    WP isa (.block ((List.range np).map (fun c => .xop (.bin .pxor (selAcc c) (selAcc c))) ++
      (List.range H).flatMap (fun m => selEntryAt st np po (m + 1)))) s fun t =>
      (∀ c < np, t.xmm (selAcc c) = accVal s.mem X st po a H c) ∧ KeepRegs [.rcx] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (clearAcc_ok np hn s) fun s₁ ⟨a₁, k₁⟩ => ?_
  refine WP.mono (selEntries_ok (X := X) hn ha H hH s₁ (by rw [k₁.gpr _ List.not_mem_nil, h8])
    (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.rd, k₁.wr]; exact hr) a₁) fun s₂ ⟨a₂, k₂⟩ =>
    ⟨fun c hc => by rw [a₂ c hc, k₁.mem], ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r List.not_mem_nil],
      by rw [k₂.rd, k₁.rd], by rw [k₂.wr, k₁.wr]⟩, by rw [k₂.mem, k₁.mem]⟩

/-- The accumulators cleared, entries `1 … H` of the table at `rdx = X` kept
under the masks of `r8 = a`, and stored to the `16 n` bytes at `E.x`. -/
theorem selPass_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {X : Addr} {a : Nat} (hn : K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16)
    (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block K.selPass) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 = accVal s.mem X (16 * K.M.n) (16 * ·) a K.H c) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [.rcx] s t := by
  unfold TCombCfg.selPass selPassAt
  rw [WP.block_append_iff]
  refine WP.mono (selLoad_ok (st := 16 * K.M.n) (po := (16 * ·)) hn hH ha h8 hx hr) fun s₂ ⟨a₂, k₂, m₂⟩ => ?_
  have hs₂ : Scr s₂ base size := hs.of_keepRegs k₂ (by decide)
  refine WP.mono (storeAcc_ok (o := K.E.x) K.M.n s₂ hs₂ hE) fun t ⟨a₃, O₃, g₃, r₃, w₃, _⟩ =>
    ⟨fun c hc => by rw [a₃ c hc, a₂ c hc], by rw [m₂] at O₃; exact O₃,
      ⟨fun r hr => by rw [g₃, k₂.gpr r hr], by rw [r₃, k₂.rd], by rw [w₃, k₂.wr]⟩⟩

/-- The words the selection stores: those of entry `a` of the table at `X`
if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word {mem mem' : Mem} {base X : Addr} {n a H o : Nat}
    (h : ∀ c < n, mem'.readW (off base (o + 16 * c)) 128 = accVal mem X (16 * n) (16 * ·) a H c) :
    ∀ i < 2 * n, word mem' base (o + 8 * i) =
      if 1 ≤ a ∧ a ≤ H then word mem X (16 * n * (a - 1) + 8 * i) else 0 := by
  intro i hi
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 2 ∧ i = 2 * c + q := ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  have e := readW_extract mem' (off base (o + 16 * c)) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add, show o + 16 * c + 8 * q = o + 8 * (2 * c + q) by omega] at e
  rw [Mont.word, off, ← e, h c (by omega), accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (16 * n * (a - 1) + 16 * c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
    rw [show 16 * n * (a - 1) + 16 * c + 8 * q = 16 * n * (a - 1) + 8 * (2 * c + q) by omega]
  · simp

/-- Word `q < 2` of a stored accumulator: that of its piece of entry `a` of
the table at `X` if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word1 {mem mem' : Mem} {base X : Addr} {st : Nat} {po : Nat → Nat} {a H c o q : Nat}
    (h : mem'.readW (off base o) 128 = accVal mem X st po a H c) (hq : q < 2) :
    word mem' base (o + 8 * q) = if 1 ≤ a ∧ a ≤ H then word mem X (st * (a - 1) + po c + 8 * q) else 0 := by
  have e := readW_extract mem' (off base o) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add] at e
  rw [Mont.word, off, ← e, h, accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (st * (a - 1) + po c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
  · simp

/-- `rcx` all ones if `r8 = a` is zero, else zero. -/
theorem isZero_ok (s : State) {a : Nat} (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rcx = bmask (decide (a = 0)) ∧ Keeps [.rcx] s t ∧ t.xmm = s.xmm := by
  crun [h8, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
    have hx : decide ((BitVec.ofNat 64 a).toNat < 1) = decide (a = 0) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact decide_eq_decide.mpr (by omega)
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = 0) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[y + 8 i] |= wordOf v i & rcx` for `i < k`, through `rax`. -/
theorem orSteps_ok {base : Addr} {size v y : Nat} {M : BitVec 64} : ∀ k, ∀ (s : State), Scr s base size →
    s.gpr .rcx = M → y + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap fun i => [.movImm64 .rax (wordOf v i), .alu .and .rax (.reg .rcx),
        .alu .or .rax (.mem (sc (y + 8 * i))), .store (sc (y + 8 * i)) .rax])) s fun t =>
      (∀ i < k, word t.mem base (y + 8 * i) = (wordOf v i &&& M) ||| word s.mem base (y + 8 * i)) ∧
      KeepRegs [.rax] s t ∧ Outside base y (8 * k) s.mem t.mem ∧ t.xmm = s.xmm
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _, rfl⟩
  | k + 1, s, hs, hc, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (orSteps_ok k s hs hc (by omega)) fun s₁ ⟨e₁, k₁, O₁, x₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hc₁ : s₁.gpr .rcx = M := by rw [k₁.gpr _ (by decide), hc]
    refine WP.mono (show WP isa (.block [.movImm64 .rax (wordOf v k), .alu .and .rax (.reg .rcx),
        .alu .or .rax (.mem (sc (y + 8 * k))), .store (sc (y + 8 * k)) .rax]) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (y + 8 * k)) ((wordOf v k &&& M) ||| word s₁.mem base (y + 8 * k)) ∧
          KeepRegs [.rax] s₁ s₂ ∧ s₂.xmm = s₁.xmm) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
        State.store64, ea_sc, hc₁, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg,
        RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
        RegUpd.mem_arithFlags, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs₁.rdi, ld_sc hs₁ (d := y + 8 * k) (by omega), st_sc hs₁ (d := y + 8 * k) (by omega),
        Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
    have O₂ : Outside base (y + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), x₂.trans x₁⟩
    rcases Nat.lt_or_ge i k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, word_writeW_self, O₁.word (by omega) (by omega)]

/-- `[z + 8 i] = wordOf v i & rcx` for `i < k`, through `rax`. -/
theorem andSteps_ok {base : Addr} {size v z : Nat} {M : BitVec 64} : ∀ k, ∀ (s : State), Scr s base size →
    s.gpr .rcx = M → z + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap fun i => [.movImm64 .rax (wordOf v i), .alu .and .rax (.reg .rcx),
        .store (sc (z + 8 * i)) .rax])) s fun t =>
      (∀ i < k, word t.mem base (z + 8 * i) = wordOf v i &&& M) ∧
      KeepRegs [.rax] s t ∧ Outside base z (8 * k) s.mem t.mem ∧ t.xmm = s.xmm
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _, rfl⟩
  | k + 1, s, hs, hc, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (andSteps_ok k s hs hc (by omega)) fun s₁ ⟨e₁, k₁, O₁, x₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hc₁ : s₁.gpr .rcx = M := by rw [k₁.gpr _ (by decide), hc]
    refine WP.mono (show WP isa (.block [.movImm64 .rax (wordOf v k), .alu .and .rax (.reg .rcx),
        .store (sc (z + 8 * k)) .rax]) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (z + 8 * k)) (wordOf v k &&& M) ∧
          KeepRegs [.rax] s₁ s₂ ∧ s₂.xmm = s₁.xmm) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.store64, ea_sc,
        hc₁, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, reduceCtorEq, ite_true, ite_false, hs₁.rdi,
        st_sc hs₁ (d := z + 8 * k) (by omega), Option.bind_some, Option.some.injEq,
        exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
    have O₂ : Outside base (z + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), x₂.trans x₁⟩
    rcases Nat.lt_or_ge i k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, word_writeW_self]

/-- `rcx = ~rcx`. -/
theorem notMask_ok (s : State) {b : Bool} (hc : s.gpr .rcx = bmask b) :
    WP isa (.block [.alu .xor .rcx (.imm (-1))]) s fun t =>
      t.gpr .rcx = bmask (!b) ∧ Keeps [.rcx] s t ∧ t.xmm = s.xmm := by
  crun [hc, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨by cases b <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `y |= R` if the magnitude `r8 = a` is zero, and `Z = R` unless it is, word
by word, through `rax` and `rcx`. -/
theorem selOne_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hy : K.E.y + 8 * K.M.n ≤ size)
    (hz : K.E.z + 8 * K.M.n ≤ size) (hyz : K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y) :
    WP isa (.block K.selOne) s fun t =>
      (∀ i < K.M.n, word t.mem base (K.E.y + 8 * i) =
        (wordOf K.one i &&& bmask (decide (a = 0))) ||| word s.mem base (K.E.y + 8 * i)) ∧
      (∀ i < K.M.n, word t.mem base (K.E.z + 8 * i) = wordOf K.one i &&& bmask (!decide (a = 0))) ∧
      KeepRegs [.rax, .rcx] s t ∧ Unch base [(K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem ∧
      t.xmm = s.xmm := by
  have hn := hs.nowrap
  unfold TCombCfg.selOne
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (isZero_ok s ha h8) fun s₁ ⟨c₁, k₁, x₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (orSteps_ok K.M.n s₁ hs₁ c₁ hy) fun s₂ ⟨e₂, k₂, O₂, x₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (notMask_ok s₂ (b := decide (a = 0)) (by rw [k₂.gpr _ (by decide), c₁]))
    fun s₃ ⟨c₃, k₃, x₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (andSteps_ok K.M.n s₃ hs₃ c₃ hz) fun t ⟨e₄, k₄, O₄, x₄⟩ =>
    ⟨fun i hi => ?_, e₄, ?_, ?_, by rw [x₄, x₃, x₂, x₁]⟩
  · rw [O₄.word (by omega) (by omega), k₃.2.1, e₂ i hi, k₁.2.1]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans
      (((Keeps.regs k₃).mono (by decide)).trans (k₄.mono (by decide))))
  · have U := ((O₂.unch.trans (show Unch base [] s₂.mem s₃.mem by rw [k₃.2.1]; exact Unch.refl _ _ _)).trans
      O₄.unch)
    rw [k₁.2.1] at U
    exact U.mono fun w hw => by simp only [List.append_nil, List.mem_append] at hw; simp only [List.mem_cons,
      List.not_mem_nil, or_false]; rcases hw with hw | hw <;> simp only [List.mem_singleton] at hw <;>
      simp [hw]

/-- Numbers with the same words. -/
theorem wordsVal_congr₂ {m m' : Mem} {b b' : Addr} : ∀ (o o' k : Nat),
    (∀ i < k, word m' b' (o' + 8 * i) = word m b (o + 8 * i)) → wordsVal m' b' o' k = wordsVal m b o k
  | _, _, 0, _ => rfl
  | o, o', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_congr₂ (o + 8) (o' + 8) k fun i hi => by
      rw [show o + 8 + 8 * i = o + 8 * (i + 1) by omega, show o' + 8 + 8 * i = o' + 8 * (i + 1) by omega]
      exact h (i + 1) (by omega)]

theorem Unch.split {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 2 * k)] m m') :
    Unch base [(o, k), (o + k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  dsimp only at h1 h2 ⊢; omega

/-- What the selection leaves: in `E`, entry `a`'s `x` and `y` (of the table
at `X`) and `R` if `a ≥ 1`, else `(0, R, 0)`. -/
structure SelPost (K : TCombCfg) (base : Addr) (s : State) (a : Nat) (X : Addr) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1)) K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then K.one else 0
  keep : KeepRegs [.rax, .rcx, .rdx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

theorem bv_and_or_true (x y : BitVec 64) : (x &&& bmask true) ||| y = x ||| y := by
  rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
theorem bv_and_or_false (x y : BitVec 64) : (x &&& bmask false) ||| y = y := by
  rw [show bmask false = 0 from rfl]; simp
theorem bv_and_true (x : BitVec 64) : x &&& bmask true = x := by
  rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
theorem bv_or_zero (x : BitVec 64) : x ||| 0 = x := by simp
theorem bv_and_false (x : BitVec 64) : x &&& bmask false = 0 := by
  rw [show bmask false = 0 from rfl]; simp

/-- The words of `v < 2^(64 k)`, word by word, are `v`. -/
theorem wordsVal_wordOf {m : Mem} {b : Addr} {o k v : Nat} (hv : v < 2 ^ (64 * k))
    (h : ∀ i < k, word m b (o + 8 * i) = wordOf v i) : wordsVal m b o k = v :=
  wordsVal_of_shifts m b o k v hv h

/-- Zero words. -/
theorem wordsVal_zeros {m : Mem} {b : Addr} {o k : Nat} (h : ∀ i < k, word m b (o + 8 * i) = 0) :
    wordsVal m b o k = 0 :=
  wordsVal_of_shifts m b o k 0 (Nat.two_pow_pos _) fun i hi => by rw [h i hi, Nat.zero_shiftRight]; rfl

/-- The entry of table `rbx = j` for the magnitude `r8 = a ≤ H` into `E`:
selected from the table at `T + j · tblBytes`, the static `tsym`'s address
plus `j` tables. -/
theorem select_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 31)
    (hexy : K.E.y = K.E.x + 8 * K.M.n) (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    {j a : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (ha : a ≤ K.H) (hT : s.syms K.tsym = T)
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) K.tblBytes) :
    WP isa (.block K.select) s (SelPost K base s a (T + BitVec.ofNat 64 (j * K.tblBytes))) := by
  have hnw := hs.nowrap
  have htbe : K.tblBytes = 16 * K.M.n * K.H := rfl
  rw [TCombCfg.select, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (selSetup_ok K s hb hT htb) fun s₁ ⟨x₁, k₁, _, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16 := by
    intro e he c hc
    rw [k₁.2.2.1, k₁.2.2.2]
    refine VG.CallLay.inRegions_sub hreg ?_ (by omega)
    have := Nat.mul_le_mul_left (16 * K.M.n) (show e + 1 ≤ K.H by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (selPass_ok K hs₁ hn.2 hH (by omega) h8₁ x₁ hr (by omega)) fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [k₂.gpr _ (by decide), h8₁]
  refine WP.mono (selOne_ok K hs₂ (by omega) h8₂ hy hz (by omega)) fun t ⟨ey, ez, k₃, U₃, _⟩ => ?_
  have W := accVal_word a₂
  rw [k₁.2.1] at W
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    U₃.word (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · have hyw : ∀ i < K.M.n, word s₂.mem base (K.E.y + 8 * i) =
        if 1 ≤ a ∧ a ≤ K.H then word s.mem (T + BitVec.ofNat 64 (j * K.tblBytes))
          (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else 0 := fun i hi => by
      rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega, W _ (by omega),
        show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) = 16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩),
          decide_eq_false (show ¬ a = 0 by omega), bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          decide_eq_true (show a = 0 by omega), bv_and_or_true, bv_or_zero]
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ez i hi, decide_eq_false (show ¬ a = 0 by omega), Bool.not_false, bv_and_true]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [ez i hi, decide_eq_true (show a = 0 by omega), Bool.not_true, bv_and_false]
  · exact ((Keeps.regs k₁).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))
  · have U₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.x + 8 * K.M.n, 8 * K.M.n)] s.mem s₂.mem := by
      rw [← k₁.2.1]
      exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega]; exact O₂.unch)
    rw [← hexy] at U₂
    exact (U₂.trans U₃).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.X86_64
