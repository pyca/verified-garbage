module

public import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Check
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.RootTable
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-224's square root on RISC-V: the table's lookups and the digits

The pieces of `Impl/EcKey/Compressed/P224/RISCV64.lean` between `t` and the
root, which compute `root224` (`Impl/EcKey/Compressed/RootTable.lean`)
exactly, for any `rhs`:

* the table (`TabOk`): its words (`sqrtWords_getD`), an entry copied to a
  slot (`entCopy_ok`), the entry of a digit read from `s4` or `s5`
  (`lookup_ok`), and the products `y Π_i T (o + i) dᵢ` (`muls_ok`, `tacc`);
* the comparisons of `y` with the last row (`cmps_ok`, `digAcc`) and a digit
  (`digit_ok`): the digits found, `kA j`, in `s4` and `s5` (`DSt`).
-/

-- separate module: its proofs cost more than its imports, and changes to the rest of the function's proof need not re-check them

@[expose] public section

namespace VG.Proof.EcKey.Compressed.RISCV64.P224

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P224
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe)
open VG.Impl.EcKey.Compressed (tacc digAcc kGo tbl224 q224 root224)
open VG.Proof.Ecdh.RISCV64.P224 (sl_eq sv_unch)

/-! ## The table -/

/-- An entry in Montgomery's form. -/
abbrev montT (m d : Nat) : Nat := Cfg.mont p224 (tbl224 m d).val

theorem montT_lt (m d : Nat) : montT m d < W.p := Nat.mod_lt _ (show 0 < Spec.P224.curve.p by decide)

theorem toM_montT (m d : Nat) : toM W.p (2 ^ 256) (montT m d) = tbl224 m d := by
  show toM W.p (2 ^ 256) ((tbl224 m d).val * 2 ^ 256 % W.p) = _
  rw [toM_mont (show UnitMod W.p (2 ^ 256) from unit)]
  exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt (tbl224 m d).isLt])

/-- Word `w` of entry `16 m + d`. -/
theorem sqrtWords_getD {m d w : Nat} (hm : m < 24) (hd : d < 16) (hw : w < 4) :
    sqrtWords.getD (64 * m + 4 * d + w) 0 = wordOf (montT m d) w := by
  unfold sqrtWords
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some]
  rw [show (64 * m + 4 * d + w) / 64 = m by omega, show (64 * m + 4 * d + w) / 4 % 16 = d by omega,
    show (64 * m + 4 * d + w) % 4 = w by omega]

theorem sqrtWords_length : sqrtWords.length = 1536 := by
  unfold sqrtWords; rw [List.length_map, List.length_range]

/-- What the code needs of the table at `T`, for the working space at `base`. -/
structure TabOk (base T : Addr) (s : State) : Prop where
  held : ∀ i < 1536, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = sqrtWords.getD i 0
  al : T.toNat % 64 = 0
  rd : (⟨T, 12288⟩ : Region) ∈ s.rd
  fit : T.toNat + 12288 ≤ 2 ^ 64
  far : ∀ d < 12288, 8192 ≤ ofs base (T + BitVec.ofNat 64 d)

/-- Memory changed only in the working space keeps the table. -/
theorem TabOk.of_mem {s s' : State} {base T : Addr} (h : TabOk base T s) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabOk base T s' where
  held i hi := by
    rw [← h.held i hi]
    refine Mem.readW_congr fun b hb => hm _ ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact h.far _ (by omega)
  al := h.al
  rd := hrd ▸ h.rd
  fit := h.fit
  far := h.far

theorem TabOk.of_unch {s s' : State} {base T : Addr} (h : TabOk base T s) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) :
    TabOk base T s' :=
  h.of_mem hrd fun _ hx => hu.far fun w hw => by have := hW w hw; omega

theorem TabOk.of_outside {s s' : State} {base T : Addr} (h : TabOk base T s) (hrd : s'.rd = s.rd) {o n : Nat}
    (hon : o + n ≤ 8192) (ho : Outside base o n s.mem s'.mem) : TabOk base T s' :=
  h.of_mem hrd fun x hx => ho x (.inr (by omega))

/-- What follows code may assume it names the same addresses of statics as before. -/
theorem WP.syms {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.syms = s.syms → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.syms he)⟩

/-! ## Reading the table -/

section
variable {s : State} {base T : Addr} {is : List Instr} {Q : State → Prop}

/-- `ld t3, off(t0)` of the table's word `i`, then `sd t3` to the working space. -/
theorem entWord_ok (hw : WsReg s base) (hT : TabOk base T s) {i dst q : Nat} (hi : i < 1536)
    (hoff : q < 2048) (h0 : s.gpr .t0 + BitVec.ofNat 64 q = T + BitVec.ofNat 64 (8 * i))
    (hdst : dst < 4095) (hd8 : dst % 8 = 0)
    (k : ∀ s', Rest [.t3] s s' → s'.mem = s.mem.writeW (off base dst) (sqrtWords.getD i 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.load .d .t3 .t0 q :: (sdAt .t3 wb dst ++ is))) s Q := by
  have := hT.fit; have := hT.al
  refine wp_ld hoff h0 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, List.mem_append_left _ hT.rd, Offset.contains_base T (d := 8 * i) (n := 8) (k := 12288) (by omega)
      (by omega)⟩ fun s₁ u₁ => ?_
  have r₁ := u₁.rest (ws := [.t3]) (by decide)
  refine sdAt_ws (hw.of_rest r₁) (by decide) hdst hd8 fun s₂ u₂ => k s₂ (r₁.trans (u₂.rest _)) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem, hT.held i hi]

/-- The entry `16 m + d` at `t0 + off` to slot `o`. -/
theorem entCopy_ok (hw : WsReg s base) (hT : TabOk base T s) {o q m d : Nat} (hm : m < 24) (hd : d < 16)
    (hoff : q + 24 < 2048) (ho : o < 100)
    (h0 : s.gpr .t0 + BitVec.ofNat 64 q = T + BitVec.ofNat 64 (32 * (16 * m + d))) :
    WP isa (.block (entCopy o q)) s fun s' => Rest [.t3] s s' ∧
      Outside base (p224.sl o) 32 s.mem s'.mem ∧ sv base s' o = montT m d := by
  have hsl := sl_eq o
  have hn := hw.nowrap
  have h0' : ∀ w < 4, s.gpr .t0 + BitVec.ofNat 64 (q + 8 * w) = T + BitVec.ofNat 64 (8 * (64 * m + 4 * d + w)) :=
    fun w _ => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, h0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2; omega
  rw [entCopy]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine entWord_ok hw hT (i := 64 * m + 4 * d + 0) (dst := p224.sl o) (by omega) (by omega) (by simpa using h0' 0 (by decide))
    (by omega) (by omega) fun s₁ r₁ m₁ => ?_
  have hw₁ := hw.of_rest r₁
  have hT₁ := hT.of_outside r₁.rd (o := p224.sl o) (n := 32) (by omega)
    (by rw [m₁]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  refine entWord_ok hw₁ hT₁ (i := 64 * m + 4 * d + 1) (dst := p224.sl o + 8) (by omega) (by omega)
    (by rw [r₁.gpr _ (by decide)]; exact h0' 1 (by decide)) (by omega) (by omega) fun s₂ r₂ m₂ => ?_
  have hw₂ := hw₁.of_rest r₂
  have hT₂ := hT₁.of_outside r₂.rd (o := p224.sl o) (n := 32) (by omega)
    (by rw [m₂]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  refine entWord_ok hw₂ hT₂ (i := 64 * m + 4 * d + 2) (dst := p224.sl o + 16) (by omega) (by omega)
    (by rw [r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 2 (by decide)) (by omega) (by omega)
    fun s₃ r₃ m₃ => ?_
  have hw₃ := hw₂.of_rest r₃
  have hT₃ := hT₂.of_outside r₃.rd (o := p224.sl o) (n := 32) (by omega)
    (by rw [m₃]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  rw [← List.append_nil (sdAt .t3 wb (p224.sl o + 24))]
  refine entWord_ok hw₃ hT₃ (i := 64 * m + 4 * d + 3) (dst := p224.sl o + 24) (by omega) (by omega)
    (by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 3 (by decide))
    (by omega) (by omega) fun s₄ r₄ m₄ => WP.block_nil ⟨r₁.trans (r₂.trans (r₃.trans r₄)), ?_, ?_⟩
  · rw [m₄, m₃, m₂, m₁]
    exact ((((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))).trans
      ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · refine wordsVal_of_shifts _ _ _ _ _ (Nat.lt_trans (montT_lt m d) (by decide)) fun j hj => ?_
    rw [m₄, m₃, m₂, m₁]
    have e := fun w (hw : w < 4) => sqrtWords_getD (m := m) (d := d) (w := w) hm hd hw
    have e0 : sqrtWords.getD (64 * m + 4 * d) 0 = wordOf (montT m d) 0 := e 0 (by decide)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp only [Nat.reduceMul, Nat.add_zero, Nat.shiftRight_zero]
      rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ _ _ (by omega)).word (by omega) (by omega), word_writeW_self, e0]; rfl
    · simp only [Nat.reduceMul]
      rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ _ _ (by omega)).word (by omega) (by omega), word_writeW_self, e 1 (by decide)]; rfl
    · simp only [Nat.reduceMul]
      rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega), word_writeW_self, e 2 (by decide)]; rfl
    · simp only [Nat.reduceMul]
      rw [word_writeW_self, e 3 (by decide)]; rfl

/-- `t0 =` the address of row `m`. -/
theorem rowAddr_ok {m : Nat} (hm : m < 2048) (hsym : s.syms sqrtSym = T)
    (k : ∀ s', Rest [.t0, .t1] s s' → s'.gpr .t0 = T + BitVec.ofNat 64 (512 * m) → s'.mem = s.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block (rowAddr m ++ is)) s Q := by
  rw [rowAddr]
  simp only [List.cons_append, List.nil_append]
  refine WP.cons exec_lla ?_
  have u₁ := Upd.write s .t0 (s.syms sqrtSym)
  refine wp_li hm fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => ?_
  refine k s₄ (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans
    (u₄.rest (by decide)))) ?_ (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hsym]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

end

/-! ## The digits' registers -/

/-- `k`'s low and high words in `s4` and `s5`. -/
def KRegs (k : Nat) (s : State) : Prop :=
  s.gpr .s4 = BitVec.ofNat 64 (k % 2 ^ 64) ∧ s.gpr .s5 = BitVec.ofNat 64 (k / 2 ^ 64)

theorem digit_bits {v : Nat} (c : Nat) (hv : v < 2 ^ 64) :
    ((BitVec.ofNat 64 v >>> (4 * c)) &&& BitVec.ofInt 64 15) <<< 5 = BitVec.ofNat 64 (32 * (v / 16 ^ c % 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv, show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    show 2 ^ (4 * c) = 16 ^ c by rw [Nat.pow_mul]]
  generalize v / 16 ^ c = x
  have : x % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [show x % 2 ^ 4 * 2 ^ 5 = 32 * (x % 16) by rw [Nat.mul_comm]]

/-- Digit `i` of `k` from its register. -/
theorem dreg_digit {k i : Nat} (hk : k < 16 ^ 24) (hi : i < 24) {s : State} (h : KRegs k s) :
    ((s.gpr (dreg i) >>> (4 * (i % 16))) &&& BitVec.ofInt 64 15) <<< 5 = BitVec.ofNat 64 (32 * (k / 16 ^ i % 16)) := by
  by_cases h16 : i < 16
  · rw [show dreg i = .s4 from ite_eq_left h16, h.1, Nat.mod_eq_of_lt h16, digit_bits i (Nat.mod_lt _ (by decide))]
    congr 2
    rw [show (2 : Nat) ^ 64 = 16 ^ i * 16 ^ (16 - i) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ ⟨16 ^ (16 - i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩]
  · have h5 : k / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; exact Nat.lt_of_lt_of_le hk (by decide)
    rw [show dreg i = .s5 from ite_eq_right h16, h.2, show i % 16 = i - 16 by omega, digit_bits (i - 16) h5]
    congr 2
    rw [Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 16 ^ (i - 16) = 16 ^ i by
      rw [show (2 : Nat) ^ 64 = 16 ^ 16 from rfl, ← Nat.pow_add]; congr 1; omega]

/-! ## Lookups and products -/

/-- The callee-saved registers but `rs`, the regions and the stack pointer kept. -/
structure Ks (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r ∈ preserved, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Ks.refl (rs : List Reg) (s : State) : Ks rs s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Ks.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Ks rs s₁ s₂) (h₂ : Ks rs s₂ s₃) : Ks rs s₁ s₃ :=
  ⟨fun r hr hn => (h₂.gpr r hr hn).trans (h₁.gpr r hr hn), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Ks.mono {rs rs' : List Reg} {s s' : State} (h : Ks rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Ks rs' s s' :=
  ⟨fun r hr hn => h.gpr r hr fun h' => hn (hs r h'), h.rd, h.wr, h.sp⟩

theorem Ks.of_kp {rs : List Reg} {s s' : State} (h : Kp s s') : Ks rs s s' :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp⟩

theorem Ks.of_rest {rs ws : List Reg} {s s' : State} (h : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∉ preserved ∨ r ∈ rs := by decide) : Ks rs s s' :=
  ⟨fun r hr hn => h.gpr r fun h' => (hws r h').elim (· hr) hn, h.rd, h.wr, h.sp⟩

theorem Ks.kp {s s' : State} (h : Ks [] s s') : Kp s s' :=
  ⟨fun r hr => h.gpr r hr (List.not_mem_nil), h.rd, h.wr, h.sp⟩

theorem KRegs.of_ks {k : Nat} {rs : List Reg} {s s' : State} (h : KRegs k s) (K : Ks rs s s')
    (h4 : Reg.s4 ∉ rs := by decide) (h5 : Reg.s5 ∉ rs := by decide) : KRegs k s' :=
  ⟨by rw [K.gpr _ (by decide) h4]; exact h.1, by rw [K.gpr _ (by decide) h5]; exact h.2⟩

theorem wsReg_of_ks {rs : List Reg} {s s' : State} {base : Addr} (h : WsReg s base) (K : Ks rs s s')
    (h0 : Reg.s0 ∉ rs := by decide) : WsReg s' base :=
  ⟨by rw [K.gpr _ (by decide) h0]; exact h.s0, by rw [K.wr]; exact h.wr, h.nowrap, h.al⟩

theorem slot_apart {i j : Nat} (h : i ≠ j) : p224.sl i + 32 ≤ p224.sl j ∨ p224.sl j + 32 ≤ p224.sl i := by
  rw [sl_eq, sl_eq]; omega

/-- The entry of row `m` at digit `i` of `k` to `XS`. -/
theorem lookup_ok {s : State} {base T : Addr} (hw : WsReg s base) (hT : TabOk base T s)
    (hsym : s.syms sqrtSym = T) {m i k : Nat} (hm : m < 24) (hi : i < 24) (hk : k < 16 ^ 24)
    (hK : KRegs k s) :
    WP isa (.block (lookup m i)) s fun s' => Rest [.t0, .t1, .t2, .t3] s s' ∧
      Outside base (p224.sl XS) 32 s.mem s'.mem ∧ sv base s' XS = montT m (k / 16 ^ i % 16) := by
  rw [lookup, List.append_assoc]
  refine rowAddr_ok (by omega) hsym fun s₁ r₁ h0₁ m₁ => ?_
  have hK₁ : KRegs k s₁ := ⟨by rw [r₁.gpr _ (by decide)]; exact hK.1, by rw [r₁.gpr _ (by decide)]; exact hK.2⟩
  simp only [List.cons_append]
  refine wp_srl (by omega) fun s₂ u₂ => wp_andi (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ =>
    wp_add fun s₅ u₅ => ?_
  have ht2 : s₄.gpr .t2 = BitVec.ofNat 64 (32 * (k / 16 ^ i % 16)) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, dreg_digit hk hi hK₁]
  have ht0 : s₅.gpr .t0 + BitVec.ofNat 64 0 = T + BitVec.ofNat 64 (32 * (16 * m + k / 16 ^ i % 16)) := by
    rw [u₅.gpr, ht2, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h0₁,
      BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega
  have r₅ : Rest [.t0, .t1, .t2, .t3] s s₅ :=
    (r₁.mono (by decide)).trans ((((u₂.rest (by decide)).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))).trans (u₅.rest (by decide)))
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hT₅ : TabOk base T s₅ := hT.of_mem r₅.rd fun x _ => by rw [hm₅]
  refine WP.mono (entCopy_ok (hw.of_rest r₅) hT₅ (o := XS) (q := 0) hm (Nat.mod_lt _ (by decide)) (by decide)
    (by decide) ht0) fun s₆ ⟨r₆, O₆, v₆⟩ => ⟨r₅.trans (r₆.mono (by decide)), by rw [← hm₅]; exact O₆, v₆⟩

/-- `[y] = [y] T m dᵢ`. -/
theorem mulStep_ok {s : State} {base T : Addr} (hw : WsReg s base) (hT : TabOk base T s)
    (hsym : s.syms sqrtSym = T) {y m i k : Nat} (hy : y < 100) (hyx : y ≠ XS) (hm : m < 24) (hi : i < 24)
    (hk : k < 16 ^ 24) (hK : KRegs k s) :
    WP isa (mulStep y m i) s fun s' => Kp s s' ∧
      Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' y < W.p ∧
      toM W.p (2 ^ 256) (sv base s' y) = toM W.p (2 ^ 256) (sv base s y) * tbl224 m (k / 16 ^ i % 16) := by
  have hsl := sl_eq y
  rw [mulStep]
  refine WP.seq (WP.mono (lookup_ok hw hT hsym hm hi hk hK) fun s₁ ⟨r₁, O₁, v₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  have ey : sv base s₁ y = sv base s y := O₁.wordsVal (by have := slot_apart hyx; omega) (by omega)
  refine WP.mono (mulCall_ok field_ok hw₁ (o := p224.sl y) (a := p224.sl y) (b := p224.sl XS)
    (by show p224.sl y + 8 * 4 ≤ 3840; omega) (by show p224.sl y + 8 * 4 ≤ 3840; omega) (by decide) (by omega)
    (by omega) (by decide)
    (by show sv base s₁ XS < _; rw [v₁]; exact montT_lt _ _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_
  refine ⟨(Kp.of_rest r₁).trans C₂.kp, O₁.unch.trans C₂.mem, lt₂, ?_⟩
  refine (toM_mul unit e₂).trans ?_
  show toM W.p (2 ^ 256) (sv base s₁ y) * toM W.p (2 ^ 256) (sv base s₁ XS) = _
  rw [ey, v₁, toM_montT]

theorem w3_le {y : Nat} (hy : y < 100) :
    ∀ w ∈ [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)], w.1 + w.2 ≤ 8192 := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · decide
  · show p224.sl y + 32 ≤ 8192; rw [sl_eq]; omega
  · decide

/-- `[y] = [y] Π_(i<n) T (o + i) dᵢ`: `tacc`. -/
theorem muls_ok {base T : Addr} {y o k : Nat} (hy : y < 100) (hyx : y ≠ XS) (hk : k < 16 ^ 24) :
    ∀ n, o + n ≤ 24 → ∀ {s : State}, WsReg s base → TabOk base T s → s.syms sqrtSym = T → KRegs k s →
      sv base s y < W.p →
      WP isa (muls y o n) s fun s' => WsReg s' base ∧ TabOk base T s' ∧ s'.syms = s.syms ∧ Kp s s' ∧
        Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' y < W.p ∧
        toM W.p (2 ^ 256) (sv base s' y) = tacc tbl224 o k (toM W.p (2 ^ 256) (sv base s y)) n
  | 0, _, _, hw, hT, _, _, hlt => WP.block_nil ⟨hw, hT, rfl, Kp.refl _, Unch.refl _ _ _, hlt, rfl⟩
  | n + 1, hn, s, hw, hT, hsym, hK, hlt => by
    have hsl := sl_eq y
    rw [muls]
    refine WP.seq (WP.syms (muls_ok hy hyx hk n (by omega) hw hT hsym hK hlt)
      fun s₁ ⟨hw₁, hT₁, _, K₁, U₁, lt₁, v₁⟩ sy₁ => ?_)
    refine WP.syms (mulStep_ok hw₁ hT₁ (by rw [sy₁]; exact hsym) hy hyx (m := o + n) (i := n) (by omega) (by omega) hk
      (hK.of_ks (Ks.of_kp (rs := []) K₁))) fun s₂ ⟨K₂, U₂, lt₂, v₂⟩ sy₂ => ?_
    refine ⟨hw₁.of_kp K₂, hT₁.of_unch K₂.rd (w3_le hy) U₂,
      by rw [sy₂, sy₁], K₁.trans K₂, (U₁.trans U₂).mono fun w hw => (List.mem_append.mp hw).elim id id, lt₂, ?_⟩
    rw [v₂, v₁, tacc]

/-! ## The comparisons -/

theorem mask_and_imm (c : Bool) (v : Nat) :
    maskOf c &&& BitVec.ofNat 64 v = BitVec.ofNat 64 (if c then v else 0) := by
  cases c
  · simp [maskOf]
  · show BitVec.allOnes 64 &&& _ = _; exact BitVec.allOnes_and

theorem digAcc_le (G : Nat → Fe W) (y : Fe W) : ∀ f, digAcc G y f ≤ 15 * f
  | 0 => Nat.le_refl _
  | f + 1 => by
    rw [digAcc]
    have := digAcc_le G y f
    split <;> omega

/-- `s6 += (16 - e) mod 16` if `y = g^e`. -/
theorem cmpStep_ok {s : State} {base : Addr} (hw : WsReg s base) {e v : Nat} (he : e < 16)
    (hY : sv base s YS < W.p) (hG : sv base s (GS e) < W.p) (h6 : s.gpr .s6 = BitVec.ofNat 64 v) :
    WP isa (cmpStep e) s fun s' => WsReg s' base ∧ Ks [.s6] s s' ∧
      Unch base [(p224.sl TD, 32), (own 4, 256)] s.mem s'.mem ∧
      s'.gpr .s6 = BitVec.ofNat 64 (v + if toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e))
        then (16 - e) % 16 else 0) := by
  have hp0 : 0 < W.p := by decide
  rw [cmpStep]
  refine WP.seq (WP.mono (subCall_ok field_ok hw (o := p224.sl TD) (a := p224.sl YS) (b := p224.sl (GS e))
    (by decide) (by decide) (by show p224.sl (GS e) + 8 * 4 ≤ 3840; rw [sl_eq]; simp only [GS]; omega) (by decide)
    (by decide) (by rw [sl_eq]; simp only [GS]; omega) hY hG) fun s₁ ⟨C₁, e₁⟩ => ?_)
  have e₁' : sv base s₁ TD = (sv base s YS + W.p - sv base s (GS e)) % W.p := e₁
  have hw₁ := hw.of_kp C₁.kp
  refine WP.block_append (WP.mono (zeroMask_ok hw₁ (n := 4) (a := p224.sl TD) (by decide) (by decide))
    fun s₂ ⟨r₂, m₂, g₂⟩ => ?_)
  refine wp_andi (by unfold imm12; omega) fun s₃ u₃ => wp_add fun s₄ u₄ => WP.block_nil ?_
  have K₄ : Ks [.s6] s s₄ := ((Ks.of_kp C₁.kp).trans (Ks.of_rest r₂)).trans
    ((Ks.of_rest (u₃.rest (ws := [.a7]) (by decide))).trans (Ks.of_rest (u₄.rest (ws := [.s6]) (by decide))))
  have hz : wordsVal s₁.mem base (p224.sl TD) 4 = 0 ↔
      toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e)) := by
    have hlt : sv base s₁ TD < W.p := by rw [e₁']; exact Nat.mod_lt _ hp0
    rw [← toM_eq_zero_iff unit hlt]
    show toM W.p (2 ^ 256) (sv base s₁ TD) = 0 ↔ _
    rw [e₁', toM_sub (by omega)]
    constructor <;> intro h <;> grind
  refine ⟨⟨by rw [K₄.gpr _ (by decide) (by decide)]; exact hw.s0, by rw [K₄.wr]; exact hw.wr, hw.nowrap, hw.al⟩,
    K₄, by rw [u₄.mem, u₃.mem, m₂]; exact C₁.mem, ?_⟩
  rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), r₂.gpr _ (by decide), C₁.kp.gpr _ (by decide), h6, g₂,
    ofInt_ofNat, mask_and_imm, BitVec.ofNat_add_ofNat]
  refine congrArg (fun x => BitVec.ofNat 64 (v + x)) ?_
  by_cases h : toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e))
  · rw [ite_eq_left h, decide_eq_true (hz.mpr h)]; rfl
  · rw [ite_eq_right h, decide_eq_false (fun h' => h (hz.mp h'))]; rfl

theorem gs_apart {e : Nat} (he : e < 16) :
    ∀ w ∈ [(p224.sl TD, 32), (own 4, 256)], p224.sl (GS e) + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl (GS e) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · right; show p224.sl TD + 32 ≤ p224.sl (GS e); rw [sl_eq, sl_eq]; simp only [GS, TD]; omega
  · left; show p224.sl (GS e) + 32 ≤ 3840; rw [sl_eq]; simp only [GS]; omega

/-- The comparisons with `g^e`, `e < f`: `digAcc`. -/
theorem cmps_ok {base : Addr} {G : Nat → Fe W} :
    ∀ f, f ≤ 16 → ∀ {s : State}, WsReg s base → sv base s YS < W.p →
      (∀ e < 16, sv base s (GS e) < W.p ∧ toM W.p (2 ^ 256) (sv base s (GS e)) = G e) →
      s.gpr .s6 = 0 →
      WP isa (cmps f) s fun s' => WsReg s' base ∧ Ks [.s6] s s' ∧
        Unch base [(p224.sl TD, 32), (own 4, 256)] s.mem s'.mem ∧
        s'.gpr .s6 = BitVec.ofNat 64 (digAcc G (toM W.p (2 ^ 256) (sv base s YS)) f)
  | 0, _, s, hw, _, _, h6 => WP.block_nil ⟨hw, Ks.refl _ _, Unch.refl _ _ _, by rw [h6]; rfl⟩
  | f + 1, hf, s, hw, hY, hG, h6 => by
    rw [cmps]
    refine WP.seq (WP.mono (cmps_ok f (by omega) hw hY hG h6) fun s₁ ⟨hw₁, K₁, U₁, v₁⟩ => ?_)
    have ey : sv base s₁ YS = sv base s YS := sv_unch U₁ YS (by decide)
    have eg : sv base s₁ (GS f) = sv base s (GS f) := sv_unch U₁ (GS f) (gs_apart (by omega)) (by simp only [GS]; omega)
    refine WP.mono (cmpStep_ok hw₁ (e := f) (by omega) (by rw [ey]; exact hY)
      (by rw [eg]; exact (hG f (by omega)).1) v₁) fun s₂ ⟨hw₂, K₂, U₂, v₂⟩ => ⟨hw₂, K₁.trans K₂,
        (U₁.trans U₂).cover (by decide), ?_⟩
    rw [v₂, ey, eg, (hG f (by omega)).2, digAcc]

/-! ## The digits -/

/-- `w`, `r`, `t` and `t^(16^m)` of `rhs = a`, and the digits, as `root224` has them. -/
abbrev wOf (a : Fe W) : Fe W := Spec.Weierstrass.pow a ((q224 - 1) / 2)
abbrev rOf (a : Fe W) : Fe W := wOf a * a
abbrev tOf (a : Fe W) : Fe W := wOf a * rOf a
abbrev sOf (a : Fe W) (m : Nat) : Fe W := Spec.Weierstrass.pow (tOf a) (16 ^ m)
abbrev kA (a : Fe W) (j : Nat) : Nat := kGo tbl224 (sOf a) 24 j

theorem kA_zero (a : Fe W) : kA a 0 = 0 := by rw [kA, kGo]

theorem root224_eq (a : Fe W) : root224 a = tacc tbl224 0 (kA a 24 / 2) (rOf a) 24 := rfl

theorem kA_lt (a : Fe W) {j : Nat} (hj : j ≤ 24) : kA a j < 16 ^ 24 :=
  Nat.lt_of_lt_of_le (VG.Proof.Weierstrass.kGo_lt _ _ _ j) (Nat.pow_le_pow_right (by decide) hj)

/-- What the digits read, after `t`'s powers and the last row. -/
structure FSt (a : Fe W) (base : Addr) (s : State) : Prop where
  ss : ∀ m < 24, sv base s (SS m) < W.p ∧ toM W.p (2 ^ 256) (sv base s (SS m)) = sOf a m
  gs : ∀ e < 16, sv base s (GS e) < W.p ∧ toM W.p (2 ^ 256) (sv base s (GS e)) = tbl224 23 e
  tr : sv base s TR < W.p ∧ toM W.p (2 ^ 256) (sv base s TR) = rOf a

/-- The slots the digits write, and the field functions' own space. -/
abbrev dW : List (Nat × Nat) := [(p224.sl YS, 32), (p224.sl XS, 32), (p224.sl TD, 32), (own 4, 256)]

theorem dW_apart {i : Nat} (hi : i = TR ∨ 55 ≤ i ∧ i < 95) :
    ∀ w ∈ dW, p224.sl i + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl i := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have ho : own 4 = 3840 := by decide
  rcases hw with rfl | rfl | rfl | rfl <;> simp only [sl_eq, YS, XS, TD, TR, ho] at hi ⊢ <;> omega

theorem FSt.of_unch {a : Fe W} {base : Addr} {s s' : State} (h : FSt a base s) (U : Unch base dW s.mem s'.mem) :
    FSt a base s' where
  ss m hm := by
    have e : sv base s' (SS m) = sv base s (SS m) :=
      sv_unch U (SS m) (dW_apart (.inr (by simp only [SS]; omega))) (by simp only [SS]; omega)
    rw [e]; exact h.ss m hm
  gs e he := by
    have e' : sv base s' (GS e) = sv base s (GS e) :=
      sv_unch U (GS e) (dW_apart (.inr (by simp only [GS]; omega))) (by simp only [GS]; omega)
    rw [e']; exact h.gs e he
  tr := by
    have e : sv base s' TR = sv base s TR := sv_unch U TR (dW_apart (.inl rfl)) (by decide)
    rw [e]; exact h.tr

/-- After `j` digits, from the state `s₀` the digits start from. -/
structure DSt (a : Fe W) (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  tab : TabOk base T s
  sym : s.syms sqrtSym = T
  ks : Ks [.s4, .s5, .s6] s₀ s
  unch : Unch base dW s₀.mem s.mem
  k : KRegs (kA a j) s

/-- `a ||| d 16^c = a + d 16^c` for `a < 16^c`. -/
theorem or_digit {a d c : Nat} (ha : a < 16 ^ c) (hd : d < 16) (hc : c < 16) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (d * 16 ^ c) = BitVec.ofNat 64 (a + d * 16 ^ c) := by
  have h16 : 16 ^ c = 2 ^ (4 * c) := by rw [Nat.pow_mul]
  have hc' : 16 ^ c * 16 ≤ 2 ^ 64 := by
    rw [← Nat.pow_succ]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : c + 1 ≤ 16)) (by decide)
  have hdl := Nat.mul_le_mul_right (16 ^ c) (show d ≤ 15 by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.or_comm, Nat.mul_comm d, h16,
    ← Nat.two_pow_add_eq_or_of_lt (by rw [← h16]; exact ha), Nat.add_comm]

/-- The digit `D mod 16` into its register. -/
theorem dfinal_ok {s : State} {j k D : Nat} (hj : j < 24) (hk : k < 16 ^ j) (h6 : s.gpr .s6 = BitVec.ofNat 64 D)
    (hK : KRegs k s) :
    WP isa (.block [.logicImm .and .s6 .s6 15, .shift .sll .d .s6 .s6 (4 * (j % 16)),
      .logic .or (dreg j) (dreg j) .s6]) s fun s' =>
      Rest [.s4, .s5, .s6] s s' ∧ s'.mem = s.mem ∧ KRegs (k + D % 16 * 16 ^ j) s' := by
  refine wp_andi (by decide) fun s₁ u₁ => wp_sll (by omega) fun s₂ u₂ => wp_or fun s₃ u₃ => WP.block_nil ?_
  have hd : D % 16 < 16 := Nat.mod_lt _ (by decide)
  have v₂ : s₂.gpr .s6 = BitVec.ofNat 64 (D % 16 * 16 ^ (j % 16)) := by
    rw [u₂.gpr, u₁.gpr, h6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
      show 2 ^ (4 * (j % 16)) = 16 ^ (j % 16) by rw [Nat.pow_mul], show D % 2 ^ 64 % 2 ^ 4 = D % 16 by omega]
  have hdr : ∀ r, r = .s4 ∨ r = .s5 → r ≠ dreg j → s₃.gpr r = s.gpr r := fun r hr hn => by
    rw [u₃.other _ hn, u₂.other _ (by rcases hr with rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl <;> decide)]
  have hd3 : s₃.gpr (dreg j) = s.gpr (dreg j) ||| BitVec.ofNat 64 (D % 16 * 16 ^ (j % 16)) := by
    rw [u₃.gpr, v₂, u₂.other _ (by unfold dreg; split <;> decide), u₁.other _ (by unfold dreg; split <;> decide)]
  refine ⟨((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by unfold dreg; split <;> decide)),
    by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  have hdl := Nat.mul_le_mul_right (16 ^ j) (show D % 16 ≤ 15 by omega)
  by_cases h16 : j < 16
  · have hj16 : 16 ^ j * 16 ≤ 2 ^ 64 := by
      rw [← Nat.pow_succ]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show j + 1 ≤ 16 by omega)) (by decide)
    have e4 : dreg j = .s4 := ite_eq_left h16
    rw [e4, hK.1, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt (by omega), or_digit hk hd h16] at hd3
    refine ⟨by rw [hd3, Nat.mod_eq_of_lt (show k + D % 16 * 16 ^ j < 2 ^ 64 by omega)], ?_⟩
    rw [hdr .s5 (.inr rfl) (by rw [e4]; decide), hK.2, Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  · have e5 : dreg j = .s5 := ite_eq_right h16
    have hp : 16 ^ j = 2 ^ 64 * 16 ^ (j - 16) := by
      rw [show (2 : Nat) ^ 64 = 16 ^ 16 from rfl, ← Nat.pow_add]; congr 1; omega
    have hkh : k / 2 ^ 64 < 16 ^ (j - 16) := by
      rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm, ← hp]; exact hk
    rw [e5, hK.2, show j % 16 = j - 16 by omega, or_digit hkh hd (by omega)] at hd3
    refine ⟨?_, ?_⟩
    · rw [hdr .s4 (.inl rfl) (by rw [e5]; decide), hK.1, hp, Nat.mul_left_comm, Nat.add_mul_mod_self_left]
    · rw [hd3, hp, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (by decide)]

/-- `y = s_(23-j)`, `s6 = 0`. -/
theorem dstart_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 24) :
    WP isa (.block (copy 4 (p224.sl YS) (p224.sl (SS (23 - j))) ++ ([.li .s6 0] : List Instr))) s fun s' =>
      Rest [.t0, .s6] s s' ∧ Outside base (p224.sl YS) 32 s.mem s'.mem ∧ sv base s' YS = sv base s (SS (23 - j)) ∧
      s'.gpr .s6 = 0 := by
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := p224.sl YS) (a := p224.sl (SS (23 - j))) (by decide)
    (by rw [sl_eq]; omega) (by decide) (by rw [sl_eq]; simp only [SS]; omega)
    (Or.inl (by rw [sl_eq, sl_eq]; simp only [SS, YS]; omega))) fun s₁ ⟨v₁, r₁, O₁⟩ =>
    wp_li (imm := 0) (by decide) fun s₂ u₂ => WP.block_nil ⟨(r₁.mono (by decide)).trans (u₂.rest (by decide)),
      by rw [u₂.mem]; exact O₁, by show wordsVal _ _ _ _ = _; rw [u₂.mem]; exact v₁, by rw [u₂.gpr]; rfl⟩)

/-- Digit `j`. -/
theorem digit_ok {a : Fe W} {base T : Addr} {s₀ s : State} {j : Nat} (hj : j < 24) (F : FSt a base s₀)
    (D : DSt a base T s₀ s j) : WP isa (digit j) s fun s' => DSt a base T s₀ s' (j + 1) := by
  have F' := F.of_unch D.unch
  have hk := VG.Proof.Weierstrass.kGo_lt tbl224 (sOf a) 24 j
  rw [digit]
  refine WP.seq (WP.syms (dstart_ok D.ws hj) fun s₁ ⟨r₁, O₁, v₁, z₁⟩ sy₁ => ?_)
  have hw₁ := wsReg_of_ks D.ws (Ks.of_rest (rs := [.s6]) r₁)
  have hT₁ := D.tab.of_outside r₁.rd (by decide) O₁
  have hK₁ : KRegs (kA a j) s₁ := ⟨by rw [r₁.gpr _ (by decide)]; exact D.k.1, by rw [r₁.gpr _ (by decide)]; exact D.k.2⟩
  refine WP.seq (WP.mono (muls_ok (y := YS) (o := 23 - j) (k := kA a j) (by decide) (by decide) (kA_lt a (by omega))
    j (by omega) hw₁ hT₁ (by rw [sy₁]; exact D.sym) hK₁ (by rw [v₁]; exact (F'.ss _ (by omega)).1))
    fun s₂ ⟨hw₂, hT₂, sy₂, K₂, U₂, lt₂, v₂⟩ => ?_)
  have U₀₂ : Unch base dW s.mem s₂.mem := (O₁.unch.trans U₂).cover (by decide)
  have hG₂ : ∀ e < 16, sv base s₂ (GS e) < W.p ∧ toM W.p (2 ^ 256) (sv base s₂ (GS e)) = tbl224 23 e :=
    (F'.of_unch U₀₂).gs
  refine WP.seq (WP.syms (cmps_ok (G := tbl224 23) 16 (by decide) hw₂ lt₂ hG₂
    (by rw [K₂.gpr _ (by decide), z₁])) fun s₃ ⟨hw₃, K₃, U₃, v₃⟩ sy₃ => ?_)
  refine WP.syms (dfinal_ok hj hk v₃ ((hK₁.of_ks (Ks.of_kp (rs := []) K₂)).of_ks K₃)) fun s₄ ⟨r₄, m₄, k₄⟩ sy₄ => ?_
  have hy₂ : toM W.p (2 ^ 256) (sv base s₂ YS) = tacc tbl224 (23 - j) (kA a j) (sOf a (23 - j)) j := by
    rw [v₂, v₁, (F'.ss _ (by omega)).2]
  refine ⟨wsReg_of_ks hw₃ (Ks.of_rest (rs := [.s4, .s5, .s6]) r₄), (hT₂.of_unch K₃.rd (by decide) U₃).of_mem r₄.rd
      (fun x _ => by rw [m₄]), by rw [sy₄, sy₃, sy₂, sy₁]; exact D.sym,
    D.ks.trans ((Ks.of_rest r₁).trans ((Ks.of_kp K₂).trans ((K₃.mono).trans (Ks.of_rest r₄)))),
    (D.unch.trans (U₀₂.trans (by rw [m₄]; exact U₃))).cover (by decide), ?_⟩
  rw [hy₂] at k₄
  exact k₄

/-- The digits `0 … j - 1`. -/
theorem digits_ok {a : Fe W} {base T : Addr} {s₀ : State} (F : FSt a base s₀) :
    ∀ j, j ≤ 24 → ∀ {s : State}, DSt a base T s₀ s 0 → WP isa (digits j) s fun s' => DSt a base T s₀ s' j
  | 0, _, _, D => WP.block_nil D
  | j + 1, hj, _, D => by
    rw [digits]
    exact WP.seq (WP.mono (digits_ok F j (by omega) D) fun _ D' => digit_ok (by omega) F D')

/-! ## The root -/

/-- `s5:s4 >>= 1`. -/
theorem halve_ok {s : State} {k : Nat} (hk : k < 16 ^ 24) (hK : KRegs k s) :
    WP isa (.block halve) s fun s' => Rest [.t0, .t1, .s4, .s5] s s' ∧ s'.mem = s.mem ∧ KRegs (k / 2) s' := by
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_or fun s₃ u₃ =>
    wp_srl (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, ?_⟩
  · exact (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))
  · have hk' : k < 2 ^ 96 := hk
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide), hK.1, hK.2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show k / 2 ^ 64 < 2 ^ 64 by omega)]
    rw [show k / 2 ^ 64 * 2 ^ 63 % 2 ^ 64 = 2 ^ 63 * (k / 2 ^ 64 % 2) by omega, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (show k % 2 ^ 64 / 2 ^ 1 < 2 ^ 63 by omega)]
    omega
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hK.2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have hk' : k < 2 ^ 96 := hk
    omega

/-- `ACC = r`, `k / 2`. -/
theorem rstart_ok {s : State} {base : Addr} (hw : WsReg s base) {k : Nat} (hk : k < 16 ^ 24) (hK : KRegs k s) :
    WP isa (.block (copy 4 (p224.sl ACC) (p224.sl TR) ++ halve)) s fun s' =>
      Rest [.t0, .t1, .s4, .s5] s s' ∧ Outside base (p224.sl ACC) 32 s.mem s'.mem ∧
      sv base s' ACC = sv base s TR ∧ KRegs (k / 2) s' :=
  WP.block_append (WP.mono (copy_ok 4 hw (o := p224.sl ACC) (a := p224.sl TR) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₁ ⟨v₁, r₁, O₁⟩ =>
      WP.mono (halve_ok hk (hK.of_ks (Ks.of_rest (rs := []) r₁))) fun s₂ ⟨r₂, m₂, k₂⟩ =>
        ⟨(r₁.mono (by decide)).trans r₂, by rw [m₂]; exact O₁, by show wordsVal _ _ _ _ = _; rw [m₂]; exact v₁, k₂⟩)

/-- `[ACC] = root224 a`. -/
theorem rootMul_ok {a : Fe W} {base T : Addr} {s₀ s : State} (F : FSt a base s₀) (D : DSt a base T s₀ s 24) :
    WP isa rootMul s fun s' => WsReg s' base ∧ TabOk base T s' ∧ s'.syms = s.syms ∧ Ks [.s4, .s5] s s' ∧
      Unch base [(p224.sl ACC, 32), (p224.sl XS, 32), (p224.sl ACC, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' ACC < W.p ∧ toM W.p (2 ^ 256) (sv base s' ACC) = root224 a := by
  have F' := F.of_unch D.unch
  rw [rootMul]
  refine WP.seq (WP.syms (rstart_ok D.ws (kA_lt a (Nat.le_refl _)) D.k) fun s₁ ⟨r₁, O₁, v₁, k₁⟩ sy₁ => ?_)
  have hw₁ := wsReg_of_ks D.ws (Ks.of_rest (rs := [.s4, .s5]) r₁)
  refine WP.mono (muls_ok (y := ACC) (o := 0) (k := kA a 24 / 2) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (kA_lt a (Nat.le_refl _))) 24 (by decide) hw₁
    (D.tab.of_outside r₁.rd (by decide) O₁) (by rw [sy₁]; exact D.sym) k₁ (by rw [v₁]; exact F'.tr.1))
    fun s₂ ⟨hw₂, hT₂, sy₂, K₂, U₂, lt₂, v₂⟩ => ⟨hw₂, hT₂, by rw [sy₂, sy₁], (Ks.of_rest r₁).trans (Ks.of_kp K₂),
      O₁.unch.trans U₂, lt₂, ?_⟩
  rw [v₂, v₁, F'.tr.2, root224_eq]

end VG.Proof.EcKey.Compressed.RISCV64.P224
