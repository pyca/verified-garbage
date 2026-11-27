module

public import VerifiedGarbage.Impl.EcKey.Compressed.P224.RISCV64
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Check
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
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
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_using [hm, hd, hw]), Option.map_some,
    Option.getD_some]
  rw [show (64 * m + 4 * d + w) / 64 = m by omega_using [hd, hw], show (64 * m + 4 * d + w) / 4 % 16 = d by omega_using [hd, hw],
    show (64 * m + 4 * d + w) % 4 = w by omega_using [hw]]

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
    exact h.far _ (by omega_using [hi, hb])
  al := h.al
  rd := hrd ▸ h.rd
  fit := h.fit
  far := h.far

theorem TabOk.of_unch {s s' : State} {base T : Addr} (h : TabOk base T s) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) :
    TabOk base T s' :=
  h.of_mem hrd fun _ hx => hu.far fun w hw => by have := hW w hw; omega_using [hx, this]

theorem TabOk.of_outside {s s' : State} {base T : Addr} (h : TabOk base T s) (hrd : s'.rd = s.rd) {o n : Nat}
    (hon : o + n ≤ 8192) (ho : Outside base o n s.mem s'.mem) : TabOk base T s' :=
  h.of_mem hrd fun x hx => ho x (.inr (by omega_using [hon, hx]))

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
  refine wp_ld hoff h0 (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [this])
    ⟨_, List.mem_append_left _ hT.rd, Offset.contains_base T (d := 8 * i) (n := 8) (k := 12288) (by omega_using [hi])
      (by omega_using [hi])⟩ fun s₁ u₁ => ?_
  obtain r₁ := u₁.rest (ws := [.t3]) (by decide)
  refine sdAt_ws (hw.of_rest r₁) (by decide) hdst hd8 fun s₂ u₂ => k s₂ (r₁.trans (u₂.rest _)) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem, hT.held i hi]

/-- The entry `16 m + d` at `t0 + off` to slot `o`. -/
theorem entCopy_ok (hw : WsReg s base) (hT : TabOk base T s) {o q m d : Nat} (hm : m < 24) (hd : d < 16)
    (hoff : q + 24 < 2048) (ho : o < 100)
    (h0 : s.gpr .t0 + BitVec.ofNat 64 q = T + BitVec.ofNat 64 (32 * (16 * m + d))) :
    WP isa (.block (entCopy o q)) s fun s' => Rest [.t3] s s' ∧
      Outside base (p224.sl o) 32 s.mem s'.mem ∧ sv base s' o = montT m d := by
  obtain hsl := sl_eq o
  have hn := hw.nowrap
  obtain h0' : ∀ w < 4, s.gpr .t0 + BitVec.ofNat 64 (q + 8 * w) = T + BitVec.ofNat 64 (8 * (64 * m + 4 * d + w)) :=
    fun w _ => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, h0, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2; omega_using []
  rw [entCopy]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine entWord_ok hw hT (i := 64 * m + 4 * d + 0) (dst := p224.sl o) (by omega_using [hm, hd]) (by omega_using [hoff]) (by simpa using h0' 0 (by decide))
    (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₁ r₁ m₁ => ?_
  obtain hw₁ := hw.of_rest r₁
  obtain hT₁ := hT.of_outside r₁.rd (o := p224.sl o) (n := 32) (by omega_using [ho, hsl])
    (by rw [m₁]; exact (writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))
  refine entWord_ok hw₁ hT₁ (i := 64 * m + 4 * d + 1) (dst := p224.sl o + 8) (by omega_using [hm, hd]) (by omega_using [hoff])
    (by rw [r₁.gpr _ (by decide)]; exact h0' 1 (by decide)) (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₂ r₂ m₂ => ?_
  obtain hw₂ := hw₁.of_rest r₂
  obtain hT₂ := hT₁.of_outside r₂.rd (o := p224.sl o) (n := 32) (by omega_using [ho, hsl])
    (by rw [m₂]; exact (writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))
  refine entWord_ok hw₂ hT₂ (i := 64 * m + 4 * d + 2) (dst := p224.sl o + 16) (by omega_using [hm, hd]) (by omega_using [hoff])
    (by rw [r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 2 (by decide)) (by omega_using [ho, hsl]) (by omega_using [hsl])
    fun s₃ r₃ m₃ => ?_
  obtain hw₃ := hw₂.of_rest r₃
  obtain hT₃ := hT₂.of_outside r₃.rd (o := p224.sl o) (n := 32) (by omega_using [ho, hsl])
    (by rw [m₃]; exact (writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))
  rw [← List.append_nil (sdAt .t3 wb (p224.sl o + 24))]
  refine entWord_ok hw₃ hT₃ (i := 64 * m + 4 * d + 3) (dst := p224.sl o + 24) (by omega_using [hm, hd]) (by omega_using [hoff])
    (by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 3 (by decide))
    (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₄ r₄ m₄ => WP.block_nil ⟨r₁.trans (r₂.trans (r₃.trans r₄)), ?_, ?_⟩
  · rw [m₄, m₃, m₂, m₁]
    exact ((((writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using [])).trans
      ((writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ _ _ (by omega_using [ho, hsl])).mono (by omega_using []) (by omega_using []))
  · refine wordsVal_of_shifts _ _ _ _ _ (Nat.lt_trans (montT_lt m d) (by decide)) fun j hj => ?_
    rw [m₄, m₃, m₂, m₁]
    obtain e := fun w (hw : w < 4) => sqrtWords_getD (m := m) (d := d) (w := w) hm hd hw
    obtain e0 : sqrtWords.getD (64 * m + 4 * d) 0 = wordOf (montT m d) 0 := e 0 (by decide)
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp only [Nat.reduceMul, Nat.add_zero, Nat.shiftRight_zero]
      rw [(writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]),
        (writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]),
        (writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]), word_writeW_self, e0]; rfl
    · simp only [Nat.reduceMul]
      rw [(writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]),
        (writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]), word_writeW_self, e 1 (by decide)]; rfl
    · simp only [Nat.reduceMul]
      rw [(writeW_outside _ _ _ (by omega_using [ho, hsl])).word (by omega_using []) (by omega_using [ho, hsl]), word_writeW_self, e 2 (by decide)]; rfl
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
  obtain u₁ := Upd.write s .t0 (s.syms sqrtSym)
  refine wp_li hm fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => ?_
  refine k s₄ (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans
    (u₄.rest (by decide)))) ?_ (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hsym]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

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
    rw [show (2 : Nat) ^ 64 = 16 ^ i * 16 ^ (16 - i) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega_using [h16])],
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ ⟨16 ^ (16 - i - 1), by rw [← Nat.pow_succ']; congr 1; omega_using [h16]⟩]
  · have h5 : k / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; exact Nat.lt_of_lt_of_le hk (by decide)
    rw [show dreg i = .s5 from ite_eq_right h16, h.2, show i % 16 = i - 16 by omega_using [hi, h16], digit_bits (i - 16) h5]
    congr 2
    rw [Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 16 ^ (i - 16) = 16 ^ i by
      rw [show (2 : Nat) ^ 64 = 16 ^ 16 from rfl, ← Nat.pow_add]; congr 1; omega_using [h16]]

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

theorem KRegs.of_ks {k : Nat} {rs : List Reg} {s s' : State} (h : KRegs k s) (K : Ks rs s s')
    (h4 : Reg.s4 ∉ rs := by decide) (h5 : Reg.s5 ∉ rs := by decide) : KRegs k s' :=
  ⟨by rw [K.gpr _ (by decide) h4]; exact h.1, by rw [K.gpr _ (by decide) h5]; exact h.2⟩

theorem wsReg_of_ks {rs : List Reg} {s s' : State} {base : Addr} (h : WsReg s base) (K : Ks rs s s')
    (h0 : Reg.s0 ∉ rs := by decide) : WsReg s' base :=
  ⟨by rw [K.gpr _ (by decide) h0]; exact h.s0, by rw [K.wr]; exact h.wr, h.nowrap, h.al⟩

theorem slot_apart {i j : Nat} (h : i ≠ j) : p224.sl i + 32 ≤ p224.sl j ∨ p224.sl j + 32 ≤ p224.sl i := by
  rw [sl_eq, sl_eq]; omega_using [h]

/-- A register shift right of `s`'s `n` by `m`'s low six bits. -/
theorem exec_srlReg (s : State) (d n m : Reg) :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

theorem bne_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this)
    simp [this, h]

theorem ltu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The loop's test `s ≠ t0` for counts `i` and `n`. -/
theorem eval_ne_count {t : State} {r : Reg} {i n : Nat} (hi : i < 2 ^ 64) (hn : n < 2 ^ 64)
    (h1 : t.gpr r = BitVec.ofNat 64 i) (h2 : t.gpr .t0 = BitVec.ofNat 64 n) :
    isa.eval (.ne r .t0) t = some (decide (i ≠ n)) := by
  show some (t.gpr r != t.gpr .t0) = _
  rw [h1, h2, bne_ofNat hi hn]

/-- The entry of row `o + i` at digit `i` of `k` to `XS`, for `i` in `s6`. -/
theorem lookup_ok {s : State} {base T : Addr} (hw : WsReg s base) (hT : TabOk base T s)
    (hsym : s.syms sqrtSym = T) {o i k : Nat} (hoi : o + i < 24) (hk : k < 16 ^ 24)
    (hK : KRegs k s) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) :
    WP isa (lookup o) s fun s' => Rest [.t0, .t1, .t2, .t3] s s' ∧
      Outside base (p224.sl XS) 32 s.mem s'.mem ∧ sv base s' XS = montT (o + i) (k / 16 ^ i % 16) := by
  obtain hi : i < 24 := by omega_using [hoi]
  unfold lookup
  refine WP.seq (WP.cons exec_lla (wp_addi (imm := o) (by omega_using [hoi]) fun s₂ u₂ =>
    wp_sll (sh := 9) (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => wp_sll (sh := 2) (by decide) fun s₅ u₅ =>
      wp_li (imm := 16) (by decide) fun s₆ u₆ => WP.block_nil ?_))
  obtain u₁ := Upd.write s .t0 (s.syms sqrtSym)
  obtain r₆ : Rest [.t0, .t1, .t2, .t3] s s₆ :=
    (((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain s6₆ : s₆.gpr .s6 = BitVec.ofNat 64 i := by rw [r₆.gpr _ (by decide)]; exact h6
  obtain t0₆ : s₆.gpr .t0 = T + BitVec.ofNat 64 (512 * (o + i)) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hsym, h6]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega_using [hoi]
  obtain t2₆ : (s₆.gpr .t2).toNat % 64 = 4 * (i % 16) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h6, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using [hi]
  obtain t3₆ : s₆.gpr .t3 = BitVec.ofNat 64 16 := u₆.gpr
  -- The digit's register, shifted.
  refine WP.seq (WP.mono (Q := fun s₇ => Upd s₆ s₇ .t2 (s.gpr (dreg i) >>> (4 * (i % 16)))) ?_ fun s₇ u₇ => ?_)
  · by_cases h16 : i < 16
    · refine WP.ite true (by
          show some (decide (s₆.gpr .s6 < s₆.gpr .t3)) = _
          rw [s6₆, t3₆, ltu_ofNat (by omega_using [hi]) (by decide), decide_eq_true h16]) (fun _ => ?_) (fun h => by cases h)
      refine WP.cons (exec_srlReg _ _ _ _) (WP.block_nil ?_)
      rw [t2₆, show dreg i = .s4 from ite_eq_left h16, ← r₆.gpr .s4 (by decide)]
      exact Upd.write _ _ _
    · refine WP.ite false (by
          show some (decide (s₆.gpr .s6 < s₆.gpr .t3)) = _
          rw [s6₆, t3₆, ltu_ofNat (by omega_using [hi]) (by decide), decide_eq_false h16]) (fun h => by cases h) (fun _ => ?_)
      refine WP.cons (exec_srlReg _ _ _ _) (WP.block_nil ?_)
      rw [t2₆, show dreg i = .s5 from ite_eq_right h16, ← r₆.gpr .s5 (by decide)]
      exact Upd.write _ _ _
  simp only [List.cons_append]
  refine wp_andi (by decide) fun s₈ u₈ => wp_sll (by decide) fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => ?_
  obtain ht2 : s₉.gpr .t2 = BitVec.ofNat 64 (32 * (k / 16 ^ i % 16)) := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, dreg_digit hk hi hK]
  obtain ht0 : s₁₀.gpr .t0 + BitVec.ofNat 64 0 = T + BitVec.ofNat 64 (32 * (16 * (o + i) + k / 16 ^ i % 16)) := by
    rw [u₁₀.gpr, ht2, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), t0₆,
      BitVec.add_zero, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega_using []
  obtain r₁₀ : Rest [.t0, .t1, .t2, .t3] s s₁₀ :=
    r₆.trans ((((u₇.rest (by decide)).trans (u₈.rest (by decide))).trans (u₉.rest (by decide))).trans
      (u₁₀.rest (by decide)))
  obtain hm₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
  obtain hT₁₀ : TabOk base T s₁₀ := hT.of_mem r₁₀.rd fun x _ => by rw [hm₁₀]
  refine WP.mono (entCopy_ok (hw.of_rest r₁₀) hT₁₀ (o := XS) (q := 0) hoi (Nat.mod_lt _ (by decide)) (by decide)
    (by decide) ht0) fun s' ⟨r', O', v'⟩ => ⟨r₁₀.trans (r'.mono (by decide)), by rw [← hm₁₀]; exact O', v'⟩

/-- `[y] = [y] T (o + i) dᵢ`, then `s6 = i + 1` and `t0 = n`. -/
theorem mulStep_ok {s : State} {base T : Addr} (hw : WsReg s base) (hT : TabOk base T s)
    (hsym : s.syms sqrtSym = T) {y o i k n : Nat} (hy : y < 100) (hyx : y ≠ XS) (hoi : o + i < 24)
    (hk : k < 16 ^ 24) (hK : KRegs k s) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hn : n < 2048) :
    WP isa (mulStep y o n) s fun s' => Ks [.s6] s s' ∧ s'.gpr .s6 = BitVec.ofNat 64 (i + 1) ∧
      s'.gpr .t0 = BitVec.ofNat 64 n ∧
      Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' y < W.p ∧
      toM W.p (2 ^ 256) (sv base s' y) = toM W.p (2 ^ 256) (sv base s y) * tbl224 (o + i) (k / 16 ^ i % 16) := by
  obtain hsl := sl_eq y
  rw [mulStep]
  refine WP.seq (WP.mono (lookup_ok hw hT hsym hoi hk hK h6) fun s₁ ⟨r₁, O₁, v₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  obtain ey : sv base s₁ y = sv base s y := O₁.wordsVal (by have := slot_apart hyx; omega_using [this]) (by omega_using [hy, hsl])
  refine WP.seq (WP.mono (mulCall_ok field_ok hw₁ (o := p224.sl y) (a := p224.sl y) (b := p224.sl XS)
    (by show p224.sl y + 8 * 4 ≤ 3840; omega_using [hy, hsl]) (by show p224.sl y + 8 * 4 ≤ 3840; omega_using [hy, hsl]) (by decide) (by omega_using [hy, hsl])
    (by omega_using [hy, hsl]) (by decide)
    (by show sv base s₁ XS < _; rw [v₁]; exact montT_lt _ _)) fun s₂ ⟨C₂, lt₂, e₂⟩ => ?_)
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_li (imm := n) hn fun s₄ u₄ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine ⟨((Ks.of_rest (rs := [.s6]) r₁).trans (Ks.of_kp C₂.kp)).trans
      ((Ks.of_rest (u₃.rest (ws := [.s6]) (by decide))).trans (Ks.of_rest (u₄.rest (ws := [.t0]) (by decide)))),
    by rw [u₄.other _ (by decide), u₃.gpr, C₂.kp.gpr _ (by decide), r₁.gpr _ (by decide), h6, BitVec.ofNat_add_ofNat],
    u₄.gpr, by rw [m₄]; exact O₁.unch.trans C₂.mem, by show wordsVal _ _ _ _ < _; rw [m₄]; exact lt₂, ?_⟩
  show toM W.p (2 ^ 256) (wordsVal s₄.mem base (p224.sl y) 4) = _
  rw [m₄]
  refine (toM_mul unit e₂).trans ?_
  show toM W.p (2 ^ 256) (sv base s₁ y) * toM W.p (2 ^ 256) (sv base s₁ XS) = _
  rw [ey, v₁, toM_montT]

theorem w3_le {y : Nat} (hy : y < 100) :
    ∀ w ∈ [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)], w.1 + w.2 ≤ 8192 := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · decide
  · show p224.sl y + 32 ≤ 8192; rw [sl_eq]; omega_using [hy]
  · decide

/-- What the products' loop keeps after `i` steps. -/
structure MInv (base T : Addr) (y o k : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  ws : WsReg s base
  tab : TabOk base T s
  sym : s.syms = s₀.syms
  ks : Ks [.s6] s₀ s
  unch : Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s₀.mem s.mem
  lt : sv base s y < W.p
  val : toM W.p (2 ^ 256) (sv base s y) = tacc tbl224 o k (toM W.p (2 ^ 256) (sv base s₀ y)) i
  cnt : s.gpr .s6 = BitVec.ofNat 64 i

/-- `[y] = [y] Π_(i<n) T (o + i) dᵢ`: `tacc`. -/
theorem muls_ok {base T : Addr} {y o k : Nat} (hy : y < 100) (hyx : y ≠ XS) (hk : k < 16 ^ 24) :
    ∀ n, o + n ≤ 24 → ∀ {s : State}, WsReg s base → TabOk base T s → s.syms sqrtSym = T → KRegs k s →
      sv base s y < W.p →
      WP isa (muls y o n) s fun s' => WsReg s' base ∧ TabOk base T s' ∧ s'.syms = s.syms ∧ Ks [.s6] s s' ∧
        Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' y < W.p ∧
        toM W.p (2 ^ 256) (sv base s' y) = tacc tbl224 o k (toM W.p (2 ^ 256) (sv base s y)) n
  | 0, _, _, hw, hT, _, _, hlt => WP.block_nil ⟨hw, hT, rfl, Ks.refl _ _, Unch.refl _ _ _, hlt, rfl⟩
  | n + 1, hn, s, hw, hT, hsym, hK, hlt => by
    rw [muls]
    refine WP.seq (WP.syms (Q := fun s₁ => Upd s s₁ .s6 (BitVec.ofNat 64 0))
      (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil u₁) fun s₁ u₁ sy₁ => ?_)
    obtain r₁ := u₁.rest (ws := [.s6]) (by decide)
    obtain I₀ : MInv base T y o k s 0 s₁ :=
      ⟨⟨by rw [r₁.gpr _ (by decide)]; exact hw.s0, by rw [r₁.wr]; exact hw.wr, hw.nowrap, hw.al⟩,
        hT.of_mem r₁.rd fun x _ => by rw [u₁.mem], sy₁, Ks.of_rest r₁, by rw [u₁.mem]; exact Unch.refl _ _ _,
        by show wordsVal _ _ _ _ < _; rw [u₁.mem]; exact hlt, by show toM _ _ (wordsVal _ _ _ _) = _; rw [u₁.mem]; rfl,
        u₁.gpr⟩
    refine WP.loop (M := isa) (c := .ne .s6 .t0)
      (Q := fun s' => WsReg s' base ∧ TabOk base T s' ∧ s'.syms = s.syms ∧ Ks [.s6] s s' ∧
        Unch base [(p224.sl XS, 32), (p224.sl y, 32), (own 4, 256)] s.mem s'.mem ∧ sv base s' y < W.p ∧
        toM W.p (2 ^ 256) (sv base s' y) = tacc tbl224 o k (toM W.p (2 ^ 256) (sv base s y)) (n + 1))
      (fun m t => ∃ i, m = n + 1 - i ∧ i < n + 1 ∧ MInv base T y o k s i t) ?_ (n + 1) s₁
      ⟨0, by omega_using [], by omega_using [], I₀⟩
    rintro _ t ⟨i, rfl, hi, I⟩
    refine WP.syms (mulStep_ok I.ws I.tab (by rw [I.sym]; exact hsym) hy hyx (o := o) (i := i) (n := n + 1)
      (by omega_using [hn, hi]) hk (hK.of_ks I.ks) I.cnt (by omega_using [hn])) fun t' ⟨K', c', z', U', lt', v'⟩ sy' => ?_
    obtain I' : MInv base T y o k s (i + 1) t' :=
      ⟨wsReg_of_ks I.ws K', I.tab.of_unch K'.rd (w3_le hy) U', by rw [sy', I.sym], I.ks.trans K',
        (I.unch.trans U').mono fun w hw => (List.mem_append.mp hw).elim id id, lt', by rw [v', I.val, tacc], c'⟩
    obtain e := eval_ne_count (i := i + 1) (n := n + 1) (by omega_using [hn, hi]) (by omega_using [hn]) c' z'
    by_cases he : i + 1 = n + 1
    · left
      exact ⟨by rw [e]; exact congrArg some (decide_eq_false fun h => h he), I'.ws, I'.tab, I'.sym, I'.ks, I'.unch,
        I'.lt, he ▸ I'.val⟩
    · right
      exact ⟨by rw [e]; exact congrArg some (decide_eq_true he), n + 1 - (i + 1), by omega_using [hi, he], i + 1, rfl,
        by omega_using [hi, he], I'⟩

/-! ## The comparisons -/

theorem mask_and_imm (c : Bool) (v : Nat) :
    maskOf c &&& BitVec.ofNat 64 v = BitVec.ofNat 64 (if c then v else 0) := by
  cases c
  · simp [maskOf]
  · show BitVec.allOnes 64 &&& _ = _; exact BitVec.allOnes_and

section
variable {s : State} {base : Addr} {is : List Instr} {Q : State → Prop}

/-- `ld t3, q(t0)` of the working space's word at `src`, then `sd t3` to `dst`. -/
theorem wsWord_ok (hw : WsReg s base) {src dst q : Nat} (hq : q < 2048)
    (h0 : s.gpr .t0 + BitVec.ofNat 64 q = off base src) (hsrc : src + 8 ≤ 8192) (hs8 : src % 8 = 0)
    (hdst : dst < 4095) (hd8 : dst % 8 = 0)
    (k : ∀ s', Rest [.t3] s s' → s'.mem = s.mem.writeW (off base dst) (word s.mem base src) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.load .d .t3 .t0 q :: (sdAt .t3 wb dst ++ is))) s Q := by
  have hn := hw.nowrap
  have ha := hw.al
  refine wp_ld hq h0 (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hn, ha, hs8, hsrc])
    ⟨_, List.mem_append_right _ hw.wr, Offset.contains_base base (by omega_using [hsrc]) (by omega_using [hsrc])⟩ fun s₁ u₁ => ?_
  obtain r₁ := u₁.rest (ws := [.t3]) (by decide)
  refine sdAt_ws (hw.of_rest r₁) (by decide) hdst hd8 fun s₂ u₂ => k s₂ (r₁.trans (u₂.rest _)) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem]

/-- Four words, equal one by one. -/
theorem wordsVal4_congr {m m' : Mem} {base : Addr} {a b : Nat}
    (h : ∀ w < 4, word m' base (a + 8 * w) = word m base (b + 8 * w)) :
    wordsVal m' base a 4 = wordsVal m base b 4 := by
  obtain e0 := h 0 (by decide)
  obtain e1 := h 1 (by decide)
  obtain e2 := h 2 (by decide)
  obtain e3 := h 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at e0 e1 e2 e3
  simp only [wordsVal, Nat.add_assoc, Nat.reduceAdd]
  rw [e0, e1, e2, e3]

/-- The four words at `t0`, the working space's at `src`, to slot `o`. -/
theorem wsCopy_ok (hw : WsReg s base) {o src : Nat} (ho : o < 100) (hsrc : src + 32 ≤ 3840) (hs8 : src % 8 = 0)
    (hsep : src + 32 ≤ p224.sl o ∨ p224.sl o + 32 ≤ src) (h0 : s.gpr .t0 = off base src) :
    WP isa (.block (entCopy o 0)) s fun s' => Rest [.t3] s s' ∧
      Outside base (p224.sl o) 32 s.mem s'.mem ∧ sv base s' o = wordsVal s.mem base src 4 := by
  obtain hsl := sl_eq o
  have hn := hw.nowrap
  obtain h0' : ∀ w < 4, s.gpr .t0 + BitVec.ofNat 64 (0 + 8 * w) = off base (src + 8 * w) := fun w _ => by
    rw [h0, Nat.zero_add]; simp only [off]; rw [Offset.add_add]
  obtain O : ∀ (m : Mem) (k : Nat) (v : BitVec 64), k ≤ 24 →
      Outside base (p224.sl o) 32 m (m.writeW (off base (p224.sl o + k)) v) := fun m k v hk =>
    (writeW_outside _ _ _ (by omega_using [ho, hsl, hk])).mono (Nat.le_add_right _ _) (by omega_using [hk])
  obtain W : ∀ (m : Mem) (k d : Nat) (v : BitVec 64), d + 8 ≤ p224.sl o + k ∨ p224.sl o + k + 8 ≤ d →
      d + 8 ≤ 2 ^ 64 → k ≤ 24 → word (m.writeW (off base (p224.sl o + k)) v) base d = word m base d :=
    fun m k d v hd hd' hk => (writeW_outside _ _ _ (by omega_using [ho, hsl, hk])).word hd hd'
  obtain wsrc : ∀ {m m' : Mem}, Outside base (p224.sl o) 32 m m' → ∀ w < 4, word m' base (src + 8 * w) = word m base (src + 8 * w) :=
    fun h w hw' => h.word (by omega_using [hsep, hw']) (by omega_using [hsrc, hw'])
  rw [entCopy]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wsWord_ok hw (src := src + 8 * 0) (dst := p224.sl o + 0) (by decide) (by simpa using h0' 0 (by decide))
    (by omega_using [hsrc]) (by omega_using [hs8]) (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₁ r₁ m₁ => ?_
  obtain O₁ : Outside base (p224.sl o) 32 s.mem s₁.mem := by rw [m₁]; exact O _ _ _ (by decide)
  refine wsWord_ok (hw.of_rest r₁) (src := src + 8 * 1) (dst := p224.sl o + 8) (by decide)
    (by rw [r₁.gpr _ (by decide)]; exact h0' 1 (by decide)) (by omega_using [hsrc]) (by omega_using [hs8])
    (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₂ r₂ m₂ => ?_
  obtain O₂ : Outside base (p224.sl o) 32 s₁.mem s₂.mem := by rw [m₂]; exact O _ _ _ (by decide)
  refine wsWord_ok ((hw.of_rest r₁).of_rest r₂) (src := src + 8 * 2) (dst := p224.sl o + 16) (by decide)
    (by rw [r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 2 (by decide)) (by omega_using [hsrc])
    (by omega_using [hs8]) (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₃ r₃ m₃ => ?_
  obtain O₃ : Outside base (p224.sl o) 32 s₂.mem s₃.mem := by rw [m₃]; exact O _ _ _ (by decide)
  rw [← List.append_nil (sdAt .t3 wb (p224.sl o + 24))]
  refine wsWord_ok (((hw.of_rest r₁).of_rest r₂).of_rest r₃) (src := src + 8 * 3) (dst := p224.sl o + 24) (by decide)
    (by rw [r₃.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide)]; exact h0' 3 (by decide))
    (by omega_using [hsrc]) (by omega_using [hs8]) (by omega_using [ho, hsl]) (by omega_using [hsl]) fun s₄ r₄ m₄ =>
      WP.block_nil ⟨r₁.trans (r₂.trans (r₃.trans r₄)), ?_, ?_⟩
  · obtain O₄ : Outside base (p224.sl o) 32 s₃.mem s₄.mem := by rw [m₄]; exact O _ _ _ (by decide)
    exact O₁.trans (O₂.trans (O₃.trans O₄))
  · obtain hd : p224.sl o + 32 ≤ 2 ^ 64 := by omega_using [ho, hsl]
    refine wordsVal4_congr fun w hw' => ?_
    rcases (by omega_using [hw'] : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with rfl | rfl | rfl | rfl
    · rw [m₄, W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₃,
        W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₂,
        W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₁, Nat.mul_zero, Nat.add_zero,
        show p224.sl o = p224.sl o + 0 from rfl, word_writeW_self]
    · rw [m₄, W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₃,
        W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₂, word_writeW_self]
      exact wsrc O₁ 1 (by decide)
    · rw [m₄, W _ _ _ _ (by omega_using []) (by omega_using [hd]) (by decide), m₃, word_writeW_self]
      exact wsrc (O₁.trans O₂) 2 (by decide)
    · rw [m₄, word_writeW_self]
      exact wsrc (O₁.trans (O₂.trans O₃)) 3 (by decide)

end

theorem gs_lt {e : Nat} (he : e < 16) : p224.sl (GS e) + 32 ≤ 3840 := by rw [sl_eq]; simp only [GS]; omega_using [he]

/-- `s6 += (16 - e) mod 16` if `y = g^e`, for `e` in `s1`; then `s1 = e + 1`, `t0 = 16`. -/
theorem cmpStep_ok {s : State} {base : Addr} (hw : WsReg s base) {e v : Nat} (he : e < 16)
    (hY : sv base s YS < W.p) (hG : sv base s (GS e) < W.p) (h1 : s.gpr .s1 = BitVec.ofNat 64 e)
    (h6 : s.gpr .s6 = BitVec.ofNat 64 v) :
    WP isa cmpStep s fun s' => WsReg s' base ∧ Ks [.s1, .s6] s s' ∧
      Unch base [(p224.sl XS, 32), (p224.sl TD, 32), (own 4, 256)] s.mem s'.mem ∧
      s'.gpr .s1 = BitVec.ofNat 64 (e + 1) ∧ s'.gpr .t0 = BitVec.ofNat 64 16 ∧
      s'.gpr .s6 = BitVec.ofNat 64 (v + if toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e))
        then (16 - e) % 16 else 0) := by
  obtain hp0 : 0 < W.p := by decide
  obtain hn := hw.nowrap
  rw [cmpStep, gcopy, show addAt .t0 .t0 (p224.sl (GS 0)) = [.addi .t0 .t0 2047, .addi .t0 .t0 545] from rfl]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_sll (sh := 5) (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addi (imm := 2047) (by decide)
    fun s₃ u₃ => wp_addi (imm := 545) (by decide) fun s₄ u₄ => ?_)
  obtain r₄ : Rest [.t0] s s₄ := (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
    (u₄.rest (by decide))
  obtain t0₄ : s₄.gpr .t0 = off base (p224.sl (GS e)) := by
    obtain hsh : BitVec.ofNat 64 e <<< 5 = BitVec.ofNat 64 (32 * e) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using [he]
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h1, hw.s0, hsh, sl_eq]
    simp only [off, GS]
    rw [BitVec.add_comm (BitVec.ofNat 64 (32 * e)) base, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
    congr 2; omega_using []
  obtain hw₄ := hw.of_rest r₄
  refine WP.mono (wsCopy_ok hw₄ (o := XS) (src := p224.sl (GS e)) (by decide) (gs_lt he)
    (by rw [sl_eq]; omega_using []) (by rw [sl_eq, sl_eq]; simp only [GS, XS]; omega_using []) t0₄) fun s₅ ⟨r₅, O₅, v₅⟩ => ?_
  obtain hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain v₅' : sv base s₅ XS = sv base s (GS e) := by rw [v₅, hm₄]
  obtain eY : sv base s₅ YS = sv base s YS := by
    show wordsVal s₅.mem base (p224.sl YS) 4 = wordsVal s.mem base (p224.sl YS) 4
    rw [O₅.wordsVal (d := p224.sl YS) (k := 4) (by rw [sl_eq, sl_eq]; decide) (by rw [sl_eq]; decide), hm₄]
  obtain hw₅ := hw₄.of_rest r₅
  refine WP.seq (WP.mono (subCall_ok field_ok hw₅ (o := p224.sl TD) (a := p224.sl YS) (b := p224.sl XS)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show sv base s₅ YS < W.p; rw [eY]; exact hY) (by show sv base s₅ XS < W.p; rw [v₅']; exact hG))
    fun s₆ ⟨C₆, e₆⟩ => ?_)
  have e₆' : sv base s₆ TD = (sv base s YS + W.p - sv base s (GS e)) % W.p := by
    rw [← eY, ← v₅']; exact e₆
  obtain hw₆ := hw₅.of_kp C₆.kp
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 4) (a := p224.sl TD) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, g₇⟩ => ?_)
  refine wp_li (imm := 16) (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ => wp_andi (by decide) fun s₁₀ u₁₀ => ?_
  refine WP.cons exec_logic ?_
  obtain u₁₁ := Upd.write s₁₀ .a7 (s₁₀.gpr .a7 &&& s₁₀.gpr .t0)
  refine wp_add fun s₁₂ u₁₂ => wp_addi (imm := 1) (by decide) fun s₁₃ u₁₃ =>
    wp_li (imm := 16) (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
  obtain hz : wordsVal s₆.mem base (p224.sl TD) 4 = 0 ↔
      toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e)) := by
    obtain hlt : sv base s₆ TD < W.p := by rw [e₆']; exact Nat.mod_lt _ hp0
    rw [← toM_eq_zero_iff unit hlt]
    show toM W.p (2 ^ 256) (sv base s₆ TD) = 0 ↔ _
    rw [e₆', toM_sub (by omega_using [hG])]
    constructor <;> intro h <;> grind
  obtain s1₆ : s₆.gpr .s1 = BitVec.ofNat 64 e := by
    rw [C₆.kp.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), h1]
  obtain s6₆ : s₆.gpr .s6 = BitVec.ofNat 64 v := by
    rw [C₆.kp.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), h6]
  obtain t0₁₀ : s₁₀.gpr .t0 = BitVec.ofNat 64 ((16 - e) % 16) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₈.other _ (by decide), r₇.gpr _ (by decide), s1₆]
    exact (by decide : ∀ e < 16, (BitVec.ofNat 64 16 - BitVec.ofNat 64 e) &&& BitVec.ofInt 64 15 =
      BitVec.ofNat 64 ((16 - e) % 16)) e he
  obtain a7₁₀ : s₁₀.gpr .a7 = maskOf (decide (wordsVal s₆.mem base (p224.sl TD) 4 = 0)) := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), g₇]
  obtain K : Ks [.s1, .s6] s s₁₄ :=
    (((Ks.of_rest r₄).trans (Ks.of_rest r₅)).trans (Ks.of_kp C₆.kp)).trans
      ((((((((Ks.of_rest r₇).trans (Ks.of_rest (u₈.rest (ws := [.t0]) (by decide)))).trans
        (Ks.of_rest (u₉.rest (ws := [.t0]) (by decide)))).trans (Ks.of_rest (u₁₀.rest (ws := [.t0]) (by decide)))).trans
        (Ks.of_rest (u₁₁.rest (ws := [.a7]) (by decide)))).trans (Ks.of_rest (u₁₂.rest (ws := [.s6]) (by decide)))).trans
        (Ks.of_rest (u₁₃.rest (ws := [.s1]) (by decide)))).trans (Ks.of_rest (u₁₄.rest (ws := [.t0]) (by decide))))
  obtain m₁₄ : s₁₄.mem = s₆.mem := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇]
  refine ⟨wsReg_of_ks hw K, K, ?_, ?_, u₁₄.gpr, ?_⟩
  · rw [m₁₄, ← hm₄]; exact (O₅.unch.trans C₆.mem).cover (by decide)
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), r₇.gpr _ (by decide), s1₆, BitVec.ofNat_add_ofNat]
  · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₁.gpr,
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), r₇.gpr _ (by decide), s6₆,
      a7₁₀, t0₁₀, mask_and_imm, BitVec.ofNat_add_ofNat]
    refine congrArg (fun x => BitVec.ofNat 64 (v + x)) ?_
    by_cases h : toM W.p (2 ^ 256) (sv base s YS) = toM W.p (2 ^ 256) (sv base s (GS e))
    · rw [ite_eq_left h, decide_eq_true (hz.mpr h)]; rfl
    · rw [ite_eq_right h, decide_eq_false (fun h' => h (hz.mp h'))]; rfl

theorem gs_apart {e : Nat} (he : e < 16) :
    ∀ w ∈ [(p224.sl XS, 32), (p224.sl TD, 32), (own 4, 256)], p224.sl (GS e) + 32 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl (GS e) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · right; show p224.sl XS + 32 ≤ p224.sl (GS e); rw [sl_eq, sl_eq]; simp only [GS, XS]; omega_using []
  · right; show p224.sl TD + 32 ≤ p224.sl (GS e); rw [sl_eq, sl_eq]; simp only [GS, TD]; omega_using []
  · left; exact gs_lt he

/-- The comparisons with `g^e`, `e < 16`: `digAcc`. -/
theorem cmps_ok {base : Addr} {G : Nat → Fe W} {s : State} (hw : WsReg s base) (hY : sv base s YS < W.p)
    (hG : ∀ e < 16, sv base s (GS e) < W.p ∧ toM W.p (2 ^ 256) (sv base s (GS e)) = G e)
    (h6 : s.gpr .s6 = 0) :
    WP isa cmps s fun s' => WsReg s' base ∧ Ks [.s1, .s6] s s' ∧
      Unch base [(p224.sl XS, 32), (p224.sl TD, 32), (own 4, 256)] s.mem s'.mem ∧
      s'.gpr .s6 = BitVec.ofNat 64 (digAcc G (toM W.p (2 ^ 256) (sv base s YS)) 16) := by
  rw [cmps]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain r₁ := u₁.rest (ws := [.s1]) (by decide)
  let J : Nat → State → Prop := fun e t => WsReg t base ∧ Ks [.s1, .s6] s t ∧
    Unch base [(p224.sl XS, 32), (p224.sl TD, 32), (own 4, 256)] s.mem t.mem ∧ t.gpr .s1 = BitVec.ofNat 64 e ∧
    t.gpr .s6 = BitVec.ofNat 64 (digAcc G (toM W.p (2 ^ 256) (sv base s YS)) e)
  obtain J₀ : J 0 s₁ := ⟨wsReg_of_ks hw (Ks.of_rest (rs := [.s1]) r₁), Ks.of_rest r₁, by rw [u₁.mem]; exact Unch.refl _ _ _,
    u₁.gpr, by rw [r₁.gpr _ (by decide), h6]; rfl⟩
  refine WP.loop (M := isa) (c := .ne .s1 .t0) (fun m t => ∃ e, m = 16 - e ∧ e < 16 ∧ J e t) ?_ 16 s₁
    ⟨0, rfl, by decide, J₀⟩
  rintro _ t ⟨e, rfl, he, hwt, Kt, Ut, c1, c6⟩
  obtain eY : sv base t YS = sv base s YS := sv_unch Ut YS (by decide) (by decide)
  obtain eG : sv base t (GS e) = sv base s (GS e) := sv_unch Ut (GS e) (gs_apart he) (by simp only [GS]; omega_using [he])
  refine WP.mono (cmpStep_ok hwt he (by rw [eY]; exact hY) (by rw [eG]; exact (hG e he).1) c1 c6)
    fun t' ⟨hw', K', U', c1', z', c6'⟩ => ?_
  obtain J' : J (e + 1) t' := ⟨hw', Kt.trans K', (Ut.trans U').cover (by decide), c1', by
    rw [c6', eY, eG, (hG e he).2, digAcc]⟩
  obtain ev := eval_ne_count (r := .s1) (i := e + 1) (n := 16) (by omega_using [he]) (by decide) c1' z'
  by_cases hl : e + 1 = 16
  · left; exact ⟨by rw [ev]; exact congrArg some (decide_eq_false fun h => h hl), J'.1, J'.2.1, J'.2.2.1, hl ▸ J'.2.2.2.2⟩
  · right; exact ⟨by rw [ev]; exact congrArg some (decide_eq_true hl), 16 - (e + 1), by omega_using [he, hl], e + 1, rfl,
      by omega_using [he, hl], J'⟩

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
  obtain ho : own 4 = 3840 := by decide
  rcases hw with rfl | rfl | rfl | rfl <;> simp only [sl_eq, YS, XS, TD, TR, ho] at hi ⊢ <;> omega_using [hi]

theorem FSt.of_unch {a : Fe W} {base : Addr} {s s' : State} (h : FSt a base s) (U : Unch base dW s.mem s'.mem) :
    FSt a base s' where
  ss m hm := by
    obtain e : sv base s' (SS m) = sv base s (SS m) :=
      sv_unch U (SS m) (dW_apart (.inr (by simp only [SS]; omega_using [hm]))) (by simp only [SS]; omega_using [hm])
    rw [e]; exact h.ss m hm
  gs e he := by
    obtain e' : sv base s' (GS e) = sv base s (GS e) :=
      sv_unch U (GS e) (dW_apart (.inr (by simp only [GS]; omega_using [he]))) (by simp only [GS]; omega_using [he])
    rw [e']; exact h.gs e he
  tr := by
    obtain e : sv base s' TR = sv base s TR := sv_unch U TR (dW_apart (.inl rfl)) (by decide)
    rw [e]; exact h.tr

/-- After `j` digits, from the state `s₀` the digits start from. -/
structure DSt (a : Fe W) (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  tab : TabOk base T s
  sym : s.syms sqrtSym = T
  ks : Ks [.s1, .s4, .s5, .s6] s₀ s
  unch : Unch base dW s₀.mem s.mem
  k : KRegs (kA a j) s

/-- `a ||| d 16^c = a + d 16^c` for `a < 16^c`. -/
theorem or_digit {a d c : Nat} (ha : a < 16 ^ c) (hd : d < 16) (hc : c < 16) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (d * 16 ^ c) = BitVec.ofNat 64 (a + d * 16 ^ c) := by
  obtain h16 : 16 ^ c = 2 ^ (4 * c) := by rw [Nat.pow_mul]
  obtain hc' : 16 ^ c * 16 ≤ 2 ^ 64 := by
    rw [← Nat.pow_succ]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega_using [hc] : c + 1 ≤ 16)) (by decide)
  obtain hdl := Nat.mul_le_mul_right (16 ^ c) (show d ≤ 15 by omega_using [hd])
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [ha, hc']),
    Nat.mod_eq_of_lt (by omega_using [hc', hdl]), Nat.mod_eq_of_lt (by omega_using [ha, hc', hdl]), Nat.or_comm, Nat.mul_comm d, h16,
    ← Nat.two_pow_add_eq_or_of_lt (by rw [← h16]; exact ha), Nat.add_comm]

/-- The digit `D mod 16` into its register. -/
theorem dfinal_ok {s : State} {j k D : Nat} (hj : j < 24) (hk : k < 16 ^ j) (h6 : s.gpr .s6 = BitVec.ofNat 64 D)
    (hK : KRegs k s) :
    WP isa (.block [.logicImm .and .s6 .s6 15, .shift .sll .d .s6 .s6 (4 * (j % 16)),
      .logic .or (dreg j) (dreg j) .s6]) s fun s' =>
      Rest [.s4, .s5, .s6] s s' ∧ s'.mem = s.mem ∧ KRegs (k + D % 16 * 16 ^ j) s' := by
  refine wp_andi (by decide) fun s₁ u₁ => wp_sll (by omega_using []) fun s₂ u₂ => wp_or fun s₃ u₃ => WP.block_nil ?_
  obtain hd : D % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain v₂ : s₂.gpr .s6 = BitVec.ofNat 64 (D % 16 * 16 ^ (j % 16)) := by
    rw [u₂.gpr, u₁.gpr, h6]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (BitVec.ofInt 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
      show 2 ^ (4 * (j % 16)) = 16 ^ (j % 16) by rw [Nat.pow_mul], show D % 2 ^ 64 % 2 ^ 4 = D % 16 by omega_using []]
  obtain hdr : ∀ r, r = .s4 ∨ r = .s5 → r ≠ dreg j → s₃.gpr r = s.gpr r := fun r hr hn => by
    rw [u₃.other _ hn, u₂.other _ (by rcases hr with rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl <;> decide)]
  obtain hd3 : s₃.gpr (dreg j) = s.gpr (dreg j) ||| BitVec.ofNat 64 (D % 16 * 16 ^ (j % 16)) := by
    rw [u₃.gpr, v₂, u₂.other _ (by unfold dreg; split <;> decide), u₁.other _ (by unfold dreg; split <;> decide)]
  refine ⟨((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by unfold dreg; split <;> decide)),
    by rw [u₃.mem, u₂.mem, u₁.mem], ?_⟩
  obtain hdl := Nat.mul_le_mul_right (16 ^ j) (show D % 16 ≤ 15 by omega_using [])
  by_cases h16 : j < 16
  · have hj16 : 16 ^ j * 16 ≤ 2 ^ 64 := by
      rw [← Nat.pow_succ]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show j + 1 ≤ 16 by omega_using [h16])) (by decide)
    obtain e4 : dreg j = .s4 := ite_eq_left h16
    rw [e4, hK.1, Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt (by omega_using [hk, hj16]), or_digit hk hd h16] at hd3
    refine ⟨by rw [hd3, Nat.mod_eq_of_lt (show k + D % 16 * 16 ^ j < 2 ^ 64 by omega_using [hk, hdl, hj16])], ?_⟩
    rw [hdr .s5 (.inr rfl) (by rw [e4]; decide), hK.2, Nat.div_eq_of_lt (by omega_using [hk, hj16]), Nat.div_eq_of_lt (by omega_using [hk, hdl, hj16])]
  · have e5 : dreg j = .s5 := ite_eq_right h16
    obtain hp : 16 ^ j = 2 ^ 64 * 16 ^ (j - 16) := by
      rw [show (2 : Nat) ^ 64 = 16 ^ 16 from rfl, ← Nat.pow_add]; congr 1; omega_using [h16]
    obtain hkh : k / 2 ^ 64 < 16 ^ (j - 16) := by
      rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm, ← hp]; exact hk
    rw [e5, hK.2, show j % 16 = j - 16 by omega_using [hj, h16], or_digit hkh hd (by omega_using [hj])] at hd3
    refine ⟨?_, ?_⟩
    · rw [hdr .s4 (.inl rfl) (by rw [e5]; decide), hK.1, hp, Nat.mul_left_comm, Nat.add_mul_mod_self_left]
    · rw [hd3, hp, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (by decide)]

/-- `y = s_(23-j)`. -/
theorem dstart_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 24) :
    WP isa (.block (copy 4 (p224.sl YS) (p224.sl (SS (23 - j))))) s fun s' =>
      Rest [.t0] s s' ∧ Outside base (p224.sl YS) 32 s.mem s'.mem ∧ sv base s' YS = sv base s (SS (23 - j)) :=
  WP.mono (copy_ok 4 hw (o := p224.sl YS) (a := p224.sl (SS (23 - j))) (by decide)
    (by rw [sl_eq]; omega) (by decide) (by rw [sl_eq]; simp only [SS]; omega)
    (Or.inl (by rw [sl_eq, sl_eq]; simp only [SS, YS]; omega))) fun _ ⟨v₁, r₁, O₁⟩ => ⟨r₁, O₁, v₁⟩

/-- Digit `j`. -/
theorem digit_ok {a : Fe W} {base T : Addr} {s₀ s : State} {j : Nat} (hj : j < 24) (F : FSt a base s₀)
    (D : DSt a base T s₀ s j) : WP isa (digit j) s fun s' => DSt a base T s₀ s' (j + 1) := by
  obtain F' := F.of_unch D.unch
  obtain hk := VG.Proof.Weierstrass.kGo_lt tbl224 (sOf a) 24 j
  rw [digit]
  refine WP.seq (WP.syms (dstart_ok D.ws hj) fun s₁ ⟨r₁, O₁, v₁⟩ sy₁ => ?_)
  obtain hw₁ := wsReg_of_ks D.ws (Ks.of_rest (rs := []) r₁)
  obtain hT₁ := D.tab.of_outside r₁.rd (by decide) O₁
  obtain hK₁ : KRegs (kA a j) s₁ := ⟨by rw [r₁.gpr _ (by decide)]; exact D.k.1, by rw [r₁.gpr _ (by decide)]; exact D.k.2⟩
  refine WP.seq (WP.mono (muls_ok (y := YS) (o := 23 - j) (k := kA a j) (by decide) (by decide) (kA_lt a (by omega_using [hj]))
    j (by omega_using [hj]) hw₁ hT₁ (by rw [sy₁]; exact D.sym) hK₁ (by rw [v₁]; exact (F'.ss _ (by omega_using [])).1))
    fun s₂ ⟨hw₂, hT₂, sy₂, K₂, U₂, lt₂, v₂⟩ => ?_)
  refine WP.seq (WP.syms (Q := fun s₂' => Upd s₂ s₂' .s6 (BitVec.ofNat 64 0))
    (wp_li (imm := 0) (by decide) fun s₂' u₂' => WP.block_nil u₂') fun s₂' u₂' sy₂' => ?_)
  obtain r₂' := u₂'.rest (ws := [.s6]) (by decide)
  obtain hw₂' := wsReg_of_ks hw₂ (Ks.of_rest (rs := [.s6]) r₂')
  obtain U₀₂ : Unch base dW s.mem s₂'.mem := by
    rw [u₂'.mem]; exact (O₁.unch.trans U₂).cover (by decide)
  obtain hG₂ : ∀ e < 16, sv base s₂' (GS e) < W.p ∧ toM W.p (2 ^ 256) (sv base s₂' (GS e)) = tbl224 23 e :=
    (F'.of_unch U₀₂).gs
  obtain lt₂' : sv base s₂' YS < W.p := by show wordsVal _ _ _ _ < _; rw [u₂'.mem]; exact lt₂
  refine WP.seq (WP.syms (cmps_ok (G := tbl224 23) hw₂' lt₂' hG₂ (by rw [u₂'.gpr]; rfl)) fun s₃ ⟨hw₃, K₃, U₃, v₃⟩ sy₃ => ?_)
  obtain K₂' : Ks [.s1, .s6] s₁ s₂' := (K₂.trans (Ks.of_rest (rs := [.s6]) r₂')).mono
  obtain K₂₃ : Ks [.s1, .s6] s₁ s₃ := K₂'.trans K₃
  refine WP.syms (dfinal_ok hj hk v₃ (hK₁.of_ks K₂₃)) fun s₄ ⟨r₄, m₄, k₄⟩ sy₄ => ?_
  obtain hy₂ : toM W.p (2 ^ 256) (sv base s₂' YS) = tacc tbl224 (23 - j) (kA a j) (sOf a (23 - j)) j := by
    show toM _ _ (wordsVal _ _ _ _) = _
    rw [u₂'.mem]; show toM _ _ (sv base s₂ YS) = _
    rw [v₂, v₁, (F'.ss _ (by omega_using [])).2]
  refine ⟨wsReg_of_ks hw₃ (Ks.of_rest (rs := [.s4, .s5, .s6]) r₄), ((hT₂.of_mem r₂'.rd fun x _ => by rw [u₂'.mem]).of_unch
      K₃.rd (by decide) U₃).of_mem r₄.rd (fun x _ => by rw [m₄]), by rw [sy₄, sy₃, sy₂', sy₂, sy₁]; exact D.sym,
    D.ks.trans (((Ks.of_rest (rs := []) r₁).mono.trans K₂₃.mono).trans
      (Ks.of_rest (rs := [.s4, .s5, .s6]) r₄).mono),
    (D.unch.trans (U₀₂.trans (by rw [m₄]; exact U₃))).cover (by decide), ?_⟩
  rw [hy₂] at k₄
  exact k₄

/-- The digits `0 … j - 1`. -/
theorem digits_ok {a : Fe W} {base T : Addr} {s₀ : State} (F : FSt a base s₀) :
    ∀ j, j ≤ 24 → ∀ {s : State}, DSt a base T s₀ s 0 → WP isa (digits j) s fun s' => DSt a base T s₀ s' j
  | 0, _, _, D => WP.block_nil D
  | j + 1, hj, _, D => by
    rw [digits]
    exact WP.seq (WP.mono (digits_ok F j (by omega_using [hj]) D) fun _ D' => digit_ok (by omega_using [hj]) F D')

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
      Nat.mod_eq_of_lt (show k / 2 ^ 64 < 2 ^ 64 by omega_using [hk])]
    rw [show k / 2 ^ 64 * 2 ^ 63 % 2 ^ 64 = 2 ^ 63 * (k / 2 ^ 64 % 2) by omega_using [], Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (show k % 2 ^ 64 / 2 ^ 1 < 2 ^ 63 by omega_using [])]
    omega_using []
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hK.2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have hk' : k < 2 ^ 96 := hk
    omega_using [hk]

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
    WP isa rootMul s fun s' => WsReg s' base ∧ TabOk base T s' ∧ s'.syms = s.syms ∧ Ks [.s4, .s5, .s6] s s' ∧
      Unch base [(p224.sl ACC, 32), (p224.sl XS, 32), (p224.sl ACC, 32), (own 4, 256)] s.mem s'.mem ∧
      sv base s' ACC < W.p ∧ toM W.p (2 ^ 256) (sv base s' ACC) = root224 a := by
  obtain F' := F.of_unch D.unch
  rw [rootMul]
  refine WP.seq (WP.syms (rstart_ok D.ws (kA_lt a (Nat.le_refl _)) D.k) fun s₁ ⟨r₁, O₁, v₁, k₁⟩ sy₁ => ?_)
  obtain hw₁ := wsReg_of_ks D.ws (Ks.of_rest (rs := [.s4, .s5]) r₁)
  refine WP.mono (muls_ok (y := ACC) (o := 0) (k := kA a 24 / 2) (by decide) (by decide)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (kA_lt a (Nat.le_refl _))) 24 (by decide) hw₁
    (D.tab.of_outside r₁.rd (by decide) O₁) (by rw [sy₁]; exact D.sym) k₁ (by rw [v₁]; exact F'.tr.1))
    fun s₂ ⟨hw₂, hT₂, sy₂, K₂, U₂, lt₂, v₂⟩ => ⟨hw₂, hT₂, by rw [sy₂, sy₁], (Ks.of_rest r₁).trans K₂.mono,
      O₁.unch.trans U₂, lt₂, ?_⟩
  rw [v₂, v₁, F'.tr.2, root224_eq]

end VG.Proof.EcKey.Compressed.RISCV64.P224
