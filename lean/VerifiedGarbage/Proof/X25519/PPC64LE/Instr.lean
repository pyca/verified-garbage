module

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# X25519 on PPC64LE: one instruction at a time

WP rules for the instructions the code uses, which expose only what changes
(`Upd`: one register, `Mupd`: the memory), what a piece of code leaves
unchanged (`Rest`), words of memory at offsets from a base (`wd`), and 64-bit
arithmetic without overflow.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws`, the link register and the
memory. -/
structure Rest (ws : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rest.refl (ws : List Reg) (s : State) : Rest ws s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Rest.trans {ws : List Reg} {s₁ s₂ s₃ : State} (h₁ : Rest ws s₁ s₂) (h₂ : Rest ws s₂ s₃) :
    Rest ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Rest.mono {ws ws' : List Reg} {s s' : State} (h : Rest ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Rest ws' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp only [State.write, ↓reduceIte], fun r h => by simp only [State.write, h, ↓reduceIte],
    rfl, rfl, rfl, rfl⟩

theorem Upd.rest {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Rest ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.rd, h.wr, h.sp⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Mupd.rest {s s' : State} {m : Mem} (h : Mupd s s' m) (ws : List Reg) : Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_add {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

theorem wp_lis {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d ((imm ++ (0 : BitVec 16)).signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lis d imm :: is)) s Q :=
  WP.cons exec_lis (k _ (Upd.write _ _ _))

theorem wp_ori {d n : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (s.gpr n ||| imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ori d n imm :: is)) s Q :=
  WP.cons exec_ori (k _ (Upd.write _ _ _))

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  WP.cons (exec_lsl h) (k _ (Upd.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_lw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_load_w hn ho hin) (k _ (Upd.write _ _ _))

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_store_w hn ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem read1_toNat (m : Mem) (a : Addr) : (m.read a 1).toNat = (m a).toNat := by
  show (Mem.read m (a + 1) 0 ++ m a).toNat = _
  rw [BitVec.toNat_append]
  simp [Mem.read]

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t (BitVec.ofNat 64 (s.mem a).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  subst ha
  have e : (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 64 =
      BitVec.ofNat 64 (s.mem (s.gpr n + BitVec.ofNat 64 off)).toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, read1_toNat, BitVec.toNat_ofNat]
  exact WP.cons (exec_lbz hn ho hin) (by rw [e]; exact k _ (Upd.write _ _ _))

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_stb hn ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

theorem eval_nonzero (s : State) (r : Reg) :
    isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  simp [eval, State.read, Size.bits]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  simp [eval, State.read, Size.bits]

/-! ## 64-bit arithmetic -/

theorem toNat_add_lt {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_le {x y : BitVec 64} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)]

theorem toNat_mul_lt {x y : BitVec 64} (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr (x : BitVec 64) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_shl (x : BitVec 64) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem toNat_imm {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_ne_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ne_eq, not_false_eq_true, decide_true, bne_iff_ne]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

/-- `BitVec.ofNat 64 n - 1`, for `1 ≤ n`. -/
theorem ofNat_sub_one {n : Nat} (hn : 1 ≤ n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sub_le (by rw [toNat_imm h, toNat_imm (by decide)]; exact hn), toNat_imm h,
    toNat_imm (by decide), toNat_imm (by omega)]

/-- A word loaded and zero-extended. -/
theorem toNat_ext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

/-- The low word of a register, as stored. -/
theorem toNat_lo32 (x : BitVec 64) : (x.setWidth 32).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_setWidth]

/-! ## Words at offsets from a base -/

/-- The word at `P + d`, as a number. -/
def wd (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 32).toNat

theorem wd_lt (m : Mem) (P : Addr) (d : Nat) : wd m P d < 2 ^ 32 := (m.readW _ 32).isLt

theorem wd_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 32) :
    wd (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [wd, Mem.readW_writeW_self32]

theorem wd_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) :
    wd (m.writeW (P + BitVec.ofNat 64 e) v) P d = wd m P d := by
  rw [wd, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), wd]

theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {d : Nat}
    (hd : ∀ r ∈ rs, (⟨P + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r) : wd m' P d = wd m P d := by
  rw [wd, wd, hf.readW (Region.contains_self _ _) hd (by decide)]

theorem wd_shift (m : Mem) (B : Addr) (a d : Nat) : wd m (B + BitVec.ofNat 64 a) d = wd m B (a + d) := by
  unfold wd; rw [Offset.add_add]

/-- An access at an offset of a region at an offset of `P`. -/
theorem in_off {rs : List Region} {P : Addr} {a len d n : Nat} (hr : (⟨P + BitVec.ofNat 64 a, len⟩ : Region) ∈ rs)
    (h1 : a ≤ d) (h2 : d + n ≤ a + len) (h3 : a + len < 2 ^ 64) :
    InRegions rs (P + BitVec.ofNat 64 d) n := ⟨_, hr, Offset.contains P h1 h2 h3⟩

theorem in_base {rs : List Region} {P : Addr} {len d n : Nat} (hr : (⟨P, len⟩ : Region) ∈ rs)
    (h : d + n ≤ len) (h3 : d < 2 ^ 64) : InRegions rs (P + BitVec.ofNat 64 d) n :=
  ⟨_, hr, Offset.contains_base P h h3⟩

end VG.Proof.X25519.PPC64LE
