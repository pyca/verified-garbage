module

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# X25519 on RISC-V: one instruction at a time

The WP rules of `Proof/Framework/RISCV64/Steps.lean` (`Upd`: one register,
`Mupd`: the memory), with those for the multiplication, `and` and the aligned
words of the working space, what a piece of code leaves unchanged (`Rest`),
words of memory at offsets from a base (`wd`), and 64-bit arithmetic without
overflow, as `Proof/X25519/PPC64LE/Instr.lean` states them for PPC64LE.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps

/-! ## What code changes -/

/-- `s'` is `s` except for the registers `ws` and the memory. -/
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

theorem _root_.VG.RISCV64.Steps.Upd.rest {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) {ws : List Reg}
    (hd : d ∈ ws) : Rest ws s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ hd), h.rd, h.wr, h.sp⟩

theorem _root_.VG.RISCV64.Steps.Mupd.rest {s s' : State} {m : Mem} (h : Mupd s s' m) (ws : List Reg) : Rest ws s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

/-! ## One instruction at a time -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_load_w ho hal hin) (k _ (Upd.write _ _ _))

theorem wp_sw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_store_w ho hal hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- `lbu`, with the byte as a number. -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t (BitVec.ofNat 64 (s.mem a).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q :=
  wp_lbu ho ha hin fun s' u => k s' (by
    have e : (s.mem a).setWidth 64 = BitVec.ofNat 64 (s.mem a).toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← e]; exact u)

end

/-- Running `l ++ rest` by running `l` first. -/
theorem WP.append {l rest : List Instr} {s : State} {P Q : State → Prop}
    (h : WP isa (.block l) s P) (k : ∀ s', P s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono h k)

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
  rw [bne, ofNat_beq_zero h]
  simp

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

/-- An address `P + d` is a multiple of 4 if `P` is one of 8 and `d` one of 4. -/
theorem al4 {P : Addr} (hP : P.toNat % 8 = 0) {d : Nat} (hd : d % 4 = 0) :
    (P + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end VG.Proof.X25519.RISCV64
