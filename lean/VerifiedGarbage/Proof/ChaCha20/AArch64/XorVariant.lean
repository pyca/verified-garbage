import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Impl.ChaCha20.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract`. -/
section

/-!
# ChaCha20 keystream XOR on AArch64
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.AArch64

/-- AArch64 contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8,
len: usize, buf: *mut [u32; 80])`: XORs the first `len` bytes of the keystream
of the state at `state` into the `len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other; `data` does not wrap around the end of the
address space. The return address is in `x30`, not on the stack, and the
code uses no stack. The pointers and the length are public; the state and
the data are secret. -/
def xorAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
        (keystream (stateAt s.mem (s.gpr .x0)) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Variant`. -/
section

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

/-- Facts needed by the generic scalar stream caller. The functional proofs
are shared; each concrete backend supplies its mechanical taint checks. -/
structure BlockImpl where
  callee : Impl.ChaCha20.AArch64.Callee
  features : List String
  ok : ∀ s, blockAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ blockAArch64.post s s'
  noFrames : callee.code.noFrames = true
  keeps : ∀ r ∈ [Reg.x0, .x1], ∀ i ∈ instrs callee.code, dstOf i ≠ some r
  xorKeeps : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28],
    ∀ i ∈ instrs (Impl.ChaCha20.AArch64.Xor.xorWith callee), dstOf i ≠ some r
  xorKeepsV : (Impl.ChaCha20.AArch64.Xor.xorWith callee).allInstrs keepsV = true
  xorNoFrames : (Impl.ChaCha20.AArch64.Xor.xorWith callee).noFrames = true
  xorTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.ChaCha20.AArch64.Xor.xorWith callee) h).isSome = true

end VG.Proof.ChaCha20.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Xor

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Xor
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor
  serialize_stateAt)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt contains_off readW_writeW_out block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    VG.Proof.ChaCha20.AArch64.Xor.Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.ChaCha20.AArch64.Xor.Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_addImm32 {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .w d n imm :: is)) s Q :=
  WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm))
    (by simp [exec, h, State.read]) (k _ (Upd.write _ _ _ _))

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_eor32 {d n m : Reg}
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .w d n m :: is)) s Q :=
  WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 ^^^ (s.gpr m).setWidth 32)) rfl
    (k _ (Upd.write _ _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, VG.Proof.ChaCha20.AArch64.Xor.read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_str32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_ldr32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.ChaCha20.AArch64.Xor.Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_ (k _ (Upd.write s .w t _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

end

/-! ## Arithmetic -/

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by lit_omega)]

theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

theorem eval_nonzero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero .x r) s = some (decide (k ≠ 0)) := by
  have e : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s r
  rw [e, h, bne, VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero hk]
  simp

/-- The byte stored by `eor w6, w6, w8; strb w6, …` after two `ldrb`s. -/
theorem xor_setWidth (a b : Byte) :
    (((a.setWidth 64).setWidth 32 ^^^ (b.setWidth 64).setWidth 32).setWidth 64).setWidth 8 =
      a ^^^ b := by
  ext i hi; simp

/-- The word stored by `add w3, w3, #1; str w3, …` after an `ldr w3`. -/
theorem inc_setWidth (v : BitVec 32) :
    ((((v.setWidth 64).setWidth 32 + BitVec.ofNat 32 1).setWidth 64).setWidth 32) = v + 1 := by
  simp

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .x0
abbrev dp : Addr := s₀.gpr .x1
abbrev L : Nat := (s₀.gpr .x2).toNat
abbrev bp : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨VG.Proof.ChaCha20.AArch64.Xor.st s₀, 64⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.AArch64.Xor.dp s₀, VG.Proof.ChaCha20.AArch64.Xor.L s₀⟩
abbrev bR : Region := ⟨VG.Proof.ChaCha20.AArch64.Xor.bp s₀, 320⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.AArch64.Xor.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) (VG.Proof.ChaCha20.AArch64.Xor.L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (VG.Proof.ChaCha20.AArch64.Xor.L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j)
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.AArch64.Xor.L s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.AArch64.Xor.stR s₀, VG.Proof.ChaCha20.AArch64.Xor.dR s₀, VG.Proof.ChaCha20.AArch64.Xor.bR s₀]
  st_d : (VG.Proof.ChaCha20.AArch64.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Xor.dR s₀)
  st_b : (VG.Proof.ChaCha20.AArch64.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Xor.bR s₀)
  d_b : (VG.Proof.ChaCha20.AArch64.Xor.dR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Xor.bR s₀)
  nowrap : (VG.Proof.ChaCha20.AArch64.Xor.dp s₀).toNat + VG.Proof.ChaCha20.AArch64.Xor.L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorAArch64.pre s₀) : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Our caller's `x19`, `x20` and `x30`, saved in `buf[256, 280)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved (VG.Proof.ChaCha20.AArch64.Xor.bp s₀) s₀.gpr VG.Impl.ChaCha20.AArch64.Xor.saved m

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = VG.Proof.ChaCha20.AArch64.Xor.st s₀
  x1 : s.gpr .x1 = VG.Proof.ChaCha20.AArch64.Xor.bp s₀
  x19 : s.gpr .x19 = VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j)
  x20 : s.gpr .x20 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (VG.Proof.ChaCha20.AArch64.Xor.st s₀) = ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.AArch64.Xor.L s₀, s.mem (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j then VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.AArch64.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.AArch64.Xor.Saved s₀ s.mem

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_out m p v (j := i) (k := 12) hi (by lit_omega) (by lit_omega)

/-- The counter (word 12) of a state in memory. -/
theorem stateAt_getElem_counter (m : Mem) (p : Addr) :
    (stateAt m p)[12] = m.readW (p + BitVec.ofNat 64 48) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-- The state after its counter is advanced by `j` in memory. -/
theorem stateAt_writeW_ctr (m : Mem) (p : Addr) (j : Nat) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48)
      (m.readW (p + BitVec.ofNat 64 48) 32 + BitVec.ofNat 32 j)) p = ctr (stateAt m p) j := by
  rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, ctr, VG.Proof.ChaCha20.AArch64.Xor.stateAt_getElem_counter]

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_off (by lit_omega) (by lit_omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Xor.bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 256, 24⟩

theorem b256_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Xor.b256 s₀) (VG.Proof.ChaCha20.AArch64.Xor.bR s₀) := Region.sub_prefix (by lit_omega)

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.AArch64.Xor.savR s₀) (VG.Proof.ChaCha20.AArch64.Xor.bR s₀) := Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (VG.Proof.ChaCha20.AArch64.Xor.savR s₀).Disjoint (VG.Proof.ChaCha20.AArch64.Xor.b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.AArch64.Xor.Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.AArch64.Xor.savR s₀).Disjoint r) : VG.Proof.ChaCha20.AArch64.Xor.Saved s₀ m' :=
  Spill.Saved.frame_in h (by decide) hf hd

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < VG.Proof.ChaCha20.AArch64.Xor.L s₀) (hk' : k' < VG.Proof.ChaCha20.AArch64.Xor.L s₀) (h : k' ≠ k) :
    VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 k' ≠ VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 k := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - VG.Proof.ChaCha20.AArch64.Xor.dp s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  exact h this

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) :
    WP isa (.block (VG.Impl.ChaCha20.AArch64.Xor.save ++ [mov .x19 .x1, mov .x20 .x2, mov .x1 .x3])) s₀ (VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ 0) := by
  refine Spill.save_ok (by decide) (fun p hp' => have hb : p.2 + 8 ≤ 320 := by revert p; decide
    ⟨VG.Proof.ChaCha20.AArch64.Xor.bR s₀, by simp [hp.wr], contains_off hb (by omega)⟩) ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_mov fun s₄ u₄ => VG.Proof.ChaCha20.AArch64.Xor.wp_mov fun s₅ u₅ => VG.Proof.ChaCha20.AArch64.Xor.wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = Spill.saveMem s₀.mem (VG.Proof.ChaCha20.AArch64.Xor.bp s₀) s₀.gpr VG.Impl.ChaCha20.AArch64.Xor.saved := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hf : Frame [VG.Proof.ChaCha20.AArch64.Xor.bR s₀] s₀.mem s₆.mem := by
    rw [hm]; exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; simp [VG.Proof.ChaCha20.AArch64.Xor.P]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide)]; simp [VG.Proof.ChaCha20.AArch64.Xor.P]
  · rw [u₆.rd, u₅.rd, u₄.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr]
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [VG.Proof.ChaCha20.AArch64.Xor.P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := VG.Proof.ChaCha20.AArch64.Xor.dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀)) hk
  · rw [hm]; exact Spill.saveMem_saved (by decide) _ _ _

/-! ## Calling the block function -/

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s where
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j))).getD t 0

theorem call_ok (v : VG.Proof.ChaCha20.AArch64.BlockImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s) :
    WP isa (.call v.callee.name v.callee.code) s (VG.Proof.ChaCha20.AArch64.Xor.AInv s₀ j) := by
  have c0 : s.callEntry.gpr .x0 = VG.Proof.ChaCha20.AArch64.Xor.st s₀ := (State.callEntry_gpr _ (by decide)).trans h.x0
  have c1 : s.callEntry.gpr .x1 = VG.Proof.ChaCha20.AArch64.Xor.bp s₀ := (State.callEntry_gpr _ (by decide)).trans h.x1
  have hwr : s.wr = [VG.Proof.ChaCha20.AArch64.Xor.stR s₀, VG.Proof.ChaCha20.AArch64.Xor.dR s₀, VG.Proof.ChaCha20.AArch64.Xor.bR s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockAArch64) v.ok
    (rd := [VG.Proof.ChaCha20.AArch64.Xor.stR s₀]) (wr := [VG.Proof.ChaCha20.AArch64.Xor.b256 s₀]) ?_ ?_ ?_ ?_ v.noFrames
  · simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (VG.Proof.ChaCha20.AArch64.Xor.b256_sub s₀)).symm⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.AArch64.Xor.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨VG.Proof.ChaCha20.AArch64.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.AArch64.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    have hst : stateAt s₂.mem (VG.Proof.ChaCha20.AArch64.Xor.st s₀) = stateAt s.mem (VG.Proof.ChaCha20.AArch64.Xor.st s₀) :=
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by simpa using hp.st_b.sub_right (VG.Proof.ChaCha20.AArch64.Xor.b256_sub s₀))
    simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    refine ⟨⟨by rw [hkeep .x0 (by decide) (v.keeps _ (by simp)), h.x0],
      by rw [hkeep .x1 (by decide) (v.keeps _ (by simp)), h.x1],
      by rw [hcs .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [hcs .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], by rw [hst, h.cnt], fun k hk => ?_,
      h.saved.frame hf (by simpa using VG.Proof.ChaCha20.AArch64.Xor.savR_b256 s₀)⟩, fun t ht => ?_⟩
    · rw [hf.bytes (R := VG.Proof.ChaCha20.AArch64.Xor.dR s₀) (by simpa using hp.d_b.sub_right (VG.Proof.ChaCha20.AArch64.Xor.b256_sub s₀)) (Nat.le_of_lt (VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀)) hk]
      exact h.data k hk
    · rw [← serialize_stateAt s₂.mem (VG.Proof.ChaCha20.AArch64.Xor.bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = VG.Proof.ChaCha20.AArch64.Xor.st s₀
  x1 : s.gpr .x1 = VG.Proof.ChaCha20.AArch64.Xor.bp s₀
  x19 : s.gpr .x19 = VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)
  x7 : s.gpr .x7 = VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j - i)
  x20 : s.gpr .x20 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j - VG.Proof.ChaCha20.AArch64.Xor.C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (VG.Proof.ChaCha20.AArch64.Xor.st s₀) = ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.AArch64.Xor.L s₀, s.mem (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i then VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.AArch64.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.AArch64.Xor.Saved s₀ s.mem
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j))).getD t 0

theorem sel_ok {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Xor.AInv s₀ j s) :
    WP isa (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
      (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
        (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1]))) s (VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j 0) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hC : VG.Proof.ChaCha20.AArch64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) := rfl
  refine WP.seq (VG.Proof.ChaCha20.AArch64.Xor.wp_lsr (by decide) fun s₁ u₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hx9 : s₂.gpr .x9 = BitVec.ofNat 64 ((VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) / 64) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.x20, VG.Proof.ChaCha20.AArch64.Xor.ofNat_shr6 (by lit_omega)]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.x20]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .x2 = BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j) ∧
      (∀ r, r ≠ .x2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) / 64 = 0))
      (by have e : isa.eval (.zero .x .x9) s₂ = some (s₂.gpr .x9 == 0) := VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₂ .x9
          rw [e, hx9, VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by lit_omega)])
      (fun ht => WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hf => VG.Proof.ChaCha20.AArch64.Xor.wp_movz fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [hx2, show VG.Proof.ChaCha20.AArch64.Xor.C s₀ j = VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show VG.Proof.ChaCha20.AArch64.Xor.C s₀ j = 64 by omega]; rfl
  · refine VG.Proof.ChaCha20.AArch64.Xor.wp_sub fun s₄ u₄ => VG.Proof.ChaCha20.AArch64.Xor.wp_mov fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .x2 → r ≠ .x20 → r ≠ .x7 → r ≠ .x9 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ => by rw [u₅.other r h₃, u₄.other r h₂, f₂ r h₁, u₂.other r h₁, u₁.other r h₄]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, u₂.mem, u₁.mem]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x0],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x1],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.x19, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.x1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂ _ (by decide), f₁, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x20, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by lit_omega)],
      by rw [u₅.rd, u₄.rd, f₄, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, u₂.wr, u₁.wr, h.wr],
      by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.ldrb .x6 .x19 0, .ldrb .x8 .x7 0, .logic .eor .w .x6 .x6 .x8, .strb .x6 .x19 0,
    .addImm .x .x19 .x19 1, .addImm .x .x7 .x7 1, .subImm .x .x2 .x2 1]

theorem xorLoop_eq : xorLoop = .loop (.block VG.Proof.ChaCha20.AArch64.Xor.xorBody) (.nonzero .x .x2) := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j = 64 * j := by
  simp only [VG.Proof.ChaCha20.AArch64.Xor.P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.AArch64.Xor.C s₀ j) :
    (VG.Proof.ChaCha20.AArch64.Xor.KS s₀).getD (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j))).getD i 0 := by
  have hP := VG.Proof.ChaCha20.AArch64.Xor.P_eq hj
  have hC : VG.Proof.ChaCha20.AArch64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) := rfl
  rw [VG.Proof.ChaCha20.AArch64.Xor.KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j i : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.AArch64.Xor.C s₀ j)
    {s : State} (h : VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j i s) : WP isa (.block VG.Proof.ChaCha20.AArch64.Xor.xorBody) s (VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j (i + 1)) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hk : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i < VG.Proof.ChaCha20.AArch64.Xor.L s₀ := by have hC : VG.Proof.ChaCha20.AArch64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j) := rfl; omega
  have hC64 : VG.Proof.ChaCha20.AArch64.Xor.C s₀ j ≤ 64 := Nat.min_le_left _ _
  have cd : (VG.Proof.ChaCha20.AArch64.Xor.dR s₀).Contains (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)) 1 :=
    contains_off (by lit_omega) (by lit_omega)
  have cb : (VG.Proof.ChaCha20.AArch64.Xor.bR s₀).Contains (VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 i) 1 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.AArch64.Xor.dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨VG.Proof.ChaCha20.AArch64.Xor.bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.AArch64.Xor.dR s₀, by simp [h.wr, hp.wr], cd⟩
  unfold VG.Proof.ChaCha20.AArch64.Xor.xorBody
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_ldrb (a := VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)) (by decide)
    (by rw [h.x19]; exact BitVec.add_zero _) i₁ fun s₁ u₁ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_ldrb (a := VG.Proof.ChaCha20.AArch64.Xor.bp s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.x7]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_eor32 fun s₃ u₃ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_strb (a := VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x19]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide) fun s₅ u₅ => VG.Proof.ChaCha20.AArch64.Xor.wp_addImm (by decide) fun s₆ u₆ =>
    VG.Proof.ChaCha20.AArch64.Xor.wp_subImm (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : (s₃.gpr .x6).setWidth 8 =
      VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i) ^^^ (VG.Proof.ChaCha20.AArch64.Xor.KS s₀).getD (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, VG.Proof.ChaCha20.AArch64.Xor.xor_setWidth, h.data _ hk,
      h.ks i (by lit_omega), VG.Proof.ChaCha20.AArch64.Xor.ks_eq hj hi]
    simp
  have hm : s₇.mem = s.mem.writeW (VG.Proof.ChaCha20.AArch64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i))
      (VG.Proof.ChaCha20.AArch64.Xor.D0 s₀ (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i) ^^^ (VG.Proof.ChaCha20.AArch64.Xor.KS s₀).getD (VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [VG.Proof.ChaCha20.AArch64.Xor.dR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x19 → r ≠ .x7 → r ≠ .x2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, g₄.gpr, u₃.other r h₁, u₂.other r h₂,
        u₁.other r h₁]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x1], ?_, ?_, ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x20],
    by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfd (by simpa using hp.st_d), h.cnt], fun k hk' => ?_,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (VG.Proof.ChaCha20.AArch64.Xor.savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.x19, VG.Proof.ChaCha20.AArch64.Xor.add_ofNat, Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.x7, VG.Proof.ChaCha20.AArch64.Xor.add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.x2, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by lit_omega), Nat.sub_sub]
  · rw [hm, VG.Proof.ChaCha20.AArch64.Xor.writeW8_apply]
    by_cases he : k = VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.AArch64.Xor.data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + i
      · simp [h₁, show k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + (i + 1) by omega]
  · rw [hfd.bytes (R := VG.Proof.ChaCha20.AArch64.Xor.bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j 0 s) : WP isa xorLoop s (VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j)) := by
  have hpos : 0 < VG.Proof.ChaCha20.AArch64.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.AArch64.Xor.C]; omega
  have hC : VG.Proof.ChaCha20.AArch64.Xor.C s₀ j ≤ 64 := by simp only [VG.Proof.ChaCha20.AArch64.Xor.C]; omega
  rw [VG.Proof.ChaCha20.AArch64.Xor.xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = VG.Proof.ChaCha20.AArch64.Xor.C s₀ j - i ∧ i < VG.Proof.ChaCha20.AArch64.Xor.C s₀ j ∧ VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block VG.Proof.ChaCha20.AArch64.Xor.xorBody) s (fun s' =>
      (isa.eval (.nonzero .x .x2) s' = some false ∧ VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j) s') ∨
      (isa.eval (.nonzero .x .x2) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.AArch64.Xor.xor_step hp hj hi hI) fun s' h' => ?_
    have hz := VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero_ofNat s' .x2 (by lit_omega) h'.x2
    by_cases hl : i + 1 = VG.Proof.ChaCha20.AArch64.Xor.C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, VG.Proof.ChaCha20.AArch64.Xor.C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

def nextInstrs : List Instr := [.ldr .w .x3 .x0 48, .addImm .w .x3 .x3 1, .str .w .x3 .x0 48]

theorem P_succ {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) : VG.Proof.ChaCha20.AArch64.Xor.P s₀ (j + 1) = VG.Proof.ChaCha20.AArch64.Xor.P s₀ j + VG.Proof.ChaCha20.AArch64.Xor.C s₀ j := by
  simp only [VG.Proof.ChaCha20.AArch64.Xor.P, VG.Proof.ChaCha20.AArch64.Xor.C] at *; omega

theorem next_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.AArch64.Xor.IInv s₀ j (VG.Proof.ChaCha20.AArch64.Xor.C s₀ j) s) : WP isa (.block VG.Proof.ChaCha20.AArch64.Xor.nextInstrs) s (VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ (j + 1)) := by
  have hP := VG.Proof.ChaCha20.AArch64.Xor.P_succ hj
  have c₁ : (VG.Proof.ChaCha20.AArch64.Xor.stR s₀).Contains (VG.Proof.ChaCha20.AArch64.Xor.st s₀ + BitVec.ofNat 64 48) 4 := contains_off (by lit_omega) (by lit_omega)
  unfold VG.Proof.ChaCha20.AArch64.Xor.nextInstrs
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_ldr32 (by decide) (by rw [h.x0]) ⟨VG.Proof.ChaCha20.AArch64.Xor.stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
    fun s₁ u₁ => VG.Proof.ChaCha20.AArch64.Xor.wp_addImm32 (by decide) fun s₂ u₂ => ?_
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_str32 (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.x0])
    ⟨VG.Proof.ChaCha20.AArch64.Xor.stR s₀, by simp [u₂.wr, u₁.wr, h.wr, hp.wr], c₁⟩ fun s₃ g₃ => WP.block_nil ?_
  have hv : s.mem.readW (VG.Proof.ChaCha20.AArch64.Xor.st s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  have hm : s₃.mem = s.mem.writeW (VG.Proof.ChaCha20.AArch64.Xor.st s₀ + BitVec.ofNat 64 48) ((ctr (VG.Proof.ChaCha20.AArch64.Xor.S0 s₀) j)[12]'(by decide) + 1) := by
    rw [g₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, VG.Proof.ChaCha20.AArch64.Xor.inc_setWidth, hv]
  have hfs : Frame [VG.Proof.ChaCha20.AArch64.Xor.stR s₀] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have g : ∀ r, r ≠ .x3 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃.gpr, u₂.other r hr, u₁.other r hr]
  refine ⟨by rw [g _ (by decide), h.x0], by rw [g _ (by decide), h.x1],
    by rw [g _ (by decide), h.x19, hP], by rw [g _ (by decide), h.x20, hP, Nat.sub_sub],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [hm, VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, h.cnt, ctr_succ], fun k hk => ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (VG.Proof.ChaCha20.AArch64.Xor.savR_sub s₀)).symm)⟩
  rw [hfs.bytes (R := VG.Proof.ChaCha20.AArch64.Xor.dR s₀) (by simpa using hp.st_d.symm) (Nat.le_of_lt (VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀)) hk, h.data k hk, hP]

theorem body_eq (v : VG.Proof.ChaCha20.AArch64.BlockImpl) : bodyWith v.callee =
    .seq (.call v.callee.name v.callee.code)
    (.seq (.block [.lsr .x .x9 .x20 6, mov .x2 .x20])
    (.seq (.ite (.zero .x .x9) (.block []) (.block [.movz .x .x2 64 0]))
    (.seq (.block [.sub .x .x20 .x20 .x2, mov .x7 .x1])
    (.seq xorLoop (.block VG.Proof.ChaCha20.AArch64.Xor.nextInstrs))))) := rfl

theorem body_ok (v : VG.Proof.ChaCha20.AArch64.BlockImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s) : WP isa (bodyWith v.callee) s (VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ (j + 1)) := by
  rw [VG.Proof.ChaCha20.AArch64.Xor.body_eq v]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Xor.call_ok v hp h) fun s₁ h₁ => ?_)
  have hs := VG.Proof.ChaCha20.AArch64.Xor.sel_ok hj h₁
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Xor.xorLoop_ok hp hj h₄) fun s₅ h₅ => VG.Proof.ChaCha20.AArch64.Xor.next_ok hp hj h₅)

/-! ## The epilogue -/

/-- What the code guarantees on return, beyond the registers it never writes. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ VG.Impl.ChaCha20.AArch64.Xor.saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.gpr .x0 = VG.Proof.ChaCha20.AArch64.Xor.st s₀ ∧ s'.gpr .x1 = VG.Proof.ChaCha20.AArch64.Xor.bp s₀ ∧
    Proof.ChaCha20.xorAArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.AArch64.Xor.P s₀ j = VG.Proof.ChaCha20.AArch64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s) : WP isa (.block VG.Impl.ChaCha20.AArch64.Xor.restore) s (VG.Proof.ChaCha20.AArch64.Xor.Post s₀) := by
  refine WP.mono (Spill.restore_wp h.x1 (by decide) (by decide) (fun p hp' =>
      have hb : p.2 + 8 ≤ 320 := by revert p; decide
      ⟨VG.Proof.ChaCha20.AArch64.Xor.bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off hb (by omega)⟩)
    h.saved) fun s₃ h₃ => ⟨h₃.gpr, by rw [h₃.other _ (by decide), h.x0],
      by rw [h₃.other _ (by decide), h.x1], ?_⟩
  · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    have hk' : k < VG.Proof.ChaCha20.AArch64.Xor.L s₀ := hk
    rw [h₃.mem, h.data k hk']
    simp only [show k < VG.Proof.ChaCha20.AArch64.Xor.P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq (v : VG.Proof.ChaCha20.AArch64.BlockImpl) : (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) =
    .seq (.block (VG.Impl.ChaCha20.AArch64.Xor.save ++ [mov .x19 .x1, mov .x20 .x2, mov .x1 .x3]))
    (.seq (.ite (.zero .x .x20) (.block []) (.loop (bodyWith v.callee) (.nonzero .x .x20))) (.block VG.Impl.ChaCha20.AArch64.Xor.restore)) := rfl

theorem main_ok (v : VG.Proof.ChaCha20.AArch64.BlockImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) : WP isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s₀ (VG.Proof.ChaCha20.AArch64.Xor.Post s₀) := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  rw [VG.Proof.ChaCha20.AArch64.Xor.xor_eq v]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.AArch64.Xor.prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, VG.Proof.ChaCha20.AArch64.Xor.P s₀ j = VG.Proof.ChaCha20.AArch64.Xor.L s₀ ∧ VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => VG.Proof.ChaCha20.AArch64.Xor.epilogue_ok hp hj h₂)
  have hz : isa.eval (.zero .x .x20) s₁ = some (decide (VG.Proof.ChaCha20.AArch64.Xor.L s₀ = 0)) := by
    have e : isa.eval (.zero .x .x20) s₁ = some (s₁.gpr .x20 == 0) := VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₁ .x20
    rw [e, h₁.x20, VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by lit_omega)]
    simp [VG.Proof.ChaCha20.AArch64.Xor.P]
  refine WP.ite (decide (VG.Proof.ChaCha20.AArch64.Xor.L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [VG.Proof.ChaCha20.AArch64.Xor.P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ j ∧ VG.Proof.ChaCha20.AArch64.Xor.P s₀ j < VG.Proof.ChaCha20.AArch64.Xor.L s₀ ∧ VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s
    have hstep : ∀ n s, Inv n s → WP isa (bodyWith v.callee) s (fun s' =>
        (isa.eval (.nonzero .x .x20) s' = some false ∧ ∃ j, VG.Proof.ChaCha20.AArch64.Xor.P s₀ j = VG.Proof.ChaCha20.AArch64.Xor.L s₀ ∧ VG.Proof.ChaCha20.AArch64.Xor.OInv s₀ j s') ∨
        (isa.eval (.nonzero .x .x20) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (VG.Proof.ChaCha20.AArch64.Xor.body_ok v hp hj hI) fun s' h' => ?_
      have hz' := VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero_ofNat s' .x20 (by lit_omega) h'.x20
      have hP := VG.Proof.ChaCha20.AArch64.Xor.P_succ hj
      have hC : 0 < VG.Proof.ChaCha20.AArch64.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.AArch64.Xor.C]; omega
      have hle : VG.Proof.ChaCha20.AArch64.Xor.P s₀ (j + 1) ≤ VG.Proof.ChaCha20.AArch64.Xor.L s₀ := by simp only [VG.Proof.ChaCha20.AArch64.Xor.P]; omega
      by_cases hl : VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h'⟩
      · exact .inr ⟨by rw [hz']; simp [hl], VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.AArch64.Xor.L s₀ - VG.Proof.ChaCha20.AArch64.Xor.P s₀ 0) s₁ ⟨0, rfl, by simp [VG.Proof.ChaCha20.AArch64.Xor.P]; omega, h₁⟩

/-- The callee-saved registers the code never writes (`x19`, `x20` and `x30`
are saved and restored). -/
def untouched : List Reg := [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

theorem untouched_ok (v : VG.Proof.ChaCha20.AArch64.BlockImpl) : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Xor.untouched,
    ∀ i ∈ instrs (Impl.ChaCha20.AArch64.Xor.xorWith v.callee), dstOf i ≠ some r := v.xorKeeps

theorem correct (v : VG.Proof.ChaCha20.AArch64.BlockImpl) {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.XPre s₀) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (Proof.ChaCha20.xorAArch64.post s₀ s' ∧ s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3) := by
  obtain ⟨t, s', he, ⟨hsv, h0, h1, hpost⟩⟩ := VG.Proof.ChaCha20.AArch64.Xor.main_ok v hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he v.xorKeepsV⟩, hpost, h0, h1⟩
  have hu : ∀ r ∈ VG.Proof.ChaCha20.AArch64.Xor.untouched, s'.gpr r = s₀.gpr r := fun r hr =>
    Exec.gpr (VG.Proof.ChaCha20.AArch64.Xor.untouched_ok v r hr) he (.inr (by
      simp only [VG.Proof.ChaCha20.AArch64.Xor.untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, 256) (by simp [VG.Impl.ChaCha20.AArch64.Xor.saved])
  · exact hsv (.x20, 264) (by simp [VG.Impl.ChaCha20.AArch64.Xor.saved])
  all_goals first | exact hsv (.x30, 272) (by simp [VG.Impl.ChaCha20.AArch64.Xor.saved]) | exact hu _ (by simp [VG.Proof.ChaCha20.AArch64.Xor.untouched])

/-- `vg_chacha20_xor` returns with `x0` holding `state` and `x1` holding `buf`
(which was in `x3` on entry), for a caller that recomputes pointers from
them. -/
theorem xor_x1 (v : VG.Proof.ChaCha20.AArch64.BlockImpl) (s : State) (hs : Proof.ChaCha20.xorAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorAArch64.post s s' ∧ s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x1 = s.gpr .x3) :=
  VG.Proof.ChaCha20.AArch64.Xor.correct v (XPre.of s hs)

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.ChaCha20.xorAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (v : VG.Proof.ChaCha20.AArch64.BlockImpl) (s : State) (hs : Proof.ChaCha20.xorAArch64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorAArch64.post s s' :=
  (VG.Proof.ChaCha20.AArch64.Xor.correct v (XPre.of s hs)).imp fun _ ⟨s', he, ha, hpost, _⟩ => ⟨s', he, ha, hpost⟩

theorem xor_ct (v : VG.Proof.ChaCha20.AArch64.BlockImpl) : ConstantTime isa Proof.ChaCha20.xorAArch64.pre Proof.ChaCha20.xorAArch64.pub
    (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) := by
  obtain ⟨h, hh⟩ := v.xorTaint
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => VG.Proof.ChaCha20.AArch64.Xor.agree₀ hp) hh

theorem xor_verified (v : VG.Proof.ChaCha20.AArch64.BlockImpl) :
    Verified AArch64.target (Impl.ChaCha20.AArch64.Xor.xorWith v.callee) (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct (VG.Proof.ChaCha20.AArch64.Xor.xor_correct v) (VG.Proof.ChaCha20.AArch64.Xor.xor_ct v)
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, AArch64.abi, AArch64.argRegs,
      Proof.ChaCha20.xorAArch64]
      [sat] using VG.Proof.ChaCha20.AArch64.Xor.sat)

end VG.Proof.ChaCha20.AArch64.Xor

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant`. -/
section

namespace VG.Proof.ChaCha20.AArch64

open VG VG.AArch64

/-- A verified stream backend, shared by the public stream and every AEAD caller. -/
structure XorImpl where
  callee : Impl.ChaCha20.AArch64.XorCallee
  features : List String
  /-- Notes on the implementation, for the documentation of `vg_chacha20_xor` and its
  variants. -/
  notes : List String
  ok : ∀ s, xorAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ xorAArch64.post s s'
  ct : ConstantTime isa xorAArch64.pre xorAArch64.pub callee.code
  noFrames : callee.code.noFrames = true
  /-- Whether ChaCha20-Poly1305 absorbs the data inside the eight-block kernel
  (`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), calling the backend for the
  rest, rather than calling it for all of the data. -/
  stitched : Bool
  /-- ChaCha20-Poly1305's code up to the tag is constant time (the rest,
  `sealTail` and `openTail`, does not depend on the backend). -/
  sealTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (Impl.ChaCha20Poly1305.AArch64.sealMainCode callee stitched) h).isSome = true
  openTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (Impl.ChaCha20Poly1305.AArch64.openMainCode callee stitched) h).isSome = true

theorem XorImpl.verified (v : VG.Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target v.callee.code (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct v.ok v.ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, AArch64.abi, AArch64.argRegs,
      VG.Proof.ChaCha20.xorAArch64] [Xor.sat] using Xor.sat)

end VG.Proof.ChaCha20.AArch64

end
