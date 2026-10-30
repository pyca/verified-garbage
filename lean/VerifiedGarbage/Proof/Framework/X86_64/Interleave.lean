module

public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# x86-64: interleaving independent code

Untrusted: everything here is checked by Lean. The x86-64 instance of
`Proof/Framework/Interleave.lean`. Each instruction of a class (the scalar
`mov` and ALU instructions, `andn`, `rorx`, `aluTbl`, the AVX2 lane-wise
binary operations, shifts and `vpalignr`, and `vmovdqu` loads and stores at
`[b + ix * sc + disp]` for a fixed base `b`, index `ix` and scale `sc`) has a
*footprint* (`Fp`): the general-purpose and vector registers (by
`ctorIdx`), the flags, and the bytes (at offsets from `b + ix * sc`) it may
read and write. Two instructions whose footprints are independent (neither
writes what the other reads or writes, nor the base or index) commute
(`exec_comm`), so any interleaving of two blocks whose footprints are
independent runs as the first block and then the second (`footprints`,
`Interleave.Footprints.indeps_of_check`, `Interleave.WP.merge`). Register
sets and byte sets are bit masks, which the kernel evaluates as `Nat`s.

A vector register in a footprint stands for its low 128 bits, bits 255:128
and bits 511:256 (`xmm`, `ymmHi`, `zmmHi`): the class's instructions write
all three, and read the first two.
-/

@[expose] public section

namespace VG.X86_64.Interleave

open VG VG.Interleave

/-- Bit `r` of a register mask. -/
def gbit (r : Reg) : Nat := 2 ^ r.ctorIdx
/-- Bit `r` of a vector register mask. -/
def xbit (r : XReg) : Nat := 2 ^ r.ctorIdx
/-- The bytes `[off, off + n)`. -/
def range (off n : Nat) : Nat := (2 ^ n - 1) * 2 ^ off

/-- What an instruction may read and write: registers and vector registers
by `ctorIdx`, the flags (CF, ZF, SF, OF) as one, memory by byte offset from
the base address. -/
structure Fp where
  gr : Nat
  gw : Nat
  xr : Nat
  xw : Nat
  cr : Bool
  cw : Bool
  mr : Nat
  mw : Nat
  deriving DecidableEq, Repr

def Fp.empty : Fp := ⟨0, 0, 0, 0, false, false, 0, 0⟩

def Fp.union (a b : Fp) : Fp :=
  ⟨a.gr ||| b.gr, a.gw ||| b.gw, a.xr ||| b.xr, a.xw ||| b.xw, a.cr || b.cr, a.cw || b.cw,
    a.mr ||| b.mr, a.mw ||| b.mw⟩

/-- Neither writes what the other reads or writes, and neither writes the
registers `bm` of the base address. -/
def Fp.indep (bm : Nat) (a b : Fp) : Bool :=
  (a.gw &&& (b.gr ||| b.gw)) == 0 && (b.gw &&& a.gr) == 0 &&
  (a.xw &&& (b.xr ||| b.xw)) == 0 && (b.xw &&& a.xr) == 0 &&
  !(a.cw && (b.cr || b.cw)) && !(b.cw && a.cr) &&
  (a.mw &&& (b.mr ||| b.mw)) == 0 && (b.mw &&& a.mr) == 0 &&
  (a.gw &&& bm) == 0 && (b.gw &&& bm) == 0 &&
  a.mr >>> 65536 == 0 && a.mw >>> 65536 == 0 && b.mr >>> 65536 == 0 && b.mw >>> 65536 == 0

section
variable (b : Reg) (ix : Option Reg) (sc : Nat)

/-- The registers of the base address. -/
def baseMask : Nat := gbit b ||| (match ix with | some i => gbit i | none => 0)

/-- The base address, `b + ix * sc`. -/
def bAddr (s : State) : Addr :=
  match ix with
  | none => s.gpr b
  | some i => s.gpr b + s.gpr i * BitVec.ofNat 64 sc

/-- The offset of a memory operand from the base address, `none` unless it
has the base, index and scale, and a displacement below `2 ^ 16`. -/
def memOff (m : MemOp) : Option Nat :=
  if m.base = b ∧ m.index = ix ∧ m.scale = sc ∧ 0 ≤ m.disp ∧ m.disp < 65536 then some m.disp.toNat else none

def regFp (r w : Nat) : Fp := ⟨r, w, 0, 0, false, false, 0, 0⟩
def vecFp (r w : Nat) : Fp := ⟨0, 0, r, w, false, false, 0, 0⟩

/-- The registers an ALU source reads, and the bytes. -/
def srcFp : Src → Option (Nat × Nat)
  | .reg r => some (gbit r, 0)
  | .imm _ => some (0, 0)
  | .mem m => (memOff b ix sc m).map fun o => (baseMask b ix, range o 8)

def readsCf : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def memIx (m : MemOp) : Nat := gbit m.base ||| (match m.index with | some i => gbit i | none => 0)

def VOp.fp : VOp → Option Fp
  | .vbin _ _ d x y | .vpalignr _ d x y _ => some (vecFp (xbit x ||| xbit y) (xbit d))
  | .vshift _ _ d x _ => some (vecFp (xbit x) (xbit d))
  | _ => none

def lenBytes : VLen → Nat
  | .l128 => 16
  | .l256 => 32

/-- The footprint of an instruction of the class, `none` for any other. -/
def fp : Instr → Option Fp
  | .mov d (.reg r) => some (regFp (gbit r) (gbit d))
  | .mov d (.imm _) => some (regFp 0 (gbit d))
  | .mov d (.mem m) => (memOff b ix sc m).map fun o => ⟨baseMask b ix, gbit d, 0, 0, false, false, range o 8, 0⟩
  | .alu op d src => (srcFp b ix sc src).map fun (g, mr) =>
    ⟨gbit d ||| g, gbit d, 0, 0, readsCf op, true, mr, 0⟩
  | .andn d x y => some ⟨gbit x ||| gbit y, gbit d, 0, 0, false, true, 0, 0⟩
  | .rorx d r _ => some (regFp (gbit r) (gbit d))
  | .aluTbl op d m _ _ => some ⟨gbit d ||| memIx m, gbit d, 0, 0, readsCf op, true, 0, 0⟩
  | .vop op => VOp.fp op
  | .vmovdquLoad len d m =>
    (memOff b ix sc m).map fun o => ⟨baseMask b ix, 0, 0, xbit d, false, false, range o (lenBytes len), 0⟩
  | .vmovdquStore len m r =>
    (memOff b ix sc m).map fun o => ⟨baseMask b ix, 0, xbit r, 0, false, false, 0, range o (lenBytes len)⟩
  | _ => none

end


/-! ## What a footprint promises -/

/-- The flags. -/
abbrev _root_.VG.X86_64.State.flags (s : State) : Option Bool × Option Bool × Option Bool × Option Bool :=
  (s.cf, s.zf, s.sf, s.of)

section
variable {b : Reg} {ix : Option Reg} {sc : Nat}

/-- `s` and `t` agree on what `F` reads (and on the base address and the regions). -/
structure Reads (b : Reg) (ix : Option Reg) (sc : Nat) (F : Fp) (s t : State) : Prop where
  gpr : ∀ r : Reg, F.gr.testBit r.ctorIdx → s.gpr r = t.gpr r
  x : ∀ r : XReg, F.xr.testBit r.ctorIdx → s.xmm r = t.xmm r ∧ s.ymmHi r = t.ymmHi r
  c : F.cr → s.flags = t.flags
  base : bAddr b ix sc s = bAddr b ix sc t
  mem : ∀ o, F.mr.testBit o → s.mem (bAddr b ix sc s + BitVec.ofNat 64 o) = t.mem (bAddr b ix sc s + BitVec.ofNat 64 o)
  rd : s.rd = t.rd
  wr : s.wr = t.wr
  syms : s.syms = t.syms

/-- `s'` and `t'` agree on what `F` writes. -/
structure Writes (b : Reg) (ix : Option Reg) (sc : Nat) (F : Fp) (s' t' : State) : Prop where
  gpr : ∀ r : Reg, F.gw.testBit r.ctorIdx → s'.gpr r = t'.gpr r
  x : ∀ r : XReg, F.xw.testBit r.ctorIdx →
    s'.xmm r = t'.xmm r ∧ s'.ymmHi r = t'.ymmHi r ∧ s'.zmmHi r = t'.zmmHi r
  c : F.cw → s'.flags = t'.flags
  mem : ∀ o, F.mw.testBit o →
    s'.mem (bAddr b ix sc s' + BitVec.ofNat 64 o) = t'.mem (bAddr b ix sc s' + BitVec.ofNat 64 o)

/-- `s'` is `s` but for what `F` writes. -/
structure Frame (b : Reg) (ix : Option Reg) (sc : Nat) (F : Fp) (s s' : State) : Prop where
  gpr : ∀ r : Reg, F.gw.testBit r.ctorIdx = false → s'.gpr r = s.gpr r
  x : ∀ r : XReg, F.xw.testBit r.ctorIdx = false →
    s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r ∧ s'.zmmHi r = s.zmmHi r
  c : F.cw = false → s'.flags = s.flags
  mem : ∀ a, (∀ o, F.mw.testBit o → a ≠ bAddr b ix sc s + BitVec.ofNat 64 o) → s'.mem a = s.mem a
  ymmH : s'.ymmH = s.ymmH
  zmmHiH : s'.zmmHiH = s.zmmHiH
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unknowns : s'.unknowns = s.unknowns
  syms : s'.syms = s.syms

/-! ## Bits -/

theorem ctorIdx_inj {a c : Reg} (h : a.ctorIdx = c.ctorIdx) : a = c := by
  cases a <;> cases c <;> first | rfl | exact absurd h (by decide)

theorem xctorIdx_inj {a c : XReg} (h : a.ctorIdx = c.ctorIdx) : a = c := by
  cases a <;> cases c <;> first | rfl | exact absurd h (by decide)

@[simp] theorem testBit_gbit (r q : Reg) : (gbit r).testBit q.ctorIdx = decide (q = r) := by
  rw [gbit, Nat.testBit_two_pow]
  by_cases h : q = r
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not]
    exact fun e => h (ctorIdx_inj e.symm)

@[simp] theorem testBit_xbit (r q : XReg) : (xbit r).testBit q.ctorIdx = decide (q = r) := by
  rw [xbit, Nat.testBit_two_pow]
  by_cases h : q = r
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not]
    exact fun e => h (xctorIdx_inj e.symm)

theorem testBit_range (off n o : Nat) : (range off n).testBit o = decide (off ≤ o ∧ o < off + n) := by
  rw [range, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : off ≤ o
  · have : o - off < n ↔ o < off + n := by omega
    simp [h, this]
  · simp [h]

theorem only_gbit {d r : Reg} (h : (gbit d).testBit r.ctorIdx = true) : r = d := by simpa using h

theorem only_xbit {d r : XReg} (h : (xbit d).testBit r.ctorIdx = true) : r = d := by simpa using h

theorem testBit_or_left {a c i : Nat} (h : a.testBit i = true) : (a ||| c).testBit i = true := by
  simp [Nat.testBit_or, h]

theorem testBit_or_right {a c i : Nat} (h : c.testBit i = true) : (a ||| c).testBit i = true := by
  simp [Nat.testBit_or, h]

/-! ## States and memory -/

theorem state_ext {s t : State} (hg : s.gpr = t.gpr) (hc : s.flags = t.flags) (hx : s.xmm = t.xmm)
    (hy : s.ymmHi = t.ymmHi) (hz : s.zmmHi = t.zmmHi) (hyh : s.ymmH = t.ymmH) (hzh : s.zmmHiH = t.zmmHiH)
    (hmx : s.mxcsr = t.mxcsr) (hm : s.mem = t.mem) (hrd : s.rd = t.rd) (hwr : s.wr = t.wr)
    (hu : s.unknowns = t.unknowns) (hsy : s.syms = t.syms) : s = t := by
  cases s; cases t
  simp only [State.flags, Prod.mk.injEq] at hg hc hx hy hz hyh hzh hmx hm hrd hwr hu hsy
  obtain ⟨h1, h2, h3, h4⟩ := hc
  subst hg h1 h2 h3 h4 hx hy hz hyh hzh hmx hm hrd hwr hu hsy; rfl

theorem read_congr {m m' : Mem} {a : Addr} {n : Nat}
    (h : ∀ k < n, m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) : m.read a n = m'.read a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun k hk => by
      have := h (k + 1) (by omega)
      rwa [show a + BitVec.ofNat 64 (k + 1) = a + 1 + BitVec.ofNat 64 k by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega] at this]

theorem write_frame (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr)
    (h : ∀ k < n, x ≠ a + BitVec.ofNat 64 k) : m.write a n v x = m x := by
  simp only [Mem.write]
  rw [ite_eq_right_iff.mpr fun hk => absurd (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_comm, BitVec.sub_add_cancel]) (h _ hk)]

theorem write_at (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) {k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    m.write a n v (a + BitVec.ofNat 64 k) = v.extractLsb' (8 * k) 8 := by
  simp only [Mem.write]
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    ite_eq_left_iff.mpr fun h => absurd hk h]

theorem addr_ne {a : Addr} {o o' : Nat} (h : o ≠ o') (ho : o < 2 ^ 64) (ho' : o' < 2 ^ 64) :
    a + BitVec.ofNat 64 o ≠ a + BitVec.ofNat 64 o' := by
  intro e
  have e' : BitVec.ofNat 64 o = BitVec.ofNat 64 o' := by
    have := congrArg (fun x => x - a) e
    simpa only [BitVec.add_comm a, BitVec.add_sub_cancel] using this
  have := congrArg BitVec.toNat e'
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt ho'] at this
  exact h this

theorem memOff_ea {m : MemOp} {o : Nat} (h : memOff b ix sc m = some o) (s : State) :
    s.ea m = bAddr b ix sc s + BitVec.ofNat 64 o ∧ o < 65536 := by
  simp only [memOff] at h
  split at h
  · rename_i hc
    obtain ⟨hb, hi, hs, h0, h1⟩ := hc
    cases h
    refine ⟨?_, by omega⟩
    have hd : BitVec.ofInt 64 m.disp = BitVec.ofNat 64 m.disp.toNat := by
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
      rw [hn, Int.toNat_natCast, BitVec.ofInt_natCast]
    cases ix with
    | none => simp only [State.ea, hi, hb, bAddr, hd]
    | some i => simp only [State.ea, hi, hb, hs, bAddr, hd]
  · cases h

theorem bAddr_congr {s t : State} (h : ∀ r : Reg, (baseMask b ix).testBit r.ctorIdx → s.gpr r = t.gpr r) :
    bAddr b ix sc s = bAddr b ix sc t := by
  cases ix with
  | none =>
    simp only [bAddr]
    exact h b (by simp [baseMask])
  | some i =>
    simp only [bAddr]
    rw [h b (by simp [baseMask]), h i (by simp [baseMask, Nat.testBit_or])]


theorem bAddr_of_gpr {s s' : State} (h : s'.gpr = s.gpr) : bAddr b ix sc s' = bAddr b ix sc s := by
  cases ix <;> simp only [bAddr, h]

/-! ## Frames of the instructions' effects -/

theorem Frame.refl (F : Fp) (s : State) : Frame b ix sc F s s :=
  ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {F : Fp} {s s₁ s₂ : State} (h₁ : Frame b ix sc F s s₁) (h₂ : Frame b ix sc F s₁ s₂)
    (hb : bAddr b ix sc s₁ = bAddr b ix sc s) : Frame b ix sc F s s₂ where
  gpr r hr := (h₂.gpr r hr).trans (h₁.gpr r hr)
  x r hr := by
    obtain ⟨a₁, a₂, a₃⟩ := h₁.x r hr
    obtain ⟨b₁, b₂, b₃⟩ := h₂.x r hr
    exact ⟨b₁.trans a₁, b₂.trans a₂, b₃.trans a₃⟩
  c hc := (h₂.c hc).trans (h₁.c hc)
  mem a ha := (h₂.mem a (by rw [hb]; exact ha)).trans (h₁.mem a ha)
  ymmH := h₂.ymmH.trans h₁.ymmH
  zmmHiH := h₂.zmmHiH.trans h₁.zmmHiH
  mxcsr := h₂.mxcsr.trans h₁.mxcsr
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr
  unknowns := h₂.unknowns.trans h₁.unknowns
  syms := h₂.syms.trans h₁.syms

theorem Frame.setReg {F : Fp} {s : State} (d : Reg) (v : BitVec 64)
    (hd : F.gw.testBit d.ctorIdx = true) : Frame b ix sc F s (s.setReg d v) where
  gpr r hr := by
    have : r ≠ d := fun e => by rw [e, hd] at hr; exact Bool.noConfusion hr
    simp only [State.setReg, this, ite_false]
  x _ _ := ⟨rfl, rfl, rfl⟩
  c _ := rfl
  mem _ _ := rfl
  ymmH := rfl
  zmmHiH := rfl
  mxcsr := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl
  syms := rfl

theorem Frame.setFlags {F : Fp} {s : State} (hc : F.cw = true) (c o z n : Option Bool) :
    Frame b ix sc F s (s.setFlags c o z n) where
  gpr _ _ := rfl
  x _ _ := ⟨rfl, rfl, rfl⟩
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem _ _ := rfl
  ymmH := rfl
  zmmHiH := rfl
  mxcsr := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl
  syms := rfl

theorem Frame.arithReg {F : Fp} {s : State} {w : Nat} (d : Reg) (r : BitVec w) (c o : Bool) (v : BitVec 64)
    (hd : F.gw.testBit d.ctorIdx = true) (hc : F.cw = true) :
    Frame b ix sc F s ((arithFlags s r c o).setReg d v) :=
  (Frame.setFlags hc _ _ _ _).trans (Frame.setReg d v hd) (bAddr_of_gpr rfl)

theorem Frame.arith {F : Fp} {s : State} {w : Nat} (r : BitVec w) (c o : Bool) (hc : F.cw = true) :
    Frame b ix sc F s (arithFlags s r c o) :=
  Frame.setFlags hc _ _ _ _

theorem Frame.setV {F : Fp} {s : State} (len : VLen) (d : XReg) (lo hi : BitVec 128)
    (hd : F.xw.testBit d.ctorIdx = true) : Frame b ix sc F s (s.setV len d lo hi) where
  gpr _ _ := rfl
  x r hr := by
    have : r ≠ d := fun e => by rw [e, hd] at hr; exact Bool.noConfusion hr
    simp only [State.setV, this, ite_false, and_self]
  c _ := rfl
  mem _ _ := rfl
  ymmH := rfl
  zmmHiH := rfl
  mxcsr := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl
  syms := rfl

theorem Frame.store {F : Fp} {s : State} {o n : Nat} (v : BitVec (8 * n))
    (hm : ∀ k, k < n → F.mw.testBit (o + k) = true) :
    Frame b ix sc F s { s with mem := s.mem.write (bAddr b ix sc s + BitVec.ofNat 64 o) n v } where
  gpr _ _ := rfl
  x _ _ := ⟨rfl, rfl, rfl⟩
  c _ := rfl
  mem a ha := write_frame _ _ _ _ _ fun k hk e => ha (o + k) (hm k hk)
    (by rw [e, BitVec.add_assoc, BitVec.ofNat_add])
  ymmH := rfl
  zmmHiH := rfl
  mxcsr := rfl
  rd := rfl
  wr := rfl
  unknowns := rfl
  syms := rfl

theorem writeW_eq (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) :
    m.writeW a v = m.write a (w / 8) (v.setWidth (8 * (w / 8))) := rfl

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (readSrc s src).bind fun v => execAluW op d v s := by
  cases op <;> rfl

theorem execAluW_frame {F : Fp} {op : AluOp} {d : Reg} {v : BitVec 64} {s s' : State}
    (hd : F.gw.testBit d.ctorIdx = true) (hc : F.cw = true) (he : execAluW op d v s = some s') :
    Frame b ix sc F s s' := by
  cases op <;> simp only [execAluW, Option.some.injEq, Option.map_eq_some_iff] at he
  all_goals first
    | (subst he; first | exact Frame.arithReg _ _ _ _ _ hd hc | exact Frame.arith _ _ _ hc)
    | (obtain ⟨_, _, rfl⟩ := he; exact Frame.arithReg _ _ _ _ _ hd hc)


theorem testBit_range_add {o n k : Nat} (hk : k < n) : (range o n).testBit (o + k) = true := by
  simp [testBit_range]; omega

theorem VOp.frame {op : VOp} {F : Fp} (hf : VOp.fp op = some F) (s : State) :
    Frame b ix sc F s (op.exec s) := by
  cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at hf <;> subst hf <;>
    exact Frame.setV _ _ _ _ (by simp [vecFp])

theorem frame {i : Instr} {F : Fp} (hf : fp b ix sc i = some F) {s s' : State} (he : exec i s = some s') :
    Frame b ix sc F s s' := by
  cases i <;> simp only [fp, reduceCtorEq] at hf
  case mov d src =>
    cases src <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at hf
    · subst hf
      simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at he
      subst he; exact Frame.setReg _ _ (by simp [regFp])
    · subst hf
      simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at he
      subst he; exact Frame.setReg _ _ (by simp [regFp])
    · obtain ⟨o, _, rfl⟩ := hf
      simp only [reduceExec, readSrc, Option.map_eq_some_iff] at he
      obtain ⟨_, _, rfl⟩ := he
      exact Frame.setReg _ _ (by simp)
  case alu op d src =>
    simp only [Option.map_eq_some_iff, Prod.exists] at hf
    obtain ⟨g, mr, _, rfl⟩ := hf
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff] at he
    obtain ⟨v, _, he⟩ := he
    exact execAluW_frame (by simp) rfl he
  case andn d x y =>
    cases hf
    simp only [exec, execAndn, Option.some.injEq] at he
    subst he; exact Frame.arithReg _ _ _ _ _ (by simp) rfl
  case rorx d r n =>
    cases hf
    simp only [exec, execRorx] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he; exact Frame.setReg _ _ (by simp [regFp])
    · cases he
  case aluTbl op d m name ws =>
    cases hf
    simp only [reduceExec] at he
    split at he
    · exact execAluW_frame (by simp) rfl he
    · cases he
  case vop op =>
    simp only [exec, Option.some.injEq] at he
    subst he; exact VOp.frame hf s
  case vmovdquLoad len d m =>
    simp only [Option.map_eq_some_iff] at hf
    obtain ⟨o, _, rfl⟩ := hf
    cases len <;> simp only [exec, State.load128, State.load256] at he <;> split at he <;>
      first
      | (simp only [Option.map_some, Option.some.injEq] at he; subst he; exact Frame.setV _ _ _ _ (by simp))
      | cases he
  case vmovdquStore len m r =>
    simp only [Option.map_eq_some_iff] at hf
    obtain ⟨o, ho, rfl⟩ := hf
    obtain ⟨ea, -⟩ := memOff_ea ho s
    cases len <;> simp only [exec, State.store128, State.store256, ea] at he <;> split at he <;>
      first
      | (simp only [Option.some.injEq] at he; subst he; rw [writeW_eq]
         exact Frame.store _ fun k hk => testBit_range_add (by simp [lenBytes]; omega))
      | cases he


/-! ## Reads determine writes -/

theorem Reads.symm {F : Fp} {s t : State} (h : Reads b ix sc F s t) : Reads b ix sc F t s where
  gpr r hr := (h.gpr r hr).symm
  x r hr := ⟨(h.x r hr).1.symm, (h.x r hr).2.symm⟩
  c hc := (h.c hc).symm
  base := h.base.symm
  mem o ho := by rw [← h.base]; exact (h.mem o ho).symm
  rd := h.rd.symm
  wr := h.wr.symm
  syms := h.syms.symm

/-- What two runs of a footprint's instruction from states that agree on its reads share. -/
def Det (b : Reg) (ix : Option Reg) (sc : Nat) (i : Instr) (F : Fp) : Prop :=
  ∀ s t, Reads b ix sc F s t → ∀ s', exec i s = some s' → ∃ t', exec i t = some t' ∧ Writes b ix sc F s' t'

theorem Writes.of {F : Fp} {s' t' : State} (hg : ∀ r : Reg, F.gw.testBit r.ctorIdx → s'.gpr r = t'.gpr r)
    (hx : F.xw = 0) (hc : F.cw → s'.flags = t'.flags) (hm : F.mw = 0) : Writes b ix sc F s' t' where
  gpr := hg
  x r hr := by rw [hx] at hr; simp at hr
  c := hc
  mem o ho := by rw [hm] at ho; simp at ho

theorem read_eq {F : Fp} {s t : State} (h : Reads b ix sc F s t) {o n : Nat}
    (hr : ∀ k, k < n → F.mr.testBit (o + k) = true) :
    s.mem.read (bAddr b ix sc s + BitVec.ofNat 64 o) n = t.mem.read (bAddr b ix sc t + BitVec.ofNat 64 o) n := by
  rw [← h.base]
  refine read_congr fun k hk => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h.mem _ (hr k hk)

theorem readW_eq {F : Fp} {s t : State} (h : Reads b ix sc F s t) {o w : Nat}
    (hr : ∀ k, k < w / 8 → F.mr.testBit (o + k) = true) :
    s.mem.readW (bAddr b ix sc s + BitVec.ofNat 64 o) w = t.mem.readW (bAddr b ix sc t + BitVec.ofNat 64 o) w := by
  simp only [Mem.readW]; rw [read_eq h hr]

theorem ea_congr {s t : State} {m : MemOp} (h : ∀ r : Reg, (memIx m).testBit r.ctorIdx → s.gpr r = t.gpr r) :
    s.ea m = t.ea m := by
  have hb := h m.base (by simp [memIx, Nat.testBit_or])
  cases e : m.index with
  | none => simp only [State.ea, e, hb]
  | some i =>
    have hi := h i (by simp [memIx, e, Nat.testBit_or])
    simp only [State.ea, e, hb, hi]

theorem base_reads {F : Fp} {s t : State} (h : Reads b ix sc F s t) (hb : ∀ i, (baseMask b ix).testBit i → F.gr.testBit i) :
    ∀ r : Reg, (baseMask b ix).testBit r.ctorIdx → s.gpr r = t.gpr r :=
  fun r hr => h.gpr r (hb _ hr)

theorem readSrc_det {F : Fp} {s t : State} (h : Reads b ix sc F s t) {src : Src} {g mr : Nat}
    (hs : srcFp b ix sc src = some (g, mr)) (hg : ∀ i, g.testBit i → F.gr.testBit i)
    (hm : ∀ i, mr.testBit i → F.mr.testBit i) : readSrc s src = readSrc t src := by
  cases src with
  | reg r =>
    simp only [srcFp, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    simp only [readSrc, h.gpr r (hg _ (by simp))]
  | imm v => rfl
  | mem m =>
    simp only [srcFp, Option.map_eq_some_iff, Prod.mk.injEq] at hs
    obtain ⟨o, ho, rfl, rfl⟩ := hs
    obtain ⟨es, ho'⟩ := memOff_ea ho s
    obtain ⟨et, -⟩ := memOff_ea ho t
    simp only [readSrc, State.load64, es, et, ← h.base, ← h.rd, ← h.wr]
    split
    · have e := readW_eq (w := 64) h fun k hk => hm _ (testBit_range_add (by omega))
      rw [e, h.base]
    · rfl

theorem arith_flags {s t : State} {w : Nat} (r : BitVec w) (c o : Bool) :
    (arithFlags s r c o).flags = (arithFlags t r c o).flags := rfl

theorem execAluW_det {F : Fp} {op : AluOp} {d : Reg} {v : BitVec 64} {s t s' : State}
    (hgw : ∀ r : Reg, F.gw.testBit r.ctorIdx → r = d) (hx : F.xw = 0) (hm : F.mw = 0)
    (hd : s.gpr d = t.gpr d) (hc : readsCf op = true → s.cf = t.cf)
    (he : execAluW op d v s = some s') : ∃ t', execAluW op d v t = some t' ∧ Writes b ix sc F s' t' := by
  cases op <;> simp only [execAluW, Option.some.injEq, Option.map_eq_some_iff] at he ⊢
  all_goals first
    | (subst he
       exact ⟨_, rfl, Writes.of (fun r hr => by
          rw [hgw r hr]; simp only [State.setReg, arithFlags, State.setFlags, ite_true, hd])
        hx (fun _ => by simp only [State.flags, State.setReg, arithFlags, State.setFlags, hd]) hm⟩)
    | (obtain ⟨c, hcs, rfl⟩ := he
       rw [← hc rfl, hcs]
       exact ⟨_, ⟨c, rfl, rfl⟩, Writes.of (fun r hr => by
          rw [hgw r hr]; simp only [State.setReg, arithFlags, State.setFlags, ite_true, hd])
        hx (fun _ => by simp only [State.flags, State.setReg, arithFlags, State.setFlags, hd]) hm⟩)


theorem Writes.setReg {F : Fp} {s t : State} (d : Reg) (v : BitVec 64)
    (hF : ∀ r : Reg, F.gw.testBit r.ctorIdx → r = d) (hx : F.xw = 0) (hc : F.cw = false) (hm : F.mw = 0) :
    Writes b ix sc F (s.setReg d v) (t.setReg d v) :=
  Writes.of (fun r hr => by rw [hF r hr]; simp only [State.setReg, ite_true]) hx
    (fun h => by rw [hc] at h; exact Bool.noConfusion h) hm

theorem lanes_eq {F : Fp} {s t : State} (h : Reads b ix sc F s t) {r : XReg} (hr : F.xr.testBit r.ctorIdx = true) :
    s.lane r 0 = t.lane r 0 ∧ s.lane r 1 = t.lane r 1 := by
  simp only [State.lane, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false]
  exact h.x r hr

theorem Writes.setV {F : Fp} {s t : State} (len : VLen) (d : XReg) (lo hi : BitVec 128)
    (hF : ∀ r : XReg, F.xw.testBit r.ctorIdx → r = d) (hg : F.gw = 0) (hc : F.cw = false) (hm : F.mw = 0) :
    Writes b ix sc F (s.setV len d lo hi) (t.setV len d lo hi) where
  gpr r hr := by rw [hg] at hr; simp at hr
  x r hr := by rw [hF r hr]; simp only [State.setV, ite_true, and_self]
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem o ho := by rw [hm] at ho; simp at ho

theorem VOp.det {op : VOp} {F : Fp} (hf : VOp.fp op = some F) {s t : State} (h : Reads b ix sc F s t) :
    Writes b ix sc F (op.exec s) (op.exec t) := by
  cases op <;> simp only [VOp.fp, reduceCtorEq, Option.some.injEq] at hf <;> subst hf
  case vbin op len d x y =>
    obtain ⟨x0, x1⟩ := lanes_eq h (r := x) (by simp [vecFp, Nat.testBit_or])
    obtain ⟨y0, y1⟩ := lanes_eq h (r := y) (by simp [vecFp, Nat.testBit_or])
    simp only [reduceVOpExec, x0, x1, y0, y1]
    exact Writes.setV _ _ _ _ (fun r hr => only_xbit hr) rfl rfl rfl
  case vshift op len d x n =>
    obtain ⟨x0, x1⟩ := lanes_eq h (r := x) (by simp [vecFp])
    simp only [reduceVOpExec, x0, x1]
    exact Writes.setV _ _ _ _ (fun r hr => only_xbit hr) rfl rfl rfl
  case vpalignr len d x y n =>
    obtain ⟨x0, x1⟩ := lanes_eq h (r := x) (by simp [vecFp, Nat.testBit_or])
    obtain ⟨y0, y1⟩ := lanes_eq h (r := y) (by simp [vecFp, Nat.testBit_or])
    simp only [reduceVOpExec, x0, x1, y0, y1]
    exact Writes.setV _ _ _ _ (fun r hr => only_xbit hr) rfl rfl rfl

theorem store_writes {F : Fp} {s t : State} {o : Nat} {w : Nat} (v : BitVec w) (hw8 : w / 8 < 2 ^ 64)
    (hw : ∀ o', F.mw.testBit o' = true → o ≤ o' ∧ o' < o + w / 8)
    (hg : F.gw = 0) (hx : F.xw = 0) (hc : F.cw = false) (hb : bAddr b ix sc s = bAddr b ix sc t) :
    Writes b ix sc F { s with mem := s.mem.writeW (bAddr b ix sc s + BitVec.ofNat 64 o) v }
      { t with mem := t.mem.writeW (bAddr b ix sc t + BitVec.ofNat 64 o) v } where
  gpr r hr := by rw [hg] at hr; simp at hr
  x r hr := by rw [hx] at hr; simp at hr
  c h := by rw [hc] at h; exact Bool.noConfusion h
  mem o' ho := by
    obtain ⟨h1, h2⟩ := hw o' ho
    have e : bAddr b ix sc { s with mem := s.mem.writeW (bAddr b ix sc s + BitVec.ofNat 64 o) v } = bAddr b ix sc s :=
      bAddr_of_gpr rfl
    rw [e]
    simp only [writeW_eq]
    rw [← hb, show bAddr b ix sc s + BitVec.ofNat 64 o' = (bAddr b ix sc s + BitVec.ofNat 64 o) + BitVec.ofNat 64 (o' - o) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h1]]
    rw [write_at _ _ _ _ (by omega) hw8, write_at _ _ _ _ (by omega) hw8]

theorem det {i : Instr} {F : Fp} (hf : fp b ix sc i = some F) : Det b ix sc i F := by
  intro s t h s' he
  cases i <;> simp only [fp, reduceCtorEq] at hf
  case mov d src =>
    cases src <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at hf
    · subst hf
      simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at he ⊢
      subst he
      rw [h.gpr _ (by simp [regFp])]
      exact ⟨_, rfl, Writes.setReg _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    · subst hf
      simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at he ⊢
      subst he
      exact ⟨_, rfl, Writes.setReg _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    · rename_i m
      obtain ⟨o, ho, rfl⟩ := hf
      have e := readSrc_det (src := .mem m) h (g := baseMask b ix) (mr := range o 8)
        (by simp [srcFp, ho]) (fun _ h => h) (fun _ h => h)
      simp only [reduceExec] at he ⊢
      rw [← e]
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨v, hv, rfl⟩ := he
      exact ⟨_, by rw [hv]; rfl, Writes.setReg _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
  case alu op d src =>
    simp only [Option.map_eq_some_iff, Prod.exists] at hf
    obtain ⟨g, mr, hs, rfl⟩ := hf
    have e := readSrc_det h hs (fun _ hi => testBit_or_right hi) (fun _ hi => hi)
    simp only [reduceExec, execAlu_eq, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, he⟩ := he
    obtain ⟨t', ht, hw⟩ := execAluW_det (F := ⟨gbit d ||| g, gbit d, 0, 0, readsCf op, true, mr, 0⟩)
      (fun r hr => only_gbit hr) rfl rfl (h.gpr d (testBit_or_left (by simp)))
      (fun hc => congrArg Prod.fst (h.c hc)) he
    exact ⟨t', ⟨v, by rw [← e]; exact hv, ht⟩, hw⟩
  case andn d x y =>
    cases hf
    simp only [reduceExec, execAndn, Option.some.injEq] at he ⊢
    subst he
    rw [h.gpr x (by simp [Nat.testBit_or]), h.gpr y (by simp [Nat.testBit_or])]
    exact ⟨_, rfl, Writes.of (fun r hr => by rw [only_gbit hr]; simp only [State.setReg, ite_true]) rfl
      (fun _ => rfl) rfl⟩
  case rorx d r n =>
    cases hf
    simp only [reduceExec, execRorx] at he ⊢
    rw [← h.gpr r (by simp [regFp])]
    split at he
    · rename_i hn
      simp only [Option.some.injEq] at he
      subst he
      exact ⟨t.setReg d ((s.gpr r).rotateRight n), by simp only [hn, and_self, ↓reduceIte],
        Writes.setReg _ _ (fun r hr => only_gbit hr) rfl rfl rfl⟩
    · cases he
  case aluTbl op d m name ws =>
    cases hf
    have em := ea_congr (s := s) (t := t) (m := m) fun r hr => h.gpr r (testBit_or_right hr)
    have eb := h.gpr m.base (testBit_or_right (by simp [memIx, Nat.testBit_or]))
    simp only [reduceExec] at he ⊢
    split at he
    · rename_i hcond
      have hc' : t.gpr m.base = t.syms name ∧ (t.ea m - t.gpr m.base).toNat % 8 = 0 ∧
          (t.ea m - t.gpr m.base).toNat / 8 < ws.length := by
        rw [← em, ← eb, ← h.syms]; exact hcond
      obtain ⟨t', ht, hw⟩ := execAluW_det (F := ⟨gbit d ||| memIx m, gbit d, 0, 0, readsCf op, true, 0, 0⟩)
        (fun r hr => only_gbit hr) rfl rfl (h.gpr d (testBit_or_left (by simp)))
        (fun hc => congrArg Prod.fst (h.c hc)) he
      refine ⟨t', ?_, hw⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc'), ← em, ← eb]
      exact ht
    · cases he
  case vop op =>
    simp only [reduceExec, Option.some.injEq] at he ⊢
    subst he
    exact ⟨_, rfl, VOp.det hf h⟩
  case vmovdquLoad len d m =>
    simp only [Option.map_eq_some_iff] at hf
    obtain ⟨o, ho, rfl⟩ := hf
    obtain ⟨es, ho'⟩ := memOff_ea ho s
    obtain ⟨et, -⟩ := memOff_ea ho t
    have hin : ∀ n, InRegions (s.rd ++ s.wr) (s.ea m) n ↔ InRegions (t.rd ++ t.wr) (t.ea m) n := fun n => by
      rw [es, et, h.base, h.rd, h.wr]
    have e : ∀ w, w / 8 ≤ lenBytes len → s.mem.readW (s.ea m) w = t.mem.readW (t.ea m) w := fun w hw => by
      rw [es, et]; exact readW_eq h fun k hk => testBit_range_add (by omega)
    cases len <;> simp only [reduceExec, State.load128, State.load256] at he ⊢ <;> split at he <;>
      first
      | (rename_i hs
         simp only [Option.map_some, Option.some.injEq] at he
         subst he
         rw [e _ (by simp [lenBytes])]
         simp only [(hin _).mp hs, ↓reduceIte]
         exact ⟨_, rfl, Writes.setV _ _ _ _ (fun r hr => only_xbit hr) rfl rfl rfl⟩)
      | cases he
  case vmovdquStore len m r =>
    simp only [Option.map_eq_some_iff] at hf
    obtain ⟨o, ho, rfl⟩ := hf
    obtain ⟨es, ho'⟩ := memOff_ea ho s
    obtain ⟨et, -⟩ := memOff_ea ho t
    obtain ⟨x0, x1⟩ := h.x r (by simp)
    have hin : ∀ n, InRegions s.wr (bAddr b ix sc s + BitVec.ofNat 64 o) n →
        InRegions t.wr (bAddr b ix sc t + BitVec.ofNat 64 o) n := fun n hn => by
      rw [← h.base, ← h.wr]; exact hn
    cases len <;> simp only [reduceExec, State.store128, State.store256, State.ymm, es, et, x0, x1] at he ⊢ <;>
      split at he <;>
      first
      | (rename_i hs
         simp only [Option.some.injEq] at he
         subst he
         refine ⟨_, by rw [ite_eq_left_of_eq_true _ _ (eq_true (hin _ hs))], ?_⟩
         exact store_writes _ (by decide) (fun o' ho => by simp [testBit_range, lenBytes] at ho; omega)
           rfl rfl rfl h.base)
      | cases he


/-! ## Independent instructions commute -/

theorem and_zero {a c i : Nat} (h : a &&& c = 0) (ha : a.testBit i = true) : c.testBit i = false := by
  have := congrArg (·.testBit i) h
  simp only [Nat.testBit_and, ha, Bool.true_and, Nat.zero_testBit] at this
  exact this

theorem lt_pow {m o : Nat} (hm : m >>> 65536 = 0) (h : m.testBit o = true) : o < 2 ^ 64 := by
  have : o < 65536 := by
    by_contra hc
    have := Nat.testBit_shiftRight m (i := 65536) (j := o - 65536)
    rw [hm, Nat.zero_testBit, show 65536 + (o - 65536) = o by omega, h] at this
    exact Bool.noConfusion this
  omega

/-- What independence says, one location at a time. -/
structure Indep (bm : Nat) (F G : Fp) : Prop where
  gw_gr : ∀ i, F.gw.testBit i = true → G.gr.testBit i = false
  gw_gw : ∀ i, F.gw.testBit i = true → G.gw.testBit i = false
  gw_gr' : ∀ i, G.gw.testBit i = true → F.gr.testBit i = false
  xw_xr : ∀ i, F.xw.testBit i = true → G.xr.testBit i = false
  xw_xw : ∀ i, F.xw.testBit i = true → G.xw.testBit i = false
  xw_xr' : ∀ i, G.xw.testBit i = true → F.xr.testBit i = false
  cw : F.cw = true → G.cr = false ∧ G.cw = false
  cw' : G.cw = true → F.cr = false
  mw_mr : ∀ o, F.mw.testBit o = true → G.mr.testBit o = false
  mw_mw : ∀ o, F.mw.testBit o = true → G.mw.testBit o = false
  mw_mr' : ∀ o, G.mw.testBit o = true → F.mr.testBit o = false
  nb : ∀ i, bm.testBit i = true → F.gw.testBit i = false
  nb' : ∀ i, bm.testBit i = true → G.gw.testBit i = false
  fmr : ∀ o, F.mr.testBit o = true → o < 2 ^ 64
  fmw : ∀ o, F.mw.testBit o = true → o < 2 ^ 64
  gmr : ∀ o, G.mr.testBit o = true → o < 2 ^ 64
  gmw : ∀ o, G.mw.testBit o = true → o < 2 ^ 64

theorem Indep.of {bm : Nat} {F G : Fp} (h : F.indep bm G = true) : Indep bm F G := by
  simp only [Fp.indep, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => and_zero h2 hi, fun i hi => ?_, fun i hi => ?_,
    fun i hi => and_zero h4 hi, fun hc => ?_, fun hc => ?_, fun o ho => ?_, fun o ho => ?_,
    fun o ho => and_zero h8 ho, fun i hi => ?_, fun i hi => ?_, fun o ho => lt_pow h11 ho,
    fun o ho => lt_pow h12 ho, fun o ho => lt_pow h13 ho, fun o ho => lt_pow h14 ho⟩
  · have := and_zero h1 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h1 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2
  · have := and_zero h3 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h3 hi; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2
  · simp only [hc, Bool.true_and, Bool.or_eq_false_iff] at h5; exact h5
  · simp only [hc, Bool.true_and] at h6; exact h6
  · have := and_zero h7 ho; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
  · have := and_zero h7 ho; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.2
  · cases e : F.gw.testBit i
    · rfl
    · rw [and_zero h9 e] at hi; exact Bool.noConfusion hi
  · cases e : G.gw.testBit i
    · rfl
    · rw [and_zero h10 e] at hi; exact Bool.noConfusion hi

theorem Indep.symm {bm : Nat} {F G : Fp} (h : Indep bm F G) : Indep bm G F where
  gw_gr := h.gw_gr'
  gw_gw i hi := by
    cases e : F.gw.testBit i
    · rfl
    · rw [h.gw_gw _ e] at hi; exact Bool.noConfusion hi
  gw_gr' := h.gw_gr
  xw_xr := h.xw_xr'
  xw_xw i hi := by
    cases e : F.xw.testBit i
    · rfl
    · rw [h.xw_xw _ e] at hi; exact Bool.noConfusion hi
  xw_xr' := h.xw_xr
  cw hc := ⟨h.cw' hc, by
    cases e : F.cw
    · rfl
    · rw [(h.cw e).2] at hc; exact Bool.noConfusion hc⟩
  cw' hc := (h.cw hc).1
  mw_mr := h.mw_mr'
  mw_mw o ho := by
    cases e : F.mw.testBit o
    · rfl
    · rw [h.mw_mw _ e] at ho; exact Bool.noConfusion ho
  mw_mr' := h.mw_mr
  nb := h.nb'
  nb' := h.nb
  fmr := h.gmr
  fmw := h.gmw
  gmr := h.fmr
  gmw := h.fmw

theorem bAddr_frame {F : Fp} {s s' : State} (hn : ∀ i, (baseMask b ix).testBit i = true → F.gw.testBit i = false)
    (hfr : Frame b ix sc F s s') : bAddr b ix sc s' = bAddr b ix sc s :=
  bAddr_congr fun r hr => hfr.gpr r (hn _ hr)

/-- Running an instruction keeps what an independent footprint reads. -/
theorem reads_of_frame {F G : Fp} (hI : Indep (baseMask b ix) F G) {s s' : State} (hfr : Frame b ix sc F s s') :
    Reads b ix sc G s s' where
  gpr r hr := (hfr.gpr r (by
    cases e : F.gw.testBit r.ctorIdx
    · rfl
    · rw [hI.gw_gr _ e] at hr; exact Bool.noConfusion hr)).symm
  x r hr := by
    have := hfr.x r (by
      cases e : F.xw.testBit r.ctorIdx
      · rfl
      · rw [hI.xw_xr _ e] at hr; exact Bool.noConfusion hr)
    exact ⟨this.1.symm, this.2.1.symm⟩
  c hc := (hfr.c (by
    cases e : F.cw
    · rfl
    · rw [(hI.cw e).1] at hc; exact Bool.noConfusion hc)).symm
  base := (bAddr_frame hI.nb hfr).symm
  mem o ho := (hfr.mem _ fun o' ho' e => by
    have hne : o ≠ o' := fun h => by rw [h, hI.mw_mr _ ho'] at ho; exact Bool.noConfusion ho
    exact addr_ne hne (hI.gmr _ ho) (hI.fmw _ ho') e).symm
  rd := hfr.rd.symm
  wr := hfr.wr.symm
  syms := hfr.syms.symm

theorem exec_comm {i j : Instr} {F G : Fp} (hi : fp b ix sc i = some F) (hj : fp b ix sc j = some G)
    (hI : Indep (baseMask b ix) F G) (s : State) : (exec i s).bind (exec j) = (exec j s).bind (exec i) := by
  cases ei : exec i s with
  | none =>
    cases ej : exec j s with
    | none => rfl
    | some t1 =>
      simp only [Option.bind_none, Option.bind_some]
      cases e2 : exec i t1 with
      | none => rfl
      | some t2 =>
        obtain ⟨_, h, _⟩ := det hi t1 s (reads_of_frame hI.symm (frame hj ej)).symm t2 e2
        rw [ei] at h; cases h
  | some s1 =>
    cases ej : exec j s with
    | none =>
      simp only [Option.bind_none, Option.bind_some]
      cases e2 : exec j s1 with
      | none => rfl
      | some s2 =>
        obtain ⟨_, h, _⟩ := det hj s1 s (reads_of_frame hI (frame hi ei)).symm s2 e2
        rw [ej] at h; cases h
    | some t1 =>
      simp only [Option.bind_some]
      obtain ⟨s2, hs2, wG⟩ := det hj s s1 (reads_of_frame hI (frame hi ei)) t1 ej
      obtain ⟨t2, ht2, wF⟩ := det hi s t1 (reads_of_frame hI.symm (frame hj ej)) s1 ei
      rw [hs2, ht2]
      congr 1
      have f1 := frame hi ei
      have f2 := frame hj hs2
      have g1 := frame hj ej
      have g2 := frame hi ht2
      have x1 : bAddr b ix sc s1 = bAddr b ix sc s := bAddr_frame hI.nb f1
      have y1 : bAddr b ix sc t1 = bAddr b ix sc s := bAddr_frame hI.nb' g1
      have x2 : bAddr b ix sc s2 = bAddr b ix sc s := (bAddr_frame hI.nb' f2).trans x1
      have y2 : bAddr b ix sc t2 = bAddr b ix sc s := (bAddr_frame hI.nb g2).trans y1
      have hxv : ∀ r : XReg, s2.xmm r = t2.xmm r ∧ s2.ymmHi r = t2.ymmHi r ∧ s2.zmmHi r = t2.zmmHi r := by
        intro r
        cases hF : F.xw.testBit r.ctorIdx
        · cases hG : G.xw.testBit r.ctorIdx
          · obtain ⟨a1, a2, a3⟩ := f2.x r hG
            obtain ⟨b1, b2, b3⟩ := f1.x r hF
            obtain ⟨c1, c2, c3⟩ := g2.x r hF
            obtain ⟨d1, d2, d3⟩ := g1.x r hG
            exact ⟨by rw [a1, b1, c1, d1], by rw [a2, b2, c2, d2], by rw [a3, b3, c3, d3]⟩
          · obtain ⟨w1, w2, w3⟩ := wG.x r hG
            obtain ⟨c1, c2, c3⟩ := g2.x r hF
            exact ⟨by rw [← w1, c1], by rw [← w2, c2], by rw [← w3, c3]⟩
        · obtain ⟨a1, a2, a3⟩ := f2.x r (hI.xw_xw _ hF)
          obtain ⟨w1, w2, w3⟩ := wF.x r hF
          exact ⟨by rw [a1, w1], by rw [a2, w2], by rw [a3, w3]⟩
      apply state_ext
      · funext r
        cases hF : F.gw.testBit r.ctorIdx
        · cases hG : G.gw.testBit r.ctorIdx
          · rw [f2.gpr r hG, f1.gpr r hF, g2.gpr r hF, g1.gpr r hG]
          · rw [← wG.gpr r hG, g2.gpr r hF]
        · rw [f2.gpr r (hI.gw_gw _ hF), wF.gpr r hF]
      · cases hF : F.cw
        · cases hG : G.cw
          · rw [f2.c hG, f1.c hF, g2.c hF, g1.c hG]
          · rw [← wG.c hG, g2.c hF]
        · rw [f2.c (hI.cw hF).2, wF.c hF]
      · funext r; exact (hxv r).1
      · funext r; exact (hxv r).2.1
      · funext r; exact (hxv r).2.2
      · rw [f2.ymmH, f1.ymmH, g2.ymmH, g1.ymmH]
      · rw [f2.zmmHiH, f1.zmmHiH, g2.zmmHiH, g1.zmmHiH]
      · rw [f2.mxcsr, f1.mxcsr, g2.mxcsr, g1.mxcsr]
      · funext a
        by_cases hx : ∃ o, F.mw.testBit o = true ∧ a = bAddr b ix sc s + BitVec.ofNat 64 o
        · obtain ⟨o, ho, rfl⟩ := hx
          have hFG : ∀ o', G.mw.testBit o' = true → o ≠ o' := fun o' ho' h => by
            subst h; rw [hI.mw_mw _ ho] at ho'; exact Bool.noConfusion ho'
          rw [f2.mem _ fun o' ho' e => addr_ne (hFG o' ho') (hI.fmw _ ho) (hI.gmw _ ho') (by rw [e, x1]),
            ← x1, wF.mem o ho, x1, ← y2]
        · by_cases hy : ∃ o, G.mw.testBit o = true ∧ a = bAddr b ix sc s + BitVec.ofNat 64 o
          · obtain ⟨o, ho, rfl⟩ := hy
            have hGF : ∀ o', F.mw.testBit o' = true → o ≠ o' := fun o' ho' h => by
              subst h; rw [hI.symm.mw_mw _ ho] at ho'; exact Bool.noConfusion ho'
            rw [g2.mem _ fun o' ho' e => addr_ne (hGF o' ho') (hI.gmw _ ho) (hI.fmw _ ho') (by rw [e, y1])]
            have w := wG.mem o ho
            rw [y1] at w
            exact w.symm
          · have nF : ∀ o, F.mw.testBit o = true → a ≠ bAddr b ix sc s + BitVec.ofNat 64 o :=
              fun o ho e => hx ⟨o, ho, e⟩
            have nG : ∀ o, G.mw.testBit o = true → a ≠ bAddr b ix sc s + BitVec.ofNat 64 o :=
              fun o ho e => hy ⟨o, ho, e⟩
            rw [f2.mem a (by rw [x1]; exact nG), f1.mem a nF, g2.mem a (by rw [y1]; exact nF), g1.mem a nG]
      · rw [f2.rd, f1.rd, g2.rd, g1.rd]
      · rw [f2.wr, f1.wr, g2.wr, g1.wr]
      · rw [f2.unknowns, f1.unknowns, g2.unknowns, g1.unknowns]
      · rw [f2.syms, f1.syms, g2.syms, g1.syms]


/-! ## The instance -/

theorem indep_union_left {bm : Nat} {A B C : Fp} (h : (A.union B).indep bm C = true) :
    A.indep bm C = true ∧ B.indep bm C = true := by
  simp only [Fp.indep, Fp.union, Nat.and_or_distrib_right, Nat.and_or_distrib_left, Nat.or_eq_zero_iff,
    Nat.shiftRight_or_distrib, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff] at h ⊢
  grind

theorem indep_union_right {bm : Nat} {A B C : Fp} (h : A.indep bm (B.union C) = true) :
    A.indep bm B = true ∧ A.indep bm C = true := by
  simp only [Fp.indep, Fp.union, Nat.and_or_distrib_right, Nat.and_or_distrib_left, Nat.or_eq_zero_iff,
    Nat.shiftRight_or_distrib, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff] at h ⊢
  grind

variable (b ix sc) in
/-- The footprints of the class, for memory at `[b + ix * sc + disp]`. -/
def footprints : Footprints isa where
  Fp := Fp
  fp := fp b ix sc
  Inv _ := True
  preserves _ _ _ _ _ := trivial
  empty := .empty
  union := Fp.union
  indep := Fp.indep (baseMask b ix)
  indep_union_left := indep_union_left
  indep_union_right := indep_union_right
  comm hx hy h s _ := exec_comm hx hy (Indep.of h) s

end

end VG.X86_64.Interleave
