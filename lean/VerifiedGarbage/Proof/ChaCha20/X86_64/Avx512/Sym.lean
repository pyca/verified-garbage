module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ChaCha20 on x86-64 with AVX-512: straight-line code, doubleword by doubleword

Outside the rounds, every instruction of the code moves, adds or XORs
doublewords of `zmm` registers and of three regions of memory: the state (at
`rdi`), `buf` (at `rcx`) and 1024 bytes of data (at `rsi`). `Sym.run` computes
each doubleword after a block of such instructions as a term (`T`) in the
doublewords before it, and `srun_ok` proves the machine agrees; the terms
themselves are then compared by the kernel.

From a source to a destination (`to`, `Sym.runT`, `SRelT`), the data at
`rsi` is the source, which the code only reads, and the destination, at
`rsi + r11`, is a fourth region (`dstR`), which it only writes: the source
itself (in place, `r11 = 0`) or apart from it. A load from the source is
allowed only of doublewords whose destination's are as on entry, so that it
reads what the source held on entry in either case. The definitions of the
destination (`dstR`, `slotD`, `Ctx3`, `src_keep`) serve the last bytes'
code too (`Avx512Tail`, `Avx2Tail`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word)

/-- The base register of region `b`: the state, `buf` and the data. -/
def baseR : Nat → Reg
  | 0 => .rdi | 1 => .rcx | _ => .rsi

/-- The doublewords of region `b`. -/
def bsize : Nat → Nat
  | 0 => 16 | 1 => 80 | _ => 256

/-- The doublewords of region `b` that may be written: the saved registers in
`buf`, and the data. -/
def wsize : Nat → Nat
  | 0 => 0 | 1 => 32 | _ => 256

def bidx : Reg → Option Nat
  | .rdi => some 0 | .rcx => some 1 | .rsi => some 2 | _ => none

theorem bidx_some {r : Reg} {b : Nat} (h : bidx r = some b) : r = baseR b ∧ b < 3 := by
  cases r <;> simp only [bidx, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> decide

/-- Region `b`, where the code starts. -/
def regn (s₀ : State) (b : Nat) : Region := ⟨s₀.gpr (baseR b), 4 * bsize b⟩

/-- The regions written. -/
def wregs (s₀ : State) : List Region := [⟨s₀.gpr .rcx, 128⟩, ⟨s₀.gpr .rsi, 1024⟩]

/-- The destination of `D` doublewords of data from a source to a
destination: at `rsi + r11`. -/
def dstR (D : Nat) (s₀ : State) : Region := ⟨s₀.gpr .rsi + s₀.gpr .r11, 4 * D⟩

/-- Where region `b` starts: the destination is region 3. -/
def memBase (s₀ : State) (b : Nat) : Addr := if b = 3 then (dstR 256 s₀).base else (regn s₀ b).base

theorem memBase_lt {s₀ : State} {b : Nat} (hb : b < 3) : memBase s₀ b = (regn s₀ b).base := by
  simp only [memBase, show b ≠ 3 by omega, ite_false]
theorem memBase_0 (s₀ : State) : memBase s₀ 0 = s₀.gpr .rdi := rfl
theorem memBase_1 (s₀ : State) : memBase s₀ 1 = s₀.gpr .rcx := rfl
theorem memBase_2 (s₀ : State) : memBase s₀ 2 = s₀.gpr .rsi := rfl
theorem memBase_3 (s₀ : State) : memBase s₀ 3 = (dstR 256 s₀).base := rfl

/-- A doubleword, from the doublewords where the code starts. -/
inductive T
  /-- Doubleword `p` of `zmm r`. -/
  | reg (r p : Nat)
  /-- Doubleword `i` of region `b` (3: the destination). -/
  | mem (b i : Nat)
  | add (a b : T)
  | xor (a b : T)
  /-- Doubleword `i` of the input of `vg_chacha20_xor_split`'s pass
  (`Avx512Split.lean`): of `src` (at `r8`) if its block ends within the
  first `r10` bytes, else of the data (at `rsi`). -/
  | inp (i : Nat)
  deriving DecidableEq

/-- Doubleword `i` of the input of a pass of `vg_chacha20_xor_split`. -/
def inpW (s₀ : State) (i : Nat) : Word :=
  if 64 * (i / 16) + 64 ≤ (s₀.gpr .r10).toNat then s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (4 * i)) 32
  else s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (4 * i)) 32

def T.eval (s₀ : State) : T → Word
  | .reg r p => zw s₀ (zreg r) p
  | .mem b i => s₀.mem.readW (memBase s₀ b + BitVec.ofNat 64 (4 * i)) 32
  | .inp i => inpW s₀ i
  | .add a b => a.eval s₀ + b.eval s₀
  | .xor a b => a.eval s₀ ^^^ b.eval s₀

/-- The doublewords of the registers (by `xidx`) and regions, as terms. -/
structure Sym where
  reg : Nat → Nat → T
  mem : Nat → Nat → T
  /-- Whether memory may have been written. -/
  dirty : Bool

def Sym.init : Sym := ⟨.reg, .mem, false⟩

def Sym.setReg (σ : Sym) (d : Nat) (f : Nat → T) : Sym :=
  { σ with reg := fun r p => if r = d then f p else σ.reg r p }

/-- A store of `σ.reg r` to doublewords `i, …, i + n - 1` of region `b`. -/
def symStore (σ : Sym) (b i n r : Nat) : Sym :=
  { σ with
    mem := fun b' i' => if b' = b ∧ i ≤ i' ∧ i' < i + n then σ.reg r (i' - i) else σ.mem b' i'
    dirty := true }

/-- Whether doublewords `i, …, i + n - 1` of the destination are as on entry. -/
def clean3 (σ : Sym) (i n : Nat) : Bool := (List.range n).all fun p => σ.mem 3 (i + p) == .mem 3 (i + p)

/-- The first doubleword of an access of `n` doublewords of the destination
at `m` (`[rsi + r11 + d]`), within its `D`. -/
def slotD (m : MemOp) (n D : Nat) : Option Nat :=
  match m.base, m.index, m.scale, m.disp with
  | .rsi, some .r11, 1, .ofNat d => if d % 4 = 0 ∧ d / 4 + n ≤ D then some (d / 4) else none
  | _, _, _, _ => none

/-- The two-bit field `i` of `o`. -/
def sel2 (o i : Nat) : Nat := o / 4 ^ i % 4

/-- Whether `zbinT` represents doubleword `p` of `op a b` as a term in
doublewords of `a` and `b`. Only its supported operations are accepted. -/
def dwordwise : ZBinOp → Bool
  | .vpaddd | .vpxord | .vpunpckldq | .vpunpckhdq | .vpunpcklqdq | .vpunpckhqdq => true
  | _ => false

/-- Doubleword `p` of `op a b`, for an operation that is `dwordwise`. -/
def zbinT (op : ZBinOp) (A B : Nat → T) (p : Nat) : T :=
  match op with
  | .vpaddd => .add (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpxord => .xor (A (4 * (p / 4) + p % 4)) (B (4 * (p / 4) + p % 4))
  | .vpunpckldq => if p % 4 % 2 = 0 then A (4 * (p / 4) + p % 4 / 2) else B (4 * (p / 4) + p % 4 / 2)
  | .vpunpckhdq =>
    if p % 4 % 2 = 0 then A (4 * (p / 4) + (2 + p % 4 / 2)) else B (4 * (p / 4) + (2 + p % 4 / 2))
  | .vpunpcklqdq => if p % 4 < 2 then A (4 * (p / 4) + p % 4) else B (4 * (p / 4) + (p % 4 - 2))
  | .vpunpckhqdq => if p % 4 < 2 then A (4 * (p / 4) + (2 + p % 4)) else B (4 * (p / 4) + p % 4)
  | _ => .reg 0 0

/-- The region and first doubleword of an access of `n` doublewords, within
the first `lim b` doublewords of its region `b`. -/
def slot (m : MemOp) (n : Nat) (lim : Nat → Nat) : Option (Nat × Nat) :=
  match bidx m.base, m.index, m.disp with
  | some b, none, .ofNat d => if d % 4 = 0 ∧ d / 4 + n ≤ lim b then some (b, d / 4) else none
  | _, _, _ => none

/-- The doublewords of region `b` that may be written, from a source to a
destination (`to`): only `buf`'s, the destination being region 3. -/
def wsizeT : Bool → Nat → Nat
  | false, b => wsize b
  | true, b => if b = 1 then wsize 1 else 0

def Sym.stepT (to : Bool) (σ : Sym) : Instr → Option Sym
  | .zop (.zbin op d a b) =>
    if dwordwise op then some (σ.setReg (xidx d) (zbinT op (σ.reg (xidx a)) (σ.reg (xidx b)))) else none
  | .zop (.vpshufd d a o) =>
    some (σ.setReg (xidx d) fun p => σ.reg (xidx a) (4 * (p / 4) + sel2 o.toNat (p % 4)))
  | .zop (.vshufi32x4 d a b n) =>
    some (σ.setReg (xidx d) fun p =>
      (if p / 4 < 2 then σ.reg (xidx a) else σ.reg (xidx b)) (4 * sel2 n.toNat (p / 4) + p % 4))
  | .vmovdqu32Load d m => (slot m 16 bsize).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 16 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p))
  | .vbroadcasti32x4 d m => (slot m 4 bsize).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 4 = false then none
    else some (σ.setReg (xidx d) fun p => σ.mem b (i + p % 4))
  | .vmovdqu32Store m r =>
    match (if to then slotD m 16 256 else none) with
    | some i => some (symStore σ 3 i 16 (xidx r))
    | none => (slot m 16 (wsizeT to)).map fun (b, i) => symStore σ b i 16 (xidx r)
  | .vpbroadcastdZ d m => (slot m 1 bsize).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 1 = false then none
    else some (σ.setReg (xidx d) fun _ => σ.mem b i)
  | .zbcstd .vpaddd d a m => (slot m 1 bsize).bind fun (b, i) =>
    if to = true ∧ b = 2 ∧ clean3 σ i 1 = false then none
    else some (σ.setReg (xidx d) fun p => .add (σ.reg (xidx a) p) (σ.mem b i))
  | _ => none

def Sym.runT (to : Bool) (σ : Sym) : List Instr → Option Sym
  | [] => some σ
  | i :: is => (σ.stepT to i).bind fun σ' => σ'.runT to is

/-- In place. -/
abbrev Sym.run (σ : Sym) := σ.runT false

/-! ## The machine agrees -/

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toInt_eq; simp

theorem add_ofNat' (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem slot_ok {m : MemOp} {n : Nat} {lim : Nat → Nat} {b i : Nat} (h : slot m n lim = some (b, i)) :
    b < 3 ∧ i + n ≤ lim b ∧ ∀ s : State, s.ea m = s.gpr (baseR b) + BitVec.ofNat 64 (4 * i) := by
  unfold slot at h
  split at h
  · rename_i b' d hb hi hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hb3⟩ := bidx_some hb
      refine ⟨hb3, hc.2, fun s => ?_⟩
      simp only [State.ea, hi, hd, ofInt_ofNat, ← e]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1)]
    · cases h
  · cases h

theorem bsize_le (b : Nat) : bsize b ≤ 256 := by
  unfold bsize; split <;> decide

theorem wsize_le (b : Nat) : wsize b ≤ bsize b := by
  unfold wsize bsize; split <;> decide

theorem regn_contains (s₀ : State) {b i n : Nat} (h : i + n ≤ bsize b) :
    (regn s₀ b).Contains ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  have := bsize_le b
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat _ (by omega)]
  simp only [regn]; omega

/-- The regions: writable (and so readable) and disjoint. -/
structure Ctx (s₀ : State) : Prop where
  w : ∀ b i n, b < 3 → i + n ≤ bsize b →
    InRegions s₀.wr ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : ∀ b b', b < 3 → b' < 3 → b ≠ b' → (regn s₀ b).Disjoint (regn s₀ b')

theorem slotD_ok {m : MemOp} {n D i : Nat} (h : slotD m n D = some i) :
    i + n ≤ D ∧ ∀ s : State, s.ea m = (s.gpr .rsi + s.gpr .r11) + BitVec.ofNat 64 (4 * i) := by
  unfold slotD at h
  split at h
  · rename_i d hb hi hsc hd
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨hc.2, fun s => ?_⟩
      simp only [State.ea, hb, hi, hsc, hd, ofInt_ofNat, BitVec.mul_one]
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1)]
    · cases h
  · cases h

theorem clean3_of {σ : Sym} {i n : Nat} (h : clean3 σ i n = true) {p : Nat} (hp : p < n) :
    σ.mem 3 (i + p) = .mem 3 (i + p) := by
  simp only [clean3, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h p hp

/-- The source and the destination of `D` doublewords, the source in region
`2` of `R` and the others of `R` the state and `buf`: what the code may do
with them. -/
structure Ctx3 (R : Nat → Region) (D : Nat) (s₀ : State) : Prop where
  src : ∀ i n, i + n ≤ D → 0 < n →
    InRegions (s₀.rd ++ s₀.wr) ((R 2).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  w : ∀ i n, i + n ≤ D → 0 < n → InRegions s₀.wr ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : ∀ b, b < 2 → (R b).Disjoint (dstR D s₀) ∧ (R b).Disjoint (R 2)
  al : s₀.gpr .r11 = 0 ∨ (R 2).Disjoint (dstR D s₀)

/-- From a source to a destination: the source where its destination is as
on entry is as on entry (in place, as the destination; apart, outside the
regions written, the destination and `B`, within `buf`). -/
theorem src_keep {R : Nat → Region} {D : Nat} {s₀ : State} (hc3 : Ctx3 R D s₀) (h2 : (R 2).base = s₀.gpr .rsi)
    {B : Region} (hB : Region.Sub B (R 1)) {t : Mem} (hf : Frame [B, dstR D s₀] s₀.mem t) {i : Nat}
    (hin : (R 2).Contains ((R 2).base + BitVec.ofNat 64 (4 * i)) (4 * 1))
    (h3 : t.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32 =
      s₀.mem.readW ((dstR D s₀).base + BitVec.ofNat 64 (4 * i)) 32) :
    t.readW ((R 2).base + BitVec.ofNat 64 (4 * i)) 32 = s₀.mem.readW ((R 2).base + BitVec.ofNat 64 (4 * i)) 32 := by
  rcases hc3.al with h0 | hdis
  · have e : (dstR D s₀).base = (R 2).base := by
      simp only [dstR, h2, h0]; exact BitVec.add_zero _
    rw [e] at h3; exact h3
  · refine hf.readW hin ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hc3.d 1 (by decide)).2.symm).sub_right hB
    · exact hdis

/-- From a source to a destination: the state and `buf`, writable (and so
readable) and disjoint. -/
structure Ctx01 (s₀ : State) : Prop where
  w : ∀ b i n, b < 2 → i + n ≤ bsize b →
    InRegions s₀.wr ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n)
  d : (regn s₀ 0).Disjoint (regn s₀ 1)

/-- The regions, in place or from a source to a destination (`to`). -/
def CtxT : Bool → State → Prop
  | false, s₀ => Ctx s₀
  | true, s₀ => Ctx01 s₀ ∧ Ctx3 (regn s₀) 256 s₀

/-- The regions written. -/
def wregsT : Bool → State → List Region
  | false, s₀ => wregs s₀
  | true, s₀ => [⟨s₀.gpr .rcx, 128⟩, dstR 256 s₀]

/-- The terms `σ` hold in `s`: in the registers, and in regions 0 to 2 (from
a source to a destination, in the source where its destination is as on
entry) and the destination. -/
structure SRelT (to : Bool) (σ : Sym) (s₀ s : State) : Prop where
  reg : ∀ r p, p < 16 → zw s r p = (σ.reg (xidx r) p).eval s₀
  mem : ∀ b i, b < 3 → i < bsize b → (to = true → b = 2 → σ.mem 3 i = .mem 3 i) →
    s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem b i).eval s₀
  mem3 : to = true → ∀ i < 256,
    s.mem.readW ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem 3 i).eval s₀
  src : to = true → ∀ i, σ.mem 2 i = .mem 2 i
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (wregsT to s₀) s₀.mem s.mem
  clean : σ.dirty = false → s.mem = s₀.mem

/-- In place. -/
abbrev SRel := SRelT false

theorem SRel.mem {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) :
    ∀ b i, b < 3 → i < bsize b →
      s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem b i).eval s₀ :=
  fun b i hb hi => SRelT.mem h b i hb hi (fun e => nomatch e)

/-- In place, from what `SRelT` asks of the registers and the regions. -/
theorem SRel.mk' {σ : Sym} {s₀ s : State} (hr : ∀ r p, p < 16 → zw s r p = (σ.reg (xidx r) p).eval s₀)
    (hm : ∀ b i, b < 3 → i < bsize b →
      s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem b i).eval s₀)
    (hg : s.gpr = s₀.gpr) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame (wregs s₀) s₀.mem s.mem)
    (hc : σ.dirty = false → s.mem = s₀.mem) : SRel σ s₀ s :=
  ⟨hr, fun b i hb hi _ => hm b i hb hi, (fun e => nomatch e), (fun e => nomatch e), hg, hrd, hwr, hf, hc⟩

theorem zreg_xidx (r : XReg) : zreg (xidx r) = r := by cases r <;> rfl

theorem SRelT.init (to : Bool) (s₀ : State) : SRelT to Sym.init s₀ s₀ :=
  ⟨fun r p _ => by simp only [Sym.init, T.eval, zreg_xidx],
   fun b i hb _ _ => by simp only [Sym.init, T.eval, memBase_lt hb],
   fun _ i _ => by simp only [Sym.init, T.eval, memBase_3],
   fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ => rfl⟩

theorem SRel.init (s₀ : State) : SRel Sym.init s₀ s₀ := SRelT.init false s₀

theorem SRelT.setReg {to : Bool} {σ : Sym} {s₀ s s' : State} (h : SRelT to σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 16 → zw s' r p = if r = d then (f p).eval s₀ else zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRelT to (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨fun r p hp => ?_, fun b i hb hi hc => by rw [hm]; exact h.mem b i hb hi hc,
    fun ht i hi => by rw [hm]; exact h.mem3 ht i hi, h.src, hg.trans h.gpr,
    hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩
  rw [hz r p hp]
  simp only [Sym.setReg, xidx_inj]
  split
  · rfl
  · exact h.reg r p hp

theorem SRel.setReg {σ : Sym} {s₀ s s' : State} (h : SRel σ s₀ s) {d : XReg} {f : Nat → T}
    (hz : ∀ r p, p < 16 → zw s' r p = if r = d then (f p).eval s₀ else zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) :
    SRel (σ.setReg (xidx d) f) s₀ s' :=
  SRelT.setReg h hz hm hg hr hw

/-! ### Lane operations -/

theorem zw_split {s : State} {r : XReg} {p : Nat} : zw s r p = dword (s.zlane r (p / 4)) (p % 4) := rfl

theorem zbinT_eval {op : ZBinOp} (hop : dwordwise op = true) {A B : Nat → T} {s₀ : State}
    {x y : BitVec 128} {p : Nat}
    (hA : ∀ k, k < 4 → (A (4 * (p / 4) + k)).eval s₀ = dword x k)
    (hB : ∀ k, k < 4 → (B (4 * (p / 4) + k)).eval s₀ = dword y k) :
    (zbinT op A B p).eval s₀ = dword (op.sse.eval x y) (p % 4) := by
  have hq : p % 4 < 4 := Nat.mod_lt _ (by decide)
  simp only [zbinT]
  generalize p % 4 = q at *
  generalize 4 * (p / 4) = l at *
  have a0 := hA 0 (by decide); have a1 := hA 1 (by decide)
  have a2 := hA 2 (by decide); have a3 := hA 3 (by decide)
  have b0 := hB 0 (by decide); have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide); have b3 := hB 3 (by decide)
  rcases cases4 hq with rfl | rfl | rfl | rfl <;> cases op <;> (try cases hop) <;>
    simp only [ZBinOp.sse, T.eval, dword_paddd _ _ (show (0 : Nat) < 4 by decide),
      dword_paddd _ _ (show (1 : Nat) < 4 by decide), dword_paddd _ _ (show (2 : Nat) < 4 by decide),
      dword_paddd _ _ (show (3 : Nat) < 4 by decide), dword_pxor, dword_punpckldq, dword_punpckhdq,
      punpcklqdq_eq, punpckhqdq_eq, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
      dword_ofDwords_3, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
      ite_true, ite_false, a0, a1, a2, a3, b0, b1, b2, b3]

theorem zw_lk (s : State) (r : XReg) {l k : Nat} (hk : k < 4) :
    zw s r (4 * l + k) = dword (s.zlane r l) k := by
  simp only [zw_split]; rw [show (4 * l + k) / 4 = l by omega, show (4 * l + k) % 4 = k by omega]

theorem sel2_eq (o : BitVec 8) (i : Nat) : (o.extractLsb' (2 * i) 2).toNat = sel2 o.toNat i := by
  simp only [BitVec.extractLsb'_toNat, sel2, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem sel2_lt (o i : Nat) : sel2 o i < 4 := Nat.mod_lt _ (by decide)

theorem pick4_same (v : BitVec 128) {i : Nat} (hi : i < 4) : pick4 v v v v i = v := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

theorem dword_rep4 (v : BitVec 32) {k : Nat} (hk : k < 4) : dword (v ++ v ++ v ++ v) k = v := by
  change dword (ofDwords v v v v) k = v
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp

theorem pick4_fn (f : Nat → BitVec 128) {l : Nat} (hl : l < 4) : pick4 (f 0) (f 1) (f 2) (f 3) l = f l := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem pick4_ext (v : BitVec 512) {l : Nat} (hl : l < 4) :
    pick4 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128) l =
      v.extractLsb' (128 * l) 128 := by
  rcases cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem dword_read512 (m : Mem) (a : Addr) {p : Nat} (hp : p < 16) :
    dword ((m.readW a 512).extractLsb' (128 * (p / 4)) 128) (p % 4) =
      m.readW (a + BitVec.ofNat 64 (4 * p)) 32 := by
  rw [dword, extract_extract _ _ _ _ _ (by omega), show 128 * (p / 4) + 32 * (p % 4) = 8 * (4 * p) by omega]
  exact readW_extract m a (w := 512) (k := 4 * p) (n := 4) (by omega)

theorem in_regn {s₀ s : State} (hc : Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ bsize b) : InRegions s.wr ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  hw ▸ hc.w b i n hb h

theorem in_regn' {s₀ s : State} (hc : Ctx s₀) {b : Nat} (hb : b < 3) (hw : s.wr = s₀.wr) {i n : Nat}
    (h : i + n ≤ bsize b) : InRegions (s.rd ++ s.wr) ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) :=
  let ⟨r, hr, hc'⟩ := in_regn hc hb hw h; ⟨r, List.mem_append_right _ hr, hc'⟩

/-- Reads of regions 0 to 2 are permitted. -/
theorem CtxT.rd {to : Bool} {s₀ s : State} (hc : CtxT to s₀) {b : Nat} (hb : b < 3)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {i n : Nat} (h : i + n ≤ bsize b) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (4 * n) := by
  cases to
  · exact in_regn' hc hb hw h
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl
    · obtain ⟨r, hr', hc'⟩ := hc.1.w 0 i n (by decide) h
      exact ⟨r, List.mem_append_right _ (by rw [hw]; exact hr'), hc'⟩
    · obtain ⟨r, hr', hc'⟩ := hc.1.w 1 i n (by decide) h
      exact ⟨r, List.mem_append_right _ (by rw [hw]; exact hr'), hc'⟩
    · rw [hr, hw]; exact hc.2.src i n h hn

/-- Doubleword `k` of `zmm r`, as a 512-bit store writes it. -/
theorem zmm_dword (s : State) (r : XReg) {k : Nat} (hk : k < 16) :
    (s.zmm r).extractLsb' (8 * (4 * k)) (8 * 4) = zw s r k := by
  rw [show 8 * (4 * k) = 8 * (16 * (k / 4) + 4 * (k % 4)) by omega,
    State.zmm_extract _ _ (by omega) (mod4_lt _)]

/-- A store of a `zmm` register at doubleword `i` of a region whose
doublewords `j < D'` are at `p + 4 j`: the doublewords after it. -/
theorem read_store16 {m : Mem} {p : Addr} {i j D' : Nat} (hD : D' ≤ 256) (hi : i + 16 ≤ D') (hj : j < D')
    (v : BitVec 512) :
    (m.writeW (p + BitVec.ofNat 64 (4 * i)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      if i ≤ j ∧ j < i + 16 then v.extractLsb' (8 * (4 * (j - i))) (8 * 4)
      else m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  by_cases hx : i ≤ j ∧ j < i + 16
  · rw [ite_eq_left hx, show p + BitVec.ofNat 64 (4 * j) =
        p + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (4 * (j - i)) by
      rw [add_ofNat']; congr 2; omega]
    exact readW_writeW_inside m _ v (k := 4 * (j - i)) (n := 4) (by omega) (by decide)
  · rw [ite_eq_right hx]
    exact readW_writeW_off m _ v (d := 4 * j) (e := 4 * i) (n := 4) (by omega) (by omega) (by omega)

/-- A store in place, to `buf` or the data. -/
theorem store_ok {s₀ : State} (hc : Ctx s₀) {σ : Sym} {s : State} (h : SRel σ s₀ s)
    {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 16 wsize = some (b, i)) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRel (symStore σ b i 16 (xidx r)) s₀ s' := by
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hi' : i + 16 ≤ bsize b := Nat.le_trans hi (wsize_le b)
  have hb0 : b = 1 ∨ b = 2 := by
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | e
    · simp [wsize] at hi
    · exact .inl e
    · exact .inr e
  have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin := in_regn hc hb h.wr hi'
  refine ⟨s.setMem (s.mem.writeW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [reduceExec, ea, State.store512_eq, hin, ite_true], SRel.mk' (fun r' p hp => ?_)
    (fun b' i' hb' hi'' => ?_) (by simp [h.gpr]) (by simp [h.rd]) (by simp [h.wr]) ?_ fun hd => by cases hd⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem, symStore]
    by_cases e : b' = b
    · subst e
      rw [read_store16 (bsize_le b') hi' hi'']
      by_cases hx : i ≤ i' ∧ i' < i + 16
      · rw [ite_eq_left hx, ite_eq_left ⟨rfl, hx⟩, zmm_dword _ _ (by omega)]
        exact h.reg r _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right (fun h' => hx h'.2)]
        exact h.mem b' i' hb' hi''
    · have f := (Frame.refl [regn s₀ b] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
        (regn_contains s₀ (n := 16) hi')
      rw [f.readW (r := regn s₀ b') (regn_contains s₀ (n := 1) (by omega))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.d b' b hb' hb e)
        (by decide), ite_eq_right (fun hx => e hx.1)]
      exact h.mem b' i' hb' hi''
  · simp only [State.setMem_mem]
    refine h.frame.writeW (r := if b = 1 then ⟨s₀.gpr .rcx, 128⟩ else ⟨s₀.gpr .rsi, 1024⟩)
      (by rcases hb0 with rfl | rfl <;> simp [wregsT, wregs]) _ ?_
    rcases hb0 with rfl | rfl
    · simp only [regn, baseR, Region.Contains, ite_true]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega
    · simp only [regn, baseR, Region.Contains, show (2 : Nat) ≠ 1 by decide, ite_false]
      simp only [wsize] at hi; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega

theorem dst_contains (s₀ : State) {j n : Nat} (hj : j + n ≤ 256) :
    (dstR 256 s₀).Contains ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * j)) (4 * n) := by
  simp only [Region.Contains, dstR]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega

/-- `buf`'s first 128 bytes, in region 1. -/
theorem save_regn (s₀ : State) : Region.Sub ⟨s₀.gpr .rcx, 128⟩ (regn s₀ 1) := by
  simp only [regn, baseR, bsize]; exact Region.sub_prefix (by omega)

/-- From a source to a destination: the source after a store, where its
destination is as on entry. -/
theorem src_after {s₀ : State} (hc : Ctx01 s₀ ∧ Ctx3 (regn s₀) 256 s₀) {σ : Sym} {t : Mem}
    (hf : Frame (wregsT true s₀) s₀.mem t)
    (hm3 : ∀ j < 256, t.readW ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * j)) 32 = (σ.mem 3 j).eval s₀)
    (hs2 : ∀ j, σ.mem 2 j = .mem 2 j) {i : Nat} (hi : i < bsize 2) (hcl : σ.mem 3 i = .mem 3 i) :
    t.readW ((regn s₀ 2).base + BitVec.ofNat 64 (4 * i)) 32 = (σ.mem 2 i).eval s₀ := by
  have hi' : i < 256 := by simpa [bsize] using hi
  rw [hs2 i]
  simp only [T.eval, memBase_lt (show 2 < 3 by decide)]
  refine src_keep hc.2 rfl (save_regn s₀) hf (regn_contains s₀ (n := 1) (by omega)) ?_
  have := hm3 i hi'
  rw [hcl] at this
  simpa only [T.eval, memBase_3] using this

/-- From a source to a destination: a store to the destination. -/
theorem store3_ok {s₀ : State} (hc : Ctx01 s₀ ∧ Ctx3 (regn s₀) 256 s₀) {σ : Sym} {s : State}
    (h : SRelT true σ s₀ s) {m : MemOp} {r : XReg} {i : Nat} (hs : slotD m 16 256 = some i) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRelT true (symStore σ 3 i 16 (xidx r)) s₀ s' := by
  obtain ⟨hi, hea⟩ := slotD_ok hs
  have ea : s.ea m = (dstR 256 s₀).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * i)) (4 * 16) := by
    rw [h.wr]; exact hc.2.w i 16 hi (by decide)
  have f := (Frame.refl [dstR 256 s₀] s.mem).writeW (List.mem_singleton_self _) (s.zmm r) (dst_contains s₀ hi)
  have F : Frame (wregsT true s₀) s₀.mem
      (s.mem.writeW ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)) :=
    h.frame.writeW (r := dstR 256 s₀) (by simp [wregsT]) _ (dst_contains s₀ hi)
  have m3 : ∀ j < 256, (s.mem.writeW ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)).readW
      ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * j)) 32 = ((symStore σ 3 i 16 (xidx r)).mem 3 j).eval s₀ := by
    intro j hj
    rw [read_store16 (Nat.le_refl _) hi hj]
    simp only [symStore, true_and]
    by_cases hx : i ≤ j ∧ j < i + 16
    · rw [ite_eq_left hx, ite_eq_left hx, zmm_dword _ _ (by omega)]
      exact h.reg r _ (by omega)
    · rw [ite_eq_right hx, ite_eq_right hx]
      exact h.mem3 rfl j hj
  have hs2 : ∀ j, (symStore σ 3 i 16 (xidx r)).mem 2 j = .mem 2 j := fun j => by
    simp only [symStore, show (2 : Nat) ≠ 3 by decide, false_and, ite_false]; exact h.src rfl j
  refine ⟨s.setMem (s.mem.writeW ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [reduceExec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ => hs2, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    have e3 : (symStore σ 3 i 16 (xidx r)).mem b' i' = σ.mem b' i' := by
      simp only [symStore, show b' ≠ 3 by omega, false_and, ite_false]
    rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [e3, f.readW (r := regn s₀ 0) (regn_contains s₀ (n := 1) (by omega))
        (by simpa using (hc.2.d 0 (by decide)).1) (by decide)]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [e3, f.readW (r := regn s₀ 1) (regn_contains s₀ (n := 1) (by omega))
        (by simpa using (hc.2.d 1 (by decide)).1) (by decide)]
      exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · exact src_after hc F m3 hs2 hi'' (hcl rfl rfl)

/-- From a source to a destination: a store to `buf`. -/
theorem storeB_ok {s₀ : State} (hc : Ctx01 s₀ ∧ Ctx3 (regn s₀) 256 s₀) {σ : Sym} {s : State}
    (h : SRelT true σ s₀ s) {m : MemOp} {r : XReg} {b i : Nat} (hs : slot m 16 (wsizeT true) = some (b, i)) :
    ∃ s', exec (.vmovdqu32Store m r) s = some s' ∧ SRelT true (symStore σ b i 16 (xidx r)) s₀ s' := by
  obtain ⟨hb, hi, hea⟩ := slot_ok hs
  have hb1 : b = 1 := by
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | e | rfl
    · simp [wsizeT] at hi
    · exact e
    · simp [wsizeT] at hi
  subst hb1
  have hi32 : i + 16 ≤ 32 := by simpa [wsizeT, wsize] using hi
  have hi' : i + 16 ≤ bsize 1 := by simp only [bsize]; omega
  have ea : s.ea m = (regn s₀ 1).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
  have hin : InRegions s.wr ((regn s₀ 1).base + BitVec.ofNat 64 (4 * i)) (4 * 16) := by
    rw [h.wr]; exact hc.1.w 1 i 16 (by decide) hi'
  have f := (Frame.refl [regn s₀ 1] s.mem).writeW (List.mem_singleton_self _) (s.zmm r)
    (regn_contains s₀ (n := 16) hi')
  have F : Frame (wregsT true s₀) s₀.mem
      (s.mem.writeW ((regn s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)) :=
    h.frame.writeW (r := ⟨s₀.gpr .rcx, 128⟩) (by simp [wregsT]) _ (by
      simp only [regn, baseR, Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
  have m3 : ∀ j < 256, (s.mem.writeW ((regn s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)).readW
      ((dstR 256 s₀).base + BitVec.ofNat 64 (4 * j)) 32 = ((symStore σ 1 i 16 (xidx r)).mem 3 j).eval s₀ := by
    intro j hj
    rw [f.readW (r := dstR 256 s₀) (dst_contains s₀ (n := 1) (by omega))
      (by simpa using (hc.2.d 1 (by decide)).1.symm) (by decide)]
    simp only [symStore, show (3 : Nat) ≠ 1 by decide, false_and, ite_false]
    exact h.mem3 rfl j hj
  have hs2 : ∀ j, (symStore σ 1 i 16 (xidx r)).mem 2 j = .mem 2 j := fun j => by
    simp only [symStore, show (2 : Nat) ≠ 1 by decide, false_and, ite_false]; exact h.src rfl j
  refine ⟨s.setMem (s.mem.writeW ((regn s₀ 1).base + BitVec.ofNat 64 (4 * i)) (s.zmm r)),
    by simp only [reduceExec, ea, State.store512_eq, hin, ite_true], ⟨fun r' p hp => ?_,
    fun b' i' hb' hi'' hcl => ?_, fun _ => m3, fun _ => hs2, by simp [h.gpr], by simp [h.rd],
    by simp [h.wr], F, fun hd => by cases hd⟩⟩
  · simp only [zw_split, State.setMem_zlane]; exact h.reg r' p hp
  · simp only [State.setMem_mem]
    rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · rw [f.readW (r := regn s₀ 0) (regn_contains s₀ (n := 1) (by omega))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.1.d) (by decide)]
      simp only [symStore, show (0 : Nat) ≠ 1 by decide, false_and, ite_false]
      exact h.mem 0 i' hb' hi'' (fun _ e => nomatch e)
    · rw [read_store16 (bsize_le 1) hi' hi'']
      simp only [symStore, true_and]
      by_cases hx : i ≤ i' ∧ i' < i + 16
      · rw [ite_eq_left hx, ite_eq_left hx, zmm_dword _ _ (by omega)]
        exact h.reg r _ (by omega)
      · rw [ite_eq_right hx, ite_eq_right hx]
        exact h.mem 1 i' hb' hi'' (fun _ e => nomatch e)
    · exact src_after hc F m3 hs2 hi'' (hcl rfl rfl)

/-- A load allowed by `Sym.stepT`: from the source, only where the
destination is as on entry. -/
theorem clean_of {to : Bool} {σ : Sym} {b i n : Nat} (hcl : ¬ (to = true ∧ b = 2 ∧ clean3 σ i n = false))
    {p : Nat} (hp : p < n) : to = true → b = 2 → σ.mem 3 (i + p) = .mem 3 (i + p) := fun ht hb2 =>
  clean3_of (by simp only [ht, hb2, true_and, Bool.not_eq_false] at hcl; exact hcl) hp

/-- One instruction. -/
theorem sstepT_ok {to : Bool} {s₀ : State} (hc : CtxT to s₀) {σ σ' : Sym} {s : State} (h : SRelT to σ s₀ s)
    {i : Instr} (e : σ.stepT to i = some σ') : ∃ s', exec i s = some s' ∧ SRelT to σ' s₀ s' := by
  unfold Sym.stepT at e
  split at e
  · rename_i op d a b
    split at e
    case isFalse => cases e
    rename_i hop
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_zbin _ _ _ _ _ _ (div4_lt hp)]
    split
    · exact (zbinT_eval hop (fun k hk => (h.reg a _ (by omega)).symm.trans (zw_lk s a hk))
        (fun k hk => (h.reg b _ (by omega)).symm.trans (zw_lk s b hk))).symm
    · rfl
  · rename_i d a o
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vpshufd _ _ _ _ _ (div4_lt hp)]
    split
    · rw [dword_shufDwords _ _ (mod4_lt p), sel2_eq, ← zw_lk s a (sel2_lt _ _)]
      exact h.reg a _ (by have := sel2_lt o.toNat (p % 4); omega)
    · rfl
  · rename_i d a b n
    cases e
    refine ⟨_, rfl, h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, zlane_vshufi32x4 _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [shuf4Lanes_eq, sel2_eq]
      have := sel2_lt n.toNat (p / 4)
      by_cases hl : p / 4 < 2
      · simp only [hl, ite_true]
        rw [← zw_lk s a (mod4_lt p)]; exact h.reg a _ (by omega)
      · simp only [hl, ite_false]
        rw [← zw_lk s b (mod4_lt p)]; exact h.reg b _ (by omega)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 16 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setZ d ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 0 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 128 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 256 128)
      ((s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 512).extractLsb' 384 128),
      by simp only [reduceExec, ea, State.load512, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_ext _ (div4_lt hp), dword_read512 _ _ hp, add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p) hb (by omega) (clean_of hcl hp)
    · rfl
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 4 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    refine ⟨s.setZ d (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128)
      (s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 128),
      by simp only [reduceExec, ea, State.load128, hin, ite_true, Option.map_some],
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
    split
    · rw [pick4_same _ (div4_lt hp), dword_readW _ _ (mod4_lt p), add_ofNat', ← Nat.mul_add]
      exact h.mem b (i + p % 4) hb (by have := mod4_lt p; omega) (clean_of hcl (mod4_lt p))
    · rfl
  · rename_i m r
    cases to
    · simp only [Bool.false_eq_true, ite_false] at e
      obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
      exact store_ok hc h hs
    · simp only [ite_true] at e
      split at e
      · rename_i j hj
        cases e
        exact store3_ok hc h hj
      · obtain ⟨⟨b, i⟩, hs, rfl⟩ := Option.map_eq_some_iff.1 e
        exact storeB_ok hc h hs
  · rename_i d m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 1 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    have hv := h.mem b i hb (by omega) (clean_of (p := 0) hcl (by decide))
    generalize hvd : s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = v at hv
    refine ⟨s.setZ d (v ++ v ++ v ++ v) (v ++ v ++ v ++ v) (v ++ v ++ v ++ v) (v ++ v ++ v ++ v), ?_,
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    · simp only [reduceExec, ea, State.load32, hin, ite_true, Option.map_some, hvd]
    · rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
      split
      · rw [pick4_same _ (div4_lt hp), dword_rep4 _ (mod4_lt p)]; exact hv
      · rfl
  · rename_i d a m
    obtain ⟨⟨b, i⟩, hs, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    by_cases hcl : to = true ∧ b = 2 ∧ clean3 σ i 1 = false
    · rw [ite_eq_left hcl] at e; cases e
    rw [ite_eq_right hcl, Option.some.injEq] at e
    subst e
    obtain ⟨hb, hi, hea⟩ := slot_ok hs
    have ea : s.ea m = (regn s₀ b).base + BitVec.ofNat 64 (4 * i) := by rw [hea, h.gpr]; rfl
    have hin := hc.rd hb h.rd h.wr hi (by decide)
    have hv := h.mem b i hb (by omega) (clean_of (p := 0) hcl (by decide))
    generalize hvd : s.mem.readW ((regn s₀ b).base + BitVec.ofNat 64 (4 * i)) 32 = v at hv
    refine ⟨s.setZ d (XBinOp.eval .paddd (s.zlane a 0) (v ++ v ++ v ++ v))
      (XBinOp.eval .paddd (s.zlane a 1) (v ++ v ++ v ++ v)) (XBinOp.eval .paddd (s.zlane a 2) (v ++ v ++ v ++ v))
      (XBinOp.eval .paddd (s.zlane a 3) (v ++ v ++ v ++ v)), ?_,
      h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
    · simp only [reduceExec, ea, State.load32, hin, ite_true, Option.map_some, ZBcstDOp.sse, hvd]
    · rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
      split
      · rw [pick4_fn (fun l => XBinOp.eval .paddd (s.zlane a l) (v ++ v ++ v ++ v)) (div4_lt hp),
          dword_paddd _ _ (mod4_lt p), dword_rep4 _ (mod4_lt p), T.eval, ← hv, ← zw_split]
        exact congrArg (· + v) (h.reg a p hp)
      · rfl
  · cases e

/-- A block of instructions. -/
theorem srunT_ok {to : Bool} {s₀ : State} (hc : CtxT to s₀) :
    ∀ (is : List Instr) {σ σ' : Sym} {s : State}, SRelT to σ s₀ s → σ.runT to is = some σ' →
      WP isa (.block is) s (SRelT to σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.runT, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstepT_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srunT_ok hc is h₁ e₂⟩

/-- A block of instructions, in place. -/
theorem srun_ok {s₀ : State} (hc : Ctx s₀) (is : List Instr) {σ σ' : Sym} {s : State}
    (h : SRel σ s₀ s) (e : σ.run is = some σ') : WP isa (.block is) s (SRel σ' s₀) :=
  srunT_ok (to := false) hc is h e

end VG.Proof.ChaCha20.X86_64.Avx512
