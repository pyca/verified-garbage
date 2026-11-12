module

-- separate module: its proofs (about 2 s, the terms' evaluation) are not checked again when `Stage` changes

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# P-256 on x86-64 with AVX512_IFMA: straight-line vector code, lane by lane

The vector code of the joint multiplication computes on the four quadwords
(lanes) of all thirty-two `ymm` registers, with `EVEX.256` instructions
only. It loads and stores 32 bytes at offsets of the working space (`rdi`)
that are multiples of 32, loads its constants from a table (at `cb`), and
loads from other registers' addresses (a table's entry).

`VSym.run` computes each quadword after a block of such instructions as a
term (`T`) in the quadwords of the registers and of the memory before it,
and the stores as a list of terms; a load of 32 bytes that the block stored
is the term stored, and a load of constants is their numbers. `run_ok`
proves the machine agrees.
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum.X86_64.AmmSym (baseOff baseOff_ok)
open VG.Proof.Bignum.X86_64.Ifma (vi vreg_vi vi_inj qv qv_setVy qword256_lanes qword_lane256 qword256_madd
  lane_app0 lane_app1 gpr_setVy)
open VG.Proof.Poly1305.X86_64.Avx2 (qword_app0 qword_app1 qword_paddq qword_psrlq qword_psllq mod2_lt qword256_eq qword256_cat
  qword_and qword256_perm sel4 sel4_lt)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52 qword_psubq)
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)

/-! ## Terms -/

/-- One of four, by lane. -/
def pick4 {α : Type} (a b c d : α) (k : Nat) : α :=
  match k with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

/-- A quadword of a vector register, in terms of the start. -/
inductive T
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  /-- The numbers `w0`, …, `w3`. -/
  | lit (w0 w1 w2 w3 : Nat)
  /-- Quadword `k` of the 32 bytes at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  | add (a b : T)
  | sub (a b : T)
  | shl (a : T) (n : Nat)
  | shr (a : T) (n : Nat)
  /-- The arithmetic shift right. -/
  | sra (a : T) (n : Nat)
  /-- The low `j_k` bits of quadword `k`. -/
  | mask (a : T) (j0 j1 j2 j3 : Nat)
  /-- Quadword `k` of `b` where bit `k` of `m` is set, else of `a`. -/
  | blend (a b : T) (m : Nat)
  /-- `vpermq`: quadword `sel4 o k` of `a`. -/
  | perm (a : T) (o : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : T)
  /-- Shifted left by `n` (in 64 bits), then right by `k`. -/
  | slr (a : T) (n k : Nat)
  /-- `b` where `c` is set, else `a` (`c` all ones or zero, where it means anything). -/
  | sel (c a b : T)
  deriving DecidableEq, Repr

def T.eval (s₀ : State) : T → Nat → BitVec 64
  | .reg r, k => qv s₀ (vreg r) k
  | .lit a b c d, k => BitVec.ofNat 64 (pick4 a b c d k)
  | .ld b d, k => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .sub a b, k => a.eval s₀ k - b.eval s₀ k
  | .shl a n, k => a.eval s₀ k <<< n
  | .shr a n, k => a.eval s₀ k >>> n
  | .sra a n, k => (a.eval s₀ k).sshiftRight n
  | .mask a j0 j1 j2 j3, k => a.eval s₀ k &&& BitVec.ofNat 64 (2 ^ pick4 j0 j1 j2 j3 k - 1)
  | .blend a b m, k => if m.testBit k then b.eval s₀ k else a.eval s₀ k
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .slr a n j, k => (a.eval s₀ k <<< n) >>> j
  | .sel c a b, k => (c.eval s₀ k &&& b.eval s₀ k) ||| (~~~c.eval s₀ k &&& a.eval s₀ k)

/-- The 32 bytes of a term. -/
def T.val (s₀ : State) (t : T) : BitVec 256 := t.eval s₀ 3 ++ t.eval s₀ 2 ++ t.eval s₀ 1 ++ t.eval s₀ 0

theorem qword256_val (s₀ : State) (t : T) {k : Nat} (hk : k < 4) : qword256 (t.val s₀) k = t.eval s₀ k := by
  rw [T.val, qword256_cat _ _ _ _ hk]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-! ## The machine -/

/-- What a block runs with: the register its constants are at and their
quadwords, the bytes it may load from each other register's address, and
the bytes of the working space at `rdi` that it loads and stores. -/
structure Par where
  cb : Reg
  cst : List Nat
  lim : Reg → Nat
  win : Nat
  /-- The stores are from `lo` of the working space. -/
  lo : Nat

/-- The terms of the thirty-two vector registers (by number), and the stores
into the working space, the last first: the offset and what was stored. -/
structure VSym where
  reg : Nat → T
  st : List (Nat × T)

def VSym.init : VSym := ⟨.reg, []⟩

/-- (`Nat.beq`, as `ESym.set`.) -/
def VSym.set (σ : VSym) (d : VReg) (t : T) : VSym :=
  { σ with reg := fun r => bif Nat.beq r (vi d) then t else σ.reg r }

def VSym.get (σ : VSym) (r : VReg) : T := σ.reg (vi r)

/-- The 32 bytes at offset `o` of the working space after the stores `st`. -/
def look : List (Nat × T) → Nat → T
  | [], o => .ld .rdi o
  | (e, t) :: st, o => bif Nat.beq e o then t else look st o

/-- The four constants at offset `o` of the table. -/
def litOf (cst : List Nat) (o : Nat) : Option T :=
  if o % 8 = 0 ∧ o / 8 + 4 ≤ cst.length then
    some (.lit (cst.getD (o / 8) 0) (cst.getD (o / 8 + 1) 0) (cst.getD (o / 8 + 2) 0) (cst.getD (o / 8 + 3) 0))
  else none

/-- The term of 32 bytes of memory. -/
def VSym.src (P : Par) (σ : VSym) (m : MemOp) : Option T :=
  (baseOff m).bind fun bo =>
    if bo.1 = .rdi then (if bo.2 % 32 = 0 ∧ bo.2 + 32 ≤ P.win then some (look σ.st bo.2) else none)
    else if bo.1 = P.cb then litOf P.cst bo.2
    else if bo.2 + 32 ≤ P.lim bo.1 then some (.ld bo.1 bo.2) else none

/-- `j` with `w = 2^j - 1`, `j ≤ 64`. -/
def maskBits (w : Nat) : Option Nat := (List.range 65).find? fun j => 2 ^ j - 1 == w

/-- The widths of a term of constants `2^j - 1`. -/
def maskOf : T → Option (Nat × Nat × Nat × Nat)
  | .lit a b c d =>
    (maskBits a).bind fun x => (maskBits b).bind fun y => (maskBits c).bind fun z => (maskBits d).map fun u =>
      (x, y, z, u)
  | _ => none

/-- Whether a quadword is all ones (`some true`) or zero. -/
def laneBit (w : Nat) : Option Nat :=
  if w = 0 then some 0 else if w = 2 ^ 64 - 1 then some 1 else none

/-- The lanes a term of constants selects: bit `k` for all ones in quadword
`k`, which is otherwise zero. -/
def blendOf : T → Option Nat
  | .lit a b c d =>
    (laneBit a).bind fun x => (laneBit b).bind fun y => (laneBit c).bind fun z => (laneBit d).map fun u =>
      x + 2 * y + 4 * z + 8 * u
  | _ => none

/-- A shift right, of a shift left or of anything else. -/
def shrOf (t : T) (n : Nat) : T :=
  match t with
  | .shl x m => .slr x m n
  | t => .shr t n

/-- `b` in the lanes of the mask `c`, else `a`: by the mask's lanes if it is of constants. -/
def selOf (c a b : T) : T :=
  match blendOf c with
  | some m => .blend a b m
  | none => .sel c a b

def VSym.eop (σ : VSym) : EOp → Option VSym
  | .bin .vpaddq d a b => some (σ.set d (.add (σ.get a) (σ.get b)))
  | .bin .vpsubq d a b => some (σ.set d (.sub (σ.get a) (σ.get b)))
  | .bin .vpxorq d a b => if a = b then some (σ.set d (.lit 0 0 0 0)) else none
  | .bin .vpandq d a b => (maskOf (σ.get b)).map fun j => σ.set d (.mask (σ.get a) j.1 j.2.1 j.2.2.1 j.2.2.2)
  | .shift .vpsrlq d a n => if n.toNat < 64 then some (σ.set d (shrOf (σ.get a) n.toNat)) else none
  | .shift .vpsllq d a n => if n.toNat < 64 then some (σ.set d (.shl (σ.get a) n.toNat)) else none
  | .vpsraq d a n => if n.toNat < 64 then some (σ.set d (.sra (σ.get a) n.toNat)) else none
  | .vpermq d a o => some (σ.set d (.perm (σ.get a) o.toNat))
  | .vpternlogq d a b n =>
    if n = 0xD8 then some (σ.set d (selOf (σ.get b) (σ.get d) (σ.get a))) else none
  | .vmovdqa64 d a => some (σ.set d (σ.get a))
  | .vpmadd52 h d a b => some (σ.set d (.mad h (σ.get d) (σ.get a) (σ.get b)))
  | _ => none

/-- One instruction. -/
def VSym.step (P : Par) (σ : VSym) : Instr → Option VSym
  | .eop o => σ.eop o
  | .evLoad d m => (σ.src P m).map fun t => σ.set d t
  | .evMadd52Load h d a m => (σ.src P m).map fun t => σ.set d (.mad h (σ.get d) (σ.get a) t)
  | .evStore m r => (baseOff m).bind fun bo =>
    if bo.1 = .rdi ∧ bo.2 % 32 = 0 ∧ bo.2 + 32 ≤ P.win ∧ P.lo ≤ bo.2 then some { σ with st := (bo.2, σ.get r) :: σ.st }
    else none
  | _ => none

def VSym.run (P : Par) (σ : VSym) : List Instr → Option VSym
  | [] => some σ
  | i :: is => (σ.step P i).bind fun σ' => σ'.run P is

/-! ## The machine agrees -/

/-- The memory after the stores `st` (the last first). -/
def stores (s₀ : State) : List (Nat × T) → Mem
  | [] => s₀.mem
  | (d, t) :: st => (stores s₀ st).writeW (s₀.gpr .rdi + BitVec.ofNat 64 d) (t.val s₀)

/-- `s₀` with the vector registers and memory of `s`. -/
def vm (s₀ s : State) : State :=
  { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, ymmH := s.ymmH, zmmHiH := s.zmmHiH, mem := s.mem }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and the stores of `σ`. -/
structure SRel (P : Par) (σ : VSym) (s₀ s : State) : Prop where
  reg : ∀ r k, k < 4 → qv s r k = (σ.reg (vi r)).eval s₀ k
  eq : vm s₀ s = s
  mem : s.mem = stores s₀ σ.st
  al : ∀ e ∈ σ.st, e.1 % 32 = 0 ∧ e.1 + 32 ≤ P.win
  lo : ∀ e ∈ σ.st, P.lo ≤ e.1

theorem SRel.gpr {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) : s.gpr = s₀.gpr := by
  rw [← h.eq]; rfl
theorem SRel.rd {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) : s.mxcsr = s₀.mxcsr := by
  rw [← h.eq]; rfl
theorem SRel.flags {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem SRel.init (P : Par) (s₀ : State) : SRel P VSym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [VSym.init, T.eval, vreg_vi], rfl, rfl, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem vm_setVy {s₀ s : State} (h : vm s₀ s = s) (d : VReg) (v : BitVec 256) :
    vm s₀ (s.setVy d v) = s.setVy d v := by
  rw [← h]; cases d <;> rfl

theorem mem_setVy (s : State) (d : VReg) (v : BitVec 256) : (s.setVy d v).mem = s.mem := by
  cases d <;> rfl

theorem SRel.set {P : Par} {σ : VSym} {s₀ s : State} (h : SRel P σ s₀ s) {d : VReg} {t : T} {v : BitVec 256}
    (hv : ∀ k, k < 4 → qword256 v k = t.eval s₀ k) : SRel P (σ.set d t) s₀ (s.setVy d v) := by
  refine ⟨fun r k hk => ?_, vm_setVy h.eq d v, (mem_setVy s d v).trans h.mem, h.al, h.lo⟩
  rw [qv_setVy]
  simp only [VSym.set, Bool.cond_eq_ite, Nat.beq_eq, vi_inj]
  split
  · exact hv k hk
  · exact h.reg r k hk

/-- What a block may read and write: the working space is writable; the
other addresses it loads from are readable and apart from the working space;
and the table of constants holds `P.cst`. -/
structure Ctx (P : Par) (s₀ : State) : Prop where
  win : ∀ d, d + 32 ≤ P.win → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 d) 32
  small : P.win < 2 ^ 62
  rd : ∀ b d, b ≠ .rdi → b ≠ P.cb → d + 32 ≤ P.lim b →
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 d) 32
  sep : ∀ b d, b ≠ .rdi → b ≠ P.cb → d + 32 ≤ P.lim b →
    Mem.Sep (s₀.gpr b + BitVec.ofNat 64 d) 32 (s₀.gpr .rdi + BitVec.ofNat 64 P.lo) (P.win - P.lo)
  crd : ∀ d, d + 32 ≤ 8 * P.cst.length → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr P.cb + BitVec.ofNat 64 d) 32
  csep : ∀ d, d + 32 ≤ 8 * P.cst.length → Mem.Sep (s₀.gpr P.cb + BitVec.ofNat 64 d) 32 (s₀.gpr .rdi + BitVec.ofNat 64 P.lo) (P.win - P.lo)
  cst : ∀ i, i < P.cst.length →
    s₀.mem.readW (s₀.gpr P.cb + BitVec.ofNat 64 (8 * i)) 64 = BitVec.ofNat 64 (P.cst.getD i 0)
  cb : P.cb ≠ .rdi

/-- A quadword of 32 bytes apart from the stores' part of the working space, after the stores. -/
theorem stores_sep {P : Par} {s₀ : State} {a : Addr}
    (hs : Mem.Sep a 32 (s₀.gpr .rdi + BitVec.ofNat 64 P.lo) (P.win - P.lo)) (hw : P.win < 2 ^ 62)
    {k : Nat} (hk : k < 4) :
    ∀ (st : List (Nat × T)), (∀ e ∈ st, e.1 % 32 = 0 ∧ e.1 + 32 ≤ P.win) → (∀ e ∈ st, P.lo ≤ e.1) →
      (stores s₀ st).readW (a + BitVec.ofNat 64 (8 * k)) 64 = s₀.mem.readW (a + BitVec.ofNat 64 (8 * k)) 64
  | [], _, _ => rfl
  | (e, t) :: st, he, hl => by
    have he0 := he (e, t) List.mem_cons_self
    have hl0 := hl (e, t) List.mem_cons_self
    simp only [stores]
    rw [Mem.readW_writeW_sep (w := 64) (w' := 256) ?_ (by decide)]
    · exact stores_sep hs hw hk st (fun x hx => he x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    · intro x hx hy
      simp only [Nat.reduceDiv] at hx hy
      refine hs x ?_ ?_
      · simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
        have := (x - a).isLt
        omega
      · simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hy ⊢
        have := (x - s₀.gpr .rdi).isLt
        omega

/-- A quadword of 32 bytes of the working space, after the stores. -/
theorem stores_look {P : Par} {s₀ : State} (hw : P.win < 2 ^ 62) {o k : Nat} (ho : o % 32 = 0)
    (ho2 : o + 32 ≤ P.win) (hk : k < 4) :
    ∀ (st : List (Nat × T)), (∀ e ∈ st, e.1 % 32 = 0 ∧ e.1 + 32 ≤ P.win) →
      (stores s₀ st).readW (s₀.gpr .rdi + BitVec.ofNat 64 (o + 8 * k)) 64 = (look st o).eval s₀ k
  | [], _ => rfl
  | (e, t) :: st, he => by
    have he0 := he (e, t) List.mem_cons_self
    simp only [stores, look, Bool.cond_eq_ite, Nat.beq_eq]
    split
    · rename_i heq
      subst heq
      have r1 := readW_writeW_inside (stores s₀ st) (s₀.gpr .rdi + BitVec.ofNat 64 e) (t.val s₀)
        (k := 8 * k) (n := 8) (by omega) (by decide)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at r1
      rw [r1, ← qword256_val s₀ t hk, qword256, show 64 * k = 8 * (8 * k) by omega]
    · rename_i hne
      have r1 := readW_writeW_off (stores s₀ st) (s₀.gpr .rdi) (t.val s₀) (d := o + 8 * k) (e := e) (n := 8)
        (by omega) (by simp only [Nat.reduceDiv]; omega) (by simp only [Nat.reduceDiv]; omega)
      rw [r1]
      exact stores_look hw ho ho2 hk st fun x hx => he x (List.mem_cons_of_mem _ hx)

theorem litOf_eval {P : Par} {s₀ : State} (hc : Ctx P s₀) {o : Nat} {t : T} (h : litOf P.cst o = some t)
    {k : Nat} (hk : k < 4) :
    s₀.mem.readW (s₀.gpr P.cb + BitVec.ofNat 64 (o + 8 * k)) 64 = t.eval s₀ k := by
  unfold litOf at h
  split at h
  case isFalse => cases h
  rename_i ho
  cases h
  have e := hc.cst (o / 8 + k) (by omega)
  rw [show 8 * (o / 8 + k) = o + 8 * k by omega] at e
  rw [e]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- The 32 bytes of a memory operand are readable, and their quadwords are
its term's. -/
theorem src_ok {P : Par} {s₀ : State} (hc : Ctx P s₀) {σ : VSym} {s : State} (h : SRel P σ s₀ s)
    {m : MemOp} {t : T} (e : σ.src P m = some t) :
    InRegions (s.rd ++ s.wr) (s.ea m) 32 ∧
      ∀ k, k < 4 → qword256 (s.mem.readW (s.ea m) 256) k = t.eval s₀ k := by
  obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
  have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr]
  have hq (k : Nat) (hk : k < 4) : qword256 (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256) k =
      s.mem.readW (s₀.gpr b + BitVec.ofNat 64 (o + 8 * k)) 64 := by
    have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k) (n := 8) (by omega)
    rw [qword256, show 64 * k = 8 * (8 * k) by omega, r1, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h.rd, h.wr, ea]
  dsimp only at e
  split at e
  · rename_i hb
    subst hb
    split at e
    case isFalse => cases e
    rename_i ho
    cases e
    refine ⟨?_, fun k hk => ?_⟩
    · obtain ⟨r, hr, hcn⟩ := hc.win o ho.2
      exact ⟨r, List.mem_append_right _ hr, hcn⟩
    · rw [hq k hk, h.mem]
      exact stores_look hc.small ho.1 ho.2 hk σ.st h.al
  · rename_i hb
    split at e
    · rename_i hcb
      subst hcb
      have hlen : o + 32 ≤ 8 * P.cst.length := by
        unfold litOf at e
        split at e
        · rename_i ho; omega
        · cases e
      refine ⟨hc.crd o hlen, fun k hk => ?_⟩
      rw [hq k hk, h.mem, BitVec.ofNat_add, ← BitVec.add_assoc,
        stores_sep (hc.csep o hlen) hc.small hk σ.st h.al h.lo, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact litOf_eval hc e hk
    · rename_i hcb
      split at e
      case isFalse => cases e
      rename_i ho
      cases e
      refine ⟨hc.rd b o hb hcb ho, fun k hk => ?_⟩
      rw [hq k hk, h.mem, BitVec.ofNat_add, ← BitVec.add_assoc,
        stores_sep (hc.sep b o hb hcb ho) hc.small hk σ.st h.al h.lo, BitVec.add_assoc, ← BitVec.ofNat_add]
      rfl

theorem maskBits_ok {w j : Nat} (h : maskBits w = some j) : w = 2 ^ j - 1 := by
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  exact this.symm

theorem laneBit_ok {w x : Nat} (h : laneBit w = some x) :
    (x = 0 ∧ w = 0) ∨ (x = 1 ∧ w = 2 ^ 64 - 1) := by
  unfold laneBit at h
  split at h
  · cases h; exact Or.inl ⟨rfl, by assumption⟩
  · split at h
    · cases h; exact Or.inr ⟨rfl, by assumption⟩
    · cases h

/-- `vpternlogq` with `0xD8`: `b` where `c` is set, else `a`. -/
theorem ternlogD8 (a b c : BitVec 128) : ternlog a b c 0xD8 = (c &&& b) ||| (~~~c &&& a) := by
  simp only [ternlog, List.range, List.range.loop, List.foldl, show (0xD8 : BitVec 8).getLsbD 0 = false from rfl,
    show (0xD8 : BitVec 8).getLsbD 1 = false from rfl, show (0xD8 : BitVec 8).getLsbD 2 = false from rfl,
    show (0xD8 : BitVec 8).getLsbD 3 = true from rfl, show (0xD8 : BitVec 8).getLsbD 4 = true from rfl,
    show (0xD8 : BitVec 8).getLsbD 5 = false from rfl, show (0xD8 : BitVec 8).getLsbD 6 = true from rfl,
    show (0xD8 : BitVec 8).getLsbD 7 = true from rfl, Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd,
    Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem qword_not (x : BitVec 128) {i : Nat} (hi : i < 2) : qword (~~~x) i = ~~~qword x i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj, show 64 * i + j < 128 by omega]

theorem qword_or' (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [qword, hj]

theorem qword256_ternD8 (dv av bv : BitVec 256) {k : Nat} (hk : k < 4) :
    qword256 (ternlog (lane256 dv 1) (lane256 av 1) (lane256 bv 1) 0xD8 ++
      ternlog (lane256 dv 0) (lane256 av 0) (lane256 bv 0) 0xD8) k =
      (qword256 bv k &&& qword256 av k) ||| (~~~qword256 bv k &&& qword256 dv k) := by
  rw [qword256_eq, ← qword_lane256 dv, ← qword_lane256 av, ← qword_lane256 bv]
  simp only [lane256]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, lane_app0, lane_app1, ternlogD8, qword_or',
      qword_and, qword_not _ (show (0 : Nat) < 2 by decide), qword_not _ (show (1 : Nat) < 2 by decide)]

theorem qword_sraq (x : BitVec 128) {n : BitVec 8} (hn : n.toNat < 64) {i : Nat} (hi : i < 2) :
    qword (sraQwords x n) i = (qword x i).sshiftRight n.toNat := by
  simp only [sraQwords, show min n.toNat 64 = n.toNat by omega]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact qword_app0 _ _
  · exact qword_app1 _ _

theorem blend_sel {x : Nat} {w : Nat} (h : (x = 0 ∧ w = 0) ∨ (x = 1 ∧ w = 2 ^ 64 - 1)) (a d : BitVec 64) :
    (BitVec.ofNat 64 w &&& a) ||| (~~~BitVec.ofNat 64 w &&& d) = if x = 1 then a else d := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.zero_and, BitVec.zero_or, BitVec.not_zero,
      BitVec.allOnes_and]
    rfl
  · have e : BitVec.ofNat 64 (2 ^ 64 - 1) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.allOnes_and, BitVec.not_allOnes, BitVec.zero_and, BitVec.or_zero]
    rfl

theorem bits4 {x y z u : Nat} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (hu : u ≤ 1) {k : Nat} (hk : k < 4) :
    (x + 2 * y + 4 * z + 8 * u).testBit k = decide (pick4 x y z u k = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [pick4, decide_eq_decide, Nat.reducePow, Nat.div_one] <;> omega

theorem shrOf_eval (s₀ : State) (t : T) (n k : Nat) : (shrOf t n).eval s₀ k = t.eval s₀ k >>> n := by
  unfold shrOf
  split <;> rfl

theorem selOf_eval (s₀ : State) (c a b : T) {k : Nat} (hk : k < 4) :
    (selOf c a b).eval s₀ k = (c.eval s₀ k &&& b.eval s₀ k) ||| (~~~c.eval s₀ k &&& a.eval s₀ k) := by
  unfold selOf
  split
  · rename_i mm hm
    cases c with
    | lit w0 w1 w2 w3 =>
      simp only [blendOf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨x, hx, y, hy, z, hz, u, hu, rfl⟩ := hm
      have bx := laneBit_ok hx; have by' := laneBit_ok hy; have bz := laneBit_ok hz; have bu := laneBit_ok hu
      have x1 : x ≤ 1 := by rcases bx with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      have y1 : y ≤ 1 := by rcases by' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      have z1 : z ≤ 1 := by rcases bz with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      have u1 : u ≤ 1 := by rcases bu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
      simp only [T.eval]
      rw [bits4 x1 y1 z1 u1 hk]
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> simp only [pick4, decide_eq_true_eq]
      · exact (blend_sel bx _ _).symm
      · exact (blend_sel by' _ _).symm
      · exact (blend_sel bz _ _).symm
      · exact (blend_sel bu _ _).symm
    | _ => simp [blendOf] at hm
  · rfl

theorem sstep_ok {P : Par} {s₀ : State} (hc : Ctx P s₀) {σ σ' : VSym} {s : State}
    (h : SRel P σ s₀ s) {i : Instr} (e : σ.step P i = some σ') :
    ∃ s', exec i s = some s' ∧ SRel P σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.get a).eval s₀ k = qv s a k := fun a k hk => (h.reg a k hk).symm
  unfold VSym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    unfold VSym.eop at e
    split at e
    · rename_i d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, T.eval]
      rw [qword_paddq _ _ (mod2_lt k), qword_lane256, qword_lane256, hR a k hk, hR b k hk]; rfl
    · rename_i d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, T.eval]
      rw [qword_psubq _ _ (mod2_lt k), qword_lane256, qword_lane256, hR a k hk, hR b k hk]; rfl
    · rename_i d a b
      split at e
      · rename_i hab
        cases e
        subst hab
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;>
          simp [EBinOp.sse, XBinOp.eval, qword, T.eval, pick4]
      · cases e
    · rename_i d a b
      obtain ⟨j, hj, e⟩ := Option.map_eq_some_iff.1 e
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_lanes _ _ _ hk]
      simp only [EBinOp.sse, XBinOp.eval, T.eval]
      rw [qword_and, qword_lane256, qword_lane256, hR a k hk]
      show qv s a k &&& qv s b k = _
      rw [← hR b k hk]
      congr 1
      generalize σ.get b = tb at hj ⊢
      cases tb with
      | lit w0 w1 w2 w3 =>
        simp only [maskOf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hj
        obtain ⟨x, hx, y, hy, z, hz, u, hu, rfl⟩ := hj
        simp only [T.eval]
        rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> simp only [pick4]
        · rw [maskBits_ok hx]
        · rw [maskBits_ok hy]
        · rw [maskBits_ok hz]
        · rw [maskBits_ok hu]
      | _ => simp [maskOf] at hj
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        simp only [ZShiftOp.sse]
        rw [qword_psrlq _ hn (mod2_lt k), qword_lane256, shrOf_eval, hR a k hk]; rfl
      · cases e
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        simp only [ZShiftOp.sse, T.eval]
        rw [qword_psllq _ hn (mod2_lt k), qword_lane256, hR a k hk]; rfl
      · cases e
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set fun k hk => ?_
        rw [qword256_lanes _ _ _ hk]
        simp only [T.eval]
        rw [qword_sraq _ hn (mod2_lt k), qword_lane256, hR a k hk]; rfl
      · cases e
    · rename_i d a o
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_perm _ _ hk]
      simp only [T.eval]
      rw [hR a _ (sel4_lt _ _)]; rfl
    · rename_i d a b n
      split at e
      · rename_i hn
        cases e
        subst hn
        refine h.set fun k hk => ?_
        rw [qword256_ternD8 _ _ _ hk, selOf_eval s₀ _ _ _ hk]
        rw [← qv, ← qv, ← qv, ← hR d k hk, ← hR a k hk, ← hR b k hk]
      · cases e
    · rename_i d a
      cases e
      refine h.set fun k hk => ?_
      rw [← qv, hR a k hk]
    · rename_i hh d a b
      cases e
      refine h.set fun k hk => ?_
      rw [qword256_madd _ _ _ _ hk]
      simp only [T.eval]
      rw [← qv, ← qv, ← qv, hR d k hk, hR a k hk, hR b k hk]
    · cases e
  · rename_i d m
    obtain ⟨t, ht, e⟩ := Option.map_eq_some_iff.1 e
    cases e
    obtain ⟨hin, hq⟩ := src_ok hc h ht
    refine ⟨s.setVy d (s.mem.readW (s.ea m) 256),
      by simp only [exec, State.load256, hin, ite_true, Option.map_some], ?_⟩
    exact h.set hq
  · rename_i hh d a m
    obtain ⟨t, ht, e⟩ := Option.map_eq_some_iff.1 e
    cases e
    obtain ⟨hin, hq⟩ := src_ok hc h ht
    let v := s.mem.readW (s.ea m) 256
    refine ⟨s.setVy d (madd52 hh (lane256 (s.vy d) 1) (lane256 (s.vy a) 1) (lane256 v 1) ++
      madd52 hh (lane256 (s.vy d) 0) (lane256 (s.vy a) 0) (lane256 v 0)),
      by simp only [exec, State.load256, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set fun k hk => ?_
    rw [qword256_madd _ _ _ _ hk]
    simp only [T.eval]
    rw [← qv, ← qv, hR d k hk, hR a k hk, hq k hk]
  · rename_i m r
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    dsimp only at e
    split at e
    case isFalse => cases e
    rename_i ho
    obtain ⟨hb, ho1, ho2, ho3⟩ := ho
    subst hb
    cases e
    have ea : s.ea m = s₀.gpr .rdi + BitVec.ofNat 64 o := by rw [baseOff_ok hbo, h.gpr]
    have hin : InRegions s.wr (s₀.gpr .rdi + BitVec.ofNat 64 o) 32 := by rw [h.wr]; exact hc.win o ho2
    refine ⟨{ s with mem := s.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 o) (s.vy r) },
      by simp only [exec, ea, State.store256, hin, ite_true], ?_⟩
    refine ⟨fun r' k hk => h.reg r' k hk, ?_, ?_, ?_, ?_⟩
    · rw [← h.eq]; rfl
    · simp only [stores]
      rw [← h.mem]
      congr 1
      refine VG.Proof.X25519.X86_64.Ifma.eq_of_qword256 fun k hk => ?_
      rw [qword256_val _ _ hk]; exact (hR r k hk).symm
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨ho1, ho2⟩
      · exact h.al x hx
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ho3
      · exact h.lo x hx
  · cases e

/-- A block of instructions. -/
theorem srun_ok {P : Par} {s₀ : State} (hc : Ctx P s₀) :
    ∀ (is : List Instr) {σ σ' : VSym} {s : State}, SRel P σ s₀ s → σ.run P is = some σ' →
      WP isa (.block is) s (SRel P σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [VSym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, srun_ok hc is h₁ e₂⟩

end VG.Proof.P256.X86_64.Ifma
