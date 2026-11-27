module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `Dsa.X86.ProbablePrime.Environment`, which this module and modules that import it used -/

section

/-! # The public environment of DSA's probable-prime test on i686

The arguments, the stack pointer below the four saved registers, and the
trial-division table, with the facts about the memory that every stage of
the test keeps.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime

/-- The sizes the test supports: a candidate of whole native words, at
least two of them, in at most 64 64-bit words. -/
structure Bits (bits : Nat) : Prop where
  low : 64 ≤ bits
  high : bits ≤ 4096
  whole : bits % 32 = 0

structure Environment where
  bits : Nat
  workspace : BitVec 32
  capacity : Nat
  rand : BitVec 32
  randLength : Nat
  used : BitVec 32
  table : BitVec 32
  /-- The stack pointer below the four saved registers. -/
  p : BitVec 32

def Environment.width (E : Environment) : Nat := VG.Impl.Dsa.X86.ProbablePrime.width E.bits
def Environment.words (E : Environment) : Nat := E.bits / 32
def Environment.base (E : Environment) : Addr := E.workspace.setWidth 64
def Environment.size (E : Environment) : Nat := 8 * E.capacity
def Environment.geometry (E : Environment) : Geometry := ⟨E.base, E.size, E.width⟩
def Environment.scratch (E : Environment) : Nat := scratchBytes E.width
def Environment.workspaceRegion (E : Environment) : Region := ⟨E.base, E.size⟩
def Environment.randRegion (E : Environment) : Region := ⟨E.rand.setWidth 64, E.randLength⟩
def Environment.usedRegion (E : Environment) : Region := ⟨E.used.setWidth 64, 8⟩
def Environment.tableRegion (E : Environment) : Region := ⟨E.table.setWidth 64, 8192⟩

/-- The candidate in memory `m`. -/
def Environment.candidate (E : Environment) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off E.base E.scratch) (E.bits / 8))

structure Environment.Valid (E : Environment) : Prop where
  bits : Bits E.bits
  room : E.scratch + E.bits / 8 ≤ E.size
  workspaceFit : E.workspace.toNat + E.size ≤ 2 ^ 32
  randFit : E.rand.toNat + E.randLength ≤ 2 ^ 32
  randLengthFit : E.randLength < 2 ^ 32
  usedFit : E.used.toNat + 8 ≤ 2 ^ 32
  tableFit : E.table.toNat + 8192 ≤ 2 ^ 32
  low : 136 ≤ E.p.toNat
  argsFit : E.p.toNat + 40 ≤ 2 ^ 32
  workspaceStack : E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 136 ≤ E.p.toNat
  argsFar : (⟨(E.p + 20#32).setWidth 64, 20⟩ : Region).Disjoint E.workspaceRegion
  randWorkspace : E.randRegion.Disjoint E.workspaceRegion
  randUsed : E.randRegion.Disjoint E.usedRegion
  usedWorkspace : E.usedRegion.Disjoint E.workspaceRegion
  tableWorkspace : E.tableRegion.Disjoint E.workspaceRegion
  tableUsed : E.tableRegion.Disjoint E.usedRegion
  savedFar : ∀ r ∈ [E.workspaceRegion, E.randRegion, E.usedRegion, E.tableRegion],
    r.Disjoint ⟨E.p.setWidth 64, 16⟩
  stackFar : ∀ r ∈ [E.workspaceRegion, E.randRegion, E.usedRegion, E.tableRegion],
    r.Disjoint (below E.p 136)

/-- The bytes of the working space past the header and the arrays, which
the test never changes. -/
def Tail (E : Environment) (m m' : Mem) : Prop :=
  ∀ i, E.scratch ≤ i → i < E.size → m' (off E.base i) = m (off E.base i)

theorem Tail.trans {E : Environment} {a b c : Mem} (A : Tail E a b) (B : Tail E b c) : Tail E a c :=
  fun i lo hi => (B i lo hi).trans (A i lo hi)

/-- The memory every stage keeps: the tape, the table, the `used` output and
the candidate. -/
structure Memory (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  usedWrite : Rt.Ws s (E.used.setWidth 64) 8
  randRead : InRegions (s.rd ++ s.wr) (E.rand.setWidth 64) E.randLength
  entropy : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.randLength = entropy
  tableRead : InRegions (s.rd ++ s.wr) (E.table.setWidth 64) 8192
  table : ∀ i < 1024, s.mem.readW (off (E.table.setWidth 64) (8 * i)) 64 =
    BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i)
  symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = E.table
  candidate : E.candidate s.mem = c

/-- What every stage keeps: the arguments the candidate code reads from the
header, and the memory. -/
structure Input (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  scratch : Scr s E.base E.size
  stack : s.gpr .esp = E.p
  randPtr : s.mem.readW (off E.base 28) 32 = E.rand
  randLength : w32 s.mem E.base 32 = E.randLength
  capacity : w32 s.mem E.base 40 = E.capacity
  usedPtr : s.mem.readW (off E.base 44) 32 = E.used
  memory : Memory E c entropy s

/-- After the candidate's import: the candidate and the candidate minus one
in arrays 0 and 5, and no octet of the tape read yet. -/
structure Loaded (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  input : Input E c entropy s
  value : val32 s.mem E.base (E.geometry.array 0) E.geometry.words = c
  minusOne : val32 s.mem E.base (E.geometry.array 5) E.geometry.words = c - 1
  count : w32 s.mem E.base 152 = 0

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! ### `Dsa.X86.ProbablePrime.Enter`, which the modules that import this one used -/

section

/-! ### `Dsa.X86.ProbablePrime.Memory`, which this module and modules that import it used -/

section

/-! # The tape, the table and the candidate outlive every stage -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The regions a stage may write: the workspace and the stack below the
saved registers. -/
def WorkFrame (E : Environment) (m m' : Mem) : Prop := Frame [E.workspaceRegion, below E.p 136] m m'

theorem WorkFrame.trans {E : Environment} {a b c : Mem} (A : WorkFrame E a b) (B : WorkFrame E b c) :
    WorkFrame E a c := fun x out => (B x out).trans (A x out)

/-- The regions the test may write. -/
def MutableFrame (E : Environment) (m m' : Mem) : Prop :=
  Frame [E.workspaceRegion, below E.p 136, E.usedRegion] m m'

theorem MutableFrame.trans {E : Environment} {a b c : Mem} (A : MutableFrame E a b) (B : MutableFrame E b c) :
    MutableFrame E a c := fun x out => (B x out).trans (A x out)

theorem WorkFrame.mutable {E : Environment} {m m' : Mem} (F : WorkFrame E m m') : MutableFrame E m m' :=
  F.mono (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem MutableFrame.of_used {E : Environment} {m m' : Mem} (F : Frame [E.usedRegion] m m') : MutableFrame E m m' :=
  F.mono (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem Environment.Valid.randFar {E : Environment} (v : E.Valid) :
    ∀ r ∈ [E.workspaceRegion, below E.p 136], E.randRegion.Disjoint r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact v.randWorkspace
  · exact v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem Environment.Valid.tableFar {E : Environment} (v : E.Valid) :
    ∀ r ∈ [E.workspaceRegion, below E.p 136], E.tableRegion.Disjoint r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact v.tableWorkspace
  · exact v.stackFar _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem Tail.candidate {E : Environment} (v : E.Valid) {m m' : Mem} (T : Tail E m m') :
    E.candidate m' = E.candidate m := by
  unfold Environment.candidate Spec.Rsa.bytesAt
  congr 1
  apply List.map_congr_left
  intro i hi
  have index := List.mem_range.mp hi
  have room := v.room
  rw [off, Offset.add_add]
  exact T _ (by omega_using []) (by omega_using [index, room])

theorem Memory.keep {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (M : Memory E c entropy s) {regs : List Reg} (K : Keeps regs s t) (F : WorkFrame E s.mem t.mem)
    (T : Tail E s.mem t.mem)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Memory E c entropy t := by
  refine ⟨M.usedWrite.of_keeps K, ?_, ?_, ?_, ?_, symbol.trans M.symbol, (T.candidate v).trans M.candidate⟩
  · rw [K.2.1, K.2.2]; exact M.randRead
  · rw [VG.Proof.RsaKeyGen.frame_bytesAt F v.randFar (by have := v.randLengthFit; omega_using [this])]
    exact M.entropy
  · rw [K.2.1, K.2.2]; exact M.tableRead
  · intro i index
    rw [F.readW (r := E.tableRegion)
      (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega_using [index]) (by omega_using [index])) v.tableFar (by decide)]
    exact M.table i index

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! # The entry copies the five arguments into the workspace header -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime VG.Impl.Mont.X86

def argsRegion (p : BitVec 32) : Region := ⟨(p + 20#32).setWidth 64, 20⟩

def Environment.argument (E : Environment) : Nat → BitVec 32
  | 0 => E.workspace
  | 1 => BitVec.ofNat 32 E.capacity
  | 2 => E.rand
  | 3 => BitVec.ofNat 32 E.randLength
  | _ => E.used

/-- The arguments stay readable on the stack while the header is written. -/
structure ArgContext (E : Environment) (s : State) : Prop where
  scratch : Scr s E.base E.size
  sp : s.gpr .esp = E.p
  read : ∀ i < 5, readSrc s (.mem (Compact.arg i)) = some (E.argument i)

theorem ArgContext.address {E : Environment} (v : E.Valid) {s : State} (C : ArgContext E s) {i : Nat} (index : i < 5) :
    s.ea (Compact.arg i) = off (argsRegion E.p).base (4 * i) := by
  change addr (s.gpr .esp) (20 + 4 * i) = _
  rw [C.sp, addr_eq (by have := v.argsFit; omega_using [index, this])]
  have start : (E.p + 20#32).setWidth 64 = off (E.p.setWidth 64) 20 := addr_eq (by have := v.argsFit; omega_using [this])
  change off (E.p.setWidth 64) (20 + 4 * i) = off ((E.p + 20#32).setWidth 64) (4 * i)
  rw [start]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem ArgContext.keep {E : Environment} (v : E.Valid) {s t : State} (C : ArgContext E s)
    (K : Keeps [.eax] s t) (F : Frame [E.workspaceRegion] s.mem t.mem) : ArgContext E t := by
  refine ⟨C.scratch.of_keeps K (by decide), (K.1 .esp (by decide)).trans C.sp, ?_⟩
  intro i index
  have eaT : t.ea (Compact.arg i) = s.ea (Compact.arg i) := by
    change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
    rw [K.1 .esp (by decide)]
  have memory : t.mem.readW (s.ea (Compact.arg i)) 32 = s.mem.readW (s.ea (Compact.arg i)) 32 := by
    rw [C.address v index]
    exact F.readW (r := argsRegion E.p)
      (Offset.contains_base _ (by change 4 * i + 4 ≤ 20; omega_using [index]) (by omega_using [index] : 4 * i < 2 ^ 64))
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.argsFar) (by decide)
  have same : readSrc t (.mem (Compact.arg i)) = readSrc s (.mem (Compact.arg i)) := by
    show t.load32 (t.ea (Compact.arg i)) = s.load32 (s.ea (Compact.arg i))
    simp only [State.load32, eaT, K.2.1, K.2.2, memory]
  exact same.trans (C.read i index)

theorem Environment.Valid.header {E : Environment} (v : E.Valid) : 256 ≤ E.size := by
  have := v.room
  unfold Environment.scratch scratchBytes VG.Impl.Bignum.X86.PublicContext.slot VG.Impl.Bignum.hdrBytes at this
  omega_using [this]

/-- A store of EAX into header byte `d` changes only those four bytes. -/
theorem store_ok {E : Environment} (v : E.Valid) {s : State} (C : ArgContext E s) {d : Nat} (fit : d + 4 ≤ 256) :
    WP isa (.block [.store (sc d) .eax]) s fun t =>
      ArgContext E t ∧ t.mem.readW (off E.base d) 32 = s.gpr .eax ∧ Outside E.base d 4 s.mem t.mem ∧
      Keeps [] s t := by
  have header := v.header
  refine wp_storeS (C.scratch.ea (by omega_using [fit, header])) (C.scratch.write (by omega_using [fit, header])) fun t T => WP.block_nil ?_
  have O : Outside E.base d 4 s.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by omega_using [fit])
  have F : Frame [E.workspaceRegion] s.mem t.mem := workspaceGlobalFrame (g := E.geometry) (rs := [(d, 4)])
    (Outs.of_outside O (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change d + 4 ≤ E.size; omega_using [fit, header])
  exact ⟨C.keep v ((T.keeps []).mono (by decide)) F, by rw [T.mem, Mem.readW_writeW_self32], O, T.keeps []⟩

theorem copy_ok {E : Environment} (v : E.Valid) {s : State} (C : ArgContext E s) {i d : Nat}
    (index : i < 5) (fit : d + 4 ≤ 256) :
    WP isa (.block (copy i d)) s fun t =>
      ArgContext E t ∧ t.mem.readW (off E.base d) 32 = E.argument i ∧ Outside E.base d 4 s.mem t.mem ∧
      Keeps [.eax] s t := by
  unfold copy
  refine wp_movS (C.read i index) fun a A _ => ?_
  have Ca : ArgContext E a := C.keep v A.keeps (by rw [A.mem]; exact Frame.refl _ _)
  refine WP.mono (store_ok v Ca fit) fun t ⟨T, value, O, K⟩ => ?_
  rw [A.gpr] at value
  rw [A.mem] at O
  exact ⟨T, value, O, A.keeps.widen K⟩

/-- The state at the body's entry, below the four saved registers. -/
structure EntryInput (E : Environment) (c : Nat) (entropy : List Byte) (s : State) : Prop where
  workspace : Rt.Ws s E.base E.size
  sp : s.gpr .esp = E.p
  read : ∀ i < 5, readSrc s (.mem (Compact.arg i)) = some (E.argument i)
  memory : Memory E c entropy s

theorem Environment.Valid.baseNat {E : Environment} (_ : E.Valid) : E.base.toNat = E.workspace.toNat := by
  change (E.workspace.setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))]

theorem Environment.Valid.stkOk {E : Environment} (v : E.Valid) : StkOk E.p E.base E.size := by
  refine ⟨by have := v.low; omega_using [this], ?_⟩
  rcases v.workspaceStack with h | h
  · exact Or.inl h
  · exact Or.inr (by omega_using [h])

/-- The header the entry writes. -/
structure Header (E : Environment) (s : State) : Prop where
  scratch : Scr s E.base E.size
  stack : s.gpr .esp = E.p
  randPtr : s.mem.readW (off E.base 28) 32 = E.rand
  randLength : w32 s.mem E.base 32 = E.randLength
  capacity : w32 s.mem E.base 40 = E.capacity
  usedPtr : s.mem.readW (off E.base 44) 32 = E.used
  count : w32 s.mem E.base 152 = 0

theorem enter_raw {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy s) :
    WP isa (.block enter) s fun t =>
      Header E t ∧ Outside E.base 0 160 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  have header := v.header
  unfold enter
  simp only [List.append_assoc, List.singleton_append]
  refine wp_movS (I.read 0 (by decide)) fun a A _ => ?_
  have Sa : Scr a E.base E.size := by
    refine ⟨by rw [A.gpr]; rfl, by rw [A.keeps.2.2]; exact I.workspace.wr, ?_, ?_⟩
    · rw [v.baseNat]; exact v.workspaceFit
    · rw [A.other .esp (by decide), I.sp]; exact v.stkOk
  have Ca : ArgContext E a := by
    refine ⟨Sa, (A.other .esp (by decide)).trans I.sp, ?_⟩
    intro i index
    have address : a.ea (Compact.arg i) = s.ea (Compact.arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (Compact.arg i)) = readSrc s (.mem (Compact.arg i)) := by
      show a.load32 (a.ea (Compact.arg i)) = s.load32 (s.ea (Compact.arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (I.read i index)
  refine WP.block_append (WP.mono (copy_ok v Ca (i := 2) (d := 28) (by decide) (by decide))
    fun b ⟨Cb, randB, Ob, Kb⟩ => ?_)
  refine WP.block_append (WP.mono (copy_ok v Cb (i := 3) (d := 32) (by decide) (by decide))
    fun d ⟨Cd, lenD, Od, Kd⟩ => ?_)
  refine WP.block_append (WP.mono (copy_ok v Cd (i := 1) (d := 40) (by decide) (by decide))
    fun e ⟨Ce, capE, Oe, Ke⟩ => ?_)
  refine WP.block_append (WP.mono (copy_ok v Ce (i := 4) (d := 44) (by decide) (by decide))
    fun f ⟨Cf, usedF, Of, Kf⟩ => ?_)
  refine wp_movS (v := 0#32) rfl fun g G _ => ?_
  have Cg : ArgContext E g := Cf.keep v G.keeps (by rw [G.mem]; exact Frame.refl _ _)
  refine WP.mono (store_ok v Cg (d := 152) (by decide)) fun t ⟨Ct, countT, Ot, Kt⟩ => ?_
  rw [G.gpr] at countT
  rw [G.mem] at Ot
  have keep (x : Nat) (o : Nat) {m m' : Mem} (O : Outside E.base o 4 m m') (small : x ≤ 256)
      (apart : x + 4 ≤ o ∨ o + 4 ≤ x) : m'.readW (off E.base x) 32 = m.readW (off E.base x) 32 :=
    BitVec.eq_of_toNat_eq (O.w32 apart (by omega_using [small]))
  have all : Outside E.base 0 160 s.mem t.mem := by
    rw [A.mem] at Ob
    exact (((((Ob.mono (by decide) (by decide)).trans (Od.mono (by decide) (by decide))).trans
      (Oe.mono (by decide) (by decide))).trans (Of.mono (by decide) (by decide))).trans
      (Ot.mono (by decide) (by decide)))
  have K : Keeps [.eax, .edi] s t :=
    (((((((A.keeps.mono (by decide)).trans (Kb.mono (by decide))).trans (Kd.mono (by decide))).trans
      (Ke.mono (by decide))).trans (Kf.mono (by decide))).trans (G.keeps.mono (by decide))).trans
      (Kt.mono (by decide)))
  refine ⟨⟨Ct.scratch, Ct.sp, ?_, ?_, ?_, ?_, ?_⟩, all, K⟩
  · rw [keep 28 152 Ot (by decide) (by decide), keep 28 44 Of (by decide) (by decide),
      keep 28 40 Oe (by decide) (by decide), keep 28 32 Od (by decide) (by decide), randB]
    rfl
  · unfold w32
    rw [keep 32 152 Ot (by decide) (by decide), keep 32 44 Of (by decide) (by decide),
      keep 32 40 Oe (by decide) (by decide), lenD]
    change (BitVec.ofNat 32 E.randLength).toNat = E.randLength
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.randLengthFit]
  · unfold w32
    rw [keep 40 152 Ot (by decide) (by decide), keep 40 44 Of (by decide) (by decide), capE]
    change (BitVec.ofNat 32 E.capacity).toNat = E.capacity
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.workspaceFit; unfold Environment.size at this; omega_using [this])]
  · rw [keep 44 152 Ot (by decide) (by decide), usedF]
    rfl
  · unfold w32
    rw [countT]
    rfl

theorem Environment.Valid.scratchLow {E : Environment} (_ : E.Valid) : 256 ≤ E.scratch := by
  unfold Environment.scratch scratchBytes VG.Impl.Bignum.X86.PublicContext.slot VG.Impl.Bignum.hdrBytes
  omega_using []

theorem Environment.Valid.tail_of_outside {E : Environment} (v : E.Valid) {o n : Nat} {m m' : Mem}
    (O : Outside E.base o n m m') (below : o + n ≤ E.scratch) : Tail E m m' := by
  intro i lo hi
  apply O
  have fit := v.workspaceFit
  rw [ofs_off0 E.base (by omega_using [hi, fit])]
  omega_using [below, lo]

theorem Environment.Valid.work_of_outside {E : Environment} (_ : E.Valid) {o n : Nat} {m m' : Mem}
    (O : Outside E.base o n m m') (fit : o + n ≤ E.size) : WorkFrame E m m' := by
  have F : Frame [E.workspaceRegion] m m' := workspaceGlobalFrame (g := E.geometry) (rs := [(o, n)])
    (Outs.of_outside O (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact fit)
  exact F.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)

theorem enter_ok {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy s) :
    WP isa (.block enter) s fun t =>
      Input E c entropy t ∧ w32 t.mem E.base 152 = 0 ∧ Outside E.base 0 160 s.mem t.mem ∧
      Keeps [.eax, .edi] s t := by
  refine WP.mono_syms (enter_raw v I) fun t ⟨H, O, K⟩ syms => ?_
  have T := v.tail_of_outside O (by have := v.scratchLow; omega_using [this])
  have W := v.work_of_outside O (by have := v.header; omega_using [this])
  exact ⟨⟨H.scratch, H.stack, H.randPtr, H.randLength, H.capacity, H.usedPtr,
    I.memory.keep v K W T (by rw [syms])⟩, H.count, O, K⟩

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! # The geometry of a candidate of `bits` bits -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG.Impl.Dsa.X86.ProbablePrime

theorem Bits.width_low {bits : Nat} (_ : Bits bits) : 4 ≤ width bits := by
  unfold width; omega_using []

theorem Bits.width_high {bits : Nat} (b : Bits bits) : width bits ≤ 64 := by
  have := b.high
  unfold width; omega_using [this]

theorem Bits.words_two {bits : Nat} (b : Bits bits) : 2 ≤ bits / 32 := by
  have := b.low; omega_using [this]

theorem Bits.words_le {bits : Nat} (b : Bits bits) : bits / 32 ≤ 2 * width bits := by
  have := b.whole
  unfold width; omega_using []

theorem Bits.bytes_eq {bits : Nat} (b : Bits bits) : 4 * (bits / 32) = bits / 8 := by
  have := b.whole; omega_using [this]

theorem Bits.draw_le {bits : Nat} (_ : Bits bits) : 8 * ((bits + 63) / 64) ≤ 8 * width bits := by
  unfold width; omega_using []

theorem Bits.draw_ge {bits : Nat} (b : Bits bits) : 4 * (bits / 32) ≤ 8 * ((bits + 63) / 64) := by
  have := b.whole; omega_using []

theorem Environment.Valid.width_low {E : Environment} (v : E.Valid) : 4 ≤ E.width := v.bits.width_low

theorem Environment.Valid.width_high {E : Environment} (v : E.Valid) : E.width ≤ 64 := v.bits.width_high

end VG.Proof.Dsa.X86.ProbablePrime
