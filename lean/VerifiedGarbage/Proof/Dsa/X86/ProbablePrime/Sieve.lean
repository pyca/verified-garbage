module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportRegions
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessZeros
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.Mont.RegionOutside
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Dsa.X86.ProbablePrime.Load`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateSave`, which only this module used -/

section

/-! # Saving and restoring an odd candidate changes only the destination -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSave
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateSave

theorem save_ok {s : State} {base : Addr} {size n src dst : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * n ≤ size) (dstFit : dst + 4 * n ≤ size)
    (sep : dst = src ∨ dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst)
    (odd : val32 s.mem base src n % 2 = 1) :
    WP isa (save n src dst) s fun t =>
      val32 t.mem base dst n + 1 = val32 s.mem base src n ∧
      Outside base dst (4 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok scratch positive srcFit dstFit sep)
    fun a ⟨Oa, value, Ka⟩ => ?_)
  obtain low : 0 < w32 a.mem base dst := LowWord.odd_low positive (by rw [value]; exact odd)
  refine WP.mono (LowWord.decrement_ok (scratch.of_keeps Ka (by decide)) positive dstFit low)
    fun t ⟨V, Ot, Kt⟩ => ?_
  rw [value] at V
  exact ⟨V, Oa.trans (Ot.mono (by omega_using []) (by omega_using [positive])), Ka.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.CandidateSave

end

end

/-! # The candidate's octets become arrays 0 and 5 of the workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime VG.Impl.Bignum.X86.PublicContext

theorem Environment.Valid.slotFit {E : Environment} (_ : E.Valid) {j : Nat} (index : j ≤ 27) :
    slot E.width j + 8 * E.width + 16 ≤ E.scratch := by
  unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes
  have := Nat.mul_le_mul_right (8 * E.width + 16) (show j + 1 ≤ 28 by omega_arith)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega_arith

theorem Environment.Valid.geometry {E : Environment} (v : E.Valid) : E.geometry.Valid := by
  refine ⟨v.bits.width_low, by have := v.bits.width_high; change VG.Impl.Dsa.X86.ProbablePrime.width E.bits ≤ 128; omega_arith, ?_⟩
  change E.geometry.array 28 ≤ E.size
  rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq E.geometry 28]
  have := v.room
  change E.scratch ≤ E.size
  omega_arith

/-- A stage that writes only the arrays keeps the input. -/
theorem Input.keepArrays {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (I : Input E c entropy s) {o n : Nat} (O : Outside E.base o n s.mem t.mem) (low : 256 ≤ o)
    (high : o + n ≤ E.scratch) {regs : List Reg} (K : Keeps regs s t) (edi : .edi ∉ regs) (esp : .esp ∉ regs)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Input E c entropy t := by
  have room := v.room
  have read (d : Nat) (small : d + 4 ≤ 256) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    BitVec.eq_of_toNat_eq (O.w32 (Or.inl (by omega_arith)) (by omega_arith))
  refine ⟨I.scratch.of_keeps K edi esp, (K.1 .esp esp).trans I.stack, ?_, ?_, ?_, ?_,
    I.memory.keep v K (v.work_of_outside O (by omega_arith)) (v.tail_of_outside O high) symbol⟩
  · rw [read 28 (by decide)]; exact I.randPtr
  · unfold w32; rw [read 32 (by decide)]; exact I.randLength
  · unfold w32; rw [read 40 (by decide)]; exact I.capacity
  · rw [read 44 (by decide)]; exact I.usedPtr

theorem load_raw {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : Input E c entropy s) (odd : c % 2 = 1) :
    WP isa (load E.words E.width) s fun t =>
      val32 t.mem E.base (slot E.width 0) (2 * E.width) = c ∧
      val32 t.mem E.base (slot E.width 5) (2 * E.width) = c - 1 ∧
      Outside E.base (slot E.width 0) (slot E.width 5 + 8 * E.width - slot E.width 0) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have b := v.bits
  have room := v.room
  have fit := v.workspaceFit
  obtain slot0 := v.slotFit (j := 0) (by decide)
  obtain slot5 := v.slotFit (j := 5) (by decide)
  have twoW := b.words_le
  have twoK := b.words_two
  have bytes := b.bytes_eq
  obtain e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega_arith
  obtain e5 : slot E.width 5 = 256 + 5 * (8 * E.width + 16) := by unfold slot stride VG.Impl.Bignum.hdrBytes; rfl
  obtain eS : E.scratch = 256 + 28 * (8 * E.width + 16) := by
    unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes; rfl
  have hk : E.words = E.bits / 32 := rfl
  have hw : E.width = width E.bits := rfl
  have hh : VG.Impl.Bignum.hdrBytes = 256 := rfl
  have hs : stride E.width = 8 * E.width + 16 := rfl
  unfold load
  refine WP.seq (wp_movS (v := s.gpr .edi) rfl fun a A _ => wp_addS (v := BitVec.ofNat 32 E.scratch) rfl
    fun e B _ => WP.block_nil ?_)
  obtain Ke : Keeps [.esi] s e := (A.keeps.mono (by decide)).trans B.keeps
  obtain Se := I.scratch.of_keeps Ke (by decide)
  obtain esi : e.gpr .esi = e.gpr .edi + BitVec.ofNat 32 E.scratch := by
    rw [B.gpr, A.gpr, Ke.1 .edi (by decide)]
  obtain srcAddr : (e.gpr .esi).setWidth 64 = off E.base E.scratch := by
    rw [esi]; exact Se.ea (by omega_arith)
  obtain dstAddr : (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64 = off E.base (slot E.width 0) :=
    Se.ea (by omega_arith)
  obtain srcNat : (e.gpr .esi).toNat = E.workspace.toNat + E.scratch := by
    rw [esi, BitVec.toNat_add, Se.edi_toNat, v.baseNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : E.scratch < 2 ^ 32), Nat.mod_eq_of_lt (by omega_arith)]
  obtain dstNat : (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).toNat = E.workspace.toNat + slot E.width 0 := by
    rw [BitVec.toNat_add, Se.edi_toNat, v.baseNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith : slot E.width 0 < 2 ^ 32), Nat.mod_eq_of_lt (by omega_arith)]
  obtain C : VG.Proof.RsaKeyGen.X86.Import.Context
      ⟨e.gpr .esi, e.gpr .edi + BitVec.ofNat 32 (slot E.width 0), E.words⟩ e := by
    refine VG.Proof.RsaKeyGen.X86.Import.context_of_regions (by show 0 < E.words; omega_arith)
      (by show (e.gpr .esi).toNat + 4 * E.words ≤ 2 ^ 32; omega_arith)
      (by show (e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).toNat + 4 * E.words ≤ 2 ^ 32; omega_arith) ?_ ?_ ?_
    · change InRegions _ ((e.gpr .esi).setWidth 64) (4 * E.words)
      rw [srcAddr]; exact Se.read (by omega_arith)
    · change InRegions _ ((e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64) (4 * E.words)
      rw [dstAddr]; exact Se.write (by omega_arith)
    · change (⟨(e.gpr .esi).setWidth 64, 4 * E.words⟩ : Region).Disjoint
        ⟨(e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64, 4 * E.words⟩
      rw [srcAddr, dstAddr]
      exact Offset.disjoint E.base (Or.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain loaded := VG.Proof.RsaKeyGen.X86.Import.load_ok C rfl rfl
  change WP isa (VG.Impl.RsaKeyGen.X86.Import.load E.words (slot E.width 0)) e _ at loaded
  refine WP.seq (WP.mono loaded fun f ⟨value, F, Kf⟩ => ?_)
  change (f.mem.read ((e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64) (4 * E.words)).toNat =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt e.mem ((e.gpr .esi).setWidth 64) (4 * E.words)) at value
  rw [dstAddr, srcAddr, VG.Proof.Bignum.read_eq_val32] at value
  obtain low : val32 f.mem E.base (slot E.width 0) E.words = c := by
    rw [value, ← I.memory.candidate]
    unfold Environment.candidate
    rw [hk, bytes, show e.mem = s.mem from by rw [B.mem, A.mem]]
  change Frame [⟨(e.gpr .edi + BitVec.ofNat 32 (slot E.width 0)).setWidth 64, 4 * E.words⟩] e.mem f.mem at F
  rw [dstAddr] at F
  obtain Of : Outside E.base (slot E.width 0) (4 * E.words) e.mem f.mem := frame_outside F (by omega_arith)
  obtain Sf := Se.of_keeps Kf (by decide)
  refine WP.seq (WP.mono (VG.Proof.RsaKeyGen.X86.WitnessLoad.zeros_ok Sf (slot E.width 0 + 4 * E.words)
    (2 * E.width - E.words) (by omega_arith)) fun g ⟨Zg, Og, Kg⟩ => ?_)
  obtain Sg := Sf.of_keeps Kg (by decide)
  obtain whole : val32 g.mem E.base (slot E.width 0) (2 * E.width) = c := by
    rw [show 2 * E.width = E.words + (2 * E.width - E.words) by omega_arith, val32_append, Zg, Nat.mul_zero,
      Nat.add_zero, Og.val32 (Or.inl (by omega_arith)) (by omega_arith), low]
  refine WP.mono (VG.Proof.RsaKeyGen.X86.CandidateSave.save_ok Sg (n := 2 * E.width)
    (src := slot E.width 0) (dst := slot E.width 5) (by omega_arith) (by omega_arith) (by omega_arith) (Or.inr (Or.inr (by omega_arith)))
    (by rw [whole]; exact odd)) fun t ⟨minus, Ot, Kt⟩ => ?_
  rw [whole] at minus
  refine ⟨?_, by omega_arith, ?_, ?_⟩
  · rw [Ot.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact whole
  · rw [B.mem, A.mem] at Of
    exact ((Of.mono (by omega_arith) (by omega_arith)).trans (Og.mono (by omega_arith) (by omega_arith))).trans
      (Ot.mono (by omega_arith) (by omega_arith))
  · exact (((Ke.mono (by decide)).trans (Kf.mono (by decide))).trans (Kg.mono (by decide))).trans
      (Kt.mono (by decide))

theorem load_ok {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : Input E c entropy s) (count : w32 s.mem E.base 152 = 0) (odd : c % 2 = 1) :
    WP isa (load E.words E.width) s fun t =>
      Loaded E c entropy t ∧ WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain slot5 := v.slotFit (j := 5) (by decide)
  obtain e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega_arith
  obtain e5 : slot E.width 5 = 256 + 5 * (8 * E.width + 16) := by unfold slot stride VG.Impl.Bignum.hdrBytes; rfl
  obtain eS : E.scratch = 256 + 28 * (8 * E.width + 16) := by
    unfold Environment.scratch scratchBytes slot stride VG.Impl.Bignum.hdrBytes; rfl
  refine WP.mono_syms (load_raw v I odd) fun t ⟨value, minus, O, K⟩ syms => ?_
  have fit := v.workspaceFit
  refine ⟨⟨I.keepArrays v O (by omega_arith) (by omega_arith) K (by decide) (by decide) (by rw [syms]), ?_, ?_, ?_⟩,
    v.work_of_outside O (by have := v.room; omega_arith), v.tail_of_outside O (by omega_arith), K⟩
  · rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq]; exact value
  · rw [← VG.Proof.RsaKeyGen.X86.Prepared.slot_eq]; exact minus
  · rw [O.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact count

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! # Trial division of the imported candidate -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.ProbablePrime VG.Impl.Bignum.X86.PublicContext
open VG.Proof.RsaKeyGen.X86

def Environment.sieveGeometry (E : Environment) : Sieve.Geometry :=
  ⟨E.p - 20#32, E.workspace + 256#32, E.table, E.width, VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width⟩

theorem Environment.Valid.candidateRoom {E : Environment} (v : E.Valid) : 256 + 8 * E.width ≤ E.size := by
  have := v.slotFit (j := 0) (by decide)
  have := v.room
  have e0 : slot E.width 0 = 256 := by unfold slot VG.Impl.Bignum.hdrBytes; omega_using []
  omega_arith

theorem Environment.Valid.candidateAddress {E : Environment} (v : E.Valid) :
    (E.workspace + 256#32).setWidth 64 = off E.base 256 := by
  have room := v.candidateRoom
  have width := v.width_low
  have fit := v.workspaceFit
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, off, Environment.base]
  have := E.workspace.isLt
  omega_using [room, width, fit]

theorem Environment.Valid.sieveCandidateSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.candidateRegion.Sub E.workspaceRegion := by
  change (⟨(E.workspace + 256#32).setWidth 64, 8 * E.width⟩ : Region).Sub E.workspaceRegion
  rw [v.candidateAddress]
  exact Offset.sub_base E.base v.candidateRoom

theorem Environment.Valid.sieveStackSub {E : Environment} (v : E.Valid) :
    E.sieveGeometry.stackRegion.Sub (below E.p 136) :=
  below_sub (by decide) v.low

theorem Environment.Valid.sieve_valid {E : Environment} (v : E.Valid) : E.sieveGeometry.Valid := by
  have width := v.width_low
  have high := v.width_high
  have room := v.candidateRoom
  have fit := v.workspaceFit
  have candidateNat : (E.workspace + 256#32).toNat = E.workspace.toNat + 256 := by
    rw [BitVec.toNat_add]
    change (E.workspace.toNat + 256) % 2 ^ 32 = E.workspace.toNat + 256
    omega_using [width, room, fit]
  refine ⟨by change 0 < E.width; exact Nat.lt_of_lt_of_le (by decide) width, by change E.width ≤ 128; omega_using [high], ?_, ?_, ?_, v.tableFit, ?_, ?_⟩
  · change 0 < VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change VG.Impl.RsaKeyGen.X86.Sieve.tableCount E.width ≤ 1024
    unfold VG.Impl.RsaKeyGen.X86.Sieve.tableCount
    split <;> decide
  · change (E.workspace + 256#32).toNat + 8 * E.width ≤ 2 ^ 32
    rw [candidateNat]
    omega_using [room, fit]
  · exact ((v.stackFar E.workspaceRegion List.mem_cons_self).sub_left v.sieveCandidateSub).sub_right
      v.sieveStackSub
  · exact (v.stackFar E.tableRegion (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right v.sieveStackSub

theorem sieve_context {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) :
    Sieve.Context E.sieveGeometry c (allocFrame 20 s) := by
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [L.input.stack]; have := v.low; omega_using [this]
  have stack := FilterStack.allocated_context fit
  rw [L.input.stack] at stack
  have room := v.candidateRoom
  refine ⟨stack, ?_, ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * E.width at index
    change InRegions ((allocFrame 20 s).rd ++ (allocFrame 20 s).wr)
      (off ((E.workspace + 256#32).setWidth 64) (4 * i)) 4
    rw [v.candidateAddress, off, Offset.add_add]
    obtain ⟨r, mem, contains⟩ := L.input.scratch.read (d := 256 + 4 * i) (n := 4) (by omega_using [room, index])
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp mem).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index d mem
    have native := v.sieve_valid
    have dBound : d = 0 ∨ d = 4 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using mem
    have address : addr (E.sieveGeometry.cursor i) d = off (E.table.setWidth 64) (8 * i + d) := by
      rw [addr_eq (by have := native.cursor_fit index; rcases dBound with rfl | rfl <;> omega_arith),
        native.cursor_addr index]
      exact Offset.add_add _ _ _
    rw [address]
    obtain ⟨r, member, contains⟩ := Candidate.read_offset L.input.memory.tableRead (d := 8 * i + d) (n := 4)
      (by rcases dBound with rfl | rfl <;> omega_using [index]) (by rcases dBound with rfl | rfl <;> omega_using [index])
    refine ⟨r, ?_, contains⟩
    simp only [allocFrame_rd, allocFrame_wr, List.mem_append, List.mem_cons]
    exact (List.mem_append.mp member).elim Or.inl (fun h => Or.inr (Or.inr h))
  · intro i index
    exact L.input.memory.table i index
  · change val32 s.mem ((E.workspace + 256#32).setWidth 64) 0 (2 * E.width) = c
    rw [v.candidateAddress, ← VG.Proof.Bignum.read_eq_val32, ← L.value, ← VG.Proof.Bignum.read_eq_val32]
    congr 2
    change off (off E.base 256) 0 = off E.base (Proof.Rsa.Mont.arrAt E.width 0)
    simp only [off, BitVec.add_zero, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero]

/-- A stage that writes only the stack below the saved registers keeps the
input. -/
theorem Loaded.keepStack {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (L : Loaded E c entropy s) (F : Frame [below E.p 136] s.mem t.mem) {regs : List Reg} (K : Keeps regs s t)
    (edi : .edi ∉ regs) (esp : .esp ∉ regs)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Loaded E c entropy t ∧ WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem := by
  have fit : E.base.toNat + E.size ≤ 2 ^ 32 := by rw [v.baseNat]; exact v.workspaceFit
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F fit
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact v.stackFar _ List.mem_cons_self)
  have T : Tail E s.mem t.mem := fun i _ hi => W i hi (by intro r mem; cases mem)
  have WF : WorkFrame E s.mem t.mem := F.mono (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have header := v.header
  have read (d : Nat) (small : d + 4 ≤ E.size) : t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    W.read32 small (by intro r mem; cases mem)
  have arrays (j : Nat) (index : j < 28) :
      val32 t.mem E.base (E.geometry.array j) E.geometry.words = val32 s.mem E.base (E.geometry.array j) E.geometry.words :=
    W.val32 ((v.geometry).arrayFit index) (by intro r mem; cases mem)
  refine ⟨⟨⟨L.input.scratch.of_keeps K edi esp, (K.1 .esp esp).trans L.input.stack, ?_, ?_, ?_, ?_,
    L.input.memory.keep v K WF T symbol⟩, ?_, ?_, ?_⟩, WF, T⟩
  · rw [read 28 (by omega_using [header])]; exact L.input.randPtr
  · unfold w32; rw [read 32 (by omega_using [header])]; exact L.input.randLength
  · unfold w32; rw [read 40 (by omega_using [header])]; exact L.input.capacity
  · rw [read 44 (by omega_using [header])]; exact L.input.usedPtr
  · rw [arrays 0 (by decide)]; exact L.value
  · rw [arrays 5 (by decide)]; exact L.minusOne
  · unfold w32; rw [read 152 (by omega_using [header])]; exact L.count

theorem sieve_ok {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (large : 8161 < c) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) s fun t =>
      Loaded E c entropy t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c).toNat ∧
      WorkFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar _ List.mem_cons_self
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    rw [L.input.scratch.edi_toNat, v.baseNat]
  refine WP.mono_syms (CandidateSieve.code_ok v.sieve_valid (sieve_context v L)
    (by rw [L.input.stack]; have := v.low; omega_using [this]) (by change s.gpr .edi + 256#32 = E.workspace + 256#32; rw [pointer])
    rfl L.input.memory.symbol
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega_using [this])]; have := v.low; omega_using [this])
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    large) fun t ⟨result, F, K⟩ syms => ?_
  have stackFrame : Frame [below E.p 136] s.mem t.mem := F.sub (by
    intro r mem
    simp only [Sieve.setupWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, v.sieveStackSub⟩
    · exact ⟨_, List.mem_singleton_self _, privateSub⟩)
  obtain ⟨Lt, W, T⟩ := L.keepStack v stackFrame K (by decide) (by decide) (by rw [syms])
  exact ⟨Lt, result, W, T, K⟩

end VG.Proof.Dsa.X86.ProbablePrime
