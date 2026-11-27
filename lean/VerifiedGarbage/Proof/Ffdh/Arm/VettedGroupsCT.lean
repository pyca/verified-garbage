module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Ffdh.Arm.VettedGroups`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.VettedGroupsLoop`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.VettedGroupsStep`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.VettedGroupsBlocks`, which this module and modules that import it used -/

section

/-! The vetted-group scanner reuses the RSA byte-comparison proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd
open VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem triple (n : Nat) : (BitVec.ofNat 32 n + (BitVec.ofNat 32 n <<< 1)) = BitVec.ofNat 32 (3 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega_using []

 theorem header_ok (s : State) {p : BitVec 32} {g : Group} {k : Nat}
    (h : RecordAt p g s) (ptr : s.gpr .r4 = p) (width : s.gpr .r6 = BitVec.ofNat 32 k)
    (kfit : k < 2 ^ 32) :
    WP isa (.block header) s fun t =>
      (t.gpr .r4 = p + 8 ∧ t.gpr .r5 = BitVec.ofNat 32 (3 * g.len) ∧
       t.gpr .r11 = BitVec.ofNat 32 g.bits ∧ t.gpr .r2 = 1 ∧
       t.z = decide (g.len = k) ∧ t.mem = s.mem) ∧ Rest [.r2, .r4, .r5, .r11] s t := by
  refine withRest_all [.r2, .r4, .r5, .r11] ?_ (by rfl) (by rfl)
  have eq : (BitVec.ofNat 32 g.len - BitVec.ofNat 32 k == 0) = decide (g.len = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro equal
      have number := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.lenFit,
        Nat.mod_eq_of_lt kfit] at number
      change (2 ^ 32 - k + g.len) % 2 ^ 32 = 0 at number
      have := h.lenFit
      omega_using [kfit, number, this]
    · intro equal
      subst k
      simp
  have rb : InRegions (s.rd ++ s.wr) (State.addr (p + 4#32)) 4 := h.readBits
  have vb : s.mem.readW (State.addr (p + 4#32)) 32 = BitVec.ofNat 32 g.bits := h.bits
  unfold header
  ffrun [ptr, width, h.readLen, rb, h.len, vb, BitVec.add_zero, BitVec.ofNat_eq_ofNat, triple, eq]
  exact eq

 theorem compareArgs_ok (s : State) :
    WP isa (.block compareArgs) s fun t =>
      (t.gpr .r0 = s.gpr .r9 ∧ t.gpr .r1 = s.gpr .r4 ∧ t.gpr .lr = s.gpr .r10 ∧
        t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  refine withRest_all [.r0, .r1, .r2, .lr] ?_ (by rfl) (by rfl)
  unfold compareArgs
  ffrun []

 theorem compare_ok (s : State) {src p : BitVec 32} {k : Nat} {dom : List Byte} {g : Group}
    (source : Source src k dom s) (record : RecordAt p g s) (same : g.len = k)
    (first : s.gpr .r9 = src) (second : s.gpr .r4 = p + 8)
    (count : s.gpr .r10 = BitVec.ofNat 32 dom.length) :
    WP isa VG.Impl.Ffdh.Arm.VettedGroups.compare s fun t =>
      (t.gpr .r2 = 0 ↔ dom = g.domain.take dom.length) ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  have nfit : dom.length < 2 ^ 32 := by rw [← same] at source; have := record.fit; rcases source.length with h | h <;> omega_using [this, h]
  have limit : dom.length ≤ 3 * g.len := by rcases source.length with h | h <;> omega_using [same, h]
  have pfit : (p + 8).toNat + dom.length ≤ 2 ^ 32 := by
    change (p.toNat + 8) % 2 ^ 32 + dom.length ≤ 2 ^ 32
    have := record.fit
    omega_using [limit, this]
  have read : InRegions (s.rd ++ s.wr) (State.addr (p + 8)) dom.length := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CallLay.inRegions_sub record.read (off := 0) (by omega_using [limit] : 0 + dom.length ≤ 3 * g.len) (by have := record.fit; omega_using [this])
  rw [VG.Impl.Ffdh.Arm.VettedGroups.compare, WP.seq_iff]
  refine WP.mono (compareArgs_ok s) ?_
  rintro u ⟨⟨r0, r1, lr, zero, memU⟩, restU⟩
  refine WP.mono (VG.Proof.Bignum.Arm.compareBuffer_ok u source.positive nfit source.fit pfit
    (by rw [restU.rd, restU.wr]; exact source.read)
    (by rw [restU.rd, restU.wr]; exact read)
    (r0.trans first) (r1.trans second) (lr.trans count) zero) ?_
  rintro t ⟨equal, memT, restT⟩
  have front : Spec.Rsa.bytesAt s.mem (State.addr (p + 8)) dom.length = g.domain.take dom.length := by
    rw [← record.bytes]
    simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left limit]
  rw [memU, source.bytes, front] at equal
  exact ⟨equal, memT.trans memU, (restU.mono (by simp)).trans restT⟩

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! ### `Ffdh.Arm.VettedGroupsFinish`, which this module and modules that import it used -/

section

/-! Public success and continuation controls of the exact-domain scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd
open VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem zero_test (s : State) (r : Reg) :
    WP isa (.block [.cmp r (.imm 0)]) s fun t =>
      (t.z = (s.gpr r == 0) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  ffrun []
  change (s.gpr r - 0#32 == 0#32) = (s.gpr r == 0#32)
  rw [BitVec.sub_zero]

 theorem matched_ok (s : State) :
    WP isa (.block matched) s fun t => (t.gpr .r7 = 0 ∧ t.mem = s.mem) ∧ Rest [.r7] s t := by
  refine withRest_all [.r7] ?_ (by rfl) (by rfl)
  unfold matched
  ffrun []

 theorem next_ok (s : State) {table : BitVec 32} {len n : Nat}
    (ptr : s.gpr .r4 = table + 8) (size : s.gpr .r5 = BitVec.ofNat 32 (3 * len))
    (count : s.gpr .r7 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block next) s fun t =>
      (t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * len) ∧
       t.gpr .r7 = BitVec.ofNat 32 n ∧ t.mem = s.mem) ∧ Rest [.r4, .r7, .r11] s t := by
  refine withRest_all [.r4, .r7, .r11] ?_ (by rfl) (by rfl)
  have pc : (table + 8) + BitVec.ofNat 32 (3 * len) = table + BitVec.ofNat 32 (8 + 3 * len) := by
    change (table + BitVec.ofNat 32 8) + BitVec.ofNat 32 (3 * len) = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have nc : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
    change BitVec.ofNat 32 (n + 1) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  unfold next
  ffrun [ptr, size, count, pc, nc, BitVec.ofNat_eq_ofNat]
  exact ⟨pc, nc⟩

 theorem finish_ok (s : State) {table : BitVec 32} {len bits n : Nat} {hit : Prop}
    [Decidable hit] (equal : s.gpr .r2 = 0 ↔ hit)
    (ptr : s.gpr .r4 = table + 8) (size : s.gpr .r5 = BitVec.ofNat 32 (3 * len))
    (cap : s.gpr .r11 = BitVec.ofNat 32 bits) (count : s.gpr .r7 = BitVec.ofNat 32 (n + 1))
    (fit : n < 2 ^ 32) :
    WP isa finish s fun t => t.mem = s.mem ∧
      (if hit then t.gpr .r11 = BitVec.ofNat 32 bits ∧ t.gpr .r7 = 0 ∧ t.z = true else
        t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * len) ∧
          t.gpr .r7 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0)) ∧
      Rest [.r4, .r7, .r11] s t := by
  rw [finish, WP.seq_iff]
  refine WP.mono (zero_test s .r2) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have test : u.z = decide hit := by
    rw [zero]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, decide_eq_true_eq] using equal
  rw [WP.seq_iff]
  refine WP.ite (decide hit) (by simpa only [eval] using congrArg some test) ?_ ?_
  · intro yes
    have hy : hit := of_decide_eq_true yes
    refine WP.mono (matched_ok u) ?_
    rintro v ⟨⟨countV, memV⟩, restV⟩
    refine WP.mono (zero_test v .r7) ?_
    rintro t ⟨⟨zeroT, memT⟩, restT⟩
    refine ⟨memT.trans (memV.trans memU), ?_, ?_⟩
    · rw [ite_eq_left hy]
      exact ⟨(restT.gpr .r11 (by simp)).trans ((restV.gpr .r11 (by simp)).trans ((restU.gpr .r11 (by simp)).trans cap)),
        (restT.gpr .r7 (by simp)).trans countV, by rw [zeroT, countV]; rfl⟩
    · exact (restU.mono (by simp)).trans ((restV.mono (by simp)).trans (restT.mono (by simp)))
  · intro no
    have hn : ¬hit := of_decide_eq_false no
    refine WP.mono (next_ok u ((restU.gpr .r4 (by simp)).trans ptr)
      ((restU.gpr .r5 (by simp)).trans size) ((restU.gpr .r7 (by simp)).trans count)) ?_
    rintro v ⟨⟨capV, ptrV, countV, memV⟩, restV⟩
    refine WP.mono (zero_test v .r7) ?_
    rintro t ⟨⟨zeroT, memT⟩, restT⟩
    refine ⟨memT.trans (memV.trans memU), ?_, ?_⟩
    · rw [ite_eq_right hn]
      refine ⟨(restT.gpr .r11 (by simp)).trans capV, (restT.gpr .r4 (by simp)).trans ptrV,
        (restT.gpr .r7 (by simp)).trans countV, ?_⟩
      rw [zeroT, countV]
      exact VG.Proof.X25519.Arm.ofNat_beq_zero fit
    · exact (restU.mono (by simp)).trans (restV.trans (restT.mono (by simp)))

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! A table record either gives an exact match or advances to the next record. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem step_ok (s : State) {table src : BitVec 32} {k : Nat} {dom : List Byte}
    {g : Group} {gs : List Group} (source : Source src k dom s) (record : RecordAt table g s)
    (cursor : Cursor table src k dom (g :: gs) s) (kfit : k < 2 ^ 32) (fit : gs.length < 2 ^ 32) :
    WP isa step s fun t => t.mem = s.mem ∧
      (if g.len = k ∧ dom = g.domain.take dom.length then
        t.gpr .r11 = BitVec.ofNat 32 g.bits ∧ t.gpr .r7 = 0 ∧ t.z = true else
        t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * g.len) ∧
          t.gpr .r7 = BitVec.ofNat 32 gs.length ∧ t.z = decide (gs.length = 0)) ∧
      Rest clobbers s t := by
  rw [step, WP.seq_iff]
  refine WP.mono (header_ok s record cursor.ptr cursor.width kfit) ?_
  rintro u ⟨⟨ptrU, sizeU, capU, oneU, zeroU, memU⟩, restU⟩
  rw [WP.seq_iff]
  have choose : WP isa (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) u fun v =>
      (v.gpr .r2 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) ∧ v.mem = u.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r12, .lr] u v := by
    refine WP.ite (decide (g.len = k)) (by simp only [eval, zeroU]) ?_ ?_
    · intro yes
      have same := of_decide_eq_true yes
      refine WP.mono (compare_ok u (source.after memU restU) (record.after memU restU) same
        ((restU.gpr .r9 (by simp)).trans cursor.source) ptrU
        ((restU.gpr .r10 (by simp)).trans cursor.length)) ?_
      rintro v ⟨equal, mem, rest⟩
      exact ⟨by simpa only [same, true_and] using equal, mem, rest⟩
    · intro no
      have different := of_decide_eq_false no
      refine WP.block_nil ⟨?_, rfl, Rest.refl _ _⟩
      rw [oneU]
      simp only [show (1 : BitVec 32) ≠ 0 by decide, false_iff]
      exact fun h => different h.1
  refine WP.mono choose ?_
  rintro v ⟨equal, memV, restV⟩
  refine WP.mono (finish_ok v equal
    ((restV.gpr .r4 (by simp)).trans ptrU) ((restV.gpr .r5 (by simp)).trans sizeU)
    ((restV.gpr .r11 (by simp)).trans capU)
    ((restV.gpr .r7 (by simp)).trans ((restU.gpr .r7 (by simp)).trans cursor.count)) fit) ?_
  rintro t ⟨memT, result, restT⟩
  exact ⟨memT.trans (memV.trans memU), result,
    (restU.mono (by simp [clobbers])).trans
      ((restV.mono (by simp [clobbers])).trans (restT.mono (by simp [clobbers])))⟩

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! The exact-domain scan returns the first matching table record or zero. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem loop_ok {table src : BitVec 32} {k : Nat} {dom : List Byte} {gs : List Group}
    (s : State) (source : Source src k dom s) (tableAt : TableAt table gs s)
    (cursor : Cursor table src k dom gs s) (positive : gs ≠ [])
    (kfit : k < 2 ^ 32) (fit : gs.length < 2 ^ 32) :
    WP isa loop s fun t => t.gpr .r11 = BitVec.ofNat 32 (recognize gs k dom) ∧
      t.mem = s.mem ∧ Rest clobbers s t := by
  induction gs generalizing s table with
  | nil => exact False.elim (positive rfl)
  | cons g gs ih =>
    have nextFit : gs.length < 2 ^ 32 := by simp only [List.length_cons] at fit; omega_using [fit]
    obtain ⟨trace, u, run, memU, result, restU⟩ := step_ok s source tableAt.1 cursor kfit nextFit
    by_cases hit : g.len = k ∧ dom = g.domain.take dom.length
    · rw [ite_eq_left hit] at result
      refine ⟨_, u, Exec.loopExit run ?_, ?_, memU, restU⟩
      · simp only [eval, result.2.2, Bool.not_true]
      · simpa only [recognize, ite_eq_left hit] using result.1
    · rw [ite_eq_right hit] at result
      by_cases last : gs = []
      · subst gs
        refine ⟨_, u, Exec.loopExit run ?_, ?_, memU, restU⟩
        · simp only [eval, result.2.2.2, List.length_nil, decide_true, Bool.not_true]
        · simp only [recognize, ite_eq_right hit]
          apply BitVec.eq_of_toNat_eq
          rw [result.1]
          rfl
      · have cursorU : Cursor (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs u :=
          ⟨result.2.1, result.2.2.1,
            (restU.gpr .r6 (by simp [clobbers])).trans cursor.width,
            (restU.gpr .r9 (by simp [clobbers])).trans cursor.source,
            (restU.gpr .r10 (by simp [clobbers])).trans cursor.length⟩
        have ready := ih u (source.after memU restU) (tableAt.2.after memU restU) cursorU last nextFit
        obtain ⟨traceT, t, runT, capT, memT, restT⟩ := ready
        refine ⟨_, t, Exec.loopNext run ?_ runT, ?_, memT.trans memU, restU.trans restT⟩
        · have hn : gs.length ≠ 0 := by intro hz; apply last; exact List.eq_nil_of_length_eq_zero hz
          simp only [eval, result.2.2.2, hn, decide_false, Bool.not_false]
        · simpa only [recognize, ite_eq_right hit] using capT

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! Complete read-only vetted-domain recognition in an FFDH frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem entry_raw_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block entry) s fun t =>
      ((t.gpr .r4 = s.syms tableSym ∧ t.gpr .r7 = 10 ∧
        t.gpr .r6 = BitVec.ofNat 32 p.k ∧ t.gpr .r9 = p.domain ∧
        t.gpr .r10 = BitVec.ofNat 32 p.dom.length) ∧ t.gpr .r8 = p.base ∧ t.mem = s.mem) ∧
      Rest [.r4, .r6, .r7, .r8, .r9, .r10] s t := by
  refine withRest_all [.r4, .r6, .r7, .r8, .r9, .r10] ?_ (by rfl) (by rfl)
  have addr (d : Nat) (hd : d + 4 ≤ 72) :
      State.addr (s.sp + BitVec.ofNat 32 d) = VG.Proof.Mont.off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega_using [hd, this])
  have r24 := h.locals.read (d := 24) (by decide)
  have r28 := h.locals.read (d := 28) (by decide)
  have r32 := h.locals.read (d := 32) (by decide)
  have v24 := h.saved 24 h24
  have v28 := h.saved 28 h28
  have v32 := h.saved 32 h32
  unfold entry
  ffrun [exec, State.load32, addr 24 (by decide), addr 28 (by decide), addr 32 (by decide),
    r24, r28, r32, v24, v28, v32, Inputs.slotValue, h.ptr, BitVec.ofNat_eq_ofNat]
  rfl

 theorem entry_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block entry) s fun t =>
      (Cursor (s.syms tableSym) p.domain p.k p.dom groups t ∧ t.gpr .r8 = p.base ∧ t.mem = s.mem) ∧
      Rest [.r4, .r6, .r7, .r8, .r9, .r10] s t := by
  refine WP.mono (entry_raw_ok s h h24 h28 h32) ?_
  rintro t ⟨⟨⟨ptr, count, width, source, length⟩, saved, mem⟩, rest⟩
  exact ⟨⟨⟨ptr, count, width, source, length⟩, saved, mem⟩, rest⟩

 theorem restore_ok (s : State) :
    WP isa (.block [.mov .r0 (.reg .r8)]) s fun t =>
      (t.gpr .r0 = s.gpr .r8 ∧ t.mem = s.mem) ∧ Rest [.r0] s t := by
  refine withRest_all [.r0] ?_ (by rfl) (by rfl)
  ffrun []

 theorem code_ok (s : State) {p : Inputs} {slots : List Nat} (h : Context p slots s)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa code s fun t => Context p slots t ∧
      t.gpr .r11 = BitVec.ofNat 32 (recognize groups p.k p.dom) ∧
      t.mem = s.mem ∧ Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [code, WP.seq_iff]
  refine WP.mono (entry_ok s h h24 h28 h32) ?_
  rintro u ⟨⟨cursor, saved, memU⟩, restU⟩
  have source : Source p.domain p.k p.dom u :=
    ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega_using [this],
      h.domain.fits, by rw [restU.rd, restU.wr]; exact h.domain.readable,
      by rw [memU]; exact h.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
  rw [WP.seq_iff]
  refine WP.mono (loop_ok u source (table.after memU restU) cursor (by decide)
    (by have := p.maxLength; omega_using [this]) (by decide)) ?_
  rintro v ⟨cap, memV, restV⟩
  refine WP.mono (restore_ok v) ?_
  rintro t ⟨⟨ptr, memT⟩, restT⟩
  have ptrT : t.gpr .r0 = p.base := ptr.trans ((restV.gpr .r8 (by simp [clobbers])).trans saved)
  have mem : t.mem = s.mem := memT.trans (memV.trans memU)
  have rest : Rest VG.Proof.Bignum.Arm.roundClobbers s t :=
    (restU.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])).trans
      ((restV.mono (by simp [clobbers, VG.Proof.Bignum.Arm.roundClobbers])).trans
        (restT.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])))
  exact ⟨h.of_mem mem rest ptrT, (restT.gpr .r11 (by simp)).trans cap, mem, rest⟩

end VG.Proof.Ffdh.Arm.VettedGroups

end

end

/-! Exact-domain recognition compares public bytes on a public table schedule. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

theorem compare_ct : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9 ∧
    s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r10 = t.gpr .r10) VG.Impl.Ffdh.Arm.VettedGroups.compare (fun _ _ => True) := by
  have args : RelCT isa (fun s t => s.gpr .r9 = t.gpr .r9 ∧
      s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r10 = t.gpr .r10) (.block compareArgs)
      (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .lr = t.gpr .lr) := by
    intro s t tr1 tr2 u v h e1 e2
    have timing : RelCT isa (fun _ _ => True) (.block compareArgs) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _; exact Taint.agree_ofRegs (by simp)
    obtain ⟨_, u', eu, ⟨u0,u1,ul,_,_⟩,_⟩ := compareArgs_ok s
    obtain ⟨_, v', ev, ⟨v0,v1,vl,_,_⟩,_⟩ := compareArgs_ok t
    obtain ⟨-,rfl⟩ := Exec.det e1 eu
    obtain ⟨-,rfl⟩ := Exec.det e2 ev
    exact ⟨(timing _ _ _ _ _ _ trivial e1 e2).1,
      u0.trans (h.1.trans v0.symm), u1.trans (h.2.1.trans v1.symm), ul.trans (h.2.2.trans vl.symm)⟩
  exact args.seq (fun s t tr1 tr2 u v h e1 e2 => ⟨compareBytes_ct _ _ _ _ _ _ trivial trivial h e1 e2, trivial⟩)

theorem finish_ct : RelCT isa (fun s t => (s.gpr .r2 = 0 ↔ t.gpr .r2 = 0)) finish (fun _ _ => True) := by
  have test : RelCT isa (fun s t => (s.gpr .r2 = 0 ↔ t.gpr .r2 = 0))
      (.block [.cmp .r2 (.imm 0)]) (fun s t => s.z = t.z) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨_,u',eu,⟨zu,_⟩,_⟩ := zero_test s .r2
    obtain ⟨_,v',ev,⟨zv,_⟩,_⟩ := zero_test t .r2
    obtain ⟨-,rfl⟩ := Exec.det e1 eu
    obtain ⟨-,rfl⟩ := Exec.det e2 ev
    have timing : RelCT isa (fun _ _ => True) (.block [.cmp .r2 (.imm 0)]) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
      intro _ _ _; exact Taint.agree_ofRegs (by simp)
    refine ⟨(timing _ _ _ _ _ _ trivial e1 e2).1, ?_⟩
    change u.z = v.z
    rw [zu,zv]
    exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using h)
  have branch : RelCT isa (fun s t => s.z = t.z) (.ite .eq (.block matched) (.block next)) (fun _ _ => True) := by
    apply RelCT.ite (fun _ _ h => by simp only [eval,h])
    · exact (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  have last : RelCT isa (fun _ _ => True) (.block [.cmp .r7 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact test.seq (branch.seq last)

abbrev ScanReady (table src : BitVec 32) (k : Nat) (dom : List Byte) (gs : List Group) (s : State) : Prop :=
  Source src k dom s ∧ TableAt table gs s ∧ Cursor table src k dom gs s

theorem step_ct {table src : BitVec 32} {k : Nat} {dom : List Byte} {g : Group} {gs : List Group}
    (kfit : k < 2 ^ 32) :
    RelCT isa (fun s t => ScanReady table src k dom (g::gs) s ∧ ScanReady table src k dom (g::gs) t)
      step (fun _ _ => True) := by
  let H := fun s : State => Source src k dom s ∧ RecordAt table g s ∧
    s.gpr .r4 = table + 8 ∧ s.gpr .r9 = src ∧ s.gpr .r10 = BitVec.ofNat 32 dom.length ∧
    s.z = decide (g.len = k) ∧ s.gpr .r2 = 1
  have headerPost (s : State) (h : ScanReady table src k dom (g::gs) s) : WP isa (.block header) s H := by
    refine WP.mono (header_ok s h.2.1.1 h.2.2.ptr h.2.2.width kfit) ?_
    rintro u ⟨⟨ptr,_,_,one,zero,mem⟩,rest⟩
    exact ⟨h.1.after mem rest, h.2.1.1.after mem rest, ptr,
      (rest.gpr .r9 (by simp)).trans h.2.2.source, (rest.gpr .r10 (by simp)).trans h.2.2.length,zero,one⟩
  have headerCT : RelCT isa (fun s t => ScanReady table src k dom (g::gs) s ∧ ScanReady table src k dom (g::gs) t)
      (.block header) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h.1.2.2.ptr.trans h.2.2.2.ptr.symm)
  have branchPost (s : State) (h : H s) : WP isa (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) s
      (fun u => u.gpr .r2 = 0 ↔ g.len = k ∧ dom = g.domain.take dom.length) := by
    refine WP.ite (decide (g.len = k)) (by simp only [eval,h.2.2.2.2.2.1]) ?_ ?_
    · intro yes
      have same := of_decide_eq_true yes
      exact WP.mono (compare_ok s h.1 h.2.1 same h.2.2.2.1 h.2.2.1 h.2.2.2.2.1)
        (fun _ out => by simpa only [same,true_and] using out.1)
    · intro no
      refine WP.block_nil ?_
      rw [h.2.2.2.2.2.2]
      simp only [show (1:BitVec 32) ≠ 0 by decide,false_iff]
      exact fun hit => of_decide_eq_false no hit.1
  have branchCT : RelCT isa (fun s t => H s ∧ H t) (.ite .eq VG.Impl.Ffdh.Arm.VettedGroups.compare (.block [])) (fun _ _ => True) := by
    apply RelCT.ite (fun _ _ h => by simp only [eval,h.1.2.2.2.2.2.1,h.2.2.2.2.2.2.1])
    · exact compare_ct.mono (fun _ _ h => ⟨h.1.1.2.2.2.1.trans h.1.2.2.2.2.1.symm,
        h.1.1.2.2.1.trans h.1.2.2.2.1.symm, h.1.1.2.2.2.2.1.trans h.1.2.2.2.2.2.1.symm⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  unfold step
  exact ((headerCT.wp (fun s t h => ⟨headerPost s h.1,headerPost t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1,h.2.2⟩)).seq
    (((branchCT.wp (fun s t h => ⟨branchPost s h.1,branchPost t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2.1.trans h.2.2.symm)).seq finish_ct)



theorem loop_ct {table src : BitVec 32} {k : Nat} {dom : List Byte} {gs : List Group}
    (positive : gs ≠ []) (kfit : k < 2 ^ 32) (fits : gs.length < 2 ^ 32) :
    RelCT isa (fun s t => ScanReady table src k dom gs s ∧ ScanReady table src k dom gs t)
      loop (fun _ _ => True) := by
  let I := fun n (s t : State) => ∃ (table : BitVec 32) (g : Group) (gs : List Group),
    (g :: gs).length = n ∧ n < 2 ^ 32 ∧
      ScanReady table src k dom (g :: gs) s ∧ ScanReady table src k dom (g :: gs) t
  have body (n : Nat) : RelCT isa (I n) step fun s t =>
      eval .ne s = eval .ne t ∧ (eval .ne s = some false → True) ∧
      (eval .ne s = some true → ∃ m < n, I m s t) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨table, g, gs, size, fit, hs, ht⟩ := h
    have nextFit : gs.length < 2 ^ 32 := by simp only [List.length_cons] at size; omega_using [size, fit]
    have timing := step_ct kfit s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    obtain ⟨_, u', eu, memU, resultU, restU⟩ := step_ok s hs.1 hs.2.1.1 hs.2.2 kfit nextFit
    obtain ⟨_, v', ev, memV, resultV, restV⟩ := step_ok t ht.1 ht.2.1.1 ht.2.2 kfit nextFit
    obtain ⟨_, rfl⟩ := Exec.det e1 eu
    obtain ⟨_, rfl⟩ := Exec.det e2 ev
    by_cases hit : g.len = k ∧ dom = g.domain.take dom.length
    · rw [ite_eq_left hit] at resultU resultV
      have exitU : eval .ne u = some false := by simp only [eval, resultU.2.2, Bool.not_true]
      have exitV : eval .ne v = some false := by simp only [eval, resultV.2.2, Bool.not_true]
      exact ⟨timing.1, exitU.trans exitV.symm, fun _ => trivial,
        fun impossible => by rw [exitU] at impossible; cases impossible⟩
    · rw [ite_eq_right hit] at resultU resultV
      by_cases last : gs = []
      · subst gs
        have exitU : eval .ne u = some false := by simp only [eval, resultU.2.2.2, List.length_nil, decide_true, Bool.not_true]
        have exitV : eval .ne v = some false := by simp only [eval, resultV.2.2.2, List.length_nil, decide_true, Bool.not_true]
        exact ⟨timing.1, exitU.trans exitV.symm, fun _ => trivial,
          fun impossible => by rw [exitU] at impossible; cases impossible⟩
      · have nonzero : gs.length ≠ 0 := by intro eq; exact last (List.eq_nil_of_length_eq_zero eq)
        have continueU : eval .ne u = some true := by simp only [eval, resultU.2.2.2, nonzero, decide_false, Bool.not_false]
        have continueV : eval .ne v = some true := by simp only [eval, resultV.2.2.2, nonzero, decide_false, Bool.not_false]
        have readyU : ScanReady (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs u :=
          ⟨hs.1.after memU restU, hs.2.1.2.after memU restU,
            ⟨resultU.2.1, resultU.2.2.1,
              (restU.gpr .r6 (by simp [clobbers])).trans hs.2.2.width,
              (restU.gpr .r9 (by simp [clobbers])).trans hs.2.2.source,
              (restU.gpr .r10 (by simp [clobbers])).trans hs.2.2.length⟩⟩
        have readyV : ScanReady (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs v :=
          ⟨ht.1.after memV restV, ht.2.1.2.after memV restV,
            ⟨resultV.2.1, resultV.2.2.1,
              (restV.gpr .r6 (by simp [clobbers])).trans ht.2.2.width,
              (restV.gpr .r9 (by simp [clobbers])).trans ht.2.2.source,
              (restV.gpr .r10 (by simp [clobbers])).trans ht.2.2.length⟩⟩
        refine ⟨timing.1, continueU.trans continueV.symm, fun _ => trivial, fun _ => ?_⟩
        cases gs with
        | nil => exact False.elim (last rfl)
        | cons g' gs' => exact ⟨(g'::gs').length, by simp only [List.length_cons] at size ⊢; omega_using [size],
            _, g', gs', rfl, nextFit, readyU, readyV⟩
  have start : ∀ s t, ScanReady table src k dom gs s ∧ ScanReady table src k dom gs t → I gs.length s t := by
    intro s t h
    cases gs with
    | nil => exact False.elim (positive rfl)
    | cons g gs => exact ⟨table, g, gs, rfl, fits, h⟩
  exact (RelCT.loop I body gs.length).mono start (fun _ _ h => h)



theorem entry_ct : RelCT isa (fun s t => s.sp = t.sp) (.block entry) (fun _ _ => True) := by
  have pureHead : RelCT isa (fun _ _ => True) (.block [.mov .r8 (.reg .r0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  have head := relCT_keep_sp (pureHead.mono (fun _ _ _ => trivial) (fun _ _ h => h))
    (fun _ _ h => h)
  have tail : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.adrSym .r4 tableSym, .mov .r7 (.imm 10)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (head.seq (RelCT.block_append
    ((stackLoads_ct [(.r9,24),(.r10,28),(.r6,32)]).seq tail)))

theorem code_ct {p : Inputs} {slots : List Nat}
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ environment.holds p s) ∧
      (Context p slots t ∧ environment.holds p t) ∧ s.sp = t.sp ∧ environment.publicRel s t)
      code (fun _ _ => True) := by
  let P := fun s t : State => (Context p slots s ∧ environment.holds p s) ∧
    (Context p slots t ∧ environment.holds p t) ∧ s.sp = t.sp ∧ environment.publicRel s t
  let Q := fun s t : State => ∃ table, ScanReady table p.domain p.k p.dom groups s ∧
    ScanReady table p.domain p.k p.dom groups t
  have stage : RelCT isa P (.block entry) Q := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := entry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, ⟨cu,_,mu⟩,ru⟩ := entry_ok s h.1.1 h24 h28 h32
    obtain ⟨_, v', ev, ⟨cv,_,mv⟩,rv⟩ := entry_ok t h.2.1.1 h24 h28 h32
    obtain ⟨_,rfl⟩ := Exec.det e1 eu
    obtain ⟨_,rfl⟩ := Exec.det e2 ev
    have source (a b : State) (context : Context p slots a)
        (mem : b.mem = a.mem) (rest : VG.Proof.X25519.Arm.Rest [.r4,.r6,.r7,.r8,.r9,.r10] a b) :
        Source p.domain p.k p.dom b :=
      ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega_using [this],
        context.domain.fits, by rw [rest.rd,rest.wr]; exact context.domain.readable,
        by rw [mem]; exact context.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
    have tabU := h.1.2.1.after mu ru
    have tabV := h.2.1.2.1.after mv rv
    have symbol : s.syms tableSym = t.syms tableSym := h.2.2.2
    rw [← symbol] at tabV cv
    exact ⟨timing.1, s.syms tableSym,
      ⟨source s u h.1.1 mu ru, tabU, cu⟩, ⟨source t v h.2.1.1 mv rv, tabV, cv⟩⟩
  have scanning : RelCT isa Q loop (fun _ _ => True) := by
    apply RelCT.exists_
    intro table
    exact loop_ct (by decide) (by have := p.maxLength; omega_using [this]) (by decide)
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact stage.seq (scanning.seq restore)

end VG.Proof.Ffdh.Arm.VettedGroups
