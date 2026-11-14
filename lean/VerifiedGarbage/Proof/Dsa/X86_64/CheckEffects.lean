module
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.LocalCallFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Finish
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
public import VerifiedGarbage.Proof.Dsa.X86_64.OneScan
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! ### `Dsa.X86_64.ReadyChecks`, which only this module used -/

section

/-! # Preserving both DSA arithmetic contexts across validation checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem nonmask_field (f : Field) (h : f ≠ .mask) : f.offset + 8 ≤ Field.mask.offset := by
  cases f <;> first | decide | exact False.elim (h rfl)

theorem rangeFrame_local {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : RangeFrame B o wx mem mem') (ho : o + slot wx 8 + tabBytes wx ≤ 2 ^ 64) :
    Frm B (localCallRanges o wx Field.mask.offset 8) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  intro x hx
  apply hf x
  · intro r hr
    have h := hx (128, 48) (by simp [localCallRanges])
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [arg, argLen] <;> omega_using [h]
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have h := hx (o + 136, slot wx 8 + tabBytes wx - 136) (by simp [localCallRanges])
    rcases ofs_rebase B x (o := o) (by omega_using [ho, hslot]) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at * <;> omega_arith
  · exact hx (Field.mask.offset, 8) (by simp [localCallRanges])

theorem checkFrame_field {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem') (ho : pWorkspace ≤ o)
    (f : Field) (hm : f ≠ .mask) : word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  have hm' := nonmask_field f hm
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro r hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; omega_using [hb]
  · left; omega_using [ho, hb]
  · exact Or.inl hm'

theorem Ready.afterCheck {L : ExecutionLayout} {s t : State} (side : ModulusSide)
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base side.offset (side.words L) (side.value L) (side.inverse L))
    (hf : RangeFrame L.base side.offset (side.words L) s.mem t.mem)
    (hk : Keep coreRegs s t) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hhi := (side.bounds L).2.2.2.2.1
  have ho : pWorkspace ≤ side.offset := by cases side <;> decide
  have hlf := rangeFrame_local hf (by omega_using [hau, hn, hhi])
  have hfields : ∀ f, f ≠ .mask → word t.mem L.base f.offset = L.fields f :=
    fun f hm => (checkFrame_field hlf ho f hm).trans (h.fields f hm)
  cases side
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields, hc,
      localCall_ready hlf h.qChild (by decide) (by omega_using [hqHi, hau, hn]) (Or.inr hpHi) (Or.inr (by decide))⟩
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields,
      localCall_ready hlf h.pChild (by decide) (by omega_using [hpHi, hqHi, hau, hn]) (Or.inl (by change pWorkspace + slot L.pWords 8 ≤ qWorkspace; omega_using [hpHi])) (Or.inr (by decide)), hc⟩

theorem Ready.afterMask {L : ExecutionLayout} {s t : State}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hf : Outside L.base Field.mask.offset 8 s.mem t.mem) (hk : Keep coreRegs s t) : Ready L t := by
  have hhi := (ModulusSide.p.bounds L).2.2.2.2.1
  have hqi := (ModulusSide.q.bounds L).2.2.2.2.1
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ activeBytes at hhi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqi
  have hn := h.scratch.nowrap
  have hau : activeBytes ≤ usedBytes := by decide
  refine ⟨hp, h.scratch.congr hk.2.2, ?_,
    maskWrite_child h.pChild hf (by decide) (by omega_using [hhi, hn, hau]),
    maskWrite_child h.qChild hf (by decide) (by omega_using [hqi, hn, hau])⟩
  intro f hm
  exact (hf.word (Or.inl (nonmask_field f hm))
    (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).trans (h.fields f hm)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ModulusMinus`, which only this module used -/

section

/-! ### `Dsa.X86_64.ResultCall`, which only this module used -/

section

/-! # DSA calls with a result binding and implicit modulus input -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem resultCall_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ModCtx u (off B o) (slot wx 8) wx minv m →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧ ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (.seq (.block (Core.operand result resultLen output ++ Core.enter o))
      (.seq body (seqs Core.finish))) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hn := hg.scr.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ output houtp (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hup, hul, _, hf, hk⟩ => ?_
  have hchild := call_ready child hf (by decide) (by decide) (by omega_using [hlo, hslot]) (by omega_using [hhi, hn])
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hm : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hmem]; exact hchild.modulus, by rw [hmem]; exact hchild.inverse⟩
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hm)
    (by rw [hmem]; exact hgu.hdr.hminv) (by rw [hmem]; exact hup) (by rw [hmem]; exact hul.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.2.2]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  rw [hft x hc hxout, hmem]
  apply (call_argument_frame hf (by decide) (by decide)) x
  intro r hr
  simp only [argumentRanges, List.mem_singleton] at hr
  subst r
  exact hx

end VG.Proof.Dsa.X86_64

end

end

/-! # Encoded p-minus-one and q-minus-two for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Form and encode a modulus-minus constant without changing the modulus. -/
theorem modulusMinus_ok {s : State} {B : Addr} {Z o w wx m k amount : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Checks.modulusMinus o amount output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k (m - amount) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have run := resultCall_ok hg child hZ hlo hhi ho output houtp hl hk1 hk' hkw hout hprefix
    (fun _ hc hm => minus_ok hc hm hw hw' ha ham)
  change WP isa (.seq (.block ((Core.operand result resultLen output ++ Core.enter o) ++ minusHead amount))
    (.seq (wordLoop 1 minusTail) (seqs Core.finish))) s _
  rw [WP.seq_iff, WP.block_append_iff]
  exact WP.mono (WP.seq_iff.mp run) fun u hu =>
    WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => WP.seq hv

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Equal`, which only this module used -/

section

/-! ### `Dsa.X86_64.EqualLoop`, which only this module used -/

section

/-! # Fixed-length equality scans for DSA signatures and keys -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev equalByte : List Instr := [.movzx8 .rax (at0 .rsi), .movzx8 .r9 (at0 .rdx),
  .alu .xor .rax (.reg .r9), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_eq (a b : Byte) : a.zeroExtend 64 = b.zeroExtend 64 ↔ a = b := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (a.setWidth 64).toNat = (b.setWidth 64).toNat at he
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]

theorem equalByte_ok {s : State} {p q : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block equalByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = s.mem q) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega_using [h64]), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega_using [h1]
  refine WP.mono (WP.keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| ((s.mem p).zeroExtend 64 ^^^ (s.mem q).zeroExtend 64) ∧
    t.zf = some (decide (n = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨htp, htq, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold equalByte
    xrun [State.ea, at0, hp, hq, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrp, hrq, hsub, hz]
  · refine ⟨htp, htq, htn, ?_, htz, htm, hk⟩
    rw [ht8]
    exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (BitVec.xor_eq_zero_iff.trans (byte_widen_eq _ _)))

/-- Both buffers are read completely, even after the first unequal byte. -/
theorem equalLoop_ok {s : State} {B p q : Addr} {Z : Nat} {as bs : List Byte}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 as.length)
    (ha : Src s B Z p as) (hb : Src s B Z q bs) (hlen : as.length = bs.length)
    (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64) :
    WP isa (.loop (.block equalByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ as = bs) ∧ t.mem = s.mem ∧
      Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ as = bs
  let Inv := fun n t => ∃ (pa pb : Addr) (aa bb : List Byte),
    aa.length = n ∧ bb.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧
    t.gpr .rsi = pa ∧ t.gpr .rdx = pb ∧ t.gpr .rcx = BitVec.ofNat 64 aa.length ∧
    Src t B Z pa aa ∧ Src t B Z pb bb ∧
    ((t.gpr .r8 = 0 ∧ aa = bb) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t
  refine WP.loop (M := isa) (body := .block equalByte) (c := .ne) Inv ?_ as.length s ?_
  · intro n u ⟨pa, pb, aa, bb, hla, hlb, hpos, hbnd, hup, huq, hun, hua, hub, htarget, hum, hku⟩
    cases aa with
    | nil => simp only [List.length_nil] at hla; omega
    | cons a aa =>
      cases bb with
      | nil => simp only [List.length_nil] at hlb; omega
      | cons b bb =>
        have hrp : InRegions (u.rd ++ u.wr) pa 1 := by simpa using hua.rd 0 (by simp)
        have hrq : InRegions (u.rd ++ u.wr) pb 1 := by simpa using hub.rd 0 (by simp)
        have va : u.mem pa = a := by
          have he := hua.val 0 (by simp)
          change u.mem (pa + 0) = a at he
          exact (congrArg u.mem (BitVec.add_zero pa)).symm.trans he
        have vb : u.mem pb = b := by
          have he := hub.val 0 (by simp)
          change u.mem (pb + 0) = b at he
          exact (congrArg u.mem (BitVec.add_zero pb)).symm.trans he
        refine WP.mono (equalByte_ok hup huq hun hrp hrq (by simp) (by omega_using [hbnd, hla]))
          fun t ⟨htp, htq, htn, ht8, htz, htm, hkt⟩ => ?_
        rw [va, vb] at ht8
        have htarget' : (t.gpr .r8 = 0 ∧ aa = bb) ↔ target := by
          rw [ht8, ← htarget, List.cons.injEq]
          exact and_assoc
        have hk : Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := (hku.trans hkt).mono (by decide)
        by_cases he : aa.length = 0
        · left
          refine ⟨?_, ?_, htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some false
            simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
          · have heb : bb.length = 0 := by simp only [List.length_cons] at hla hlb; omega_using [hla, hlb, he]
            simpa only [List.length_eq_zero_iff.mp he, List.length_eq_zero_iff.mp heb, and_true] using htarget'
        · right
          refine ⟨?_, aa.length, by simp only [List.length_cons] at hla; omega_using [hla],
            pa + 1, pb + 1, aa, bb, rfl, by simp only [List.length_cons] at hla hlb; omega_using [hla, hlb],
            by omega_using [he], by simp only [List.length_cons] at hla; omega_using [hbnd, hla], htp, htq, ?_,
            source_tail (hua.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
            source_tail (hub.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some true
            simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
          · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, q, as, bs, rfl, hlen.symm, h1, h64, hp, hq, hn, ha, hb, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete byte-buffer equality and inequality checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem equal_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 as.length)
    (has : Src s B Z (pointerValue s.mem B a.pointer) as)
    (hbs : Src s B Z (pointerValue s.mem B b.pointer) bs)
    (helen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.equal seqs
  refine WP.seq (WP.mono (equalHead_ok hg.scr hg.rdi hZ a b ha hb)
    fun u ⟨hup, huq, hun, hu8, hum, hku⟩ => ?_)
  rw [hlen] at hun
  have hua := has.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  have hub := hbs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  refine WP.seq (WP.mono (equalLoop_ok hup huq hun hua hub helen h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (as = bs) := by
    apply decide_eq_decide.mpr
    simpa only [hu8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 unequal) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hks := (hku.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hum)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hks.2.2, (hks.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Range`, which only this module used -/

section

/-! ### `Dsa.X86_64.LoadRange`, which only this module used -/

section

/-! # Scalar range checks on caller or scratch byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadRange_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) :
    WP isa (.seq (Arithmetic.load aX sp sl) (Checks.rangeMask aboveOne)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega_using [hw48, hfit]) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.mono (rangeMask_ok hcu.good (Nat.le_refl _) hw2 (by omega_using [hw48]) aboveOne)
    fun t ⟨ht, hmem, hkt⟩ => ?_
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hct := hcu.of_frmT hft (workRanges_ok wx) hkt.2.2 (hkt.gpr (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  rw [hv, hmu.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA range validation through the parent calling convention -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Range validation always completes the same load and scans, then combines
its result with the existing mask and returns to the parent workspace. -/
theorem range_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.range o a aboveOne) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have run := checkCall_ok hg child hZ hlo hfield hhi ho a ha hmask
    (body := .seq (Arithmetic.load aX arg argLen) (Checks.rangeMask aboveOne))
    (accepted := decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧ Spec.Dsa.decodeBE bytes < m)) ?_
  · unfold Checks.range seqs
    exact WP.seq (WP.mono (WP.seq_iff.mp run) fun u hu =>
      WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => WP.seq hv))
  intro u hc hm hp hl hf hk
  exact loadRange_ok hc hm hw2 hw48 hwx hw30 (by decide) (by decide) hp (hl.trans hlen)
    (call_source hf hk (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc) h1 hfit aboveOne

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Zero`, which only this module used -/

section

/-! ### `Dsa.X86_64.ZeroLoop`, which only this module used -/

section

/-! # Fixed-length bytewise zero tests for DSA acceptance masks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev zeroByte : List Instr := [.movzx8 .rax (at0 .rsi), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_zero (b : Byte) : b.zeroExtend 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (b.setWidth 64).toNat = 0 at he
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; subst b; rfl

theorem zeroByte_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hr : InRegions (s.rd ++ s.wr) p 1) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block zeroByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = 0) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r8, .rsi, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega_using [h64]), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega_using [h1]
  refine WP.mono (WP.keep [.rax, .r8, .rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| (s.mem p).zeroExtend 64 ∧ t.zf = some (decide (n = 1)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨htp, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold zeroByte
    xrun [State.ea, at0, hp, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr, hsub, hz]
  · exact ⟨htp, htn, by rw [ht8]; exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (byte_widen_zero _)), htz, htm, hk⟩

/-- A positive-length zero scan reads every byte, including leading zeros. -/
theorem zeroLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (h1 : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop (.block zeroByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0) ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .rsi, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ t.gpr .rsi = ptr ∧
    t.gpr .rcx = BitVec.ofNat 64 rest.length ∧ Src t B Z ptr rest ∧
    ((t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r8, .rsi, .rcx] s t
  refine WP.loop (M := isa) (body := .block zeroByte) (c := .ne) Inv ?_ bs.length s ?_
  · intro n u ⟨ptr, rest, hlen, hpos, hbnd, hup, hun, hus, htarget, hum, hku⟩
    cases rest with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b rest =>
      have hr : InRegions (u.rd ++ u.wr) ptr 1 := by simpa using hus.rd 0 (by simp)
      have hbyte : u.mem ptr = b := by
        have he := hus.val 0 (by simp)
        change u.mem (ptr + 0) = b at he
        exact (congrArg u.mem (BitVec.add_zero ptr)).symm.trans he
      refine WP.mono (zeroByte_ok hup hun hr (by simp) (by omega_using [hbnd, hlen]))
        fun t ⟨htp, htn, ht8, htz, htm, hkt⟩ => ?_
      rw [hbyte] at ht8
      have htarget' : (t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target := by
        rw [ht8, ← htarget]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_assoc
      have hk : Keep [.rax, .r8, .rsi, .rcx] s t := (hku.trans hkt).mono (by decide)
      by_cases he : rest.length = 0
      · left
        refine ⟨?_, ?_, htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
        · simpa only [List.length_eq_zero_iff.mp he, List.not_mem_nil, forall_const, false_implies, implies_true, and_true] using htarget'
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega_using [hlen],
          ptr + 1, rest, rfl, by omega_using [he], by simp only [List.length_cons] at hlen; omega_using [hbnd, hlen],
          htp, ?_, source_tail (hus.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some true
          simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
        · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, bs, rfl, h1, h64, hp, hn, hs, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete byte-buffer zero and nonzero checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Scan every byte and intersect the acceptance mask with the requested
zero/nonzero predicate. No input or temporary scalar buffer is modified. -/
theorem zero_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.zero seqs
  refine WP.seq (WP.mono (zeroHead_ok hg.scr hg.rdi hZ a ha)
    fun v ⟨hvp, hvn, hv8, hvm, hks⟩ => ?_)
  rw [hlen] at hvn
  have hvs : Src v B Z (pointerValue s.mem B a.pointer) bytes :=
    hsrc.congrK (by rw [hvm]; exact InScr.refl _ _ _) hks
  refine WP.seq (WP.mono (zeroLoop_ok hvp hvn hvs h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (∀ b ∈ bytes, b = 0) := by
    apply decide_eq_decide.mpr
    simpa only [hv8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 nonzero) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hkl' := (hks.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hvm)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hkl'.2.2, (hkl'.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hkl'.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.IsOne`, which only this module used -/

section

/-! ### `Dsa.X86_64.LoadOne`, which only this module used -/

section

/-! # Testing a byte-encoded DSA subgroup result against one -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadOne_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx) :
    WP isa (.seq (Arithmetic.load aX sp sl) (.seq (.seq (.block oneScanHead)
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]))
      (.block [.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)]))) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .rax = mask (decide (Spec.Dsa.decodeBE bytes = 1)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega_using [hw48, hfit]) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.seq (WP.mono (oneScan_ok hcu.good (Nat.le_refl _) hw2 (by omega_using [hw48]))
    fun v ⟨hv15, hvm, hkv⟩ => ?_)
  rw [hv] at hv15
  refine WP.mono (zeroMask_ok .r15 false) fun t ⟨ht, htm, hkt⟩ => ?_
  change t.gpr .rax = mask (decide (v.gpr .r15 = 0)) at ht
  rw [decide_eq_decide.mpr hv15] at ht
  have hmem : t.mem = u.mem := htm.trans hvm
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hku : Keep mmRegs u t := (hkv.trans hkt).mono (by decide)
  have hct := hcu.of_frmT hft (workRanges_ok wx) hku.2.2 (hku.gpr (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hku).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Complete checks of DSA subgroup exponentiation results -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem isOne_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.isOne o a) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide (Spec.Dsa.decodeBE bytes = 1) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have run := checkCall_ok hg child hZ hlo hfield hhi ho a ha hmask
    (body := .seq (Arithmetic.load aX arg argLen) (.seq (.seq (.block oneScanHead)
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]))
      (.block [.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)])))
    (accepted := decide (Spec.Dsa.decodeBE bytes = 1)) ?_
  · unfold Checks.isOne seqs
    refine WP.seq (WP.mono (WP.seq_iff.mp run) fun u hu => ?_)
    refine WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => ?_)
    refine WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hv)) fun z hz => ?_)
    refine WP.seq (WP.mono hz fun f hf => ?_)
    change WP isa (.block (([.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (([Crt.leave] : List Instr) ++ Checks.accumulate))) f _
    exact WP.block_append_iff.mpr hf
  intro u hc hm hp hl hf hk
  exact loadOne_ok hc hm hw2 hw48 hwx hw30 (by decide) (by decide) hp (hl.trans hlen)
    (call_source hf hk (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc) h1 hfit

end VG.Proof.Dsa.X86_64

end

end


/-! # Validation effects shared by the DSA key-check schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CheckEffect (L : ExecutionLayout) (valid : Bool) (s t : State) : Prop where
  ready : Ready L t
  mask : word t.mem L.base Field.mask.offset = VG.Proof.Bignum.mask valid
  frame : Outside L.base 128 (activeBytes - 128) s.mem t.mem
  keep : Keep coreRegs s t

theorem checkFrame_outside {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem')
    (ho : pWorkspace ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ activeBytes) :
    Outside B 128 (activeBytes - 128) mem mem' := by
  have hslot : 136 ≤ slot wx 8 + tabBytes wx := by unfold slot hdrBytes; omega_using []
  have hlo : 128 ≤ pWorkspace := by decide
  have hma : Field.mask.offset + 8 ≤ activeBytes := by decide
  have hml : 128 ≤ Field.mask.offset := by decide
  intro x hx
  apply hf x
  intro range hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only at * <;> omega_arith

theorem readyRange_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    (aboveOne : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.range side.offset a aboveOne) s
      (CheckEffect L (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < side.value L) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (range_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw aboveOne hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyIsOne_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.isOne side.offset a) s
      (CheckEffect L (decide (Spec.Dsa.decodeBE bytes = 1) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (isOne_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyZero_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes) (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s
      (CheckEffect L ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) s) := by
  refine WP.mono (zero_ok h.parent (by decide) a ha hb.length hb.source h1 h64 nonzero hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyEqual_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (has : OperandBytes s L.base activeBytes a as) (hbs : OperandBytes s L.base activeBytes b bs)
    (hlen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s
      (CheckEffect L ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) s) := by
  refine WP.mono (equal_ok h.parent (by decide) a b ha hb has.length has.source hbs.source hlen h1 h64 unequal hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyMinus_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (amount : Nat) (ha : amount < 2 ^ 31) (ham : amount ≤ side.value L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (side.value L - amount) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (modulusMinus_ok h.parent (h.child side) (by decide) hlo hhi ho hw2
    (Nat.lt_of_le_of_lt hw48 (by decide)) ha ham ⟨.local d, side.lengthField⟩ hdp
    (h.length side) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64
