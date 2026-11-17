module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroBuffer
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScanBlocks
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.ZeroOptional`, which this module and modules that import it used -/

section

/-! Clearing an empty public prefix is a no-op; nonempty prefixes use the same
verified byte loop as full output clearing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem zeroCount_ok (s : State) :
    WP isa (.block [.cmp .lr (.imm 0)]) s fun t =>
      (t.z = (s.gpr .lr == 0) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by intro r _ i hi; simp only [instrs, List.mem_singleton] at hi; subst i; rfl) (by rfl)
  ffrun []
  change (s.gpr .lr - 0#32 == 0#32) = (s.gpr .lr == 0#32)
  rw [BitVec.sub_zero]

theorem zeroOptional_ok (advance : Bool) (s : State) {src dst : BitVec 32} {n : Nat}
    (fits : n < 2 ^ 32) (destFits : dst.toNat + n ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) n) (zero : s.gpr .r2 = 0)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block (if advance then VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
        else VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep)) .ne)) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = List.replicate n 0 ∧
      t.gpr .r0 = dst + BitVec.ofNat 32 n ∧ t.gpr .r1 = src + BitVec.ofNat 32 (if advance then n else 0) ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero, WP.seq_iff]
  refine WP.mono (zeroCount_ok s) ?_
  rintro u ⟨⟨zeroU, memU⟩, restU⟩
  have countZero : (BitVec.ofNat 32 n == (0#32)) = decide (n = 0) := by
    change decide (BitVec.ofNat 32 n = BitVec.ofNat 32 0) = decide (n = 0)
    apply decide_eq_decide.mpr
    constructor
    · intro eq
      have hn := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Nat.zero_mod] using hn
    · intro eq
      subst n
      rfl
  by_cases empty : n = 0
  · subst n
    refine WP.ite true (by change some u.z = some true; rw [zeroU, count]; rfl) ?_ (by intro hf; cases hf)
    intro _
    apply WP.block_nil
    refine ⟨by simp [Spec.Rsa.bytesAt], ?_, ?_, ?_, restU.mono (by simp)⟩
    · simpa using (restU.gpr .r0 (by simp)).trans dest
    · simpa using (restU.gpr .r1 (by simp)).trans source
    · rw [memU]; exact Frame.refl _ _
  · refine WP.ite false (by change some u.z = some false; rw [zeroU, count]; change some (BitVec.ofNat 32 n == 0#32) = some false; rw [countZero, decide_eq_false empty]) (by intro ht; cases ht) ?_
    intro _
    refine WP.mono (zeroBuffer_ok advance u (by omega_using [empty]) fits destFits (by rw [restU.wr]; exact write)
      ((restU.gpr .r2 (by simp)).trans zero) ((restU.gpr .r1 (by simp)).trans source)
      ((restU.gpr .r0 (by simp)).trans dest) ((restU.gpr .lr (by simp)).trans count)) ?_
    rintro t ⟨bytes, dstT, srcT, frame, rest⟩
    exact ⟨bytes, dstT, srcT, by rw [memU] at frame; exact frame,
      (restU.mono (by simp)).trans rest⟩

end VG.Proof.Ffdh.Arm

end

end

/-! Clear only the publicly known leading scalar bytes while advancing the
entropy and output pointers together. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem samplePrefix_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleMemory p l slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy) (dest : s.gpr .r0 = p.privateValue)
    (count : s.gpr .lr = BitVec.ofNat 32 l.lead) (zero : s.gpr .r2 = 0) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s fun t =>
      SampleMemory p l slots t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) l.lead = List.replicate l.lead 0 ∧
      t.gpr .r0 = l.start ∧ t.gpr .r1 = p.entropy + BitVec.ofNat 32 l.lead ∧
      Frame [⟨State.addr p.privateValue, l.lead⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  have bound : l.lead ≤ p.k := by have := l.lead_lt; omega_using [this]
  have buf := output.prefix bound
  refine WP.mono (zeroOptional_ok true s (by have := p.maxLength; omega_using [bound, this]) buf.fits buf.writable
    zero source dest count) ?_
  rintro t ⟨bytes, ptr, src, frame, rest⟩
  have sub : (⟨State.addr p.privateValue, l.lead⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Region.sub_prefix bound
  have context := h.after_output frame rest (domainSep.sub_right sub) (stackSep.sub_right sub) saved
  exact ⟨context, bytes, ptr, src, frame, rest⟩

end VG.Proof.Ffdh.Arm
