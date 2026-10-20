module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Semantics
import Mathlib.Tactic.SplitIfs

/-! ## Buffer -/

@[expose] public section

section

/-!
# Integer preparation of the counter buffer

The integer pipeline writes counter words while leaving every vector
register available to the interleaved AES/GHASH work.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (prepCounter)

private theorem ea_at (s : State) (r : Reg) (n : Nat) :
    s.ea (at_ r n) = s.gpr r + BitVec.ofNat 64 n := by
  simp [at_, State.ea, BitVec.ofInt_natCast]

private theorem store32_eq (s : State) (a : Addr) (v : BitVec 32) :
    s.store32 a v = if InRegions s.wr a 4 then some (s.setMem (s.mem.writeW a v)) else none := rfl

/-- Integer preparation only changes `rax`, flags, and memory. -/
structure BufferFrame (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  xmm : t.xmm = s.xmm
  ymmHi : t.ymmHi = s.ymmHi
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem BufferFrame.refl (s : State) : BufferFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem BufferFrame.trans {s t u : State} (h : BufferFrame s t) (h' : BufferFrame t u) :
    BufferFrame s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.xmm.trans h.xmm,
    h'.ymmHi.trans h.ymmHi, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem BufferFrame.lane {s t : State} (h : BufferFrame s t) (r : XReg) (l : Nat) :
    t.lane r l = s.lane r l := by
  simp only [State.lane, h.xmm, h.ymmHi]

theorem prepCounter_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i)) 4) :
    WP isa (.block (prepCounter i)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i))
        (bswap32 ((s.gpr .r8).setWidth 32 + BitVec.ofNat 32 i)) ∧ BufferFrame s t := by
  apply WP.of_runBlock
  simp only [prepCounter, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    readSrc32, execAlu32, State.setReg32, gpr_setReg, gpr_arithFlags,
    reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some,
    setWidth_setWidth_32, store32_eq, ea_at, wr_setReg, wr_arithFlags,
    mem_setReg, mem_arithFlags, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [State.setMem_gpr, gpr_setReg, gpr_arithFlags, hr, ite_false]
  · simp only [State.setMem_xmm, xmm_setReg, xmm_arithFlags]
  · simp only [State.setMem_ymmHi, ymmHi_setReg, ymmHi_arithFlags]
  · simp only [State.setMem_rd, rd_setReg, rd_arithFlags]
  · simp only [State.setMem_wr, wr_setReg, wr_arithFlags]

/-- The memory effect of preparing any collection of next-counter slots. -/
def prepCountersMem (m : Mem) (p : Addr) (v : BitVec 32) (is : List Nat) : Mem :=
  is.foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (652 + 16 * i))
    (bswap32 (v + BitVec.ofNat 32 i))) m

theorem prepCounters_ok (is : List Nat) (s : State)
    (hw : ∀ i ∈ is, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (652 + 16 * i)) 4) :
    WP isa (.block (is.flatMap prepCounter)) s fun t =>
      t.mem = prepCountersMem s.mem (s.gpr .r11) ((s.gpr .r8).setWidth 32) is ∧ BufferFrame s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, BufferFrame.refl _⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (prepCounter_ok s i (hw i List.mem_cons_self)) fun t ⟨hm, hf⟩ => ?_
    refine WP.mono (ih t (fun j hj => by
      rw [hf.wr, hf.gpr .r11 (by decide)]
      exact hw j (List.mem_cons_of_mem _ hj))) fun u ⟨hm', hf'⟩ => ⟨?_, hf.trans hf'⟩
    rw [hm', hf.gpr .r11 (by decide), hf.gpr .r8 (by decide), hm]
    rfl

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Flow -/
section

/-! # Register frames for the integer and vector work between AES rounds -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64

structure FlowFrame (rs : List XReg) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  lane : ∀ r, r ∉ rs → ∀ l < 2, t.lane r l = s.lane r l
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem FlowFrame.refl (rs : List XReg) (s : State) : FlowFrame rs s s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem FlowFrame.trans {rs : List XReg} {s t u : State}
    (h : FlowFrame rs s t) (h' : FlowFrame rs t u) : FlowFrame rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr),
    fun r hr l hl => (h'.lane r hr l hl).trans (h.lane r hr l hl),
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem FlowFrame.of_yframe {rs : List XReg} {s t : State} (h : YFrame rs s t) :
    FlowFrame rs s t := ⟨fun r _ => congrFun h.gpr r, h.lane, h.rd, h.wr⟩

theorem FlowFrame.of_buffer (rs : List XReg) {s t : State} (h : BufferFrame s t) :
    FlowFrame rs s t := ⟨h.gpr, fun r _ l _ => h.lane r l, h.rd, h.wr⟩

theorem FlowFrame.mono {rs rs' : List XReg} {s t : State} (h : FlowFrame rs s t)
    (hs : ∀ r ∈ rs, r ∈ rs') : FlowFrame rs' s t :=
  ⟨h.gpr, fun r hr => h.lane r (fun he => hr (hs r he)), h.rd, h.wr⟩

end VG.Proof.Gcm.X86_64.StitchAvx8

end

/-! ## Bump -/
section

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64 VG.X86_64.RegUpd

theorem bump_ok (s : State) :
    WP isa (.block [.alu32 .add .r8 (.imm 8)]) s fun t =>
      (t.gpr .r8).setWidth 32 = (s.gpr .r8).setWidth 32 + 8 ∧
      (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      (∀ r l, t.lane r l = s.lane r l) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    execAlu32, readSrc32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setReg32, gpr_setReg, ite_true, setWidth_setWidth_32]
  · intro r hr; simp only [State.setReg32, gpr_setReg, gpr_arithFlags, hr, ite_false]
  · simp only [State.setReg32, mem_setReg, mem_arithFlags]
  · intro r l
    simp only [State.lane, State.setReg32, xmm_setReg, xmm_arithFlags,
      ymmHi_setReg, ymmHi_arithFlags]
  · simp only [State.setReg32, rd_setReg, rd_arithFlags]
  · simp only [State.setReg32, wr_setReg, wr_arithFlags]

end VG.Proof.Gcm.X86_64.StitchAvx8

end
