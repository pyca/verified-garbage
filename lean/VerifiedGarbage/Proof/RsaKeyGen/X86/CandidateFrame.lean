module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # A single private frame supplies the prepared-call ABI for all witnesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFrame
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem code_full_ok {body : Prog isa} (noSp : NoSp body)
    {g : Geometry} {s : State} {capacity : Nat} {Q : State → Prop} (S : Scr s g.W g.L)
    (header : 256 ≤ g.L) (length : w32 s.mem g.W 40 = capacity)
    (fit : 96 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ g.W.toNat ∨ g.W.toNat + g.L + 96 ≤ (s.gpr .esp).toNat)
    (runBody : ∀ a, Scr a g.W g.L → Caller g capacity (privateSp s) a →
      (lengthRegion (privateSp s)).Disjoint (below (privateSp s) 68) →
      Frame [below (s.gpr .esp) 28] s.mem a.mem →
      Keeps [.edx] (allocFrame 28 s) a → WP isa body a fun t => Q (freed 28 t)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code body) s Q := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFrame.code VG.Impl.RsaKeyGen.X86.CandidateFrame.bytes
  refine WP.seq (wp_movS (readSrc_sc S (d := 40) (by omega)) fun a A _ => WP.block_nil ?_)
  have Sa := S.of_keeps A.keeps (by decide)
  have spA := A.other .esp (by decide)
  have privateA : privateSp a = privateSp s := by unfold privateSp; rw [spA]
  have capA : a.gpr .edx = BitVec.ofNat 32 capacity := by
    rw [A.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← length, Nat.mod_eq_of_lt (by change w32 s.mem g.W 40 < 2 ^ 32; exact (s.mem.readW _ 32).isLt)]
  have innerNoSp : NoSp (.seq (.block [.store (at_ .esp 24) .edx]) body) := by
    intro i hi
    simp only [instrs, List.mem_append, List.mem_singleton] at hi
    rcases hi with rfl | hi
    · rfl
    · exact noSp i hi
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [spA]; omega) innerNoSp ?_
  refine WP.seq (WP.mono (slot_ok Sa (by rw [spA]; exact fit)
    (by rw [spA]; exact separate) capA) fun b ⟨Sb, Cb, lenFar, Fb, Kb⟩ => ?_)
  rw [privateA] at Cb lenFar
  rw [spA, A.mem] at Fb
  have Kalloc : Keeps [.edx] (allocFrame 28 s) (allocFrame 28 a) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r mem
      by_cases same : r = .esp
      · subst r; rw [allocFrame_esp, allocFrame_esp, spA]
      · rw [allocFrame_gpr _ _ same, allocFrame_gpr _ _ same]
        exact A.keeps.1 r mem
    · rw [allocFrame_rd, allocFrame_rd]; exact A.keeps.2.1
    · rw [allocFrame_wr, allocFrame_wr, spA, A.keeps.2.2]
  exact runBody b Sb Cb lenFar Fb (Kalloc.widen Kb)

theorem code_ok {body : Prog isa} (noSp : NoSp body)
    {g : Geometry} {s : State} {capacity : Nat} {Q : State → Prop} (S : Scr s g.W g.L)
    (header : 256 ≤ g.L) (length : w32 s.mem g.W 40 = capacity)
    (fit : 96 ≤ (s.gpr .esp).toNat)
    (separate : (s.gpr .esp).toNat ≤ g.W.toNat ∨ g.W.toNat + g.L + 96 ≤ (s.gpr .esp).toNat)
    (runBody : ∀ a, Scr a g.W g.L → Caller g capacity (privateSp s) a →
      (lengthRegion (privateSp s)).Disjoint (below (privateSp s) 68) →
      Frame [below (s.gpr .esp) 28] s.mem a.mem → WP isa body a fun t => Q (freed 28 t)) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateFrame.code body) s Q :=
  code_full_ok noSp S header length fit separate fun a Sa Ca far F _ => runBody a Sa Ca far F

end VG.Proof.RsaKeyGen.X86.CandidateFrame
