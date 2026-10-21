module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvanceMath

/-! # A masked public countdown stops the sieve on its first divisor -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem advanceCount_ok {p : BitVec 32} {s : State} (C : StackContext p s)
    {q : Nat} (positive : 0 < q) (bound : q < 2 ^ 32) (hit : Bool)
    (count : s.mem.readW (off (p.setWidth 64) 12) 32 = BitVec.ofNat 32 q)
    (mask : s.gpr .ecx = BitVec.ofNat 32 hit.toNat - 1) :
    WP isa (.block (advanceCount stackSlots)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextCount q hit) ∧
      t.mem = s.mem.writeW (off (p.setWidth 64) 12) (BitVec.ofNat 32 (nextCount q hit)) ∧
      Outside (p.setWidth 64) 12 4 s.mem t.mem ∧ Keeps [.eax] s t ∧ StackContext p t ∧
      t.zf = some (BitVec.ofNat 32 (nextCount q hit) == 0#32) := by
  change WP isa (.block [.mov .eax (.mem (slot 12)), .alu .sub .eax (.imm 1),
    .alu .and .eax (.reg .ecx), .store (slot 12) .eax, .alu .cmp .eax (.imm 0)]) s _
  refine wp_movS (C.read 12 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  refine wp_logicS (.inl rfl) rfl fun c D => ?_
  have K : Keeps [.eax] s c := (A.keeps.trans B.keeps).trans D.keeps
  have M : c.mem = s.mem := D.mem.trans (B.mem.trans A.mem)
  have value : c.gpr .eax = BitVec.ofNat 32 (nextCount q hit) := by
    rw [D.gpr, B.gpr, A.gpr, count, B.other .ecx (by decide), A.other .ecx (by decide), mask]
    exact nextCount_word positive bound hit
  change WP isa (.block ([.store (slot 12) .eax] ++ [.alu .cmp .eax (.imm 0)])) c _
  refine WP.block_append (WP.mono ((C.keep K (by decide)).store 12 (by decide) .eax)
    fun d ⟨Md, O, Kd, Cd⟩ => ?_)
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  have keep : Keeps [.eax] s t := (K.widen Kd).widen (T.keeps [])
  refine ⟨?_, ?_, ?_, keep, C.keep keep (by decide), ?_⟩
  · rw [T.gpr, Kd.1 .eax (by decide)]
    exact value
  · rw [T.mem, Md, M, value]
  · rw [M] at O
    rw [T.mem]
    exact O
  · rw [Z, Kd.1 .eax (by decide), value]
    change some (BitVec.ofNat 32 (nextCount q hit) - 0#32 == 0#32) = _
    rw [BitVec.sub_zero]

end VG.Proof.RsaKeyGen.X86.Sieve
