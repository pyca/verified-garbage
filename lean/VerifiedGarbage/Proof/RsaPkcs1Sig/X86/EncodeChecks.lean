module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeDispatch
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Status and public-length branches of the encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86

theorem SameF.keeps {s t : State} (h : SameF s t) (regs : List Reg) : Keeps regs s t :=
  ⟨fun r _ => congrFun h.1 r, h.2.2.1, h.2.2.2⟩

theorem fail_ok (s : State) : WP isa fail s fun t =>
    Keeps [.eax] s t ∧ t.mem = s.mem ∧ t.gpr .eax = 0 := by
  unfold fail
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨T.keeps, T.mem, T.gpr⟩

theorem cmpLen_ok (s : State) :
    WP isa (.block [.alu .cmp .ebp (.reg .eax)]) s fun t => SameF s t ∧
      t.zf = some (s.gpr .ebp == s.gpr .eax) := by
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  exact ⟨⟨F.gpr, F.mem, F.rd, F.wr⟩, Z.trans (congrArg some (sub_beq32 _ _))⟩

theorem cmpK_ok (s : State) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 11), .alu .cmp .ecx (.reg .eax)]) s
      fun t => Keeps [.eax] s t ∧ t.mem = s.mem ∧
        t.cf = some (decide ((s.gpr .ecx).toNat < (s.gpr .ebx + 11).toNat)) := by
  refine wp_movS rfl fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  refine wp_cmp fun t F C _ => WP.block_nil ?_
  refine ⟨(U.keeps.trans V.keeps).trans (F.keeps _), F.mem.trans (V.mem.trans U.mem), ?_⟩
  rw [C, V.other .ecx (by decide), U.other .ecx (by decide), V.gpr, U.gpr]

end VG.Proof.RsaPkcs1Sig.X86
