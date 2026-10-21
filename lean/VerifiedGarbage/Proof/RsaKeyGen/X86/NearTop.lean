module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Read the four highest native words for the separation comparison -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Near

def word (m : Mem) (base : Addr) (offset : Nat) : BitVec 32 := m.readW (off base offset) 32

theorem top_ok {s : State} {base : Addr} {size n src : Nat}
    (scratch : Scr s base size) (positive : 4 ≤ n) (fit : src + 4 * n ≤ size) :
    WP isa (.block (top n src)) s fun t =>
      t.gpr .ecx = word s.mem base (src + 4 * (n - 4)) >>> 28 ∧
      t.gpr .ebx = s.gpr .ebx ||| (word s.mem base (src + 4 * (n - 4)) &&& 0x0fffffff) ∧
      t.gpr .edx = (word s.mem base (src + 4 * (n - 4) + 4) |||
        word s.mem base (src + 4 * (n - 4) + 8)) ||| word s.mem base (src + 4 * (n - 4) + 12) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold top
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => wp_movS rfl fun b B _ =>
    wp_shr (by decide) fun c C _ => wp_andi fun d D => wp_orS rfl fun e E => ?_
  have Ke : Keeps [.eax, .ebx, .ecx] s e :=
    ((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps
  have Me : e.mem = s.mem := E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))
  have Se := scratch.of_keeps Ke (by decide)
  refine wp_movS (readSrc_sc Se (by omega)) fun f F _ => ?_
  have Sf := Se.of_keeps F.keeps (by decide)
  refine wp_orS (readSrc_sc Sf (by omega)) fun h H => ?_
  have Sh := Sf.of_keeps H.keeps (by decide)
  refine wp_orS (readSrc_sc Sh (by omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, T.mem.trans (H.mem.trans (F.mem.trans Me)),
    (((Ke.mono (by decide)).widen F.keeps).widen H.keeps).widen T.keeps⟩
  · rw [T.other .ecx (by decide), H.other .ecx (by decide), F.other .ecx (by decide),
      E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, B.gpr, A.gpr]
    rfl
  · rw [T.other .ebx (by decide), H.other .ebx (by decide), F.other .ebx (by decide), E.gpr,
      D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.other .ebx (by decide),
      D.gpr, C.other .eax (by decide), B.other .eax (by decide), A.gpr]
    rfl
  · rw [T.gpr, H.gpr, F.gpr, H.mem, F.mem, Me]
    rfl

end VG.Proof.RsaKeyGen.X86.Near
