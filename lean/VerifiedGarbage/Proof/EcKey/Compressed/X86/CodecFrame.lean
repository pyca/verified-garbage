module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

 theorem codec_args_frame {il ol : Nat} {s t : State} (hp : codecPre il ol false s)
    (he : t.gpr .esp = s.gpr .esp) (W : Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) :
    ∀ i, i < 3 → arg t i = arg s i := by
  obtain ⟨_, hwr, _, _, _, hao, haw, _, _, _, _, _, hsf, hlo, _, _⟩ := hp
  intro i hi
  have hd : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 28], Region.Disjoint ⟨argAddr s i, 4⟩ r := by
    intro r hr
    rw [hwr] at hr
    simp only [Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hao.sub_left (arg_subN (k := 3) (by omega) hi)
    · exact haw.sub_left (arg_subN (k := 3) (by omega) hi)
    · exact ((below_disjoint_args (k := 12) hlo (by omega) (by decide)).sub_right
        (arg_subN (k := 3) (by omega) hi)).symm
  change t.mem.readW (argAddr t i) 32 = _
  rw [show argAddr t i = argAddr s i by simp only [argAddr, he]]
  exact W.readW (Region.contains_self _ _) hd (by decide)

 theorem codec_pre_frame {il ol : Nat} {s t : State} (hp : codecPre il ol false s)
    (he : t.gpr .esp = s.gpr .esp) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (W : Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) : codecPre il ol false t := by
  have ha := codec_args_frame hp he W
  simpa only [codecPre, ptr, argAddr, he, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), hr, hw]
    using hp

end VG.Proof.EcKey.Compressed.X86
