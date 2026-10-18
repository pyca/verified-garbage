module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentAccumulate
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Public exponent bytes determine the scanner's saturation branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem exponentAccumulate_trace :
    RelCT isa (VG.X86.Taint.Agree (τr [.esi])) (.block exponentAccumulate) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (τr [.esi]) (fun _ _ h => h) (hc := .block [])
  rfl

theorem exponentSaturate_trace :
    RelCT isa (fun s t => s.zf = t.zf)
      (.ite .e (.block []) (.block [.mov .edx (.imm 2)])) (fun _ _ => True) := by
  apply VG.RelCT.ite (M := isa) (c := .e) (P := fun s t => s.zf = t.zf) (fun _ _ h => h)
  · exact VG.RelCT.block_nil (fun _ _ _ => trivial)
  · apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl

theorem exponentConsume_trace {s t : State}
    (ptr : s.gpr .esi = t.gpr .esi) (low : s.gpr .ebx = t.gpr .ebx)
    (high : s.gpr .edx = t.gpr .edx)
    (readS : InRegions (s.rd ++ s.wr) (s.ea ⟨.esi, 0⟩) 1)
    (readT : InRegions (t.rd ++ t.wr) (t.ea ⟨.esi, 0⟩) 1)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa exponentConsume s tr sf) (F : Exec isa exponentConsume t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      obtain ⟨_, _, Zs, _, _⟩ := wp_result (exponentAccumulate_ok s rfl readS) E1
      obtain ⟨_, _, Zt, _, _⟩ := wp_result (exponentAccumulate_ok t rfl readT) F1
      have T1 := (exponentAccumulate_trace _ _ _ _ _ _
        (agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ptr)) E1 F1).1
      have T2 := (exponentSaturate_trace _ _ _ _ _ _
        (by dsimp only; rw [Zs, Zt, low, high]) E2 F2).1
      rw [T1, T2]

end VG.Proof.Bignum.X86
