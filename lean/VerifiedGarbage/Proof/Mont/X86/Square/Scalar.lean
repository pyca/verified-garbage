module

public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.TCB.X86.Isa

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86

theorem wp_cmpCF {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, VG.X86.Wp.Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  VG.X86.Wp.cons (s' := arithFlags s (s.gpr d-v) (decide ((s.gpr d).toNat<v.toNat)) (subOverflow (s.gpr d) v (s.gpr d-v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end VG.Proof.Mont.X86.Square
