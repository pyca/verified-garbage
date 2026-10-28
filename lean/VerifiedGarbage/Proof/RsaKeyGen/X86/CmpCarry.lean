module

public import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # A comparison's borrow -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86
open VG VG.X86 VG.X86.Wp

/-- `cmp d, src` and its borrow. -/
theorem wp_cmpCarry {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

end VG.Proof.RsaKeyGen.X86
