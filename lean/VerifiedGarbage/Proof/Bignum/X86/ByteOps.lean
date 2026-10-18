module

public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Byte-load and byte-store rules for the RSA conversion loops -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadByte {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  cons (s' := s.setReg d ((s.mem a).setWidth 32))
    (by simp only [exec, ha, State.load8, hr, ite_true, Option.map_some])
    (k _ (Upd.setReg _ _ _))

theorem wp_storeByte {r : Reg8} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end
end VG.Proof.Bignum.X86
