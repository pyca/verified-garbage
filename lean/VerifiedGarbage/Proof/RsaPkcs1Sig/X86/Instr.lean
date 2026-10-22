module

public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# The x86 RSA padding functions: instruction rules

Continuation-passing rules (as `Proof/Framework/X86/Wp.lean`) for the byte
loads and stores of the padding functions (`movzx8`, `store8`), and the
operands they read (`readSrc`): a register, an immediate, or a word of
memory; with the rules of `Proof/Mont/X86/Instr.lean` for any operand.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86 VG.X86.Wp

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ha, hout]

/-- `xor d, v` of an immediate. -/
theorem wp_xorI {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `and d, src` of any operand. -/
theorem wp_andS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

end

theorem readSrc_reg (s : State) (r : Reg) : readSrc s (.reg r) = some (s.gpr r) := rfl

theorem readSrc_imm (s : State) (v : BitVec 32) : readSrc s (.imm v) = some v := rfl

theorem readSrc_memOp {s : State} {b : Reg} {d : Nat} {a : Addr} (ha : addr (s.gpr b) d = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) : readSrc s (.mem ⟨b, d⟩) = some (s.mem.readW a 32) := by
  rw [← ha]; exact readSrc_mem rfl (by rw [ha]; exact hin)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea ⟨b, d⟩ = addr (s.gpr b) d := rfl

end VG.Proof.RsaPkcs1Sig.X86
