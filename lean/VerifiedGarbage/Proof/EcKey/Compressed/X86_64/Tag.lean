module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Code

/-! # The compressed tag store -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem eaRsi (s : State) : s.ea { base := .rsi } = s.gpr .rsi := by
  simp [State.ea]

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size)
    (hw : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressTag c)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi)
        ((((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) &&& 1) + 2) &&& s.gpr .rcx).setWidth 8) ∧
      KeepRegs [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.compressTag, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, Option.map_some, Option.bind_some, State.load64, State.store8,
    ea_sc, eaRsi, hs.rdi, ld_sc hs hy, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
