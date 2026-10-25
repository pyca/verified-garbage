module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.EcKey.AArch64.Main
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Code

/-! # Encode the compressed point's parity tag -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)

 theorem tag_ok {c : Cfg} {s : State} {base out : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.AArch64.QY + 8 ≤ size)
    (hout : s.gpr .x20 = out) (hw : InRegions s.wr out 1) (b : Bool)
    (hf : s.gpr .x3 = if b then BitVec.allOnes 64 else 0) (hn : 0 < c.n) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.compressTag c)) s fun s' =>
      s'.mem out = (if b then BitVec.ofNat 8 (2 + sv c base s Impl.Ecdh.AArch64.QY % 2) else 0) ∧
      Outside out 0 1 s.mem s'.mem ∧ KeepRegs [.x1, .x2] s s' := by
  change WP isa (.block ([ld .x1 (c.sl Impl.Ecdh.AArch64.QY)] ++ _)) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs hy (sl_mod8 c _) .x1) fun t ⟨ht, kt, _⟩ => ?_
  have ha : t.gpr .x20 + BitVec.ofNat 64 0 = out := by
    rw [kt.gpr _ (by decide), hout, BitVec.add_zero]
  have hw' : InRegions t.wr out 1 := by rw [kt.wr]; exact hw
  have hf' : t.gpr .x3 = if b then BitVec.allOnes 64 else 0 := by rw [kt.gpr _ (by decide), hf]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide,
    show (2 : Nat) < 4096 by decide, and_self, ite_true, RegUpd.gpr_write,
    RegUpd.wr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, ha, hw',
    hf', ht, Option.bind_some, State.store, State.read, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_⟩
  · rw [VG.Proof.EcKey.AArch64.byte_self]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact tag_byte _ _ _ _ hn b
  · simp only [RegUpd.mem_write, kt.mem]
    exact VG.Proof.EcKey.AArch64.byte_outside _ _ _
  · refine ⟨fun r hr => ?_, kt.rd, kt.wr, kt.sp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.1,
      RegUpd.gpr_write_of_ne _ _ _ hr.1,
      RegUpd.gpr_write_of_ne _ _ _ hr.1,
      RegUpd.gpr_write_of_ne _ _ _ hr.2,
      kt.gpr _ (by simpa using hr.1)]

end VG.Proof.EcKey.Compressed.AArch64
