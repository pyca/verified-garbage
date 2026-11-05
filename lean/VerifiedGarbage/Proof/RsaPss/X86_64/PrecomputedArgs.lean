module
public import VerifiedGarbage.Impl.RsaPss.X86_64
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCall

import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.X86_64.Safe

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

variable {tsH tsG : List FnTable}

theorem arg_read {s u : State} (hp : Pre tsH tsG s) (hrd : u.rd = s.rd) {j : Nat} (hj : j < 10) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) 8 := by
  rw [hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem arg_keep {s : State} {m : Mem} (hp : Pre tsH tsG s) (hf : Frame (vwrR s) s.mem m) {j : Nat} (hj : j < 10) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.argsStack
    · exact hp.argsScr

theorem load_pre {s t : State} (hp : Pre tsH tsG s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd)
    (hf : Frame (vwrR s) s.mem t.mem) :
    WP isa (.block [.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧
        u.gpr .rdx = stackArg s 6 ∧ u.gpr .rcx = stackArg s 7 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [arg, ea_sp, hsp, arg_read hp hrd (show 6 < 10 by decide), arg_read hp hrd (show 7 < 10 by decide),
    arg_keep hp hf (show 6 < 10 by decide), arg_keep hp hf (show 7 < 10 by decide)]

end VG.Proof.RsaPss.X86_64.Pc
