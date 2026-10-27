module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Set
import Mathlib.Data.Int.GCD
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSASSA-PSS verification on x86-64: the call of `vg_rsa_public_checked`

With its stack arguments in the frame's first 4 words (the signature, `k`,
the rest of `scratch`), `vg_rsa_public_checked` runs under its contract
(`pub_pre`) and returns with `EM`'s place (`scratch + oEm`) written as it
says, the frame and the rest of our working space kept (`pub_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {G : Spec.Mgf1.Hash}

/-- Its stack arguments. -/
def vArg (s : State) (i : Nat) : BitVec 64 :=
  match i with
  | 0 => s.gpr .r9
  | 1 => s.gpr .rsi
  | 2 => off (stackArg s 3) oRsa
  | _ => stackArg s 4 - BitVec.ofNat 64 1024

theorem vfb_sub8 {s : State} (hp : VPre G s) : (fb s - 8).toNat = (fb s).toNat - 8 := by
  have hF := vfb_toNat hp; have := hp.sp1
  rw [BitVec.toNat_sub]; unfold verifyStack frameBytes at *
  rw [show (8 : BitVec 64).toNat = 8 from rfl]; omega_arith

theorem vstackArg_call {s t : State} (hp : VPre G s) (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat}
    (hi : i < 4) : stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hF := vfb_toNat hp
  have := hp.sp1; have := hp.sp2
  have hsep := Offset.sep (fb s - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith)
    (by unfold verifyStack frameBytes at *; omega_arith)
  rw [show fb s - 8 + BitVec.ofNat 64 0 = fb s - 8 from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  have ea : fb s - 8 + BitVec.ofNat 64 (8 * (i + 1)) = off (fb s) (8 * i) := by
    simp only [off]
    rw [show 8 * (i + 1) = 8 + 8 * i by omega_arith, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      show BitVec.ofNat 64 8 = 8 from rfl, BitVec.sub_add_cancel]
  rw [ea]

theorem vsc_sub {s : State} (hp : VPre G s) :
    (stackArg s 4 - 1024#64).toNat = (stackArg s 4).toNat - 1024 := by
  have := hp.hsl; have := hp.k1
  rw [BitVec.toNat_sub, show (1024#64).toNat = 1024 from rfl]; omega_arith

end VG.Proof.RsaPss.X86_64
