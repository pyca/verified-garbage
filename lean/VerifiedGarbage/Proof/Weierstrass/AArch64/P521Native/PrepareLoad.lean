module

-- separate module: the existing stage-one proof is adapted to the native block/loop shape without duplicating its arithmetic proof

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareEquiv
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Framework.Lit

/-! The native preparation prefix reuses verified key/peer loading and bit extraction. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock001 outerBlock002 loop20 sequence)

/-- The frame-relative pointer setup and original ECDH argument shuffle. -/
theorem prepare_args_source : outerBlock001.take 5=
    [.addSp .x26 0]++VG.Impl.Ecdh.AArch64.Cfg.args := by lit_decide

theorem prepare_load_source : outerBlock001.drop 5=config.setupWith none++
    [.movz .x .x19 72 0,.movz .x .x5 1 0] := by lit_decide

theorem prepare_bits_source : outerBlock002=bitsBody 2296 3304 := by lit_decide

def prepareLoadBits : Prog isa := .seq (.block (outerBlock001.drop 5)) loop20

/-- The full load-and-original-bit-table machine phase establishes the same
signature-layout invariant used by the existing ECDH proof. -/
theorem prepare_load_bits_ok (hc : BaseCfgOk config) {s : State} (hp : SetupPre config s) :
    WP isa prepareLoadBits s (St₁ config none s (s.gpr .x4)) := by
  have h := stage₁ hc (.inl rfl) hp (rest:=.block []) (Q:=St₁ config none s (s.gpr .x4))
    (fun _ stage => WP.block_nil stage)
  have shaped : WP isa (.block (config.setupWith none)) s fun u =>
      WP isa (.block [.movz .x .x19 72 0,.movz .x .x5 1 0]) u fun v =>
      WP isa (.loop (.block (bitsBody 2296 3304)) (.nonzero .x .x19)) v (St₁ config none s (s.gpr .x4)) := by
    rw [VG.WP.seq_iff] at h
    refine VG.WP.mono h fun u hu => ?_
    rw [VG.WP.seq_iff] at hu
    have hb := VG.WP.mono hu (fun _ hv => VG.WP.block_nil_iff.mp hv)
    rw [bits_eq,VG.WP.seq_iff] at hb
    exact hb
  rw [prepareLoadBits,prepare_load_source,WP.seq_iff,WP.block_append_iff]
  refine WP.mono shaped fun u hu => WP.mono hu fun v hv => ?_
  rw [loop20,sequence,List.foldr_cons,List.foldr_nil,prepare_bits_source]
  exact wp_loop_append_nil hv

end VG.Proof.Weierstrass.AArch64.P521Native
