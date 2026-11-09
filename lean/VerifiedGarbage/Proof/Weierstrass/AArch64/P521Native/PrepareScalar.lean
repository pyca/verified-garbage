module

-- separate module: scalar bounds reuse radix mathematics independently of peer validation and field representation conversions

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Window.Mask
public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.RecodeMath
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Mask the working scalar, add the105-window offset, and initialize recoding. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
attribute [local instance high] instPowNat
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock005 config)

/-- Signed radix32 offset for105digits. -/
def recodeOffset : Nat := 16*Window5.geom 105

theorem recode_offset_bound : recodeOffset<32^105 := Window5.half_geom_lt 105

theorem recode_sum_bound (k : Nat) : k%2^521+recodeOffset<32^105 := by
  exact p521_recode_bound (Nat.mod_lt k (Nat.pow_pos (a:=2) (n:=521) (by decide)))

theorem window_radix_lt (J W : Nat) (h : 5*J<W) : (32 : Nat)^J<2^W := by
  rw [show (32 : Nat)=2^5 from rfl,←Nat.pow_mul]
  exact Nat.pow_lt_pow_right (by decide) h

theorem prepare_scalar_source : outerBlock005=
    VG.Impl.Ecdh.AArch64.P521Window.maskK++
      (VG.Impl.Weierstrass.AArch64.WinCfg.addConst 9 2296 3944 recodeOffset++([.movz .x .x19 80 0,.movz .x .x5 1 0] : List Instr)) := by lit_decide

theorem prepare_scalar_counters (s : State) :
    WP isa (.block [.movz .x .x19 80 0,.movz .x .x5 1 0]) s fun t =>
      t.gpr .x19=80 ∧ t.gpr .x5=1 ∧ Keeps [.x19,.x5] s t := by
  rw [←List.singleton_append,WP.block_append_iff]
  refine WP.mono (setCounter_ok s (j:=80) (by decide)) fun u ⟨count,k⟩ => ?_
  refine WP.mono (movz1_ok u .x5) fun t ⟨one,kt⟩ => ?_
  exact ⟨(kt.gpr .x19 (by decide)).trans count,one,(k.mono (by decide)).trans (kt.mono (by decide))⟩

/-- The actual machine phase retains the original range-check scalar, bounds
its working copy, and leaves the ten-word recoding input ready for loop21. -/
theorem prepare_scalar_ok {s : State} {base : Addr} (hs : Scr s base 8192) :
    WP isa (.block outerBlock005) s fun t =>
      Scr t base 8192 ∧
      wordsVal t.mem base 3944 10=wordsVal s.mem base 2296 9%2^521+recodeOffset ∧
      wordsVal t.mem base 3944 10<32^105 ∧ t.gpr .x19=80 ∧ t.gpr .x5=1 ∧
      KeepRegs (.x19::clob 9) s t ∧
      Unch base [(2296,72),(3944,80)] s.mem t.mem := by
  rw [prepare_scalar_source,WP.block_append_iff]
  refine WP.mono (VG.Proof.Ecdh.AArch64.P521.Window.mask_ok hs) fun u ⟨hu,ku,masked,unch⟩ => ?_
  change wordsVal u.mem base 2296 9=wordsVal s.mem base 2296 9%2^521 at masked
  have cb := Nat.lt_trans recode_offset_bound (window_radix_lt 105 (64*(9+1)) (by decide))
  have sum0 := recode_sum_bound (wordsVal s.mem base 2296 9)
  rw [←masked] at sum0
  have sum := Nat.lt_trans sum0 (window_radix_lt 105 (64*(9+1)) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (addConst_ok hu (n:=9) (src:=2296) (dst:=3944) (c:=recodeOffset)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cb sum)
    fun v ⟨value,kv,outside⟩ => ?_
  refine WP.mono (prepare_scalar_counters v) fun t ⟨count,one,kt⟩ => ?_
  have k : KeepRegs (.x19::clob 9) s t :=
    ((ku.mono (by decide)).trans (kv.mono (by decide))).trans ((Keeps.regs kt).mono (by decide))
  refine ⟨hs.of_keepRegs k (by decide),?_,?_,count,one,k,?_⟩
  · rw [kt.mem,value,masked]
  · rw [kt.mem,value,masked]
    exact recode_sum_bound _
  · have first : Unch base [(2296,72),(3944,80)] s.mem u.mem := unch.mono (by decide)
    have second : Unch base [(2296,72),(3944,80)] u.mem v.mem := outside.unch.mono (by decide)
    rw [kt.mem]
    exact (first.trans second).mono (by intro w hw; simpa only [List.mem_append,or_self] using hw)

end VG.Proof.Weierstrass.AArch64.P521Native
