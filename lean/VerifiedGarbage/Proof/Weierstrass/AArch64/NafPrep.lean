module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSubtract
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Registers written by the public scalar recoder. -/
def nafPrepClob : List Reg := [.x1,.x2,.x3,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x19,.x20]

theorem nafByte_word (k j : Nat) :
    BitVec.ofNat 8 (BitVec.ofInt 64 (Naf5.digit k j)).toNat=Naf5.byte k j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,nafWord_toNat,Naf5.byte_toNat]
  have hb := Naf5.magnitude_le k j
  cases hn : Naf5.negative k j
  · simp only [Bool.false_eq_true,ite_false]; omega_using [hb]
  · have hp := Naf5.negative_magnitude_pos k j hn
    simp only [ite_true]; omega_using [hb, hp]

theorem nafLoads_ok {s : State} {base : Addr} {size src : Nat}
    (hs : Scr s base size) (hsrc : src+32≤size) (hsrc8 : src%8=0) :
    WP isa (.block (VG.Impl.Mont.AArch64.loads [.x5,.x6,.x7,.x8] src)) s fun t =>
      regsVal t [.x5,.x6,.x7,.x8]=wordsVal s.mem base src 4 ∧ Keeps [.x5,.x6,.x7,.x8] s t := by
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok hs (d:=src) (by omega_using [hsrc]) hsrc8 .x5) fun a ⟨va,ka,_⟩ => ?_
  have sa := hs.of_keeps ka (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sa (d:=src+8) (by omega_using [hsrc]) (by omega_using [hsrc8]) .x6) fun b ⟨vb,kb,_⟩ => ?_
  have sb := sa.of_keeps kb (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sb (d:=src+8+8) (by omega_using [hsrc]) (by omega_using [hsrc8]) .x7) fun c ⟨vc,kc,_⟩ => ?_
  have sc := sb.of_keeps kc (by decide)
  rw [VG.Impl.Mont.AArch64.loads,←List.singleton_append,WP.block_append_iff]
  refine WP.mono (ld_ok sc (d:=src+8+8+8) (by omega_using [hsrc]) (by omega_using [hsrc8]) .x8) fun t ⟨vt,kt,_⟩ => ?_
  apply WP.block_nil
  refine ⟨?_,?_,kt.mem.trans (kc.mem.trans (kb.mem.trans ka.mem)),kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
    kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
  · simp only [regsVal,wordsVal,kt.gpr .x5 (by decide),kt.gpr .x6 (by decide),kt.gpr .x7 (by decide),
      kc.gpr .x5 (by decide),kc.gpr .x6 (by decide),kb.gpr .x5 (by decide),va,vb,vc,vt,
      kc.mem,kb.mem,ka.mem]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    rw [kt.gpr r (by simpa using hr.2.2.2),kc.gpr r (by simpa using hr.2.2.1),
      kb.gpr r (by simpa using hr.2.1),ka.gpr r (by simpa using hr.1)]

end VG.Proof.Weierstrass.AArch64
