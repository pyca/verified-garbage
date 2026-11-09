module

-- separate module: the native peer-prefix identity is separate from the public-buffer permission adapter

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareValidate
public import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Framework.Lit

/-! The native preparation reads and masks the peer with the existing checked code. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP QY)
open VG.Impl.Weierstrass.AArch64.P521Native (outerBlock003 config)

def preparePeer : Prog isa := .block (outerBlock003.take 137)

theorem prepare_peer_prefix : outerBlock003.take 137=VG.Impl.Ecdh.AArch64.Cfg.peer config := by lit_decide

theorem prepare_peer_ok (hc : BaseCfgOk config) {base : Addr} {s : State} (hs : Scr s base size) {q : Addr}
    (hq : s.gpr .x6=q) (hin : (⟨q,1+2*config.C.len⟩ : Region)∈s.rd++s.wr)
    (apart : Region.Disjoint ⟨q,1+2*config.C.len⟩ ⟨base,size⟩) :
    WP isa preparePeer s fun t =>
      Scr t base size ∧ KeepRegs [.x1,.x2,.x5,.x7,.x16,.x17] s t ∧
      Unch base (slW config [R2P,BP,QY]++[(config.sl VG.Impl.Ecdsa.AArch64.FLAG,8)]) s.mem t.mem ∧
      sv config base t R2P=config.R*config.R%config.C.p ∧ sv config base t BP=config.mont config.C.b ∧
      sv config base t QY=VG.Spec.Weierstrass.ofBytes
        (VG.Spec.Ecdsa.bytesAt s.mem (q+BitVec.ofNat 64 (1+config.C.len)) config.C.len) ∧
      word t.mem base (config.sl VG.Impl.Ecdsa.AArch64.FLAG)=
        word s.mem base (config.sl VG.Impl.Ecdsa.AArch64.FLAG)&&&VG.Proof.Weierstrass.mask (s.mem q=4) := by
  rw [preparePeer,prepare_peer_prefix]
  exact VG.Proof.Ecdh.AArch64.peer_ok hc hs hq hin apart

end VG.Proof.Weierstrass.AArch64.P521Native
