module

public import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem slSub_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hA : sv c base s a < c.C.p) (hB : sv c base s b < c.C.p) :
    WP isa (Mont.subCall c.SP (c.sl o) (c.sl a) (c.sl b)) s fun t =>
      CKeep c.MP' base c.wk (c.sl o) s t ∧
      sv c base t o = (sv c base s a + c.C.p - sv c base s b) % c.C.p :=
  subC_ok (slCall (MP'_n c) hc.fp) hs (sl_below_wk c ho) (sl_below_wk c ha) (sl_below_wk c hb) hA hB

end VG.Proof.EcKey.Compressed.X86
