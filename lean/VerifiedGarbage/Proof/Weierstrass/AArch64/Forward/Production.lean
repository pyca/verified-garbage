import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256DR
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256ED
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds

namespace VG.Proof.Weierstrass.AArch64.Forward.Production

theorem cases : Fixed.Cases where
  rd := ⟨P256RD.checked,P256Bounds.rd_left,P256Bounds.rd_right,P256Bounds.rd_clob⟩
  dr := ⟨P256DR.checked,P256Bounds.dr_left,P256Bounds.dr_right,P256Bounds.dr_clob⟩
  ed := ⟨P256ED.checked,P256Bounds.ed_left,P256Bounds.ed_right,P256Bounds.ed_clob⟩

end VG.Proof.Weierstrass.AArch64.Forward.Production
