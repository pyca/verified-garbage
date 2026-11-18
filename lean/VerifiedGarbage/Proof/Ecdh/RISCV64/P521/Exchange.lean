module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.Tail
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.RISCV64.P521.CheckLit
import VerifiedGarbage.Proof.P521.Point

/-!
# ECDH over P-521 on RISC-V: correctness

The curve's kit for `Proof/Ecdh/RISCV64/ExchangeAll.lean`, and what that
proof gives of `vg_ecdh_p521`: it meets its contract by register (`ecdhRV`), given
the group law (`ecdh_rv`); the peer's point read to the check's slots
(`peerLoad_ok`) and its check (`check_ok`), which verification and the
compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P521

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P521
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P521.curve (ofBytes (bytesAt m d 66)) (bytesAt m peer 133)

def ecdhRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 66⟩
    let d : Region := ⟨s.gpr .a1, 66⟩
    let peer : Region := ⟨s.gpr .a2, 133⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .a0).toNat + 66 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 66 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    match ex s.mem (s.gpr .a1) (s.gpr .a2) with
    | some z => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 66 = z
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 66 = List.replicate 66 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

theorem onG : Spec.Weierstrass.onCurve W (Spec.Weierstrass.G W) = true := VG.Proof.P521.onCurve_G

theorem checkNF : checkP521.noFrames = true := checkP521_noFrames

/-- The curve's kit. -/
def kit : Kit where
  toTKit := tkit
  L := 66
  len := rfl
  Ln := by decide
  onG := onG
  load := loadLen 66
  store := storeLen 66
  load_ok := Kit.loadLen_kit (c := p521) (by decide) (by decide)
  store_ok := Kit.storeLen_kit (c := p521) (by decide) (by decide)
  checkN := "vg_p521_check_point"
  checkNF := checkNF
  mulN := "vg_p521_mul"
  mulC := mulP521
  mulNF := mulNF
  mul_rv := mul_meets
  chainP_ok := chainP_ok
  consts_lt := consts_lt

/-- What the contract gives, by register. -/
abbrev EPre (s : State) : Prop := kit.EPre s

/-- The peer's point read from `[q]` (`x` and `y` to the check's slots), the
flag set to the mask of its first byte being `04`, and the constants. -/
theorem peerLoad_ok {s : State} {base : Addr} {q : Reg} (hw : WsReg s base) (hq : q ∉ [Reg.t0, .t1, .a7])
    (hrd : (⟨s.gpr q, 133⟩ : Region) ∈ s.rd ++ s.wr) (hdis : (⟨s.gpr q, 133⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hfit : (s.gpr q).toNat + 133 ≤ 2 ^ 64) :
    WP isa (.block (loadLen p521.C.len (p521.sl CX) q 1 ++ loadLen p521.C.len (p521.sl CY) q (1 + p521.C.len) ++
      leadMask q ++ sdAt .a7 wb (p521.sl FLAG) ++ constCode p521)) s fun s' =>
      WsReg s' base ∧ Rest [.t0, .t1, .a7] s s' ∧
      Unch base ([(p521.sl CX, 8 * 9)] ++ [(p521.sl CY, 8 * 9)] ++ [(FL, 8)] ++
        (consts p521).map fun e => (p521.sl e.1, 72)) s.mem s'.mem ∧
      sv base s' CX = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 1) 66) ∧
      sv base s' CY = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 67) 66) ∧
      word s'.mem base FL = maskOf (decide (s.mem (s.gpr q) = 4)) ∧
      ∀ e ∈ consts p521, sv base s' e.1 = e.2 :=
  kit.peerLoad_ok hw hq hrd hdis hfit

/-- The check of the peer's point, by its call. -/
theorem check_ok {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base) (hc : ∀ e ∈ consts p521, sv base s e.1 = e.2)
    (hf : word s.mem base FL = 0 ∨ word s.mem base FL = BitVec.allOnes 64) :
    WP isa (wsCall "vg_p521_check_point" checkP521) s fun s' =>
      Kp s s' ∧ Unch base checkKW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&&
        Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid (sv base s CX) (sv base s CY)) ∧
      sv base s' CPX = (if word s'.mem base FL = 0 then sv base s GX else sv base s CX * 2 ^ 576 % W.p) ∧
      sv base s' CPY = (if word s'.mem base FL = 0 then sv base s GY else sv base s CY * 2 ^ 576 % W.p) :=
  kit.check_ok hw h3 hc hf

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    bytesAt m p (1 + 2 * L) = m p :: (bytesAt m (p + BitVec.ofNat 64 1) L ++
      bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) :=
  Kit.peer_bytes m p L

theorem mask_eq (P : Prop) [Decidable P] : Impl.Weierstrass.CheckPoint.Curve.mask P = maskOf (decide P) :=
  Kit.mask_eq P

/-- The check's validity is the specification's, but for the first byte. -/
theorem valid_iff (x y : Nat) :
    CC.Valid x y ↔ x < W.p ∧ y < W.p ∧ VG.Proof.Ecdh.OnCurveF W x y :=
  Kit.valid_iff_of rfl x y

theorem ecdh_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : ecdhRV.pre s) :
    ∃ t s', Exec isa ecdhP521 s t s' ∧ abiPreserved s s' ∧ ecdhRV.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  obtain ⟨t, s', he, h⟩ := kit.ecdh_ok hL ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdh.RISCV64.P521
