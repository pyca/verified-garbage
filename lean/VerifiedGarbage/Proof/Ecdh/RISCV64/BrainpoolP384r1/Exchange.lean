module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.Tail
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
public import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdh.RISCV64.BrainpoolP384r1.CheckLit
import VerifiedGarbage.Proof.BrainpoolP384r1.Point

/-!
# ECDH over brainpoolP384r1 on RISC-V: correctness

The curve's kit for `Proof/Ecdh/RISCV64/ExchangeAll.lean`, and what that
proof gives of `vg_ecdh_brainpoolp384r1`: it meets its contract by register (`ecdhRV`), given
the group law (`ecdh_rv`); the peer's point read to the check's slots
(`peerLoad_ok`) and its check (`check_ok`), which verification and the
compressed keys use too.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.BrainpoolP384r1

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes)

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP384r1.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 48⟩
    let d : Region := ⟨s.gpr .a1, 48⟩
    let peer : Region := ⟨s.gpr .a2, 97⟩
    let scratch : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .a0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 48 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + 8192 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    match ex s.mem (s.gpr .a1) (s.gpr .a2) with
    | some z => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 48 = z
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3

theorem onG : Spec.Weierstrass.onCurve W (Spec.Weierstrass.G W) = true := VG.Proof.BrainpoolP384r1.onCurve_G

theorem checkNF : checkBrainpoolP384r1.noFrames = true := checkBrainpoolP384r1_noFrames

/-- The curve's kit. -/
def kit : Kit where
  c := brainpoolp384r1
  L := 48
  len := rfl
  n9 := by decide
  Ln := by decide
  unit := unit
  onG := onG
  load := loadNum 6
  store := storeNum 6
  load_ok := Kit.loadNum_kit (c := brainpoolp384r1) (by decide)
  store_ok := Kit.storeNum_kit (c := brainpoolp384r1) (by decide)
  CC := CC
  CCW := rfl
  CCk := rfl
  checkN := "vg_brainpoolp384r1_check_point"
  checkC := checkBrainpoolP384r1
  checkNF := checkNF
  check_rv := check_rv
  num_eq := fun m ws i hi => num_eq m ws i hi
  flag_eq := flag_eq
  checkKW := checkKW
  check_unch := unch_of_checkKeeps
  check_lo := by decide
  check_keep := by decide
  mulN := "vg_brainpoolp384r1_mul"
  mulC := mulBrainpoolP384r1
  tailW := tailW
  tail_lo := by decide
  tail_ok := fun hL _ _ hw h3 a1 a2 a3 a4 a5 a6 a7 a8 => tail_ok hL hw h3 ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  andFlag_ok := andFlag_ok
  save_ok := save_ok
  cs := 41
  consts_ok := consts_ok
  consts_slots := consts_slots
  consts_lt := consts_lt

/-- What the contract gives, by register. -/
abbrev EPre (s : State) : Prop := kit.EPre s

/-- The peer's point read from `[q]` (`x` and `y` to the check's slots), the
flag set to the mask of its first byte being `04`, and the constants. -/
theorem peerLoad_ok {s : State} {base : Addr} {q : Reg} (hw : WsReg s base) (hq : q ∉ [Reg.t0, .t1, .a7])
    (hrd : (⟨s.gpr q, 97⟩ : Region) ∈ s.rd ++ s.wr) (hdis : (⟨s.gpr q, 97⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hfit : (s.gpr q).toNat + 97 ≤ 2 ^ 64) :
    WP isa (.block (loadNum brainpoolp384r1.n (brainpoolp384r1.sl CX) q 1 ++ loadNum brainpoolp384r1.n (brainpoolp384r1.sl CY) q (1 + 8 * brainpoolp384r1.n) ++
      leadMask q ++ sdAt .a7 wb (brainpoolp384r1.sl FLAG) ++ constCode brainpoolp384r1)) s fun s' =>
      WsReg s' base ∧ Rest [.t0, .t1, .a7] s s' ∧
      Unch base ([(brainpoolp384r1.sl CX, 8 * 6)] ++ [(brainpoolp384r1.sl CY, 8 * 6)] ++ [(FL, 8)] ++
        (consts brainpoolp384r1).map fun e => (brainpoolp384r1.sl e.1, 48)) s.mem s'.mem ∧
      sv base s' CX = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 1) 48) ∧
      sv base s' CY = ofBytes (bytesAt s.mem (s.gpr q + BitVec.ofNat 64 49) 48) ∧
      word s'.mem base FL = maskOf (decide (s.mem (s.gpr q) = 4)) ∧
      ∀ e ∈ consts brainpoolp384r1, sv base s' e.1 = e.2 :=
  kit.peerLoad_ok hw hq hrd hdis hfit

/-- The check of the peer's point, by its call. -/
theorem check_ok {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base) (hc : ∀ e ∈ consts brainpoolp384r1, sv base s e.1 = e.2)
    (hf : word s.mem base FL = 0 ∨ word s.mem base FL = BitVec.allOnes 64) :
    WP isa (wsCall "vg_brainpoolp384r1_check_point" checkBrainpoolP384r1) s fun s' =>
      Kp s s' ∧ Unch base checkKW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&&
        Impl.Weierstrass.CheckPoint.Curve.mask (CC.Valid (sv base s CX) (sv base s CY)) ∧
      sv base s' CPX = (if word s'.mem base FL = 0 then sv base s GX else sv base s CX * 2 ^ 384 % W.p) ∧
      sv base s' CPY = (if word s'.mem base FL = 0 then sv base s GY else sv base s CY * 2 ^ 384 % W.p) :=
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
    ∃ t s', Exec isa ecdhBrainpoolP384r1 s t s' ∧ abiPreserved s s' ∧ ecdhRV.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  obtain ⟨t, s', he, h⟩ := kit.ecdh_ok hL ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨t, s', he, h⟩

end VG.Proof.Ecdh.RISCV64.BrainpoolP384r1
