module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared input and workspace setup for ARMv7 point conversion -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

 structure InputPre (c : Cfg) (len : Nat) (s : State) : Prop where
  pk : (⟨ptr s .r1, len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨ptr s .r2, 8192⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨ptr s .r1, len⟩ ⟨ptr s .r2, 8192⟩
  pk_fit : (s.gpr .r1).toNat + len ≤ 2 ^ 32
  ws_fit : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

 theorem input_setup {c : Cfg} {len : Nat} {s : State}
    (hp : InputPre c len s) (hlen : c.C.len ≤ len) :
    SetupPre c Impl.EcKey.Compressed.Arm.args s := by
  change SetupPre c ⟨.r1, .r1, .r1, some .r2, none⟩ s
  have hf := hp.pk_fit
  have hi : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s .r1 + BitVec.ofNat 64 e) 4 := by
    intro e he
    exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨ptr s .r1, c.C.len⟩ ⟨ptr s .r2, size⟩ :=
    (hp.disjoint.sub_left (by simpa using Offset.sub_base (ptr s .r1) (d := 0) (by omega : 0 + c.C.len ≤ len))).sub_right
      (by simpa using Offset.sub_base (ptr s .r2) (d := 0) (by decide : size ≤ 8192))
  refine ⟨.inl rfl, by simp [argsOk], ?_, hp.ws, hi, hi, hi, hd, hd, hd,
    by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega, by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega,
    by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega, hp.ws_fit⟩
  intro h
  cases h

 theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c Impl.EcKey.Compressed.Arm.args s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved⟩

end VG.Proof.EcKey.Compressed.Arm
