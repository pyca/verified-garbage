module

public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionStageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A Montgomery round leaks only its public layout and word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure RoundReady (base : BitVec 32) (size tmp a b mod acc n i : Nat) (s : State) : Prop where
  ctx : RoundCtx s base size tmp a b mod acc n
  secret : ∃ inv, RoundMeta s.mem base tmp a b mod acc n i inv ∧
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp
  bound : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n
  operand : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n

structure ReductionReady (base : BitVec 32) (size tmp a b mod acc n i : Nat) (s : State) : Prop where
  ctx : RoundCtx s base size tmp a b mod acc n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * n)
  secret : ∃ inv, RoundMeta s.mem base tmp a b mod acc n i inv ∧
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0 ∧
    val32 s.mem (State.addr base) acc (n + 2) +
      (inv * s.mem.readW (off (State.addr base) acc) 32).toNat * val32 s.mem (State.addr base) mod n <
        2 ^ (32 * (n + 2))

theorem RoundReady.stage {base : BitVec 32} {size tmp a b mod acc n i : Nat} {s : State}
    (h : RoundReady base size tmp a b mod acc n i s) :
    StageReady base size tmp a b mod acc n i tmp s :=
  ⟨h.ctx, h.secret.elim (fun inv hi => ⟨inv, hi.1⟩), h.ptr⟩

theorem ReductionReady.stage {base : BitVec 32} {size tmp a b mod acc n i : Nat} {s : State}
    (h : ReductionReady base size tmp a b mod acc n i s) :
    StageReady base size tmp a b mod acc n i (acc + 4 * n) s :=
  ⟨h.ctx, h.secret.elim (fun inv hi => ⟨inv, hi.1⟩), h.ptr⟩

theorem productStage_ready {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n)
    (s : State) (h : RoundReady base size tmp a b mod acc n i s) :
    WP isa productStage s (ReductionReady base size tmp a b mod acc n i) := by
  obtain ⟨inv, hdr, inverse⟩ := h.secret
  refine WP.mono (productStage_ok s h.ctx hdr hi h.ptr h.bound h.operand) ?_
  rintro t ⟨product, header, ptr, outside, keep⟩
  have nowrap := h.ctx.workspace.nowrap
  have fits := h.ctx.mFits
  have sep := h.ctx.accM
  have modulus := outside.val32 (d := mod) (k := n) (by omega) (by omega)
  refine ⟨h.ctx.congr keep.wr, ptr, inv, header, ?_, ?_⟩
  · rw [modulus]; exact inverse
  · rw [product, modulus]
    exact round_fit h.bound (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
      h.operand (inv * t.mem.readW (off (State.addr base) acc) 32).isLt
      (val32_lt s.mem (State.addr base) mod n)

theorem montRound_ct {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n) :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n i s ∧
      RoundReady base size tmp a b mod acc n i t) montRound (fun _ _ => True) := by
  have product := pair_posts (P := RoundReady base size tmp a b mod acc n i) ((productStage_ct hi).mono
    (fun _ _ h => ⟨h.1.stage, h.2.stage⟩) (fun _ _ h => h)) (productStage_ready hi)
  have reduction : RelCT isa
      (fun s t => ReductionReady base size tmp a b mod acc n i s ∧
        ReductionReady base size tmp a b mod acc n i t)
      fusedReductionStage (fun s t => s.gpr .r0=t.gpr .r0) :=
    fusedReductionStage_relCT.mono (fun _ _ h => ⟨h.1.stage,h.2.stage⟩) (fun _ _ h => h)
  have finish : RelCT isa (fun s t => s.gpr .r0=t.gpr .r0)
      (.block roundFinish) (fun _ _ => True) := by
    apply RelCT.taint (A:=taint) (Taint.ofRegs [.r0]) ?_ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (by simpa using h)
  exact product.seq (reduction.seq finish)

end VG.Proof.Bignum.Arm
