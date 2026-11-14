module

public import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.ArgsCT
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionCT
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.Round
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath

/-! ### `Bignum.Arm.FusedReductionStageCT`, which only this module used -/

section

/-! Cancellation writes the shifted result without leaking secret limbs. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem fusedReductionStage_relCT {base : BitVec 32} {size tmp a b mod acc n i : Nat} :
    RelCT isa (fun s t => StageReady base size tmp a b mod acc n i (acc + 4 * n) s ∧
      StageReady base size tmp a b mod acc n i (acc + 4 * n) t) fusedReductionStage (fun s t => s.gpr .r0=t.gpr .r0) := by
  let P := StageReady base size tmp a b mod acc n i (acc + 4 * n)
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 acc ∧
    s.gpr .r12 = base + BitVec.ofNat 32 mod ∧ s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block reductionArgs) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨cs, ⟨is, hs⟩, ps⟩ := h.1
    obtain ⟨ct, ⟨it, ht⟩, pt⟩ := h.2
    have layout := cs.layout
    have fits := cs.tmpFits
    apply reductionArgs_ct (base := base) (size := size) (top := acc + 4 * n) (acc := acc) (by omega_using [layout, fits]) s t tr1 tr2 u v ?_ e1 e2
    refine ⟨cs.workspace, ct.workspace, ps, pt, ?_, ?_⟩
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega_using [layout]] using hs.accPtr
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega_using [layout]] using ht.accPtr
  have wp (s : State) (h : P s) : WP isa (.block reductionArgs) s Q := by
    obtain ⟨ctx, ⟨inv, hdr⟩, ptr⟩ := h
    have layout := ctx.layout
    have fits := ctx.tmpFits
    refine WP.mono (reductionArgs_ok s (acc := acc) (mod := mod) (n := n) inv ctx.workspace
      (by omega_using [layout, fits]) (by omega_using [layout, fits]) ptr ?_ ?_ ?_ ?_) (fun _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩)
    · simpa only [show acc + 4 * n + 16 = tmp by omega_using [layout]] using hdr.count
    · simpa only [show acc + 4 * n + 24 = tmp + 8 by omega_using [layout]] using hdr.mPtr
    · simpa only [show acc + 4 * n + 28 = tmp + 12 by omega_using [layout]] using hdr.inverse
    · simpa only [show acc + 4 * n + 44 = tmp + 28 by omega_using [layout]] using hdr.accPtr
  unfold fusedReductionStage
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact FusedReduction.code_relCT s t tr1 tr2 u v
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2


end VG.Proof.Bignum.Arm

end

end


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
  have modulus := outside.val32 (d := mod) (k := n) (by omega_using [sep]) (by omega_using [nowrap, fits])
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
