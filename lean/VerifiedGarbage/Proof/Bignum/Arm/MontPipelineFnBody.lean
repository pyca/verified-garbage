module

public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineLoop
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineRound
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline
import VerifiedGarbage.Proof.Bignum.Arm.LayoutBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Bignum.Arm.MontFinish
import VerifiedGarbage.Proof.Bignum.Arm.MontInit

/-! ### `Bignum.Arm.MontPipelineCore`, which only this module used -/

section

/-! Lift any native scanning round through the existing Montgomery pipeline. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem core_ok (round : Prog isa) (law : LoopLaw round) (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (even : n % 2 = 0) (finish : CsubCtx s base size out acc mod tmp n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n 0 inv)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out)
    (hzero : val32 s.mem (State.addr base) acc (n + 2) = 0)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.core round) s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) b n % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp + 16, 8), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have hn := ctx.count
  have nowrap := ctx.workspace.nowrap
  have fitsM := ctx.mFits
  have accM := ctx.accM
  have tmpM := ctx.tmpM
  have tmpFits := ctx.tmpFits
  have layout := ctx.layout
  rw [VG.Impl.Bignum.Arm.MontPipeline.core, WP.seq_iff]
  refine WP.mono (law s ctx even hdr ptr hzero hB hInv) ?_
  intro u loop
  have oldM := loop.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fitsM])
  have oldOut := outs_word32 loop.outside (d := tmp + 24) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, tmpFits])
  have outU : u.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out := by
    apply BitVec.eq_of_toNat_eq
    exact oldOut.trans (congrArg BitVec.toNat outPtr)
  refine WP.mono (montFinish_ok u (finish.congr loop.rest.wr) (by omega_using [hn]) tmpFits loop.ptr
    loop.hdr.count outU loop.hdr.accPtr loop.hdr.mPtr (by rw [oldM]; exact loop.bound)) ?_
  rintro t ⟨value, outside, keep⟩
  rw [oldM] at value
  refine ⟨?_, ?_, ?_, loop.rest.trans keep⟩
  · rw [value]; exact Nat.mod_lt _ (by omega_using [hB])
  · rw [value, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    exact loop.value
  · exact (loop.outside.mono (by simp)).trans (outside.mono (by simp))


end VG.Proof.Bignum.Arm.MontPipeline

end

end

/-! Lift any native scanning round through the existing Montgomery pipeline. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontPipelineBody.lean`, which only this module imported.
section

/-! Lift any native scanning round through the existing Montgomery pipeline. -/

section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem body_ok (round : Prog isa) (law : LoopLaw round) (s : State) {base : BitVec 32} {size out tmp a b mod acc n : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (even : n % 2 = 0) (finish : CsubCtx s base size out acc mod tmp n)
    (regs : InitRegs s base out tmp a b mod acc n inv)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.body round) s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) b n % val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(acc, 4 * (n + 2)), (tmp, 32), (tmp + 16, 8), (tmp, 4 * n), (out, 4 * n)] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.MontPipeline.body, WP.seq_iff]
  refine WP.mono (montInit_ok s ctx regs hB hInv) ?_
  rintro u ⟨ready, outsideU, restU⟩
  obtain ⟨inverse, header, hinverse⟩ := ready.round.secret
  refine WP.mono (core_ok round law u ready.round.ctx even (finish.congr restU.wr) header ready.round.ptr
    ready.outPtr ready.zero ready.round.operand hinverse) ?_
  rintro t ⟨bound, value, outsideT, restT⟩
  have nowrap := ctx.workspace.nowrap
  have old (d : Nat) (fits : d + 4 * n ≤ size)
      (sepA : d + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ d)
      (sepT : d + 4 * n ≤ tmp ∨ tmp + 32 ≤ d) :
      val32 u.mem (State.addr base) d n = val32 s.mem (State.addr base) d n :=
    outsideU.val32 (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepA
      · exact sepT) (by omega)
  have oldM := old mod ctx.mFits ctx.accM.symm ctx.tmpM.symm
  have oldA := old a ctx.aFits ctx.accA.symm ctx.tmpA.symm
  have oldB := old b ctx.bFits ctx.accB.symm ctx.tmpB.symm
  rw [oldM] at bound
  rw [oldM, oldA, oldB] at value
  exact ⟨bound, value, (outsideU.mono (by simp)).trans (outsideT.mono (by simp)), restU.trans restT⟩


end VG.Proof.Bignum.Arm.MontPipeline
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)

theorem fnBody_ok (round : Prog isa) (law : LoopLaw round) (s : State) {base : BitVec 32} {len o a b : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (ptr : s.gpr .r0 = base) (po : s.gpr .r2 = BitVec.ofNat 32 o)
    (pa : s.gpr .r3 = BitVec.ofNat 32 a) (pb : s.gpr .r12 = BitVec.ofNat 32 b)
    (inverse : ((word s.mem (State.addr base) (arrAt (wOf s.mem (State.addr base)) 0)).toNat *
      (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0)
    (operand : numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) b <
      numAt s.mem (State.addr base) (wOf s.mem (State.addr base)) 0) :
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.fnBody round) s fun t =>
      let w := wOf s.mem (State.addr base)
      let M := numAt s.mem (State.addr base) w 0
      numAt t.mem (State.addr base) w o < M ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % M =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := wOf s.mem (State.addr base)
  have hw : 2 ≤ w := layout.1
  have fits : arrAt w 8 ≤ 8 * len := layout.2.2.1
  have header := nativeHeader_of_layout s.mem base ws.nowrap (Nat.le_refl _) layout
  obtain ⟨ctx, finish⟩ := layout_context ws hw fits ho ha hb
  have bound : 128 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega_using [fits]
  rw [VG.Impl.Bignum.Arm.MontPipeline.fnBody, WP.seq_iff]
  refine WP.mono (bases_ok s ws bound header ho.1 ha.1 hb.1 ptr po pa pb) ?_
  rintro u ⟨regs, mem, keep⟩
  refine WP.mono (body_ok round law u (ctx.congr keep.wr) (by omega_using []) (finish.congr keep.wr) regs ?_ ?_) ?_
  · rw [mem, ← numAt_native, ← numAt_native]; exact operand
  · rw [mem]; exact native_inverse s.mem (State.addr base) (by omega_using [hw]) inverse
  · rintro t ⟨lt, value, outside, rest⟩
    rw [mem] at lt value outside
    refine ⟨?_, ?_, keeps_of_native ws.nowrap hw outside, frame_of_native hw ho.1 fits outside, keep.trans rest⟩
    · simpa only [numAt_native] using lt
    · rw [numAt_native, numAt_native, numAt_native, numAt_native, Nat.mul_comm _ (2 ^ (64 * w))]
      simpa only [radix32] using value


end VG.Proof.Bignum.Arm.MontPipeline
