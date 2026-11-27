module

public import VerifiedGarbage.Impl.Bignum.Arm.MontCore
import VerifiedGarbage.Proof.Bignum.Arm.MontRounds
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.MontState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontFinish
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.MontFinish
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.FinishArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.Csub
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Bignum.Arm.MontFinishCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.CsubCT`, which this module and modules that import it used -/

section

/-! # Final modular reduction has no secret-dependent branches or addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem csub_ct : ConstantTime isa (fun _ => True)
    (fun s t => ∀ r ∈ [.r0, .r7, .r9, .r10, .r12, .lr], s.gpr r = t.gpr r) csub := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r7, .r9, .r10, .r12, .lr]) ?_
    (by taint_decide)
  intro s t _ _ h
  exact Taint.agree_ofRegs h

end VG.Proof.Bignum.Arm

end

end

/-! # Final reduction leaks only its count and pointers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure FinishReady (base : BitVec 32) (size tmp out acc mod n : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp
  count : s.mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n
  outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out
  accPtr : s.mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc
  mPtr : s.mem.readW (off (State.addr base) (tmp + 8)) 32 = base + BitVec.ofNat 32 mod

theorem montFinish_ct {base : BitVec 32} {size tmp out acc mod n : Nat} (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => FinishReady base size tmp out acc mod n s ∧
      FinishReady base size tmp out acc mod n t) montFinish (fun _ _ => True) := by
  let P := FinishReady base size tmp out acc mod n
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 tmp ∧
    s.gpr .r7 = BitVec.ofNat 32 n ∧ s.gpr .r9 = base + BitVec.ofNat 32 out ∧
    s.gpr .r10 = base + BitVec.ofNat 32 acc ∧ s.gpr .r12 = base + BitVec.ofNat 32 mod ∧
    s.gpr .lr = BitVec.ofNat 32 n
  have ct : RelCT isa (fun s t => P s ∧ P t) (.block finishArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    simpa only [List.mem_singleton, forall_eq] using h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block finishArgs) s Q := by
    refine WP.mono (finishArgs_ok s h.workspace ht h.ptr h.count h.outPtr h.accPtr h.mPtr) ?_
    rintro t ⟨p0, p9, p10, p12, count, lr, _⟩
    exact ⟨p0, count, p9, p10, p12, lr⟩
  unfold montFinish
  refine (pair_posts ct wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  refine ⟨csub_ct s t tr1 tr2 u v trivial trivial ?_ e1 e2, trivial⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases h with ⟨⟨s0, s7, s9, s10, s12, slr⟩, ⟨t0, t7, t9, t10, t12, tlr⟩⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact s0.trans t0.symm
  · exact s7.trans t7.symm
  · exact s9.trans t9.symm
  · exact s10.trans t10.symm
  · exact s12.trans t12.symm
  · exact slr.trans tlr.symm

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.MontRoundsCT`, which this module and modules that import it used -/

section

/-! # Constant-time Montgomery scanning with secret operands and inverse -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem montRound_ready {base : BitVec 32} {size tmp a b mod acc n i : Nat} (hi : i < n)
    (s : State) (h : RoundReady base size tmp a b mod acc n i s) :
    WP isa montRound s fun t => RoundReady base size tmp a b mod acc n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.secret
  refine WP.mono (montRound_ok s h.ctx hdr hi h.ptr h.bound h.operand inverse) ?_
  intro t post
  have nowrap := h.ctx.workspace.nowrap
  have fitsB := h.ctx.bFits
  have fitsM := h.ctx.mFits
  have accB := h.ctx.accB
  have accM := h.ctx.accM
  have tmpB := h.ctx.tmpB
  have tmpM := h.ctx.tmpM
  have oldB := post.outside.val32 (d := b) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fitsB])
  have oldM := post.outside.val32 (d := mod) (k := n) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fitsM])
  refine ⟨⟨h.ctx.congr post.rest.wr, ⟨inv, post.hdr, ?_⟩, post.ptr, ?_, ?_⟩, post.zero⟩
  · rw [oldM]; exact inverse
  · rw [oldM]; exact post.bound
  · rw [oldB, oldM]; exact h.operand

theorem montRounds_ct {base : BitVec 32} {size tmp a b mod acc n : Nat} :
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n 0 s ∧
      RoundReady base size tmp a b mod acc n 0 t) montRounds (fun _ _ => True) := by
  let I := fun k s t => ∃ i, i + k = n ∧ 0 < k ∧
    RoundReady base size tmp a b mod acc n i s ∧ RoundReady base size tmp a b mod acc n i t
  have step : ∀ k, RelCT isa (I k) montRound fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k
    apply RelCT.exists_
    intro i s t tr1 tr2 u v h e1 e2
    obtain ⟨hik, hk, hs, ht⟩ := h
    have hi : i < n := by omega_using [hik, hk]
    obtain ⟨trace, posts⟩ := pair_posts (montRound_ct hi) (montRound_ready hi)
      s t tr1 tr2 u v ⟨hs, ht⟩ e1 e2
    obtain ⟨⟨hu, zu⟩, ⟨hv, zv⟩⟩ := posts
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      have ne : i + 1 ≠ n := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, ne], hu, hv⟩
  apply (RelCT.loop I step n).mono _ (fun _ _ h => h)
  intro s t h
  have count := h.1.ctx.count
  exact ⟨0, by omega_using [], by omega_using [count], h⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Constant time of canonical Montgomery multiplication after initialization -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure CoreReady (base : BitVec 32) (size out tmp a b mod acc n : Nat) (s : State) : Prop where
  round : RoundReady base size tmp a b mod acc n 0 s
  outPtr : s.mem.readW (off (State.addr base) (tmp + 24)) 32 = base + BitVec.ofNat 32 out
  zero : val32 s.mem (State.addr base) acc (n + 2) = 0

theorem montRounds_finishReady {base : BitVec 32} {size out tmp a b mod acc n : Nat}
    (s : State) (h : CoreReady base size out tmp a b mod acc n s) :
    WP isa montRounds s (FinishReady base size tmp out acc mod n) := by
  obtain ⟨inv, hdr, inverse⟩ := h.round.secret
  refine WP.mono (montRounds_ok s h.round.ctx hdr h.round.ptr h.zero h.round.operand inverse) ?_
  intro t loop
  have nowrap := h.round.ctx.workspace.nowrap
  have layout := h.round.ctx.layout
  have fits := h.round.ctx.tmpFits
  have oldOut := outs_word32 loop.outside (d := tmp + 24) (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_using [nowrap, fits])
  refine ⟨h.round.ctx.workspace.congr loop.rest.wr, loop.ptr, loop.hdr.count, ?_,
    loop.hdr.accPtr, loop.hdr.mPtr⟩
  apply BitVec.eq_of_toNat_eq
  exact oldOut.trans (congrArg BitVec.toNat h.outPtr)

theorem montCore_ct {base : BitVec 32} {size out tmp a b mod acc n : Nat} (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => CoreReady base size out tmp a b mod acc n s ∧
      CoreReady base size out tmp a b mod acc n t) montCore (fun _ _ => True) := by
  have rounds := pair_posts (P := CoreReady base size out tmp a b mod acc n)
    (montRounds_ct.mono (fun _ _ h => ⟨h.1.round, h.2.round⟩) (fun _ _ h => h)) montRounds_finishReady
  exact rounds.seq (montFinish_ct ht)

end VG.Proof.Bignum.Arm
