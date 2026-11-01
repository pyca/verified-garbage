module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Resident.Pair
meta import VerifiedGarbage.Proof.Scrypt.AArch64.Resident.Pair
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.MdStream.AArch64.Common
meta import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.MdStream.AArch64.Common
meta import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
meta import VerifiedGarbage.Proof.Scrypt.AArch64.Common
public import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixVerified
public import VerifiedGarbage.Proof.Scrypt.AArch64.Common
public import VerifiedGarbage.Proof.Scrypt.Contract

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Resident
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Proof.Scrypt.AArch64.BlockMix
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt bytesAt_congr)
open VG.Proof.MdStream.AArch64 (eval_nonzero ofNat_beq_zero write_frame_bytes)

theorem loop_ok {s₀ : State} (hp : BlockMix.Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.loop VG.Impl.Scrypt.AArch64.Resident.body (.nonzero .x .x23)) s (Inv s₀ (rr s₀)) := by
  have lt := r_lt hp
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀-k ∧ k < rr s₀ ∧ Inv s₀ k s)
    ?_ (rr s₀) s ⟨0,rfl,hp.pos,h⟩
  rintro n s ⟨k,rfl,hk,hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' hi' => ?_
  have hz : isa.eval (.nonzero .x .x23) s' = some (decide (rr s₀-(k+1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x23) s' = _
    rw [eval_nonzero,hi'.x23,bne,ofNat_beq_zero (by omega)]
    simp
  by_cases hl : rr s₀-(k+1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl],?_⟩
    rwa [show k+1 = rr s₀ by omega] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl],rr s₀-(k+1),by omega,k+1,rfl,by omega,hi'⟩

theorem prologue_ok {s₀ : State} (hp : BlockMix.Pre s₀) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Resident.prologue) s₀ (BlockMix.Inv s₀ 0) := by
  change WP isa (.block VG.Impl.Scrypt.AArch64.bmPrologue) s₀ _
  rw [prologue_eq]
  exact save_ok hp fun s₁ g hrd hwr hsp hm => setup_ok hp g hrd hwr hsp hm

theorem correctMain {s₀ : State} (hp : BlockMix.Pre s₀) :
    WP isa VG.Impl.Scrypt.AArch64.Resident.main s₀ fun s' =>
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ bytesAt s'.mem (yP s₀) (128*rr s₀) = blockMix (rr s₀) (BlockMix.B s₀) := by
  refine WP.seq (WP.block_append (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_))
  refine WP.mono (load_inv hp h₁) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃.toInv) fun s' ⟨hm,hsp,hg⟩ => ⟨hg,hsp.trans h₃.sp,?_⟩
  rw [hm]
  exact BlockMix.post_of fun i hi => h₃.done i hi

theorem correct
    (hd : 16 * VG.Impl.Scrypt.AArch64.Resident.main.aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : BlockMix.Pre s₀) (hs : BlockMix.Stack s₀) :
    WP isa VG.Impl.Scrypt.AArch64.Resident.code s₀ fun s' =>
      GprAbi s₀ s' ∧ Proof.Scrypt.blockMixAArch64.post s₀ s' := by
  have hpi : BlockMix.Pre (BlockMix.inner s₀) := ⟨hp.rd, hp.wr, hp.y_s, hp.b_y, hp.b_s, hp.b_nw, hp.y_nw, hp.s_nw,
    hp.x3, hp.pos⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hd
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.y
    · exact hs.s
  · refine ⟨⟨fun r hr => ?_, rfl⟩, ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : BlockMix.B (BlockMix.inner s₀) = bytesAt s₀.mem (bP s₀) (128 * rr s₀) :=
        bytesAt_congr fun i hi => by
          have hi' : i < 128 * rr s₀ := hi
          exact write_frame_bytes (R := BlockMix.bR s₀) hs.b (by have := r_lt hp; simp only; omega_arith)
            (by simp only; omega_arith)
      show bytesAt s'.mem (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s₀.mem (bP s₀) (128 * rr s₀))
      rw [← e]
      exact hpost


theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixAArch64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.AArch64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixAArch64.post s s' := by
  obtain ⟨t,s',he,h⟩ := correct (by decide +kernel) (BlockMix.pre_of hs).1 (BlockMix.pre_of hs).2
  exact ⟨t,s',he,⟨h.1.1,h.1.2,Exec.preservedV he (by lit_decide)⟩,h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixAArch64.pre
    Proof.Scrypt.blockMixAArch64.pub Impl.Scrypt.AArch64.blockMix := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem blockMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.blockMix (Proof.Scrypt.blockMixContract AArch64.abi
      16) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Proof.Scrypt.blockMixContract, Proof.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Proof.Scrypt.blockMixContract, Proof.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Proof.Scrypt.blockMixContract, Proof.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Proof.Scrypt.blockMixContract, Proof.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixAArch64, AArch64.abi, AArch64.argRegs,
          Proof.Scrypt.AArch64.BlockMix.bmSat]
          [Proof.Scrypt.AArch64.BlockMix.bmSat] using Proof.Scrypt.AArch64.BlockMix.bmSat }

end VG.Proof.Scrypt.AArch64.Resident
