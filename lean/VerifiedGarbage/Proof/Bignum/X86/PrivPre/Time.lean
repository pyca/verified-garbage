module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
meta import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Fn
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.CrtResources

/-! # The factors' values of an RSA private key on x86: constant time

`primesBody` is checked whole by the SIMD taint analysis from `τA`
(`body_check`), on runs narrowed to the output and the working space as
`CrtRt.sized`'s (`body_relCT`); the entry and the return are private CRT's
(`Crt.entry_relCT`, `Crt.restore_relCT`): `primes` is constant time
(`constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.PublicRt (Both setWidth_toNat relCT_narrow)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Dsa.X86 (wp_result)
open VG.Impl.Bignum.X86.PrivPre (primes primesBody)

theorem body_check : XCheck primesBody := by dsimp only [XCheck]; taint_decide

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {s : State}

theorem side_in (S : Side base bytes len args sp s) :
    RIn base bytes len args (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨h, _, _, _⟩ := S
  have x := h.extra
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.room, h.top, h.need,
    h.hbase, h.hbytes, ⟨x.space, x.nLen, x.inLen, x.pShort, x.qShort, x.dpLen, x.dqLen, x.qiLen, x.outFit,
    ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, x.outApart, x.positive, x.bounded, x.fits,
    fun i hi => ?_, x.apart⟩⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := x.readable i hi
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem side_run (S : Side base bytes len args sp s) :
    Run (CrtExtra base bytes len args) base bytes len args sp
      (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  refine ⟨side_in S, ⟨S.1.top, fun r hr => ?_⟩, S.2.1⟩
  simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact S.2.2.1
  · exact S.2.2.2

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (Both (Side base bytes len args sp)) primesBody fun _ _ => True := by
  refine relCT_narrow (Pn := Both (Run (CrtExtra base bytes len args) base bytes len args sp))
    (fun s => s.rd ++ s.wr) (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_)
    (RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.agree h.2) body_check)
  have cov : ∀ {s : State}, Side base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.crt.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, Side base bytes len args sp s →
      ∃ F, WP isa primesBody (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F :=
    fun S => ⟨_, primesBody_ok (side_in S)⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    side_run S₁, side_run S₂⟩

end

theorem primes_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 18, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa primes s tr sf) (F : Exec isa primes t ur tf) : tr = ur := by
  have A0 := args 0 (by decide)
  have A1 := args 1 (by decide)
  have A3 := args 3 (by decide)
  have A8 := args 16 (by decide)
  have A9 := args 17 (by decide)
  have hb : (arg s 16).toNat = (argumentPointer s 16).toNat := (setWidth_toNat _).symm
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (Crt.entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 16 < 18)).readSrc,
          (B.abi.stackArgument (by decide : 16 < 18)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, _⟩ := wp_result (Crt.installed_ok A.abi) E1
      obtain ⟨It, _, Kt, _⟩ := wp_result (Crt.installed_ok B.abi) F1
      have Iv : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have need := need_le A.abi.lengths.1 A.abi.scratchLength
      have espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      have espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      have Su : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨In.ofInputs Is need hb rfl, espu, ?_, ?_⟩
        · rw [espu, ← A.abi.outLength]; exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      have Sv : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨In.ofInputs Iv need hb rfl, espv, ?_, ?_⟩
        · rw [espv]
          have D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          rw [← A.abi.outLength]; exact D
        · rw [espv]
          have D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv⟩ E2 F2).1
          obtain ⟨-, -, -, -, Ksu⟩ := wp_result (primesBody_ok Su.1) E2
          obtain ⟨-, -, -, -, Ktv⟩ := wp_result (primesBody_ok Sv.1) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.pair Sv).agree.rf.1 _ (by decide))
          have T3 := (Crt.restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem constantTime : ConstantTime isa primesContract.pre primesContract.pub primes := by
  intro s t tr ur sf tf S T H E F
  have Args := Crt.arguments H
  exact primes_trace (topABI_of S) (topABI_of T) Args.2 Args.1 E F

end VG.Proof.Bignum.X86.PrivPre
