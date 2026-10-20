module

public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Remainder
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Four-word rows retain the existing scalar multiply-add contract. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (mask16 ofNat_beq_zero)

private theorem rowPrefix_count (s : State) :
    WP isa (.block (rowSplit ++ rowParity)) s fun t =>
      t.gpr .lr = s.gpr .lr ∧ t.z = decide ((s.gpr .lr).toNat % 2 = 0) := by
  have mask : (s.gpr .lr &&& 1 == 0) = decide ((s.gpr .lr).toNat % 2 = 0) := by
    have bits := ofNat_and_one (s.gpr .lr).isLt
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at bits
    rw [bits, ofNat_beq_zero (by omega)]
  apply WP.block_append_iff.mpr
  refine WP.mono (rowSplit_ok s) ?_
  rintro u ⟨_,_,_,_,rest⟩
  apply WP.of_runBlock
  simp only [rowParity,runBlock_cons,isa,exec,Op2.eval]
  refine ⟨_,rfl,?_⟩
  simp only [subFlags,gpr_setReg,reduceCtorEq,↓reduceIte,sub_zero32]
  have count := rest.gpr .lr (by simp)
  rw [count]
  exact ⟨rfl,mask⟩

private theorem rowBody_count {s t : State} {tr : List Leak}
    (run : Exec isa rowBody s tr t) : t.gpr .lr = s.gpr .lr - 1 := by
  obtain ⟨u,tr1,tr2,first,last,_⟩ := seq_inv run
  have kept : u.gpr .lr = s.gpr .lr := VG.Arm.Exec.gpr (by intro i hi; revert i hi; decide) first
  obtain ⟨_,v,advance,_,_,count,_⟩ := rowAdvance_ok u
  rw [(Exec.det advance last).2] at count
  exact count.trans (congrArg (fun x : BitVec 32 => x-1) kept)

private theorem rowBody_count_nat {s t : State} {tr : List Leak}
    (run : Exec isa rowBody s tr t) (positive : 0 < (s.gpr .lr).toNat) :
    (t.gpr .lr).toNat = (s.gpr .lr).toNat - 1 := by
  rw [rowBody_count run,BitVec.toNat_sub]
  have := (s.gpr .lr).isLt
  change (2^32-1+(s.gpr .lr).toNat)%2^32 = _
  omega

private theorem rowOdd_even {s t : State} {tr : List Leak}
    (parity : s.z = decide ((s.gpr .lr).toNat % 2 = 0))
    (run : Exec isa (.ite .ne rowBody (.block [])) s tr t) :
    (t.gpr .lr).toNat % 2 = 0 := by
  cases run with
  | iteT condition body =>
    have odd : (s.gpr .lr).toNat % 2 ≠ 0 := by
      change some (!s.z) = some true at condition
      rw [parity] at condition
      simpa only [Bool.not_eq_true',decide_eq_false_iff_not,Option.some.injEq] using condition
    have value := rowBody_count_nat body (by omega)
    omega
  | iteF condition empty =>
    have even : (s.gpr .lr).toNat % 2 = 0 := by
      change some (!s.z) = some false at condition
      rw [parity] at condition
      simpa only [Bool.not_eq_false',decide_eq_true_eq,Option.some.injEq] using condition
    have trivialExec : Exec isa (.block []) s [] s := Exec.block_iff.mpr rfl
    have eq := (Exec.det trivialExec empty).2
    rw [←eq]
    exact even

private theorem cmpCount_post {s t : State} {tr : List Leak}
    (run : Exec isa (.block [.cmp .lr (.imm 0)]) s tr t) :
    t.gpr .lr = s.gpr .lr ∧ t.z = (t.gpr .lr == 0) := by
  have same : Exec isa (.block [.cmp .lr (.imm 0)]) s [] (subFlags s (s.gpr .lr) 0) := by
    apply Exec.block_iff.mpr
    simp only [execBlock,isa,exec,Op2.eval,Option.map_some,addrs,List.map_nil,List.append_nil]
    rfl
  obtain ⟨rfl,rfl⟩ := Exec.det same run
  exact ⟨rfl,by simp only [subFlags,sub_zero32]⟩

/-- The changed loop removes public branches but retains the complete final state. -/
theorem rowU_refine {s t : State} {tr : List Leak} (run : Exec isa rowU s tr t) :
    ∃ trace, Exec isa rowU4 s trace t := by
  unfold rowU at run
  obtain ⟨s1,tr1,tail1,first,h1,rfl⟩ := seq_inv run
  obtain ⟨s2,tr2,tail2,odd,h2,rfl⟩ := seq_inv h1
  obtain ⟨s3,tr3,tail3,cmp,h3,rfl⟩ := seq_inv h2
  obtain ⟨s4,tr4,tr5,loop,last,rfl⟩ := seq_inv h3
  obtain ⟨_,_,entry,entryCount,entryParity⟩ := rowPrefix_count s
  have state := (Exec.det entry first).2
  rw [state] at entryCount entryParity
  have even2 : (s2.gpr .lr).toNat % 2 = 0 := rowOdd_even (by rw [entryCount]; exact entryParity) odd
  obtain ⟨count3,zero3⟩ := cmpCount_post cmp
  have even3 : (s3.gpr .lr).toNat % 2 = 0 := by rw [count3]; exact even2
  have changed : ∃ trace, Exec isa (.ite .ne rowLoopU4 (.block [])) s3 trace s4 := by
    cases loop with
    | iteT condition body =>
      have nonzero : s3.gpr .lr ≠ 0 := by
        intro zero
        change some (!s3.z) = some true at condition
        rw [zero3,zero] at condition
        contradiction
      have positive : 0 < (s3.gpr .lr).toNat := by
        have value : (s3.gpr .lr).toNat ≠ 0 := by
          intro zero
          exact nonzero (BitVec.eq_of_toNat_eq zero)
        omega
      obtain ⟨newTrace,newRun⟩ := rowLoopU_refine positive even3 body
      exact ⟨_,.iteT condition newRun⟩
    | iteF condition empty => exact ⟨_,.iteF condition empty⟩
  obtain ⟨newTrace,newRun⟩ := changed
  exact ⟨_,.seq first (.seq odd (.seq cmp (.seq newRun last)))⟩

/-- The four-word UMAAL row has exactly the existing row_ok arithmetic contract. -/
theorem row4_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa rowU4 s (RowInv s base o b n n) := by
  obtain ⟨trace,t,run,post⟩ := row_ok s ctx hn hp0 hp12 hcount
  obtain ⟨newTrace,newRun⟩ := rowU_refine (row_sim run)
  exact ⟨newTrace,t,newRun,post⟩

end VG.Proof.Bignum.Arm
