module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the front

`fnContract`: `vg_rsa_private_precompute(pre = a0, pre_len = a1, n = a2,
n_len = a3, p = a4, p_len = a5, q = a6, q_len = a7, scratch, scratch_len)`,
the last two on the stack, on the registers and the stack. `save_ok`: the
working space's address from the stack, and `vg_rsa_private_crt`'s registers
saved in its header (`Crt.Saved`); `args_ok`: the arguments in the header.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64 (Scr add_ofNat_zero)
open VG.Proof.Bignum.RISCV64.Crt (savW savR save_step SI Saved saved_ne_t0 hdr_rw out_wr)

/-- `pre`, `pre_len` words at `a0`. -/
abbrev preR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩
/-- `n`, `n_len` bytes at `a2`. -/
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
/-- `p`, `p_len` bytes at `a4`. -/
abbrev pR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
/-- `q`, `q_len` bytes at `a6`. -/
abbrev qR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
/-- The working space, `scratch_len` words. -/
abbrev scrR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
/-- The arguments on the stack. -/
abbrev argsR (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The bytes of `n`, `p` and `q`. -/
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat
abbrev pB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat
abbrev qB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat

/-- `vg_rsa_private_precompute`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [nR s, pR s, qR s, argsR s] ∧ s.wr = [preR s, scrR s] ∧
      (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (pR s) ∧ (preR s).Disjoint (qR s) ∧
      (preR s).Disjoint (scrR s) ∧ (preR s).Disjoint (argsR s) ∧
      (nR s).Disjoint (scrR s) ∧ (pR s).Disjoint (scrR s) ∧ (qR s).Disjoint (scrR s) ∧
      (scrR s).Disjoint (argsR s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a3).toNat ∧ 1 ≤ (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat < (s.gpr .a3).toNat ∧
      1 ≤ (s.gpr .a7).toNat ∧ (s.gpr .a7).toNat < (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .a3).toNat (s.gpr .a5).toNat
        (s.gpr .a7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a3).toNat ≤ (stackArg s 1).toNat ∧
      (s.gpr .a0).toNat % 8 = 0 ∧ (stackArg s 0).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s s' :=
    match Spec.Rsa.privatePrecompute (nB s) (pB s) (qB s) with
    | some ws => (s'.gpr .a0).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .a0) (s.gpr .a1).toNat = ws
    | none => (s'.gpr .a0).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .a0) (s.gpr .a1).toNat = List.replicate (s.gpr .a1).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 2).map (stackArg s₁) = (List.range 2).map (stackArg s₂) ∧ nB s₁ = nB s₂

/-- The working space. -/
abbrev cS (s : State) : Addr := stackArg s 0
/-- Its size in bytes. -/
abbrev cZ (s : State) : Nat := (stackArg s 1).toNat * 8
/-- `k`. -/
abbrev ck (s : State) : Nat := (s.gpr .a3).toNat
/-- `n`'s words. -/
abbrev cw (s : State) : Nat := (ck s + 7) / 8

/-- `save`, the working space `S` the first stack argument, readable and
aligned (as the stack pointer is), and its header's words 14–26 writable and
aligned: `Crt.save_ok`'s, from the first stack argument. -/
theorem save_ok (s₀ : State) {S : Addr} (hS : stackArg s₀ 0 = S)
    (hst : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 8) (hsp : s₀.sp.toNat % 8 = 0)
    (hin : ∀ i < 13, InRegions s₀.wr (Mont.off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (Mont.off (savW S) (8 * i)).toNat % 8 = 0) :
    WP isa (.block PrivPre.save) s₀ (Saved s₀ S) := by
  rw [PrivPre.save, List.append_assoc]
  have hst' : InRegions (s₀.rd ++ s₀.wr) s₀.sp 8 := by
    simpa only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd, add_ofNat_zero] using hst
  have hv : s₀.mem.readW s₀.sp 64 = S := by
    rw [← hS]; show s₀.mem.readW s₀.sp 64 = s₀.mem.readW (stackArgAddr s₀ 0) 64
    simp only [stackArgAddr, Nat.reduceMul, add_ofNat_zero]
  have first : WP isa (.block [.addSp .t0 0, .load .d .t0 .t0 0]) s₀ fun s₁ => s₁ = s₀.write .t0 S := by
    brun [exec_addSp (show 0 < 2048 by decide), add_ofNat_zero, hst', hsp, hv, write_write]
  refine WP.block_append (WP.mono first ?_)
  · rintro s₁ rfl
    have h0 : (s₀.write .t0 S).gpr .t0 = S := gpr_write_self _ _ _
    refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI (s₀.write .t0 S))
      (fun k s hk h => save_step (s₀.write .t0 S) (by rw [h0]; exact hin) (by rw [h0]; exact hal) hk h)
      13 (Nat.le_refl _) (s₀.write .t0 S)
      ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
    have hf := h.frame
    have hsv := h.saved
    rw [h0] at hf hsv
    have hw : s.gpr .t0 = S := by rw [h.gpr, h0]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
      BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
    have k1 : Keep [.t0] s₀ (s₀.write .t0 S) := Keep.write _ _ _
    refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, gpr_write_self _ _ _, ?_, hf, fun i hi => ?_⟩
    · have hr6 : r ≠ .s6 := fun e => hr (by simp [e])
      have hr0 : r ∉ [Reg.t0] := fun e => hr (by simp_all)
      rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e hr6, h.gpr, k1.gpr hr0]
    · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (by decide), hw]
    · rw [mem_write, hsv i hi, gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_ne_t0 i hi)]

/-- The header after `args`. -/
structure ArgsP (m : Mem) (S : Addr) (s : State) : Prop where
  out : Mont.word m S oOut = s.gpr .a0
  n : Mont.word m S oN = s.gpr .a2
  nLen : Mont.word m S oNLen = s.gpr .a3
  inp : Mont.word m S oIn = s.gpr .a0
  p : Mont.word m S oP = s.gpr .a4
  pLen : Mont.word m S oPLen = s.gpr .a5
  q : Mont.word m S oQ = s.gpr .a6
  qLen : Mont.word m S oQLen = s.gpr .a7
  qinv : Mont.word m S oQInv = s.gpr .a0

/-- `args`: the arguments into the header, the working space at `s6`
(writable, aligned). -/
theorem args_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 88 ≤ Z)
    (h6 : s.gpr .s6 = Mont.off S 0) :
    WP isa (.block PrivPre.args) s fun t =>
      (ArgsP t.mem S s ∧ Mont.Outside S 0 88 s.mem t.mem) ∧ Keep [] s t := by
  have hnw := hs.nowrap
  have st : ∀ d, d + 8 ≤ 88 → d % 8 = 0 → InRegions s.wr (Mont.off S d) 8 ∧ (Mont.off S d).toNat % 8 = 0 :=
    fun d h1 h2 => ⟨hs.st (by omega_arith), hs.al8 (by omega_arith) h2⟩
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold PrivPre.args
  brun [h6, oOut, oN, oNLen, oIn, oP, oPLen, oQ, oQLen, oQInv,
    (st 0 (by decide) (by decide)).1, (st 0 (by decide) (by decide)).2,
    (st 8 (by decide) (by decide)).1, (st 8 (by decide) (by decide)).2,
    (st 16 (by decide) (by decide)).1, (st 16 (by decide) (by decide)).2,
    (st 24 (by decide) (by decide)).1, (st 24 (by decide) (by decide)).2,
    (st 32 (by decide) (by decide)).1, (st 32 (by decide) (by decide)).2,
    (st 40 (by decide) (by decide)).1, (st 40 (by decide) (by decide)).2,
    (st 48 (by decide) (by decide)).1, (st 48 (by decide) (by decide)).2,
    (st 56 (by decide) (by decide)).1, (st 56 (by decide) (by decide)).2,
    (st 80 (by decide) (by decide)).1, (st 80 (by decide) (by decide)).2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals (try simp (disch := omega_arith) only [Mont.word, oOut, oN, oNLen, oIn, oP, oPLen, oQ, oQLen,
    oQInv, hdr_rw, Mem.readW_writeW_self64])
  iterate 9 refine out_wr S ?_ (by decide) _
  exact Mont.Outside.refl _ _ _ _

end VG.Proof.Bignum.RISCV64.PrivPre
