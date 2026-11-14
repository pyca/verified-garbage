module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Body
public import VerifiedGarbage.Proof.Mont.X86.Rt.ABI
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Time
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified

/-! ### `Mont.X86.Sse2.At`, which only this module used -/

section

/-! ### `Mont.X86.Sse2.AtABI`, which only this module used -/

section

/-! # `vg_rsa_mont_mul_at`'s entry

`AtABI s`: the facts of `mulContract abi 56`'s precondition; from them, the
stack (`Entry`), the layout (`Lay`) and the parameters `atParams` computes
(`atParams_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

structure AtABI (s : State) : Prop where
  stackLo : 56 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 36⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  argScratch : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  stkScratch : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  stkArgs : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  pos : 0 < (arg s 2).toNat
  mo_le : (arg s 3).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  inv_le : (arg s 4).toNat + 4 ≤ 8 * (arg s 1).toNat
  s_le : (arg s 5).toNat + scratchBytes (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  o_le : (arg s 6).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  a_le : (arg s 7).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  b_le : (arg s 8).toNat + 8 * (arg s 2).toNat ≤ 8 * (arg s 1).toNat
  smo : Apart (arg s 3).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sinv : Apart (arg s 4).toNat 4 ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  so : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sa : Apart (arg s 7).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  sb : Apart (arg s 8).toNat (8 * (arg s 2).toNat) ((arg s 5).toNat, scratchBytes (arg s 2).toNat)
  omo : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 3).toNat, 8 * (arg s 2).toNat)
  oinv : Apart (arg s 6).toNat (8 * (arg s 2).toNat) ((arg s 4).toNat, 4)
  inv : (numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat) *
    numAt s.mem (wsOf s) (arg s 4).toNat 4 + 1) % 2 ^ 32 = 0
  bLt : numAt s.mem (wsOf s) (arg s 8).toNat (8 * (arg s 2).toNat) <
    numAt s.mem (wsOf s) (arg s 3).toNat (8 * (arg s 2).toNat)

theorem atAbi_of {s : State} (h : (Proof.Rsa.MontMul.mulContract abi 56).pre s) : AtABI s := by
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem AtABI.ws_toNat {s : State} (_ : AtABI s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem AtABI.ws {s : State} (A : AtABI s) : Ws s (wsOf s) (lenOf s) :=
  ⟨by rw [A.wr]; exact List.mem_singleton_self _, by rw [A.ws_toNat]; exact A.bound⟩

theorem AtABI.entry {s : State} (A : AtABI s) : Entry s (wsOf s) (lenOf s) := by
  have hlo := A.stackLo
  have hhi := A.stackBound
  refine ⟨hlo, by omega_arith, A.ws, fun j hj => ofs_far fun hc => ?_⟩
  have := (s.gpr .esp).isLt
  by_cases h56 : j < 56
  · refine A.stkScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith
  · refine A.retScratch _ ?_ hc
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (56 : BitVec 64).toNat = 56 from rfl]
    omega_arith

/-- The width `N = 2 n` of 32-bit words. -/
abbrev nAt (s : State) : Nat := 2 * (arg s 2).toNat

theorem AtABI.lay {s : State} (A : AtABI s) :
    Lay (lenOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat (arg s 7).toNat
      (arg s 8).toNat := by
  have := A.s_le; have := A.mo_le; have := A.inv_le; have := A.a_le; have := A.b_le; have := A.o_le
  have := A.smo; have := A.sinv; have := A.sa; have := A.sb; have := A.so; have := A.omo; have := A.oinv
  have := A.pos; have := A.bound
  simp only [scratchBytes, Apart] at *
  constructor <;> simp only [nAt, lenOf] <;> omega_arith

/-- The arguments, read from the state after the registers' push. -/
theorem AtABI.readArg {s : State} (A : AtABI s) {t : State} (hesp : t.gpr .esp = s.gpr .esp - 16)
    (hrd : t.rd = s.rd) (hmem : Frame [below (s.gpr .esp) 16] s.mem t.mem) {i : Nat} (hi : i < 9) :
    readSrc t (.mem (atArg i)) = some (arg s i) := by
  have hb := A.stackBound
  have hlo := A.stackLo
  have ea : t.ea (atArg i) = argAddr s i := by
    simp only [State.ea, atArg, at_, hesp, argAddr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (16 : BitVec 32).toNat = 16 from rfl]
    have := (s.gpr .esp).isLt
    omega_arith
  have hin : InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
    rw [hrd, A.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega_arith
  show t.load32 (t.ea (atArg i)) = _
  rw [ea, State.load32, ite_eq_left_iff.mpr fun h => absurd hin h]
  refine congrArg some (Mem.readW_congr fun j hj => hmem _ fun r hr h => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  have := (s.gpr .esp).isLt
  simp only [Region.Contains, argAddr, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat] at h
  omega_arith

theorem upd_trans {t t₁ t₂ : State} {r : Reg} {v₁ v₂ : BitVec 32} (u₁ : Upd t t₁ r v₁) (u₂ : Upd t₁ t₂ r v₂) :
    Upd t t₂ r v₂ :=
  ⟨u₂.gpr, fun q h => (u₂.other q h).trans (u₁.other q h), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.syms.trans u₁.syms⟩

/-- `atPtr r i`: `r = ws + ` the offset in argument `i`. -/
theorem atPtr_ok {s t : State} {r : Reg} (hr : r ≠ .esp) {i : Nat} {is : List Instr} {Q : State → Prop}
    (h0 : readSrc t (.mem (atArg 0)) = some (arg s 0)) (hi : readSrc t (.mem (atArg i)) = some (arg s i))
    (k : ∀ t', Upd t t' r (arg s 0 + arg s i) → WP isa (.block is) t' Q) :
    WP isa (.block (atPtr r i ++ is)) t Q := by
  simp only [atPtr, List.cons_append, List.nil_append]
  refine wp_movS h0 fun t₁ u₁ _ => wp_addS (by rw [Dynamic.readSrc_upd u₁ (Ne.symm hr)]; exact hi)
    fun t₂ u₂ _ => k t₂ ?_
  rw [u₁.gpr] at u₂
  exact upd_trans u₁ u₂

/-- `atParams`: the kernel's parameters from the arguments. -/
theorem atParams_ok {s : State} (A : AtABI s) :
    WP isa (.block atParams) (pushed rs4 s) fun t =>
      PVals (vals t) (wsOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
        (arg s 7).toNat (arg s 8).toNat ∧
      t.gpr .esp = s.gpr .esp - 16 ∧ t.mem = (pushed rs4 s).mem ∧ t.rd = s.rd ∧ t.wr = (pushed rs4 s).wr := by
  have hlo := A.stackLo
  have h16 : 4 * rs4.length ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  have F1 := pushed_frame (rs := rs4) (s := s) (by decide) h16
  rw [show 4 * rs4.length = 16 from rfl] at F1
  have e1 : (pushed rs4 s).gpr .esp = s.gpr .esp - 16 := by rw [pushed_esp]; rfl
  have rd : ∀ t, t.gpr .esp = s.gpr .esp - 16 → t.rd = s.rd → t.mem = (pushed rs4 s).mem →
      ∀ i < 9, readSrc t (.mem (atArg i)) = some (arg s i) := fun t he hr hm i hi =>
    A.readArg he hr (by rw [hm]; exact F1) hi
  let St : State → Prop := fun t => t.gpr .esp = s.gpr .esp - 16 ∧ t.rd = s.rd ∧
    t.mem = (pushed rs4 s).mem ∧ t.wr = (pushed rs4 s).wr
  have st : ∀ {t t' : State} {r : Reg} {v : BitVec 32}, St t → Upd t t' r v → r ≠ .esp → St t' :=
    fun ⟨a, b, c, d⟩ u hr => ⟨by rw [u.other _ (Ne.symm hr), a], by rw [u.rd, b], by rw [u.mem, c], by rw [u.wr, d]⟩
  have S0 : St (pushed rs4 s) := ⟨e1, pushed_rd _ _, rfl, rfl⟩
  have rd' : ∀ {t}, St t → ∀ i < 9, readSrc t (.mem (atArg i)) = some (arg s i) :=
    fun h => rd _ h.1 h.2.1 h.2.2.1
  simp only [atParams, List.append_assoc]
  refine atPtr_ok (by decide) (rd' S0 0 (by decide)) (rd' S0 7 (by decide)) fun t1 u1 => ?_
  have S1 := st S0 u1 (by decide)
  refine atPtr_ok (by decide) (rd' S1 0 (by decide)) (rd' S1 8 (by decide)) fun t2 u2 => ?_
  have S2 := st S1 u2 (by decide)
  refine atPtr_ok (by decide) (rd' S2 0 (by decide)) (rd' S2 3 (by decide)) fun t3 u3 => ?_
  have S3 := st S2 u3 (by decide)
  refine atPtr_ok (by decide) (rd' S3 0 (by decide)) (rd' S3 6 (by decide)) fun t4 u4 => ?_
  have S4 := st S3 u4 (by decide)
  refine atPtr_ok (by decide) (rd' S4 0 (by decide)) (rd' S4 5 (by decide)) fun t5 u5 => ?_
  have S5 := st S4 u5 (by decide)
  refine atPtr_ok (by decide) (rd' S5 0 (by decide)) (rd' S5 4 (by decide)) fun t6 u6 => ?_
  have S6 := st S5 u6 (by decide)
  refine wp_movS (rd' S6 2 (by decide)) fun t7 u7 _ => wp_addS rfl fun t8 u8 _ => wp_addS rfl fun t9 u9 _ =>
    wp_addS rfl fun t10 u10 _ => WP.block_nil ?_
  have S10 := st (st (st (st S6 u7 (by decide)) u8 (by decide)) u9 (by decide)) u10 (by decide)
  have g : ∀ r, r ≠ .eax → t10.gpr r = t6.gpr r := fun r h => by
    rw [u10.other _ h, u9.other _ h, u8.other _ h, u7.other _ h]
  have hW := A.ws_toNat
  have hn8 : 8 * (arg s 2).toNat < 2 ^ 32 := by
    have := A.s_le; have := A.bound; simp only [scratchBytes, lenOf] at *; omega_arith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, S10.1, S10.2.2.1, S10.2.1, S10.2.2.2⟩
  · show (t10.gpr .ebp).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .edi).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .esi).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr,
      BitVec.toNat_add, hW]
  · show (t10.gpr .edx).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .ecx).toNat = _
    rw [g _ (by decide), u6.other _ (by decide), u5.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .ebx).toNat = _
    rw [g _ (by decide), u6.gpr, BitVec.toNat_add, hW]
  · show (t10.gpr .eax).toNat = _
    rw [u10.gpr, u9.gpr, u8.gpr, u7.gpr]
    simp only [BitVec.toNat_add]
    have := (arg s 2).isLt
    simp only [nAt]
    omega_arith

end VG.Proof.Mont.X86.Sse2

end

end


/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: correctness

`at_correct`: from `mulContract abi 56`'s precondition, `atBody` terminates
with the callee-saved registers and the return address as they were and the
contract's postcondition.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

theorem read_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_val32' (m : Mem) (ws : Addr) (d n : Nat) : numAt m ws d (8 * n) = val32 m ws d (2 * n) := by
  unfold numAt
  rw [show 8 * n = 4 * (2 * n) by omega_using []]
  exact read_val32 m ws (2 * n) d

theorem numAt_w32' (m : Mem) (ws : Addr) (d : Nat) : numAt m ws d 4 = w32 m ws d := by
  unfold numAt
  rw [show 4 = 4 * 1 from rfl, read_val32 m ws 1 d]
  simp [val32]

theorem atBody_noSp : NoSp (seqs [.block atParams, withParams, .block restoreRegs]) :=
  NoSp.of_all (by decide +kernel)

/-- What `body atParams` takes of a state meeting the contract's precondition. -/
theorem atReady {s : State} (A : AtABI s) :
    Ready atParams (wsOf s) (lenOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
      (arg s 7).toNat (arg s 8).toNat s := by
  have Ly := A.lay
  have hinv := A.inv
  have hb := A.bLt
  rw [numAt_val32', numAt_w32'] at hinv
  rw [numAt_val32', numAt_val32'] at hb
  exact ⟨A.entry, Ly, atParams_ok A, VG.Proof.Mont.X86.Square.low_inverse s.mem (wsOf s) _ _ Ly.hN hinv, hb⟩

theorem at_correct (s : State) (h : (Proof.Rsa.MontMul.mulContract abi 56).pre s) :
    ∃ tr t, Exec isa atBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.MontMul.mulContract abi 56).post s t := by
  have A := atAbi_of h
  have R := atReady A
  obtain ⟨tr, t, E, lt, cong, mem, cs, -, -⟩ := body_ok R.entry R.ly atBody_noSp R.par R.inv R.bLt
  have hso := A.so
  have hol := A.o_le
  have hscr := A.s_le
  have hst := A.stackBound
  simp only [Apart, scratchBytes] at hso hscr
  refine ⟨tr, t, E, ⟨cs, ?_⟩, ?_⟩
  · refine Mem.readW_congr fun i hi => mem _ (fun r hr => ?_) (fun hc => ?_)
    · have := ofs_far (base := wsOf s) (size := lenOf s) (x := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i)
        fun hc => A.retScratch _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [nAt, lenOf] at this ⊢ <;> omega_arith
    · have := (s.gpr .esp).isLt
      simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        at hc
      omega_using [hi, hc]
  · sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [numAt_val32', numAt_val32']; exact lt
    · rw [numAt_val32', numAt_val32', numAt_val32', numAt_val32',
        show 64 * (arg s 2).toNat = 32 * nAt s by simp only [nAt]; omega_using []]
      exact cong
    · intro i hi hj
      have hb := A.bound
      apply mem _ (fun r hr => ?_) (fun hc => ?_)
      · rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
          simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, scratchBytes] at this
        rcases hr with rfl | rfl <;> simp only [nAt] <;> omega_using [this]
      · have := (s.gpr .esp).isLt
        have := (arg s 0).isLt
        have := A.stackLo
        refine A.stkScratch (wsOf s + BitVec.ofNat 64 i) ?_ ?_
        · simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            at hc ⊢
          omega_using [this, hc]
        · simp only [Region.Contains, lenOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat]
          omega_using [hi]

end VG.Proof.Mont.X86.Sse2

end

end


/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: verified

Two runs from states with the same public arguments compute the same
numbers (`atReady`), so `body_relCT` makes them leak the same; the witness of
the scalar function's precondition, whose stack is far from its working
space, meets this one's too.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)

theorem at_publicArgs {s t : State} (H : (Proof.Rsa.MontMul.mulContract abi 56).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 9, arg s i = arg t i := by
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption
  | 5, _ => with_reducible assumption
  | 6, _ => with_reducible assumption
  | 7, _ => with_reducible assumption
  | 8, _ => with_reducible assumption

theorem at_constantTime :
    ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 56).pre (Proof.Rsa.MontMul.mulContract abi 56).pub atBody := by
  apply RelCT.constantTime
  refine RelCT.mono (P := fun s₁ s₂ => ∃ W L N S mo inv o a b, BPair atParams W L N S mo inv o a b s₁ s₂)
    (RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => body_relCT (fun _ _ h => h) (atParams_relCT.mono (fun _ _ ⟨_, _, B, ex, ey⟩ => by
        rw [ex, ey, pushed_esp, pushed_esp, B.2.2]) fun _ _ _ => trivial)) ?_ fun _ _ _ => trivial
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨sp, args⟩ := at_publicArgs hp
  have R := atReady (atAbi_of h₂)
  simp only [wsOf, lenOf, nAt, ← args 0 (by decide), ← args 1 (by decide), ← args 2 (by decide),
    ← args 3 (by decide), ← args 4 (by decide), ← args 5 (by decide), ← args 6 (by decide),
    ← args 7 (by decide), ← args 8 (by decide)] at R
  exact ⟨_, _, _, _, _, _, _, _, _, atReady (atAbi_of h₁), R, sp⟩

end VG.Proof.Mont.X86.Sse2
