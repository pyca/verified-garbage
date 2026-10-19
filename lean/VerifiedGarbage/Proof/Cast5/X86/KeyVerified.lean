module

public import VerifiedGarbage.Proof.Cast5.X86.Key
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.X86.Key
import VerifiedGarbage.Proof.Cast5.X86.KeyGroup
meta import VerifiedGarbage.Proof.Cast5.X86.KeyGroup
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword

/-!
# CAST5 key expansion on 32-bit x86: verified against the shared contract

Constant time by the taint analysis: `esp`, the arguments on the stack (the
working space's address among them) and the table's address are public; the
key's length decides the number of bytes copied.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- The initial taint: `esp`, the 16 bytes of arguments (the fourth, the base
of writable region 1, the working space) and the 4 bytes of stack below `esp`
outside every writable region. -/
def τKey : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 256], argLen := 20, argBases := [(16, 1)], room := 4 }

theorem τKey_wf {s : State} (h : keyX.pre s) : VG.X86.Taint.Wf τKey s := by
  have hw := h.wrEq
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨h.spfit, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
      and_true]
    exact ⟨h.dKS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitK
    · simp only [toNat_setWidth]; exact h.fitS
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega) h.dRK h.dAK
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := h.spfit; omega) h.dRS h.dAS
  · intro p hp
    simp only [τKey, List.mem_singleton] at hp
    subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.X86.Taint.region, hw]
    show addr (arg s 3) 0 = _
    rw [addr_off h.fitS 0 (by decide), BitVec.add_zero]
    rfl
  · intro _
    refine ⟨h.sp, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth h.sp).symm
    simp only [τKey]
    rw [e]
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dK.symm
    · exact h.dS.symm

theorem τKey_agree {s₁ s₂ : State} (h₁ : keyX.pre s₁) (h₂ : keyX.pre s₂) (hp : keyX.pub s₁ s₂) :
    VG.X86.Taint.AgreeS [s5678Sym] τKey s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τKey_wf h₁, τKey_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩, fun n hn => ?_⟩
  · simp only [τKey, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq, args 2 (by decide), args 3 (by decide)]
  · simp only [τKey] at hk
    rw [show VG.X86.Taint.depth τKey.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.spfit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.spfit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))
  · simp only [List.mem_singleton] at hn
    subst hn
    exact sy

theorem expandKey_ct : ConstantTime isa keyX.pre keyX.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) τKey (fun _ _ h₁ h₂ hp => τKey_agree h₁ h₂ hp)
    (by taint_decide)

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl

theorem key_implies_pre (s : State)
    (h : (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4).pre s) : keyX.pre s := by
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s5678_length] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, htake, hwr, dkK, dkS, dKS, dKA, dSA, -, dRK, dRS, -, -, dBK,
    dBS, -, fk, fK, fS, hv⟩ := h
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, Taint.sub_setWidth h4]
  have hrd : s.rd = [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩,
      ⟨(s.syms s5678Sym).setWidth 64, 4096⟩] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have mK : (⟨(arg s 2).setWidth 64, 128⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mS : (⟨(arg s 3).setWidth 64, 256⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrd
  · exact hwr
  · exact h4
  · exact hsp
  · exact fk
  · exact fK
  · exact fS
  · exact fitT
  · exact fun i hi => held i (by rw [s5678_length] at hi; exact hi)
  · exact dkK
  · exact dkS
  · exact dKS
  · exact dTw _ mK
  · exact dTw _ mS
  · exact dKA.symm
  · exact dSA.symm
  · exact dRK
  · exact dRS
  · rw [be]; exact dBK.symm
  · rw [be]; exact dBS.symm
  · rw [be]; exact dTB
  · exact hv

/-- The arguments of the witness at `0x8004`: a key of 16 bytes at `0x1000`,
the schedule at `0x2000` and the working space at `0x3000`. -/
def keyArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30
  else 0

/-- The memory of the contract's witness: the table at `0x100000`, the
arguments elsewhere (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def keySatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s5678 a else keyArgs a

theorem keySatMem_held : ∀ i < s5678.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  intro i hi
  rw [s5678_length] at hi
  have hm : keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s5678).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold keySatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega)]
  exact hm.trans (constMem_held 0x100000 s5678 (by rw [s5678_length]; decide) i (by rw [s5678_length]; exact hi))

/-- A state satisfying key expansion's precondition. -/
def keySat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := keySatMem
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

theorem keySat_arg (j : Nat) (hj : j < 4) : arg keySat j = keyArgs.readW (argAddr keySat j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change keySatMem _ = _
  unfold keySatMem
  have : ∀ j < 4, ∀ b < 4, ¬ (argAddr keySat j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by decide
  rw [ite_eq_right (this j hj b (by omega))]

theorem key_sat : (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4).pre keySat := by
  have a0 : arg keySat 0 = 0x1000 := (keySat_arg 0 (by decide)).trans (by decide)
  have a1 : arg keySat 1 = 16 := (keySat_arg 1 (by decide)).trans (by decide)
  have a2 : arg keySat 2 = 0x2000 := (keySat_arg 2 (by decide)).trans (by decide)
  have a3 : arg keySat 3 = 0x3000 := (keySat_arg 3 (by decide)).trans (by decide)
  have held := keySatMem_held
  generalize e : keySat = s
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s5678_length]
  subst s
  rw [a0, a1, a2, a3]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s5678_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem key_implies : keyX.Implies (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4) where
  pre := key_implies_pre
  post := by
    intro s t _ h
    sig_post [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, keyConsts_eq, Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, keyConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun i hi => ?_, hsy⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  sat := ⟨keySat, key_sat⟩

theorem keyX_correct (s : State) (hs : keyX.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyX.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_correct s hs
  exact ⟨t, s', he, ha, hp⟩

theorem expandKey_verified :
    Verified X86.target expandKey (Spec.Cast5.expandKeyContract (X86.abi.withConsts keyConsts) 4) :=
  Verified.of_correct keyX_correct expandKey_ct key_implies

end VG.Proof.Cast5.X86
