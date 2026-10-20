module

public import VerifiedGarbage.Proof.Cast5.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 ECB on 32-bit x86: verified against the shared contracts

Constant time by the taint analysis: `esp`, the arguments on the stack (the
working space's address among them) and the table's address are public; the
working space's slots then hold public values (pointers, counts).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

/-- The initial taint: `esp`, the 20 bytes of arguments (the fifth, the base
of writable region 1, the working space) and the 4 bytes of stack below `esp`
outside every writable region. -/
def τEcb : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 256], argLen := 24, argBases := [(20, 1)], room := 4 }

theorem τEcb_wf {up : Bool} {s : State} (h : (ecbX up).pre s) : VG.X86.Taint.Wf τEcb s := by
  have hw := h.wrEq
  have dDS : Region.Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩ ⟨(arg s 4).setWidth 64, 256⟩ := by
    rw [Nat.mul_comm]; exact h.dDS
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨h.spfit, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
      and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only [toNat_setWidth]; rw [Nat.mul_comm]; exact h.fitD
    · simp only [toNat_setWidth]; exact h.fitS
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := h.spfit; omega)
        (by rw [Nat.mul_comm]; exact h.dRD) (by rw [Nat.mul_comm]; exact h.dAD)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := h.spfit; omega) h.dRS h.dAS
  · intro p hp
    simp only [τEcb, List.mem_singleton] at hp
    subst hp
    refine ⟨by decide, ?_⟩
    simp only [VG.X86.Taint.region, hw]
    show addr (arg s 4) 0 = _
    rw [addr_off h.fitS 0 (by decide), BitVec.add_zero]
    rfl
  · intro _
    refine ⟨h.sp, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth h.sp).symm
    simp only [τEcb]
    rw [e]
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Nat.mul_comm]; exact h.dD.symm
    · exact h.dS.symm

theorem τEcb_agree {up : Bool} {s₁ s₂ : State} (h₁ : (ecbX up).pre s₁) (h₂ : (ecbX up).pre s₂)
    (hp : (ecbX up).pub s₁ s₂) : VG.X86.Taint.AgreeS [s1234Sym] τEcb s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τEcb_wf h₁, τEcb_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩, fun n hn => ?_⟩
  · simp only [τEcb, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq, args 2 (by decide), args 3 (by decide), args 4 (by decide)]
  · simp only [τEcb] at hk
    rw [show VG.X86.Taint.depth τEcb.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := h₁.spfit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := h₂.spfit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))
  · simp only [List.mem_singleton] at hn
    subst hn
    exact sy

theorem ecbEncrypt_ct : ConstantTime isa (ecbX true).pre (ecbX true).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τEcb (fun _ _ h₁ h₂ hp => τEcb_agree h₁ h₂ hp)
    (by taint_decide)

theorem ecbDecrypt_ct : ConstantTime isa (ecbX false).pre (ecbX false).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τEcb (fun _ _ h₁ h₂ hp => τEcb_agree h₁ h₂ hp)
    (by taint_decide)

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The arguments of the witness at `0x8004`: the schedule at `0x1000`, 16
rounds, one block at `0x2000` and the working space at `0x3000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8010 then 1
  else if a = 0x8015 then 0x30 else 0

/-- The memory of the contracts' witness: the table at `0x100000`, the
arguments elsewhere (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else satArgs a

theorem ecbSatMem_held : ∀ i < s1234.length,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  rw [s1234_length] at hi
  have hm : ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold ecbSatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega)]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi))

/-- A state satisfying the ECB functions' precondition. -/
def ecbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x8004, 20⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

theorem sat_arg (j : Nat) (hj : j < 5) : arg ecbSat j = satArgs.readW (argAddr ecbSat j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change ecbSatMem _ = _
  unfold ecbSatMem
  have : ∀ j < 5, ∀ b < 4, ¬ (argAddr ecbSat j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by decide
  rw [ite_eq_right (this j hj b (by omega))]

theorem ecb_sat (up : Bool) :
    (Spec.Cast5.ecbContract (X86.abi.withConsts ecbConsts) (if up then .encrypt else .decrypt) 4).pre ecbSat := by
  have a0 : arg ecbSat 0 = 0x1000 := (sat_arg 0 (by decide)).trans (by decide)
  have a1 : arg ecbSat 1 = 16 := (sat_arg 1 (by decide)).trans (by decide)
  have a2 : arg ecbSat 2 = 0x2000 := (sat_arg 2 (by decide)).trans (by decide)
  have a3 : arg ecbSat 3 = 1 := (sat_arg 3 (by decide)).trans (by decide)
  have a4 : arg ecbSat 4 = 0x3000 := (sat_arg 4 (by decide)).trans (by decide)
  have held := ecbSatMem_held
  generalize e : ecbSat = s
  sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 256⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl

theorem ecb_implies (up : Bool) :
    (ecbX up).Implies (Spec.Cast5.ecbContract (X86.abi.withConsts ecbConsts) (if up then .encrypt else .decrypt) 4) where
  pre s h := by
    sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length] at h
    obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, htake, hwr, dKD, dKS, dDS, dDA, dSA, -, dRD, dRS, -, dBK, dBD,
      dBS, -, fK, fD, fS, nv⟩ := h
    have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
      simp only [below, Taint.sub_setWidth h4]
    have e8 : 8 * (arg s 3).toNat = (arg s 3).toNat * 8 := Nat.mul_comm _ _
    have hrd : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩, ⟨(s.syms s1234Sym).setWidth 64, 4096⟩] := by
      rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
    have mK : (⟨(arg s 0).setWidth 64, 128⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
    have mA : (⟨argAddr s 0, 20⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have mT : (⟨(s.syms s1234Sym).setWidth 64, 4096⟩ : Region) ∈ s.rd := by
      rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have mD : (⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
    have mS : (⟨(arg s 4).setWidth 64, 256⟩ : Region) ∈ s.wr := by
      rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have dTD := dTw _ mD
    have dTS := dTw _ mS
    rw [← e8] at mD dDS dKD dDA dRD dBD fD dTD
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact hrd
    · exact hwr
    · exact h4
    · exact hsp
    · exact ⟨_, List.mem_append_left _ mA, Region.contains_self _ _⟩
    · exact fS
    · exact fD
    · exact fK
    · exact fitT
    · exact ⟨_, mS, Region.contains_self _ _⟩
    · exact ⟨_, mD, Region.contains_self _ _⟩
    · exact ⟨_, List.mem_append_left _ mK, Region.contains_self _ _⟩
    · exact ⟨_, List.mem_append_left _ mT, Region.contains_self _ _⟩
    · exact fun i hi => held i (by rw [s1234_length] at hi; exact hi)
    · exact dDS
    · exact dKS
    · exact dKD
    · exact dTS
    · exact dTD
    · rw [be]; exact dBS.symm
    · rw [be]; exact dBD.symm
    · rw [be]; exact dBK.symm
    · rw [be]; exact dTB
    · exact dSA.symm
    · exact dDA.symm
    · exact dRS
    · exact dRD
    · exact nv
  post := by
    intro s t _ h
    sig_post [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, ecbConsts_eq, Abi.withConsts]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2, h3, h4⟩ := h
    refine ⟨hsp, fun i hi => ?_, hsy⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  sat := ⟨ecbSat, ecb_sat up⟩

theorem ecbX_correct (up : Bool) (s : State) (hs : (ecbX up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbX up).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct up s hs
  exact ⟨t, s', he, ha, hp⟩

theorem ecbEncrypt_verified :
    Verified X86.target ecbEncrypt (Spec.Cast5.ecbEncryptContract (X86.abi.withConsts ecbConsts) 4) :=
  Verified.of_correct (ecbX_correct true) ecbEncrypt_ct (ecb_implies true)

theorem ecbDecrypt_verified :
    Verified X86.target ecbDecrypt (Spec.Cast5.ecbDecryptContract (X86.abi.withConsts ecbConsts) 4) :=
  Verified.of_correct (ecbX_correct false) ecbDecrypt_ct (ecb_implies false)

end VG.Proof.Cast5.X86
