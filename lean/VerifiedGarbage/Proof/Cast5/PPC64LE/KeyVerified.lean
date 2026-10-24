module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Key
public import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Key
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5 key expansion on PPC64LE: verified

Constant time by the taint analysis: `r3`–`r6` (the pointers and the key's
length) and the table's address are public; the step and half counts, the
copy's pointers and the schedule's pointer are computed from them.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s5678Sym s5678 keyConsts)

/-- Key expansion's contract on PPC64LE, as its proof states it. -/
def keyP : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sch : Region := ⟨s.gpr .r5, 128⟩
    let scr : Region := ⟨s.gpr .r6, 256⟩
    s.rd = [key] ∧ s.wr = [sch, scr] ∧ key.Disjoint sch ∧ key.Disjoint scr ∧ sch.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 256 ≤ 2 ^ 64 ∧ Spec.Cast5.validKey (s.gpr .r4).toNat
  post s s' :=
    Spec.Cast5.scheduleAt s'.mem (s.gpr .r5) =
      Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- Key expansion's contract with the table, as the proof states it. -/
def keyPC : Contract isa where
  pre s := keyP.pre (stripConsts keyConsts s) ∧ ConstsOk keyConsts 0 s
  post := keyP.post
  pub s₁ s₂ := keyP.pub s₁ s₂ ∧ s₁.syms s5678Sym = s₂.syms s5678Sym

/-- The registers key expansion writes. -/
def keyRegs : List Reg := [.r0, .r3, .r4, .r5, .r7, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
  .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30]

theorem s5678_len' : 8 * s5678.length = 4096 := s5678_len

theorem key_ok (hw : writesOnly keyRegs expandKey = true) (hn : expandKey.noCalls = true)
    (s : State) (hs : keyPC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyPC.post s s' := by
  obtain ⟨⟨hrd, hwr, _, dkS, dKS, hkf, hKf, hcf, hn'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dkS dKS hkf hKf hcf hn'
  have trd : (⟨s.syms s5678Sym, 4096⟩ : Region) ∈ s.rd := s5678_len' ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s5678Sym, 4096⟩ r := s5678_len' ▸ ConstsOk.wr1 hk
  have pre : KeyPre s :=
    { key := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
      kfit := hkf
      sch := by rw [hwr]; simp
      Kfit := hKf
      scr := by rw [hwr]; simp
      sfit := hcf
      keyScr := dkS
      schScr := dKS
      valid := hn'
      trd := List.mem_append_left _ trd
      held := ConstsOk.held1 hk
      tblSch := twr _ (by rw [hwr]; simp)
      tblScr := twr _ (by rw [hwr]; simp) }
  obtain ⟨t, s', he, hp, hk'⟩ := WP.keep keyRegs (key_wp pre) hw hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hp.lr⟩, hp.sched⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk'.gpr (by decide)

theorem key_agree : ∀ s₁ s₂, keyPC.pre s₁ → keyPC.pre s₂ → keyPC.pub s₁ s₂ →
    (taintSym [s5678Sym]).Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  intro s₁ s₂ _ _ ⟨h, hsy⟩
  refine ⟨⟨h.2.2.2.2, fun r hr => ?_⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem expandKey_ct : ConstantTime isa keyPC.pre keyPC.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [s5678Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6]) key_agree
    (by taint_decide)

/-- A state satisfying the precondition without the table: a key of five bytes. -/
def keySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 5 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 5⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 256⟩]

theorem key_implies : keyP.Implies (Spec.Cast5.expandKeyContract abi) := by
  sig_implies [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre,
    Spec.Cast5.expandKeyPost, abi, argRegs, keyP, Spec.Cast5.validKey] [keySat] using keySat

theorem keyConsts_eq : keyConsts = [(s5678Sym, s5678)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 s5678

theorem keySatMem_held : ∀ i < s5678.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s5678.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [Impl.Cast5.s5678, table_length]; decide)

/-- A state satisfying the precondition with the table. -/
def keySatC : State :=
  { keySat with mem := keySatMem, rd := [⟨0x1000, 5⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem key_sat : (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)).pre keySatC := by
  have hl : s5678.length = 512 := by rw [Impl.Cast5.s5678, table_length]
  have held := keySatMem_held
  rw [keyConsts_eq]
  generalize s5678 = W at hl held ⊢
  generalize e : keySatC = s
  sig_pre [Spec.Cast5.expandKeyContract, Spec.Cast5.expandKeySig, Spec.Cast5.expandKeyPre, abi, argRegs,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, Spec.Cast5.validKey]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x2000, 128⟩, ⟨0x3000, 256⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem keyPC_implies : keyPC.Implies (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts keyConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts keyConsts s₁) (stripConsts keyConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := ⟨keySatC, key_sat⟩

theorem expandKey_verified :
    Verified target expandKey (Spec.Cast5.expandKeyContract (abi.withConsts keyConsts)) :=
  Verified.of_correct (key_ok (by lit_decide) (by lit_decide)) expandKey_ct keyPC_implies

end VG.Proof.Cast5.PPC64LE
