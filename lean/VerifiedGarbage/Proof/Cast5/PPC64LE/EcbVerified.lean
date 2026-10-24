module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Cast5.Contract
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# CAST5 ECB on PPC64LE: verified

Constant time by the taint analysis: `r3`–`r7` and the table's address are
public (`taintSym`). The proof's contract (`ecbPC`) is `ecbP` for the state
without the table's region, with what the contract says of the table
(`ConstsOk`).
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

def dir (up : Bool) : Spec.Cast5.Direction := if up then .encrypt else .decrypt

/-- The ECB functions' contract on PPC64LE, as their proof states it. -/
def ecbP (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨s.gpr .r3, 128⟩
    let dat : Region := ⟨s.gpr .r5, 8 * (s.gpr .r6).toNat⟩
    let scr : Region := ⟨s.gpr .r7, 256⟩
    s.rd = [sch] ∧ s.wr = [dat, scr] ∧ sch.Disjoint dat ∧ sch.Disjoint scr ∧ dat.Disjoint scr ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r7).toNat + 256 ≤ 2 ^ 64 ∧ ((s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .r3)) (s.gpr .r4).toNat (dir up)
        (Spec.Cast5.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

/-- The ECB functions' contract with the table, as the proof states it. -/
def ecbPC (up : Bool) : Contract isa where
  pre s := (ecbP up).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts 0 s
  post := (ecbP up).post
  pub s₁ s₂ := (ecbP up).pub s₁ s₂ ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

section
variable {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State}

/-- What the contract says of a function's one table: its words. -/
theorem ConstsOk.held1 (h : ConstsOk [(name, ws)] st s) : Held s.mem (s.syms name) ws :=
  h.2.1 _ List.mem_cons_self

/-- The code may read it. -/
theorem ConstsOk.rd1 (h : ConstsOk [(name, ws)] st s) : (⟨s.syms name, 8 * ws.length⟩ : Region) ∈ s.rd :=
  h.mem_rd List.mem_cons_self

/-- No writable region overlaps it. -/
theorem ConstsOk.wr1 (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms name, 8 * ws.length⟩ r :=
  (h.2.2 _ List.mem_cons_self).2.1

end

theorem stripConsts_rd_mem {K : List (String × List (BitVec 64))} {s : State} {r : Region}
    (h : r ∈ (stripConsts K s).rd) : r ∈ s.rd := List.mem_of_mem_take h

theorem ecb_blocks (K : Spec.Cast5.Schedule) (n : Nat) (up : Bool) (m m' : Mem) (D : Addr) (N : Nat)
    (h : ∀ b < N, Spec.Cast5.blockAt m' (wAt D b) = cipher up K n (Spec.Cast5.blockAt m (wAt D b))) :
    Spec.Cast5.blocksAt m' D N = Spec.Cast5.ecb K n (dir up) (Spec.Cast5.blocksAt m D N) := by
  simp only [Spec.Cast5.blocksAt, Spec.Cast5.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- The registers ECB writes. -/
def ecbRegs : List Reg := [.r0, .r4, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19,
  .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30]

theorem ecb_ok (up : Bool) (hw : writesOnly ecbRegs (ecb up) = true) (hn : (ecb up).noCalls = true)
    (s : State) (hs : (ecbPC up).pre s) :
    ∃ t s', Exec isa (ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbPC up).post s s' := by
  obtain ⟨⟨hrd, hwr, dKD, dKS, dDS, hkf, hdf, hcf, hn'⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dKD dKS dDS hkf hdf hcf hn'
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have pre : EcbPre s :=
    { key := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
      kfit := hkf
      data := by rw [hwr]; simp
      fit := hdf
      scr := by rw [hwr]; simp
      sfit := hcf
      keyData := dKD
      keyScr := dKS
      dataScr := dDS
      nv := hn'
      trd := List.mem_append_left _ trd
      held := ConstsOk.held1 hk
      tblData := twr _ (by rw [hwr]; simp)
      tblScr := twr _ (by rw [hwr]; simp) }
  obtain ⟨t, s', he, hp, hk'⟩ := WP.keep ecbRegs (ecb_wp up pre) hw hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hp.lr⟩,
    ecb_blocks _ _ _ _ _ _ _ hp.done⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    first
    | exact hp.saved _ (by decide)
    | exact hk'.gpr (by decide)

theorem ecb_agree (up : Bool) : ∀ s₁ s₂, (ecbPC up).pre s₁ → (ecbPC up).pre s₂ → (ecbPC up).pub s₁ s₂ →
    (taintSym [s1234Sym]).Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  intro s₁ s₂ _ _ ⟨h, hsy⟩
  refine ⟨⟨h.2.2.2.2.2, fun r hr => ?_⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem ecbEncrypt_ct : ConstantTime isa (ecbPC true).pre (ecbPC true).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (ecb_agree true) (by taint_decide)

theorem ecbDecrypt_ct : ConstantTime isa (ecbPC false).pre (ecbPC false).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (ecb_agree false) (by taint_decide)

/-- A state satisfying the precondition without the table: no blocks. -/
def ecbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 12 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 256⟩]

theorem ecbP_implies (up : Bool) : (ecbP up).Implies (Spec.Cast5.ecbContract abi (dir up)) := by
  cases up <;>
  sig_implies [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, Spec.Cast5.ecbPost, abi, argRegs,
    ecbP, dir] [ecbSat] using ecbSat

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the witness with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def ecbSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else 0

theorem ecbSatMem_held : ∀ i < s1234.length,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  rw [hl] at hi
  have hm : ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold ecbSatMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega)]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [hl]; decide) i (by rw [hl]; exact hi))

/-- A state satisfying the precondition with the table. -/
def ecbSatC : State :=
  { ecbSat with mem := ecbSatMem, rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩], syms := fun _ => 0x100000 }

theorem ecb_sat (up : Bool) : (Spec.Cast5.ecbContract (abi.withConsts ecbConsts) (dir up)).pre ecbSatC := by
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : ecbSatC = s
  sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, abi, argRegs, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, rfl, rfl,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
  change r ∈ [⟨0x2000, 0⟩, ⟨0x3000, 256⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)

theorem ecbPC_implies (up : Bool) :
    (ecbPC up).Implies (Spec.Cast5.ecbContract (abi.withConsts ecbConsts) (dir up)) :=
  { pre := fun _ hs => ⟨(ecbP_implies up).pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
    post := fun s s' hs hp => post_consts.mpr ((ecbP_implies up).post (stripConsts ecbConsts s) s'
      (pre_consts.mp hs).1 hp)
    pub := fun s₁ s₂ h₁ h₂ hp => ⟨(ecbP_implies up).pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂)
        (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
    sat := ⟨ecbSatC, ecb_sat up⟩ }

theorem ecbEncrypt_verified :
    Verified target ecbEncrypt (Spec.Cast5.ecbEncryptContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_ok true (by lit_decide) (by lit_decide)) ecbEncrypt_ct (ecbPC_implies true)

theorem ecbDecrypt_verified :
    Verified target ecbDecrypt (Spec.Cast5.ecbDecryptContract (abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_ok false (by lit_decide) (by lit_decide)) ecbDecrypt_ct (ecbPC_implies false)

end VG.Proof.Cast5.PPC64LE
