module

public import VerifiedGarbage.Impl.Sm4.X86_64.Fn
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Sm4.X86_64.KeyVerified
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

meta import VerifiedGarbage.Impl.Sm4.X86_64.Fn
meta import VerifiedGarbage.Proof.Sm4.X86_64.Lit
-- separate module: the frame/call proof is checked independently of the other
-- modes' residue proofs, which take substantially longer than these imports.

@[expose] public section
namespace VG.Proof.Sm4.X86_64
open VG VG.X86_64 VG.Impl.Sm4.X86_64.Fn

private theorem keyCore_spSafe : SpSafe keyCore := by
  apply SpSafe.of_all
  exact withStackScratch_spSafe (r := .rdx) (by decide)
    (Code.all_of_spTest (by lit_decide))

private theorem keyCall_entry (s : State)
    (hp : (Spec.Sm4.expandKeyContract X86_64.abi 3160).pre s) :
    let a := allocState 8 s
    (Spec.Sm4.expandKeyContract X86_64.abi 3144).pre
      (a.callEntry.withRegions [⟨s.gpr .rdi, 16⟩] [⟨s.gpr .rsi, 128⟩]) ∧
    Covers ([⟨s.gpr .rdi, 16⟩] ++ [⟨s.gpr .rsi, 128⟩]) (a.rd ++ a.wr) ∧
    Covers [⟨s.gpr .rsi, 128⟩] a.wr := by
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at hp
  obtain ⟨hst, hrd, hwr, hks, hrk, hrs, hsk, hss, hkw, hsw⟩ := hp
  let a := allocState 8 s
  have asp : a.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8 := allocState_rsp' _ _
  have ag : ∀ r, r ≠ .rsp → a.gpr r = s.gpr r := fun r hr => allocState_gpr' _ _ hr
  have hret : Region.Sub ⟨a.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 3160) := by
    rw [asp, BitVec.sub_sub]
    exact Offset.sub_below _ (a := 16) (by decide) (by decide)
  have hstk : Region.Sub ⟨a.gpr .rsp - 8 - BitVec.ofNat 64 3144, 3144⟩
      (below (s.gpr .rsp) 3160) := by
    rw [asp, BitVec.sub_sub, BitVec.sub_sub]
    exact Offset.sub_below _ (a := 3160) (by decide) (by decide)
  have hpre : (Spec.Sm4.expandKeyContract X86_64.abi 3144).pre
      (a.callEntry.withRegions [⟨s.gpr .rdi, 16⟩] [⟨s.gpr .rsi, 128⟩]) := by
    sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs]
    refine ⟨?_, hks, ?_, ?_, ?_, ?_, hkw, hsw⟩
    · rw [BitVec.sub_sub]
      change 3144 ≤ (s.gpr .rsp - BitVec.ofNat 64 16).toNat
      rw [toNat_sub_ofNat (by omega_using [hst])]
      omega_using [hst]
    · simpa only [asp] using hsk.sub_left hret
    · simpa only [asp] using hss.sub_left hret
    · simpa only [asp] using hsk.sub_left hstk
    · simpa only [asp] using hss.sub_left hstk
  have hc : Covers ([⟨s.gpr .rdi, 16⟩] ++ [⟨s.gpr .rsi, 128⟩]) (a.rd ++ a.wr) := by
    apply Covers.of_mem
    change ∀ r ∈ _, r ∈ s.rd ++ (⟨s.gpr .rsp - 8, 8⟩ :: s.wr)
    rw [hrd, hwr]
    regions_sub
  have hw : Covers [⟨s.gpr .rsi, 128⟩] a.wr := by
    apply Covers.of_mem
    change ∀ r ∈ _, r ∈ ⟨s.gpr .rsp - 8, 8⟩ :: s.wr
    rw [hwr]
    regions_sub
  exact ⟨hpre, hc, hw⟩

private theorem keyCall_correct (s : State)
    (hp : (Spec.Sm4.expandKeyContract X86_64.abi 3160).pre s) :
    ∃ t s', Exec isa keyCall s t s' ∧ abiPreserved s s' ∧
      (Spec.Sm4.expandKeyContract X86_64.abi 3160).post s s' := by
  obtain ⟨hpre, hc, hw⟩ := keyCall_entry s hp
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at hp
  obtain ⟨hst, hrd, hwr, hks, hrk, hrs, hsk, hss, hkw, hsw⟩ := hp
  let a := allocState 8 s
  have asp : a.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8 := allocState_rsp' _ _
  have ag : ∀ r, r ≠ .rsp → a.gpr r = s.gpr r := fun r hr => allocState_gpr' _ _ hr
  have hret : Region.Sub ⟨a.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 3160) := by
    rw [asp, BitVec.sub_sub]
    exact Offset.sub_below _ (a := 16) (by decide) (by decide)
  suffices run : WP isa keyCall s (fun s' => abiPreserved s s' ∧
      (Spec.Sm4.expandKeyContract X86_64.abi 3160).post s s') from
    run.elim fun t ⟨s', he, ha, hp⟩ => ⟨t, s', he, ha, hp⟩
  apply alloc_frame_ok (s := s) (bytes := 8) (by decide) (by omega_using [hst])
  refine WP.callF (c := keyCore) (k := Spec.Sm4.expandKeyContract X86_64.abi 3144)
    expandKey_framedU.1 keyCore_spSafe (by lit_decide) hpre hc hw ?_
  intro u urd uwr ucs uf ⟨v, vm, vg, vp⟩ umx
  have usp := ucs .rsp (by decide)
  refine ⟨usp, uwr, ?_⟩
  intro m U fm
  have subCall : Region.Sub (below (a.gpr .rsp) (keyCore.x86_64Depth + 8))
      (below (s.gpr .rsp) 3160) := by
    have hd : keyCore.x86_64Depth = 3144 := by lit_decide
    rw [hd, asp]
    change Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 3152, 3152⟩ _
    rw [BitVec.sub_sub]
    exact Offset.sub_below _ (a := 3160) (by decide) (by decide)
  have subFrame : Region.Sub ⟨s.gpr .rsp - 8, 8⟩ (below (s.gpr .rsp) 3160) :=
    Offset.sub_below _ (a := 8) (by decide) (by decide)
  have fc : Frame [⟨s.gpr .rsi, 128⟩, below (s.gpr .rsp) 3160] s.mem u.mem := by
    apply uf.sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), subCall⟩
  have ff : Frame [⟨s.gpr .rsi, 128⟩, below (s.gpr .rsp) 3160] u.mem m := by
    apply fm.sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), subFrame⟩
  have ft := fc.trans ff
  have fE : Frame [⟨a.gpr .rsp - 8, 8⟩] s.mem a.callEntry.mem := by
    rw [State.callEntry_mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have eK : Spec.Sm4.blockAt a.callEntry.mem (s.gpr .rdi) = Spec.Sm4.blockAt s.mem (s.gpr .rdi) := by
    apply Vector.ext
    intro i hi
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    exact fE.bytes (R := ⟨s.gpr .rdi, 16⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (hsk.sub_left hret).symm)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hi
  have eS : Spec.Sm4.scheduleAt m (s.gpr .rsi) = Spec.Sm4.scheduleAt u.mem (s.gpr .rsi) := by
    apply Proof.Sm4.scheduleAt_congr
    intro i hi
    exact fm.bytes (R := ⟨s.gpr .rsi, 128⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (hss.sub_left subFrame).symm)
      (by show (128 : Nat) ≤ 2 ^ 64; decide) hi
  sig_post [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at vp ⊢
  change Spec.Sm4.blockAt (s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8 - 8) (s.unknowns 0))
    (s.gpr .rdi) = Spec.Sm4.blockAt s.mem (s.gpr .rdi) at eK
  rw [vm, eK] at vp
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    by_cases h : r = .rsp
    · subst h
      exact freeState_rsp usp
    · change (freeState 8 u).gpr r = s.gpr r
      change (u.setReg .rsp (u.gpr .rsp + BitVec.ofNat 64 8)).gpr r = s.gpr r
      rw [RegUpd.gpr_setReg_of_ne _ _ h]
      exact (ucs r hr).trans (allocState_gpr' _ _ h)
  · exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hrs
        · exact Offset.base_disjoint_below _ (by decide)) (by decide)
  · change u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    exact umx
  · rw [eS]
    exact vp

theorem keyCall_spSafe : keyCall.all (fun i => !isa.writesSp i) = true := by
  sp_safe

private theorem keyCall_ct : ConstantTime isa
    (Spec.Sm4.expandKeyContract X86_64.abi 3160).pre
    (Spec.Sm4.expandKeyContract X86_64.abi 3160).pub keyCall := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
  refine RelCT.callEx (k := Spec.Sm4.expandKeyContract X86_64.abi 3144)
    expandKey_framedU.1 expandKey_framedU.2.1 ?_
  intro a b hab
  obtain ⟨s₁, s₂, hp, ha, hb⟩ := hab
  subst a b
  obtain ⟨h₁, h₂, hp⟩ := hp
  obtain ⟨pre₁, cov₁, wr₁⟩ := keyCall_entry s₁ h₁
  obtain ⟨pre₂, cov₂, wr₂⟩ := keyCall_entry s₂ h₂
  refine ⟨_, _, _, _, pre₁, pre₂, ?_, cov₁, wr₁, cov₂, wr₂, ?_⟩
  · sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at hp ⊢
    obtain ⟨hsp, hk, hs⟩ := hp
    exact ⟨by rw [hsp], hk, hs⟩
  · sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86_64.abi, X86_64.argRegs] at hp
    rw [allocState_rsp', allocState_rsp', hp.1]

theorem keyCall_verified : Verified target keyCall (Spec.Sm4.expandKeyContract X86_64.abi 3160) :=
  ⟨keyCall_correct, keyCall_ct,
    X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
      (by rw [Curry.apply_const]; trivial)⟩

end VG.Proof.Sm4.X86_64
