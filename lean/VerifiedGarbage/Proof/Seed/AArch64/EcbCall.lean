module
public import VerifiedGarbage.Impl.Seed.AArch64.Modes
public import VerifiedGarbage.Proof.Seed.Contract
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Seed.AArch64.ModeCore
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Seed.AArch64.Link
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Modes.AArch64.Ecb
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Seed.ModeBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Seed.AArch64.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Seed.AArch64.Verified
meta import VerifiedGarbage.Proof.Seed.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Modes.Ctr
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Seed.AArch64.Link
meta import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Modes.AArch64.Ecb
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Seed.AArch64.Lit
meta import VerifiedGarbage.Proof.Seed.AArch64.Lit

/-!
# SEED ECB on AArch64: a few blocks one at a time, or calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1456 bytes, the modes' 182 words) and, for seven blocks
or more, call the blocks function of their direction with it (`ecbCall`,
which uses 1088 bytes of it: `ecbCall_correct`, from the blocks functions'
contracts), in a frame saving `x30`; fewer blocks go one at a time through
the modes' generic ECB over the one-block core (`ecbShort_wp`, from
`Proof.Modes.AArch64.ecb_wp`). `ecbFew_verified` proves the two together,
with the working space as an argument and 16 bytes of stack;
`ecbFew_framed` adds the frame of the working space.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.Impl.Seed.AArch64

/-- The ECB contracts with `N` bytes of `scratch` (the 136 words of the
blocks functions, or the 182 of `vg_seed_ecb_{en,de}crypt`'s frame) and
`stack = 16`, as `sig_pre` evaluates them. -/
def ecbCallAArch64 (d : Spec.Seed.Direction) (N : Nat := 1088) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let scr : Region := ⟨s.gpr .x3, N⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + N ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem frame_push (s₀ : State) :
    Frame [⟨s₀.sp - 16, 16⟩] s₀.mem (s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30)) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by simp [Region.Contains])

/-- A call, in a frame saving `x30`, of code meeting the blocks contract of
`d`. -/
theorem call_correct {d : Spec.Seed.Direction} {name : String} {c : Prog isa} {N : Nat} (hN : 1088 ≤ N)
    (hv : Verified AArch64.target c (Proof.Seed.blocksContract AArch64.abi d)) (hn : c.noFrames = true)
    (s₀ : State) (hs : (ecbCallAArch64 d N).pre s₀) :
    ∃ t s', Exec isa (.frame (.push .x30) (.call name c) (.pop .x30)) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (ecbCallAArch64 d N).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩ := hs
  refine (WP.frameRegKept (r := .x30) (s₀ := s₀) hsp (fun R hR => ?_) ?_
    (by rw [fdepth_of_noFrames (show (Code.call name c : Prog isa).noFrames = true from hn)]; decide)).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  · rw [hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sD
    · exact sS
  have hsub : Region.Sub ⟨s₀.gpr .x3, 1088⟩ ⟨s₀.gpr .x3, N⟩ := Region.sub_prefix hN
  have hw : Covers [⟨s₀.gpr .x1, (s₀.gpr .x2).toNat * 16⟩, ⟨s₀.gpr .x3, 1088⟩] s₀.wr := by
    rw [hwr]
    refine Covers.pair (Covers.of_mem fun r hr => ?_) (Covers.of_sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by omega_using [hN]⟩
  refine WP.callV (k := Proof.Seed.blocksContract AArch64.abi d) hv.1 (rd := s₀.rd)
    (wr := [⟨s₀.gpr .x1, (s₀.gpr .x2).toNat * 16⟩, ⟨s₀.gpr .x3, 1088⟩]) ?_ ?_ ?_ ?_ hn
  rotate_left
  · exact Covers.append (Covers.refl _) hw
  · exact hw
  rotate_left
  · sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, AArch64.abi, AArch64.argRegs]
    exact ⟨hrd, dKD, dKS.sub_right hsub, dDS.sub_right hsub, fitK, fitD, by omega_using [fitS, hN]⟩
  · intro s' rd' wr' sp' hf hg _ hvv hpost
    sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, AArch64.abi, AArch64.argRegs] at hpost
    rw [BitVec.setWidth_eq] at hpost
    have hfr := frame_push s₀
    have hsch := Proof.Seed.scheduleAt_frame hfr (p := s₀.gpr .x0) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sK.symm
    have hblk := Proof.Seed.blocksAt_frame hfr (p := s₀.gpr .x1) (n := (s₀.gpr .x2).toNat) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega_using [fitD])
    refine ⟨⟨fun r hr => ?_, rfl, fun r hr => hvv r hr⟩, ?_⟩
    · show (s'.write .x .x30 (s₀.gpr .x30)).gpr r = s₀.gpr r
      by_cases h : r = .x30
      · subst h; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · rw [RegUpd.gpr_write_of_ne _ _ _ h, hg r hr h]
    · show Spec.Seed.blocksAt s'.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat = _
      rw [hpost, hsch, hblk]

theorem ecbCall_correct (d : Spec.Seed.Direction) {N : Nat} (hN : 1088 ≤ N) (s₀ : State)
    (hs : (ecbCallAArch64 d N).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallAArch64 d N).post s₀ s' := by
  cases d
  · exact call_correct hN encrypt_blocks_verified (by lit_decide) s₀ hs
  · exact call_correct hN decrypt_blocks_verified (by lit_decide) s₀ hs

/-! ## A few blocks, one at a time -/

attribute [local irreducible] Spec.Seed.cipher Spec.Seed.invCipher in
theorem serialDirCipher_eq (d : Spec.Seed.Direction) : (serialDirCoreSpec d).cipher = Proof.Seed.dirCipher d := rfl

/-- The modes' ECB of the blocks' bytes is the contract's of the blocks. -/
theorem ecb_of_blocks {K : Spec.Seed.Schedule} {d : Spec.Seed.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Proof.Modes.blocksOf 16 m' D n = (Proof.Modes.blocksOf 16 m D n).map (Proof.Seed.dirCipher d K)) :
    Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n) := by
  have hb : ∀ j < n, Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := fun j hj => by
    have e := congrArg (fun l => l[j]?) h
    simp only [Proof.Modes.blocksOf, List.map_map, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Function.comp_apply, Option.some.injEq] at e
    rw [Proof.Seed.bytesAt_eq, dirCipher_bytes] at e
    exact Vector.toList_inj.mp e
  simp only [Spec.Seed.blocksAt, Spec.Seed.ecb, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  rw [Function.comp_apply, hb j (List.mem_range.mp hj)]
  cases d <;> rfl

/-- Fewer than seven blocks: the modes' ECB over the one-block core. -/
theorem ecbShort_wp (d : Spec.Seed.Direction) {s₀ : State} (hs : (ecbCallAArch64 d 1456).pre s₀) :
    WP isa (ecbShort d) s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ (ecbCallAArch64 d 1456).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩ := hs
  have hwS : (⟨s₀.gpr .x3, 8 * 182⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have e16 : 8 * (serialDirCore d).bw * (s₀.gpr .x2).toNat = (s₀.gpr .x2).toNat * 16 := by
    rw [serialCore_bw]; omega_using []
  refine WP.mono (Proof.Modes.AArch64.ecb_wp (serialDirCoreSpec d) (data := .x1) (nR := .x2) (scr := .x3)
    (by decide) (by decide) (by cases d <;> decide)
    (B := s₀.gpr .x3) (D := s₀.gpr .x1) (n := (s₀.gpr .x2).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl ⟨hwS, fitS⟩
    (by rw [hwr, e16]; exact List.mem_cons_self) (by rw [e16]; exact dDS) (by rw [e16]; exact fitD)
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [serialCore_bw, show 8 * 2 = 16 from rfl, serialDirCipher_eq] at hdata
  exact ecb_of_blocks hdata

theorem ecbFew_keepsV (d : Spec.Seed.Direction) : (ecbFew d).allInstrs keepsV = true := by
  cases d
  · exact (by lit_decide : ecbEncrypt.allInstrs keepsV = true)
  · exact (by lit_decide : ecbDecrypt.allInstrs keepsV = true)

/-- `vg_seed_ecb_{en,de}crypt` within its frame of 182 words. -/
theorem ecbFew_correct (d : Spec.Seed.Direction) (s₀ : State) (hs : (ecbCallAArch64 d 1456).pre s₀) :
    ∃ t s', Exec isa (ecbFew d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallAArch64 d 1456).post s₀ s' := by
  obtain ⟨sₐ, eₐ, _, gₐ, mₐ, rdₐ, wrₐ⟩ := Modes.AArch64.addImm_ok s₀ .x13 .x2 (v := 1) (by decide)
  obtain ⟨s₁, e', _, g', m', rd', wr'⟩ := Modes.AArch64.lsr_ok sₐ .x13 .x13 (sh := 3) (by decide)
  have e₁ : runBlock isa [.addImm .x .x13 .x2 1, .lsr .x .x13 .x13 3] s₀ = some s₁ := by
    rw [show ([.addImm .x .x13 .x2 1, .lsr .x .x13 .x13 3] : List Instr) =
      [.addImm .x .x13 .x2 1] ++ [.lsr .x .x13 .x13 3] from rfl, Modes.AArch64.runBlock_app, eₐ,
      Option.bind_some, e']
  have g₁ : ∀ r, r ≠ .x13 → s₁.gpr r = s₀.gpr r := fun r hr => (g' r hr).trans (gₐ r hr)
  have m₁ : s₁.mem = s₀.mem := m'.trans mₐ
  have rd₁ : s₁.rd = s₀.rd := rd'.trans rdₐ
  have wr₁ : s₁.wr = s₀.wr := wr'.trans wrₐ
  have sp₁ : s₁.sp = s₀.sp := by
    obtain ⟨t, s'', he, rfl⟩ := (WP.of_runBlock ⟨s₁, e₁, rfl⟩ :
      WP isa (.block [.addImm .x .x13 .x2 1, .lsr .x .x13 .x13 3]) s₀ fun s' => s' = s₁)
    exact Exec.sp he
  have hp₁ : (ecbCallAArch64 d 1456).pre s₁ := by
    simpa only [ecbCallAArch64, rd₁, wr₁, sp₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide),
      g₁ .x3 (by decide)] using hs
  have transfer {s' : State} (h : (ecbCallAArch64 d 1456).post s₁ s') : (ecbCallAArch64 d 1456).post s₀ s' := by
    simpa only [ecbCallAArch64, m₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide)] using h
  have hpres : ∀ r ∈ preserved, r ≠ .x13 := by decide
  have main : WP isa (ecbFew d) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      (ecbCallAArch64 d 1456).post s₀ s' := by
    unfold ecbFew
    refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
    refine WP.ite _ rfl (fun _ => ?_) (fun _ => ?_)
    · refine WP.mono (WP.gprs' (ecbShort_keeps_x30 d) (ecbShort_wp d hp₁)) fun s' ⟨⟨h₁, h₂⟩, h₃⟩ =>
        ⟨fun r hr => (Modes.AArch64.preserved_of h₁ h₃ r hr).trans (g₁ r (hpres r hr)), transfer h₂⟩
    · obtain ⟨t, s', he, ha, hq⟩ := ecbCall_correct d (N := 1456) (by decide) s₁ hp₁
      exact ⟨t, s', he, fun r hr => (ha.1 r hr).trans (g₁ r (hpres r hr)), transfer hq⟩
  obtain ⟨t, s', he, hr, hq⟩ := main
  exact ⟨t, s', he, ⟨hr, Exec.sp he, Exec.preservedV he (ecbFew_keepsV d)⟩, hq⟩

theorem ecbTaint_agree (d : Spec.Seed.Direction) (s₁ s₂ : State) (_ : (ecbCallAArch64 d 1456).pre s₁)
    (_ : (ecbCallAArch64 d 1456).pre s₂) (hp : (ecbCallAArch64 d 1456).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3, h4⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbFew_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (ecbCallAArch64 d 1456).pre (ecbCallAArch64 d 1456).pub (ecbFew d) := by
  cases d
  · exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbTaint_agree .encrypt)
      (by taint_decide) : ConstantTime isa _ _ ecbEncrypt)
  · exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbTaint_agree .decrypt)
      (by taint_decide) : ConstantTime isa _ _ ecbDecrypt)

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, one block at `0x3000`, the working space
at `0x4000`. -/
def ecbFewSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 1456⟩]

theorem ecbFew_verified (d : Spec.Seed.Direction) :
    Verified AArch64.target (ecbFew d) (Proof.Seed.ecbScratchContract AArch64.abi d 182 16) :=
  Verified.of_correct (ecbFew_correct d) (ecbFew_ct d) (by
    sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, ecbCallAArch64,
      AArch64.abi, AArch64.argRegs] [ecbFewSat] using ecbFewSat)

/-- `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`: the code in a frame
allocating the working space, 1472 bytes of stack in all. -/
theorem ecbFew_framed (d : Spec.Seed.Direction) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x3 182 (ecbFew d))
      (Spec.Seed.ecbContract AArch64.abi d 1472) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Spec.Seed.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 1456) (ecbFew_verified d) (by decide) (by decide) (by decide) (Proof.Seed.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.AArch64
