module
public import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Impl.Sm4.AArch64.EcbFew
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.Sm4.CtrCipher
public import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.Sm4.AArch64.EcbFew
meta import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.Ecb
import VerifiedGarbage.Proof.Sm4.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.Ecb
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.Sm4.AArch64.Verified
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.AArch64.CryptSum
meta import VerifiedGarbage.Proof.Sm4.AArch64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4 ECB on AArch64: the functions of one direction

`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` (`ecbFew`) take fewer than
seven blocks one at a time: the modes' generic ECB over the one-block core
of the direction (`ecbShort_wp`, from `Proof.Modes.AArch64.ecb_wp`), in a
frame of its 408 words of working space (`ecbShortFramed_verified`).
Otherwise (`ecbCall`) they set `decrypt` and call `vg_sm4_ecb`
(`ecbAny_framed`), in a frame saving `x30`: 16 bytes of stack below the
callee's 3168 (`ecbCall_correct`). `ecbFew_verified` proves the two
together against the ECB contracts with `stack = 3264`.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64
open VG.Proof.Sm4 (specDirA)

/-- `vg_sm4_ecb`'s code: `ecbAny` with its working space on the stack. -/
abbrev ecbAnyFramed : Prog isa := Impl.StackScratch.AArch64.withStackScratchWiped 3168 .x4 396 ecbAny

/-- The ECB contracts with `stack = 3184`, as `sig_pre` evaluates them. -/
def ecbCallAArch64 (dir : Dir) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 3184, 3184⟩
    3184 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ stk.Disjoint sched ∧
      stk.Disjoint data ∧ (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) (specDirA dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

/-- The value `ecbCall dir` sets `decrypt` to. -/
def dirFlag : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

theorem ecbCall_eq (dir : Dir) :
    ecbCall dir ecbAnyFramed = .frame (.push .x30)
      (.seq (.block [.movz .x .x3 (BitVec.ofNat 16 (dirFlag dir)) 0]) (.call "vg_sm4_ecb" ecbAnyFramed))
      (.pop .x30) := by
  cases dir <;> rfl

theorem specDirA_dirFlag (dir : Dir) :
    specDirA dir = Proof.Sm4.directionOf (BitVec.ofNat 64 (dirFlag dir)).toNat := by
  cases dir <;> rfl

theorem movz_sp_ok (s : State) (d : Reg) {v : Nat} (hv : v < 65536) :
    ∃ s', runBlock isa [.movz .x d (BitVec.ofNat 16 v) 0] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.v = s.v := by
  refine ⟨s.write .x d ((BitVec.ofNat 16 v).setWidth 64 <<< (16 * 0)), ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [runBlock_cons]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hv]

theorem ecbCall_depth (dir : Dir) :
    16 * (Code.seq (.block [.movz .x .x3 (BitVec.ofNat 16 (dirFlag dir)) 0])
      (.call "vg_sm4_ecb" ecbAnyFramed) : Prog isa).aarch64Depth + 16 < 2 ^ 64 := by
  cases dir <;> lit_decide

theorem ecbCall_correct (dir : Dir) (s₀ : State) (hs : (ecbCallAArch64 dir).pre s₀) :
    ∃ t s', Exec isa (ecbCall dir ecbAnyFramed) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (ecbCallAArch64 dir).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dSK, dSD, fitK, fitD⟩ := hs
  have hk : dirFlag dir ≤ 1 := by cases dir <;> decide
  -- The frame's slot and the callee's stack, below the stack the contract reserves.
  have frameSub : Region.Sub ⟨s₀.sp - BitVec.ofNat 64 16, 16⟩ ⟨s₀.sp - BitVec.ofNat 64 3184, 3184⟩ :=
    fun x hx => Offset.below_mono s₀.sp (by decide) (by decide) x hx
  have slotSub : Region.Sub ⟨s₀.sp - BitVec.ofNat 64 16, 8⟩ ⟨s₀.sp - BitVec.ofNat 64 3184, 3184⟩ :=
    fun x hx => frameSub x (Region.sub_prefix (by decide) x hx)
  have spSub : s₀.sp - BitVec.ofNat 64 16 - BitVec.ofNat 64 3168 = s₀.sp - BitVec.ofNat 64 3184 := by
    rw [← Offset.sub_add_eq, BitVec.ofNat_add_ofNat]
  rw [ecbCall_eq]
  refine (WP.frameRegKept (r := .x30) (s₀ := s₀) (by omega_using [hsp]) (fun R hR => ?_) ?_ (ecbCall_depth dir)).elim
    fun t ⟨s', he, hq⟩ => ⟨t, s', he, hq⟩
  · rw [hwr, List.mem_singleton] at hR; subst hR
    exact dSD.sub_left frameSub
  obtain ⟨σ, e₂, x3₂, o₂, m₂, rd₂, wr₂, sp₂, v₂⟩ := movz_sp_ok
    { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) } .x3 (v := dirFlag dir)
    (by omega_using [hk])
  refine WP.seq (WP.of_runBlock ⟨σ, e₂, ?_⟩)
  have g₂ : ∀ r, r ≠ .x3 → σ.gpr r = s₀.gpr r := fun r h => o₂ r h
  have hsp₂ : σ.sp = s₀.sp - BitVec.ofNat 64 16 := sp₂
  refine WP.callFV (k := Proof.Sm4.ecbDirContract AArch64.abi 3168) ecbAny_framed.1 (rd := s₀.rd) (wr := s₀.wr)
    ?_ (fun _ _ h => by rw [rd₂, wr₂]; exact h) (fun _ _ h => by rw [wr₂]; exact h) ?_ (by lit_decide)
  · have e0 : σ.gpr .x0 = s₀.gpr .x0 := g₂ _ (by decide)
    have e1 : σ.gpr .x1 = s₀.gpr .x1 := g₂ _ (by decide)
    have e2 : σ.gpr .x2 = s₀.gpr .x2 := g₂ _ (by decide)
    sig_pre [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs]
    simp only [e0, e1, e2, x3₂, hsp₂, spSub]
    refine ⟨?_, hrd, hwr, dKD, dSK.sub_left (Region.sub_prefix (by decide)),
      dSD.sub_left (Region.sub_prefix (by decide)), fitK, fitD, ?_⟩
    · rw [Offset.toNat_sub_ofNat]; omega_using [hsp]
    · rw [BitVec.toNat_ofNat]; omega_using [hk]
  · intro s' rd' wr' sp' hf hg hv hpost
    sig_reduce [Proof.Sm4.ecbDirContract, Proof.Sm4.ecbDirSig, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs] at hpost
    have e0 : σ.gpr .x0 = s₀.gpr .x0 := g₂ _ (by decide)
    have e1 : σ.gpr .x1 = s₀.gpr .x1 := g₂ _ (by decide)
    have e2 : σ.gpr .x2 = s₀.gpr .x2 := g₂ _ (by decide)
    rw [e0, e1, e2, x3₂, BitVec.setWidth_eq, BitVec.setWidth_eq] at hpost
    have hfr : Frame [⟨s₀.sp - BitVec.ofNat 64 16, 8⟩] s₀.mem σ.mem := by
      rw [m₂]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsch : Spec.Sm4.scheduleAt σ.mem (s₀.gpr .x0) = Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0) :=
      Proof.Sm4.scheduleAt_frame hfr fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact (dSK.sub_left slotSub).symm
    have hblk : Spec.Sm4.blocksAt σ.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat =
        Spec.Sm4.blocksAt s₀.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat :=
      Proof.Sm4.blocksAt_frame hfr (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact (dSD.sub_left slotSub).symm) (by omega_using [fitD])
    refine ⟨⟨fun r hr => ?_, rfl, fun r hr => (hv r hr).trans (by rw [v₂])⟩, ?_⟩
    · show (s'.write .x .x30 (s₀.gpr .x30)).gpr r = s₀.gpr r
      by_cases h : r = .x30
      · subst h; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · have h3 : r ≠ .x3 := fun h3 => by subst h3; exact absurd hr (by decide)
        rw [RegUpd.gpr_write_of_ne _ _ _ h, hg r hr h, g₂ r h3]
    · show Spec.Sm4.blocksAt s'.mem (s₀.gpr .x1) (s₀.gpr .x2).toNat = _
      rw [hpost, hsch, hblk, specDirA_dirFlag]


/-- A state satisfying the ECB functions' precondition with `stack = 3184`:
the schedule at `0x1000`, one block at `0x3000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

/-! ## A few blocks, one at a time -/

open VG.Proof.Modes.AArch64 (KeepsReg)

/-- The ECB contracts with `scratch: *mut [u64; 408]`, as `sig_pre` evaluates
them. -/
def ecbShortAArch64 (d : Spec.Sm4.Direction) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let scr : Region := ⟨s.gpr .x3, 3264⟩
    s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 3264 ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3

/-- The modes' ECB of the blocks' bytes is the contract's of the blocks. -/
theorem ecb_of_blocks {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Proof.Modes.blocksOf 16 m' D n = (Proof.Modes.blocksOf 16 m D n).map (Serial.dirCipher d K)) :
    Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n) := by
  have hb : ∀ j < n, Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      (match d with | .encrypt => Spec.Sm4.encryptBlock K | .decrypt => Spec.Sm4.decryptBlock K)
        (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := fun j hj => by
    have e := congrArg (fun l => l[j]?) h
    simp only [Proof.Modes.blocksOf, List.map_map, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Function.comp_apply, Option.some.injEq] at e
    rw [Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.bytesAt_eq_blockAt] at e
    cases d
    · simp only [Serial.dirCipher, Spec.Sm4.cipher, Proof.Sm4.ofFn_toList] at e
      exact Vector.toList_inj.mp e
    · simp only [Serial.dirCipher, Spec.Sm4.invCipher, Proof.Sm4.ofFn_toList] at e
      exact Vector.toList_inj.mp e
  simp only [Spec.Sm4.blocksAt, Spec.Sm4.ecb, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  rw [Function.comp_apply, hb j (List.mem_range.mp hj)]
  cases d <;> rfl

/-- The one-block core of each direction, and what it computes. -/
theorem ecbShort_wp (d : Spec.Sm4.Direction) {s₀ : State} (hs : (ecbShortAArch64 d).pre s₀) :
    WP isa (ecbShort d) s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ (ecbShortAArch64 d).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, fitK, fitD, fitS⟩ := hs
  have hwS : (⟨s₀.gpr .x3, 8 * 408⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have e16 : 8 * 2 * (s₀.gpr .x2).toNat = (s₀.gpr .x2).toNat * 16 := by omega_using []
  cases d
  · refine WP.mono (Proof.Modes.AArch64.ecb_wp Serial.blockSpec (data := .x1) (nR := .x2) (scr := .x3)
      (by decide) (by decide) (by decide)
      (B := s₀.gpr .x3) (D := s₀.gpr .x1) (n := (s₀.gpr .x2).toNat)
      (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl ⟨hwS, fitS⟩
      (by rw [hwr, Serial.core_bw, e16]; exact List.mem_cons_self) (by rw [Serial.core_bw, e16]; exact dDS)
      (by rw [Serial.core_bw, e16]; exact fitD)
      ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
    rw [Serial.core_bw, show 8 * 2 = 16 from rfl] at hdata
    exact ecb_of_blocks (d := .encrypt) (by
      rw [hdata]; exact congrArg (fun f => List.map f _) (funext fun b => Serial.cipher_eq _ ▸ rfl))
  · refine WP.mono (Proof.Modes.AArch64.ecb_wp Serial.decBlockSpec (data := .x1) (nR := .x2) (scr := .x3)
      (by decide) (by decide) (by decide)
      (B := s₀.gpr .x3) (D := s₀.gpr .x1) (n := (s₀.gpr .x2).toNat)
      (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl ⟨hwS, fitS⟩
      (by rw [hwr, Serial.decCore_bw, e16]; exact List.mem_cons_self) (by rw [Serial.decCore_bw, e16]; exact dDS)
      (by rw [Serial.decCore_bw, e16]; exact fitD)
      ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩) fun s' ⟨hcs, hdata, _, _, _⟩ => ⟨hcs, ?_⟩
    rw [Serial.decCore_bw, show 8 * 2 = 16 from rfl] at hdata
    exact ecb_of_blocks (d := .decrypt) (by
      rw [hdata]; exact congrArg (fun f => List.map f _) (funext fun b => Serial.invCipher_eq _ ▸ rfl))

theorem ecbShort_keeps_x30 (d : Spec.Sm4.Direction) : KeepsReg .x30 (ecbShort d) := by
  cases d
  · show KeepsReg .x30 (Serial.core.ecb .x1 .x2 .x3)
    unfold Impl.Modes.AArch64.Core.ecb Impl.Modes.AArch64.Core.ecbGroup Impl.Modes.AArch64.Core.copyBlocks
      Impl.Modes.AArch64.Core.groupCount
    sm4_keeps_x30
  · show KeepsReg .x30 (Serial.decCore.ecb .x1 .x2 .x3)
    unfold Impl.Modes.AArch64.Core.ecb Impl.Modes.AArch64.Core.ecbGroup Impl.Modes.AArch64.Core.copyBlocks
      Impl.Modes.AArch64.Core.groupCount
    sm4_keeps_x30

theorem ecbShort_keepsV (d : Spec.Sm4.Direction) : (ecbShort d).allInstrs keepsV = true := by
  cases d
  · exact (by lit_decide : ecbShortEncrypt.allInstrs keepsV = true)
  · exact (by lit_decide : ecbShortDecrypt.allInstrs keepsV = true)

theorem ecbShortTaint_agree (d : Spec.Sm4.Direction) (s₁ s₂ : State) (_ : (ecbShortAArch64 d).pre s₁)
    (_ : (ecbShortAArch64 d).pre s₂) (hp : (ecbShortAArch64 d).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3, h4⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbShort_ct (d : Spec.Sm4.Direction) :
    ConstantTime isa (ecbShortAArch64 d).pre (ecbShortAArch64 d).pub (ecbShort d) := by
  cases d
  · exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbShortTaint_agree .encrypt)
      (by taint_decide) : ConstantTime isa _ _ ecbShortEncrypt)
  · exact (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) (ecbShortTaint_agree .decrypt)
      (by taint_decide) : ConstantTime isa _ _ ecbShortDecrypt)

/-- A state satisfying `ecbShortAArch64`'s precondition. -/
def ecbShortSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 3264⟩]

theorem ecbShort_verified (d : Spec.Sm4.Direction) :
    Verified AArch64.target (ecbShort d) (Proof.Sm4.ecbScratchContract AArch64.abi d 408) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' (ecbShort_keeps_x30 d) (ecbShort_wp d hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (ecbShort_keepsV d), h₂⟩)
    (ecbShort_ct d) (by
    sig_implies [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, ecbShortAArch64,
      AArch64.abi, AArch64.argRegs] [ecbShortSat] using ecbShortSat)

/-- A few blocks, with the working space on the stack: 3264 bytes. -/
theorem ecbShortFramed_verified (d : Spec.Sm4.Direction) :
    Verified AArch64.target (ecbShortFramed d) (Spec.Sm4.ecbContract AArch64.abi d 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Spec.Sm4.ecbPost d AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) (ecbShort_verified d) (by decide) (by decide) (by decide) (Proof.Sm4.ecbPostOut_local _ d)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## The two together -/

/-- The ECB contracts with `stack = 3264`, as `sig_pre` evaluates them. -/
def ecbFewAArch64 (d : Spec.Sm4.Direction) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 3264, 3264⟩
    3264 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ stk.Disjoint sched ∧
      stk.Disjoint data ∧ (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (Spec.Sm4.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

theorem specDirA_callDir (d : Spec.Sm4.Direction) : specDirA (callDir d) = d := by cases d <;> rfl

theorem ecbFew_correct (d : Spec.Sm4.Direction) (s₀ : State) (hs : (ecbFewAArch64 d).pre s₀) :
    ∃ t s', Exec isa (ecbFew d ecbAnyFramed) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbFewAArch64 d).post s₀ s' := by
  have hpres : ∀ r ∈ preserved, r ≠ .x13 := by decide
  refine few7_wp (Q := fun s' => abiPreserved s₀ s' ∧ (ecbFewAArch64 d).post s₀ s')
    fun s₁ g₁ m₁ rd₁ wr₁ sp₁ v₁ => ?_
  obtain ⟨hsp, hrd, hwr, dKD, dSK, dSD, fitK, fitD⟩ := hs
  have e0 : s₁.gpr .x0 = s₀.gpr .x0 := g₁ _ (by decide)
  have e1 : s₁.gpr .x1 = s₀.gpr .x1 := g₁ _ (by decide)
  have e2 : s₁.gpr .x2 = s₀.gpr .x2 := g₁ _ (by decide)
  have back {s' : State} (ha : abiPreserved s₁ s') : abiPreserved s₀ s' :=
    ⟨fun r hr => (ha.1 r hr).trans (g₁ r (hpres r hr)), ha.2.1.trans sp₁, fun r hr => (ha.2.2 r hr).trans (v₁ r hr)⟩
  constructor
  · obtain ⟨t, s', he, ha, hq⟩ := (ecbShortFramed_verified d).1 s₁ (by
      sig_pre [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, AArch64.abi, AArch64.argRegs]
      simp only [e0, e1, e2, sp₁, rd₁, wr₁]
      exact ⟨hsp, hrd, hwr, dKD, dSK, dSD, fitK, fitD⟩)
    refine ⟨t, s', he, back ha, ?_⟩
    sig_reduce [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, AArch64.abi, AArch64.argRegs] at hq
    simpa only [ecbFewAArch64, e0, e1, e2, m₁, BitVec.setWidth_eq] using hq
  · have sub : Region.Sub ⟨s₀.sp - BitVec.ofNat 64 3184, 3184⟩ ⟨s₀.sp - BitVec.ofNat 64 3264, 3264⟩ :=
      fun x hx => Offset.below_mono s₀.sp (by decide) (by decide) x hx
    obtain ⟨t, s', he, ha, hq⟩ := ecbCall_correct (callDir d) s₁ (by
      simp only [ecbCallAArch64, e0, e1, e2, sp₁, rd₁, wr₁]
      exact ⟨by omega_using [hsp], hrd, hwr, dKD, dSK.sub_left sub, dSD.sub_left sub, fitK, fitD⟩)
    refine ⟨t, s', he, back ha, ?_⟩
    simpa only [ecbCallAArch64, ecbFewAArch64, e0, e1, e2, m₁, specDirA_callDir] using hq

theorem ecbFewTaint_agree (d : Spec.Sm4.Direction) (s₁ s₂ : State) (_ : (ecbFewAArch64 d).pre s₁)
    (_ : (ecbFewAArch64 d).pre s₂) (hp : (ecbFewAArch64 d).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem ecbFew_ct (d : Spec.Sm4.Direction) :
    ConstantTime isa (ecbFewAArch64 d).pre (ecbFewAArch64 d).pub (ecbFew d ecbAnyFramed) := by
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbFewTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbFewTaint_agree .decrypt)
      (by taint_decide)

/-- `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`: a few blocks one at a
time, or a call of `vg_sm4_ecb`; 3264 bytes of stack. -/
theorem ecbFew_verified (d : Spec.Sm4.Direction) :
    Verified AArch64.target (ecbFew d ecbAnyFramed) (Spec.Sm4.ecbContract AArch64.abi d 3264) :=
  Verified.of_correct (ecbFew_correct d) (ecbFew_ct d) (by
    cases d <;>
    sig_implies [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, ecbFewAArch64,
      AArch64.abi, AArch64.argRegs] [ecbCallSat] using ecbCallSat)

end VG.Proof.Sm4.AArch64
