module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecMain
public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCorrect
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import Mathlib.Data.Int.ModEq

/-! ### `RsaOaep.X86_64.DecPriv`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP decryption on x86-64: the private-key operation

`vg_rsa_private_checked`'s precondition with its stack arguments in the
frame (`privD_pre`), and what its call leaves (`privD_call`): `EM`'s place
in the working space holds its outcome for the ciphertext, and the frame its
words.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack privK)

/-- The base of the stack the function uses. -/
abbrev kbD (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 decStack

theorem fb_eqD (s : State) : fb s = off (kbD s) (8 + privStack) := Offset.sub_ofNat_eq _ (by decide)

theorem fb_sub8D (s : State) : fb s - 8 = off (kbD s) privStack := by
  rw [fb_eqD, off, off, show 8 + privStack = privStack + 8 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem kbD_toNat {s : State} (hp : DPre s) : (kbD s).toNat + decStack + 144 ≤ 2 ^ 64 ∧
    (kbD s).toNat + decStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kbD, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega_arith

/-- What `vg_rsa_private_checked` reads: `n`, `e`, the ciphertext, the
private key and its stack arguments. -/
def privRdD (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 13, (s.gpr .r8).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨fb s, 112⟩]

/-- The working space the call gets: ours ends at `oRsa`. -/
def rsaD (s : State) : Region := ⟨off (stackArg s 15) oRsa, (stackArg s 16 - 1024).toNat * 8⟩

/-- What it writes: `EM`'s place and the rest of the working space. -/
def privWrD (s : State) : List Region := [⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩, rsaD s]

theorem rsaD_toNat {s : State} (hp : DPre s) :
    (stackArg s 16 - 1024).toNat = (stackArg s 16).toNat - 1024 ∧
      (off (stackArg s 15) oRsa).toNat = (stackArg s 15).toNat + oRsa := by
  have := hp.hsl; have := hp.wS; have := hp.lv.1
  constructor
  · rw [BitVec.toNat_sub, show (1024 : BitVec 64).toNat = 1024 from rfl]; omega_arith
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oRsa at *; omega_arith

theorem rsaD_sub {s : State} (hp : DPre s) : Region.Sub (rsaD s) (scrD s) := by
  have := hp.hsl
  have ⟨r1, _⟩ := rsaD_toNat hp
  simp only [rsaD, scrD]; rw [r1]
  exact Offset.sub_base _ (by unfold oRsa; omega_arith)

theorem emD_sub {s : State} (hp : DPre s) : Region.Sub ⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ (scrD s) := by
  have := hp.hsl; have := hp.lv.2
  exact Offset.sub_base _ (by unfold oEm; omega_arith)

/-- The entry state's stack arguments: the frame's words. -/
theorem privD_args {s t : State} {W : Nat → BitVec 64} (hp : DPre s) (h : DCall s W t) (rd wr : List Region) {i : Nat}
    (hi : i < 14) :
    stackArg (t.callEntry.withRegions rd wr) i = privW s i := by
  have hF := fb_toNatD hp
  rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold decStack privStack frameBytes at *; omega_arith) _ _
    (by have := hp.sp2; unfold frameBytes at *; omega_arith)]
  exact (h.R.rd i rfl (by unfold nW frameBytes; omega_arith)).trans (h.hW i hi)

theorem stackArgAddr_entryD {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp]
  rw [show 8 * (0 + 1) = 8 from rfl, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]

theorem privD_pre {s t : State} {W : Nat → BitVec 64} (hp : DPre s) (h : DCall s W t) :
    privK.pre (t.callEntry.withRegions (privRdD s) (privWrD s)) := by
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRdD s) (privWrD s)) i = privW s i :=
    fun hi => privD_args hp h _ _ hi
  simp only [privK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp,
    stackArgAddr_entryD h.he.rsp, e (show 0 < 14 by decide), e (show 1 < 14 by decide), e (show 2 < 14 by decide),
    e (show 3 < 14 by decide), e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide),
    e (show 7 < 14 by decide), e (show 8 < 14 by decide), e (show 9 < 14 by decide),
    e (show 10 < 14 by decide), e (show 11 < 14 by decide), e (show 12 < 14 by decide),
    e (show 13 < 14 by decide), fb_sub8D]
  simp only [privW, upd, Nat.reduceEqDiff, ↓reduceIte]
  have ⟨hK1, hK2⟩ := kbD_toNat hp
  have ⟨r1, r2⟩ := rsaD_toNat hp
  have hk1 := hp.lv.1; have hk2 := hp.lv.2
  have hsl := hp.hsl; have wS := hp.wS
  have e5 : decStack = 3560 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 296 := rfl
  have hfb : fb s = off (kbD s) (8 + privStack) := fb_eqD s
  have sK : Region.Sub ⟨kbD s, privStack⟩ (stkD s) := Region.sub_prefix (by omega_arith)
  have sR : Region.Sub ⟨off (kbD s) privStack, 8⟩ (stkD s) := Offset.sub_base _ (by omega_arith)
  have sA : Region.Sub ⟨fb s, 112⟩ (stkD s) := by rw [hfb]; exact Offset.sub_base _ (by omega_arith)
  have dRA : (⟨off (kbD s) privStack, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have dKA : (⟨kbD s, privStack⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  have hoff : (off (kbD s) privStack).toNat = (kbD s).toNat + privStack := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  have kbsub : kbD s = off (kbD s) privStack - BitVec.ofNat 64 privStack := by
    rw [off, BitVec.add_sub_cancel]
  rw [← kbsub]
  have em := emD_sub hp
  have rs := rsaD_sub hp
  have dEmR : Region.Disjoint ⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ (rsaD s) := by
    simp only [rsaD]; rw [r1]
    exact Offset.disjoint _ (.inl (by unfold oEm oRsa; omega_arith)) (by unfold oEm; omega_arith) (by unfold oRsa; omega_arith)
  have dSK : (scrD s).Disjoint (stkD s) := hp.dKs.symm
  -- Regions apart from the working space are apart from `EM` and the call's working space.
  have dE : ∀ {r : Region}, (r).Disjoint (scrD s) →
      (⟨off (stackArg s 15) oEm, (s.gpr .r8).toNat⟩ : Region).Disjoint r ∧ r.Disjoint (rsaD s) :=
    fun h => ⟨(h.sub_right em).symm, h.sub_right rs⟩
  have dcts : (⟨stackArg s 13, (s.gpr .r8).toNat⟩ : Region).Disjoint (scrD s) := by
    have := hp.dcts; rwa [hp.hcl] at this
  have dKct : (stkD s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dKct; rwa [hp.hcl] at this
  refine ⟨by omega_arith, by omega_arith, rfl, rfl, (dE hp.dns).1, (dE hp.des).1, (dE dcts).1, (dE hp.dps).1,
    (dE hp.dqs).1, (dE hp.ddps).1, (dE hp.ddqs).1, (dE hp.dqis).1, dEmR,
    ((dSK.sub_right sA).sub_left em), (dE hp.dns).2, (dE hp.des).2, (dE dcts).2, (dE hp.dps).2,
    (dE hp.dqs).2, (dE hp.ddps).2, (dE hp.ddqs).2, (dE hp.dqis).2, ((dSK.sub_right sA).sub_left rs),
    ((dSK.symm.sub_left sR).sub_right em), hp.dKn.sub_left sR, hp.dKe.sub_left sR, dKct.sub_left sR,
    hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR, hp.dKqi.sub_left sR,
    ((dSK.symm.sub_left sR).sub_right rs), dRA, ((dSK.symm.sub_left sK).sub_right em), hp.dKn.sub_left sK,
    hp.dKe.sub_left sK, dKct.sub_left sK, hp.dKp.sub_left sK, hp.dKq.sub_left sK, hp.dKdp.sub_left sK,
    hp.dKdq.sub_left sK, hp.dKqi.sub_left sK, ((dSK.symm.sub_left sK).sub_right rs), dKA,
    by simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm; omega_arith, hp.wN, hp.wE,
    by have := hp.wC; rw [hp.hcl] at this; exact this, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi,
    by rw [r1, r2]; unfold oRsa; omega_arith, hp.lv, trivial, trivial, hp.el1, hp.el2, hp.pl1, hp.pl2, hp.ql1, hp.ql2,
    hp.hdpl, hp.hqil, hp.hdql, by rw [r1]; unfold Spec.Rsa.scratchWords; omega_arith⟩

theorem privD_covers {s t : State} {W : Nat → BitVec 64} (hp : DPre s) (h : DCall s W t) :
    Covers (privRdD s ++ privWrD s) (t.rd ++ t.wr) ∧ Covers (privWrD s) t.wr := by
  have hk2 := hp.lv.2; have hsl := hp.hsl; have hcl := hp.hcl
  have ⟨r1, r2⟩ := rsaD_toNat hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hwr := h.he.wr
  have cw : Covers (privWrD s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWrD, rsaD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hwr]
    rcases hr with rfl | rfl
    · exact ⟨scrD s, by simp, oEm, rfl, by simp only [scrD]; unfold oEm; omega_arith⟩
    · exact ⟨scrD s, by simp, oRsa, rfl, by simp only [scrD]; rw [r1]; unfold oRsa; omega_arith⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.he.rd]; exact hx)
  simp only [privRdD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨s.gpr .r9, (stackArg s 0).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 13, (stackArg s 14).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 1, (stackArg s 2).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨frR s, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self ..), 0, z _,
      by show 0 + 112 ≤ frameBytes; decide⟩

/-! ## The call -/

/-- The private-key operation's outcome for the ciphertext, from the entry
state. -/
def privOutD (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 13) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)

/-- A word of the frame, apart from what the call writes. -/
theorem frame_apartD {s : State} (hp : DPre s) {k : Nat} (hk : k < nW) :
    ∀ r ∈ privWrD s ++ [below (fb s) (8 + privStack)], (⟨off (fb s) (8 * k), 8⟩ : Region).Disjoint r := by
  have hF := fb_toNatD hp
  have := hp.sp2
  have sF : Region.Sub ⟨off (fb s) (8 * k), 8⟩ (stkD s) :=
    fun x h => frame_subD s x (Offset.sub_base _ (by unfold nW frameBytes at *; omega_arith) x h)
  intro r hr
  simp only [privWrD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.dKs.sub_left sF).sub_right (emD_sub hp)
  · exact (hp.dKs.sub_left sF).sub_right (rsaD_sub hp)
  · exact Offset.disjoint_below _ (by unfold nW frameBytes privStack at *; omega_arith)

/-- The call of a function that writes what `vg_rsa_private_checked` does
(`hk`), under its contract `k`, which the call meets (`hpre`, `hc`, `hw`)
with the regions `rds` read: the frame's words kept, `EM`'s place in the
working space holding the outcome. -/
theorem privDW_call {name : String} {code : Prog isa} {k : Contract isa} (hk : ∀ a b, k.post a b → privK.post a b)
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hspC : code.all (fun i => !isa.writesSp i) = true) (hdp : code.x86_64Depth ≤ privStack)
    {s t : State} {W : Nat → BitVec 64} (hp : DPre s) (h : DCall s W t) {rds : List Region}
    (hpre : k.pre (t.callEntry.withRegions rds (privWrD s))) (hc : Covers (rds ++ privWrD s) (t.rd ++ t.wr))
    (hw : Covers (privWrD s) t.wr) :
    WP isa (.call name code) t fun t' => EnvD s t' ∧
      (∀ {k : Nat}, k < nW → word t'.mem (fb s) (8 * k) = word t.mem (fb s) (8 * k)) ∧
      Rep t'.mem (fb s) (stackArg s 15) (fun o => t'.mem (off (stackArg s 15) o)) W ∧
      Spec.Rsa.writtenOutcome t'.mem (off (stackArg s 15) oEm) (s.gpr .r8).toNat ((t'.gpr .rax).setWidth 32)
        (privOutD s) := by
  have e2 : privStack = 3256 := rfl
  have hF := fb_toNatD hp
  refine WP.call_sp_mx (k := k) hv (SpSafe.of_all hspC) (by omega_arith) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  replace hpost := hk _ _ hpost
  rw [h.he.rsp] at hf
  have hf' : Frame (privWrD s ++ [below (fb s) (8 + privStack)]) t.mem s'.mem :=
    Frame.below_mono hf (by omega_arith) (by have := hp.sp2; unfold frameBytes at *; omega_arith)
  have hfe : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have hfE : FrD s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., below_subD s (by decide)⟩)
  have e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions rds (privWrD s)) i = privW s i :=
    fun hi => privD_args hp h _ _ hi
  have bo : ∀ {p : Addr} {len : Nat}, (stkD s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrD s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hm hs hl => FrD.bytes hfE hk ho hm hs.symm hl
  simp only [privK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rdx, h.rcx, h.r8, h.r9, hm₂,
    hg₂ .rax (by decide), e (show 0 < 14 by decide), e (show 2 < 14 by decide), e (show 3 < 14 by decide),
    e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide), e (show 8 < 14 by decide),
    e (show 10 < 14 by decide)] at hpost
  simp only [privW, upd, Nat.reduceEqDiff, ↓reduceIte] at hpost
  have hcl := hp.hcl
  have dcts : (⟨stackArg s 13, (s.gpr .r8).toNat⟩ : Region).Disjoint (scrD s) := by
    have := hp.dcts; rwa [hcl] at this
  have dKct : (stkD s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dKct; rwa [hcl] at this
  have dOct : (outR s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dOct; rwa [hcl] at this
  have dMct : (mlR s).Disjoint ⟨stackArg s 13, (s.gpr .r8).toNat⟩ := by have := hp.dMct; rwa [hcl] at this
  rw [bo hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega_arith),
    bo hp.dKe hp.dOe hp.dMe hp.des (by have := hp.wE; omega_arith),
    bo dKct dOct dMct dcts (by have := hp.wC; omega_arith),
    bo hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega_arith),
    bo hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega_arith),
    show (stackArg s 2).toNat = (stackArg s 6).toNat from hp.hdpl.symm,
    bo hp.dKdp hp.dOdp hp.dMdp hp.ddps (by have := hp.wDp; omega_arith),
    show (stackArg s 4).toNat = (stackArg s 8).toNat from hp.hdql.symm,
    bo hp.dKdq hp.dOdq hp.dMdq hp.ddqs (by have := hp.wDq; omega_arith),
    show (stackArg s 6).toNat = (stackArg s 10).toNat by rw [hp.hdpl, hp.hqil],
    bo hp.dKqi hp.dOqi hp.dMqi hp.dqis (by have := hp.wQi; omega_arith)] at hpost
  have hkeep : ∀ {k : Nat}, k < nW → word s'.mem (fb s) (8 * k) = word t.mem (fb s) (8 * k) := fun hk =>
    hf'.readW (Region.contains_self _ _) (frame_apartD hp hk) (by decide)
  have hsp' : s'.gpr .rsp = fb s := (hcs .rsp (by decide)).trans h.he.rsp
  refine ⟨⟨hsp', hrd.trans h.he.rd, hwr.trans h.he.wr, fun r hr hne => (hcs r hr).trans (h.he.cs r hr hne),
    hmx.trans h.he.mx, h.he.fr.trans (hf'.sub fun r hr => ?_)⟩, hkeep,
    ⟨fun _ _ => rfl, fun k hk => (hkeep hk).trans (h.R.fr k hk)⟩, ?_⟩
  · simp only [privWrD, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrD s, by simp, emD_sub hp⟩
    · exact ⟨scrD s, by simp, rsaD_sub hp⟩
    · exact ⟨stkD s, by simp, below_subD s (le_refl _)⟩
  · simp only [privOutD]
    rw [show (stackArg s 10).toNat = (stackArg s 2).toNat from hp.hqil,
      show (stackArg s 8).toNat = (stackArg s 4).toNat from hp.hdql] at hpost
    exact hpost

end VG.Proof.RsaOaep.X86_64

end

end

/-!
# RSAES-OAEP decryption on x86-64: correctness

The frame, the prologue, the private operation, its result to its slot and
the check of `k` (zeros to `out` and `*msg_len` if the operation failed or
`k` is too small, the decoding otherwise): `dec_correct`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HashTable.X86_64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf fnsGood_of)

/-- The private operation's result to its slot, zero-extended, and the
check of `k`. -/
theorem resK_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hk1 : k < 2 ^ 32) (hD : Hm.D < 2 ^ 20) :
    WP isa (.block (([.mov32 .rax (.reg .rax), .store (sp sR) .rax] : List Instr) ++ chkK Hm)) u fun u' =>
      Keep [.rax] u u' ∧ Lay u' F S ∧ Rep u'.mem F S V (upd W 30 (((u.gpr .rax).setWidth 32).setWidth 64)) ∧
      u'.cf = some (decide (k < 2 * Hm.D + 2)) := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun x => x.mem = u.mem.writeW (off F sR)
    (((u.gpr .rax).setWidth 32).setWidth 64)) ?_ rfl) fun x ⟨hmx, kx⟩ => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sR) (by decide)]
  have R' : Rep x.mem F S V (upd W 30 (((u.gpr .rax).setWidth 32).setWidth 64)) := by
    rw [hmx]; exact R.wf L.geo (k := 30) (by decide) _
  have L' : Lay x F S := L.of_rep' R R' (by simp [upd]) (kx.gpr (by decide)) kx.2.2
  refine WP.mono (chkK_ok L' R' (by simp only [upd]; exact hk) hk1 hD) fun u' ⟨k2, hm2, _, hcf⟩ =>
    ⟨(kx.trans k2).mono (by decide), L'.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), hm2 ▸ R', hcf⟩

theorem decKs_iff {k : Nat} (h : k ∈ decKs) : k = 14 ∨ (21 ≤ k ∧ k ≤ 29) := by
  simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega_using [h]

theorem ArgsD_privW (s : State) : ArgsD s (privW s) := fun j hj => by
  have := decKs_iff hj
  simp only [privW, upd, show j ≠ 0 by omega_using [this], show j ≠ 1 by omega_using [this], show j ≠ 2 by omega_using [this], show j ≠ 3 by omega_using [this],
    show j ≠ 4 by omega_using [this], show j ≠ 5 by omega_using [this], show j ≠ 6 by omega_using [this], show j ≠ 7 by omega_using [this], show j ≠ 8 by omega_using [this],
    show j ≠ 9 by omega_using [this], show j ≠ 10 by omega_using [this], show j ≠ 11 by omega_using [this], show j ≠ 12 by omega_using [this],
    show j ≠ 13 by omega_using [this], ↓reduceIte]

/-! ## The end -/

/-- What the function's caller sees: from a state in the frame with `out`
and `*msg_len` written as `o` says. -/
theorem decEnd_ok {s s₂ : State} (hp : DPre s) (he : EnvD s s₂) {o : Spec.Rsa.Outcome}
    (hw : Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat
      ((s₂.gpr .rax).setWidth 32) o) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧
      (abiPreserved s (freed frameBytes s₂) ∧
        Spec.RsaOaep.writtenDecrypt (freed frameBytes s₂).mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat
          (((freed frameBytes s₂).gpr .rax).setWidth 32) o) := by
  refine ⟨he.rsp, by rw [he.wr, hp.wr], ⟨fun r hr => ?_, ?_, he.mx⟩, hw⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show s₂.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [he.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else s₂.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact he.cs r hr hr'
  · have := hp.sp1; have := hp.sp2
    refine Frame.readW he.fr (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have := Offset.disjoint_below (s.gpr .rsp) (n := decStack) (d := 0) (k := 8)
        (by unfold decStack privStack Impl.RsaOaep.X86_64.frameBytes; omega_using [])
      simpa only [stkD, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
    · exact hp.dRO
    · exact hp.dRM
    · exact hp.dRs

/-- The tail for a digest length, which is all it uses of the streaming
functions' shape. -/
theorem decTail_D {G G' : Stream} (h : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [decTail, decMain, chkK, seedArgs, dbArgs, accLh, scan, tLen, clearBuf, decRet, h]

variable {vs : List MdHash} (hc : Coh vs)

/-- The tables that `decK`'s precondition says the entry state holds. -/
def DTabs (ts : List FnTable) (s : State) : Prop :=
  (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)) ∧
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 18) (FnTable.words isa s T)) ∧
    (tabFns ts).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)

/-- `decK`'s precondition, by name. -/
def DPreT (ts : List FnTable) (s : State) : Prop := DPre s ∧ DTabs ts s

include hc in
/-- After the private-key operation (whose outcome is in `m` and `r`) and
the table of the label's hash function to its slot: the rest of `decBody`,
for frame words `W` that hold the arguments. -/
theorem decAfterTab_ok {s ta : State} (hp : DPre s) (htab : DTabs (tables vs) s) {m : Mem} {r : BitVec 64}
    (hw1 : Spec.Rsa.writtenOutcome m (off (stackArg s 15) oEm) (s.gpr .r8).toNat (r.setWidth 32) (privOutD s))
    (hea : EnvD s ta) (hsy : ta.syms = s.syms) (La : Lay ta (fb s) (stackArg s 15)) {W : Nat → BitVec 64}
    (hA : ArgsD s W)
    (Ra : Rep ta.mem (fb s) (stackArg s 15) (fun o => m (off (stackArg s 15) o)) (upd W 35 (stackArg s 17)))
    (hax : ta.gpr .rax = r) {Q : State → Prop}
    (fin : ∀ s₂ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some H →
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 18) = some G → EnvD s s₂ →
      Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((s₂.gpr .rax).setWidth 32)
        (decOut H G (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) (privOutD s)) → Q s₂) :
    WP isa (seqs [.block lenLoad, byLen (fun d => decTail (ofLen d) (fnsOf vs)) lens]) ta Q := by
  obtain ⟨⟨T₁, hT₁, hheld₁⟩, ⟨T, hT, hheld⟩, hd⟩ := htab
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hidxL, hDmL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hidx, hDm⟩ := held_tableOf hheld
  have okL := tabOK_of hc hd hw₁
  have ok := tabOK_of hc hd hw
  obtain ⟨hgi, hgu, hgf⟩ := fnsGood_of vs
  have hHa : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some w₁.mgf.G := hashAt_tableOf hidxL
  have hGa : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 18) = some w.mgf.G := hashAt_tableOf hidx
  have hk1 := hp.lv.1; have hk2 := hp.lv.2
  have hD := w₁.ok.hD0; have hDN := w₁.ok.hDN; have hN := w₁.ok.N_le
  have hlen : w₁.mgf.G.len = w₁.H.D := w₁.mgf.len
  have hsD : w₁.H.stream.D = w₁.H.D := rfl
  have TL := dtabL hp hea hsy okL hmL hDmL
  have hDa : ta.mem.readW (off (stackArg s 17) 48) 64 = BitVec.ofNat 64 w₁.H.stream.D :=
    (TL.mem ta.mem (Frame.refl _ _)).2.1
  unfold seqs
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (lenLoad_ok La Ra (by simp [upd]) TL.rdD hDa))
    fun tb ⟨⟨kb, h11b, hmb, syb⟩, spb, mxb, fb'⟩ _ => ?_)
  have heb : EnvD s tb := hea.step kb.2.1 kb.2.2 spb (keep_cs3 kb (by decide)) mxb fb'
  have hDl : w₁.H.stream.D ∈ lens := by rw [hsD, ← hlen]; exact mem_lens w₁.mgf.mem
  refine byLen_ok hDl (by decide) (by have := mem_lens_lt hDl; omega_using [this]) h11b fun t1' kc hmc syc mxc => ?_
  rw [decTail_D (G := ofLen w₁.H.stream.D) (G' := w₁.H.stream) rfl]
  have he1' : EnvD s t1' := heb.step kc.2.1 kc.2.2 (kc.gpr (by simp)) (keep_cs3 kc rfl) mxc
    (by rw [hmc]; exact Frame.refl _ _)
  have hm1' : t1'.mem = ta.mem := hmc.trans hmb
  have L1' : Lay t1' (fb s) (stackArg s 15) := La.congr ((kc.gpr (by simp)).trans (kb.gpr (by decide)))
    (kc.2.2.trans kb.2.2) (by rw [hm1'])
  have R1' := hm1' ▸ Ra
  have hax' : t1'.gpr .rax = r := (kc.gpr (by simp)).trans ((kb.gpr (by decide)).trans hax)
  unfold decTail seqs
  have hW1 : ArgsD s (upd W 35 (stackArg s 17)) := hA.of fun j hj => by
    have := decKs_iff hj; simp only [upd]; rw [ifn (by omega_using [this])]
  obtain ⟨-, w21, -, w23, -, -, -, -, -, w29⟩ := hW1.w
  have w23' : upd W 35 (stackArg s 17) 23 = BitVec.ofNat 64 (s.gpr .r8).toNat := by
    rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono_syms (wp_good (block_good _ rfl) (resK_ok (Hm := w₁.H.stream) L1' R1' w23' (by omega_using [hk2])
      (by omega_using [hDN, hN, hsD])))
    fun t2 ⟨⟨k2, L2, R2, hcf2⟩, sp2, mx2, f2⟩ sy2 => ?_)
  have he2 : EnvD s t2 := he1'.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  rw [hax'] at R2
  generalize hW2 : upd (upd W 35 (stackArg s 17)) 30 ((r.setWidth 32).setWidth 64) = W2 at R2
  have hA2 : ArgsD s W2 := hW1.of fun j hj => by
    rw [← hW2]; simp only [upd]
    rw [ifn (by simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at hj; omega_using [hj])]
  have h30 : W2 30 = (r.setWidth 32).setWidth 64 := by rw [← hW2]; simp [upd]
  have h35 : W2 35 = stackArg s 17 := by rw [← hW2]; simp [upd]
  -- The private operation's outcome, in our working space and slot 30.
  have hres : ResD (fun o => m (off (stackArg s 15) o)) W2 (s.gpr .r8).toNat (privOutD s) := by
    revert hw1
    cases privOutD s with
    | ok em =>
      rintro ⟨hr, hb⟩
      refine ⟨by rw [h30, hr]; rfl, ?_⟩
      rw [← hb]; simp only [Spec.Rsa.bytesAt, off]
      refine List.map_congr_left fun i _ => ?_
      rw [show oEm = 0 from rfl, Nat.zero_add, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    | invalid => rintro ⟨hr, -⟩; show W2 30 = 0; rw [h30, hr]; rfl
    | fault => rintro ⟨hr, -⟩; show W2 30 = 2; rw [h30, hr]; rfl
  have hlenO : ∀ em, privOutD s = .ok em → em.length = (s.gpr .r8).toNat := fun em he => by
    rw [he] at hw1; rw [← hw1.2]; simp [Spec.Rsa.bytesAt]
  refine WP.ite (M := isa) _ (show isa.eval .b t2 = _ from hcf2) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    obtain ⟨-, x21, -, x23, -, -, -, -, -, x29⟩ := hA2.w
    have hout : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by simp [outR, hp.hsi]
    have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by have := hp.hsl; unfold oRsa; omega_using [this])
    have aO : Apart (fb s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by
      rw [hout]; exact ⟨hp.dKO.sub_left (frame_subD s), hp.dOs.symm.sub_left sS, hp.dKO.sub_left (ret_subD s)⟩
    have aM : Apart (fb s) (stackArg s 15) (mlR s) :=
      ⟨hp.dKM.sub_left (frame_subD s), hp.dMs.symm.sub_left sS, hp.dKM.sub_left (ret_subD s)⟩
    have dom : Region.Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ ⟨s.gpr .rdx, 8⟩ := by
      have := hp.dOM; rw [hp.hsi] at this; exact this
    refine WP.mono (wp_good decFail_good (decFail_ok L2 R2 (o := s.gpr .rdi) (pm := s.gpr .rdx)
      (k := (s.gpr .r8).toNat) x21 x29 (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega_using [hk1]) hk2 (by rw [he2.wr, hout]; simp) (by have := hp.wO; rw [hp.hsi] at this; exact this) aO
      (by rw [he2.wr]; simp [mlR]) hp.wM aM dom))
      fun t3 ⟨⟨L3, k3, R3, hz3, hm3, _, hax3⟩, sp3, mx3, f3⟩ => fin t3 _ _ hHa hGa (he2.step k3.2.1 k3.2.2 sp3
        (keep_cs3 k3 (by decide)) mx3 f3) ?_
    rw [decOut_short hlenO (by rw [hlen, ← hsD]; exact hb)]
    revert hres hlenO
    cases privOutD s with
    | ok em =>
      rintro ⟨hr, -⟩ -
      refine ⟨by rw [hax3, faultW, hr]; rfl, hz3, hm3⟩
    | invalid =>
      intro hr _
      refine ⟨by rw [hax3, faultW, show W2 30 = 0 from hr]; rfl, hz3, hm3⟩
    | fault =>
      intro hr _
      refine ⟨by rw [hax3, faultW, show W2 30 = 2 from hr]; rfl, hz3, hm3⟩
  · rw [decide_eq_false_iff_not] at hb
    exact WP.mono (decMain_ok w₁.ok w.ok w₁.mgf w.mgf hgi hgu hgf hp he2 (sy2.trans (syc.trans (syb.trans hsy)))
      okL hmL hDmL ok hm hDm L2 R2 hA2 h35 (by omega_using [hsD, hb]) hres)
      fun t3 ⟨he3, hw3⟩ => fin t3 _ _ hHa hGa he3 hw3

/-- What `decEnd_ok` gives at the end, for the tables' hash functions. -/
theorem decFinAt {s s₂ : State} (hp : DPre s) {H G : Spec.Mgf1.Hash}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some H)
    (hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 18) = some G) (he : EnvD s s₂)
    (hw : Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((s₂.gpr .rax).setWidth 32)
      (decOut H G (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) (privOutD s))) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧
      (abiPreserved s (freed frameBytes s₂) ∧ (decK (tables vs)).post s (freed frameBytes s₂)) := by
  have hct : (Spec.Rsa.bytesAt s.mem (stackArg s 13) (s.gpr .r8).toNat).length =
      (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).length := by simp [Spec.Rsa.bytesAt]
  obtain ⟨a, b, c, d⟩ := decEnd_ok hp he hw
  refine ⟨a, b, c, fun H' G' hH' hG' => ?_⟩
  rw [hH] at hH'
  rw [hG] at hG'
  obtain rfl := Option.some.inj hH'
  obtain rfl := Option.some.inj hG'
  rw [decrypt_eq hct]; exact d

/-- `EnvD`, whatever the frame's bytes hold once released. -/
theorem EnvD.lost {s s₂ : State} (he : EnvD s s₂) {m : Mem} {u : Nat → BitVec 64}
    (fm : Frame [⟨fb s, frameBytes⟩] s₂.mem m) : EnvD s { s₂ with mem := m, unknowns := u } :=
  he.step rfl rfl rfl (fun _ _ _ => rfl) rfl (fm.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [he.wr]; simp)

/-- What `out` and `*msg_len` hold, whatever the frame's bytes hold once released. -/
theorem DPre.written_lost {s : State} (hp : DPre s) {m₁ m₂ : Mem}
    (fm : Frame [⟨fb s, frameBytes⟩] m₁ m₂) {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hw : Spec.RsaOaep.writtenDecrypt m₁ (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat r o) :
    Spec.RsaOaep.writtenDecrypt m₂ (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat r o := by
  have hsi := hp.hsi
  have hb := Proof.Rsa.rsa_bytes_frame fm (s.gpr .r8).isLt (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    have := (hp.dKO.sub_left (frame_subD s)).symm
    rwa [hsi] at this)
  have hr : m₂.readW (s.gpr .rdx) 64 = m₁.readW (s.gpr .rdx) 64 :=
    fm.readW (r := mlR s) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hp.dKM.sub_left (frame_subD s)).symm) (by decide)
  cases o <;> simp only [Spec.RsaOaep.writtenDecrypt] at hw ⊢ <;> rw [hb, hr] <;> exact hw

/-- `decFinAt`, whatever the frame's bytes hold once released. -/
theorem decFin {s s₂ : State} (hp : DPre s) {H G : Spec.Mgf1.Hash}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 17) = some H)
    (hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 18) = some G) (he : EnvD s s₂)
    (hw : Spec.RsaOaep.writtenDecrypt s₂.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((s₂.gpr .rax).setWidth 32)
      (decOut H G (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) (privOutD s))) :
    s₂.gpr .rsp = fb s ∧ s₂.wr = (allocState frameBytes s).wr ∧ ∀ m u, Frame [⟨fb s, frameBytes⟩] s₂.mem m →
      abiPreserved s { freed frameBytes s₂ with mem := m, unknowns := u } ∧
        (decK (tables vs)).post s { freed frameBytes s₂ with mem := m, unknowns := u } := by
  refine ⟨he.rsp, by rw [he.wr, hp.wr], fun m u fm => ?_⟩
  exact (decFinAt hp hH hG (he.lost (u := u) fm) (hp.written_lost fm hw)).2.2

end VG.Proof.RsaOaep.X86_64
