module

public import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.VerifyMsg
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Calls
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.VerifyMsg
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.SignCT
meta import VerifiedGarbage.Proof.Ed448.RISCV64.VCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Ed448.RISCV64.Whole.Calls
meta import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
public import VerifiedGarbage.Impl.Ed448.RISCV64.Whole
public import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# `vg_ed448_verify` on RISC-V in constant time

As on PPC64LE (`Proof/Ed448/PPC64LE/Whole/VerifyCT.lean`): two runs from
states that satisfy `VerPre` and agree on the arguments in registers, the
stack pointer and the inputs (`VPubB`) leak the same trace
(`verifyMessage_ct`): the length check and the branch on it from `ctxlen`,
the setup from the arguments, the challenge by `hash_then` (the hash, then
the reduction and the arguments of `verify_equation` from `s1` and `s11`),
the call of `verify_equation` by its own constant time, which needs its
pointers and the bytes they point at, the copies of the public key and the
signature and the challenge, to agree (`veqK`, `RelCT.callEx`): the same
inputs give the same challenge (`vB_eq`). Then the restores from `F` in
`s11`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64.Whole
open VG.Spec.Ed448 (bytesAt)

/-- What two runs agree on: the arguments in registers and the stack pointer. -/
def VPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp

theorem verV_eq {s₁ s₂ : State} (hp : VPub s₁ s₂) : ∀ r ∈ verifyRegs, verV s₁ r = verV s₂ r := by
  obtain ⟨-, p1, p2, p3, p4, -, p6, p7, -⟩ := hp
  intro r hr
  simp only [verifyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [p6, p1, p2, p3, p4, p7]

theorem vinv_regs {s₁ s₂ a b : State} (hp : VPub s₁ s₂) (ha : VInv s₁ a) (hb : VInv s₂ b) :
    ∀ r ∈ verifyRegs, a.gpr r = b.gpr r := fun r hr =>
  (ha.regs r hr).trans ((verV_eq hp r hr).trans (hb.regs r hr).symm)

theorem vinv_sp {s₁ s₂ a b : State} (hp : VPub s₁ s₂) (ha : VInv s₁ a) (hb : VInv s₂ b) : a.sp = b.sp :=
  ha.sp.trans (hp.2.2.2.2.2.2.2.2.trans hb.sp.symm)

/-- `verify_equation`'s contract. -/
abbrev veqK : Contract isa := Proof.Ed448.RISCV64.verifyRISCV64

/-- What two runs agree on: the arguments, the stack pointer and the inputs. -/
def VPubB (s₁ s₂ : State) : Prop :=
  VPub s₁ s₂ ∧ (vpkB s₁ ++ vctxB s₁ ++ vmsgB s₁ ++ vsigB s₁).map (·.toNat) =
    (vpkB s₂ ++ vctxB s₂ ++ vmsgB s₂ ++ vsigB s₂).map (·.toNat)

/-- The inputs, so `k`, agree. -/
theorem vB_eq {s₁ s₂ : State} (hp : VPubB s₁ s₂) : vpkB s₁ = vpkB s₂ ∧ vsigB s₁ = vsigB s₂ ∧ vkB s₁ = vkB s₂ := by
  obtain ⟨⟨-, p1, p2, p3, p4, p5, -, -, -⟩, hb⟩ := hp
  have hi : Function.Injective (fun x : Byte => x.toNat) := fun x y hxy => BitVec.eq_of_toNat_eq hxy
  have e := List.map_injective_iff.mpr hi hb
  have l1 : (vpkB s₁).length = (vpkB s₂).length := by simp [bytesAt]
  have l2 : (vctxB s₁).length = (vctxB s₂).length := by simp [bytesAt, p2]
  have l3 : (vmsgB s₁).length = (vmsgB s₂).length := by simp [bytesAt, p4]
  obtain ⟨e1, e4⟩ := List.append_inj e (by simp [l1, l2, l3])
  obtain ⟨e1, e3⟩ := List.append_inj e1 (by simp [l1, l2])
  obtain ⟨e1, e2⟩ := List.append_inj e1 l1
  refine ⟨e1, e4, ?_⟩
  have t : ∀ s : State, bytesAt s.mem (s.gpr .a5) 57 = (vsigB s).take 57 := fun s =>
    (Proof.Ed448.RISCV64.bytes_take s.mem _).symm
  simp only [vkB]
  rw [t s₁, t s₂, e4, e2, e1, e3]

/-- The regions `verify_equation` is given: the copies of `pk` and the signature, and `k`, in `F`. -/
abbrev veqRd (s : State) : List Region :=
  [⟨s.gpr .a7 + BitVec.ofNat 64 320, 57⟩, ⟨s.gpr .a7 + BitVec.ofNat 64 200, 114⟩,
    ⟨s.gpr .a7 + BitVec.ofNat 64 136, 57⟩]

/-- The narrowed state `verify_equation` starts in, and its regions' cover. -/
theorem veq_pre {s t : State} (hp : VerPre s) (h : VArgs s t) :
    veqK.pre (t.callEntry.withRegions (veqRd s) [vscR s]) ∧
    Covers (veqRd s ++ [vscR s]) (t.rd ++ t.wr) ∧ Covers [vscR s] t.wr := by
  have hW : Covers [vscR s] t.wr := fun a n ⟨r, hr, hc⟩ => by
    rw [List.mem_singleton.mp hr] at hc; exact ⟨_, vC hp h.inv, hc⟩
  refine ⟨⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
      ce_gpr _ _ _ (by decide), h.a0, h.a1, h.a2],
    by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), h.a3],
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.a0, h.a3]; exact vfsc hp (by decide),
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.a1, h.a3]; exact vfsc hp (by decide),
    by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h.a2, h.a3]; exact vfsc hp (by decide)⟩, ?_, hW⟩
  intro a n ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cov_right (cov_in (vF hp h.inv) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  · exact cov_right hW a n ⟨_, List.mem_singleton_self _, hc⟩

/-- The length checked into `t0`. -/
abbrev VLen (s u : State) : Prop := Upd s u .t0 (s.gpr .a2 >>> 8)

theorem verifyMessage_ct (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa VerPre VPubB verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.mono (P := fun a b => ∃ x : State × State, a = x.1 ∧ b = x.2 ∧ VerPre x.1 ∧ VerPre x.2 ∧
    VPubB x.1 x.2) (RelCT.exists_ fun ⟨s₁, s₂⟩ => ?_) (fun a b h => ⟨(a, b), rfl, rfl, h⟩) (fun _ _ h => h)
  by_cases hH : VerPre s₁ ∧ VerPre s₂ ∧ VPubB s₁ s₂
  swap
  · exact RelCT.of_false fun a b h => hH h.2.2
  obtain ⟨hp₁, hp₂, hpubB⟩ := hH
  obtain ⟨ek, es, ec⟩ := vB_eq hpubB
  have hpub := hpubB.1
  refine RelCT.mono (P := fun a b => a = s₁ ∧ b = s₂) ?_ (fun a b h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)
  have pub := hpub
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, psp⟩ := pub
  unfold verifyMessage verifyMain verifyHash
  -- The length check.
  refine RelCT.seq (R := fun a b => VLen s₁ a ∧ VLen s₂ b)
    (RelCT.mono (relct_wp (ct_prog [.a2] (fun a b hab => by rw [hab.1, hab.2, psp])
      (fun a b hab r hr => by rw [List.mem_singleton.mp hr, hab.1, hab.2, p2]) (by taint_decide)) fun a b hab =>
      ⟨by rw [hab.1]; exact wp_srl (by decide) fun u hu => WP.block_nil hu,
       by rw [hab.2]; exact wp_srl (by decide) fun u hu => WP.block_nil hu⟩) (fun _ _ h => h)
      fun _ _ h => h) ?_
  refine RelCT.ite (fun a b hab => by rw [eval_zero, eval_zero, hab.1.gpr, hab.2.gpr, p2]) ?_ ?_
  · -- The challenge.
    refine RelCT.seq (R := fun a b => VArgs s₁ a ∧ VArgs s₂ b) ?_ ?_
    · refine RelCT.seq (R := fun a b => V1 s₁ a ∧ V1 s₂ b)
        (relct_wp (ct_prog [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] (fun a b hab => by
          rw [hab.1.1.sp, hab.1.2.sp, psp]) (fun a b hab r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rw [hab.1.1.other _ (by decide), hab.1.2.other _ (by decide)] <;>
            with_reducible assumption) (by taint_decide)) fun a b hab =>
          ⟨verSetup_ok hp₁ hab.1.1, verSetup_ok hp₂ hab.1.2⟩) ?_
      exact relct_wp (hash_then (by taint_decide) (fun a b h => ⟨(h.1.hashOk hp₁).1, (h.2.hashOk hp₂).1,
          vinv_sp hpub h.1.inv h.2.inv, fun r hr => vinv_regs hpub h.1.inv h.2.inv r (by revert r hr; decide)⟩)
        [.s1, .s11] (fun a b h r hr =>
          ⟨verifyRegs_pres r (by revert r; decide), vinv_regs hpub h.1.inv h.2.inv r (by revert r; decide)⟩)
        (by taint_decide)) fun a b hab => ⟨verHash_ok hp₁ hab.1, verHash_ok hp₂ hab.2⟩
    -- The call of `verify_equation`, then the restores.
    refine RelCT.seq (R := fun a b => VInv s₁ a ∧ VInv s₂ b)
      (relct_wp (RelCT.callEx (k := veqK) (Proof.Ed448.RISCV64.verifyEquation_ok hR)
        (Proof.Ed448.RISCV64.verifyEquation_ct hR) fun t₁ t₂ ⟨a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨a₁, a₂⟩ =>
        ⟨WP.mono (verCall_ok hR hp₁ a₁) fun _ h => h.1, WP.mono (verCall_ok hR hp₂ a₂) fun _ h => h.1⟩)
      (ct_prog [.s11] (fun a b hab => vinv_sp hpub hab.1 hab.2)
        (fun a b hab r hr => by rw [List.mem_singleton.mp hr]; exact vinv_regs hpub hab.1 hab.2 _ (by decide))
        (by taint_decide))
    obtain ⟨q₁, c₁, w₁⟩ := veq_pre hp₁ a₁
    obtain ⟨q₂, c₂, w₂⟩ := veq_pre hp₂ a₂
    refine ⟨_, _, _, _, q₁, q₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.a0, a₂.a0, p7]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.a1, a₂.a1, p7]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.a2, a₂.a2, p7]
    · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.a3, a₂.a3, p6]
    · rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, a₁.inv.sp,
        a₂.inv.sp, psp]
    · simp only [State.withRegions_mem, State.callEntry_mem]
      rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), a₁.a0, a₂.a0, a₁.a1, a₂.a1, a₁.a2, a₂.a2, a₁.pk, a₂.pk,
        a₁.sg, a₂.sg, a₁.ch, a₂.ch, ek, es, ec]
  · -- `ctxlen ≥ 256`.
    exact ct_prog [] (fun a b hab => by rw [hab.1.1.sp, hab.1.2.sp, psp])
      (fun _ _ _ r hr => absurd hr List.not_mem_nil) (by taint_decide)

end VG.Proof.Ed448.RISCV64.Whole
