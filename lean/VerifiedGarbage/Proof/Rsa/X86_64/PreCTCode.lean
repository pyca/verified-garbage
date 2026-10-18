module

public import VerifiedGarbage.Proof.Rsa.X86_64.PreCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.PreCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.PreCode
meta import VerifiedGarbage.Proof.Rsa.X86_64.PreCode
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_precompute` on x86-64: constant time

Runs that agree on the public data (the pointers, the lengths and `n`) leak
the same: `entry` from `rsp` and then the working space's base, the modulus'
check from `n`'s pointer and length, the branch on its validity, `failZ`
from `pre`'s pointer and length, and `main` (`ppCode_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit invalid)

/-- The public data of `vg_rsa_private_precompute`. -/
structure PCPub where
  q : PPub
  rsp : Addr
  nb : List Byte

/-- A state the contract allows, with the public data `p`. -/
def PpRel (p : PCPub) (s : State) : Prop :=
  ppContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 2 = p.q.m.kp.B ∧
    (stackArg s 3).toNat * 8 = p.q.m.kp.Z ∧ (s.gpr .rcx).toNat = p.q.m.k ∧ s.gpr .rdx = p.q.m.np ∧
    s.gpr .rdi = p.q.op ∧ (s.gpr .rsi).toNat = p.q.L ∧ s.gpr .r8 = p.q.m.kp.pp ∧
    (s.gpr .r9).toNat = p.q.m.kp.pl ∧ stackArg s 0 = p.q.m.kp.pq ∧ (stackArg s 1).toNat = p.q.m.kp.ql ∧
    p.q.m.kp.pd = p.q.m.np ∧ p.q.m.kp.dl = p.q.m.k ∧ p.q.m.kp.pdp = p.q.m.kp.pp ∧
    p.q.m.kp.pqi = p.q.m.kp.pp ∧ p.q.m.kp.pdq = p.q.m.kp.pq ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = p.nb ∧ p.q.m.kp.w = (p.q.m.k + 7) / 8

theorem ppEntry_split : Impl.Rsa.X86_64.PrivPre.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ Impl.Rsa.X86_64.PrivPre.entry.drop 1 :=
  rfl

/-- After `entry` and the modulus' check. -/
def PpAfter (s t : State) : Prop :=
  ∃ t₁, PpEntryPost s (stackArg s 2) t₁ ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat) ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t

/-- After `entry`'s first instruction. -/
def PC1 (p : PCPub) (t : State) : Prop :=
  ∃ s, PpRel p s ∧ t.gpr .r11 = p.q.m.kp.B ∧ t.gpr .rsp = p.rsp ∧ t.gpr .rdx = p.q.m.np ∧
    t.gpr .rcx = BitVec.ofNat 64 p.q.m.k ∧
    WP isa (.block (Impl.Rsa.X86_64.PrivPre.entry.drop 1 ++ invalid)) t (PpAfter s)

/-- After the modulus' check. -/
def PC2 (p : PCPub) (t : State) : Prop := ∃ s, PpRel p s ∧ PpAfter s t

theorem ppHead_ok {s : State} (c : PpArgs s) :
    WP isa (.block (Impl.Rsa.X86_64.PrivPre.entry ++ invalid)) s (PpAfter s) := by
  have hZ := c.hZ
  have := c.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (ppEntry_ok rfl hw c.ha c.hsep) fun t₁ h₁ => ?_
  have in₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside h₁.out (by omega)
  have nb₁ := c.nb.congrK in₁ h₁.keep
  exact WP.mono (invalid_ok (s := t₁) (nb := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (h₁.keep.gpr (by decide)) (by rw [h₁.keep.gpr (by decide), ofNat_toNat64]) c.k1 c.k2 (bytesAt_length _ _ _)
    (fun i hi => nb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => nb₁.val i _))
    fun t₂ ⟨hz₂, hm₂, k₂⟩ => ⟨t₁, h₁, hz₂, hm₂, k₂⟩

theorem PpAfter.rdi {s t : State} (h : PpAfter s t) : t.gpr .rdi = stackArg s 2 :=
  let ⟨_, h₁, _, _, k⟩ := h; (k.gpr (by decide)).trans h₁.rdi

/-- `main`'s hypotheses, after the checks, for a valid modulus. -/
theorem toP0 {p : PCPub} {t : State} (h : PC2 p t ∧ isa.eval .ne t = some false) : P0 p.q t := by
  obtain ⟨⟨s, hs, t₁, h₁, hz, hm, k⟩, he⟩ := h
  have c := ppArgs_of hs.1
  obtain ⟨-, -, hB, hZ, hk, hnp, hop, hL, hpp, hpl, hpq, hql, hpd, hdl, hpdp, hpqi, hpdq, hnb, hw⟩ := hs
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
      (s.gpr .rcx).toNat = true := by
    simp only [eval, hz] at he; simpa using he
  have hmp := c.mainPre h₁ hm k hv
  have := c.k1
  have := c.k2
  have := c.pl2
  have := c.ql2
  have hZ' := c.hZ
  have hLv := c.hL
  unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hLv
  have kk := h₁.keep.trans k
  refine ⟨?_, by rw [hm, ← hB, h₁.hE, hop], by rw [hm, ← hB, h₁.hEl, ← hL, ofNat_toNat64], by rw [← hL, hLv, hw, ← hk, ← hpl, ← hql],
    by rw [hw]; omega, by rw [hw]; omega, by rw [hw, ← hpl]; omega, by rw [hw, ← hql]; omega,
    by rw [hw, ← hL, ← hZ, hLv]; unfold slot hdrBytes Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega,
    fun i hi => by rw [kk.2.2, ← hop]; exact c.hpw i (by omega), fun i hi => by rw [← hB, ← hZ, ← hop]; exact c.hps i (by omega)⟩
  unfold M0
  rw [hpd, hdl, hpdp, hpqi, hpdq]
  rw [hB, hZ, hk, hnp, hpp, hpq] at hmp
  exact ⟨_, _, _, _, _, _, _, _, hmp, hw, by rw [bytesAt_length], by rw [bytesAt_length, hpl],
    by rw [bytesAt_length, hql]⟩

theorem ppCode_ct : RelCT isa (Two PpRel) Impl.Rsa.X86_64.PrivPre.code fun _ _ => True := by
  unfold Impl.Rsa.X86_64.PrivPre.code
  refine RelCT.seq (R := Two PC2) ?_ ?_
  · rw [ppEntry_split, List.append_assoc]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := PC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp, .rdx, .rcx] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, d₁, _⟩ ⟨_, _, a₂, b₂, c₂, d₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]
        · rw [c₁, c₂]
        · rw [d₁, d₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := ppArgs_of hs.1
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 24 })] ++
        (Impl.Rsa.X86_64.PrivPre.entry.drop 1 ++ invalid))) s (PpAfter s) := by
      rw [← List.append_assoc, ← ppEntry_split]; exact ppHead_ok c
    have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
    have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
    obtain ⟨-, hsp, hB, -, hk, hnp, -⟩ := id hs
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
      (by xrun [State.ea, e2, c.ha 2 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hB, (k.gpr (by decide)).trans hsp, (k.gpr (by decide)).trans hnp,
          by rw [k.gpr (by decide), ← hk, ofNat_toNat64], hw⟩
  refine two_ite (fun p s₁ s₂ ⟨σ₁, c₁, a₁⟩ ⟨σ₂, c₂, a₂⟩ => ?_) ?_ ?_
  · obtain ⟨_, _, z₁, _⟩ := a₁
    obtain ⟨_, _, z₂, _⟩ := a₂
    obtain ⟨-, -, -, -, k₁, -, -, -, -, -, -, -, -, -, -, -, -, n₁, -⟩ := c₁
    obtain ⟨-, -, -, -, k₂, -, -, -, -, -, -, -, -, -, -, -, -, n₂, -⟩ := c₂
    simp only [eval]
    rw [z₁, z₂, n₁, n₂, k₁, k₂]
  · -- `failZ`.
    unfold Impl.Rsa.X86_64.PrivPre.failZ
    refine RelCT.seq (two_piece (Ψ := fun (p : PCPub) t => RegsAre [(.rbx, p.q.op), (.r12, BitVec.ofNat 64 p.q.L),
        (.rdi, p.q.m.kp.B)] t) [.rdi]
      (pins_of (fun (p : PCPub) _ => p.q.m.kp.B) fun _ _ h r hr => by
        obtain ⟨⟨s, hs, ha⟩, -⟩ := h
        simp only [List.mem_singleton] at hr; subst hr; rw [ha.rdi, hs.2.2.1])
      (by taint_decide) fun p t h => ?_)
      (two_taint [.rbx, .r12, .rdi] (pins_regsAre (fun (p : PCPub) => [(.rbx, p.q.op),
        (.r12, BitVec.ofNat 64 p.q.L), (.rdi, p.q.m.kp.B)]) (fun _ => rfl) fun _ _ h => h) (by taint_decide))
    obtain ⟨⟨s, hs, ha⟩, -⟩ := h
    have c := ppArgs_of hs.1
    have hdi := ha.rdi
    obtain ⟨t₁, h₁, -, hm, k⟩ := ha
    have hZ := c.hZ
    have := c.k1
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * i)) 8 := fun i hi => by
      rw [(h₁.keep.trans k).2.1, (h₁.keep.trans k).2.2]; exact c.hs.ld (by omega)
    obtain ⟨-, -, hB, -, -, -, hop, hL, -⟩ := hs
    refine WP.mono (WP.keep [.rbx, .r12, .rax] (Q := fun u => u.gpr .rbx = p.q.op ∧
        u.gpr .r12 = BitVec.ofNat 64 p.q.L ∧ u.gpr .rdi = p.q.m.kp.B) (by
      xrun [State.ea, hdr, hdi, hdrOff, hl sE (by decide), hl sElen (by decide), hm, h₁.hE, h₁.hEl]
      exact ⟨hop, by rw [← hL, ofNat_toNat64], hB⟩) rfl) fun u ⟨⟨a, b, d⟩, _⟩ =>
        regsAre_cons a (regsAre_cons b (regsAre_cons d regsAre_nil))
  · exact preMain_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p.q, toP0 h₁, toP0 h₂⟩) h)
      fun _ _ h => h

/-- The public data of a state. -/
def ppPubOf (s : State) : PCPub :=
  ⟨⟨⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, ((s.gpr .rcx).toNat + 7) / 8, s.gpr .rdx, s.gpr .r8, stackArg s 0,
    s.gpr .r8, stackArg s 0, s.gpr .r8, (s.gpr .rcx).toNat, (s.gpr .r9).toNat, (stackArg s 1).toNat⟩,
    s.gpr .rdx, (s.gpr .rcx).toNat⟩, s.gpr .rdi, (s.gpr .rsi).toNat⟩, s.gpr .rsp,
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩

/-- `vg_rsa_private_precompute` is constant time but for `n`. -/
theorem ppCode_constantTime :
    ConstantTime isa ppContract.pre ppContract.pub Impl.Rsa.X86_64.PrivPre.code := by
  refine RelCT.constantTime (ppCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨ppPubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a2.symm, congrArg (·.toNat * 8) a3.symm, congrArg BitVec.toNat (r .rcx (by decide)),
      r .rdx (by decide), r .rdi (by decide), congrArg BitVec.toNat (r .rsi (by decide)), r .r8 (by decide),
      congrArg BitVec.toNat (r .r9 (by decide)), a0.symm, congrArg BitVec.toNat a1.symm, rfl, rfl, rfl, rfl, rfl,
      hn.symm, rfl⟩

end VG.Proof.Rsa.X86_64.Key
