module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsg
import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.VerifyMsg
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.Whole.Sha512OK
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# `vg_ed25519_verify` on RISC-V, with its frame as an argument: by register, and constant time

The contract by register (`verC`), from an aligned `scratch`, and the
proof against it (`ver_ok`). The contract declares the inputs public, and
two runs on the same inputs leak the same trace (`ver_ct`): the taint
analysis checks the challenge's computation (only the pointers and the
length are public to it, and they stay in `s7`–`s10`), and the call of
`verify_equation`, whose branches depend on the inputs, is related by its
own constant time and the arguments' agreement (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64.Whole

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64.Whole
open VG.Spec.Ed25519 (bytesAt)

/-- The contract by register: `pk` in `a0`, the message in `a1` (`len` in `a2`), the signature in
`a3`, `scratch` in `a4`, the frame in `a5`. -/
def verC : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let msg : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    let sig : Region := ⟨s.gpr .a3, 64⟩
    let sc : Region := ⟨s.gpr .a4, 8192⟩
    let fr : Region := ⟨s.gpr .a5, 272⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [sc, fr] ∧ (s.gpr .a4).toNat % 8 = 0 ∧ (s.gpr .a5).toNat % 8 = 0 ∧
      pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧ msg.Disjoint fr ∧ sig.Disjoint sc ∧ sig.Disjoint fr ∧
      sc.Disjoint fr ∧ s.sp.toNat % 16 = 0 ∧ 208 ≤ s.sp.toNat ∧
      (below s.sp 208).Disjoint pk ∧ (below s.sp 208).Disjoint msg ∧ (below s.sp 208).Disjoint sig ∧
      (below s.sp 208).Disjoint sc ∧ (below s.sp 208).Disjoint fr
  post s s' := (s'.gpr .a0).setWidth 32 = verResult s
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp ∧
    (bytesAt s₁.mem (s₁.gpr .a0) 32 ++ bytesAt s₁.mem (s₁.gpr .a1) (s₁.gpr .a2).toNat ++
      bytesAt s₁.mem (s₁.gpr .a3) 64).map (·.toNat) =
    (bytesAt s₂.mem (s₂.gpr .a0) 32 ++ bytesAt s₂.mem (s₂.gpr .a1) (s₂.gpr .a2).toNat ++
      bytesAt s₂.mem (s₂.gpr .a3) 64).map (·.toNat)

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s :=
  let ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o, p, q, r⟩

theorem ver_ok (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := verifyMessage_wp sha512OK (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .a0) 32 = bytesAt s₂.mem (s₂.gpr .a0) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .a3) 64 = bytesAt s₂.mem (s₂.gpr .a3) 64 := by
  obtain ⟨-, -, -, -, p2, -, -, -, -, pl⟩ := h
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [bytesAt]
  exact bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl, p2]) pl

/-- The restores, with `F` in `s10` in both runs. -/
theorem restore_ct {P : State → State → Prop}
    (hp : ∀ t₁ t₂, P t₁ t₂ → t₁.sp = t₂.sp ∧ t₁.gpr .s10 = t₂.gpr .s10) :
    RelCT isa P (.block (restoreRegs .s10 224 verifyRegs)) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.s10]) (fun t₁ t₂ h => ⟨(hp _ _ h).1, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr; exact (hp _ _ h).2⟩) (by taint_decide)

/-- Two runs' entry states. -/
abbrev VPair : Type := {σ : State × State // VP σ.1 σ.2}

theorem ver_ct : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerArgs σ.1.1 t₁ ∧ VerArgs σ.1.2 t₂) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := VerArgs) fun s₁ s₂ h =>
        ⟨verifyHash_ok sha512OK (verC_pre h.1), verifyHash_ok sha512OK (verC_pre h.2.1)⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, p0, p1, p2, p3, p4, p5, psp, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := verifyRV) verify_ok' verify_ct fun t₁ t₂ ⟨a₁, a₂⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨a₁, a₂⟩ =>
        ⟨WP.mono (verCall_ok (verC_pre σ.2.1) a₁) fun _ h => h.1,
          WP.mono (verCall_ok (verC_pre σ.2.2.1) a₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁, verCall_pre hp₂ a₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, p0, p1, p2, p3, p4, p5, psp, -⟩ := σ.2
    obtain ⟨b0, bm, b3⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b3, b0, bm]
    simp only [verifyRV, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
    rw [a₁.a0, a₂.a0, a₁.a1, a₂.a1, a₁.a2, a₂.a2, a₁.a3, a₂.a3, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      a₁.pk, a₂.pk, a₁.sig, a₂.sig, b0, b3, ch]
    exact ⟨by rw [p5], by rw [p5], p5, p4, psp, rfl⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ =>
      ⟨by rw [i₁.sp, i₂.sp]; exact σ.2.2.2.2.2.2.2.2.2.1, by
        rw [i₁.regs .s10 (by decide), i₂.regs .s10 (by decide), verV_s10, verV_s10]
        exact σ.2.2.2.2.2.2.2.2.1⟩

end VG.Proof.Ed25519.RISCV64.Whole
