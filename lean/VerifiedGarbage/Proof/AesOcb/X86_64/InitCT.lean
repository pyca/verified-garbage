import VerifiedGarbage.Proof.AesOcb.X86_64.Init
import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase

/-!
# AES-OCB on x86-64: `vg_aes_ocb_init` is constant time

Untrusted: everything here is checked by Lean. The code between the calls
passes the taint analysis from the registers that are public (the
arguments, then the key context's address, the rounds and the scratch
buffer's address); the calls have the same arguments in both runs, by
correctness (`key_rel`, `blk_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem init_rel (v : BlocksImpl) {s₀ s₀' : State} {Kp C S : Addr} {KL : Nat} (Ar : IArgs s₀ Kp C S KL)
    (Ar' : IArgs s₀' Kp C S KL)
    (hdi : s₀.gpr .rdi = Kp) (hsi : s₀.gpr .rsi = BitVec.ofNat 64 KL) (hdx : s₀.gpr .rdx = C) (hcx : s₀.gpr .rcx = S)
    (hdi' : s₀'.gpr .rdi = Kp) (hsi' : s₀'.gpr .rsi = BitVec.ofNat 64 KL) (hdx' : s₀'.gpr .rdx = C)
    (hcx' : s₀'.gpr .rcx = S) (hsp : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init (callees v)) fun _ _ => True := by
  -- The first block.
  have first : ∀ {σ : State}, IArgs σ Kp C S KL → σ.gpr .rdi = Kp → σ.gpr .rsi = BitVec.ofNat 64 KL →
      σ.gpr .rdx = C → σ.gpr .rcx = S →
      WP isa (.block [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi,
          .shift .shr .rbp 2, addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO]) σ fun s₁ =>
        KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = σ.gpr .rsp ∧ s₁.gpr .rbx = C ∧
          s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr :=
    fun A h₁ h₂ h₃ h₄ => by
      obtain ⟨s₁, run₁, rbx₁, rbp₁, r12₁, _, _, rd₁, wr₁, K₁, hsp₁⟩ := init1_ok A h₁ h₂ h₃ h₄
      exact WP.of_runBlock ⟨s₁, run₁, K₁, hsp₁, rbx₁, rbp₁, r12₁, rd₁, wr₁⟩
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (.block [st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi,
          .shift .shr .rbp 2, addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO]) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hdi, hdi']
    · rw [hsi, hsi']
    · rw [hdx, hdx']
    · rw [hcx, hcx']
    · exact hsp) hA).wp
    (F₁ := fun (s₁ : State) => KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr)
    (F₂ := fun (s₁ : State) => KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀'.gpr .rsp ∧ s₁.gpr .rbx = C ∧
      s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀'.rd ∧ s₁.wr = s₀'.wr)
    fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first Ar hdi hsi hdx hcx, first Ar' hdi' hsi' hdx' hcx'⟩
  -- The key schedule.
  have b := (key_rel v (P := fun s₁ s₂ => True ∧
      (KCall s₁ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧
        s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ∧
      (KCall s₂ Kp C (S + BitVec.ofNat 64 512) KL ∧ s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧
        s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧ s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr))
    fun s₁ s₂ h => ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1, hsp]⟩).wp
    (F₁ := fun (s₂ : State) => s₂.gpr .rsp = s₀.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
      s₂.gpr .r12 = S ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr)
    (F₂ := fun (s₂ : State) => s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
      s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr) fun s₁ s₂ h => by
      obtain ⟨_, ⟨K₁, sp₁, bx₁, bp₁, r₁, rd₁, wr₁⟩, ⟨K₂, sp₂, bx₂, bp₂, r₂, rd₂, wr₂⟩⟩ := h
      exact ⟨WP.mono (key_call v K₁) fun t P => ⟨by rw [P.saved _ (by decide), sp₁],
          by rw [P.saved _ (by decide), bx₁], by rw [P.saved _ (by decide), bp₁], by rw [P.saved _ (by decide), r₁],
          by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩,
        WP.mono (key_call v K₂) fun t P => ⟨by rw [P.saved _ (by decide), sp₂],
          by rw [P.saved _ (by decide), bx₂], by rw [P.saved _ (by decide), bp₂], by rw [P.saved _ (by decide), r₂],
          by rw [P.rd, rd₂], by rw [P.wr, wr₂]⟩⟩
  -- The zero block, enciphered.
  have third : ∀ {σ s₂ : State}, IArgs σ Kp C S KL → s₂.gpr .rsp = σ.gpr .rsp → s₂.gpr .rbx = C →
      s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) → s₂.gpr .r12 = S → s₂.rd = σ.rd → s₂.wr = σ.wr →
      WP isa (.block [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
          mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO]) s₂ fun s₃ =>
        BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
          s₃.gpr .rsp = σ.gpr .rsp ∧ s₃.gpr .r12 = S := fun A sp bx bp r rd wr => by
      obtain ⟨s₃, run₃, g₃, _, _, _, B₃, hsp₃⟩ := init3_ok A bx bp r rd wr sp
      exact WP.of_runBlock ⟨s₃, run₃, B₃, hsp₃, by rw [g₃ _ (by decide), r]⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .rsp])
      (.block [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax, mvr .rdi .rbx, mvr .rsi .rbp,
          mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1), mvr .r8 .r12, addi .r8 scrO]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have c := (RelCT.taint (A := taint) _ (fun s₁ s₂ (h : True ∧
      (s₁.gpr .rsp = s₀.gpr .rsp ∧ s₁.gpr .rbx = C ∧ s₁.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
        s₁.gpr .r12 = S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr) ∧
      (s₂.gpr .rsp = s₀'.gpr .rsp ∧ s₂.gpr .rbx = C ∧ s₂.gpr .rbp = BitVec.ofNat 64 (KL / 4 + 6) ∧
        s₂.gpr .r12 = S ∧ s₂.rd = s₀'.rd ∧ s₂.wr = s₀'.wr)) => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2.1, h.2.2.2.2.1]
      · rw [h.2.1.2.2.2.1, h.2.2.2.2.2.1]
      · rw [h.2.1.1, h.2.2.1, hsp]) hB).wp
    (F₁ := fun (s₃ : State) => BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
      s₃.gpr .rsp = s₀.gpr .rsp ∧ s₃.gpr .r12 = S)
    (F₂ := fun (s₃ : State) => BCall s₃ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧
      s₃.gpr .rsp = s₀'.gpr .rsp ∧ s₃.gpr .r12 = S) fun s₁ s₂ h => by
      obtain ⟨_, ⟨sp₁, bx₁, bp₁, r₁, rd₁, wr₁⟩, ⟨sp₂, bx₂, bp₂, r₂, rd₂, wr₂⟩⟩ := h
      exact ⟨third Ar sp₁ bx₁ bp₁ r₁ rd₁ wr₁, third Ar' sp₂ bx₂ bp₂ r₂ rd₂ wr₂⟩
  have d := (blk_rel (name := (callees v).enc.name) v.encOk v.encCt (P := fun s₁ s₂ => True ∧
      (BCall s₁ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₁.gpr .rsp = s₀.gpr .rsp ∧
        s₁.gpr .r12 = S) ∧
      (BCall s₂ C (C + BitVec.ofNat 64 240) (S + BitVec.ofNat 64 512) (KL / 4 + 6) 1 ∧ s₂.gpr .rsp = s₀'.gpr .rsp ∧
        s₂.gpr .r12 = S))
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1, hsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .r12 = S) (F₂ := fun (s : State) => s.gpr .r12 = S) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call v.encOk v.encNosp v.encDepth h.2.1.1) fun t P => by rw [P.saved _ (by decide), h.2.1.2.2],
        WP.mono (blk_call v.encOk v.encNosp v.encDepth h.2.2.1) fun t P => by rw [P.saved _ (by decide), h.2.2.2.2]⟩
  -- The registers back.
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r12])
      (.block [ld .rbx .r12 0, ld .rbp .r12 8, ld .r12 .r12 16]) hc).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) _ (fun s₁ s₂ (h : True ∧ s₁.gpr .r12 = S ∧ s₂.gpr .r12 = S) => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1, h.2.2]) hE
  unfold init
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d e)))

/-- `vg_aes_ocb_init` is constant time. -/
theorem init_ct (v : BlocksImpl) : ConstantTime isa initX86_64.pre initX86_64.pub (init (callees v)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have A₂ := IArgs.of h₂
  rw [← q1, ← q2, ← q3, ← q4] at A₂
  exact (init_rel v (IArgs.of h₁) A₂ rfl (ofNat_toNat64 _).symm rfl rfl q1.symm
    (by rw [← q2]; exact (ofNat_toNat64 _).symm) q3.symm q4.symm q5 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64
