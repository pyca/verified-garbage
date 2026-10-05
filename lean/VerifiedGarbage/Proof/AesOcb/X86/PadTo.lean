import VerifiedGarbage.Proof.AesOcb.X86.Nonce

/-!
# AES-OCB on x86: a padded block (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d cO` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `esi`, `n` at `W + cO`, to `W + d`:
zeros, the bytes (`copyLoop`), and `0x80` after them (`padTo_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 copyLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 LoopPre CopyPost
  copyLoop_ok length_bytesAt)

/-- A buffer of `n` bytes at `S` that the code may read. -/
structure SBuf (p : Prm) (s : State) (S : BitVec 32) (n : Nat) : Prop where
  fit : S.toNat + n ≤ 2 ^ 32
  w : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)

theorem SBuf.of_eq {p : Prm} {s s' : State} {S : BitVec 32} {n : Nat} (h : SBuf p s S n) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : SBuf p s' S n := ⟨h.fit, h.w, by rw [hrd, hwr]; exact h.rd⟩

/-- The head of `padTo`: `W + d` zeroed, the copy's arguments. -/
theorem padToHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {S : BitVec 32} {n d cO : Nat}
    (hd : d + 16 ≤ 2560) (hc : cO + 4 ≤ 2560) (hcd : cO + 4 ≤ d ∨ d + 16 ≤ cO)
    (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W cO = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa (zero4 d ++
      ([.mov .edi (.reg .esi), .mov .edx (.reg .ebp), .alu .add .edx (imm d), .mov .ecx (slot cO)] : List Instr)) s =
        some s₁ ∧
      s₁.mem = Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 d) ∧ s₁.gpr .edi = S ∧
      s₁.gpr .edx = p.W + BitVec.ofNat 32 d ∧ s₁.gpr .ecx = BitVec.ofNat 32 n ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hz := zero4_fold s.mem p.W d
  have hcnt' : (Proof.Cmac.zero4 s.mem (w64 p.W + BitVec.ofNat 64 d)).readW (w64 p.W + BitVec.ofNat 64 cO) 32 =
      BitVec.ofNat 32 n := by
    rw [← hcnt, slotv_eq]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).readW (r := ⟨w64 p.W + BitVec.ofNat 64 cO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w hcd hc hd) (by decide)
  exact ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hsi, hcnt', hz], by gmems [hz], by gregs [hsi],
    by gregs [E.ebp], by gregs [hcnt', hz], fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [],
    by gmems []⟩

/-- `padTo d cO`: `W + d ← pad(S)`, for the `n` bytes `S` at `esi`, `0 < n < 16`. -/
theorem padTo_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {S : BitVec 32} {n d cO : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (hc : cO + 4 ≤ 2560) (hcd : cO + 4 ≤ d ∨ d + 16 ≤ cO)
    (hsi : s.gpr .esi = S) (hcnt : slotv s.mem p.W cO = BitVec.ofNat 32 n) (hS : SBuf p s S n) :
    WP isa (padTo d cO) s fun t => Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) = pad (bytesAt s.mem (w64 S) n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have aD : w64 (p.W + BitVec.ofNat 32 d) = w64 p.W + BitVec.ofNat 64 d := L.aW (by omega)
  obtain ⟨s₁, run₁, m₁, di₁, dx₁, cx₁, g₁, rd₁, wr₁⟩ := padToHead_ok L E hd hc hcd hsi hcnt
  have fr₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 d, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have eS : bytesAt s₁.mem (w64 S) n = bytesAt s.mem (w64 S) n :=
    Proof.AesGcm.X86.bytesAt_frame fr₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS.w.sub_right (Lay.wSub hd)) (by omega)
  have lp : LoopPre s₁ S (p.W + BitVec.ofNat 32 d) n :=
    ⟨di₁, dx₁, cx₁, hn, by omega, hS.fit, by rw [L.nW (by omega)]; have := L.ww; omega,
      by rw [rd₁, wr₁]; exact hS.rd, by rw [aD, wr₁]; exact E.perm.wC (by omega),
      by rw [aD]; exact hS.w.sub_right (Lay.wSub (by omega))⟩
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₁ lp) fun s₂ P₂ => ?_)
  have aN : w64 (p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n := by
    rw [show p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0 = p.W + BitVec.ofNat 32 (d + n) by
      rw [BitVec.add_zero, Proof.AesGcm.X86.add_ofNat_assoc32], L.aW (by omega), add_ofNat_assoc]
  have w₂ : InRegions s₂.wr (w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [P₂.wr, wr₁, add_ofNat_assoc]; exact E.perm.wW (by omega)
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.mov .eax (imm 0x80), .store8 (at_ .edx 0) .al] s₂ =
      some s₃ ∧ s₃.mem = s₂.mem.writeW (w64 p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) (0x80 : Byte) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by grun [P₂.edx, aN, w₂], ?_, fun r h => by gregs [h], by gmems [], by gmems []⟩
    gmems [P₂.edx, aN]; rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hlen : (bytesAt s.mem (w64 S) n).length = n := length_bytesAt _ _ _
  have key : s₃.mem = writeBytes s₁.mem (w64 p.W + BitVec.ofNat 64 d) (bytesAt s.mem (w64 S) n ++ [0x80]) := by
    rw [m₃, P₂.mem, eS, aD, writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [rd₃, P₂.rd, rd₁], by rw [wr₃, P₂.wr, wr₁]⟩
  · rw [key]
    refine fr₁.trans fun x hx => ?_
    exact writeBytes_frame _ _ _ (by
      simp only [List.length_append, hlen, List.length_singleton]; exact contains_pre _ (by omega)) x hx
  · rw [key, blockAtMem, Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), m₁,
      Proof.Cmac.zero4_bytes]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Cmac.zeros, Spec.Ocb.zeros,
      List.drop_replicate, List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · rw [g₃ r h₁, P₂.other r h₁ h₄ h₃ h₂, g₁ r h₁ h₂ h₃ h₄]

end VG.Proof.AesOcb.X86
