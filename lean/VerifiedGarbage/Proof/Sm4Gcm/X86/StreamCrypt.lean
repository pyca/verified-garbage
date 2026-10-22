module

public import VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb
public import VerifiedGarbage.Proof.AesGcm.X86.Top
public import VerifiedGarbage.Proof.Sm4Gcm.X86.Contract
public import VerifiedGarbage.Proof.Sm4Gcm.X86.CtrCall
meta import VerifiedGarbage.Proof.AesGcm.X86.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# SM4-GCM on x86: the entry of `stream_encrypt` and `stream_decrypt`

Untrusted: everything here is checked by Lean. What the precondition
gives (`CrPure`), the entry (`crEntry_pc`), the text as `crypt` takes it
(`setText_ok`) and as `textAbsorb` takes it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Sm4Gcm.X86 VG.WriteBytes VG.Proof.AesGcm.X86
open VG.Impl.AesGcm.X86 hiding ctrCall keyCall ctrArgs cryptWhole cryptTail crypt tag init cryptEntry
  streamEncrypt streamDecrypt finEntry finTag streamFinish streamVerify oneEntry oneTag oneCrypt «seal» «open»
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr)
open VG.Spec.Gcm (ctxH)
open VG.Spec.Sm4.Gcm (ctxCiph)

abbrev crKeeps : List (Nat × Nat) :=
  [(0, ctxO), (2, alO), (3, ahO), (4, xlO), (5, xhO), (6, dataO), (7, lenO)]

/-- The facts of the precondition about the public data `p` alone. -/
structure CrPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  lay : Lay4 (p.2 0) (p.2 1) (p.2 8) p.1 1536
  fd : (p.2 6).toNat + (p.2 7).toNat ≤ 2 ^ 32
  dctx : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  dst : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  dw : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  dstk : (below p.1 1536).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_s : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 1), 80⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  sp : 1536 ≤ p.1.toNat

theorem crPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : streamCryptPre s) (hp : pubOf 9 s = p) :
    CrPure p := by
  simp only [streamCryptPre] at h
  sig_split h
  rename_i hdrop0 hdrop1 d_cs d_cd d_cw hdrop5 d_sd d_sw hdrop8 d_dw hdrop10 hdrop11 hdrop12 r_s r_d r_w
    hdrop16 k_c k_s k_d k_w hdrop21 fc fs fd fw sp
  clear hdrop0 hdrop1 hdrop5 hdrop8 hdrop10 hdrop11 hdrop12 hdrop16 hdrop21 h
  rw [ofNat_lit, below_eq sp] at k_c k_s k_d k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a6 := pubOf_arg hp (i := 6) (by decide); have a7 := pubOf_arg hp (i := 7) (by decide)
  have a8 := pubOf_arg hp (i := 8) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a6, a7, a8, e] at d_cs d_cd d_cw d_sd d_sw d_dw r_s r_d r_w k_c k_s k_d k_w fc fs fd fw sp
  exact ⟨Lay4.of fc fs fw (by decide) sp d_cs d_cw (d_sw.sub_right (Region.sub_prefix (by decide)))
    (d_sw.sub_right (Lay.wSub (by decide))) k_c k_s k_w, fd, d_cd, d_sd.symm, d_dw, k_d, r_s, r_d, r_w, sp⟩

/-- After the entry of `stream_encrypt` or `stream_decrypt`. -/
structure CEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : streamCryptPre s₀
  pub : pubOf 9 s₀ = p
  env : Env (p.2 0) (p.2 1) (p.2 8) p.1 s
  ta : TaSl (p.2 8) (p.2 6) (p.2 7).toNat (p.2 2) (p.2 4) (p.2 5) s.mem
  ah : slotv s.mem (p.2 8) ahO = p.2 3
  saved : SavedAt s.mem (p.2 8) s₀
  frame : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem crEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => streamCryptPre s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀)
      (entry 8 (([.mov .esi (argOp 1)] : List Instr) ++ (crKeeps.flatMap (fun p => keep p.1 p.2) ++ []))) (CEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hp := hpre
    simp only [streamCryptPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 d_wa hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 fw hdrop26
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop12 hdrop13 hdrop14 hdrop15
      hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop26
    have fa := hp
    clear hp
    have a : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 8), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 9] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 9).Disjoint ⟨w64 (arg s₀ 8), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok crKeeps [] (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega) fw
      fun s₂ e => ?_
    have he : Env (arg s₀ 0) (arg s₀ 1) (arg s₀ 8) (s₀.gpr .esp) s₂ :=
      ⟨e.ebp, e.esi, e.esp, by rw [e.rd, e.wr, hrd]; exact covers_of_mem (by simp),
        by rw [e.wr, hwr]; exact covers_of_mem (by simp), by rw [e.wr]; exact wW,
        e.slots (0, ctxO) (by simp)⟩
    refine ⟨s₂, rfl, hpre, hpub, ?_, ?_, ?_, ?_, ?_, e.rd, e.wr⟩
    · rw [← a 0 (by decide), ← a 1 (by decide), ← a 8 (by decide), ← esp]; exact he
    · rw [← a 2 (by decide), ← a 4 (by decide), ← a 5 (by decide), ← a 6 (by decide), ← a 7 (by decide),
        ← a 8 (by decide)]
      exact ⟨e.slots (6, dataO) (by simp), by rw [e.slots (7, lenO) (by simp), ofNat_toNat32],
        e.slots (2, alO) (by simp), e.slots (4, xlO) (by simp), e.slots (5, xhO) (by simp)⟩
    · rw [← a 3 (by decide), ← a 8 (by decide)]; exact e.slots (3, ahO) (by simp)
    · rw [← a 8 (by decide)]; exact e.saved
    · rw [← a 8 (by decide)]; exact e.frame
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 8 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [streamCryptPre] at hp
    sig_split hp
    rename_i hrd hwr hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13
      hdrop14 hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop25 hdrop26
    have fa := hp
    clear hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9 hdrop10 hdrop11 hdrop12 hdrop13 hdrop14
      hdrop15 hdrop16 hdrop17 hdrop18 hdrop19 hdrop20 hdrop21 hdrop22 hdrop23 hdrop24 hdrop25 hdrop26
    clear hp
    have rA : Covers [argsR (s₀.gpr .esp) 9] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- `setText`: the text as the pieces take it. -/
theorem setText_ok {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay4 Ctx St W SP K) {D : BitVec 32} {n : Nat}
    {al xl xh : BitVec 32} {s : State} (he : Env Ctx St W SP s) (hs : TaSl W D n al xl xh s.mem) :
    ∃ s', runBlock isa setText s = some s' ∧ slotv s'.mem W dO = D ∧ slotv s'.mem W nO = BitVec.ofNat 32 n ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (xl.toNat % 16) ∧ Frame [pslotR W] s.mem s'.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := hs.data; have h2 := hs.len; have h3 := hs.xl
  rw [slotv_eq] at h1 h2 h3
  simp only [dataO, lenO, xlO] at h1 h2 h3
  have hand := and15 xl
  refine ⟨_, by xrun [setText, he.ebp, L.aW, he.wIn, he.wIn', h1, h2, h3], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mems [slotv_eq]
  · mems [slotv_eq, h2]
  · mems [slotv_eq, h3]; rw [hand]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · regs []
  · regs []
  · regs []
  all_goals rfl

end VG.Proof.Sm4Gcm.X86
