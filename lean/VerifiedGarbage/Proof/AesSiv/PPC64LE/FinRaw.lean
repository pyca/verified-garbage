module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Finalize
public import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-SIV on PPC64LE: `vg_cmac_aes_finalize` with any subkeys

Untrusted: everything here is checked by Lean. `vg_cmac_aes_finalize`'s
contract states the MAC only when the subkeys after the key schedule are
the schedule's own; S2V's PRF (`Spec.Siv.ctxMac`) uses whatever subkeys the
key context holds. Its proof (`Proof/CmacAes/PPC64LE/Finalize.lean`) shows
more: the state becomes `CIPH_K(C ⊕ Mₙ)` with `Mₙ` the last block formed
from the subkeys in memory (`mn`). That is the contract here
(`finRawPPC64LE`), proven the same way, and the call lemma `fin_call_raw`.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Proof.CmacAes.PPC64LE (FPre finalizePPC64LE finPre_wp fin_bound slots_scr finMem_frame mn wr_in
  ciphAt cipher_bytes preserved_ne)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs finalize_noFrames)
open VG.Proof.AesCbc.PPC64LE (blk_call callEntry_gpr' toNat_rounds)
open VG.Spec.Aes (bytesAt)

/-- `vg_cmac_aes_finalize`, whatever the subkeys: the state becomes
`CIPH_K(C ⊕ Mₙ)`. -/
def finRawPPC64LE : Contract isa where
  pre := finalizePPC64LE.pre
  post s s' := bytesAt s'.mem (s.gpr .r5) 16 = ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    (Spec.Cmac.xor (bytesAt s.mem (s.gpr .r5) 16) (mn s.mem (s.gpr .r3) (s.gpr .r6) (s.gpr .r7).toNat))
  pub := finalizePPC64LE.pub

theorem finalize_raw_wp {s₀ : State} (h0 : finRawPPC64LE.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      finRawPPC64LE.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .r3 = W at hp
  generalize hSt : s₀.gpr .r5 = St at hp
  generalize hP : s₀.gpr .r6 = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .r7).toNat = L at hp
  generalize hR : (s₀.gpr .r4).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.AesCbc.PPC64LE.encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have slotD : ∀ p ∈ finSaved, ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S, 2048⟩],
      Region.Disjoint ⟨S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    have hb := fin_bound p hp'
    have hsub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact hp.st_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have hsv : Spill.Saved S (s₀.write .r0 s₀.lr).gpr finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem S _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl))).frame
      c.frame fun p hp' r hr => slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl))
  have r14₂ : s₂.gpr .r14 = S := by rw [c.saved _ (by decide), h₁.r14]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [show finSaved.map (fun (r, d) => Instr.load .d r .r14 d) = Spill.restoreCode .r14 finSaved from rfl]
  refine Spill.restore_ok (b := .r14) (l := finSaved) (by decide) r14₂ (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := fin_bound p hp'
    rw [rdwr₂]; exact wr_in (hp.inScr (by omega))
  · show s₃.gpr r = _
    have h0 : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, (preserved_ne r hr).1]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [c.saved r hr, h₁.keep r hr h14, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 2064) (by decide)]; simp [State.write]
  · show bytesAt s₃.mem (s₀.gpr .r5) 16 = _
    rw [hW, hR, hSt, hP, hL]
    have sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))
          · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)]
      exact Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (slots_scr S)) (by omega)
    rw [r₃.mem, c.out, cipher_bytes, sch, h₁.st]

theorem finalize_raw_correct (s : State) (hs : finRawPPC64LE.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finRawPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := finalize_raw_wp hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, whatever the subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : bytesAt s'.mem St 16 = ciphAt s.mem K R (Spec.Cmac.xor (bytesAt s.mem St 16) (mn s.mem K P L))

theorem fin_call_raw {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.PPC64LE.finCall s (FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := Proof.CmacAes.Stream.PPC64LE.toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finRawPPC64LE) finalize_raw_correct h.pre h.reads h.writes ?_ finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finRawPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, hR, hL] at hpost
  exact hpost

end VG.Proof.AesSiv.PPC64LE
