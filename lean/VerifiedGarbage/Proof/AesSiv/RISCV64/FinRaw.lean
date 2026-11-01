module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Finalize
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-SIV on RISC-V: `vg_cmac_aes_finalize` with any subkeys

Untrusted: everything here is checked by Lean. `vg_cmac_aes_finalize`'s
contract states the MAC only when the subkeys after the key schedule are
the schedule's own; S2V's PRF (`Spec.Siv.ctxMac`) uses whatever subkeys the
key context holds. Its proof (`Proof/CmacAes/RISCV64/Finalize.lean`) shows
more: the state becomes `CIPH_K(C ⊕ Mₙ)` with `Mₙ` the last block formed
from the subkeys in memory (`mn`). That is the contract here
(`finRawRISCV64`), proven the same way, and the call lemma `fin_call_raw`,
as on PPC64LE (`Proof/AesSiv/PPC64LE/FinRaw.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.Impl.CmacAes.RISCV64
open VG.Proof.CmacAes.RISCV64 (FPre finalizeRISCV64 finPre_wp fin_bound finMem finG FPre.fin_frame
  FPre.key_frame mn ciphAt cipher_bytes svOf svOf_sub svOf_ws svOf_add)
open VG.Proof.CmacAes.Stream.RISCV64 (FArgs finalize_noFrames preserved_ne toNat_ofNat)
open VG.Proof.AesCbc.RISCV64 (blk_call savePtr_ok encryptBlocks_noFrames toNat_rounds)
open VG.Spec.Aes (bytesAt)

/-- `vg_cmac_aes_finalize`, whatever the subkeys: the state becomes
`CIPH_K(C ⊕ Mₙ)`. -/
def finRawRISCV64 : Contract isa where
  pre := finalizeRISCV64.pre
  post s s' := bytesAt s'.mem (s.gpr .a2) 16 = ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat
    (Spec.Cmac.xor (bytesAt s.mem (s.gpr .a2) 16) (mn s.mem (s.gpr .a0) (s.gpr .a3) (s.gpr .a4).toNat))
  pub := finalizeRISCV64.pub

theorem finalize_raw_wp {s₀ : State} (h0 : finRawRISCV64.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ finRawRISCV64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .a0 = W at hp
  generalize hSt : s₀.gpr .a2 = St at hp
  generalize hP : s₀.gpr .a3 = P at hp
  generalize hS : s₀.gpr .a5 = S at hp
  generalize hL : (s₀.gpr .a4).toNat = L at hp
  generalize hR : (s₀.gpr .a1).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have slotD : ∀ p ∈ finSaved, ∀ r ∈ [(⟨St, 16⟩ : Region), ⟨S, 2048⟩],
      Region.Disjoint ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    have hb := fin_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (svOf_sub S (by omega))
    · exact svOf_ws S (by omega)
  have hsv : Spill.Saved (svOf S) (finG s₀ S) finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem (svOf S) _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by simp only [List.mem_singleton] at hr; subst hr; simp)).frame
      c.frame fun p hp' r hr => slotD p hp' r hr
  have s1₂ : s₂.gpr .s1 = S := by rw [c.saved _ (by decide), h₁.s1]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [finRestore, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂, show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := svOf S) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := fin_bound p hp'
    have := pad_lt (S + BitVec.ofNat 64 2048)
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [rdwr₂, hp.rd, hp.wr]
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : finG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, c.saved r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, c.sp, h₁.sp]
  · show bytesAt s₄.mem (s₀.gpr .a2) 16 = _
    rw [hW, hR, hSt, hP, hL]
    have hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₁.mem :=
      FPre.fin_frame.trans (h₁.frame.mono (by simp))
    have sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      have := hp.key_frame hfm (d := 0) (n := 16 * (R + 1)) (by omega)
      rwa [BitVec.add_zero] at this
    rw [r₄.mem, RegUpd.mem_write, c.out, cipher_bytes, sch, h₁.st]

theorem finalize_raw_correct (s : State) (hs : finRawRISCV64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finRawRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finalize_raw_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-- What a call of `vg_cmac_aes_finalize` leaves, whatever the subkeys. -/
structure FRPost (s : State) (K St P S : Addr) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s.mem s'.mem
  out : bytesAt s'.mem St 16 = ciphAt s.mem K R (Spec.Cmac.xor (bytesAt s.mem St 16) (mn s.mem K P L))

theorem fin_call_raw {s : State} {K St P S : Addr} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa Impl.CmacAes.Stream.RISCV64.finCall s (FRPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL := toNat_ofNat (n := L) (by have := h.len; omega)
  refine WP.call (k := finRawRISCV64) finalize_raw_correct h.pre h.reads h.writes ?_ finalize_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [finRawRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, hR, hL] at hpost
  exact hpost

end VG.Proof.AesSiv.RISCV64
