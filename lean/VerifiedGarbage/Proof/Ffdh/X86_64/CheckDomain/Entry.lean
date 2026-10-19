module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry

/-! # FFDH domain validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  (((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW
    (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW
    (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW
    (off B (8 * sDom)) (s.gpr .rdi)).writeW (off B (8 * sDomLen)) (s.gpr .rsi)).writeW
    (off B (8 * sK)) (s.gpr .rdx))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧ word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧ word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧ word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdi ∧ word m B (8 * sDomLen) = s.gpr .rsi ∧
    word m B (8 * sK) = s.gpr .rdx ∧ Outside B 0 (8 * 19) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

private theorem entry_eq : VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry =
    [.store (ws .rcx 0) .rbx, .store (ws .rcx 1) .rbp, .store (ws .rcx 2) .r12, .store (ws .rcx 3) .r13,
      .store (ws .rcx 4) .r14, .store (ws .rcx 5) .r15, .store (ws .rcx sDom) .rdi,
      .store (ws .rcx sDomLen) .rsi, .store (ws .rcx sK) .rdx, .mov .rdi (.reg .rcx)] := rfl

theorem cdEntry_ok {s : State} {B : Addr} (hB : s.gpr .rcx = B)
    (hw : ∀ i < 19, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdi), (sDomLen, s.gpr .rsi), (sK, s.gpr .rdx)] ∧
      Outside B 0 (8 * 19) s.mem t.mem ∧ Keep [.rdi] s t := by
  rw [entry_eq]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by xrun [State.ea, ws, hB, hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
      hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hD
    · exact hL
    · exact hK

end VG.Proof.Ffdh.X86_64.CheckDomain
