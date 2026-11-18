module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front

/-! ### `Ffdh.X86_64.CheckPublic.Entry`, which the modules that import this one used -/

section

/-! # FFDH public-key validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  (((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW
    (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW
    (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW
    (off B (8 * sDom)) (s.gpr .rdi)).writeW (off B (8 * sDomLen)) (s.gpr .rsi)).writeW
    (off B (8 * sK)) (s.gpr .rdx)).writeW (off B (8 * sY)) (s.gpr .rcx)

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧ word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧ word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧ word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdi ∧ word m B (8 * sDomLen) = s.gpr .rsi ∧
    word m B (8 * sK) = s.gpr .rdx ∧ word m B (8 * sY) = s.gpr .rcx ∧ Outside B 0 (8 * 20) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

private theorem entry_eq : VG.Impl.Ffdh.X86_64.Domain.CheckPublic.entry =
    [.store (ws .r9 0) .rbx, .store (ws .r9 1) .rbp, .store (ws .r9 2) .r12, .store (ws .r9 3) .r13,
      .store (ws .r9 4) .r14, .store (ws .r9 5) .r15, .store (ws .r9 sDom) .rdi,
      .store (ws .r9 sDomLen) .rsi, .store (ws .r9 sK) .rdx, .store (ws .r9 sY) .rcx, .mov .rdi (.reg .r9)] := rfl

theorem cpEntry_ok {s : State} {B : Addr} (hB : s.gpr .r9 = B)
    (hw : ∀ i < 20, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPublic.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdi), (sDomLen, s.gpr .rsi), (sK, s.gpr .rdx), (sY, s.gpr .rcx)] ∧
      Outside B 0 (8 * 20) s.mem t.mem ∧ Keep [.rdi] s t := by
  rw [entry_eq]
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by xrun [State.ea, ws, hB, hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide),
      hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sDom (by decide), hw sDomLen (by decide),
      hw sK (by decide), hw sY (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, hY, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK hY ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hD
    · exact hL
    · exact hK
    · exact hY

end VG.Proof.Ffdh.X86_64.CheckPublic

end

end

/-! # FFDH public-key validation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure CpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  yl : (s.gpr .r8).toNat = (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (scrLen s).toNat * 8
  hs : Scr s (s.gpr .r9) ((scrLen s).toNat * 8)
  dom : Src s (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rdi) (cpDom s)
  y : Src s (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rcx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)

theorem cpCtx_of {s : State} (h : cpPre s) : CpCtx s := by
  obtain ⟨_, hrd, hwr, dds, dys, _, _, _, _, _, wD, wY, wS, ⟨hk1, hk2⟩, hdl, hyl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, hyl, by omega_using [hsl], Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega_using []) dds, src_of_region (by rw [hrd]; simp) (by omega_using []) dys⟩

end VG.Proof.Ffdh.X86_64.CheckPublic
