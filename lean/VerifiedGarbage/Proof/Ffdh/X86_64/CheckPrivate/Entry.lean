module

public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH public-key validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  ((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * sDom)) (s.gpr .rdi)).writeW (off B (8 * sDomLen)) (s.gpr .rsi)).writeW (off B (8 * sK)) (s.gpr .rdx)).writeW (off B (8 * sY)) (s.gpr .rcx)).writeW (off B (8 * sX)) (s.gpr .r9)).writeW (off B (8 * sXl)) (stackArg s 0))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * sDom) = s.gpr .rdi ∧
    word m B (8 * sDomLen) = s.gpr .rsi ∧
    word m B (8 * sK) = s.gpr .rdx ∧
    word m B (8 * sY) = s.gpr .rcx ∧
    word m B (8 * sX) = s.gpr .r9 ∧
    word m B (8 * sXl) = stackArg s 0 ∧ Outside B 0 (8 * 22) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem kpEntry_ok {s : State} {B : Addr} (hB : stackArg s 1 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(sDom, s.gpr .rdi), (sDomLen, s.gpr .rsi), (sK, s.gpr .rdx),
        (sY, s.gpr .rcx), (sX, s.gpr .r9), (sXl, stackArg s 0)] ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.rax, .r10, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 2)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry save
      simp only [saved, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append]
      dsimp only [VG.Impl.Rsa.X86_64.Crt.stk, stackArgAddr] at ha ⊢
      xrun [State.ea, ws, hdrOff, stackArg, stackArgAddr, hB',
        hw 0 (by decide),
        hw 1 (by decide),
        hw 2 (by decide),
        hw 3 (by decide),
        hw 4 (by decide),
        hw 5 (by decide),
        hw sDom (by decide),
        hw sDomLen (by decide),
        hw sK (by decide),
        hw sY (by decide),
        hw sX (by decide),
        hw sXl (by decide), ha 1 (by decide), ha 0 (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hD, hL, hK, hY, hX, hXl, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hD hL hK hY hX hXl ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hD, hL, hK, hY, hX, hXl]

end VG.Proof.Ffdh.X86_64.CheckPrivate
