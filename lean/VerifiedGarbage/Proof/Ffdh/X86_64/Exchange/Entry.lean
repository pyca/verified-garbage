module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry

/-! # FFDH public-key validation on x86-64: save the arguments and ABI registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (ws)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def entryMem (s : State) (B : Addr) : Mem :=
  (((((((((((((s.mem.writeW (off B (8 * 0)) (s.gpr .rbx)).writeW (off B (8 * 1)) (s.gpr .rbp)).writeW (off B (8 * 2)) (s.gpr .r12)).writeW (off B (8 * 3)) (s.gpr .r13)).writeW (off B (8 * 4)) (s.gpr .r14)).writeW (off B (8 * 5)) (s.gpr .r15)).writeW (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut)) (s.gpr .rdi)).writeW (off B (8 * sDom)) (s.gpr .rdx)).writeW (off B (8 * sDomLen)) (s.gpr .rcx)).writeW (off B (8 * sK)) (s.gpr .r8)).writeW (off B (8 * sX)) (s.gpr .r9)).writeW (off B (8 * sXl)) (stackArg s 0)).writeW (off B (8 * sY)) (stackArg s 1))

private theorem entryMem_facts (s : State) (B : Addr) :
    let m := entryMem s B
    word m B (8 * 0) = s.gpr .rbx ∧
    word m B (8 * 1) = s.gpr .rbp ∧
    word m B (8 * 2) = s.gpr .r12 ∧
    word m B (8 * 3) = s.gpr .r13 ∧
    word m B (8 * 4) = s.gpr .r14 ∧
    word m B (8 * 5) = s.gpr .r15 ∧
    word m B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut) = s.gpr .rdi ∧
    word m B (8 * sDom) = s.gpr .rdx ∧
    word m B (8 * sDomLen) = s.gpr .rcx ∧
    word m B (8 * sK) = s.gpr .r8 ∧
    word m B (8 * sX) = s.gpr .r9 ∧
    word m B (8 * sXl) = stackArg s 0 ∧
    word m B (8 * sY) = stackArg s 1 ∧ Outside B 0 (8 * 23) s.mem m := by
  intro m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

theorem exEntry_ok {s : State} {B : Addr} (hB : stackArg s 3 = B)
    (hw : ∀ i < 23, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) s fun t => t.gpr .rdi = B ∧
      (∀ i < 6, word t.mem B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Slots t.mem B [(VG.Impl.Ffdh.X86_64.Domain.sOut, s.gpr .rdi), (sDom, s.gpr .rdx), (sDomLen, s.gpr .rcx),
        (sK, s.gpr .r8), (sX, s.gpr .r9), (sXl, stackArg s 0), (sY, stackArg s 1)] ∧
      Outside B 0 (8 * 23) s.mem t.mem ∧ Keep [.rax, .r10, .r11, .rdi] s t := by
  have hB' : s.mem.readW (off (s.gpr .rsp) (8 * 4)) 64 = B := hB
  refine WP.mono (WP.keep [.rax, .r10, .r11, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = entryMem s B)
    (by
      unfold VG.Impl.Ffdh.X86_64.Domain.Exchange.entry save
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
          hw VG.Impl.Ffdh.X86_64.Domain.sOut (by decide),
          hw sDom (by decide),
          hw sDomLen (by decide),
          hw sK (by decide),
          hw sX (by decide),
          hw sXl (by decide),
          hw sY (by decide), ha 3 (by decide), ha 0 (by decide), ha 1 (by decide)]; rfl) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hD, hL, hK, hX, hXl, hY, ho⟩ := entryMem_facts s B
  rw [← hm] at h0 h1 h2 h3 h4 h5 hO hD hL hK hX hXl hY ho
  refine ⟨hdi, ?_, ?_, ho, k⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3, h4, h5]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hO, hD, hL, hK, hX, hXl, hY]

end VG.Proof.Ffdh.X86_64.Exchange
