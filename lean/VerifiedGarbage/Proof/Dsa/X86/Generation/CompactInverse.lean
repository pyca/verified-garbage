module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.CompactInverse
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HeaderWord
public import VerifiedGarbage.Proof.Mont.X86.Inverse64

/-! The shared header receives a genuine negative inverse modulo 2^64. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem compact_inverse {s : State} {base : Addr} {bytes : Nat}
    (h : Scr s base bytes) (fit : 264 ≤ bytes)
    (inverse : (w32 s.mem base 256 * (s.gpr .ecx).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block compactInverse) s fun t =>
      Scr t base bytes ∧ Outside base 56 8 s.mem t.mem ∧
      ((word t.mem base 256).toNat * (word t.mem base 56).toNat + 1) % 2 ^ 64 = 0 ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  unfold compactInverse
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc h (d := 256) (by omega)) fun a A _ => ?_
  have ha := h.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc ha (d := 260) (by omega)) fun b B _ => ?_
  have lo : b.gpr .eax = s.mem.readW (off base 256) 32 := by rw [B.other .eax (by decide), A.gpr]
  have hi : b.gpr .ebx = s.mem.readW (off base 260) 32 := by rw [B.gpr, A.mem]
  have inv : b.gpr .ecx = s.gpr .ecx := by rw [B.other .ecx (by decide), A.other .ecx (by decide)]
  refine WP.block_append (WP.mono (extend_inverse lo hi inv inverse) ?_)
  rintro c ⟨high, mem, K⟩
  have Kc : Keeps [.eax, .ebx, .edx, .ebp] s c :=
    ((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans (K.mono (by decide))
  refine wp_movS rfl fun d D _ => wp_movS rfl fun e E _ => ?_
  have Ke : Keeps [.eax, .ebx, .edx, .ebp] s e :=
    (Kc.trans (D.keeps.mono (by decide))).trans (E.keeps.mono (by decide))
  have meme : e.mem = s.mem := E.mem.trans (D.mem.trans (mem.trans (B.mem.trans A.mem)))
  have he := h.of_keeps Ke (by decide)
  refine WP.mono (store_header_pair he (offset := 56) (by omega)) ?_
  rintro t ⟨ht, F, value, Kt⟩
  rw [meme] at F
  have highSmall : inverseHigh (w32 s.mem base 256) (w32 s.mem base 260) (s.gpr .ecx).toNat < 2 ^ 32 := by
    unfold inverseHigh
    exact Nat.mod_lt _ (Nat.two_pow_pos 32)
  rw [E.gpr, D.other .ecx (by decide), Kc.1 .ecx (by decide),
    E.other .edx (by decide), D.gpr, high, BitVec.toNat_ofNat, Nat.mod_eq_of_lt highSmall] at value
  refine ⟨ht, F, ?_, Ke.trans (Kt.mono (by simp))⟩
  rw [F.word (d := 256) (by decide) (by have := h.nowrap; omega), value, word_eq_w32]
  exact inverse_lift inverse

end VG.Proof.Dsa.X86.Generation
