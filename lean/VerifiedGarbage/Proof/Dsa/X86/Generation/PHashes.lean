module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashFrame

/-! Every modulus hash contribution is retained at its specified big-endian position. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem p_hash_prefix {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes offset count k : Nat} {src : BitVec 32} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) src seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + count < 2 ^ 31)
    (hash : ∀ x, ok.SH.H.hash x = Spec.Dsa.seedHash (8 * H.D) x)
    (fit : (count + 1) * H.D ≤ 384) (bound : k ≤ count + 1) :
    WP isa (pHashPrefix H seed.length count k) s fun t =>
      (∀ j < k, Spec.Rsa.bytesAt t.mem (off base (Layout.hashes + (count - j) * H.D)) H.D =
        Spec.Dsa.seedHash (8 * H.D) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j)))) ∧
      PHashFrame base (s.gpr .esp) s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  induction k generalizing s with
  | zero => exact WP.block_nil ⟨by intro j hj; omega, Frame.refl _ _, Keeps.refl _ _⟩
  | succ k ih =>
    unfold pHashPrefix
    refine WP.seq (WP.mono (ih scr room tape pointer value (by omega)) fun a ⟨previous, F, K⟩ => ?_)
    have Sa := scr.of_keeps K (by decide)
    have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
    have Ta : WitnessTape base bytes (a.gpr .esp) src seed a := by
      rw [K.1 .esp (by decide)]
      exact tape.keep_enclosed (p_hash_enclose F capacity room) K.2.1 K.2.2
    have controls : ∀ d, Layout.packed ≤ d → d + 4 ≤ Layout.control →
        a.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
      fun d lo hi => p_hash_metadata (d := d) F capacity room lo hi
    have placement := contribution_fit (j := k) fit
    refine WP.mono (p_hash_one (offset := offset) ok Sa capacity Ra Ta length
      (by rw [controls seedPointer (by decide) (by decide)]; exact pointer)
      (by rw [controls candidateOffset (by decide) (by decide)]; exact value)
      (by omega) hash (by unfold Layout.hashes; omega)) fun t ⟨hashed, FT, KT⟩ => ?_
    refine ⟨?_, ?_, K.trans KT⟩
    · intro j hj
      by_cases eq : j = k
      · subst j; exact hashed
      · rw [p_hash_previous FT capacity Ra length fit (by omega : j < k) (by omega)]
        exact previous j (by omega)
    · have step := p_hash_frame FT length (Nat.le_add_right _ _) (by omega)
      rw [K.1 .esp (by decide)] at step
      exact F.trans step

theorem p_hashes {H : Hash} (ok : HashOK H) {s : State} {base : Addr}
    {bytes offset count : Nat} {src : BitVec 32} {seed : List Byte}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) src seed s) (length : seed.length ≤ 32)
    (pointer : s.mem.readW (off base seedPointer) 32 = src)
    (value : s.mem.readW (off base candidateOffset) 32 = BitVec.ofNat 32 offset)
    (small : offset + count < 2 ^ 31)
    (hash : ∀ x, ok.SH.H.hash x = Spec.Dsa.seedHash (8 * H.D) x)
    (fit : (count + 1) * H.D ≤ 384) :
    WP isa (pHashes H seed.length count) s fun t =>
      (∀ j < count + 1, Spec.Rsa.bytesAt t.mem (off base (Layout.hashes + (count - j) * H.D)) H.D =
        Spec.Dsa.seedHash (8 * H.D) (Spec.Dsa.encodeBE seed.length (Spec.Dsa.decodeBE seed + (offset + j)))) ∧
      PHashFrame base (s.gpr .esp) s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t :=
  p_hash_prefix ok scr capacity room tape length pointer value small hash fit (Nat.le_refl _)

end VG.Proof.Dsa.X86.Generation
