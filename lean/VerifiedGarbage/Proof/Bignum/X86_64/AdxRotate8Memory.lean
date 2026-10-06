import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core

/-! Memory interfaces for the rotating columns. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem ea_at {s : State} {B : Addr} {e : Nat} {r : Reg}
    (hr : s.gpr r = off B e) (d : Nat) : s.ea (at_ r d) = off B (e + d) := by
  simp only [State.ea, at_, hr, BitVec.ofInt_natCast, off, BitVec.add_assoc, BitVec.ofNat_add]

theorem number_words (m : Mem) (B : Addr) (e : Nat) :
    number (fun k => word m B (e + 8 * k)) = wv m B e 8 := by
  simp only [number, wv, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.pow_zero,
    Nat.one_mul, show 64 * 2 = 128 from rfl, show 64 * 3 = 192 from rfl,
    show 64 * 4 = 256 from rfl, show 64 * 5 = 320 from rfl,
    show 64 * 6 = 384 from rfl, show 64 * 7 = 448 from rfl]

theorem core_mem {s : State} {B : Addr} {Z e : Nat} (hs : Scr s B Z)
    (hp : s.gpr .rbp = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxRotate8.core) s fun t =>
      (t.gpr .rbx).toNat + 2 ^ 64 * cols t = cols s + (s.gpr .rdx).toNat * wv s.mem B e 8 ∧
      t.cf = some false ∧ t.of = some false ∧
      Keeps [.rbx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hm : ∀ k < 8, readSrc s (.mem (at_ .rbp (8 * k))) = some (word s.mem B (e + 8 * k)) := by
    intro k hk
    exact readSrc_word hs (ea_at hp (8 * k)) (by omega)
  simpa only [number_words] using core_ok s (fun k => word s.mem B (e + 8 * k)) hm

theorem loadCols_ok {s : State} {B : Addr} {Z e : Nat} (hs : Scr s B Z)
    (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxRotate8.loadCols) s fun t =>
      cols t = wv s.mem B e 8 ∧ Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have ad (d : Nat) : off B e + BitVec.ofInt 64 (d : Int) = off B (e + d) := by
    simp only [BitVec.ofInt_natCast, off, BitVec.ofNat_add, BitVec.add_assoc]
  have hm : WP isa (.block AdxRotate8.loadCols) s fun t =>
      t.gpr .r8 = word s.mem B (e + 0) ∧ t.gpr .r9 = word s.mem B (e + 8) ∧ t.gpr .r10 = word s.mem B (e + 16) ∧ t.gpr .r11 = word s.mem B (e + 24) ∧ t.gpr .r12 = word s.mem B (e + 32) ∧ t.gpr .r13 = word s.mem B (e + 40) ∧ t.gpr .r14 = word s.mem B (e + 48) ∧ t.gpr .r15 = word s.mem B (e + 56) ∧ t.mem = s.mem ∧
      Keep [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
    refine WP.mono (WP.keep [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .r8 = word s.mem B (e + 0) ∧ t.gpr .r9 = word s.mem B (e + 8) ∧ t.gpr .r10 = word s.mem B (e + 16) ∧ t.gpr .r11 = word s.mem B (e + 24) ∧ t.gpr .r12 = word s.mem B (e + 32) ∧ t.gpr .r13 = word s.mem B (e + 40) ∧ t.gpr .r14 = word s.mem B (e + 48) ∧ t.gpr .r15 = word s.mem B (e + 56) ∧ t.mem = s.mem) ?_ rfl)
      (fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩)
    unfold AdxRotate8.loadCols
    xrun [State.ea, at_, hp, ad, Nat.add_zero,
      hs.ld (show e + 0 + 8 ≤ Z by omega),
      hs.ld (show e + 8 + 8 ≤ Z by omega),
      hs.ld (show e + 16 + 8 ≤ Z by omega),
      hs.ld (show e + 24 + 8 ≤ Z by omega),
      hs.ld (show e + 32 + 8 ≤ Z by omega),
      hs.ld (show e + 40 + 8 ≤ Z by omega),
      hs.ld (show e + 48 + 8 ≤ Z by omega),
      hs.ld (show e + 56 + 8 ≤ Z by omega)]
  refine WP.mono hm fun t ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm, k⟩ => ⟨?_, k.1, hm, k.2.1, k.2.2⟩
  unfold cols
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [wv, Nat.reduceMul, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
end VG.Proof.Bignum.X86_64.AdxRotate8
