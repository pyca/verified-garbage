import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep

/-! A pair returns the high half to `rcx`, leaving both flags live. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem pair_ok {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 16 ≤ Z) (hZb : eb + 8 * j + 8 * k + 16 ≤ Z)
    (sb : eb + 8 * j + 8 * k + 16 ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 16 ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.pair k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) 2 +
        2 ^ 128 * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) 2 +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) 2 +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 16 s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.pair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok hs h8 h9 h14 (by omega) (by omega) hc ho
    (by decide) (by decide) (by decide) (by decide) (by decide))
    fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
  refine WP.mono (word_ok (k := k + 1) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by omega) (by omega) hca hoa (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
  have he : e + 8 * j + 8 * (k + 1) = e + 8 * j + 8 * k + 8 := by omega
  have heb : eb + 8 * j + 8 * (k + 1) = eb + 8 * j + 8 * k + 8 := by omega
  rw [he, heb, ka.gpr (by decide)] at et
  rw [he] at outt
  have lo : word t.mem B (e + 8 * j + 8 * k) = word a.mem B (e + 8 * j + 8 * k) :=
    outt.word (by omega) (by omega)
  have ti : word a.mem B (e + 8 * j + 8 * k + 8) = word s.mem B (e + 8 * j + 8 * k + 8) :=
    outa.word (by omega) (by omega)
  have bi : word a.mem B (eb + 8 * j + 8 * k + 8) = word s.mem B (eb + 8 * j + 8 * k + 8) :=
    outa.word (by omega) (by omega)
  rw [ti, bi] at et
  refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
  · rw [AdxSquare.wv2, AdxSquare.wv2, AdxSquare.wv2, lo]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (s.gpr .rdx).toNat]
    omega_using [ea, et]
  · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 16) (Nat.le_refl _) (by omega)).trans
      (outt.mono (o' := e + 8 * j + 8 * k) (n' := 16) (by omega) (by omega))
end VG.Proof.Bignum.X86_64.AdxSquareWide
