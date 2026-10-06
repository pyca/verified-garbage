import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWidePair

/-! Composing live-carry pairs into an unrolled multiply-add chain. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem chain_ok (n : Nat) {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 * (2 * n) ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ Z)
    (sb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 8 * (2 * n) ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.chain n k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) (2 * n) +
        2 ^ (64 * (2 * n)) * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) (8 * (2 * n)) s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  induction n generalizing s k c o with
  | zero =>
    apply WP.block_nil
    exact ⟨c, o, hc, ho, by simp [wv], Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _⟩
  | succ n ih =>
    have hn := hs.nowrap
    rw [AdxSquareWide.chain, WP.block_append_iff]
    refine WP.mono (pair_ok hs h8 h9 h14 (by omega) (by omega) (by omega) hc ho)
      fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
    refine WP.mono (ih (k := k + 2) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
      ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
      (by omega) (by omega) (by omega) hca hoa)
      fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
    have he : e + 8 * j + 8 * (k + 2) = e + 8 * j + 8 * k + 8 * 2 := by omega
    have heb : eb + 8 * j + 8 * (k + 2) = eb + 8 * j + 8 * k + 8 * 2 := by omega
    rw [he, heb, ka.gpr (by decide)] at et
    rw [he] at outt
    have lo : wv t.mem B (e + 8 * j + 8 * k) 2 = wv a.mem B (e + 8 * j + 8 * k) 2 :=
      outt.wv (by omega) (by omega)
    have ti : wv a.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega) (by omega)
    have bi : wv a.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega) (by omega)
    rw [ti, bi] at et
    refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega, wv_add, wv_add, wv_add, lo,
        show 64 * (2 + 2 * n) = 128 + 64 * (2 * n) by omega, Nat.pow_add]
      grind
    · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (Nat.le_refl _) (by omega)).trans
        (outt.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (by omega) (by omega))
end VG.Proof.Bignum.X86_64.AdxSquareWide
