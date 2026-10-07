import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory

/-! Storing a register block preserves every byte outside that block. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

def regWord (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r8
  | 1 => s.gpr .r9
  | 2 => s.gpr .r10
  | 3 => s.gpr .r11
  | 4 => s.gpr .r12
  | 5 => s.gpr .r13
  | 6 => s.gpr .r14
  | _ => s.gpr .r15

def digits (v : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => digits v n + 2 ^ (64 * n) * (v n).toNat

def writeWords (m : Mem) (B : Addr) (e : Nat) (v : Nat → BitVec 64) : Nat → Mem
  | 0 => m
  | n + 1 => (writeWords m B e v n).writeW (off B (e + 8 * n)) (v n)

theorem writeWords_ok (m : Mem) (B : Addr) (e : Nat) (v : Nat → BitVec 64) (n : Nat)
    (he : e + 8 * n ≤ 2 ^ 64) :
    wv (writeWords m B e v n) B e n = digits v n ∧
      Outside B e (8 * n) m (writeWords m B e v n) := by
  induction n with
  | zero => exact ⟨rfl, Outside.refl _ _ _ _⟩
  | succ n ih =>
    have ⟨hv, ho⟩ := ih (by omega)
    have ht := writeW_outside (writeWords m B e v n) B (v n) (d := e + 8 * n) (by omega)
    constructor
    · rw [writeWords, wv_writeW_top _ _ _ _ _ (by omega), hv]; rfl
    · exact (ho.mono (o' := e) (n' := 8 * (n + 1)) (by omega) (by omega)).trans
        (ht.mono (o' := e) (n' := 8 * (n + 1)) (by omega) (by omega))

theorem storeCols_ok {s : State} {B : Addr} {Z e : Nat} (hs : Scr s B Z)
    (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxRotate8.storeCols) s fun t =>
      wv t.mem B e 8 = cols s ∧ Outside B e 64 s.mem t.mem ∧ Keep [] s t := by
  have hn := hs.nowrap
  have ad (d : Nat) : off B e + BitVec.ofInt 64 (d : Int) = off B (e + d) := by
    simp only [BitVec.ofInt_natCast, off, BitVec.ofNat_add, BitVec.add_assoc]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = writeWords s.mem B e (regWord s) 8) ?_ rfl)
    fun t ⟨hm, k⟩ => ?_
  · unfold AdxRotate8.storeCols
    xrun [State.ea, at_, hp, ad, Nat.add_zero,
      hs.st (show e + 0 + 8 ≤ Z by omega),
      hs.st (show e + 8 + 8 ≤ Z by omega),
      hs.st (show e + 16 + 8 ≤ Z by omega),
      hs.st (show e + 24 + 8 ≤ Z by omega),
      hs.st (show e + 32 + 8 ≤ Z by omega),
      hs.st (show e + 40 + 8 ≤ Z by omega),
      hs.st (show e + 48 + 8 ≤ Z by omega),
      hs.st (show e + 56 + 8 ≤ Z by omega)]
    rfl
  · have ⟨hv, ho⟩ := writeWords_ok s.mem B e (regWord s) 8 (by omega)
    rw [← hm] at hv ho
    refine ⟨?_, ho, k⟩
    rw [hv]
    simp only [digits, regWord, cols, Nat.reduceMul, Nat.zero_add,
      Nat.pow_zero, Nat.one_mul]
end VG.Proof.Bignum.X86_64.AdxRotate8
