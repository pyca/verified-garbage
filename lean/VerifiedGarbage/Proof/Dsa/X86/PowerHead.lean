module

public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHead
public import VerifiedGarbage.Proof.Dsa.X86.PowCall

/-! # Loading shared exponentiation's operands without duplicating setup -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def powerHead (len bl : Nat) (modulus : Field) (a b : Pointer) : Prog isa :=
  .seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 0) (.input modulus))
    (.seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 5) a)
      (Core.load ((len + 7) / 8) bl (slot ((len + 7) / 8) 8) b))

structure PowerReady (base : Addr) (size n : Nat) (s : State) : Prop where
  scr : Scr s base size
  room : Pow.Room (s.gpr .esp) base size
  large : 1 < wordsVal s.mem base (slot n 0) n
  odd : wordsVal s.mem base (slot n 0) n % 2 = 1

theorem powerHead_ok {base : Addr} {size len bl : Nat} {modulus : Field} {a b : Pointer} {s : State}
    (P : ArithmeticPre base size len bl modulus a b s) (room : Pow.Room (s.gpr .esp) base size)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hb4 : 4 ≤ bl) (hb : bl ≤ len)
    (hw4 : len % 4 = 0) (hwb : bl % 4 = 0) :
    WP isa (powerHead len bl modulus a b) s fun t =>
      PowerReady base size ((len + 7) / 8) t ∧ Keeps loadClob s t := by
  let n := (len + 7) / 8
  have hn : n ≤ 48 := by dsimp only [n]; omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have sz : 8256 ≤ size := hz
  have nw := P.scr.nowrap
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega
  unfold powerHead
  refine WP.seq (WP.mono (coreLoad_ok P.scr hz (bounds 0 (by decide)) h4 (by omega) hw4
    P.modulusReady.toReadableComponent (P.modulusReady.slot (by decide))) fun u ⟨M, K, O⟩ => ?_)
  have O' := slotOutside_whole O (by decide)
  have A := P.leftReady.keep K (by decide) O' hn
  have B := P.rightReady.keep K (by decide) O' hn
  refine WP.seq (WP.mono (coreLoad_ok (P.scr.of_keeps K (by decide)) hz (bounds 5 (by decide)) h4
    (by omega) hw4 A.toReadableComponent (A.slot (by decide))) fun v ⟨_, L, F⟩ => ?_)
  have B' := B.keep L (by decide) (slotOutside_whole F (by decide)) hn
  refine WP.mono (coreLoad_ok (P.scr.of_keeps (K.trans L) (by decide)) hz (bounds 8 (by decide)) hb4
    (by omega) hwb B'.toReadableComponent (B'.slot (by decide))) fun t ⟨_, N, G⟩ => ?_
  have allK := (K.trans L).trans N
  have mod : wordsVal t.mem base (slot n 0) n =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) := by
    rw [slotOutside_val G (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega),
      slotOutside_val F (by decide) (by have H := bounds 0 (by decide); dsimp only [n] at H; omega), M]
  exact ⟨⟨P.scr.of_keeps allK (by decide), by rw [allK.1 _ (by decide)]; exact room,
    mod ▸ P.large, mod ▸ P.odd⟩, allK⟩

end VG.Proof.Dsa.X86
