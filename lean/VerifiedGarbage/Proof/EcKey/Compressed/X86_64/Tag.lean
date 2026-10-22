module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # The compressed tag store -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem eaRsi (s : State) : s.ea { base := .rsi } = s.gpr .rsi := by
  simp [State.ea]

/-- The low bit of the little-endian slot is the parity of its canonical
integer, even for encodings whose top word is only partly occupied. -/
theorem word_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    word m base a &&& 1 = BitVec.ofNat 64 (wordsVal m base a n % 2) := by
  have hp : wordsVal m base a n % 2 = (word m base a).toNat % 2 := by
    cases n with
    | zero => omega
    | succ n =>
      simp only [wordsVal, Nat.add_mod, Nat.mul_mod,
        show 2 ^ 64 % 2 = 0 from rfl, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat, hp,
    Nat.mod_eq_of_lt (show (word m base a).toNat % 2 < 2 ^ 64 by omega)]

theorem tag_byte (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) (b : Bool) :
    ((((word m base a &&& 1) + 2) &&& (if b then BitVec.allOnes 64 else 0)).setWidth 8) =
      if b then BitVec.ofNat 8 (2 + wordsVal m base a n % 2) else 0 := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [word_parity m base a n hn,
      show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
      BitVec.ofNat_add_ofNat, BitVec.setWidth_ofNat_of_le (by decide), Nat.add_comm]

theorem slot_parity (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    (word m base a).toNat % 2 = wordsVal m base a n % 2 := by
  have h := congrArg BitVec.toNat (word_parity m base a n hn)
  simpa only [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show wordsVal m base a n % 2 < 2 ^ 64 by omega)] using h

theorem tag_ok {c : Cfg} {s : State} {base : Addr} (hs : Scr s base size)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size)
    (hw : InRegions s.wr (s.gpr .rsi) 1) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.compressTag c)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi)
        ((((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) &&& 1) + 2) &&& s.gpr .rcx).setWidth 8) ∧
      KeepRegs [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.compressTag, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, Option.map_some, Option.bind_some, State.load64, State.store8,
    ea_sc, eaRsi, hs.rdi, ld_sc hs hy, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    ite_true, ite_false, reduceCtorEq, hw, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
