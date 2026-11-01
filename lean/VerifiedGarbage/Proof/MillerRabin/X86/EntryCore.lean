module

public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryValues
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory

import VerifiedGarbage.Proof.MillerRabin.X86.EntryMarker
import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.MillerRabin.ExponentWords32
import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
import VerifiedGarbage.Proof.MillerRabin.X86.Core
/-! # The complete round body satisfies the reviewed mathematical result -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/EntryStage.lean`, which only this module imported.
section

/-! # ABI setup establishes the complete round stage with workspace-only writes -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86

def narrowed (s : State) : State := (entered s).withRegions (entered s).rd [⟨wsOf s, lenOf s⟩]

theorem Entry.narrowed_caller {s : State} (E : Entry s) :
    Caller (geometry s) (arg s 1).toNat ((entered s).gpr .esp) (narrowed s) := by
  have C := E.caller
  refine ⟨C.sp, C.low, C.stackFar, C.lengthFar, C.lengthStackFar, ?_⟩
  change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1)) = _
  have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 1) = argAddr s 1 := Compact.argument_address s 1
  rw [ea]
  have access : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 1) 4 := by
    change InRegions ((entered s).rd ++ _) _ _
    rw [entered, Compact.entered, pushed_rd, E.rd]
    refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
    rw [argument_offset E (by decide : 1 < 2)]
    exact Offset.contains_base _ (by decide : 4 * 1 + 4 ≤ 8) (by decide)
  rw [State.load32, ite_eq_left access]
  change some ((entered s).mem.readW (argAddr s 1) 32) = _
  rw [E.pushed_arg (by decide : 1 < 2), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Entry.narrowed_base {s : State} (E : Entry s) :
    WP isa (.block [.mov .edi (.mem (at_ .esp 20))]) (narrowed s) fun t =>
      Stage (geometry s) (arg s 1).toNat (initialValues s 0) ((entered s).gpr .esp)
        (initialValues s) initialArrays (fun _ => 0) [] t ∧
      t.mem = (entered s).mem ∧ Keeps [.edi] (narrowed s) t := by
  have access : readSrc (narrowed s) (.mem (at_ .esp 20)) = some (arg s 0) := by
    change (narrowed s).load32 ((narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0)) = _
    have ea : (narrowed s).ea (VG.Impl.Mont.X86.Compact.arg 0) = argAddr s 0 := Compact.argument_address s 0
    rw [ea, State.load32]
    have region : InRegions ((narrowed s).rd ++ (narrowed s).wr) (argAddr s 0) 4 := by
      change InRegions ((entered s).rd ++ _) _ _
      rw [entered, Compact.entered, pushed_rd, E.rd]
      refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      simpa only [BitVec.add_zero] using
        (Offset.contains_base (argAddr s 0) (by decide : 0 + 4 ≤ 8) (by decide))
    rw [ite_eq_left region]
    exact congrArg some (E.pushed_arg (by decide : 0 < 2))
  refine wp_movS access fun t T _ => WP.block_nil ?_
  have mem : t.mem = (entered s).mem := T.mem
  have workspace : (⟨wsOf s, lenOf s⟩ : Region) ∈ t.wr := by
    rw [T.wr]
    exact List.mem_singleton_self _
  have base : PtrAt t (wsOf s) .edi 0 := by
    rw [PtrAt, T.gpr, Nat.add_zero, E.ws_toNat]
    exact (Nat.mod_eq_of_lt (arg s 0).isLt).symm
  refine ⟨⟨E.data mem workspace base, E.modulus mem, ?_, ?_⟩, mem, T.keeps⟩
  · apply E.narrowed_caller.keepFrame T.keeps (by decide)
    rw [T.mem]
    exact Frame.refl _ _
  · intro j known
    change j ∈ [0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/NativeDigits32.lean`, which only this module imported.
section

/-! # A high-to-low native-word window is the corresponding exponent digit -/

section
namespace VG.Proof.MillerRabin

theorem exponentWindow_digit (E N j i : Nat) (word : j < N) (window : i < 8) :
    ((exponentWord E (N - 1 - j) <<< (4 * i)) >>> 28).toNat =
      E / 16 ^ (8 * N - 1 - (8 * j + i)) % 16 := by
  rw [Word32.shl_shr28 _ window, exponentWord, BitVec.toNat_ofNat,
    show 28 - 4 * i = 4 * (7 - i) by omega,
    Word32.digit_word E (N - 1 - j) (7 - i) (by omega)]
  rw [show 8 * (N - 1 - j) + (7 - i) = 8 * N - 1 - (8 * j + i) by omega]

end VG.Proof.MillerRabin
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ExponentMath.lean`, which only this module imported.
section

/-! # The native-word execution order is the shared mathematical window run -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86

theorem wordState_mrun (A : Nat → Nat) (c w E N j : Nat) (F : Bool)
    (word : j < N)
    (initial : (A aY, F) = Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j)) :
    ∀ i, i ≤ 8 → wordState A c w (exponentWord E (N - 1 - j)) F i =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) E (8 * N) (8 * j + i)
  | 0, _ => by simpa only [wordState, Nat.add_zero] using initial
  | i + 1, bound => by
    rw [wordState, wordState_mrun A c w E N j F word initial i (by omega),
      show 8 * j + (i + 1) = (8 * j + i) + 1 by omega, Word32.mrun,
      exponentWindow_digit E N j i word (by omega)]

theorem powerView_setY (A : Nat → Nat) (y : Nat) :
    (fun d => setAt A aY y (aTable + d)) = (fun d => A (aTable + d)) := by
  funext d
  exact setAt_other _ _ (by unfold aTable aY; omega)

theorem exponentState_mrun (A : Nat → Nat) (c w N : Nat) (one : A aY = A aTable) :
    ∀ j, j ≤ N → exponentState A c w N false j =
      Word32.mrun c w (A aMinusOne) (fun d => A (aTable + d)) (A aExponent) (8 * N) (8 * j)
  | 0, _ => by
    change (A aY, false) = (A (aTable + 0), false)
    rw [Nat.add_zero, one]
  | j + 1, bound => by
    have ih := exponentState_mrun A c w N one j (by omega)
    let st := exponentState A c w N false j
    let nextA := setAt A aY st.1
    have start : (nextA aY, st.2) =
        Word32.mrun c w (nextA aMinusOne) (fun d => nextA (aTable + d)) (A aExponent) (8 * N) (8 * j) := by
      change (setAt A aY st.1 aY, st.2) = _
      rw [setAt_self]
      change st = Word32.mrun c w (setAt A aY st.1 aMinusOne)
        (fun d => setAt A aY st.1 (aTable + d)) (A aExponent) (8 * N) (8 * j)
      rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY]
      exact ih
    have result := wordState_mrun nextA c w (A aExponent) N j st.2 (by omega) start 8 (by decide)
    change wordState nextA c w (exponentWord (A aExponent) (N - 1 - j)) st.2 8 = _
    rw [result]
    change Word32.mrun c w (setAt A aY st.1 aMinusOne) (fun d => setAt A aY st.1 (aTable + d))
      (A aExponent) (8 * N) (8 * j + 8) = _
    rw [setAt_other _ _ (by decide : aMinusOne ≠ aY), powerView_setY,
      show 8 * j + 8 = 8 * (j + 1) by omega]

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/TableCongr32.lean`, which only this module imported.
section

/-! # A window run reads only the sixteen represented table powers -/

section
namespace VG.Proof.MillerRabin.Word32

theorem mwin_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M d : Nat) (digit : d < 16) (s : Nat × Bool) : mwin c w M T d s = mwin c w M U d s := by
  unfold mwin
  rw [table d digit, table 0 (by decide)]

theorem mrun_table_congr {T U : Nat → Nat} (table : ∀ d < 16, T d = U d)
    (c w M E W j : Nat) : mrun c w M T E W j = mrun c w M U E W j := by
  induction j with
  | zero => rw [mrun, mrun, table 0 (by decide)]
  | succ j ih =>
    rw [mrun, mrun, ih]
    exact mwin_table_congr table c w M _ (Nat.mod_lt _ (by decide)) _

end VG.Proof.MillerRabin.Word32
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/ResultMath.lean`, which only this module imported.
section

/-! # The complete native-window result is the reviewed Miller–Rabin test -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.Impl.MillerRabin.X86 VG.Proof.RsaKeyGen

theorem finishedState_eq {A : Nat → Nat} {c w b : Nat}
    (odd : c % 2 = 1) (minimum : 3 ≤ c) (fits : c < 2 ^ (64 * w))
    (witness : A aX = b % c * 2 ^ (64 * w) % c)
    (one : A aOne = 2 ^ (64 * w) % c) (minus : A aMinusOne = c - 2 ^ (64 * w) % c)
    (exponent : A aExponent = mrE c) :
    (finishedState A c w (2 * w) (mrA c % 64)).2 = Proof.MillerRabin.Round.round c b := by
  change (Word32.msqs c w (runValues A c w aMinusOne) (4 - sigOf (mrA c % 64)) 3
    (exponentState (runValues A c w) c w (2 * w) false (2 * w)) 3).2 = _
  rw [runValues_minus, sigOf_mod, exponentState_mrun (runValues A c w) c w (2 * w)
    (runValues_identity A c w) (2 * w) (Nat.le_refl _), runValues_minus, runValues_exp]
  have table : ∀ j < 16, runValues A c w (aTable + j) = Word32.tp c w (A aX) (A aOne) j :=
    fun j digit => runValues_power A c w digit
  rw [Word32.mrun_table_congr table c w (A aMinusOne) (A aExponent) (8 * (2 * w)) (8 * (2 * w)),
    show 8 * (2 * w) = 16 * w by omega, exponent]
  exact Word32.final_eq odd minimum fits witness one minus

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.RsaKeyGen
open VG.Impl.MillerRabin.X86

def Result (s : State) (t : State) : Prop :=
  (∀ b, initialValues s aX = b % initialValues s 0 * 2 ^ (64 * (geometry s).w) % initialValues s 0 →
    (t.gpr .eax).toNat = if Proof.MillerRabin.Round.round (initialValues s 0) b then 1 else 0) ∧
  WorkspaceFrame (geometry s) (roundWrites (geometry s)) (entered s).mem t.mem

theorem Entry.narrowed_body {s : State} (E : Entry s) :
    WP isa (body montName montCode) (narrowed s) fun t =>
      Result s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] (narrowed s) t := by
  unfold body
  refine WP.seq (WP.mono E.narrowed_base fun t ⟨S, mem, K⟩ => ?_)
  obtain ⟨minimum, odd, _, Xlt, one, minus, exponent, _⟩ := E.prepared
  change 3 ≤ initialValues s 0 at minimum
  change initialValues s 0 % 2 = 1 at odd
  change initialValues s aX < initialValues s 0 at Xlt
  change initialValues s aOne = 2 ^ (64 * (geometry s).w) % initialValues s 0 at one
  change initialValues s aMinusOne = initialValues s 0 - 2 ^ (64 * (geometry s).w) % initialValues s 0 at minus
  change initialValues s aExponent = mrE (initialValues s 0) at exponent
  have marker := E.marker
  rw [← mem] at marker
  have Olt : initialValues s aOne < initialValues s 0 := by
    rw [one]
    exact Nat.mod_lt _ (by omega)
  refine WP.mono (core_ok VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack E.valid S
    (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega) odd Xlt Olt (Nat.mod_lt _ (by decide)) marker.1 marker.2)
    fun u ⟨value, frame, keep⟩ => ?_
  refine ⟨⟨?_, ?_⟩, (K.mono (by decide)).widen keep⟩
  · intro b witness
    have fits : initialValues s 0 < 2 ^ (64 * (geometry s).w) := by
      rw [initialValues, Compact.numAt_val32]
      have := val32_lt s.mem (wsOf s) (Proof.Rsa.Mont.arrAt (geometry s).w 0) (2 * (geometry s).w)
      simpa only [show 32 * (2 * (geometry s).w) = 64 * (geometry s).w by omega] using this
    have final := finishedState_eq odd minimum fits witness one minus exponent
    change u.gpr .eax = BitVec.ofNat 32
      (finishedState (initialValues s) (initialValues s 0) (geometry s).w (2 * (geometry s).w)
        (mrA (initialValues s 0) % 64)).2.toNat at value
    rw [value, final]
    cases Proof.MillerRabin.Round.round (initialValues s 0) b <;> rfl
  · rw [mem] at frame
    exact frame

end VG.Proof.MillerRabin.X86
