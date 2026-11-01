module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.Contract

/-! # `vg_rsa_keygen_inverse` runs `KeyRt.inverse` in its frame and restores the caller's registers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.Keys (Keep num invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)

/-- What the inversion leaves: its frame in the working space, and the gcd and coefficient. -/
structure Done (s t : State) : Prop where
  keep : Keep (base s) (kw (len s)) invArrs invSlots (Compact.entered s).mem t.mem
  gcd : num t.mem (base s) (kw (len s)) 1 =
    Nat.gcd (num s.mem (base s) (kw (len s)) 0) (num s.mem (base s) (kw (len s)) aM)
  bezout : (num s.mem (base s) (kw (len s)) aM : Int) ∣
    (num t.mem (base s) (kw (len s)) 3 : Int) * num s.mem (base s) (kw (len s)) 0 - num t.mem (base s) (kw (len s)) 1
  lt : num t.mem (base s) (kw (len s)) 3 < num s.mem (base s) (kw (len s)) aM

theorem inner_noSp : NoSp (.seq (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi VG.Impl.RsaKeyGen.X86.Inverse.lay))
    (.seq (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.RsaKeyGen.X86.Inverse.lay) (.block Compact.restoreRegs))) :=
  NoSp.of_all (by decide +kernel)

theorem framed_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.Inverse.code s fun t => abiPreserved s t ∧ Done s t := by
  have A := entry h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have frameWs : (below (s.gpr .esp) 16).Disjoint ⟨base s, size s⟩ := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact A.stackWs.sub_left (Offset.sub_below _ (by decide) (by decide))
  unfold VG.Impl.RsaKeyGen.X86.Inverse.code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide) fit inner_noSp ?_
  refine WP.seq (WP.mono (start_ok A) fun u ⟨H, mu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.inverse_ok H (by decide)) fun v ⟨Hv, Kv, KRv, res⟩ => ?_)
  have hws := H.ws
  have O : Outside (base s) 0 (size s) u.mem v.mem :=
    VG.Proof.Rsa.X86.KeyRt.keep_outside hws Kv (by decide) (by decide)
  have FV : Frame [⟨base s, size s⟩] u.mem v.mem := by
    have F := VG.Proof.Bignum.outside_frame O (by have := A.wsFit; unfold size at *; omega)
    simpa only [off, BitVec.add_zero] using F
  have spV : v.gpr .esp = (Compact.entered s).gpr .esp := by
    rw [KRv.1 .esp (by decide), Ku.1 .esp (by decide)]
  have pFit : ((Compact.entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [Compact.entered, pushed_esp, show 4 * Compact.savedRegisters.length = 16 from rfl,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega
  have frameAt : below (s.gpr .esp) 16 = ⟨((Compact.entered s).gpr .esp).setWidth 64, 16⟩ := by
    rw [Compact.entered, pushed_esp]; rfl
  have word (i : Nat) (hi : i < 4) : v.mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
    have same := FV.readW (r := below (s.gpr .esp) 16) (a := addr ((Compact.entered s).gpr .esp) (4 * i))
      (w := 32) (by rw [frameAt, addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact frameWs) (by decide)
    rw [same, mu]
    exact pushed_word (rs := Compact.savedRegisters) (s := s) (by decide) fit hi
  have read (i : Nat) (hi : i < 4) : readSrc v (.mem (at_ .esp (4 * i))) = some
      (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    have access : InRegions (v.rd ++ v.wr) (addr (v.gpr .esp) (4 * i)) 4 := by
      rw [KRv.2.1, KRv.2.2, Ku.2.1, Ku.2.2, spV]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      rw [frameAt, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change v.load32 (addr (v.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, spV, word i hi]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro w ⟨edi, esi, ebp, memory, keep⟩
  have spW : w.gpr .esp = (Compact.entered s).gpr .esp := (keep.1 .esp (by decide)).trans spV
  have returnSame : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    have same := FV.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.returnWs) (by decide)
    rw [same, mu]
    have pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
    have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
      unfold below
      rw [Taint.sub_setWidth fit]
      exact Offset.base_disjoint_below _ (by decide)
    exact pushed.readW (w := 32) (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  have mem0 := A.entered_num (j := 0) (by decide)
  have memM := A.entered_num (j := aM) (by decide)
  have premises := res
    (by
      rw [mu, A.entered_num (j := aNM) (by decide), memM, ← inverseNum_num, ← inverseNum_num]
      unfold aNM aM
      rw [A.negated]
      simp only [kw, Spec.Rsa.modulusWords, Proof.RsaKeyGen.inverseBytes]
      congr 1; omega)
    (by rw [mu, A.entered_num (j := aZero) (by decide), ← inverseNum_num]; exact A.zero)
    (by rw [mu, memM, ← inverseNum_num]; exact A.odd)
    (by rw [mu, memM, ← inverseNum_num]; exact A.large)
    (by
      simp only [VG.Proof.Rsa.X86.Keys.bank, Nat.zero_add]
      rw [mu, A.entered_num (j := 1) (by decide), A.entered_num (j := 2) (by decide),
        A.entered_num (j := 3) (by decide), mem0, memM, ← inverseNum_num, ← inverseNum_num,
        ← inverseNum_num, ← inverseNum_num, ← inverseNum_num]
      unfold aM
      rw [A.v, A.x₁, A.x₂])
  rw [mu, mem0, memM] at premises
  obtain ⟨g, b, l⟩ := premises
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, spW, memory]
      exact word 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact ebp
    · rw [popped_esp, spW, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, memory]
    exact returnSame
  · rw [popped_mem, memory, ← mu]
    exact Kv
  · rw [popped_mem, memory]; exact g
  · rw [popped_mem, memory]; exact b
  · rw [popped_mem, memory]; exact l

end VG.Proof.RsaKeyGen.X86.Inverse
