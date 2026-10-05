import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the copies of `PS` and `M`

`psLoop` copies the padding string `PS` to `EM` after its first two bytes,
collecting in `rdx` whether any byte is zero (`zmask`); `msgLoop` copies the
message after the separator.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `[b + i + d]` for `b = p` and `i = j`. -/
theorem ea_bx {t : State} {b i : Reg} {p : Addr} {j : Nat} (d : Nat) (hb : t.gpr b = p)
    (hi : t.gpr i = BitVec.ofNat 64 j) : t.ea (bx b i d) = off p (d + j) := by
  simp only [State.ea, bx, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

/-- All ones if a byte of `bs` is zero, zero if none is. -/
def zmask (bs : List Byte) : BitVec 64 := if bs.all (· != 0) then 0 else BitVec.allOnes 64

/-- The `rdx` the loop collects after one more byte `b`. -/
theorem zmask_snoc (bs : List Byte) (b : Byte) :
    zmask (bs ++ [b]) = zmask bs ||| (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (b.toNat < 1)))) := by
  by_cases hb : b = 0
  · subst hb
    have : ¬ (bs ++ [(0 : Byte)]).all (· != 0) = true := by simp
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((0 : Byte).toNat < 1)))) = BitVec.allOnes 64 by decide,
      BitVec.or_allOnes]
    simp only [zmask, this, Bool.false_eq_true, ↓reduceIte]
  · have hb' : ¬ b.toNat < 1 := fun h => hb (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [decide_eq_false hb', show (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0#64 by decide,
      BitVec.or_zero]
    have : (b != 0) = true := by simpa using hb
    simp only [zmask, List.all_append, List.all_cons, List.all_nil, Bool.and_true, this]

theorem bytesAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Rsa.bytesAt m p (j + 1) = Spec.Rsa.bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ]

/-! ## `PS` -/

/-- After `j` bytes of `PS`, from the state `t₀` before the loop. -/
structure PsInv (s t₀ : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r11, .r10, .rdx] t₀ t
  out : Outside (fb s) (oEM + 2) j t₀.mem t.mem
  ps : ∀ i < j, byte t.mem (fb s) (oEM + 2 + i) = s.mem (stackArg s 2 + BitVec.ofNat 64 i)
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  rdx : t.gpr .rdx = zmask (Spec.Rsa.bytesAt s.mem (stackArg s 2) j)

theorem psLoop_ok {s t₀ : State} (hp : EPre s) (hsp : t₀.gpr .rsp = fb s) (hrd : t₀.rd = s.rd)
    (hwr : t₀.wr = ⟨fb s, frameBytes⟩ :: s.wr) (ho : Outside (fb s) 0 frameBytes s.mem t₀.mem)
    (hsi : t₀.gpr .rsi = stackArg s 2) (hcx : t₀.gpr .rcx = stackArg s 3)
    (h10 : t₀.gpr .r10 = BitVec.ofNat 64 0) (hdx : t₀.gpr .rdx = 0) :
    WP isa psLoop t₀ (PsInv s t₀ (stackArg s 3).toNat) := by
  have hF := fb_toNat hp
  have hP := hp.psLen
  have hk2 := hp.k2
  have hml := hp.hml
  have hs : Scr t₀ (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [hcx]; simp
  refine wp_upto (a := 0) (N := (stackArg s 3).toNat) (by omega) (PsInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), h10, by rw [hdx]; rfl⟩
  intro j _ hj u hI
  have hsp' : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hsp
  have hsi' : u.gpr .rsi = stackArg s 2 := (hI.keep.gpr (by decide)).trans hsi
  have hcx'' : u.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := (hI.keep.gpr (by decide)).trans hcx'
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 2) (0 + j)) 1 :=
    ⟨⟨stackArg s 2, (stackArg s 3).toNat⟩, List.mem_append_left _ (by rw [hI.keep.2.1, hrd, hp.hrd]; simp),
      by rw [Nat.zero_add]; exact Offset.contains_base _ (by omega) (by have := hp.wP; omega)⟩
  have hst : InRegions u.wr (off (fb s) (oEM + 2 + j)) 1 :=
    (hs.congr (hI.keep.2.2)).st8 (by unfold frameBytes oEM; omega)
  have hb : u.mem (off (stackArg s 2) (0 + j)) = s.mem (stackArg s 2 + BitVec.ofNat 64 j) := by
    rw [Nat.zero_add]
    have hd : (stkR s).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩ := hp.dKp
    rw [hI.out _ (.inr ?_)]
    · exact byte_outside ho hd (by have := hp.wP; omega) hj
    · have := outside_frame s (x := off (stackArg s 2) j) fun hc =>
        hd _ hc (Offset.contains_base _ (by omega) (by have := hp.wP; omega))
      unfold frameBytes at this; unfold oEM; omega
  refine WP.mono (WP.keep [.rax, .r11, .r10, .rdx] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) (oEM + 2 + j)) (s.mem (stackArg s 2 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = (stackArg s 3).toNat)) ∧
      u'.gpr .rdx = u.gpr .rdx ||| (0#64 - BitVec.setWidth 64
        (BitVec.ofBool (decide ((s.mem (stackArg s 2 + BitVec.ofNat 64 j)).toNat < 1))))) (by
    xrun [psLoop, ea_bx (j := j) (p := stackArg s 2), ea_bx (j := j) (p := fb s), hsi', hsp',
      hin, hst, hb, hI.r10, hcx'', ofNat_add_one, trunc_zext, zext_toNat, one64_toNat,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show (stackArg s 3).toNat < 2 ^ 64 by omega)]
    done) rfl) fun u' ⟨⟨hm, h10', hz, hdx'⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10', ?_⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega) (by unfold oEM; omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by unfold oEM; omega) (by unfold oEM; omega)]; exact hI.ps i hi
    · exact byte_wb_self _ _ _ _
  · rw [hdx', hI.rdx, bytesAt_succ, zmask_snoc]

end VG.Proof.RsaPkcs1Enc.X86_64
