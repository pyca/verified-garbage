module

import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `RsaPkcs1Enc.X86_64.EncLoops`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the copies of `PS` and `M`

`psLoop` copies the padding string `PS` to `EM` after its first two bytes,
collecting in `rdx` whether any byte is zero (`zmask`); `msgLoop` copies the
message after the separator.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
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
  · have hb' : ¬ b.toNat < 1 := fun h => hb (BitVec.eq_of_toNat_eq (by simp; omega_using [h]))
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
    (by have := hF.1; omega_using [hF])
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [hcx]; simp
  refine wp_upto (a := 0) (N := (stackArg s 3).toNat) (by omega_using [hP, hml]) (PsInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), h10, by rw [hdx]; rfl⟩
  intro j _ hj u hI
  have hsp' : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hsp
  have hsi' : u.gpr .rsi = stackArg s 2 := (hI.keep.gpr (by decide)).trans hsi
  have hcx'' : u.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := (hI.keep.gpr (by decide)).trans hcx'
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 2) (0 + j)) 1 := by
    rw [hI.keep.2.1, hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArg s 2, (stackArg s 3).toNat⟩, by simp,
      by rw [Nat.zero_add]; exact Offset.contains_base _ (by omega_using [hj]) (by have := hp.wP; omega_using [hj])⟩
  have hst : InRegions u.wr (off (fb s) (oEM + 2 + j)) 1 :=
    (hs.congr (hI.keep.2.2)).st8 (by unfold frameBytes oEM; omega_using [hP, hk2, hj])
  have hb : u.mem (off (stackArg s 2) (0 + j)) = s.mem (stackArg s 2 + BitVec.ofNat 64 j) := by
    rw [Nat.zero_add]
    have hd : (stkR s).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩ := hp.dKp
    rw [hI.out _ (.inr ?_)]
    · exact byte_outside ho hd (by have := hp.wP; omega_using []) hj
    · have := outside_frame s (x := off (stackArg s 2) j) fun hc =>
        hd _ hc (Offset.contains_base _ (by omega_using [hj]) (by have := hp.wP; omega_using [hj]))
      unfold frameBytes at this; unfold oEM; omega_using [hP, hk2, hj, this]
  refine WP.mono (WP.keep [.rax, .r11, .r10, .rdx] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) (oEM + 2 + j)) (s.mem (stackArg s 2 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = (stackArg s 3).toNat)) ∧
      u'.gpr .rdx = u.gpr .rdx ||| (0#64 - BitVec.setWidth 64
        (BitVec.ofBool (decide ((s.mem (stackArg s 2 + BitVec.ofNat 64 j)).toNat < 1))))) (by
    xrun [psLoop, ea_bx (j := j) (p := stackArg s 2), ea_bx (j := j) (p := fb s), hsi', hsp',
      hin, hst, hb, hI.r10, hcx'', ofNat_add_one, trunc_zext, zext_toNat, one64_toNat,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_using [hj]) (show (stackArg s 3).toNat < 2 ^ 64 by omega_using [])]
    done) rfl) fun u' ⟨⟨hm, h10', hz, hdx'⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10', ?_⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega_using []) (by omega_using [])) _ (by omega_using []) (by omega_using []) (by unfold oEM; omega_using [hP, hk2, hj])
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega_using [hi]) (by unfold oEM; omega_arith) (by unfold oEM; omega_using [hP, hk2, hj])]; exact hI.ps i hi
    · exact byte_wb_self _ _ _ _
  · rw [hdx', hI.rdx, bytesAt_succ, zmask_snoc]

end VG.Proof.RsaPkcs1Enc.X86_64

end

end

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the encoded message

The separator and the zero test's slot (`sep_run`), the copy of `M`
(`msgLoop_ok`, `msgCopy_ok`), and, from the bytes they leave, `EM`
(`em_eq`): after the first four pieces, the frame holds
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` (`em_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## `EM` from its bytes -/

theorem map_getD_range (L : List Byte) : (List.range L.length).map (fun i => L.getD i 0) = L :=
  List.ext_getElem (by simp) fun i h₁ _ => by simp at h₁; simp [h₁]

theorem getD_app (l₁ l₂ : List Byte) (i : Nat) :
    (l₁ ++ l₂).getD i 0 = if i < l₁.length then l₁.getD i 0 else l₂.getD (i - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

theorem getD_zero (n : Nat) : [(0 : Byte)].getD n 0 = 0 := by rcases n with _ | n <;> rfl

theorem getD_encode (M PS : List Byte) (i : Nat) :
    (Spec.RsaPkcs1Enc.encode M PS).getD i 0 =
      if i = 0 then 0 else if i = 1 then 2 else if i < PS.length + 2 then PS.getD (i - 2) 0
      else if i = PS.length + 2 then 0 else M.getD (i - PS.length - 3) 0 := by
  simp only [Spec.RsaPkcs1Enc.encode, getD_app, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> first
    | omega_arith
    | exact getD_zero _
    | (subst_vars; rfl)
    | (congr 1; omega_arith)

/-- `EM` in memory, from its bytes. -/
theorem em_eq {m : Mem} {base : Addr} {M PS : List Byte} {k : Nat} (hk : k = PS.length + M.length + 3)
    (hk' : k < 2 ^ 64) (b0 : m (off base 0) = 0) (b1 : m (off base 1) = 2)
    (bp : ∀ i < PS.length, m (off base (2 + i)) = PS.getD i 0) (bs : m (off base (2 + PS.length)) = 0)
    (bm : ∀ j < M.length, m (off base (3 + PS.length + j)) = M.getD j 0) :
    Spec.Rsa.bytesAt m base k = Spec.RsaPkcs1Enc.encode M PS := by
  have hl : (Spec.RsaPkcs1Enc.encode M PS).length = k := by simp [Spec.RsaPkcs1Enc.encode, hk]; omega_arith
  rw [← map_getD_range (Spec.RsaPkcs1Enc.encode M PS), hl, Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [getD_encode, show base + BitVec.ofNat 64 i = off base i from rfl]
  split
  · subst_vars; exact b0
  split
  · subst_vars; exact b1
  split
  · rw [show i = 2 + (i - 2) by omega_arith]
    rw [show 2 + (i - 2) - 2 = i - 2 by omega_arith]
    exact bp _ (by omega_arith)
  split
  · subst_vars; rw [Nat.add_comm]; exact bs
  · rw [show i = 3 + PS.length + (i - PS.length - 3) by omega_arith, show 3 + PS.length + (i - PS.length - 3) - PS.length - 3 = i - PS.length - 3 by omega_arith]
    exact bm _ (by omega_arith)

/-! ## The separator -/

/-- `rsp + n + d` for `rsp = p`. -/
theorem add_reg_imm (p : Addr) (n d : Nat) (hd : d < 2 ^ 31) :
    p + BitVec.ofNat 64 n + BitVec.signExtend 64 (BitVec.ofNat 32 d) = off p (d + n) := by
  rw [sx_ofNat hd, off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem sep_run {s t : State} (hp : EPre s) (hsp : t.gpr .rsp = fb s) (hrd : t.rd = s.rd)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (ho : Outside (fb s) 0 frameBytes s.mem t.mem)
    (hcx : t.gpr .rcx = stackArg s 3) :
    WP isa (.block sep) t fun t' =>
      t'.mem = (t.mem.writeW (off (fb s) (oEM + 2 + (stackArg s 3).toNat)) (0 : Byte)).writeW (off (fb s) oZ)
        (t.gpr .rdx) ∧
      t'.gpr .rdi = off (fb s) (oEM + 3 + (stackArg s 3).toNat) ∧ t'.gpr .rsi = stackArg s 0 ∧
      t'.gpr .rcx = stackArg s 1 ∧ t'.gpr .r10 = BitVec.ofNat 64 0 ∧
      t'.zf = some (stackArg s 1 == 0) ∧ Keep [.rax, .rdi, .rsi, .rcx, .r10, .r11] t t' := by
  have hF := fb_toNat hp
  have hP := hp.psLen
  have hk2 := hp.k2
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega_arith)
  have hcx' : t.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [hcx]; simp
  have hst : InRegions t.wr (off (fb s) (oEM + 2 + (stackArg s 3).toNat)) 1 :=
    hs.st8 (by unfold frameBytes oEM; omega_arith)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rcx, .r10, .r11] (c := .block sep) (Q := fun t' =>
      t'.mem = (t.mem.writeW (off (fb s) (oEM + 2 + (stackArg s 3).toNat)) (0 : Byte)).writeW (off (fb s) oZ)
        (t.gpr .rdx) ∧
      t'.gpr .rdi = off (fb s) (oEM + 3 + (stackArg s 3).toNat) ∧ t'.gpr .rsi = stackArg s 0 ∧
      t'.gpr .rcx = stackArg s 1 ∧ t'.gpr .r10 = BitVec.ofNat 64 0 ∧
      t'.zf = some (stackArg s 1 == 0)) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2, k⟩
  have ha0 := arg_in hp hrd t.wr (show 0 < 6 by decide)
  have ha1 := arg_in hp hrd t.wr (show 1 < 6 by decide)
  xrun [sep, ea_bx (j := (stackArg s 3).toNat) (p := fb s), ea_sp, ea_arg (s := s), hsp, hcx', hst,
    hs.st (d := oZ) (by decide), ha0, ha1, arg_outside hp ho (show 0 < 6 by decide),
    arg_outside hp ho (show 1 < 6 by decide), add_reg_imm _ _ _ (show oEM + 3 < 2 ^ 31 by decide), BitVec.and_self, zero_trunc]
  done

/-! ## `M` -/

/-- After `j` bytes of `M`, from the state `t₀` before the loop, whose `rdi`
is `EM`'s byte `o`. -/
structure MsgInv (s t₀ : State) (o j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  out : Outside (fb s) o j t₀.mem t.mem
  msg : ∀ i < j, byte t.mem (fb s) (o + i) = s.mem (stackArg s 0 + BitVec.ofNat 64 i)
  r10 : t.gpr .r10 = BitVec.ofNat 64 j

theorem msgLoop_ok {s t₀ : State} (hp : EPre s) {o : Nat} (_ho' : oEM + 3 ≤ o)
    (hoK : o + (stackArg s 1).toNat ≤ oEM + (s.gpr .rcx).toNat) (hm0 : 0 < (stackArg s 1).toNat)
    (hrd : t₀.rd = s.rd) (hwr : t₀.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (ho : Outside (fb s) 0 frameBytes s.mem t₀.mem) (hdi : t₀.gpr .rdi = off (fb s) o)
    (hsi : t₀.gpr .rsi = stackArg s 0) (hcx : t₀.gpr .rcx = stackArg s 1)
    (h10 : t₀.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa msgLoop t₀ (MsgInv s t₀ o (stackArg s 1).toNat) := by
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hs : Scr t₀ (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega_arith)
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [hcx]; simp
  refine wp_upto (a := 0) (N := (stackArg s 1).toNat) hm0 (MsgInv s t₀ o) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), h10⟩
  intro j _ hj u hI
  have hdi' : u.gpr .rdi = off (fb s) o := (hI.keep.gpr (by decide)).trans hdi
  have hsi' : u.gpr .rsi = stackArg s 0 := (hI.keep.gpr (by decide)).trans hsi
  have hcx'' : u.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat := (hI.keep.gpr (by decide)).trans hcx'
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 0) j) 1 := by
    rw [hI.keep.2.1, hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArg s 0, (stackArg s 1).toNat⟩, by simp,
      Offset.contains_base _ (by omega_arith) (by have := hp.wM; omega_arith)⟩
  have hst : InRegions u.wr (off (fb s) (o + j)) 1 :=
    (hs.congr (hI.keep.2.2)).st8 (by unfold frameBytes oEM at *; omega_arith)
  have hb : u.mem (off (stackArg s 0) j) = s.mem (stackArg s 0 + BitVec.ofNat 64 j) := by
    have hd : (stkR s).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ := hp.dKm
    rw [hI.out _ (.inr ?_)]
    · exact byte_outside ho hd (by have := hp.wM; omega_arith) hj
    · have := outside_frame s (x := off (stackArg s 0) j) fun hc =>
        hd _ hc (Offset.contains_base _ (by omega_arith) (by have := hp.wM; omega_arith))
      unfold frameBytes oEM at *; omega_arith
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) (o + j)) (s.mem (stackArg s 0 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = (stackArg s 1).toNat))) (by
    xrun [msgLoop, ea_bx (j := j) (p := stackArg s 0), ea_bx (j := j) (p := off (fb s) o), hsi', hdi',
      hin, hst, hb, hI.r10, hcx'', ofNat_add_one, trunc_zext, off_off, Nat.zero_add,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show (stackArg s 1).toNat < 2 ^ 64 by omega_arith)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega_arith) (by omega_arith)) _ (by omega_arith) (by omega_arith)
      (by unfold frameBytes oEM at *; omega_arith)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega_arith) (by unfold frameBytes oEM at *; omega_arith) (by unfold frameBytes oEM at *; omega_arith)]
      exact hI.msg i hi
    · exact byte_wb_self _ _ _ _

end VG.Proof.RsaPkcs1Enc.X86_64
