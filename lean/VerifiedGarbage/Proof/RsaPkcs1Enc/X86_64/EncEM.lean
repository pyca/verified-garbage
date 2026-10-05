import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncLoops

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the encoded message

The separator and the zero test's slot (`sep_run`), the copy of `M`
(`msgLoop_ok`, `msgCopy_ok`), and, from the bytes they leave, `EM`
(`em_eq`): after the first four pieces, the frame holds
`EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` (`em_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

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
    | omega
    | exact getD_zero _
    | (subst_vars; rfl)
    | (congr 1; omega)

/-- `EM` in memory, from its bytes. -/
theorem em_eq {m : Mem} {base : Addr} {M PS : List Byte} {k : Nat} (hk : k = PS.length + M.length + 3)
    (hk' : k < 2 ^ 64) (b0 : m (off base 0) = 0) (b1 : m (off base 1) = 2)
    (bp : ∀ i < PS.length, m (off base (2 + i)) = PS.getD i 0) (bs : m (off base (2 + PS.length)) = 0)
    (bm : ∀ j < M.length, m (off base (3 + PS.length + j)) = M.getD j 0) :
    Spec.Rsa.bytesAt m base k = Spec.RsaPkcs1Enc.encode M PS := by
  have hl : (Spec.RsaPkcs1Enc.encode M PS).length = k := by simp [Spec.RsaPkcs1Enc.encode, hk]; omega
  rw [← map_getD_range (Spec.RsaPkcs1Enc.encode M PS), hl, Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [getD_encode, show base + BitVec.ofNat 64 i = off base i from rfl]
  split
  · subst_vars; exact b0
  split
  · subst_vars; exact b1
  split
  · rw [show i = 2 + (i - 2) by omega]
    rw [show 2 + (i - 2) - 2 = i - 2 by omega]
    exact bp _ (by omega)
  split
  · subst_vars; rw [Nat.add_comm]; exact bs
  · rw [show i = 3 + PS.length + (i - PS.length - 3) by omega, show 3 + PS.length + (i - PS.length - 3) - PS.length - 3 = i - PS.length - 3 by omega]
    exact bm _ (by omega)

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
    (by have := hF.1; omega)
  have hcx' : t.gpr .rcx = BitVec.ofNat 64 (stackArg s 3).toNat := by rw [hcx]; simp
  have hst : InRegions t.wr (off (fb s) (oEM + 2 + (stackArg s 3).toNat)) 1 :=
    hs.st8 (by unfold frameBytes oEM; omega)
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

theorem msgLoop_ok {s t₀ : State} (hp : EPre s) {o : Nat} (ho' : oEM + 3 ≤ o)
    (hoK : o + (stackArg s 1).toNat ≤ oEM + (s.gpr .rcx).toNat) (hm0 : 0 < (stackArg s 1).toNat)
    (hrd : t₀.rd = s.rd) (hwr : t₀.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (ho : Outside (fb s) 0 frameBytes s.mem t₀.mem) (hdi : t₀.gpr .rdi = off (fb s) o)
    (hsi : t₀.gpr .rsi = stackArg s 0) (hcx : t₀.gpr .rcx = stackArg s 1)
    (h10 : t₀.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa msgLoop t₀ (MsgInv s t₀ o (stackArg s 1).toNat) := by
  have hF := fb_toNat hp
  have hk2 := hp.k2
  have hs : Scr t₀ (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [hcx]; simp
  refine wp_upto (a := 0) (N := (stackArg s 1).toNat) hm0 (MsgInv s t₀ o) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), h10⟩
  intro j _ hj u hI
  have hdi' : u.gpr .rdi = off (fb s) o := (hI.keep.gpr (by decide)).trans hdi
  have hsi' : u.gpr .rsi = stackArg s 0 := (hI.keep.gpr (by decide)).trans hsi
  have hcx'' : u.gpr .rcx = BitVec.ofNat 64 (stackArg s 1).toNat := (hI.keep.gpr (by decide)).trans hcx'
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 0) j) 1 :=
    ⟨⟨stackArg s 0, (stackArg s 1).toNat⟩, List.mem_append_left _ (by rw [hI.keep.2.1, hrd, hp.hrd]; simp),
      Offset.contains_base _ (by omega) (by have := hp.wM; omega)⟩
  have hst : InRegions u.wr (off (fb s) (o + j)) 1 :=
    (hs.congr (hI.keep.2.2)).st8 (by unfold frameBytes oEM at *; omega)
  have hb : u.mem (off (stackArg s 0) j) = s.mem (stackArg s 0 + BitVec.ofNat 64 j) := by
    have hd : (stkR s).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩ := hp.dKm
    rw [hI.out _ (.inr ?_)]
    · exact byte_outside ho hd (by have := hp.wM; omega) hj
    · have := outside_frame s (x := off (stackArg s 0) j) fun hc =>
        hd _ hc (Offset.contains_base _ (by omega) (by have := hp.wM; omega))
      unfold frameBytes oEM at *; omega
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) (o + j)) (s.mem (stackArg s 0 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = (stackArg s 1).toNat))) (by
    xrun [msgLoop, ea_bx (j := j) (p := stackArg s 0), ea_bx (j := j) (p := off (fb s) o), hsi', hdi',
      hin, hst, hb, hI.r10, hcx'', ofNat_add_one, trunc_zext, off_off, Nat.zero_add,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show (stackArg s 1).toNat < 2 ^ 64 by omega)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega)
      (by unfold frameBytes oEM at *; omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by unfold frameBytes oEM at *; omega) (by unfold frameBytes oEM at *; omega)]
      exact hI.msg i hi
    · exact byte_wb_self _ _ _ _

end VG.Proof.RsaPkcs1Enc.X86_64
