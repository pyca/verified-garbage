module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode

/-!
# RSA paddings on PPC64LE: MGF1's blocks

Untrusted: everything here is checked by Lean. The blocks of MGF1's round
(`Impl.RsaOaep.PPC64LE.round`) between the calls: the counter written
big-endian to `S + oCtr` (`ctr_ok`, as `ctrV`), the selection of how many
digest bytes go into `dst` (`xorHead_ok`), their exclusive-or into it
(`xorLoop_ok`), and the next counter (`nextCtr_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_xor wp_mov wp_lsr
  wp_stb wp_lbz wp_nil wp_countdown ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.Mgf1 (ifp ifn)

/-- Our part of the working space with `I2OSP(c, 4)` at `oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (o : Nat) : Byte :=
  if oCtr ≤ o ∧ o < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (o - oCtr) 0 else V o

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

omit P in
theorem off_add (S : Addr) (d j : Nat) : off S d + BitVec.ofNat 64 j = off S (d + j) := off_off S d j

omit P in
theorem view_w8' (m : Mem) {S : Addr} {d j o : Nat} (b : Byte) (hd : d + j < oRsa) (ho : o < oRsa) :
    view (m.writeW (off S d + BitVec.ofNat 64 j) b) S o = if o = d + j then b else view m S o := by
  rw [off_add]; exact view_w8 m b hd ho

/-- The counter, big-endian, to `S + oCtr`; then `update`'s arguments for it. -/
theorem ctr_ok {t : State} (h : Base S vf s t) {c : Nat} (h28 : t.gpr .r28 = BitVec.ofNat 64 c) (hc : c < 2 ^ 32) :
    WP isa (.block updCtrArgs) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      (∀ o < oRsa, view t'.mem (S s) o = ctrV (view t.mem (S s)) c o) ∧
      t'.gpr .r3 = off (S s) oSt ∧ t'.gpr .r4 = t.gpr .r25 ∧ t'.gpr .r5 = off (S s) oCtr ∧
      t'.gpr .r6 = BitVec.ofNat 64 4 ∧ t'.gpr .r7 = off (S s) oW := by
  obtain ⟨_, _, _, _, _, _⟩ := offs
  have hw : ∀ {u : State}, u.wr = t.wr → ∀ j < 4, InRegions u.wr (off (S s) oCtr + BitVec.ofNat 64 j) 1 :=
    fun hu j hj => by rw [hu, h.wr, off_add]; exact sc_inW P (by omega)
  simp only [updCtrArgs]
  refine wp_addi fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => ?_
  have a₂ : u₂.gpr .r5 = off (S s) oCtr := by rw [o₂.get .r5, e₁, h.r14]
  have k₂ : Only [.r5, .r8] t u₂ := (o₁.trans o₂).mono
  refine wp_stb (a := off (S s) oCtr + BitVec.ofNat 64 3) (by rw [a₂]) (hw k₂.wr 3 (by omega)) fun u₃ m₃ => ?_
  refine wp_lsr fun u₄ o₄ e₄ => ?_
  refine wp_stb (a := off (S s) oCtr + BitVec.ofNat 64 2) (by rw [o₄.get .r5, m₃.gpr, a₂])
    (hw (by rw [o₄.wr, m₃.wr, k₂.wr]) 2 (by omega)) fun u₅ m₅ => ?_
  refine wp_lsr fun u₆ o₆ e₆ => ?_
  refine wp_stb (a := off (S s) oCtr + BitVec.ofNat 64 1) (by rw [o₆.get .r5, m₅.gpr, o₄.get .r5, m₃.gpr, a₂])
    (hw (by rw [o₆.wr, m₅.wr, o₄.wr, m₃.wr, k₂.wr]) 1 (by omega)) fun u₇ m₇ => ?_
  refine wp_lsr fun u₈ o₈ e₈ => ?_
  refine wp_stb (a := off (S s) oCtr + BitVec.ofNat 64 0)
    (by rw [o₈.get .r5, m₇.gpr, o₆.get .r5, m₅.gpr, o₄.get .r5, m₃.gpr, a₂])
    (hw (by rw [o₈.wr, m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, k₂.wr]) 0 (by omega)) fun u₉ m₉ => ?_
  refine wp_addi fun u₁₀ o₁₀ e₁₀ => wp_mov fun u₁₁ o₁₁ e₁₁ => wp_li (by decide) fun u₁₂ o₁₂ e₁₂ =>
    wp_addi fun u₁₃ o₁₃ e₁₃ => wp_nil ?_
  -- The bytes.
  have r8₂ : u₂.gpr .r8 = BitVec.ofNat 64 c := by rw [e₂, o₁.get .r28, h28]
  have r8₄ : u₄.gpr .r8 = BitVec.ofNat 64 (c / 2 ^ 8) := by rw [e₄, m₃.gpr, r8₂, shr8 (by omega)]
  have r8₆ : u₆.gpr .r8 = BitVec.ofNat 64 (c / 2 ^ 8 / 2 ^ 8) := by
    rw [e₆, m₅.gpr, r8₄, shr8 (by omega)]
  have r8₈ : u₈.gpr .r8 = BitVec.ofNat 64 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8) := by
    rw [e₈, m₇.gpr, r8₆, shr8 (by omega)]
  have k₁₃ : Only [.r3, .r4, .r6, .r7] u₉ u₁₃ := (o₁₀.trans (o₁₁.trans (o₁₂.trans o₁₃))).mono
  have hm : u₁₃.mem = (((t.mem.writeW (off (S s) oCtr + BitVec.ofNat 64 3) (BitVec.ofNat 8 c)).writeW
      (off (S s) oCtr + BitVec.ofNat 64 2) (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off (S s) oCtr + BitVec.ofNat 64 1)
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW (off (S s) oCtr + BitVec.ofNat 64 0)
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)) := by
    rw [k₁₃.mem, m₉.mem, r8₈, trunc8, o₈.mem, m₇.mem, r8₆, trunc8, o₆.mem, m₅.mem, r8₄, trunc8, o₄.mem, m₃.mem,
      r8₂, trunc8, k₂.mem]
  have hK : Keep [.r3, .r4, .r5, .r6, .r7, .r8] t u₁₃ :=
    (k₂.keep.trans (m₃.keep.trans (o₄.keep.trans (m₅.keep.trans (o₆.keep.trans (m₇.keep.trans
      (o₈.keep.trans (m₉.keep.trans k₁₃.keep)))))))).mono
  have hf : Frame [⟨off (S s) oCtr, 4⟩] t.mem u₁₃.mem := by
    rw [hm]
    have c : ∀ j < 4, Region.Contains ⟨off (S s) oCtr, 4⟩ (off (S s) oCtr + BitVec.ofNat 64 j) (8 / 8) :=
      fun j hj => Offset.contains_base _ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 2 (by omega)) |>.writeW (List.mem_singleton_self _) _ (c 1 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 0 (by omega))
  refine ⟨h.keep P hK hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    fun r hr => hK.gpr r (by revert r; decide), fun o ho => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, view_w8' _ _ (by omega) ho, view_w8' _ _ (by omega) ho, view_w8' _ _ (by omega) ho,
      view_w8' _ _ (by omega) ho, ctrV, i2osp_four]
    rcases (show o = oCtr ∨ o = oCtr + 1 ∨ o = oCtr + 2 ∨ o = oCtr + 3 ∨ ¬(oCtr ≤ o ∧ o < oCtr + 4) by omega) with
      h' | h' | h' | h' | h'
    · subst h'; simp
    · subst h'; simp
    · subst h'; simp
    · subst h'; simp
    · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), ifn h']
  · rw [o₁₃.get .r3, o₁₂.get .r3, o₁₁.get .r3, e₁₀, m₉.gpr, o₈.get .r14, m₇.gpr, o₆.get .r14, m₅.gpr,
      o₄.get .r14, m₃.gpr, k₂.get .r14, h.r14]
  · rw [o₁₃.get .r4, o₁₂.get .r4, e₁₁, o₁₀.get .r25, m₉.gpr, o₈.get .r25, m₇.gpr, o₆.get .r25, m₅.gpr,
      o₄.get .r25, m₃.gpr, k₂.get .r25]
  · rw [k₁₃.get .r5, m₉.gpr, o₈.get .r5, m₇.gpr, o₆.get .r5, m₅.gpr, o₄.get .r5, m₃.gpr, a₂]
  · rw [o₁₃.get .r6, e₁₂]
  · rw [e₁₃, o₁₂.get .r14, o₁₁.get .r14, o₁₀.get .r14, m₉.gpr, o₈.get .r14, m₇.gpr, o₆.get .r14, m₅.gpr,
      o₄.get .r14, m₃.gpr, k₂.get .r14, h.r14]

end

/-- How many bytes of the digest go into `dst`: `min(hLen, dstLen - done)`. -/
theorem xorHead_ok {G : Impl.Hmac.Stream.PPC64LE.Hash} {t : State} {S : Addr} {dst dstLen done : Nat}
    (hD : G.D < 2 ^ 15) (h14 : t.gpr .r14 = S) (h26 : t.gpr .r26 = off S dst) (h27 : t.gpr .r27 = BitVec.ofNat 64 dstLen)
    (h29 : t.gpr .r29 = BitVec.ofNat 64 done) (hlt : done < dstLen) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (xorHead G)) t fun t' => Only [.r6, .r7, .r8, .r9, .r10, .r11, .r12] t t' ∧
      t'.gpr .r11 = off S oDig ∧ t'.gpr .r12 = off S (dst + done) ∧
      t'.gpr .r9 = BitVec.ofNat 64 (min G.D (dstLen - done)) := by
  simp only [xorHead]
  refine wp_addi fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ => wp_li hD fun u₄ o₄ e₄ =>
    wp_sub fun u₅ o₅ e₅ => wp_lsr fun u₆ o₆ e₆ => wp_li (by decide) fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ =>
    wp_and fun u₉ o₉ e₉ => wp_add fun u₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k : Only [.r6, .r7, .r8, .r9, .r10, .r11, .r12] t u₁₀ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have r8 : u₃.gpr .r8 = BitVec.ofNat 64 (dstLen - done) := by
    rw [e₃, o₂.get .r27, o₂.get .r29, o₁.get .r27, o₁.get .r29, h27, h29, Offset.ofNat_sub_ofNat (by omega)]
  have r10 : u₅.gpr .r10 = BitVec.ofNat 64 (dstLen - done) - BitVec.ofNat 64 G.D := by
    rw [e₅, o₄.get .r8, r8, e₄]
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [o₁₀.get .r11, o₉.get .r11, o₈.get .r11, o₇.get .r11, o₆.get .r11, o₅.get .r11, o₄.get .r11, o₃.get .r11,
      o₂.get .r11, e₁, h14]
  · rw [o₁₀.get .r12, o₉.get .r12, o₈.get .r12, o₇.get .r12, o₆.get .r12, o₅.get .r12, o₄.get .r12, o₃.get .r12, e₂,
      o₁.get .r26, o₁.get .r29, h26, h29, off_add]
  · rw [e₁₀, o₉.get .r9, o₈.get .r9, o₇.get .r9, o₆.get .r9, o₅.get .r9, e₄, e₉, o₈.get .r10, o₇.get .r10,
      o₆.get .r10, r10, e₈, e₇, o₇.get .r6, e₆, r10]
    exact minSel (by omega) (by omega)

/-- `nextCtr`: the next counter and `done`, and in `r12` whether `done` is
still below `dstLen`. -/
theorem nextCtr_ok {G : Impl.Hmac.Stream.PPC64LE.Hash} {t : State} {c done dstLen : Nat}
    (h28 : t.gpr .r28 = BitVec.ofNat 64 c) (h29 : t.gpr .r29 = BitVec.ofNat 64 done)
    (h27 : t.gpr .r27 = BitVec.ofNat 64 dstLen) (hD : G.D < 2 ^ 15) (hd : done + G.D < 2 ^ 63) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (nextCtr G)) t fun t' => Only [.r28, .r29, .r12] t t' ∧
      t'.gpr .r28 = BitVec.ofNat 64 (c + 1) ∧ t'.gpr .r29 = BitVec.ofNat 64 (done + G.D) ∧
      (t'.gpr .r12 != 0) = decide (done + G.D < dstLen) := by
  simp only [nextCtr]
  refine wp_addi fun u₁ o₁ e₁ => wp_addi (h := hD) fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ => wp_lsr fun u₄ o₄ e₄ =>
    wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_, ?_⟩
  · rw [o₄.get .r28, o₃.get .r28, o₂.get .r28, e₁, h28, BitVec.ofNat_add]
  · rw [o₄.get .r29, o₃.get .r29, e₂, o₁.get .r29, h29, BitVec.ofNat_add]
  · rw [e₄, e₃, o₂.get .r27, e₂, o₁.get .r29, o₁.get .r27, h29, h27, ← BitVec.ofNat_add]
    exact ne_zero_ltBit hd hdl

/-- The `n` bytes at `p` XORed with those at `q`. -/
def xorAt (m : Mem) (p q : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i)

theorem xorAt_length (m : Mem) (p q : Addr) (n : Nat) : (xorAt m p q n).length = n := by simp [xorAt]

theorem xorAt_take_succ (m : Mem) (p q : Addr) {n i : Nat} (hi : i < n) :
    (xorAt m p q n).take (i + 1) =
      (xorAt m p q n).take i ++ [m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i)] := by
  simp only [xorAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

/-- `xorBody`'s loop XORs the `n` bytes at `r11 = q` into those at
`r12 = p`, counted down in `r9`. -/
theorem xorLoop_ok {t : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h11 : t.gpr .r11 = q) (h12 : t.gpr .r12 = p) (h9 : t.gpr .r9 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions t.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i)
    (hp : ∀ i < n, ∀ j < n, i ≠ j → p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j) :
    WP isa (.loop (.block xorBody) (.nonzero .d .r9)) t fun t' => Keep [.r8, .r9, .r10, .r11, .r12] t t' ∧
      t'.mem = writeBytes t.mem p (xorAt t.mem p q n) := by
  refine WP.mono (wp_countdown (cnt := .r9) hn' hn
    (fun i u => Keep [.r8, .r9, .r10, .r11, .r12] t u ∧
      u.mem = writeBytes t.mem p ((xorAt t.mem p q n).take i) ∧
      u.gpr .r12 = p + BitVec.ofNat 64 i ∧ u.gpr .r11 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h12], by simp [h11]⟩ h9) fun u h => ⟨h.1, ?_⟩
  · intro i hi u ⟨hK, hm, h12', h11'⟩ _
    have hR : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [h11', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hvq : u.mem (q + BitVec.ofNat 64 i) = t.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, xorAt_length]; omega)]
    have hvp : u.mem (p + BitVec.ofNat 64 i) = t.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun i' hi' => hp i hi i' (by omega) (by omega))
        (by simp only [List.length_take, xorAt_length]; omega)]
    refine wp_lbz rfl hR fun u₁ o₁ e₁ => ?_
    have hR' : InRegions (u₁.rd ++ u₁.wr) (u₁.gpr .r12 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.get .r12, h12', o₁.rd, o₁.wr, hK.rd, hK.wr, BitVec.add_zero]
      obtain ⟨r, hr', hc⟩ := hw i hi
      exact ⟨r, List.mem_append_right _ hr', hc⟩
    refine wp_lbz rfl hR' fun u₂ o₂ e₂ => wp_xor fun u₃ o₃ e₃ => ?_
    have hA : InRegions u₃.wr (u₃.gpr .r12 + BitVec.ofNat 64 0) 1 := by
      rw [o₃.wr, o₂.wr, o₁.wr, o₃.get .r12, o₂.get .r12, o₁.get .r12, h12', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun u₄ m₄ => wp_addi fun u₅ o₅ e₅ => wp_addi fun u₆ o₆ e₆ =>
      wp_subi fun u₇ o₇ e₇ => wp_nil ?_
    have hK' : Keep [.r8, .r9, .r10, .r11, .r12] u u₇ :=
      (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans
        o₇.keep)))))).mono
    have hlt : ((xorAt t.mem p q n).take i).length = i := by simp [xorAt_length]; omega
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₇.mem, o₆.mem, o₅.mem, m₄.mem, e₃, e₂, o₂.get .r10, e₁, o₃.mem, o₂.mem, o₁.mem, o₂.get .r12 |> fun _ =>
        o₃.get .r12]
      rw [o₂.get .r12, o₁.get .r12, h12', h11']
      simp only [BitVec.add_zero]
      rw [hvp, hvq, byte_xor, hm, xorAt_take_succ _ _ _ hi, writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₇.get .r12, e₆, o₅.get .r12, m₄.gpr, o₃.get .r12, o₂.get .r12, o₁.get .r12, h12', ofNat_succ']
    · rw [o₇.get .r11, o₆.get .r11, e₅, m₄.gpr, o₃.get .r11, o₂.get .r11, o₁.get .r11, h11', ofNat_succ']
    · rw [e₇, o₆.get .r9, o₅.get .r9, m₄.gpr, o₃.get .r9, o₂.get .r9, o₁.get .r9]
  · rw [List.take_of_length_le (by simp [xorAt_length])] at h
    exact h.2.1

end VG.Proof.RsaOaep.PPC64LE
