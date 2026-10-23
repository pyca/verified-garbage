module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.AesGcm.Bytes
import VerifiedGarbage.Proof.AesGcm.CmpBytes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Buffer

/-!
# AES-GCM on PPC64LE: checking a received tag (`tagLenOk`, `cmp`)

Untrusted: everything here is checked by Lean. `pad b o` writes the `r24`
bytes at `b` padded with zeros to `W + o` (`pad_wp`); `cmpTail` leaves 1 in
`r3` if the 16 bytes at `W + vpO` and `W + rO` are equal and 0 if not,
without a branch (`cmpTail_wp`); so `cmp` leaves 1 iff the received tag (at
`r23`) is the first `r24` bytes of the computed one at `W + vO` (`cmp_wp`).
`tagLenOk ok bad` runs `ok` iff `tagLenOk` allows a tag of `r24` bytes
(`tagLenOk_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_ld wp_std wp_xor wp_or wp_sub wp_lsr)
open VG.Spec.Gcm (zeros)
open VG.Spec.Aes (bytesAt)

/-- Before `pad b o`: the `t` bytes at `S` (in `b`) and `W + o` apart. -/
structure PadPre (s : State) (W St C : Addr) (b : Reg) (o : Nat) (S : Addr) (t : Nat) : Prop where
  env : Env s W St C
  hb : s.gpr b = S
  hb0 : b ≠ .r0
  r24 : s.gpr .r24 = BitVec.ofNat 64 t
  pos : 1 ≤ t
  le : t ≤ 16
  ho : o + 16 ≤ 2112 ∧ o % 4 = 0
  rd : Covers [⟨S, t⟩] (s.rd ++ s.wr)
  disj : (⟨S, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 o, 16⟩

/-- After `pad b o`. -/
structure PadPost (s₀ : State) (W : Addr) (o : Nat) (S : Addr) (t : Nat) (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s₀.mem s.mem
  out : bytesAt s.mem (W + BitVec.ofNat 64 o) 16 = bytesAt s₀.mem S t ++ zeros (16 - t)

theorem pad_wp {s : State} {W St C : Addr} {b : Reg} {o : Nat} {S : Addr} {t : Nat}
    (hp : PadPre s W St C b o S t) : WP isa (pad b o) s (PadPost s W o S t) := by
  have he := hp.env
  have ho := hp.ho
  have hle := hp.le
  have hpos := hp.pos
  simp only [pad, zero16, List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_std (a := W + BitVec.ofNat 64 o) (by decide) ⟨by omega, ho.2⟩
    (by rw [u₁.other _ (by decide), he.r14]) (by rw [u₁.wr]; exact he.wInR (by omega)) fun s₂ u₂ => ?_
  refine wp_std (a := W + BitVec.ofNat 64 (o + 8)) (by decide) ⟨by omega, by omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide), he.r14]) (by rw [u₂.wr, u₁.wr]; exact he.wInR (by omega))
    fun s₃ u₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_addi (by decide) (by omega) fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans
    ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have hm₆ : s₆.mem = writeBytes s.mem (W + BitVec.ofNat 64 o) (zeros 16) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr, ← Offset.add_add]
    exact Proof.AesGcm.write_zeros16 _ _
  have hz : (zeros 16).length = 16 := Proof.Gcm.length_zeros 16
  have f₆ : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem s₆.mem := by
    rw [hm₆]; exact Proof.AesGcm.writeBytes_frame' _ hz
  have hS : bytesAt s₆.mem S t = bytesAt s.mem S t :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by omega)
  have hcont : Region.Sub ⟨W + BitVec.ofNat 64 o, t⟩ ⟨W + BitVec.ofNat 64 o, 16⟩ := Region.sub_prefix hp.le
  have hq : VG.Proof.Gather.PPC64LE.BytesPre s₆ S (W + BitVec.ofNat 64 o) t :=
    { r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        u₁.other _ hp.hb0, hp.hb]
      r9 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr,
        u₁.other _ (by decide), he.r14]
      r4 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
        u₁.other _ (by decide), hp.r24]
      pos := hp.pos
      lt := by omega
      rd := by rw [pk₆.rd, pk₆.wr]; exact hp.rd
      wr := by
        rw [pk₆.wr]
        exact VG.Proof.Gather.PPC64LE.covers_prefix (he.wIn (d := o) (n := 16) (by omega)) hp.le
      disj := hp.disj.sub_right hcont }
  refine WP.mono (VG.Proof.Gather.PPC64LE.copyBytes_wp s₆ hq) fun s₇ ⟨hm₇, _, k₇⟩ => ?_
  have hl : (bytesAt s₆.mem S t).length = t := Proof.AesGcm.length_bytesAt _ _ _
  refine ⟨pk₆.trans (PK.ofKeeps k₇), f₆.trans ?_, ?_⟩
  · rw [hm₇]
    refine writeBytes_frame _ _ _ ?_
    rw [hl]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
    exact hp.le
  · have hz₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 o) 16 = zeros 16 := by
      have hb := Proof.AesGcm.bytesAt_writeBytes_self s.mem (W + BitVec.ofNat 64 o) (zeros 16)
        (by rw [hz]; omega)
      rw [hz] at hb; rw [hm₆, hb]
    rw [hm₇, Proof.AesGcm.pad_bytes hz₆ _ (by omega), hl, hS]

/-- `1 - ((d ||| -d) >>> 63)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - ((d ||| (BitVec.ofNat 64 0 - d)) >>> 63) = BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  have h := Proof.AesGcm.neg_or_msb d
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl, h]
  by_cases hd : d = 0 <;> simp only [hd, ite_true, ite_false] <;> decide

/-- `r3` is 1 iff the 16 bytes at `W + vpO` and at `W + rO` are equal. -/
theorem cmpTail_wp {s : State} {W St C : Addr} (he : Env s W St C) :
    WP isa (.block cmpTail) s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r3 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 2080) 16 =
        bytesAt s.mem (W + BitVec.ofNat 64 2096) 16 then 1 else 0) := by
  unfold cmpTail
  refine wp_ld (a := W + BitVec.ofNat 64 2080) (by decide) (by decide) (by rw [he.r14]; rfl)
    (he.wRdR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := W + BitVec.ofNat 64 2096) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), he.r14]; rfl) (by rw [u₁.rd, u₁.wr]; exact he.wRdR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := W + BitVec.ofNat 64 2088) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), he.r14]; rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.wRdR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := W + BitVec.ofNat 64 2104) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      he.r14]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.wRdR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃)))))))))))),
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .r5 = (s.mem.readW (W + BitVec.ofNat 64 2080) 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 2096) 64) |||
      (s.mem.readW (W + BitVec.ofNat 64 2088) 64 ^^^ s.mem.readW (W + BitVec.ofNat 64 2104) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .r5 (by decide), u₅.gpr, u₅.other .r6 (by decide), u₄.gpr,
      u₅.other .r5 (by decide), u₄.other .r5 (by decide), u₃.gpr, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other .r5 (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .r5 (by decide),
    u₈.gpr, u₈.other .r5 (by decide), hd, zero_test]
  have hw := Proof.AesGcm.words_eq s.mem (W + BitVec.ofNat 64 2080) (W + BitVec.ofNat 64 2096)
  rw [Offset.add_add, Offset.add_add] at hw
  congr 2
  exact propext hw

/-- `cmp`: 1 in `r3` iff the `t` bytes at `Tg` (`r23`) are the first `t` of the
computed tag at `W + vO`. -/
theorem cmp_wp {s : State} {W St C Tg : Addr} {t : Nat} (he : Env s W St C) (h23 : s.gpr .r23 = Tg)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 t) (hpos : 1 ≤ t) (hle : t ≤ 16) (hrd : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hdw : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa cmp s fun s' => PK s s' ∧ Frame [wR W] s.mem s'.mem ∧
      s'.gpr .r3 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 2064) t = bytesAt s.mem Tg t then 1 else 0) := by
  unfold cmp
  have hp₁ : PadPre s W St C .r23 2096 Tg t :=
    { env := he, hb := h23, hb0 := by decide, r24 := h24, pos := hpos, le := hle, ho := by decide, rd := hrd
      disj := hdw.sub_right (Offset.sub_base W (by decide)) }
  refine WP.seq (WP.mono (pad_wp (o := 2096) hp₁) fun s₁ P₁ => ?_)
  refine WP.seq (WP.seq (wp_addi (by decide) (by decide) fun s₂ u₂ => WP.block_nil ?_))
  have he₂ : Env s₂ W St C := he.of_pk (P₁.pk.trans (PK.ofUpd u₂))
  have hv : bytesAt s₂.mem (W + BitVec.ofNat 64 2064) t = bytesAt s.mem (W + BitVec.ofNat 64 2064) t := by
    rw [u₂.mem]
    exact Proof.Cmac.bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by omega) (by omega) (by omega)) (by omega)
  have hp₂ : PadPre s₂ W St C .r12 2080 (W + BitVec.ofNat 64 2064) t :=
    { env := he₂
      hb := by rw [u₂.gpr, P₁.pk.gpr .r14 (by decide), he.r14]; rfl
      hb0 := by decide
      r24 := by rw [u₂.other _ (by decide), P₁.pk.gpr .r24 (by decide), h24]
      pos := hpos
      le := hle
      ho := by decide
      rd := VG.Covers.right (VG.Proof.Gather.PPC64LE.covers_prefix (he₂.wIn (d := 2064) (n := 16) (by decide))
        hle)
      disj := Offset.disjoint W (by omega) (by omega) (by decide) }
  refine WP.mono (pad_wp (o := 2080) hp₂) fun s₃ P₃ => ?_
  refine WP.mono (cmpTail_wp (he₂.of_pk P₃.pk)) fun s₄ ⟨pk₄, m₄, r3₄⟩ => ?_
  have hr : bytesAt s₃.mem (W + BitVec.ofNat 64 2096) 16 = bytesAt s.mem Tg t ++ zeros (16 - t) := by
    rw [Proof.Cmac.bytesAt_frame P₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (by decide) (by decide) (by decide)) (by decide), u₂.mem, P₁.out]
  refine ⟨P₁.pk.trans ((PK.ofUpd u₂).trans (P₃.pk.trans pk₄)), ?_, ?_⟩
  · have f₁ : Frame [wR W] s.mem s₁.mem := P₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base W (by decide)⟩
    have f₃ : Frame [wR W] s₂.mem s₃.mem := P₃.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base W (by decide)⟩
    rw [u₂.mem] at f₃
    rw [m₄]; exact f₁.trans f₃
  · rw [r3₄, P₃.out, hr, hv]
    congr 2
    exact propext (Proof.AesGcm.pad_eq (by rw [Proof.AesGcm.length_bytesAt, Proof.AesGcm.length_bytesAt]))

theorem beq_zero (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · rintro rfl; rfl
  · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)

/-- `tagLenOk ok bad` runs `ok` iff a tag of `t` bytes is allowed. -/
theorem tagLenOk_wp {s : State} {t : Nat} {ok bad : Prog isa} {Q : State → Prop}
    (h24 : s.gpr .r24 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64)
    (hok : ∀ s', PK s s' → Spec.Gcm.tagLenOk t = true → WP isa ok s' Q)
    (hbad : ∀ s', PK s s' → Spec.Gcm.tagLenOk t = false → WP isa bad s' Q) :
    WP isa (tagLenOk ok bad) s Q := by
  unfold tagLenOk
  refine WP.seq (wp_subi (by decide) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have r5 : s₂.gpr .r5 = BitVec.ofNat 64 t - BitVec.ofNat 64 4 := by
    rw [u₂.other _ (by decide), u₁.gpr, h24]
  have hx : (BitVec.ofNat 64 t - BitVec.ofNat 64 4).toNat = (2 ^ 64 - 4 + t) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (by decide : 4 < 2 ^ 64)]
  refine WP.ite (decide (4 ≤ t ∧ t < 20))
    (by
      rw [VG.Proof.Poly1305.PPC64LE.eval_zero, u₂.gpr, u₁.gpr, h24, beq_zero, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, hx]
      exact congrArg some (decide_eq_decide.mpr (by omega)))
    (fun ht₁ => ?_) (fun hf₁ => hbad _ pk₂ (by
      have := of_decide_eq_false hf₁
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega))
  have h₁ := of_decide_eq_true ht₁
  refine WP.seq (wp_subi (by decide) (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_)
  have pk₄ : PK s s₄ := pk₂.trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄))
  refine WP.ite (decide (17 ≤ t))
    (by
      rw [VG.Proof.Poly1305.PPC64LE.eval_zero, u₄.gpr, u₃.gpr, r5, beq_zero, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hx, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by decide : 13 < 2 ^ 64)]
      exact congrArg some (decide_eq_decide.mpr (by omega)))
    (fun ht₂ => hbad _ pk₄ (by
      have := of_decide_eq_true ht₂
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fun hf₂ => hok _ pk₄ (by
      have := of_decide_eq_false hf₂
      simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq]; omega))

end VG.Proof.AesGcm.PPC64LE
