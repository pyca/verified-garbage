module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncPre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverMask
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncPre
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.RecoverMask
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two

/-! ### `RsaPkcs1Enc.PPC64LE.EncCT`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: the taint checks

The code around the call, checked by the taint analysis from the stack
pointer and the registers holding public values: after the setup, `PS`'s
place and length (loaded from the stack), `EM`'s place and the message's
place and length; after the call, `out` and `k` in `r28` and `r29`. `PS`
and `M` are secret: only copied, and `PS`'s zero test only masks.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.Proof.RsaPkcs1Sig.PPC64LE

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block setup) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem preCall_taint (h : Pins Φ [.r4, .r9, .r10, .r11, .r12]) : RelCT isa (Two Φ) preCall fun _ _ => True :=
  two_taint [.r4, .r9, .r10, .r11, .r12] h (by taint_decide)

theorem tail_taint (h : Pins Φ [.r28, .r29]) : RelCT isa (Two Φ) tail fun _ _ => True :=
  two_taint [.r28, .r29] h (by taint_decide)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

end

end

/-! ### `RsaPkcs1Enc.PPC64LE.EncCorrect`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.EncCall`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.PPC64LE.EncLoops`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: the loops

Untrusted: everything here is checked by Lean. `psLoop_ok`: `PS` is copied,
and the low bit of `r5` set if one of its bytes is zero (`zbit`).
`msgLoop_ok`: `M` is copied. `maskLoop_ok`: `out`'s bytes are masked with
`r5` and `EM`'s zeroed. As `encode`'s loops (`Proof/RsaPkcs1Sig/PPC64LE/Encode.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)

/-- 1 if one of the bytes is zero, 0 if not. -/
def zbit (l : List Byte) : BitVec 64 := if l.all (· != 0) then 0 else 1

theorem zbit_nil : zbit [] = 0 := rfl

theorem zbit_snoc (l : List Byte) (b : Byte) :
    zbit (l ++ [b]) = zbit l ||| (if b = 0 then 1 else 0) := by
  unfold zbit
  rw [List.all_append]
  cases hl : l.all (· != 0) <;> by_cases hb : b = 0 <;> simp [hb] <;> first | decide | (split <;> decide)

theorem byte_toNat_lt (b : Byte) : (b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_setWidth]; have := b.isLt; omega_using []

theorem setWidth_eq_zero {b : Byte} : (b.setWidth 64 = 0) ↔ b = 0 := by
  constructor
  · intro h; have := congrArg (BitVec.setWidth 8) h; simpa using this
  · intro h; rw [h]; rfl

/-- `psLoop` copies the `n` bytes at `r4 = q` to `r11 = p`, counted down in
`r12`, and ORs their zero test into `r5`. -/
theorem psLoop_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = q) (h11 : s.gpr .r11 = p) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa psLoop s fun t => Keep [.r0, .r3, .r4, .r5, .r11, .r12] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .r5 = s.gpr .r5 ||| zbit (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .r11 = p + BitVec.ofNat 64 n := by
  refine WP.mono (wp_countdown (cnt := .r12) hn' hn
    (fun i t => Keep [.r0, .r3, .r4, .r5, .r11, .r12] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .r4 = q + BitVec.ofNat 64 i ∧ t.gpr .r11 = p + BitVec.ofNat 64 i ∧
      t.gpr .r5 = s.gpr .r5 ||| zbit ((Spec.Rsa.bytesAt s.mem q n).take i)) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h4], by simp [h11], by simp [zbit_nil]⟩ h12)
    fun t h => ⟨h.1, ?_, ?_, h.2.2.2.1⟩
  · intro i hi t ⟨hK, hm, h4', h11', h5'⟩ _
    obtain hR : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    obtain hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega_using [])]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => ?_
    obtain hA : InRegions s₁.wr (s₁.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .r11, h11', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₂ m₂ => wp_subi fun s₃ o₃ e₃ => wp_lsr fun s₄ o₄ e₄ => wp_or fun s₅ o₅ e₅ =>
      wp_addi fun s₆ o₆ e₆ => wp_addi fun s₇ o₇ e₇ => wp_subi fun s₈ o₈ e₈ => wp_nil ?_
    obtain hK' : Keep [.r0, .r3, .r4, .r5, .r11, .r12] t s₈ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
        (o₇.keep.trans o₈.keep))))))).mono
    obtain hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega_using [hi]
    obtain hb : s₂.gpr .r3 = (s.mem (q + BitVec.ofNat 64 i)).setWidth 64 := by
      rw [m₂.gpr, e₁, h4', BitVec.add_zero, hv]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h4', o₁.get .r11, h11']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, hm, bytesAt_take_succ _ _ hi, writeBytes_snoc _ _ _ _ (by omega_using [hn', hi, hlt]), hlt]
    · rw [o₈.get .r4, o₇.get .r4, e₆, o₅.get .r4, o₄.get .r4, o₃.get .r4, m₂.gpr, o₁.get .r4, h4', ofNat_succ']
    · rw [o₈.get .r11, e₇, o₆.get .r11, o₅.get .r11, o₄.get .r11, o₃.get .r11, m₂.gpr, o₁.get .r11, h11',
        ofNat_succ']
    · rw [o₈.get .r5, o₇.get .r5, o₆.get .r5, e₅, o₄.get .r5, e₄, o₃.get .r5, e₃, hb, m₂.gpr, o₁.get .r5, h5',
        borrow1 (byte_toNat_lt _), bytesAt_take_succ _ _ hi, zbit_snoc, BitVec.or_assoc]
      congr 2
      by_cases h : s.mem (q + BitVec.ofNat 64 i) = 0
      · rw [ite_eq_left h, ite_eq_left (setWidth_eq_zero.mpr h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (setWidth_eq_zero.mp h'))]
    · rw [e₈, o₇.get .r12, o₆.get .r12, o₅.get .r12, o₄.get .r12, o₃.get .r12, m₂.gpr, o₁.get .r12]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.2.2.2

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

end

end


/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: up to the call

`setup_ok`: the saves, `out`, `k`, `e` and `e_len` kept in `r28`–`r31`, and
`EM`'s first two bytes (`Setup`). `em_ok`: `PS`, the separator and `M`
complete `EM = encode M PS` (`EmDone`), with `PS`'s zero test in `r5`.
`callArgs_ok` and `call_ok`: the call writes RSAEP of `EM` to `out` if `pre`
holds the modulus' values (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- In the frame: `out`, `k`, `e` and `e_len` kept. -/
abbrev EMid (s t : State) : Prop := Mid (scR s) s (s.gpr .r3) (s.gpr .r6) (s.gpr .r7) (s.gpr .r8) t

/-- `EM`'s place. -/
abbrev emA (s : State) : Addr := fb s + BitVec.ofNat 64 oEM

/-- `EM` holds `xs` over some memory `M₀`. -/
def Em (s : State) (xs : List Byte) (t : State) : Prop := ∃ M₀ : Mem, t.mem = writeBytes M₀ (emA s) xs

section
variable {s : State}

theorem in_a6R {j : Nat} (hj : j < 6) : (a6R s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem arg_rd (hp : PreE s) (rs : List Region) {j : Nat} (hj : j < 6) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨a6R s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_a6R hj⟩

theorem arg_frame (hp : PreE s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 6) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_a6R hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

/-- A stack argument, in memory changed only in the frame and the working
space. -/
theorem arg_mid (hp : PreE s) {m : Mem} (h : Frame [kR s, scR s] s.mem m) {j : Nat} (hj : j < 6) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_a6R hj) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ka.symm
    · exact hp.sa.symm) (by decide)

end

theorem add_ofNat_ofNat (a : Addr) (d e : Nat) :
    a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- After the setup. -/
structure Setup (s w : State) : Prop extends
    Mid (scR s) s (s.gpr .r3) (s.gpr .r6) (s.gpr .r7) (s.gpr .r8) w where
  em : Em s [0x00, 0x02] w
  g4 : w.gpr .r4 = stackArg s 0
  g5 : w.gpr .r5 = 0
  g9 : w.gpr .r9 = s.gpr .r9
  g10 : w.gpr .r10 = s.gpr .r10
  g11 : w.gpr .r11 = fb s + BitVec.ofNat 64 (oEM + 2)
  g12 : w.gpr .r12 = stackArg s 1

theorem setup_ok {s u : State} (hp : PreE s) (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.r11, .r12] → u.gpr r = s.gpr r)
    (hlr : u.lr = s.lr) :
    WP isa (.block setup) u (Setup s) := by
  unfold setup
  refine save_ok hsp hwr hm (fun r hr => hg r (by revert r; decide)) hlr fun v kv v12 fv sv lv => ?_
  obtain gv : ∀ r, r ∉ [Reg.r12, .r0, .r11] → v.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kv.gpr r (by simp [hr.1, hr.2.1]), hg r (by simp [hr.1, hr.2.2])]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_li (by decide) fun v₅ o₅ e₅ => ?_
  obtain O₅ : Only [.r28, .r29, .r30, .r31, .r0] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  obtain r12₅ : v₅.gpr .r12 = fb s := by rw [O₅.get .r12, v12]
  obtain wr₅ : v₅.wr = fr s :: s.wr := by rw [O₅.wr, kv.wr, hwr]
  refine wp_stb (a := emA s) (by rw [r12₅]) (by rw [wr₅]; exact in_fr s _ (by decide) (by decide))
    fun v₆ m₆ => wp_li (by decide) fun v₇ o₇ e₇ => ?_
  refine wp_stb (a := emA s + BitVec.ofNat 64 1) (by rw [o₇.get .r12, m₆.gpr, r12₅, add_ofNat_ofNat])
    (by rw [o₇.wr, m₆.wr, wr₅, add_ofNat_ofNat]; exact in_fr s _ (by decide) (by decide)) fun v₈ m₈ => ?_
  obtain r12₈ : v₈.gpr .r12 = fb s := by rw [m₈.gpr, o₇.get .r12, m₆.gpr, r12₅]
  obtain rd₈ : v₈.rd = s.rd := by rw [m₈.rd, o₇.rd, m₆.rd, O₅.rd, kv.rd, hrd]
  obtain mem₈ : v₈.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by
    obtain b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
    obtain b2 : (BitVec.ofNat 64 2).setWidth 8 = (0x02 : Byte) := by decide
    rw [m₈.mem, o₇.mem, m₆.mem, O₅.mem, e₇, e₅, b0, b2,
      show ([0x00, 0x02] : List Byte) = [] ++ [0x00] ++ [0x02] from rfl, writeBytes_snoc _ _ _ _ (by decide),
      writeBytes_snoc _ _ _ _ (by decide), writeBytes_nil]
    simp only [List.length_nil, List.nil_append, List.length_singleton, BitVec.add_zero]
  obtain fr₈ : Frame [kR s] s.mem v₈.mem := by
    rw [mem₈]
    obtain hw := frame_writeBytes v.mem (emA s) [0x00, 0x02]
    exact fv.trans (hw.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM) (n := 2) (by decide)⟩)
  obtain hdS : ∀ {d k : Nat}, d + k ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨emA s, 2⟩ := fun hk =>
    Offset.disjoint _ (.inl (by unfold oLr oEM oEM1 at *; omega_arith)) (by unfold oLr at hk; omega_arith) (by decide)
  refine wp_ld (a := stackArgAddr s 0) (by rw [r12₈, stackArgAddr_fb]) (by rw [rd₈]; exact arg_rd hp _ (by decide))
    fun v₉ o₉ e₉ => wp_addi fun v₁₀ o₁₀ e₁₀ => wp_li (by decide) fun v₁₁ o₁₁ e₁₁ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₁₁.get .r12, o₁₀.get .r12, o₉.get .r12, r12₈, stackArgAddr_fb])
    (by rw [o₁₁.rd, o₁₀.rd, o₉.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₂ o₁₂ e₁₂ => wp_nil ?_
  obtain O₁₂ : Only [.r4, .r11, .r5, .r12] v₈ v₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  obtain g₈ : ∀ r, r ∉ [Reg.r0] → v₈.gpr r = v₅.gpr r := fun r hr => by rw [m₈.gpr, o₇.gpr r hr, m₆.gpr]
  obtain mem₁₂ : v₁₂.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by rw [O₁₂.mem, mem₈]
  refine {
    sp := by rw [O₁₂.sp, m₈.sp, o₇.sp, m₆.sp, O₅.sp, kv.sp, hsp]
    rd := by rw [O₁₂.rd, rd₈]
    wr := by rw [O₁₂.wr, m₈.wr, o₇.wr, m₆.wr, wr₅]
    r28 := by
      rw [O₁₂.get .r28, g₈ .r28 (by decide), o₅.get .r28, o₄.get .r28, o₃.get .r28, o₂.get .r28, e₁,
        gv .r3 (by decide)]
    r29 := by
      rw [O₁₂.get .r29, g₈ .r29 (by decide), o₅.get .r29, o₄.get .r29, o₃.get .r29, e₂, o₁.get .r6,
        gv .r6 (by decide)]
    r30 := by
      rw [O₁₂.get .r30, g₈ .r30 (by decide), o₅.get .r30, o₄.get .r30, e₃, o₂.get .r7, o₁.get .r7,
        gv .r7 (by decide)]
    r31 := by
      rw [O₁₂.get .r31, g₈ .r31 (by decide), o₅.get .r31, e₄, o₃.get .r8, o₂.get .r8, o₁.get .r8,
        gv .r8 (by decide)]
    hi := fun r hr => by
      obtain h₁ : r ∉ [Reg.r4, .r11, .r5, .r12] := by revert r; decide
      obtain h₂ : r ∉ [Reg.r0] := by revert r; decide
      obtain h₃ : r ∉ [Reg.r28, .r29, .r30, .r31, .r0] := by revert r; decide
      obtain h₄ : r ∉ [Reg.r12, .r0, .r11] := by revert r; decide
      rw [O₁₂.gpr r h₁, g₈ r h₂, O₅.gpr r h₃, gv r h₄]
    mem := by
      rw [O₁₂.mem]
      exact fr₈.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₂]
      exact sv.frame (frame_writeBytes v.mem (emA s) [0x00, 0x02]) fun p hp r hr => by
        rw [List.mem_singleton.mp hr]; exact hdS (by have := saved_offs p hp; unfold oSave oLr at *; omega_arith)
    ls := by
      rw [mem₁₂, (frame_writeBytes v.mem (emA s) [0x00, 0x02]).readW (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdS (by decide)) (by decide)]
      exact lv
    em := ⟨v.mem, mem₁₂⟩
    g4 := by rw [o₁₂.get .r4, o₁₁.get .r4, o₁₀.get .r4, e₉, arg_frame hp fr₈ (by decide)]
    g5 := by rw [o₁₂.get .r5, e₁₁]; rfl
    g9 := by rw [O₁₂.get .r9, g₈ .r9 (by decide), O₅.get .r9, gv .r9 (by decide)]
    g10 := by rw [O₁₂.get .r10, g₈ .r10 (by decide), O₅.get .r10, gv .r10 (by decide)]
    g11 := by rw [o₁₂.get .r11, o₁₁.get .r11, e₁₀, o₉.get .r12, r12₈]
    g12 := by rw [e₁₂, o₁₁.mem, o₁₀.mem, o₉.mem, arg_frame hp fr₈ (by decide)] }

/-- `M` and `PS`, from the entry state. -/
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
abbrev psB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat

/-- `EM` complete, `PS`'s zero test in `r5`, `r12` the frame's base. -/
structure EmDone (s y : State) : Prop extends EMid s y where
  em : Em s (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)) y
  g5 : y.gpr .r5 = zbit (psB s)
  g12 : y.gpr .r12 = fb s

theorem em_ok {s w : State} (hp : PreE s) (hs : Setup s w) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ y, EmDone s y → WP isa rest y Q) :
    WP isa (.seq psLoop (.seq (.block sep) (.seq msgCopy rest))) w Q := by
  obtain hk1 := hp.k1; have hk2 := hp.k2; have hml := hp.ml; have hpl := hp.pl
  obtain ⟨M₀, hM₀⟩ := hs.em
  obtain hn : 0 < (stackArg s 1).toNat := by omega_arith
  obtain hdP : (psR s).Disjoint ⟨emA s + BitVec.ofNat 64 2, (stackArg s 1).toNat⟩ := by
    rw [add_ofNat_ofNat]
    exact (hp.kps.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM + 2) (n := (stackArg s 1).toNat)
      (by unfold oEM oEM1 frameBytes; omega_arith))).symm
  refine WP.seq (WP.mono (psLoop_ok (p := emA s + BitVec.ofNat 64 2) (q := stackArg s 0)
    (n := (stackArg s 1).toNat) hn (by omega_arith) hs.g4 (by rw [hs.g11, add_ofNat_ofNat]) (by rw [hs.g12]; simp)
    (fun j hj => ⟨psR s, List.mem_append_left _ (by rw [hs.rd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by have := hp.wps; omega_arith)⟩)
    (fun i hi => by
      rw [hs.wr, add_ofNat_ofNat, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith))
    (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdP (by omega_arith) (by omega_arith) hj hi))
    fun y₁ ⟨k₁, m₁, r5₁, r11₁⟩ => ?_)
  obtain hPS : Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat = psB s :=
    bytes_of_frame hs.mem hp.kps hp.pss.symm (by have := hp.wps; omega_arith)
  obtain hl2 : ([(0x00 : Byte), 0x02] ++ psB s).length = 2 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  obtain mem₁ : y₁.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s) := by
    rw [m₁, hPS, hM₀, ← writeBytes_append _ _ _ _ (by rw [← List.length_append, hl2]; omega_arith)]
    rfl
  obtain fr₁ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2), (stackArg s 1).toNat⟩] w.mem y₁.mem := by
    obtain h := frame_writeBytes w.mem (emA s + BitVec.ofNat 64 2)
      (Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat)
    rw [bytesAt_length, add_ofNat_ofNat] at h
    rw [m₁, add_ofNat_ofNat]; exact h
  obtain mid₁ : EMid s y₁ := hs.toMid.frameW1 k₁ hp.ksc (by decide) (by unfold oEM oEM1 frameBytes; omega_arith) fr₁
  obtain b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
  obtain inEM : ∀ {d n : Nat}, d + n ≤ 1024 → InRegions (fr s :: s.wr) (emA s + BitVec.ofNat 64 d) n :=
    fun h => by rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith)
  refine WP.seq (wp_li (by decide) fun y₂ o₂ e₂ =>
    wp_stb (a := emA s + BitVec.ofNat 64 (2 + (stackArg s 1).toNat))
      (by rw [o₂.get .r11, r11₁, BitVec.add_zero, add_ofNat_ofNat])
      (by rw [o₂.wr, mid₁.wr]; exact inEM (by omega_arith)) fun y₃ m₃ =>
    wp_addi fun y₄ o₄ e₄ => wp_addSp fun y₅ o₅ e₅ => wp_nil ?_)
  obtain hl3 : ([(0x00 : Byte), 0x02] ++ psB s ++ [0x00]).length = 3 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  obtain mem₃ : y₃.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by
    rw [writeBytes_snoc _ _ _ _ (by omega_arith), hl2, m₃.mem, o₂.mem, mem₁, e₂, b0]
  obtain fr₃ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2 + (stackArg s 1).toNat), 1⟩] y₁.mem y₃.mem := by
    rw [m₃.mem, o₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (by
      rw [add_ofNat_ofNat, show oEM + (2 + (stackArg s 1).toNat) = oEM + 2 + (stackArg s 1).toNat by omega_arith]
      exact Region.contains_self _ _)
  obtain mid₃ : EMid s y₃ := mid₁.frameW1 (o₂.keep.trans m₃.keep) hp.ksc (by unfold oLr oEM oEM1; omega_arith)
    (by unfold oEM oEM1 frameBytes; omega_arith) fr₃
  obtain O₅ : Only [.r11, .r12] y₃ y₅ := o₄.trans o₅
  obtain mid₅ : EMid s y₅ := mid₃.only O₅
  obtain r12₅ : y₅.gpr .r12 = fb s := by rw [e₅, o₄.sp, m₃.sp, o₂.sp, mid₁.sp, BitVec.add_zero]
  obtain r11₅ : y₅.gpr .r11 = emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat) := by
    rw [o₅.get .r11, e₄, m₃.gpr, o₂.get .r11, r11₁, ofNat_succ', add_ofNat_ofNat,
      show 2 + ((stackArg s 1).toNat + 1) = 3 + (stackArg s 1).toNat by omega_arith]
  obtain r5₅ : y₅.gpr .r5 = zbit (psB s) := by
    rw [O₅.get .r5, m₃.gpr, o₂.get .r5, r5₁, hs.g5, hPS]; simp
  obtain r10₅ : y₅.gpr .r10 = s.gpr .r10 := by
    rw [O₅.get .r10, m₃.gpr, o₂.get .r10, k₁.get .r10, hs.g10]
  obtain r9₅ : y₅.gpr .r9 = s.gpr .r9 := by
    rw [O₅.get .r9, m₃.gpr, o₂.get .r9, k₁.get .r9, hs.g9]
  obtain mem₅ : y₅.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by rw [O₅.mem, mem₃]
  refine WP.seq ?_
  unfold msgCopy
  by_cases hm0 : (s.gpr .r10).toNat = 0
  · refine WP.ite false (by rw [eval_nonzero, ne_zero_iff, r10₅, hm0]; rfl) (by simp) fun _ => wp_nil ?_
    refine k y₅ ⟨mid₅, ⟨M₀, ?_⟩, r5₅, r12₅⟩
    rw [mem₅]
    unfold Spec.RsaPkcs1Enc.encode msgB
    rw [hm0]
    simp [Spec.Rsa.bytesAt]
  · refine WP.ite true (by rw [eval_nonzero, ne_zero_iff, r10₅]; simp [hm0]) (fun _ => ?_) (by simp)
    refine WP.seq (wp_mov fun c₁ p₁ f₁ => wp_mov fun c₂ p₂ f₂ => wp_mov fun c₃ p₃ f₃ => wp_nil ?_)
    obtain P₃ : Only [.r7, .r4, .r8] y₅ c₃ := p₁.trans (p₂.trans p₃)
    obtain midc : EMid s c₃ := mid₅.only P₃
    obtain hdM : (mR s).Disjoint ⟨emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat), (s.gpr .r10).toNat⟩ := by
      rw [add_ofNat_ofNat]
      exact (hp.km.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM + (3 + (stackArg s 1).toNat)) (n := (s.gpr .r10).toNat)
        (by unfold oEM oEM1 frameBytes; omega_arith))).symm
    obtain hM : Spec.Rsa.bytesAt c₃.mem (s.gpr .r9) (s.gpr .r10).toNat = msgB s :=
      bytes_of_frame midc.mem hp.km hp.ms.symm (by have := hp.wm; omega_arith)
    refine WP.mono (copy_ok (p := emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat)) (q := s.gpr .r9)
      (n := (s.gpr .r10).toNat) (by omega_arith) (by omega_arith) (by rw [p₃.get .r4, f₂, p₁.get .r11, r11₅])
      (by rw [p₃.get .r7, p₂.get .r7, f₁, r9₅]) (by rw [f₃, p₂.get .r10, p₁.get .r10, r10₅]; simp)
      (fun j hj => ⟨mR s, List.mem_append_left _ (by rw [midc.rd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by have := hp.wm; omega_arith)⟩)
      (fun i hi => by rw [midc.wr, add_ofNat_ofNat]; exact inEM (by omega_arith))
      (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdM (by omega_arith) (by omega_arith) hj hi))
      fun c₄ ⟨kc, mc⟩ => k c₄ ⟨?_, ⟨M₀, ?_⟩, ?_, ?_⟩
    · have h := frame_writeBytes c₃.mem (emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt c₃.mem (s.gpr .r9) (s.gpr .r10).toNat)
      rw [bytesAt_length, add_ofNat_ofNat] at h
      obtain h' : Frame [⟨fb s + BitVec.ofNat 64 (oEM + (3 + (stackArg s 1).toNat)), (s.gpr .r10).toNat⟩]
          c₃.mem c₄.mem := by rw [mc, add_ofNat_ofNat]; exact h
      exact midc.frameW1 kc hp.ksc (by unfold oLr oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith) h'
    · rw [mc, hM, P₃.mem, mem₅, ← hl3, writeBytes_append _ _ _ _ (by simp [bytesAt_length]; omega_arith)]
      rfl
    · rw [kc.get .r5, P₃.get .r5, r5₅]
    · rw [kc.get .r12, P₃.get .r12, r12₅]

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ hn

/-- At the call: `EM` complete, the zero test in its word, and the call's
arguments. -/
structure AtCall (s t : State) : Prop extends EMid s t where
  emb : Spec.Rsa.bytesAt t.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s)
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  g3 : t.gpr .r3 = s.gpr .r3
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 4
  g6 : t.gpr .r6 = stackArg s 5
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = emA s
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = stackArg s 2
  a1 : stackArg t 1 = stackArg s 3

theorem encode_length {s : State} (hp : PreE s) :
    (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)).length = (s.gpr .r6).toNat := by
  have := hp.ml; have := hp.pl
  simp [Spec.RsaPkcs1Enc.encode, bytesAt_length]; omega_arith

theorem callArgs_ok {s y : State} (hp : PreE s) (hy : EmDone s y) :
    WP isa (.block callArgs) y (AtCall s) := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨M₀, hM₀⟩ := hy.em
  obtain emb₀ : Spec.Rsa.bytesAt y.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [hM₀, bytes_written (encode_length hp) (by omega_arith)]
  unfold callArgs
  obtain hz : InRegions y.wr (fb s + BitVec.ofNat 64 oZ) 8 := by rw [hy.wr]; exact in_fr s _ (by decide) (by decide)
  refine wp_std (a := fb s + BitVec.ofNat 64 oZ) (by rw [hy.g12]) hz fun y₁ m₁ => ?_
  refine wp_mov fun y₂ o₂ e₂ => wp_mov fun y₃ o₃ e₃ => wp_mov fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ =>
    wp_addi fun y₆ o₆ e₆ => wp_mov fun y₇ o₇ e₇ => ?_
  obtain fr₁ : Frame [⟨fb s + BitVec.ofNat 64 oZ, 8⟩] y.mem y₁.mem := by
    rw [m₁.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain mid₁ : EMid s y₁ := hy.toMid.frameW1 m₁.keep hp.ksc (by decide) (by decide) fr₁
  obtain O₇ : Only [.r3, .r4, .r7, .r8, .r9, .r10] y₁ y₇ :=
    (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))).mono
  obtain mid₇ : EMid s y₇ := mid₁.only O₇
  obtain r12₇ : y₇.gpr .r12 = fb s := by rw [O₇.get .r12, m₁.gpr, hy.g12]
  unfold callArgs at *
  refine wp_ld (a := stackArgAddr s 2) (by rw [r12₇, stackArgAddr_fb])
    (by rw [mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₈ o₈ e₈ => ?_
  rw [arg_mid hp mid₇.mem (by decide)] at e₈
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [o₈.get .r12, r12₇])
    (by rw [o₈.wr, mid₇.wr]; exact in_fr s _ (by decide) (by decide)) fun y₉ m₉ => ?_
  obtain fr₉ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] y₇.mem y₉.mem := by
    rw [m₉.mem, o₈.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))
  obtain K₉ : Frame [kR s, scR s] s.mem y₉.mem := mid₇.mem.trans (fr₉.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide)⟩)
  refine wp_ld (a := stackArgAddr s 3) (by rw [m₉.gpr, o₈.get .r12, r12₇, stackArgAddr_fb])
    (by rw [m₉.rd, o₈.rd, mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₁₀ o₁₀ e₁₀ => ?_
  rw [arg_mid hp K₉ (by decide)] at e₁₀
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₁₀.get .r12, m₉.gpr, o₈.get .r12, r12₇])
    (by rw [o₁₀.wr, m₉.wr, o₈.wr, mid₇.wr]; exact in_fr s _ (by decide) (by decide)) fun y₁₁ m₁₁ => ?_
  obtain fr₁₁ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] y₇.mem y₁₁.mem := by
    rw [m₁₁.mem, o₁₀.mem]
    exact fr₉.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  obtain K₁₁ : Frame [kR s, scR s] s.mem y₁₁.mem := mid₇.mem.trans (fr₁₁.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide)⟩)
  obtain r12₁₁ : y₁₁.gpr .r12 = fb s := by rw [m₁₁.gpr, o₁₀.get .r12, m₉.gpr, o₈.get .r12, r12₇]
  obtain rd₁₁ : y₁₁.rd = s.rd := by rw [m₁₁.rd, o₁₀.rd, m₉.rd, o₈.rd, mid₇.rd]
  refine wp_ld (a := stackArgAddr s 4) (by rw [r12₁₁, stackArgAddr_fb])
    (by rw [rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₂ o₁₂ e₁₂ => ?_
  refine wp_ld (a := stackArgAddr s 5) (by rw [o₁₂.get .r12, r12₁₁, stackArgAddr_fb])
    (by rw [o₁₂.rd, rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₃ o₁₃ e₁₃ => wp_nil ?_
  rw [arg_mid hp K₁₁ (by decide)] at e₁₂
  rw [o₁₂.mem, arg_mid hp K₁₁ (by decide)] at e₁₃
  obtain O₁₃ : Only [.r5, .r6] y₁₁ y₁₃ := o₁₂.trans o₁₃
  obtain g₁₁ : ∀ r, r ∉ [Reg.r0] → y₁₁.gpr r = y₇.gpr r := fun r hr => by
    rw [m₁₁.gpr, o₁₀.gpr r hr, m₉.gpr, o₈.gpr r hr]
  obtain hd96 : ∀ {d k : Nat}, 112 ≤ d → d + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨fb s + BitVec.ofNat 64 96, 16⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (.inr (by omega_arith)) (by unfold frameBytes at h₂; omega_arith) (by decide)
  have hEM : (⟨emA s, (s.gpr .r6).toNat⟩ : Region) = ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩ := rfl
  obtain emb₁ : Spec.Rsa.bytesAt y₁.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .r6).toNat⟩) fr₁
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith), emb₀]
  obtain hdS : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 oSave, 32⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
  obtain hdL : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 oLr, 64 / 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
  obtain hsv : Spill.Saved (fb s) s.gpr saved y₁₃.mem := by
    rw [O₁₃.mem]; exact mid₇.sv.frame_in saved_offs fr₁₁ hdS
  obtain hls : y₁₃.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [O₁₃.mem, fr₁₁.readW (Region.contains_self _ _) hdL (by decide)]; exact mid₇.ls
  obtain hK : Frame [kR s, scR s] s.mem y₁₃.mem := by rw [O₁₃.mem]; exact K₁₁
  obtain hm := Mid.of mid₇ (w := y₁₃) (fun r hr => by rw [O₁₃.gpr r (by revert r; decide), g₁₁ r (by revert r; decide)])
    (by rw [O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp]) (by rw [O₁₃.rd, rd₁₁, mid₇.rd])
    (by rw [O₁₃.wr, m₁₁.wr, o₁₀.wr, m₉.wr, o₈.wr]) hK hsv hls
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₁₃.mem, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .r6).toNat⟩) fr₁₁
      (hd96 (by decide) (by unfold oEM oEM1 frameBytes; omega_arith)) (by dsimp only; omega_arith), O₇.mem, emb₁]
  · have hdZ : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 oZ, 64 / 8⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
    rw [O₁₃.mem, fr₁₁.readW (Region.contains_self _ _) hdZ (by decide), O₇.mem, m₁.mem,
      Mem.readW_writeW_self64, hy.g5]
  · rw [O₁₃.get .r3, g₁₁ .r3 (by decide), o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, o₃.get .r3, e₂,
      mid₁.r28]
  · rw [O₁₃.get .r4, g₁₁ .r4 (by decide), o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, e₃, o₂.get .r29,
      mid₁.r29]
  · rw [o₁₃.get .r5, e₁₂]
  · rw [e₁₃]
  · rw [O₁₃.get .r7, g₁₁ .r7 (by decide), o₇.get .r7, o₆.get .r7, o₅.get .r7, e₄, o₃.get .r30, o₂.get .r30,
      mid₁.r30]
  · rw [O₁₃.get .r8, g₁₁ .r8 (by decide), o₇.get .r8, o₆.get .r8, e₅, o₄.get .r31, o₃.get .r31, o₂.get .r31,
      mid₁.r31]
  · rw [O₁₃.get .r9, g₁₁ .r9 (by decide), o₇.get .r9, e₆, o₅.get .r12, o₄.get .r12, o₃.get .r12, o₂.get .r12,
      m₁.gpr, hy.g12]
  · rw [O₁₃.get .r10, g₁₁ .r10 (by decide), e₇, o₆.get .r29, o₅.get .r29, o₄.get .r29, o₃.get .r29,
      o₂.get .r29, mid₁.r29]
  · show y₁₃.mem.readW (stackArgAddr y₁₃ 0) 64 = _
    rw [stackArgAddr_in, O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, mid₇.sp, O₁₃.mem, m₁₁.mem, o₁₀.mem,
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₉.mem,
      Mem.readW_writeW_self64]
    exact e₈
  · show y₁₃.mem.readW (stackArgAddr y₁₃ 1) 64 = _
    rw [stackArgAddr_in, O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, mid₇.sp, O₁₃.mem, m₁₁.mem,
      Mem.readW_writeW_self64, e₁₀]

/-- `EM`, of `k` bytes. -/
abbrev emR (s : State) : Region := ⟨emA s, (s.gpr .r6).toNat⟩

theorem em_sub {s : State} (hp : PreE s) : Region.Sub (emR s) (kR s) :=
  Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM) (n := (s.gpr .r6).toNat) (by have := hp.k2; unfold oEM oEM1 frameBytes; omega_arith)

theorem oR_eq {s : State} (hp : PreE s) : oR s = ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by
  rw [oR, hp.ok]

theorem pdOk_of {s t : State} (hp : PreE s) (ha : AtCall s t) : PdOk t := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  obtain hfb := fb_toNat hp.sp1
  obtain hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, ha.sp]
  obtain hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, ha.a1, hsa]
    exact {
      on := by rw [← oR_eq hp]; exact hp.op
      oe := by rw [← oR_eq hp]; exact hp.oe
      oi := (hko.sub_left (em_sub hp)).symm
      os := by rw [← oR_eq hp]; exact hp.osc
      oa := (hko.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide))).symm
      ns := hp.sp.symm
      es := hp.es
      is := hp.ksc.sub_left (em_sub hp)
      sa := (hp.ksc.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide))).symm
      wo := by have := hp.wo; rw [hp.ok] at this; exact this
      wn := hp.wp
      we := hp.we
      wi := by
        show (fb s + BitVec.ofNat 64 oEM).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM oEM1 frameBytes at *; omega_arith
      ws := hp.wsc }
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega_arith
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.wr]
    obtain hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (Covers.one (in_fr' s _ _ (by decide) (by unfold oEM oEM1 frameBytes; omega_arith)))
        (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, ha.a1, ha.wr]
    exact Covers.of_mem fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr, oR_eq hp]; simp)
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp)
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact hp.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact hp.e1
  case he2 => rw [ha.g8, ha.g4]; exact hp.e2
  case hs => rw [ha.g4, ha.a1]; exact hp.hs

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat)

/-- RSAEP of `EM`, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s))

/-- After the call: what the restores need, `out` and `k` kept, the zero
test in its word, and `out` written with RSAEP's result if `pre` holds the
modulus' values. -/
structure AfterCall (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  r28 : t.gpr .r28 = s.gpr .r3
  r29 : t.gpr .r29 = s.gpr .r6
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .r3) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreE s) (ha : AtCall s t) : WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1] at hf
  obtain hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  obtain hdF : ∀ {d k : Nat}, d + k ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region), scR s],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s h)
    · exact hp.ksc.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s h)
  refine ⟨⟨hsp'.trans ha.sp, hwr'.trans ha.wr, fun r hr => (hpres r (by revert r; decide)).trans (ha.hi r hr),
    ha.sv.frame hf fun p hp' => hdF (by have := saved_offs p hp'; unfold oSave frameBytes at *; omega_arith),
    by rw [hf.readW (Region.contains_self _ _) (hdF (by decide)) (by decide)]; exact ha.ls⟩,
    hrd'.trans ha.rd, (hpres .r28 (by decide)).trans ha.r28, (hpres .r29 (by decide)).trans ha.r29,
    by rw [hf.readW (Region.contains_self _ _) (hdF (by decide)) (by decide)]; exact ha.slot, fun hc => ?_⟩
  obtain hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat := by
    rw [ha.g5, ha.g6]; exact words_of_frame ha.mem hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, ha.emb,
    bytes_of_frame ha.mem hp.ke hp.es.symm (by have := hp.we; omega_arith)] at this
  exact this

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

end

end


/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: correctness

After the call (`AfterCall`), the result and `out` are masked with `PS`'s
zero test (`vg_rsa_pkcs1_recover_precomputed`'s `maskLoop`), `EM` is zeroed
(`encode`'s `fillLoop`) and the registers restored (`tail_ok`): if `pre`
holds the modulus' values, RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE.Rec (maskOf maskOf_bytes maskOf_byte)
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .r3) (s.gpr .r6).toNat ((s'.gpr .r3).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (msgB s) (psB s)))

theorem zbit_mask (l : List Byte) : zbit l - BitVec.ofNat 64 1 = maskOf (zbit l = 0) := by
  unfold maskOf zbit; split <;> decide

theorem zbit_eq_zero {l : List Byte} : zbit l = 0 ↔ l.all (· != 0) = true := by
  unfold zbit; split <;> simp_all

theorem encrypt_eq {s : State} (hp : PreE s) :
    Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (msgB s) (psB s) =
      if zbit (psB s) = 0 then pubOut s else none := by
  have := hp.ml; have := hp.pl
  unfold Spec.RsaPkcs1Enc.encrypt pubOut
  simp only [bytesAt_length, zbit_eq_zero]
  by_cases h : (psB s).all (· != 0) = true
  · rw [ite_eq_left ⟨by omega_arith, by omega_arith, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2.2), ite_eq_right h]

/-- Writes of the frame above the slots keep `Saves`. -/
theorem saves_frameW1 {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {e n : Nat}
    (he : oLr + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s w := by
  obtain hd : ∀ {d' k : Nat}, d' + k ≤ oLr + 8 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 e, n⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d', k⟩ r := fun hk r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by unfold oLr at hk; omega_arith) (by unfold frameBytes at hen; omega_arith)
  exact ⟨o.sp.trans h.sp, o.wr.trans h.wr,
    fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr),
    h.sv.frame_in saved_offs hm (hd (by decide)),
    by rw [hm.readW (Region.contains_self _ _) (hd (by decide)) (by decide)]; exact h.ls⟩

theorem tail_ok {s t : State} (hp : PreE s) (ha : AfterCall s t) :
    WP isa tail t fun w => Post s (freed frameBytes w) := by
  obtain hk1 := hp.k1; have hk2 := hp.k2
  unfold tail maskArgs
  refine WP.seq (wp_addSp fun t₁ o₁ e₁ => ?_)
  rw [ha.sv.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oZ) (by rw [e₁])
    (by rw [o₁.rd, o₁.wr, ha.sv.wr]; exact in_fr' s _ _ (by decide) (by decide)) fun t₂ o₂ e₂ =>
    wp_subi fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil ?_
  obtain O₆ : Only [.r12, .r9, .r9, .r3, .r11, .r8] t t₆ :=
    o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))
  obtain sv₆ : Saves s t₆ := ha.sv.keep O₆.keep (R := []) (by rw [O₆.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  obtain r9₆ : t₆.gpr .r9 = maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .r9, o₅.get .r9, o₄.get .r9, e₃, e₂, o₁.mem, ha.slot, zbit_mask]
  obtain r3₆ : t₆.gpr .r3 = t.gpr .r3 &&& maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .r3, o₅.get .r3, e₄, o₃.get .r3, o₂.get .r3, o₁.get .r3, ← r9₆, o₆.get .r9, o₅.get .r9,
      o₄.get .r9]
  obtain hout : ∀ i < (s.gpr .r6).toNat, InRegions (fr s :: s.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
      Offset.contains_base _ (by rw [hp.ok]; omega_arith) (by have := hp.wo; omega_arith)⟩
  obtain hdo : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine WP.seq (WP.mono (Rec.maskLoop_ok (p := s.gpr .r3) (n := (s.gpr .r6).toNat) (by omega_arith) (by omega_arith)
    (by rw [o₆.get .r11, e₅, o₄.get .r28, o₃.get .r28, o₂.get .r28, o₁.get .r28, ha.r28])
    (by rw [e₆, o₅.get .r29, o₄.get .r29, o₃.get .r29, o₂.get .r29, o₁.get .r29, ha.r29]; simp)
    (fun i hi => by rw [sv₆.wr]; exact hout i hi)) fun u ⟨ku, mu⟩ => ?_)
  obtain hB : Spec.Rsa.bytesAt t₆.mem (s.gpr .r3) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat := by rw [O₆.mem]
  rw [r9₆, maskOf_bytes, bytesAt_length, hB] at mu
  generalize hX : (if zbit (psB s) = 0 then Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat
    else List.replicate (s.gpr .r6).toNat 0) = X at mu
  obtain hXl : X.length = (s.gpr .r6).toNat := by rw [← hX]; split <;> simp [bytesAt_length]
  obtain svu : Saves s u := sv₆.keep ku (R := [⟨s.gpr .r3, (s.gpr .r6).toNat⟩])
    (by have h := frame_writeBytes t₆.mem (s.gpr .r3) X; rw [hXl] at h; rw [mu]; exact h)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdo)
  unfold wipeArgs
  refine WP.seq (wp_addSp fun w₁ p₁ f₁ => wp_addi fun w₂ p₂ f₂ => wp_mov fun w₃ p₃ f₃ =>
    wp_li (by decide) fun w₄ p₄ f₄ => wp_nil ?_)
  rw [svu.sp, BitVec.add_zero] at f₁
  obtain P₄ : Only [.r12, .r4, .r11, .r0] u w₄ := p₁.trans (p₂.trans (p₃.trans p₄))
  obtain svw : Saves s w₄ := svu.keep P₄.keep (R := []) (by rw [P₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  obtain hem : ∀ {i : Nat}, i < (s.gpr .r6).toNat → InRegions (fr s :: s.wr) (emA s + BitVec.ofNat 64 i) 1 :=
    fun hi => by
      rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith)
  refine WP.seq (WP.mono (fill_ok (p := emA s) (n := (s.gpr .r6).toNat) (b := 0) (by omega_arith) (by omega_arith)
    (by rw [p₄.get .r4, p₃.get .r4, f₂, f₁])
    (by rw [p₄.get .r11, f₃, p₂.get .r29, p₁.get .r29, ku.get .r29, o₆.get .r29, o₅.get .r29, o₄.get .r29,
      o₃.get .r29, o₂.get .r29, o₁.get .r29, ha.r29]; simp)
    (by rw [f₄]; rfl)
    (fun i hi => by rw [svw.wr]; exact hem hi)) fun w₅ ⟨k₅, m₅⟩ => ?_)
  obtain fr₅ : Frame [⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩] w₄.mem w₅.mem := by
    obtain h := frame_writeBytes w₄.mem (emA s) (List.replicate (s.gpr .r6).toNat (0 : Byte))
    rw [List.length_replicate] at h; rw [m₅]; exact h
  obtain sv₅ : Saves s w₅ := saves_frameW1 svw k₅ (by decide) (by unfold oEM oEM1 frameBytes; omega_arith) fr₅
  refine WP.mono (restore_ok sv₅) fun w' ⟨habi, h3, hm⟩ => ⟨habi, fun hc => ?_⟩
  obtain hbytes : Spec.Rsa.bytesAt w'.mem (s.gpr .r3) (s.gpr .r6).toNat = X := by
    rw [hm, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨s.gpr .r3, (s.gpr .r6).toNat⟩) fr₅
      (hdo.sub_left (em_sub hp)).symm (by dsimp only; omega_arith), P₄.mem, mu, bytes_written hXl (by omega_arith)]
  obtain hr : w'.gpr .r3 = t.gpr .r3 &&& maskOf (zbit (psB s) = 0) := by
    rw [h3, k₅.get .r3, P₄.get .r3, ku.get .r3, r3₆]
  rw [freed_mem, freed_gpr, hr, encrypt_eq hp]
  obtain hres := ha.res hc
  unfold maskOf
  by_cases hz : zbit (psB s) = 0
  · simp only [hz, ↓reduceIte, BitVec.and_allOnes] at hX ⊢
    rw [← hX] at hbytes
    revert hres
    cases pubOut s with
    | none => exact fun h => ⟨h.1, hbytes.trans h.2⟩
    | some y => exact fun h => ⟨h.1, hbytes.trans h.2⟩
  · simp only [hz, ↓reduceIte] at hX ⊢
    rw [← hX] at hbytes
    exact ⟨by simp, hbytes⟩

theorem preCall_ok {s w : State} (hp : PreE s) (hw : Setup s w) : WP isa preCall w (AtCall s) :=
  em_ok hp hw fun _ hy => callArgs_ok hp hy

/-- `written` reads the memory only in the output. -/
private theorem written_lost {m m' : Mem} {out : Addr} {k : Nat} {r r' : BitVec 32} {o : Option (List Byte)}
    (hr : r' = r) (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r' o := by
  subst hr
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

theorem code_ok {s : State} (hp : PreE s) : WP isa code s (Post s) := by
  unfold code
  refine WP.alloc (by decide) hp.sp1 ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok hp (by rw [allocated_sp]) (by rw [allocated_wr, frameR_eq])
    (by rw [allocated_rd])
    (by rw [allocated_mem]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
    (fun r _ => by rw [allocated_gpr]) (by rw [allocated_lr])) fun w hw => ?_)
  refine WP.seq (WP.mono (preCall_ok hp hw) fun t ht => ?_)
  -- The `free` loses the frame's bytes, which lie apart from the output.
  refine WP.seq (WP.mono (call_ok hp ht) fun t' ht' => WP.mono (tail_ok hp ht')
    fun w h mL _ fl => ⟨abiPreserved_lost h.1, fun ok => ?_⟩)
  have hb : Spec.Rsa.bytesAt mL (s.gpr .r3) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt (freed frameBytes w).mem (s.gpr .r3) (s.gpr .r6).toNat := by
    rw [freed_mem_eq]
    exact List.map_congr_left fun i hi => lost_byte fl (R := ⟨s.gpr .r3, (s.gpr .r6).toNat⟩)
      (by rw [← hp.ok]; exact hp.ko.symm) (List.mem_range.mp hi)
  exact written_lost rfl hb (h.2 ok)

/-- The correctness of `vg_rsa_pkcs1_encrypt_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preE_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

end

end

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: `Verified`

Correctness (`code_correct`), constant time (`code_ct`: the code around the
call by the taint analysis, from registers holding public values, which the
correctness proofs pin after the setup and the call; the call of
`vg_rsa_public_precomputed_checked` by its contract, `pdCallCT`) and a state
meeting the precondition. As `vg_rsa_pkcs1_verify_precomputed`'s
(`Proof/RsaPkcs1Sig/PPC64LE/VerifyVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, the bytes of `n` and `e`, and the precomputed values. -/
structure PubE (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  args : ∀ i < 6, stackArg s i = stackArg a i
  be : Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r7) (a.gpr .r8).toNat
  w : Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat

theorem leak_eq2W {a b a' b' : List Byte} {w w' : List (BitVec 64)} (ha : a.length = a'.length)
    (hb : b.length = b'.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (a' ++ b').map (·.toNat) ++ w'.map (·.toNat)) :
    b = b' ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = a' ++ b' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  obtain ⟨-, e⟩ := List.append_inj hi ha
  exact ⟨e, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

theorem pubE_of {S : Nat} {s₁ s₂ : State}
    (h : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi S).pub s₁ s₂) : PubE s₁ s₂ := by
  sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5⟩ := h
  obtain ⟨he, hw⟩ := leak_eq2W (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8]) hl
  refine ⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm]

/-- An entry state with the anchor's public data. -/
def E (a s : State) : Prop := PreE s ∧ PubE a s

/-! ## Constant time -/

theorem fb_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) : fb s₁ = fb s₂ := by
  simp only [fb, h₁.2.sp, h₂.2.sp]

theorem gpr_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {r : Reg} (hr : r ∈ argRegs := by decide) :
    s₁.gpr r = s₂.gpr r :=
  (h₁.2.g r hr).trans (h₂.2.g r hr).symm

theorem arg_eq {a s₁ s₂ : State} (h₁ : E a s₁) (h₂ : E a s₂) {i : Nat} (hi : i < 6 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.2.args i hi).trans (h₂.2.args i hi).symm

theorem call_ct : RelCT isa (Two fun a t => ∃ s, E a s ∧ AtCall s t) pubCall fun _ _ => True := by
  refine pdCallCT fun t₁ t₂ ⟨a, ⟨s₁, h₁, c₁⟩, ⟨s₂, h₂, c₂⟩⟩ => ⟨pdOk_of h₁.1 c₁,
    pdOk_of h₂.1 c₂, ⟨?_, fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [c₁.sp, c₂.sp, fb_eq h₁ h₂]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [c₁.g3, c₂.g3, gpr_eq h₁ h₂]
    · rw [c₁.g4, c₂.g4, gpr_eq h₁ h₂]
    · rw [c₁.g5, c₂.g5, arg_eq h₁ h₂]
    · rw [c₁.g6, c₂.g6, arg_eq h₁ h₂]
    · rw [c₁.g7, c₂.g7, gpr_eq h₁ h₂]
    · rw [c₁.g8, c₂.g8, gpr_eq h₁ h₂]
    · rw [c₁.g9, c₂.g9, emA, fb_eq h₁ h₂]
    · rw [c₁.g10, c₂.g10, gpr_eq h₁ h₂]
  · rw [c₁.a0, c₂.a0, arg_eq h₁ h₂]
  · rw [c₁.a1, c₂.a1, arg_eq h₁ h₂]
  · rw [c₁.g5, c₂.g5, c₁.g6, c₂.g6, words_of_frame c₁.mem h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame c₂.mem h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · rw [c₁.g7, c₂.g7, c₁.g8, c₂.g8, bytes_of_frame c₁.mem h₁.1.ke h₁.1.es.symm (by have := h₁.1.we; omega_using []),
      bytes_of_frame c₂.mem h₂.1.ke h₂.1.es.symm (by have := h₂.1.we; omega_using []), h₁.2.be, h₂.2.be]

theorem code_ct : RelCT isa (Two E) code fun _ _ => True := by
  unfold code
  refine two_alloc (R := fun _ _ => True)
    (fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, E a s ∧ Setup s w)
    (setup_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂, allocated_sp, allocated_sp, h₁.2.sp, h₂.2.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    exact WP.mono (setup_ok h.1 (by rw [allocated_sp]) (by rw [allocated_wr, frameR_eq]) (by rw [allocated_rd])
      (by rw [allocated_mem]; exact Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (fb_contains s))
      (fun r _ => by rw [allocated_gpr]) (by rw [allocated_lr])) fun w hw => ⟨s, h, hw⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AtCall s t)
    (preCall_taint fun _ _ _ ⟨s₁, h₁, w₁⟩ ⟨s₂, h₂, w₂⟩ => ⟨by rw [w₁.sp, w₂.sp, fb_eq h₁ h₂], fun r hr => ?_⟩)
    fun a w ⟨s, h, hw⟩ => WP.mono (preCall_ok h.1 hw) fun t ht => ⟨s, h, ht⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [w₁.g4, w₂.g4, arg_eq h₁ h₂]
    · rw [w₁.g9, w₂.g9, gpr_eq h₁ h₂]
    · rw [w₁.g10, w₂.g10, gpr_eq h₁ h₂]
    · rw [w₁.g11, w₂.g11, fb_eq h₁ h₂]
    · rw [w₁.g12, w₂.g12, arg_eq h₁ h₂]
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E a s ∧ AfterCall s t) call_ct
    fun a t ⟨s, h, ht⟩ => WP.mono (call_ok h.1 ht) fun w hw => ⟨s, h, hw⟩) ?_
  refine tail_taint fun _ _ _ ⟨s₁, h₁, a₁⟩ ⟨s₂, h₂, a₂⟩ => ⟨?_, fun r hr => ?_⟩
  · rw [a₁.sv.sp, a₂.sv.sp, fb_eq h₁ h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a₁.r28, a₂.r28, gpr_eq h₁ h₂]
    · rw [a₁.r29, a₂.r29, gpr_eq h₁ h₂]

theorem code_constantTime :
    ConstantTime isa (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre
      (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pub code :=
  RelCT.constantTime (code_ct.mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preE_of h₁, ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩⟩, preE_of h₂, pubE_of hp⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- `out` and a modulus of 64 bytes at `0x6000` and `0x1000`, `e` and the
message of a byte each, `PS` of 60 bytes, 112 words of working space and 16
precomputed words; the stack arguments at `sp + 96`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x6000 | .r4 => 64 | .r5 => 0x1000 | .r6 => 64 | .r7 => 0x2000 | .r8 => 1 | .r9 => 0x3000
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000061 then 0x40
    else bif Nat.beq a.toNat 0x10000000068 then 60 else bif Nat.beq a.toNat 0x10000000072 then 1
    else bif Nat.beq a.toNat 0x10000000078 then 0x70 else bif Nat.beq a.toNat 0x10000000081 then 0x50
    else bif Nat.beq a.toNat 0x10000000088 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 60⟩, ⟨0x5000, 128⟩, ⟨0x10000000060, 48⟩]
  wr := [⟨0x6000, 64⟩, ⟨0x10000, 896⟩]

theorem sat_args : stackArg satState 0 = 0x4000 ∧ stackArg satState 1 = 60 ∧ stackArg satState 2 = 0x10000 ∧
    stackArg satState 3 = 112 ∧ stackArg satState 4 = 0x5000 ∧ stackArg satState 5 = 16 := by
  decide

theorem sat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : frameBytes = 2223 + 1 := rfl
  rw [e]
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000000060 := by decide
  simp only [a0, a1, a2, a3, a4, a5, ha]
  exact ⟨by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by unfold Spec.Rsa.lenValid; decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified PPC64LE.target code (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
