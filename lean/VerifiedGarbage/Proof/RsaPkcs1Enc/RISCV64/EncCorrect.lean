module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Frame
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.VerifyCall
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.RecoverCorrect

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on RISC-V: correctness

After the call (`AfterCall`), the result and `out` are masked to zero if
`PS` has a zero byte, and `EM` is zeroed (`tail_ok`): if `pre` holds the
modulus' values, RFC 8017 §7.2.1's encryption (`encrypt_eq`). As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/EncCorrect.lean`).
-/

@[expose] public section

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on RISC-V: up to the call

`setup_ok`: the saves, `out`, `k`, `e` and `e_len` kept in `s1`–`s4`, and
`EM`'s first two bytes (`Setup`). `em_ok`: `PS`, the separator and `M`
complete `EM = encode M PS` (`EmDone`), with `PS`'s zero test in `t5`.
`callArgs_ok` and `call_ok`: the call writes RSAEP of `EM` to `out` if `pre`
holds the modulus' values (`AfterCall`). As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/EncCall.lean`).
-/


/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on RISC-V: the precondition

Untrusted: everything here is checked by Lean. `PreE s`: the shared
contract's precondition (`encryptPrecomputedContract`, with the stack of the
frame of `vg_rsa_pkcs1_verify_precomputed`, whose frame it shares), by name
(`preE_of`). As on PPC64LE (`Proof/RsaPkcs1Enc/PPC64LE/EncPre.lean`).
-/


namespace VG.Proof.RsaPkcs1Enc.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- The buffers: `out`, `n`, `e`, the message, `PS`, the working space, the
precomputed values and the arguments on the stack (the stack the function
uses is `kR`). -/
abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev mR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev psR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev a6R (s : State) : Region := ⟨stackArgAddr s 0, 48⟩

/-- What the code needs of `encryptPrecomputedContract.pre`, by name. -/
structure PreE (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 48 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, mR s, psR s, pR s, a6R s]
  hwr : s.wr = [oR s, scR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  om : (oR s).Disjoint (mR s)
  ops : (oR s).Disjoint (psR s)
  osc : (oR s).Disjoint (scR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (a6R s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ms : (mR s).Disjoint (scR s)
  pss : (psR s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sa : (scR s).Disjoint (a6R s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  km : (kR s).Disjoint (mR s)
  kps : (kR s).Disjoint (psR s)
  ksc : (kR s).Disjoint (scR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (a6R s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wm : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wps : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wsc : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a3).toNat
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  ml : (s.gpr .a7).toNat + 11 ≤ (s.gpr .a3).toNat
  pl : (stackArg s 1).toNat = (s.gpr .a3).toNat - (s.gpr .a7).toNat - 3
  hs : Spec.Rsa.publicScratchWords (s.gpr .a3).toNat ≤ (stackArg s 3).toNat
  hp : (stackArg s 5).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat
  al2 : (stackArg s 2).toNat % 8 = 0
  al4 : (stackArg s 4).toNat % 8 = 0

theorem preE_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s) : PreE s := by
  have e : frameBytes = 2127 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨spal, sp1, sp2, hrd, hwr, on, oe, om, ops, osc, op, oa, ns, es, ms, pss, sp, sa, ko, kn, ke, km, kps, ksc,
    kp, ka, wo, wn, we, wm, wps, wsc, wp, ⟨k1, k2⟩, ok, e1, e2, ml, pl, hs, hp, al2, al4⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, on, oe, om, ops, osc, op, oa, ns, es, ms, pss, sp, sa, ko, kn, ke, km, kps, ksc,
    kp, ka, wo, wn, we, wm, wps, wsc, wp, k1, k2, ok, e1, e2, ml, pl, hs, hp, al2, al4⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Enc

/-!
# RSAES-PKCS1-v1_5 encryption on RISC-V: the copy of `PS`

Untrusted: everything here is checked by Lean. `psLoop_ok`: `PS` is copied
to `EM` and whether one of its bytes is zero is ORed into `t5`. As on
PPC64LE (`Proof/RsaPkcs1Enc/PPC64LE/EncLoops.lean`).
-/


namespace VG.Proof.RsaPkcs1Enc.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)
open VG.Proof.Bignum.RISCV64 (wp_countdown)

/-- 1 if one of the bytes is zero, 0 if not. -/
def zbit (l : List Byte) : BitVec 64 := if l.all (· != 0) then 0 else 1

theorem zbit_nil : zbit [] = 0 := rfl

theorem zbit_snoc (l : List Byte) (b : Byte) :
    zbit (l ++ [b]) = zbit l ||| (if b = 0 then 1 else 0) := by
  unfold zbit
  rw [List.all_append]
  cases hl : l.all (· != 0) <;> by_cases hb : b = 0 <;> simp [hb] <;> first | decide | (split <;> decide)

theorem byte_toNat_lt (b : Byte) : (b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_setWidth]; have := b.isLt; omega

theorem setWidth_eq_zero {b : Byte} : (b.setWidth 64 = 0) ↔ b = 0 := by
  constructor
  · intro h; have := congrArg (BitVec.setWidth 8) h; simpa using this
  · intro h; rw [h]; rfl

/-- `psLoop` copies the `n` bytes at `t2 = q` to `t4 = p`, counted down in
`t3`, and ORs their zero test into `t5`. -/
theorem psLoop_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .t2 = q) (h11 : s.gpr .t4 = p) (h12 : s.gpr .t3 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa psLoop s fun t => Kept [.t1, .t2, .t5, .t4, .t3] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .t5 = s.gpr .t5 ||| zbit (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .t4 = p + BitVec.ofNat 64 n := by
  refine WP.mono (wp_countdown (cnt := .t3) hn' hn
    (fun i t => Kept [.t1, .t2, .t5, .t4, .t3] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .t2 = q + BitVec.ofNat 64 i ∧ t.gpr .t4 = p + BitVec.ofNat 64 i ∧
      t.gpr .t5 = s.gpr .t5 ||| zbit ((Spec.Rsa.bytesAt s.mem q n).take i)) ?_
    ⟨Kept.refl _ _, by simp [writeBytes_nil], by simp [h4], by simp [h11], by simp [zbit_nil]⟩ h12)
    fun t h => ⟨h.1, ?_, ?_, h.2.2.2.1⟩
  · intro i hi t ⟨hK, hm, h4', h11', h5'⟩ _
    simp only [psBody, List.cons_append, List.nil_append]
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .t2 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega)]
    refine wp_lbu rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .t4 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .t4, h11', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_sb rfl hA fun s₂ m₂ => wp_subi (imm := 1) fun s₃ o₃ e₃ => wp_srl fun s₄ o₄ e₄ =>
      wp_or fun s₅ o₅ e₅ => wp_addi (imm := 1) fun s₆ o₆ e₆ => wp_addi (imm := 1) fun s₇ o₇ e₇ =>
      wp_subi (imm := 1) fun s₈ o₈ e₈ => wp_nil ?_
    have hK' : Kept [.t1, .t2, .t5, .t4, .t3] t s₈ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
        (o₇.keep.trans o₈.keep))))))).mono
    have hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega
    have hb : s₂.gpr .t1 = (s.mem (q + BitVec.ofNat 64 i)).setWidth 64 := by
      rw [m₂.gpr, e₁, h4', BitVec.add_zero, hv]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h4', o₁.get .t4, h11']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, hm, bytesAt_take_succ _ _ hi, writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₈.get .t2, o₇.get .t2, e₆, o₅.get .t2, o₄.get .t2, o₃.get .t2, m₂.gpr, o₁.get .t2, h4', ofNat_succ']
    · rw [o₈.get .t4, e₇, o₆.get .t4, o₅.get .t4, o₄.get .t4, o₃.get .t4, m₂.gpr, o₁.get .t4, h11',
        ofNat_succ']
    · rw [o₈.get .t5, o₇.get .t5, o₆.get .t5, e₅, o₄.get .t5, e₄, o₃.get .t5, e₃, hb, m₂.gpr, o₁.get .t5, h5',
        borrow1 (byte_toNat_lt _), bytesAt_take_succ _ _ hi, zbit_snoc, BitVec.or_assoc]
      congr 2
      by_cases h : s.mem (q + BitVec.ofNat 64 i) = 0
      · rw [ite_eq_left h, ite_eq_left (setWidth_eq_zero.mpr h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (setWidth_eq_zero.mp h'))]
    · rw [e₈, o₇.get .t3, o₆.get .t3, o₅.get .t3, o₄.get .t3, o₃.get .t3, m₂.gpr, o₁.get .t3]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.2.2.2

end VG.Proof.RsaPkcs1Enc.RISCV64.Enc


namespace VG.Proof.RsaPkcs1Enc.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- In the frame: `out`, `k`, `e` and `e_len` kept. -/
abbrev EMid (s t : State) : Prop := Mid (scR s) s (s.gpr .a0) (s.gpr .a3) (s.gpr .a4) (s.gpr .a5) t

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

/-- `t6` after `argBase`, from the frame's stack pointer. -/
theorem t6_eq {s : State} {x : Addr} (h : x = fb s) :
    x + BitVec.ofNat 64 2032 + BitVec.ofNat 64 ((frameBytes - 2032 : Nat) : Int).toNat = stackArgAddr s 0 := by
  rw [h, stackArgAddr_fb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl

/-- After the setup. -/
structure Setup (s w : State) : Prop extends
    Mid (scR s) s (s.gpr .a0) (s.gpr .a3) (s.gpr .a4) (s.gpr .a5) w where
  em : Em s [0x00, 0x02] w
  g2 : w.gpr .t2 = stackArg s 0
  g3 : w.gpr .t3 = stackArg s 1
  g4 : w.gpr .t4 = fb s + BitVec.ofNat 64 (oEM + 2)
  g5 : w.gpr .t5 = 0
  g6 : w.gpr .a6 = s.gpr .a6
  g7 : w.gpr .a7 = s.gpr .a7

theorem setup_ok {s u : State} (hp : PreE s) (hsp : u.sp = fb s) (hwr : u.wr = kR s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, u.gpr r = s.gpr r) :
    WP isa (.block setup) u (Setup s) := by
  have hfa := fb_al hp.spal hp.sp1
  unfold setup argBase
  simp only [List.append_assoc]
  refine save_ok hsp hwr (by omega) hm (fun r _ => hg r) fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => by rw [kv.gpr r hr, hg r]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_li (imm := 0) (by decide) fun v₅ o₅ e₅ => ?_
  have O₅ : Only [.s1, .s2, .s3, .s4, .t1] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have t0₅ : v₅.gpr .t0 = fb s := by rw [O₅.get .t0, v0]
  have wr₅ : v₅.wr = kR s :: s.wr := by rw [O₅.wr, kv.wr, hwr]
  refine wp_sb (a := emA s) (by rw [t0₅]) (by rw [wr₅]; exact in_fr s _ (by decide))
    fun v₆ m₆ => wp_li (imm := 2) (by decide) fun v₇ o₇ e₇ => ?_
  refine wp_sb (a := emA s + BitVec.ofNat 64 1) (by rw [o₇.get .t0, m₆.gpr, t0₅, add_ofNat_ofNat])
    (by rw [o₇.wr, m₆.wr, wr₅, add_ofNat_ofNat]; exact in_fr s _ (by decide)) fun v₈ m₈ => ?_
  have t0₈ : v₈.gpr .t0 = fb s := by rw [m₈.gpr, o₇.get .t0, m₆.gpr, t0₅]
  have rd₈ : v₈.rd = s.rd := by rw [m₈.rd, o₇.rd, m₆.rd, O₅.rd, kv.rd, hrd]
  have sp₈ : v₈.sp = fb s := by rw [m₈.sp, o₇.sp, m₆.sp, O₅.sp, kv.sp, hsp]
  have mem₈ : v₈.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by
    have b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
    have b2 : (BitVec.ofNat 64 2).setWidth 8 = (0x02 : Byte) := by decide
    rw [m₈.mem, o₇.mem, m₆.mem, O₅.mem, e₇, e₅, b0, b2,
      show ([0x00, 0x02] : List Byte) = [] ++ [0x00] ++ [0x02] from rfl, writeBytes_snoc _ _ _ _ (by decide),
      writeBytes_snoc _ _ _ _ (by decide), writeBytes_nil]
    simp only [List.length_nil, List.nil_append, List.length_singleton, BitVec.add_zero]
  have fr₈ : Frame [kR s] s.mem v₈.mem := by
    rw [mem₈]
    have hw := frame_writeBytes v.mem (emA s) [0x00, 0x02]
    exact fv.trans (hw.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, frame_sub s (d := oEM) (n := 2) (by decide)⟩)
  have hdS : ∀ {d k : Nat}, d + k ≤ oRa + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨emA s, 2⟩ := fun hk =>
    Offset.disjoint _ (.inl (by unfold oRa oEM oEM1 at *; omega_arith)) (by unfold oRa at hk; omega_arith)
      (by decide)
  refine wp_addSp fun v₉ o₉ e₉ => wp_addi fun v₁₀ o₁₀ e₁₀ => ?_
  have t6₁₀ : v₁₀.gpr .t6 = stackArgAddr s 0 := by rw [e₁₀, e₉, sp₈]; exact t6_eq rfl
  have P₁₀ : Only [.t6, .t6] v₈ v₁₀ := o₉.trans o₁₀
  refine wp_ld (a := stackArgAddr s 0) (by rw [t6₁₀, BitVec.add_zero]) (arg_al hp.spal 0)
    (by rw [P₁₀.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₁ o₁₁ e₁₁ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₁₁.get .t6, t6₁₀, stackArgAddr_eq s 1]) (arg_al hp.spal 1)
    (by rw [o₁₁.rd, P₁₀.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₂ o₁₂ e₁₂ => ?_
  refine wp_addi (imm := oEM + 2) fun v₁₃ o₁₃ e₁₃ => wp_li (imm := 0) (by decide) fun v₁₄ o₁₄ e₁₄ => wp_nil ?_
  have O₁₄ : Only [.t6, .t6, .t2, .t3, .t4, .t5] v₈ v₁₄ := (P₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans o₁₄)))).mono
  have g₈ : ∀ r, r ∉ [Reg.t1] → v₈.gpr r = v₅.gpr r := fun r hr => by rw [m₈.gpr, o₇.gpr r hr, m₆.gpr]
  have mem₁₄ : v₁₄.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by rw [O₁₄.mem, mem₈]
  refine {
    sp := by rw [O₁₄.sp, sp₈]
    rd := by rw [O₁₄.rd, rd₈]
    wr := by rw [O₁₄.wr, m₈.wr, o₇.wr, m₆.wr, wr₅]
    s1 := by
      rw [O₁₄.get .s1, g₈ .s1 (by decide), o₅.get .s1, o₄.get .s1, o₃.get .s1, o₂.get .s1, e₁,
        gv .a0 (by decide)]
    s2 := by
      rw [O₁₄.get .s2, g₈ .s2 (by decide), o₅.get .s2, o₄.get .s2, o₃.get .s2, e₂, o₁.get .a3,
        gv .a3 (by decide)]
    s3 := by
      rw [O₁₄.get .s3, g₈ .s3 (by decide), o₅.get .s3, o₄.get .s3, e₃, o₂.get .a4, o₁.get .a4,
        gv .a4 (by decide)]
    s4 := by
      rw [O₁₄.get .s4, g₈ .s4 (by decide), o₅.get .s4, e₄, o₃.get .a5, o₂.get .a5, o₁.get .a5,
        gv .a5 (by decide)]
    hi := fun r hr => by
      have h₁ : r ∉ [Reg.t6, .t6, .t2, .t3, .t4, .t5] := by revert r; decide
      have h₂ : r ∉ [Reg.t1] := by revert r; decide
      have h₃ : r ∉ [Reg.s1, .s2, .s3, .s4, .t1] := by revert r; decide
      have h₄ : r ∉ [Reg.t0] := by revert r; decide
      rw [O₁₄.gpr r h₁, g₈ r h₂, O₅.gpr r h₃, gv r h₄]
    mem := by
      rw [O₁₄.mem]
      exact fr₈.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₄]
      exact sv.frame (frame_writeBytes v.mem (emA s) [0x00, 0x02]) fun p hp r hr => by
        rw [List.mem_singleton.mp hr]; exact hdS (by have := saved_offs p hp; unfold oSave oRa at *; omega_arith)
    em := ⟨v.mem, mem₁₄⟩
    g2 := by
      rw [o₁₄.get .t2, o₁₃.get .t2, o₁₂.get .t2, e₁₁, P₁₀.mem, arg_frame hp fr₈ (by decide)]
    g3 := by rw [o₁₄.get .t3, o₁₃.get .t3, e₁₂, o₁₁.mem, P₁₀.mem, arg_frame hp fr₈ (by decide)]
    g4 := by rw [o₁₄.get .t4, e₁₃, o₁₂.get .t0, o₁₁.get .t0, P₁₀.get .t0, t0₈]
    g5 := by rw [e₁₄]; rfl
    g6 := by rw [O₁₄.get .a6, g₈ .a6 (by decide), O₅.get .a6, gv .a6 (by decide)]
    g7 := by rw [O₁₄.get .a7, g₈ .a7 (by decide), O₅.get .a7, gv .a7 (by decide)] }

/-- `M` and `PS`, from the entry state. -/
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat
abbrev psB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat

/-- `EM` complete, `PS`'s zero test in `t5`. -/
structure EmDone (s y : State) : Prop extends EMid s y where
  em : Em s (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)) y
  g5 : y.gpr .t5 = zbit (psB s)

theorem em_ok {s w : State} (hp : PreE s) (hs : Setup s w) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ y, EmDone s y → WP isa rest y Q) :
    WP isa (.seq psLoop (.seq (.block sep) (.seq msgCopy rest))) w Q := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hml := hp.ml; have hpl := hp.pl
  obtain ⟨M₀, hM₀⟩ := hs.em
  have hn : 0 < (stackArg s 1).toNat := by omega_arith
  have hdP : (psR s).Disjoint ⟨emA s + BitVec.ofNat 64 2, (stackArg s 1).toNat⟩ := by
    rw [add_ofNat_ofNat]
    exact (hp.kps.sub_left (frame_sub s (d := oEM + 2) (n := (stackArg s 1).toNat)
      (by unfold oEM oEM1 frameBytes; omega_arith))).symm
  refine WP.seq (WP.mono (psLoop_ok (p := emA s + BitVec.ofNat 64 2) (q := stackArg s 0)
    (n := (stackArg s 1).toNat) hn (by omega_arith) hs.g2 (by rw [hs.g4, add_ofNat_ofNat]) (by rw [hs.g3]; simp)
    (fun j hj => ⟨psR s, List.mem_append_left _ (by rw [hs.rd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by have := hp.wps; omega_arith)⟩)
    (fun i hi => by
      rw [hs.wr, add_ofNat_ofNat, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM oEM1 frameBytes; omega_arith))
    (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdP (by omega_arith) (by omega_arith) hj hi))
    fun y₁ ⟨k₁, m₁, r5₁, r11₁⟩ => ?_)
  have hPS : Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat = psB s :=
    bytes_of_frame hs.mem hp.kps hp.pss.symm (by have := hp.wps; omega_arith)
  have hl2 : ([(0x00 : Byte), 0x02] ++ psB s).length = 2 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  have mem₁ : y₁.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s) := by
    rw [m₁, hPS, hM₀, ← writeBytes_append _ _ _ _ (by rw [← List.length_append, hl2]; omega_arith)]
    rfl
  have fr₁ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2), (stackArg s 1).toNat⟩] w.mem y₁.mem := by
    have h := frame_writeBytes w.mem (emA s + BitVec.ofNat 64 2)
      (Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat)
    rw [bytesAt_length, add_ofNat_ofNat] at h
    rw [m₁, add_ofNat_ofNat]; exact h
  have mid₁ : EMid s y₁ := hs.toMid.frameW1 k₁ hp.ksc (by decide) (by unfold oEM oEM1 frameBytes; omega_arith) fr₁
  have b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
  have inEM : ∀ {d n : Nat}, d + n ≤ 1024 → InRegions (kR s :: s.wr) (emA s + BitVec.ofNat 64 d) n :=
    fun h => by rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1 frameBytes; omega_arith)
  refine WP.seq (wp_li (imm := 0) (by decide) fun y₂ o₂ e₂ =>
    wp_sb (a := emA s + BitVec.ofNat 64 (2 + (stackArg s 1).toNat))
      (by rw [o₂.get .t4, r11₁, BitVec.add_zero, add_ofNat_ofNat])
      (by rw [o₂.wr, mid₁.wr]; exact inEM (by omega_arith)) fun y₃ m₃ =>
    wp_addi (imm := 1) fun y₄ o₄ e₄ => wp_nil ?_)
  have hl3 : ([(0x00 : Byte), 0x02] ++ psB s ++ [0x00]).length = 3 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  have mem₃ : y₃.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by
    rw [writeBytes_snoc _ _ _ _ (by omega_arith), hl2, m₃.mem, o₂.mem, mem₁, e₂, b0]
  have fr₃ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2 + (stackArg s 1).toNat), 1⟩] y₁.mem y₃.mem := by
    rw [m₃.mem, o₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (by
      rw [add_ofNat_ofNat, show oEM + (2 + (stackArg s 1).toNat) = oEM + 2 + (stackArg s 1).toNat by omega_arith]
      exact Region.contains_self _ _)
  have mid₃ : EMid s y₃ := mid₁.frameW1 (o₂.keep.trans m₃.keep) hp.ksc (by unfold oRa oEM oEM1; omega_arith)
    (by unfold oEM oEM1 frameBytes; omega_arith) fr₃
  have mid₄ : EMid s y₄ := mid₃.only o₄
  have r11₄ : y₄.gpr .t4 = emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat) := by
    rw [e₄, m₃.gpr, o₂.get .t4, r11₁, ofNat_succ', add_ofNat_ofNat,
      show 2 + ((stackArg s 1).toNat + 1) = 3 + (stackArg s 1).toNat by omega_arith]
  have r5₄ : y₄.gpr .t5 = zbit (psB s) := by
    rw [o₄.get .t5, m₃.gpr, o₂.get .t5, r5₁, hs.g5, hPS]; simp
  have r10₄ : y₄.gpr .a7 = s.gpr .a7 := by
    rw [o₄.get .a7, m₃.gpr, o₂.get .a7, k₁.get .a7, hs.g7]
  have r9₄ : y₄.gpr .a6 = s.gpr .a6 := by
    rw [o₄.get .a6, m₃.gpr, o₂.get .a6, k₁.get .a6, hs.g6]
  have mem₄ : y₄.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by rw [o₄.mem, mem₃]
  refine WP.seq ?_
  unfold msgCopy
  by_cases hm0 : (s.gpr .a7).toNat = 0
  · refine WP.ite false (by rw [eval_nonzero, ne_zero_iff, r10₄, hm0]; rfl) (by simp) fun _ => wp_nil ?_
    refine k y₄ ⟨mid₄, ⟨M₀, ?_⟩, r5₄⟩
    rw [mem₄]
    unfold Spec.RsaPkcs1Enc.encode msgB
    rw [hm0]
    simp [Spec.Rsa.bytesAt]
  · refine WP.ite true (by rw [eval_nonzero, ne_zero_iff, r10₄]; simp [hm0]) (fun _ => ?_) (by simp)
    refine WP.seq (wp_mov fun c₁ p₁ f₁ => wp_mov fun c₂ p₂ f₂ => wp_mov fun c₃ p₃ f₃ => wp_nil ?_)
    have P₃ : Only [.a4, .a1, .a5] y₄ c₃ := p₁.trans (p₂.trans p₃)
    have midc : EMid s c₃ := mid₄.only P₃
    have hdM : (mR s).Disjoint ⟨emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat), (s.gpr .a7).toNat⟩ := by
      rw [add_ofNat_ofNat]
      exact (hp.km.sub_left (frame_sub s (d := oEM + (3 + (stackArg s 1).toNat)) (n := (s.gpr .a7).toNat)
        (by unfold oEM oEM1 frameBytes; omega_arith))).symm
    have hM : Spec.Rsa.bytesAt c₃.mem (s.gpr .a6) (s.gpr .a7).toNat = msgB s :=
      bytes_of_frame midc.mem hp.km hp.ms.symm (by have := hp.wm; omega_arith)
    refine WP.mono (copy_ok (p := emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat)) (q := s.gpr .a6)
      (n := (s.gpr .a7).toNat) (by omega_arith) (by omega_arith) (by rw [p₃.get .a1, f₂, p₁.get .t4, r11₄])
      (by rw [p₃.get .a4, p₂.get .a4, f₁, r9₄]) (by rw [f₃, p₂.get .a7, p₁.get .a7, r10₄]; simp)
      (fun j hj => ⟨mR s, List.mem_append_left _ (by rw [midc.rd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by have := hp.wm; omega_arith)⟩)
      (fun i hi => by rw [midc.wr, add_ofNat_ofNat]; exact inEM (by omega_arith))
      (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdM (by omega_arith) (by omega_arith) hj hi))
      fun c₄ ⟨kc, mc⟩ => k c₄ ⟨?_, ⟨M₀, ?_⟩, ?_⟩
    · have h := frame_writeBytes c₃.mem (emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt c₃.mem (s.gpr .a6) (s.gpr .a7).toNat)
      rw [bytesAt_length, add_ofNat_ofNat] at h
      have h' : Frame [⟨fb s + BitVec.ofNat 64 (oEM + (3 + (stackArg s 1).toNat)), (s.gpr .a7).toNat⟩]
          c₃.mem c₄.mem := by rw [mc, add_ofNat_ofNat]; exact h
      exact midc.frameW1 kc hp.ksc (by unfold oRa oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith) h'
    · rw [mc, hM, P₃.mem, mem₄, ← hl3, writeBytes_append _ _ _ _ (by simp [bytesAt_length]; omega_arith)]
      rfl
    · rw [kc.get .t5, P₃.get .t5, r5₄]

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ hn

/-- At the call: `EM` complete, the zero test in its word, and the call's
arguments. -/
structure AtCall (s t : State) : Prop extends EMid s t where
  emb : Spec.Rsa.bytesAt t.mem (emA s) (s.gpr .a3).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s)
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  g0 : t.gpr .a0 = s.gpr .a0
  g1 : t.gpr .a1 = s.gpr .a3
  g2 : t.gpr .a2 = stackArg s 4
  g3 : t.gpr .a3 = stackArg s 5
  g4 : t.gpr .a4 = s.gpr .a4
  g5 : t.gpr .a5 = s.gpr .a5
  g6 : t.gpr .a6 = emA s
  g7 : t.gpr .a7 = s.gpr .a3
  sa0 : stackArg t 0 = stackArg s 2
  sa1 : stackArg t 1 = stackArg s 3

theorem encode_length {s : State} (hp : PreE s) :
    (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)).length = (s.gpr .a3).toNat := by
  have := hp.ml; have := hp.pl
  simp [Spec.RsaPkcs1Enc.encode, bytesAt_length]; omega_arith

theorem callArgs_ok {s y : State} (hp : PreE s) (hy : EmDone s y) :
    WP isa (.block callArgs) y (AtCall s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨M₀, hM₀⟩ := hy.em
  have emb₀ : Spec.Rsa.bytesAt y.mem (emA s) (s.gpr .a3).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [hM₀, bytes_written (encode_length hp) (by omega_arith)]
  unfold callArgs argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun y₀ o₀ e₀ => ?_
  rw [hy.sp, BitVec.add_zero] at e₀
  have hz : InRegions y₀.wr (fb s + BitVec.ofNat 64 oZ) 8 := by rw [o₀.wr, hy.wr]; exact in_fr s _ (by decide)
  refine wp_sd (a := fb s + BitVec.ofNat 64 oZ) (by rw [e₀]) (fb_al8 hp.spal hp.sp1 (by decide)) hz
    fun y₁ m₁ => ?_
  refine wp_mov fun y₂ o₂ e₂ => wp_mov fun y₃ o₃ e₃ => wp_mov fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ =>
    wp_addi (imm := oEM) fun y₆ o₆ e₆ => wp_mov fun y₇ o₇ e₇ => ?_
  have fr₁ : Frame [⟨fb s + BitVec.ofNat 64 oZ, 8⟩] y.mem y₁.mem := by
    rw [m₁.mem, o₀.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₁ : EMid s y₁ := hy.toMid.frameW1 (o₀.keep.trans m₁.keep) hp.ksc (by decide) (by decide) fr₁
  have O₇ : Only [.a0, .a1, .a4, .a5, .a6, .a7] y₁ y₇ :=
    (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))).mono
  have mid₇ : EMid s y₇ := mid₁.only O₇
  have t0₇ : y₇.gpr .t0 = fb s := by rw [O₇.get .t0, m₁.gpr, e₀]
  refine wp_addSp fun w₁ p₁ f₁ => wp_addi fun w₂ p₂ f₂ => ?_
  have t6₂ : w₂.gpr .t6 = stackArgAddr s 0 := by rw [f₂, f₁, mid₇.sp]; exact t6_eq rfl
  have P₂ : Only [.t6, .t6] y₇ w₂ := p₁.trans p₂
  refine wp_ld (a := stackArgAddr s 2) (by rw [t6₂, stackArgAddr_eq s 2]) (arg_al hp.spal 2)
    (by rw [P₂.rd, mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₈ o₈ e₈ => ?_
  rw [P₂.mem, arg_mid hp mid₇.mem (by decide)] at e₈
  refine wp_sd (a := fb s + BitVec.ofNat 64 0) (by rw [o₈.get .t0, P₂.get .t0, t0₇])
    (fb_al8 hp.spal hp.sp1 (by decide)) (by rw [o₈.wr, P₂.wr, mid₇.wr]; exact in_fr s _ (by decide))
    fun y₉ m₉ => ?_
  have fr₉ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] y₇.mem y₉.mem := by
    rw [m₉.mem, o₈.mem, P₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 0) (e := 0) (by decide) (by decide) (by decide))
  have K₉ : Frame [kR s, scR s] s.mem y₉.mem := mid₇.mem.trans (fr₉.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s (d := 0) (n := 16) (by decide)⟩)
  have g₉ : ∀ r, r ∉ [Reg.t1] → y₉.gpr r = w₂.gpr r := fun r hr => by rw [m₉.gpr, o₈.gpr r hr]
  refine wp_ld (a := stackArgAddr s 3) (by rw [g₉ .t6 (by decide), t6₂, stackArgAddr_eq s 3]) (arg_al hp.spal 3)
    (by rw [m₉.rd, o₈.rd, P₂.rd, mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₁₀ o₁₀ e₁₀ => ?_
  rw [arg_mid hp K₉ (by decide)] at e₁₀
  refine wp_sd (a := fb s + BitVec.ofNat 64 8) (by rw [o₁₀.get .t0, g₉ .t0 (by decide), P₂.get .t0, t0₇])
    (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁₀.wr, m₉.wr, o₈.wr, P₂.wr, mid₇.wr]; exact in_fr s _ (by decide)) fun y₁₁ m₁₁ => ?_
  have fr₁₁ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] y₇.mem y₁₁.mem := by
    rw [m₁₁.mem, o₁₀.mem]
    exact fr₉.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 8) (e := 0) (by decide) (by decide) (by decide))
  have K₁₁ : Frame [kR s, scR s] s.mem y₁₁.mem := mid₇.mem.trans (fr₁₁.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s (d := 0) (n := 16) (by decide)⟩)
  have g₁₁ : ∀ r, r ∉ [Reg.t1] → y₁₁.gpr r = w₂.gpr r := fun r hr => by
    rw [m₁₁.gpr, o₁₀.gpr r hr, g₉ r hr]
  have rd₁₁ : y₁₁.rd = s.rd := by rw [m₁₁.rd, o₁₀.rd, m₉.rd, o₈.rd, P₂.rd, mid₇.rd]
  refine wp_ld (a := stackArgAddr s 4) (by rw [g₁₁ .t6 (by decide), t6₂, stackArgAddr_eq s 4]) (arg_al hp.spal 4)
    (by rw [rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₂ o₁₂ e₁₂ => ?_
  refine wp_ld (a := stackArgAddr s 5) (by rw [o₁₂.get .t6, g₁₁ .t6 (by decide), t6₂, stackArgAddr_eq s 5])
    (arg_al hp.spal 5) (by rw [o₁₂.rd, rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₃ o₁₃ e₁₃ => wp_nil ?_
  rw [arg_mid hp K₁₁ (by decide)] at e₁₂
  rw [o₁₂.mem, arg_mid hp K₁₁ (by decide)] at e₁₃
  have O₁₃ : Only [.a2, .a3] y₁₁ y₁₃ := o₁₂.trans o₁₃
  have g₁₃ : ∀ r, r ∉ [Reg.a2, .a3, .t1, .t6, .t6] → y₁₃.gpr r = y₇.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [O₁₃.gpr r (by simp [hr.1, hr.2.1]), g₁₁ r (by simp [hr.2.2.1]), P₂.gpr r (by simp [hr.2.2.2.1])]
  have hd0 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨fb s + BitVec.ofNat 64 0, 16⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (.inr (by omega_arith)) (by unfold frameBytes at h₂; omega_arith) (by decide)
  have emb₁ : Spec.Rsa.bytesAt y₁.mem (emA s) (s.gpr .a3).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .a3).toNat⟩) fr₁
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith), emb₀]
  have hdS : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 oSave, 40⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd0 (by decide) (by decide)
  have hsv : Spill.Saved (fb s) s.gpr saved y₁₃.mem := by
    rw [O₁₃.mem]; exact mid₇.sv.frame_in saved_offs fr₁₁ hdS
  have hK : Frame [kR s, scR s] s.mem y₁₃.mem := by rw [O₁₃.mem]; exact K₁₁
  have hm := Mid.of mid₇ (w := y₁₃) (fun r hr => g₁₃ r (by revert r; decide))
    (by rw [O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, P₂.sp]) (by rw [O₁₃.rd, rd₁₁, mid₇.rd])
    (by rw [O₁₃.wr, m₁₁.wr, o₁₀.wr, m₉.wr, o₈.wr, P₂.wr]) hK hsv
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₁₃.mem, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .a3).toNat⟩) fr₁₁
      (hd0 (by decide) (by unfold oEM oEM1 frameBytes; omega_arith)) (by dsimp only; omega_arith), O₇.mem,
      emb₁]
  · have hdZ : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 oZ, 64 / 8⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd0 (by decide) (by decide)
    rw [O₁₃.mem, fr₁₁.readW (Region.contains_self _ _) hdZ (by decide), O₇.mem, m₁.mem,
      Mem.readW_writeW_self64, o₀.get .t5, hy.g5]
  · rw [g₁₃ .a0 (by decide), o₇.get .a0, o₆.get .a0, o₅.get .a0, o₄.get .a0, o₃.get .a0, e₂, mid₁.s1]
  · rw [g₁₃ .a1 (by decide), o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, e₃, o₂.get .s2, mid₁.s2]
  · rw [o₁₃.get .a2, e₁₂]
  · rw [e₁₃]
  · rw [g₁₃ .a4 (by decide), o₇.get .a4, o₆.get .a4, o₅.get .a4, e₄, o₃.get .s3, o₂.get .s3, mid₁.s3]
  · rw [g₁₃ .a5 (by decide), o₇.get .a5, o₆.get .a5, e₅, o₄.get .s4, o₃.get .s4, o₂.get .s4, mid₁.s4]
  · rw [g₁₃ .a6 (by decide), o₇.get .a6, e₆, o₅.get .t0, o₄.get .t0, o₃.get .t0, o₂.get .t0, m₁.gpr, e₀]
  · rw [g₁₃ .a7 (by decide), e₇, o₆.get .s2, o₅.get .s2, o₄.get .s2, o₃.get .s2, o₂.get .s2, mid₁.s2]
  · show y₁₃.mem.readW (y₁₃.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, P₂.sp, mid₇.sp, O₁₃.mem, m₁₁.mem, o₁₀.mem,
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₉.mem,
      Mem.readW_writeW_self64]
    exact e₈
  · show y₁₃.mem.readW (y₁₃.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, P₂.sp, mid₇.sp, O₁₃.mem, m₁₁.mem, Mem.readW_writeW_self64, e₁₀]

/-- `EM`, of `k` bytes. -/
abbrev emR (s : State) : Region := ⟨emA s, (s.gpr .a3).toNat⟩

theorem em_sub {s : State} (hp : PreE s) : Region.Sub (emR s) (kR s) :=
  frame_sub s (d := oEM) (n := (s.gpr .a3).toNat) (by have := hp.k2; unfold oEM oEM1 frameBytes; omega_arith)

theorem oR_eq {s : State} (hp : PreE s) : oR s = ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by
  rw [oR, hp.ok]

theorem pdOk_of {s t : State} (hp : PreE s) (ha : AtCall s t) : PdOk t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp.sp1
  have hfa := fb_al hp.spal hp.sp1
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 0 := by rw [stackArgAddr, ha.sp]
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine ⟨?hl, ?spal, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs, ?al2, ?al0⟩
  case hl =>
    rw [ha.g0, ha.g1, ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.sa0, ha.sa1, hsa]
    exact {
      on := by rw [← oR_eq hp]; exact hp.op
      oe := by rw [← oR_eq hp]; exact hp.oe
      oi := (hko.sub_left (em_sub hp)).symm
      os := by rw [← oR_eq hp]; exact hp.osc
      oa := (hko.sub_left (frame_sub s (d := 0) (n := 16) (by decide))).symm
      ns := hp.sp.symm
      es := hp.es
      is := hp.ksc.sub_left (em_sub hp)
      sa := (hp.ksc.sub_left (frame_sub s (d := 0) (n := 16) (by decide))).symm
      wo := by have := hp.wo; rw [hp.ok] at this; exact this
      wn := hp.wp
      we := hp.we
      wi := by
        show (fb s + BitVec.ofNat 64 oEM).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM oEM1 frameBytes at *; omega_arith
      ws := hp.wsc }
  case spal => rw [ha.sp]; exact hfa
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega_arith
  case hrd =>
    simp only [pdRd]
    rw [ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, hsa, ha.rd, ha.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (kR s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (Covers.one (in_fr' s _ _ (by unfold oEM oEM1 frameBytes; omega_arith)))
        (Covers.one (in_fr' s _ _ (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g0, ha.g1, ha.sa0, ha.sa1, ha.wr]
    exact Covers.of_mem fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr, oR_eq hp]; simp)
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp)
  case hk => rw [ha.g1]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g3, ha.g1]; exact hp.hp
  case h10 => rw [ha.g7, ha.g1]
  case he1 => rw [ha.g5]; exact hp.e1
  case he2 => rw [ha.g5, ha.g1]; exact hp.e2
  case hs => rw [ha.g1, ha.sa1]; exact hp.hs
  case al2 => rw [ha.g2]; exact hp.al4
  case al0 => rw [ha.sa0]; exact hp.al2

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat)

/-- RSAEP of `EM`, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s))

/-- After the call: what the restores need, `out` and `k` kept, the zero
test in its word, and `out` written with RSAEP's result if `pre` holds the
modulus' values. -/
structure AfterCall (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s1 : t.gpr .s1 = s.gpr .a0
  s2 : t.gpr .s2 = s.gpr .a3
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .a0) (s.gpr .a3).toNat ((t.gpr .a0).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreE s) (ha : AtCall s t) : WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g0, ha.g1, ha.sa0, ha.sa1] at hf
  have hko : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  have hdF : ∀ {d k : Nat}, d + k ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region), scR s],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (frame_sub s h)
    · exact hp.ksc.sub_left (frame_sub s h)
  refine ⟨⟨hsp'.trans ha.sp, hwr'.trans ha.wr, fun r hr => (hpres r (by revert r; decide)).trans (ha.hi r hr),
    ha.sv.frame hf fun p hp' => hdF (by have := saved_offs p hp'; unfold oSave frameBytes at *; omega_arith)⟩,
    hrd'.trans ha.rd, (hpres .s1 (by decide)).trans ha.s1, (hpres .s2 (by decide)).trans ha.s2,
    by rw [hf.readW (Region.contains_self _ _) (hdF (by decide)) (by decide)]; exact ha.slot, fun hc => ?_⟩
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat := by
    rw [ha.g2, ha.g3]; exact words_of_frame ha.mem hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (by rw [ha.g1, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g0, ha.g1, ha.g4, ha.g5, ha.g6, ha.emb,
    bytes_of_frame ha.mem hp.ke hp.es.symm (by have := hp.we; omega_arith)] at this
  exact this

end VG.Proof.RsaPkcs1Enc.RISCV64.Enc


namespace VG.Proof.RsaPkcs1Enc.RISCV64.Enc

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Sig.RISCV64.Rec (maskOf maskOf_bytes maskOf_byte freed_mem freed_gpr)
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- The result and `out`, from the entry state `s`: the octets `encrypt`
returns, or zeros. -/
def Post (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s →
    Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (msgB s) (psB s)))

theorem zbit_mask (l : List Byte) : zbit l - BitVec.ofNat 64 1 = maskOf (zbit l = 0) := by
  unfold maskOf zbit; split <;> decide

theorem zbit_eq_zero {l : List Byte} : zbit l = 0 ↔ l.all (· != 0) = true := by
  unfold zbit; split <;> simp_all

theorem encrypt_eq {s : State} (hp : PreE s) :
    Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (msgB s) (psB s) =
      if zbit (psB s) = 0 then pubOut s else none := by
  have := hp.ml; have := hp.pl
  unfold Spec.RsaPkcs1Enc.encrypt pubOut
  simp only [bytesAt_length, zbit_eq_zero]
  by_cases h : (psB s).all (· != 0) = true
  · rw [ite_eq_left ⟨by omega_arith, by omega_arith, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2.2), ite_eq_right h]

/-- Writes of the frame above the slots keep `Saves`. -/
theorem saves_frameW1 {s t w : State} {rs : List Reg} (h : Saves s t) (o : Kept rs t w) {e n : Nat}
    (he : oRa + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Saves s w := by
  have hd : ∀ {d' k : Nat}, d' + k ≤ oRa + 8 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 e, n⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d', k⟩ r := fun hk r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by unfold oRa at hk; omega_arith)
      (by unfold frameBytes at hen; omega_arith)
  exact ⟨o.sp.trans h.sp, o.wr.trans h.wr,
    fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr),
    h.sv.frame_in saved_offs hm (hd (by decide))⟩

theorem tail_ok {s t : State} (hp : PreE s) (ha : AfterCall s t) :
    WP isa tail t fun w => Post s (freed frameBytes w) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfa := fb_al hp.spal hp.sp1
  unfold tail maskArgs
  refine WP.seq (wp_addSp fun t₁ o₁ e₁ => ?_)
  rw [ha.sv.sp, BitVec.add_zero] at e₁
  refine wp_ld (a := fb s + BitVec.ofNat 64 oZ) (by rw [e₁]) (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁.rd, o₁.wr, ha.sv.wr]; exact in_fr' s _ _ (by decide)) fun t₂ o₂ e₂ =>
    wp_subi (imm := 1) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ =>
    wp_nil ?_
  have O₆ : Only [.t0, .a3, .a3, .a0, .a1, .a5] t t₆ :=
    o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))
  have sv₆ : Saves s t₆ := ha.sv.keep O₆.keep (R := []) (by rw [O₆.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have r9₆ : t₆.gpr .a3 = maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .a3, o₅.get .a3, o₄.get .a3, e₃, e₂, o₁.mem, ha.slot, zbit_mask]
  have r3₆ : t₆.gpr .a0 = t.gpr .a0 &&& maskOf (zbit (psB s) = 0) := by
    rw [o₆.get .a0, o₅.get .a0, e₄, o₃.get .a0, o₂.get .a0, o₁.get .a0, ← r9₆, o₆.get .a3, o₅.get .a3,
      o₄.get .a3]
  have hout : ∀ i < (s.gpr .a3).toNat, InRegions (kR s :: s.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨oR s, List.mem_cons_of_mem _ (by rw [hp.hwr]; simp),
      Offset.contains_base _ (by rw [hp.ok]; omega_arith) (by have := hp.wo; omega_arith)⟩
  have hdo : (kR s).Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine WP.seq (WP.mono (Rec.maskLoop_ok (p := s.gpr .a0) (n := (s.gpr .a3).toNat) (by omega_arith)
    (by omega_arith)
    (by rw [o₆.get .a1, e₅, o₄.get .s1, o₃.get .s1, o₂.get .s1, o₁.get .s1, ha.s1])
    (by rw [e₆, o₅.get .s2, o₄.get .s2, o₃.get .s2, o₂.get .s2, o₁.get .s2, ha.s2]; simp)
    (fun i hi => by rw [sv₆.wr]; exact hout i hi)) fun u ⟨ku, mu⟩ => ?_)
  have hB : Spec.Rsa.bytesAt t₆.mem (s.gpr .a0) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a3).toNat := by rw [O₆.mem]
  rw [r9₆, maskOf_bytes, bytesAt_length, hB] at mu
  generalize hX : (if zbit (psB s) = 0 then Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a3).toNat
    else List.replicate (s.gpr .a3).toNat 0) = X at mu
  have hXl : X.length = (s.gpr .a3).toNat := by rw [← hX]; split <;> simp [bytesAt_length]
  have svu : Saves s u := sv₆.keep ku (R := [⟨s.gpr .a0, (s.gpr .a3).toNat⟩])
    (by have h := frame_writeBytes t₆.mem (s.gpr .a0) X; rw [hXl] at h; rw [mu]; exact h)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdo)
  unfold wipeArgs
  refine WP.seq (wp_addSp fun w₁ p₁ f₁ => wp_addi (imm := oEM) fun w₂ p₂ f₂ => wp_mov fun w₃ p₃ f₃ =>
    wp_li (imm := 0) (by decide) fun w₄ p₄ f₄ => wp_nil ?_)
  rw [svu.sp, BitVec.add_zero] at f₁
  have P₄ : Only [.t0, .a1, .t5, .t0] u w₄ := p₁.trans (p₂.trans (p₃.trans p₄))
  have svw : Saves s w₄ := svu.keep P₄.keep (R := []) (by rw [P₄.mem]; exact Frame.refl _ _)
    (fun r h => nomatch h)
  have hem : ∀ {i : Nat}, i < (s.gpr .a3).toNat → InRegions (kR s :: s.wr) (emA s + BitVec.ofNat 64 i) 1 :=
    fun hi => by
      rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1 frameBytes; omega_arith)
  refine WP.seq (WP.mono (fill_ok (p := emA s) (n := (s.gpr .a3).toNat) (b := 0) (by omega_arith)
    (by omega_arith) (by rw [p₄.get .a1, p₃.get .a1, f₂, f₁])
    (by rw [p₄.get .t5, f₃, p₂.get .s2, p₁.get .s2, ku.get .s2, o₆.get .s2, o₅.get .s2, o₄.get .s2,
      o₃.get .s2, o₂.get .s2, o₁.get .s2, ha.s2]; simp)
    (by rw [f₄]; rfl)
    (fun i hi => by rw [svw.wr]; exact hem hi)) fun w₅ ⟨k₅, m₅⟩ => ?_)
  have fr₅ : Frame [⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .a3).toNat⟩] w₄.mem w₅.mem := by
    have h := frame_writeBytes w₄.mem (emA s) (List.replicate (s.gpr .a3).toNat (0 : Byte))
    rw [List.length_replicate] at h; rw [m₅]; exact h
  have sv₅ : Saves s w₅ := saves_frameW1 svw k₅ (by decide) (by unfold oEM oEM1 frameBytes; omega_arith) fr₅
  refine WP.mono (restore_ok sv₅ (by omega)) fun w' ⟨habi, h3, hm⟩ => ⟨habi, fun hc => ?_⟩
  have hbytes : Spec.Rsa.bytesAt w'.mem (s.gpr .a0) (s.gpr .a3).toNat = X := by
    rw [hm, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨s.gpr .a0, (s.gpr .a3).toNat⟩) fr₅
      (hdo.sub_left (em_sub hp)).symm (by dsimp only; omega_arith), P₄.mem, mu, bytes_written hXl (by omega_arith)]
  have hr : w'.gpr .a0 = t.gpr .a0 &&& maskOf (zbit (psB s) = 0) := by
    rw [h3, k₅.get .a0, P₄.get .a0, ku.get .a0, r3₆]
  rw [freed_mem, freed_gpr, hr, encrypt_eq hp]
  have hres := ha.res hc
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

theorem code_ok {s : State} (hp : PreE s) : WP isa code s (Post s) := by
  unfold code
  refine WP.allocLe (by decide) hp.sp1 ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok hp rfl rfl rfl (Frame.refl _ _) (fun _ => rfl)) fun w hw => ?_)
  refine WP.seq (WP.mono (preCall_ok hp hw) fun t ht => ?_)
  exact WP.seq (WP.mono (call_ok hp ht) fun t' ht' => tail_ok hp ht')

/-- The correctness of `vg_rsa_pkcs1_encrypt_precomputed`, against its
shared contract. -/
theorem code_correct (s : State) (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok (preE_of h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    stackArgs_six, List.append_eq]
  exact hr

end VG.Proof.RsaPkcs1Enc.RISCV64.Enc
