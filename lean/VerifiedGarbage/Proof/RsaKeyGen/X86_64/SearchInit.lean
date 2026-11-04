module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SearchInit
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SearchInit
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationContract
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues

/-! # Starting the RSA prime search on x86-64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.SearchInit

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.SearchInit
open VG.Proof.RsaKeyGen.SearchInit

/-! ## Whether the exponent is 3 -/

/-! ## The loop over the exponent's octets -/

/-- Before the loop: no OR yet, `e_len - 1` leading octets to go, and
whether there are none. -/
theorem isThree_setup {s : State} {len : Nat} (hl : s.gpr .rcx = BitVec.ofNat 64 len)
    (h1 : 1 ≤ len) (h8 : len ≤ 8) :
    WP isa (.block [.mov32 .r9 (.imm 0), .mov .r11 (.reg .rcx), .alu .sub .r11 (.imm 1),
      .alu .test .r11 (.reg .r11)]) s fun t =>
      (t.gpr .r9 = 0 ∧ t.gpr .r11 = BitVec.ofNat 64 (len - 1) ∧
        eval .e t = some (decide (len - 1 = 0)) ∧ t.mem = s.mem) ∧ Keep [.r9, .r11] s t := by
  refine WP.keep [.r9, .r11] ?_ ?_
  · xrun [hl, eval, ofNat64_pred h1 (by omega), BitVec.and_self, ofNat64_beq_zero (show len - 1 < 2 ^ 64 by omega)]
  · rfl

/-- One leading octet: ORed in, the pointer advanced, one fewer to go. -/
theorem isThree_body {t : State} {P : Addr} {j k : Nat} {acc : BitVec 64}
    (hp : t.gpr .rdx = P + BitVec.ofNat 64 j) (hk : t.gpr .r11 = BitVec.ofNat 64 (k + 1))
    (hacc : t.gpr .r9 = acc) (hk8 : k < 8)
    (hr : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.movzx8 .rax { base := .rdx }, .alu .or .r9 (.reg .rax),
      .alu .add .rdx (.imm 1), .alu .sub .r11 (.imm 1)]) t fun u =>
      (u.zf = some (decide (k = 0)) ∧ u.gpr .rdx = P + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .r11 = BitVec.ofNat 64 k ∧
        u.gpr .r9 = acc ||| (t.mem (P + BitVec.ofNat 64 j)).setWidth 64 ∧ u.mem = t.mem) ∧
      Keep [.rax, .r9, .rdx, .r11] t u := by
  refine WP.keep [.rax, .r9, .rdx, .r11] ?_ ?_
  · have hk' : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k :=
      (ofNat64_pred (by omega) (by omega)).trans (by rw [Nat.add_sub_cancel])
    have h1 : BitVec.signExtend 64 1#32 = (1 : BitVec 64) := by decide
    have hz : (BitVec.ofNat 64 k == 0#64) = decide (k = 0) := ofNat64_beq_zero (by omega)
    xrun [State.ea, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hp, hk, hacc, hr, h1, hk', hz,
      BitVec.add_assoc, ofNat_add_one]
    have e1 : (1#64 : BitVec 64) = 1 := rfl
    refine ⟨?_, ?_, ?_⟩ <;> simp only [e1, hk', hz, ofNat_add_one]
  · rfl

/-- After `j` leading octets. -/
def LeadInv (s : State) (P : Addr) (len j : Nat) (u : State) : Prop :=
  u.gpr .rdx = P + BitVec.ofNat 64 j ∧ u.gpr .r11 = BitVec.ofNat 64 (len - 1 - j) ∧
    u.gpr .r9 = orOf (Spec.Rsa.bytesAt s.mem P j) ∧ u.mem = s.mem ∧
    Keep [.r9, .r11, .rax, .rdx] s u

/-- The leading octets: none, or the loop over them. -/
theorem isThree_loop {s t : State} {P : Addr} {len : Nat} (h1 : 1 ≤ len) (h8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (he : eval .e t = some (decide (len - 1 = 0))) (h0 : LeadInv s P len 0 t) :
    WP isa (.ite .e (.block [])
        (.loop (.block [.movzx8 .rax { base := .rdx }, .alu .or .r9 (.reg .rax),
          .alu .add .rdx (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)) t
      (LeadInv s P len (len - 1)) := by
  refine WP.ite (decide (len - 1 = 0)) he (fun hz => ?_) (fun hz => ?_)
  · have hz : len - 1 = 0 := of_decide_eq_true hz
    exact WP.block_nil (by rw [hz]; exact h0)
  · have hz : len - 1 ≠ 0 := of_decide_eq_false hz
    refine wp_upto (a := 0) (N := len - 1) (by omega) (LeadInv s P len) ?_ (fun _ h => h) h0
    intro j _ hj u ⟨hdx, hr11, hr9, hum, ku⟩
    have hk1 : len - 1 - j = (len - 1 - j - 1) + 1 := by omega
    have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
      rw [ku.2.1, ku.2.2]; exact hrd j (by omega)
    refine WP.mono (isThree_body hdx (k := len - 1 - j - 1) (by rw [hr11, ← hk1]) hr9 (by omega) hr)
      fun v ⟨⟨hz, hd, h11', h9', hm'⟩, kv⟩ => ⟨?_, hd, ?_, ?_, hm'.trans hum, (ku.trans kv).mono (by decide)⟩
    · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
    · rw [h11', show len - 1 - j - 1 = len - 1 - (j + 1) by omega]
    · rw [h9', bytesAt_succ, orOf_snoc, hum]

/-- The last octet XOR 3, ORed with the leading ones. -/
theorem isThree_last {s u : State} {P : Addr} {len : Nat} (h1 : 1 ≤ len)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (h : LeadInv s P len (len - 1) u) :
    WP isa (.block [.movzx8 .rax { base := .rdx }, .alu .xor .rax (.imm 3), .alu .or .rax (.reg .r9)]) u
      fun t => (t.gpr .rax = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧ t.mem = s.mem ∧
        Keep [.r9, .r11, .rax, .rdx] s t := by
  obtain ⟨hdx, -, hr9, hum, ku⟩ := h
  have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 1)) 1 := by
    rw [ku.2.1, ku.2.2]; exact hrd (len - 1) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax =
      ((u.mem (P + BitVec.ofNat 64 (len - 1))).setWidth 64 ^^^ 3) ||| orOf (Spec.Rsa.bytesAt s.mem P (len - 1)) ∧
      t.mem = u.mem) ?_ ?_) fun t ⟨⟨ha, hm⟩, kt⟩ => ⟨?_, hm.trans hum, (ku.trans kt).mono (by decide)⟩
  · have h3 : BitVec.signExtend 64 3#32 = (3 : BitVec 64) := by decide
    xrun [State.ea, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hdx, hr, hr9, h3]
  · rfl
  · have hb : Spec.Rsa.bytesAt s.mem P len =
        Spec.Rsa.bytesAt s.mem P (len - 1) ++ [s.mem (P + BitVec.ofNat 64 (len - 1))] := by
      rw [← bytesAt_succ, Nat.sub_add_cancel h1]
    rw [ha, hum, hb, os2ip_eq_three, BitVec.or_comm]

/-- `isThree`: rax is 0 iff `e` (`len` octets at rdx) is 3. -/
theorem isThree_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .rdx = P)
    (hl : s.gpr .rcx = BitVec.ofNat 64 len) (h1 : 1 ≤ len) (h8 : len ≤ 8)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa isThree s fun t =>
      (t.gpr .rax = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) ∧ t.mem = s.mem ∧
        Keep [.r9, .r11, .rax, .rdx] s t := by
  unfold isThree
  refine WP.seq (WP.mono (isThree_setup hl h1 h8) fun t ⟨⟨h9, h11, he, hm⟩, k⟩ => ?_)
  have h0 : LeadInv s P len 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero], by
      rw [h11, Nat.sub_zero], h9, hm, k.mono (by decide)⟩
  exact WP.seq (WP.mono (isThree_loop h1 h8 hrd he h0) fun u hu => isThree_last h1 hrd hu)

/-! ## The four words -/

theorem initialize_ok {s : State} {B : Addr} {L : Nat} {three : Bool}
    (scr : Scr s B 32) (hdi : s.gpr .rdi = B) (hsi : s.gpr .rsi = BitVec.ofNat 64 L) (hL : L ≤ 512)
    (hz : (s.gpr .rax == 0) = three) :
    WP isa (.block [
      .mov .r9 (.reg .rax), .mov .rax (.reg .rsi), .shift .shl .rax 3, .mov .rcx (.reg .rax),
      .shift .shl .rax 2, .alu .add .rax (.reg .rcx), .mov .rcx (.reg .rsi), .shift .shl .rcx 6,
      .alu .test .r9 (.reg .r9), .cmov .e .rax (.reg .rcx), .store (field 0) .rax,
      .store (field 1) .rsi,
      .mov .rax (.reg .rsi), .shift .shl .rax 15, .alu .add .rax (.reg .rsi), .store (field 2) .rax,
      .mov .rax (.reg .rsi), .shift .shl .rax 5, .store (field 3) .rax, .mov32 .rax (.imm 1)]) s
      fun t => t.gpr .rax = 1 ∧ t.mem = written s.mem B (initWords L three) := by
  have hstore : ∀ j < 4, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  have h8 := shl_ofNat L 3 (by omega_using [hL])
  have h32 := shl_ofNat (L * 2 ^ 3) 2 (by omega_using [hL])
  have h64 := shl_ofNat L 6 (by omega_using [hL])
  have h15 := shl_ofNat L 15 (by omega_using [hL])
  have h5 := shl_ofNat L 5 (by omega_using [hL])
  have e40 : BitVec.ofNat 64 (L * 2 ^ 3 * 2 ^ 2) + BitVec.ofNat 64 (L * 2 ^ 3) = BitVec.ofNat 64 (40 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e64 : BitVec.ofNat 64 (L * 2 ^ 6) = BitVec.ofNat 64 (64 * L) := by congr 1; omega
  have e32769 : BitVec.ofNat 64 (L * 2 ^ 15) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e32 : BitVec.ofNat 64 (L * 2 ^ 5) = BitVec.ofNat 64 (32 * L) := by congr 1; omega
  unfold written initWords
  cases three <;>
  xrun [field, State.ea, off, BitVec.ofInt_natCast, eval, execCmov, hdi, hsi, h8, h32, h64, h15, h5, e40, e64,
    e32769, e32, BitVec.and_self, hz, hstore 0 (by decide), hstore 1 (by decide), hstore 2 (by decide),
    hstore 3 (by decide), Bool.false_eq_true] <;>
  simp only [Nat.reduceMul, BitVec.add_zero, List.getD_cons_zero, List.getD_cons_succ] <;> rfl

/-! ## The guards -/

/-- `cmp r, c` for an immediate `c` that sign-extends to `k`. -/
theorem cmp_imm (s : State) (r : Reg) (c : BitVec 32) (k : Nat) (hk : k < 2 ^ 31)
    (hc : BitVec.signExtend 64 c = BitVec.ofNat 64 k) :
    WP isa (.block [.alu .cmp r (.imm c)]) s fun t =>
      (eval .b t = some (decide ((s.gpr r).toNat < k)) ∧
        eval .ae t = some (decide (k ≤ (s.gpr r).toNat)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [r] (Q := fun t => eval .b t = some (decide ((s.gpr r).toNat < k)) ∧
      eval .ae t = some (decide (k ≤ (s.gpr r).toNat)) ∧ t.mem = s.mem ∧ t.gpr r = s.gpr r) ?_ ?_)
    fun t ⟨⟨hb, ha, hm, hr⟩, kt⟩ => ⟨⟨hb, ha, hm⟩, ⟨fun q _ => by
      by_cases he : q = r
      · subst he; exact hr
      · exact kt.gpr (by simpa only [List.mem_singleton] using he), kt.2⟩⟩
  · have hkk : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    xrun [hc, eval, hkk]
    by_cases h : k ≤ (s.gpr r).toNat
    · simp only [show ¬(s.gpr r).toNat < k by omega, decide_false, Bool.not_false, h, decide_true]
    · simp only [show (s.gpr r).toNat < k by omega, decide_true, Bool.not_true, h, decide_false]
  · cases r <;> rfl

theorem and7_beq (x : BitVec 64) : (x &&& BitVec.signExtend 64 (7 : BitVec 32) == 0) = decide (x.toNat % 8 = 0) := by
  have h7 : BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 (2 ^ 3 - 1) := by decide
  rw [h7]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (2 ^ 3 - 1) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (2 ^ 3 - 1) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact h

/-- Whether `prime_len` is a multiple of 8. -/
theorem multiple_guard (s : State) :
    WP isa (.block [.mov .rax (.reg .rsi), .alu .and .rax (.imm 7)]) s fun t =>
      (eval .ne t = some (!decide ((s.gpr .rsi).toNat % 8 = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  refine WP.keep [.rax] ?_ ?_
  · xrun [eval, and7_beq]
  · rfl

/-- Whether `e_len` is 0. -/
theorem zero_guard (s : State) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      (eval .e t = some (decide ((s.gpr .rcx).toNat = 0)) ∧ t.mem = s.mem ∧ t.gpr .rcx = s.gpr .rcx) ∧
        Keep [.rcx] s t := by
  refine WP.keep [.rcx] ?_ ?_
  · have hz : (s.gpr .rcx == 0) = decide ((s.gpr .rcx).toNat = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    xrun [eval, BitVec.and_self, hz]
  · rfl

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 32) (hdi : s.gpr .rdi = B) :
    WP isa clear s fun t => t.gpr .rax = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  have hstore : ∀ j < 4, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  unfold clear written
  xrun [field, State.ea, off, BitVec.ofInt_natCast, hdi,
    hstore 0 (by decide), hstore 1 (by decide), hstore 2 (by decide), hstore 3 (by decide)]
  simp only [Nat.reduceMul, BitVec.add_zero, List.getD_cons_zero, List.getD_cons_succ]
  rfl

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L len : Nat) (m : Mem) (B P : Addr) (t : State) : Prop :=
  if initValid L len then
    t.gpr .rax = 1 ∧ t.mem = written m B (initWords L (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P len) = 3)))
  else t.gpr .rax = 0 ∧ t.mem = written m B [0, 0, 0, 0]

private theorem clear_post {t : State} {B P : Addr} {L len : Nat} {m : Mem}
    (scr : Scr t B 32) (hdi : t.gpr .rdi = B) (hm : t.mem = m) (hv : ¬initValid L len) :
    WP isa clear t (InitPost L len m B P) := by
  refine WP.mono (clear_ok scr hdi) fun u ⟨ha, hu⟩ => ?_
  unfold InitPost
  split
  · exact absurd ‹_› hv
  · exact ⟨ha, by rw [hu, hm]⟩

theorem init_ok {s : State} {B P : Addr} (scr : Scr s B 32) (hdi : s.gpr .rdi = B) (hp : s.gpr .rdx = P)
    (hrd : (s.gpr .rcx).toNat ≤ 8 →
      ∀ i < (s.gpr .rcx).toNat, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa init s (InitPost (s.gpr .rsi).toNat (s.gpr .rcx).toNat s.mem B P) := by
  let L := (s.gpr .rsi).toNat
  let len := (s.gpr .rcx).toNat
  change WP isa init s (InitPost L len s.mem B P)
  unfold init
  refine WP.seq (WP.mono (cmp_imm s .rsi 32 32 (by decide) (by decide)) fun u ⟨⟨hb, _, hm⟩, k⟩ => ?_)
  have hsc : ∀ {a b : State}, Keep [] a b → ∀ r, b.gpr r = a.gpr r := fun k r => k.gpr (by simp)
  refine WP.ite _ hb (fun h => clear_post (scr.congr k.2.2) ((hsc k _).trans hdi) hm
    fun hv => by have := of_decide_eq_true h; exact absurd hv.1 (by omega)) fun h => ?_
  have h32 : 32 ≤ L := by have := of_decide_eq_false h; omega
  refine WP.seq (WP.mono (cmp_imm u .rsi 513 513 (by decide) (by decide)) fun v ⟨⟨_, ha, hmv⟩, kv⟩ => ?_)
  rw [hsc k] at ha
  refine WP.ite _ ha (fun h => clear_post ((scr.congr k.2.2).congr kv.2.2)
    (by rw [hsc kv, hsc k, hdi]) (hmv.trans hm)
    fun hv => by have := of_decide_eq_true h; exact absurd hv.2.1 (by omega)) fun h => ?_
  have h512 : L ≤ 512 := by have := of_decide_eq_false h; omega
  refine WP.seq (WP.mono (multiple_guard v) fun w ⟨⟨hne, hmw⟩, kw⟩ => ?_)
  rw [hsc kv, hsc k] at hne
  have hdw : w.gpr .rdi = B := by rw [kw.gpr (by decide), hsc kv, hsc k, hdi]
  have scw : Scr w B 32 := ((scr.congr k.2.2).congr kv.2.2).congr kw.2.2
  have hmw' : w.mem = s.mem := hmw.trans (hmv.trans hm)
  refine WP.ite _ hne (fun h => clear_post scw hdw hmw'
    fun hv => by simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h; exact h hv.2.2.1) fun h => ?_
  have h8 : L % 8 = 0 := by simpa only [Bool.not_eq_false', decide_eq_true_eq] using h
  unfold checkExponent
  refine WP.seq (WP.mono (zero_guard w) fun x ⟨⟨hz, hmx, hcx⟩, kx⟩ => ?_)
  have hcw : w.gpr .rcx = s.gpr .rcx := by rw [kw.gpr (by decide), hsc kv, hsc k]
  rw [hcw] at hz
  have hdx : x.gpr .rdi = B := by rw [kx.gpr (by decide), hdw]
  have scx : Scr x B 32 := scw.congr kx.2.2
  have hmx' : x.mem = s.mem := hmx.trans hmw'
  refine WP.ite _ hz (fun h => clear_post scx hdx hmx'
    fun hv => by have := of_decide_eq_true h; exact absurd hv.2.2.2.1 (by omega)) fun h => ?_
  have h1 : 1 ≤ len := by have := of_decide_eq_false h; omega
  refine WP.seq (WP.mono (cmp_imm x .rcx 9 9 (by decide) (by decide)) fun y ⟨⟨_, ha9, hmy⟩, ky⟩ => ?_)
  rw [hcx, hcw] at ha9
  have hdy : y.gpr .rdi = B := by rw [hsc ky, hdx]
  have scy : Scr y B 32 := scx.congr ky.2.2
  have hmy' : y.mem = s.mem := hmy.trans hmx'
  refine WP.ite _ ha9 (fun h => clear_post scy hdy hmy'
    fun hv => by have := of_decide_eq_true h; exact absurd hv.2.2.2.2 (by omega)) fun h => ?_
  have h9 : len ≤ 8 := by have := of_decide_eq_false h; omega
  have hv : initValid L len := ⟨h32, h512, h8, h1, h9⟩
  -- The exponent's octets are readable in `y`.
  have hry : ∀ i < len, InRegions (y.rd ++ y.wr) (P + BitVec.ofNat 64 i) 1 := by
    rw [ky.2.1, ky.2.2, kx.2.1, kx.2.2, kw.2.1, kw.2.2, kv.2.1, kv.2.2, k.2.1, k.2.2]
    exact hrd h9
  have hpy : y.gpr .rdx = P := by
    rw [hsc ky, kx.gpr (by decide), kw.gpr (by decide), hsc kv, hsc k, hp]
  have hly : y.gpr .rcx = BitVec.ofNat 64 len := by
    rw [hsc ky, hcx, hcw]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)])
  unfold initializeState
  refine WP.seq (WP.mono (isThree_ok hpy hly h1 h9 hry) fun z ⟨hzi, hmz, kz⟩ => ?_)
  have hsz : z.gpr .rsi = BitVec.ofNat 64 L := by
    rw [kz.gpr (by decide), hsc ky, kx.gpr (by decide), kw.gpr (by decide), hsc kv, hsc k]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)])
  have hdz : z.gpr .rdi = B := by rw [kz.gpr (by decide), hdy]
  have hzz : (z.gpr .rax == 0) = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P len) = 3) := by
    rw [← hmy']
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact hzi
  refine WP.mono (initialize_ok (scy.congr kz.2.2) hdz hsz h512 hzz) fun t ⟨ha, ht⟩ => ?_
  unfold InitPost
  split
  · exact ⟨ha, by rw [ht, hmz, hmy']⟩
  · exact absurd hv ‹_›

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩] ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩

def initPost (s t : State) : Prop :=
  match Spec.RsaKeyGen.primeInit (s.gpr .rsi).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
  | none => ((t.gpr .rax).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = List.replicate 4 0
  | some values => ((t.gpr .rax).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop :=
  s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .rsi).toNat (s.gpr .rcx).toNat s.mem (s.gpr .rdi) (s.gpr .rdx) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost
  have hl : (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length = (s.gpr .rcx).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  rw [primeInit_eq, hl]
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [h.1]; rfl, ?_⟩
    rw [h.2, initWords, written_words]
    simp only [List.map_cons, List.map_nil, decide_eq_true_eq]
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome, hret⟩ := h
  have scr : Scr s (s.gpr .rdi) 32 := Scr.of_mem (by rw [hwr]; simp) hroom
  have hreads : (s.gpr .rcx).toNat ≤ 8 →
      ∀ i < (s.gpr .rcx).toNat, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) 1 :=
    fun _ i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r9, .r11]
    (init_ok scr rfl rfl hreads) (by decide +kernel)
  have safe : SpSafe init := SpSafe.of_all (Code.all_of_allInstrs (by decide +kernel))
  have hd : init.x86_64Depth = 0 := rfl
  have hf := Exec.stackFrame safe he (by rw [hd]; decide)
  rw [hwr, hd] at hf
  have hr : t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hret
    · exact Offset.base_disjoint_below _ (by decide)
  refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ⟨?_, hr⟩, result_post hp⟩
  intro r hr
  exact k.gpr (by revert r; decide)

def InitInput (p : Addr × BitVec 64 × Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .rdi = p.1 ∧ s.gpr .rsi = p.2.1 ∧ s.gpr .rdx = p.2.2.1 ∧ s.gpr .rcx = p.2.2.2

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have ct : RelCT isa (Two InitInput) init fun _ _ => True :=
    two_taint [.rdi, .rsi, .rdx, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.1.trans h₂.2.2.1.symm,
        h₁.2.2.2.trans h₂.2.2.2.symm]) (by taint_decide)
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hdi, hsi, hdx, hcx⟩ := h
  exact ⟨(s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx), ⟨rfl, rfl, rfl, rfl⟩,
    hdi.symm, hsi.symm, hdx.symm, hcx.symm⟩

private def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 3 | .rsp => 0x3000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.primeInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.primeInitContract, Spec.RsaKeyGen.primeInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.RsaKeyGen.X86_64.SearchInit
