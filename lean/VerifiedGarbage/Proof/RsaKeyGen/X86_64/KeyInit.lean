module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
meta import VerifiedGarbage.Impl.RsaKeyGen.X86_64.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes

/-! # Starting RSA key generation on x86-64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.KeyInit

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.KeyInit

/-! ## The exponent's octets -/

theorem shl8_add (v : Nat) (hv : v < 2 ^ 32) (b : Byte) :
    BitVec.ofNat 64 v <<< 8 + b.setWidth 64 = BitVec.ofNat 64 (256 * v + b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : v * 2 ^ 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem low32 (n : Nat) : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) =
    BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem shr32 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 32 = BitVec.ofNat 64 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem octet_ok {t : State} {P : Addr} {j k v : Nat} {acc : BitVec 64}
    (hp : t.gpr .rdx = P + BitVec.ofNat 64 j) (hk : t.gpr .rcx = BitVec.ofNat 64 (k + 1))
    (hv : t.gpr .r9 = BitVec.ofNat 64 v) (hacc : t.gpr .r10 = acc) (hk64 : k + 1 < 2 ^ 64)
    (hv32 : v < 2 ^ 32)
    (hr : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 j) 1) :
    WP isa (.block octet) t fun u =>
      (u.zf = some (decide (k = 0)) ∧ u.gpr .rdx = P + BitVec.ofNat 64 (j + 1) ∧
        u.gpr .rcx = BitVec.ofNat 64 k ∧
        u.gpr .r9 = BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) % 2 ^ 32) ∧
        u.gpr .r10 = acc ||| BitVec.ofNat 64 ((256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat) / 2 ^ 32) ∧
        u.mem = t.mem) ∧
      Keep [.rax, .r9, .r10, .rdx, .rcx] t u := by
  refine WP.keep [.rax, .r9, .r10, .rdx, .rcx] ?_ ?_
  · unfold octet
    have hk' : BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k :=
      (ofNat64_pred (by omega) (by omega)).trans (by rw [Nat.add_sub_cancel])
    have h1 : BitVec.signExtend 64 1#32 = (1 : BitVec 64) := by decide
    have hz : (BitVec.ofNat 64 k == 0#64) = decide (k = 0) := ofNat64_beq_zero (by omega)
    have hb := (t.mem (P + BitVec.ofNat 64 j)).isLt
    xrun [State.ea, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hp, hk, hv, hacc, hr, h1,
      shl8_add v hv32, low32, shr32 (show 256 * v + (t.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 64 by omega)]
    have e1 : (1#64 : BitVec 64) = 1 := rfl
    refine ⟨?_, ?_, ?_⟩ <;> simp only [e1, hk', hz, BitVec.add_assoc, ofNat_add_one]
  · rfl

theorem os2ip_snoc (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · intro h; rw [h]; rfl

/-- After `j` of `e`'s octets: its value so far modulo `2^32` in r9, and in
r10 whether it is below `2^32`. -/
def ScanInv (s : State) (P : Addr) (len j : Nat) (u : State) : Prop :=
  u.gpr .rdx = P + BitVec.ofNat 64 j ∧ u.gpr .rcx = BitVec.ofNat 64 (len - j) ∧
    u.gpr .r9 = BitVec.ofNat 64 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) ∧
    (u.gpr .r10 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) < 2 ^ 32) ∧ u.mem = s.mem ∧
    Keep [.rax, .r9, .r10, .rdx, .rcx] s u

theorem scan_setup {s : State} {len : Nat} (hl : s.gpr .rcx = BitVec.ofNat 64 len) (hl64 : len < 2 ^ 64) :
    WP isa (.block [.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)]) s fun t =>
      (t.gpr .r9 = 0 ∧ t.gpr .r10 = 0 ∧ eval .e t = some (decide (len = 0)) ∧ t.mem = s.mem ∧
        t.gpr .rcx = s.gpr .rcx) ∧ Keep [.r9, .r10, .rcx] s t := by
  refine WP.keep [.r9, .r10, .rcx] ?_ rfl
  xrun [hl, eval, BitVec.and_self, ofNat64_beq_zero hl64]

theorem scan_ok {s : State} {P : Addr} {len : Nat} (hp : s.gpr .rdx = P)
    (hl : s.gpr .rcx = BitVec.ofNat 64 len) (hl64 : len < 2 ^ 64)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) :
    WP isa scan s (ScanInv s P len len) := by
  unfold scan
  refine WP.seq (WP.mono (scan_setup hl hl64) fun t ⟨⟨h9, h10, he, hm, hcx⟩, k⟩ => ?_)
  have h0 : ScanInv s P len 0 t := ⟨by rw [k.gpr (by decide), hp, BitVec.add_zero],
    by rw [hcx, hl, Nat.sub_zero], by rw [h9]; rfl,
    by rw [h10]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], hm, k.mono (by decide)⟩
  refine WP.ite (decide (len = 0)) he (fun hz => ?_) (fun hz => ?_)
  · have hz : len = 0 := of_decide_eq_true hz
    subst hz
    exact WP.block_nil h0
  · have hz : len ≠ 0 := of_decide_eq_false hz
    refine wp_upto (a := 0) (N := len) (by omega) (ScanInv s P len) ?_ (fun _ h => h) h0
    intro j _ hj u ⟨hdx, hcx, hr9, hr10, hum, ku⟩
    have hr : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 j) 1 := by
      rw [ku.2.1, ku.2.2]; exact hrd j hj
    have hk1 : len - j = (len - j - 1) + 1 := by omega
    rw [hk1] at hcx
    refine WP.mono (octet_ok hdx hcx hr9 rfl (by omega) (Nat.mod_lt _ (by decide)) hr)
      fun v ⟨⟨hz, hd, hc, h9', h10', hm'⟩, kv⟩ => ⟨?_, hd, ?_, ?_, ?_, hm'.trans hum,
        (ku.trans kv).mono (by decide)⟩
    · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
    · rw [hc, show len - j - 1 = len - (j + 1) by omega]
    · rw [h9', SearchInit.bytesAt_succ, os2ip_snoc, hum]
      congr 1
      omega
    · have := (s.mem (P + BitVec.ofNat 64 j)).isLt
      have := Nat.mod_lt (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j)) (show 0 < 2 ^ 32 by decide)
      rw [h10', SearchInit.or_eq_zero, hr10, SearchInit.bytesAt_succ, os2ip_snoc, hum,
        ofNat64_eq_zero (by omega)]
      constructor
      · rintro ⟨h1, h2⟩
        have : 256 * (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P j) % 2 ^ 32) +
          (s.mem (P + BitVec.ofNat 64 j)).toNat < 2 ^ 32 := by
          rcases Nat.eq_zero_or_pos (2 ^ 32) with h | h
          · omega
          · exact (Nat.div_eq_zero_iff_lt h).mp h2
        omega
      · intro h
        refine ⟨by omega, ?_⟩
        apply Nat.div_eq_of_lt
        omega

/-! ## Comparisons and conditional moves -/

theorem sub_beq_zero {x k : Nat} (hx : x < 2 ^ 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k == 0) = decide (x = k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hk, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega
  · intro h; subst h; exact BitVec.sub_self _

/-- `cmp r, k` then `cmov cc d, q`, for `cc` below, above or equal. -/
theorem cmp_cmov {s : State} (r : Reg) (c : BitVec 32) (cc : Cond) (d q : Reg) {x k : Nat}
    (hr : s.gpr r = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) (hk : BitVec.signExtend 64 c = BitVec.ofNat 64 k)
    (hk64 : k < 2 ^ 64) (hrd : r ≠ d) (hcc : cc ≠ .ne) :
    WP isa (.block [.alu .cmp r (.imm c), .cmov cc d (.reg q)]) s fun t =>
      (t.gpr d = (if (match cc with | .b => decide (x < k) | .ae => decide (k ≤ x) | _ => decide (x = k))
          then s.gpr q else s.gpr d) ∧ t.mem = s.mem ∧ t.gpr r = s.gpr r) ∧
        Keep [d, r] s t := by
  refine WP.keep [d, r] ?_ (by cases r <;> cases d <;> rfl)
  have hdr : d ≠ r := Ne.symm hrd
  cases cc with
  | ne => exact absurd rfl hcc
  | b =>
    xrun [hr, hk, eval, execCmov]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hk64]
    by_cases h : x < k <;> simp [h, State.setReg, State.setFlags, hrd, hr]
  | ae =>
    xrun [hr, hk, eval, execCmov]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hk64]
    by_cases h : k ≤ x <;> simp [h, show ¬ x < k ↔ k ≤ x from Nat.not_lt, State.setReg, State.setFlags, hrd,
      hr] <;> omega
  | e =>
    xrun [hr, hk, eval, execCmov, sub_beq_zero hx hk64]
    by_cases h : x = k <;> simp [h, State.setReg, State.setFlags, hrd, hr]

/-- `test r, r` then `cmov.ne d, q`. -/
theorem test_cmov_ne {s : State} (r d q : Reg) (hrd : r ≠ d) :
    WP isa (.block [.alu .test r (.reg r), .cmov .ne d (.reg q)]) s fun t =>
      (t.gpr d = (if s.gpr r = 0 then s.gpr d else s.gpr q) ∧ t.mem = s.mem ∧ t.gpr r = s.gpr r) ∧
        Keep [d, r] s t := by
  refine WP.keep [d, r] ?_ (by cases r <;> cases d <;> rfl)
  xrun [eval, execCmov, BitVec.and_self]
  by_cases h : s.gpr r = 0#64
  · simp [h, State.setFlags]
  · simp [h, State.setReg, State.setFlags, hrd]

/-- `mov r11, r9; and r11, 1; cmov.e rax, r8`: whether r9 is even. -/
theorem even_cmov {s : State} {x : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 x) (hx : x < 2 ^ 64) :
    WP isa (.block [.mov .r11 (.reg .r9), .alu .and .r11 (.imm 1), .cmov .e .rax (.reg .r8)]) s fun t =>
      (t.gpr .rax = (if x % 2 = 0 then s.gpr .r8 else s.gpr .rax) ∧ t.mem = s.mem) ∧
        Keep [.rax, .r11] s t := by
  refine WP.keep [.rax, .r11] ?_ rfl
  have h1 : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
    omega
  have hs1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := by decide
  xrun [h9, eval, execCmov, hs1, h1, ofNat64_beq_zero (show x % 2 < 2 ^ 64 by omega)]
  by_cases h : x % 2 = 0 <;> simp [h, State.setReg, State.setFlags]

/-! ## The status -/

/-- The status `vg_rsa_generate_init` returns, of the size and `e`'s value. -/
def initStatus (bits e : Nat) : Nat :=
  if !Spec.RsaKeyGen.exponentValid e then 0
  else if Spec.RsaKeyGen.modulusBits bits = none then 2 else 1

theorem status_split : status =
    ([.mov32 .rax (.imm 1), .mov32 .r8 (.imm 2)] : List Instr) ++
      (([.alu .cmp .rsi (.imm 512), .cmov .b .rax (.reg .r8)] : List Instr) ++
      (([.alu .cmp .rsi (.imm 8193), .cmov .ae .rax (.reg .r8)] : List Instr) ++
        (([.mov32 .r8 (.imm 0)] : List Instr) ++
        (([.alu .test .r10 (.reg .r10), .cmov .ne .rax (.reg .r8)] : List Instr) ++
          (([.mov .r11 (.reg .r9), .alu .and .r11 (.imm 1), .cmov .e .rax (.reg .r8)] : List Instr) ++
            ([.alu .cmp .r9 (.imm 1), .cmov .e .rax (.reg .r8)] : List Instr)))))) := rfl

theorem initStatus_val (bits E : Nat) :
    initStatus bits E = if E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 then
      (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 2) else 0 := by
  unfold initStatus Spec.RsaKeyGen.exponentValid Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits
    Spec.RsaKeyGen.minBits
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | simp_all | omega

theorem initStatus_eq (bits E : Nat) :
    (if E % 2 ^ 32 = 1 then (0 : BitVec 64) else if E % 2 ^ 32 % 2 = 0 then 0 else
      if E < 2 ^ 32 then (if 8193 ≤ bits then 2 else if bits < 512 then 2 else 1) else 0) =
      BitVec.ofNat 64 (initStatus bits E) := by
  rw [initStatus_val]
  repeat' split
  all_goals first | rfl | (exfalso; omega)

theorem status_ok {s : State} {bits E : Nat} (hsi : s.gpr .rsi = BitVec.ofNat 64 bits)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (E % 2 ^ 32)) (h10 : s.gpr .r10 = 0 ↔ E < 2 ^ 32) (hb : bits < 2 ^ 64) :
    WP isa (.block status) s fun t => (t.gpr .rax = BitVec.ofNat 64 (initStatus bits E) ∧
      t.gpr .rsi = s.gpr .rsi ∧ t.gpr .r9 = s.gpr .r9 ∧ t.mem = s.mem) ∧
      Keep [.rax, .r8, .r11, .rsi, .r9, .r10] s t := by
  have hV : E % 2 ^ 32 < 2 ^ 64 := by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega
  rw [status_split, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.gpr .rax = 1 ∧ t.gpr .r8 = 2 ∧ t.mem = s.mem)
    (by xrun) rfl) fun t1 ⟨⟨a1, r1, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  have si1 : t1.gpr .rsi = BitVec.ofNat 64 bits := (k1.gpr (by decide)).trans hsi
  refine WP.mono (cmp_cmov .rsi 512 .b .rax .r8 (k := 512) si1 hb (by decide) (by decide) (by decide) (by decide))
    fun t2 ⟨⟨a2, m2, si2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp_cmov .rsi 8193 .ae .rax .r8 (k := 8193) (si2.trans si1) hb (by decide) (by decide) (by decide)
    (by decide)) fun t3 ⟨⟨a3, m3, si3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = 0 ∧ t.mem = t3.mem) (by xrun) rfl)
    fun t4 ⟨⟨r4, m4⟩, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (test_cmov_ne .r10 .rax .r8 (by decide)) fun t5 ⟨⟨a5, m5, x5⟩, k5⟩ => ?_
  rw [WP.block_append_iff]
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have h9' : t5.gpr .r9 = BitVec.ofNat 64 (E % 2 ^ 32) := (k15.gpr (by decide)).trans h9
  refine WP.mono (even_cmov h9' hV) fun t6 ⟨⟨a6, m6⟩, k6⟩ => ?_
  have h9'' : t6.gpr .r9 = BitVec.ofNat 64 (E % 2 ^ 32) := (k6.gpr (by decide)).trans h9'
  refine WP.mono (cmp_cmov .r9 1 .e .rax .r8 (k := 1) h9'' hV (by decide) (by decide) (by decide) (by decide))
    fun t ⟨⟨a7, m7, x7⟩, k7⟩ => ?_
  have k := (k15.trans k6).trans k7
  refine ⟨⟨?_, ?_, ?_, ?_⟩, k.mono (by decide)⟩
  · have r8a : t6.gpr .r8 = 0 := by rw [k6.gpr (by decide), k5.gpr (by decide), r4]
    have r8b : t5.gpr .r8 = 0 := by rw [k5.gpr (by decide), r4]
    have z4 : t4.gpr .r10 = s.gpr .r10 := by
      rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]
    have r82 : t2.gpr .r8 = 2 := by rw [k2.gpr (by decide), r1]
    have ax4 : t4.gpr .rax = t3.gpr .rax := k4.gpr (by decide)
    rw [a7, a6, a5, r8a, r8b, ax4, a3, a2, a1, r82, r1, z4, ← initStatus_eq bits E]
    simp only [decide_eq_true_eq]
    by_cases hz : s.gpr .r10 = 0
    · simp only [hz, ↓reduceIte, h10.mp hz]
    · simp only [hz, ↓reduceIte, show ¬ E < 2 ^ 32 from fun h => hz (h10.mpr h), r4]
  · rw [k7.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), si3, si2,
      k1.gpr (by decide)]
  · rw [x7, k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide),
      k2.gpr (by decide), k1.gpr (by decide)]
  · rw [m7, m6, m5, m4, m3, m2, m1]

/-! ## The words -/

/-- The seven words stored, from their values. -/
def stored (m : Mem) (B : Addr) (w : List (BitVec 64)) : Mem :=
  ((((((m.writeW B (w.getD 0 0)).writeW (off B 8) (w.getD 1 0)).writeW (off B 16) (w.getD 2 0)).writeW
    (off B 24) (w.getD 3 0)).writeW (off B 32) (w.getD 4 0)).writeW (off B 40) (w.getD 5 0)).writeW
    (off B 48) (w.getD 6 0)

/-- The primes' octets, from the size. -/
abbrev plenBV (bits : Nat) : BitVec 64 := (BitVec.ofNat 64 bits >>> 7) <<< 3

/-- The words' values, if the status is 1. -/
def wordValues (bits V : Nat) : List (BitVec 64) :=
  let P := plenBV bits
  [if V = 3 then P <<< 6 else (P <<< 3) <<< 2 + P <<< 3, P, (P <<< 15) + P, P <<< 5, 0, 4,
    bswap64 (BitVec.ofNat 64 V)]

theorem words_ok {s : State} {B : Addr} {bits V st : Nat} (scr : Scr s B 56) (hdi : s.gpr .rdi = B)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 bits) (h9 : s.gpr .r9 = BitVec.ofNat 64 V)
    (hax : s.gpr .rax = BitVec.ofNat 64 st) (hV : V < 2 ^ 64) (hst : st < 2 ^ 64) :
    WP isa (.block words) s fun t => (t.gpr .rax = s.gpr .rax ∧
      t.mem = stored s.mem B (if st = 1 then wordValues bits V else List.replicate 7 0)) ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] s t := by
  refine WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] ?_ rfl
  have hstore : ∀ j < 7, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  unfold words compute Impl.RsaKeyGen.X86_64.KeyInit.mask stores stored wordValues
  simp only [List.cons_append, List.nil_append]
  have e3 : (BitVec.ofNat 64 V - 3 == 0) = decide (V = 3) := sub_beq_zero hV (k := 3) (by decide)
  have e1 : (BitVec.ofNat 64 st - 1 == 0) = decide (st = 1) := sub_beq_zero hst (k := 1) (by decide)
  have z0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := rfl
  by_cases h3 : V = 3 <;> by_cases h1 : st = 1 <;>
  xrun [field, State.ea, off, BitVec.ofInt_natCast, eval, execCmov, hdi, hsi, h9, hax, e3, e1, h3, h1, z0,
    hstore 0 (by decide), hstore 1 (by decide), hstore 2 (by decide), hstore 3 (by decide),
    hstore 4 (by decide), hstore 5 (by decide), hstore 6 (by decide)] <;>
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMul, BitVec.add_zero,
    List.replicate_succ, List.replicate_zero] <;>
  rfl

/-! ## The state's words and the exponent's octets -/

open VG.Proof.Ffdh.Control (controller_store_word)

theorem stored_eq (m : Mem) (B : Addr) (w : List (BitVec 64)) : stored m B w =
    ((((((m.writeW (off B (8 * 0)) (w.getD 0 0)).writeW (off B (8 * 1)) (w.getD 1 0)).writeW (off B (8 * 2))
      (w.getD 2 0)).writeW (off B (8 * 3)) (w.getD 3 0)).writeW (off B (8 * 4)) (w.getD 4 0)).writeW
      (off B (8 * 5)) (w.getD 5 0)).writeW (off B (8 * 6)) (w.getD 6 0) := by
  simp only [stored, off, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul]

theorem stored_word (m : Mem) (B : Addr) (w : List (BitVec 64)) {j : Nat} (hj : j < 7) :
    word (stored m B w) B (8 * j) = w.getD j 0 := by
  rw [stored_eq]
  simp only [controller_store_word _ _ _ (show 6 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 5 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 4 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 3 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 2 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 1 < 16 by decide) (show j < 16 by omega),
    controller_store_word _ _ _ (show 0 < 16 by decide) (show j < 16 by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    h | h | h | h | h | h | h <;> subst h <;> rfl

theorem stored_words6 (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.wordsAt (stored m B w) B 6 = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0,
      w.getD 5 0] := by
  change [word (stored m B w) B (8 * 0), word (stored m B w) B (8 * 1), word (stored m B w) B (8 * 2),
    word (stored m B w) B (8 * 3), word (stored m B w) B (8 * 4), word (stored m B w) B (8 * 5)] = _
  rw [stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide)]

theorem stored_words7 (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.wordsAt (stored m B w) B 7 = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0,
      w.getD 5 0, w.getD 6 0] := by
  change [word (stored m B w) B (8 * 0), word (stored m B w) B (8 * 1), word (stored m B w) B (8 * 2),
    word (stored m B w) B (8 * 3), word (stored m B w) B (8 * 4), word (stored m B w) B (8 * 5),
    word (stored m B w) B (8 * 6)] = _
  rw [stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide), stored_word _ _ _ (by decide), stored_word _ _ _ (by decide),
    stored_word _ _ _ (by decide)]

/-- The octets of the last word stored. -/
theorem stored_bytes (m : Mem) (B : Addr) (w : List (BitVec 64)) :
    Spec.Rsa.bytesAt (stored m B w) (B + 48) 8 =
      (List.range 8).map fun i => (w.getD 6 0).extractLsb' (8 * i) 8 := by
  simp only [Spec.Rsa.bytesAt, stored]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [Mem.writeW, Mem.write]
  have hx : (B + 48 + BitVec.ofNat 64 i - (B + 48)).toNat = i := by
    rw [BitVec.add_comm (B + 48), BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h48 : off B 48 = B + 48 := rfl
  rw [h48, hx, ite_eq_left (by omega)]
  simp only [BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

theorem bswap_bytes (E : Nat) :
    ((List.range 8).map fun i => (bswap64 (BitVec.ofNat 64 E)).extractLsb' (8 * i) 8) = Spec.Rsa.i2osp E 8 := by
  simp only [Spec.Rsa.i2osp]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [Proof.Bignum.X86_64.WordIO.bswap_byte _ hi, Proof.Bignum.X86_64.WordIO.extract_nat _ (by omega)]

/-! ## The result -/

open VG.Proof.RsaKeyGen.SearchInit (shl_ofNat add_ofNat)

def initPre (s : State) : Prop :=
  s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧ s.wr = [⟨s.gpr .rdi, 56⟩] ∧
    (s.gpr .rdi).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 56⟩

def initPost (s t : State) : Prop :=
  let eB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  match Spec.RsaKeyGen.keySearchInit (s.gpr .rsi).toNat eB with
  | .error c => ((t.gpr .rax).setWidth 32).toNat = c ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 7 = List.replicate 7 0
  | .ok values => ((t.gpr .rax).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 6 =
        (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .rdi + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip eB) 8 ∧
      Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first

theorem plen_eq {bits : Nat} (hb : bits < 2 ^ 64) : plenBV bits = BitVec.ofNat 64 (bits / 128 * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem setWidth32_toNat {n : Nat} (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem result_post {s t : State} {E : Nat}
    (hE : E = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (hax : t.gpr .rax = BitVec.ofNat 64 (initStatus (s.gpr .rsi).toNat E))
    (hm : t.mem = stored s.mem (s.gpr .rdi) (if initStatus (s.gpr .rsi).toNat E = 1 then
      wordValues (s.gpr .rsi).toNat (E % 2 ^ 32) else List.replicate 7 0)) :
    initPost s t := by
  unfold initPost Spec.RsaKeyGen.keySearchInit
  dsimp only
  subst hE
  generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) = E at *
  generalize hbits : (s.gpr .rsi).toNat = bits at hax hm ⊢
  have hb : bits < 2 ^ 64 := by rw [← hbits]; exact BitVec.isLt _
  have hst := initStatus_val bits E
  by_cases hv : Spec.RsaKeyGen.exponentValid E = true
  · rw [ite_eq_right (by rw [hv]; decide)]
    have hvE : E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 := by
      unfold Spec.RsaKeyGen.exponentValid at hv
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      omega
    cases hmb : Spec.RsaKeyGen.modulusBits bits with
    | none =>
      have h2 : initStatus bits E = 2 := by
        unfold initStatus; rw [hv, hmb]; rfl
      refine ⟨by rw [hax, h2]; rfl, ?_⟩
      rw [hm, h2, ite_eq_right (by decide), stored_words7]
      rfl
    | some nlen =>
      have hn : 512 ≤ bits ∧ bits ≤ 8192 ∧ nlen = bits / 128 * 128 := by
        unfold Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits Spec.RsaKeyGen.minBits at hmb
        by_cases h1 : 8192 < bits
        · simp [h1] at hmb
        · by_cases h2 : bits / 128 * 128 < 512
          · simp [h1, h2] at hmb
          · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hmb
            omega
      have h1 : initStatus bits E = 1 := by
        rw [hst, ite_eq_left hvE, ite_eq_left (by omega)]
      have hP : nlen / 16 = bits / 128 * 8 := by omega
      have hL : bits / 128 * 8 ≤ 512 := by omega
      have hL32 : 32 ≤ bits / 128 * 8 := by omega
      refine ⟨by rw [hax, h1]; rfl, 32 * (bits / 128 * 8), ?_, ?_, ?_⟩
      · rw [hm, h1, ite_eq_left rfl, stored_words6]
        simp only [wordValues, plen_eq hb, Nat.mod_eq_of_lt hvE.2.2, List.getD_cons_zero, List.getD_cons_succ,
          hP, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Spec.RsaKeyGen.keyGenerations,
          Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeEntropy]
        rw [shl_ofNat _ 6 (by omega), shl_ofNat _ 15 (by omega), shl_ofNat _ 5 (by omega),
          shl_ofNat _ 3 (by omega), shl_ofNat _ 2 (by omega), add_ofNat, add_ofNat]
        by_cases h3 : E = 3 <;> simp only [h3, ↓reduceIte, List.cons.injEq, and_true] <;> and_intros <;>
          first | rfl | trivial | (congr 1; omega)
      · rw [hm, h1, ite_eq_left rfl, stored_bytes]
        simp only [wordValues, List.getD_cons_zero, List.getD_cons_succ, Nat.mod_eq_of_lt hvE.2.2]
        exact bswap_bytes E
      · simp only [List.getD_cons_zero, List.getD_cons_succ, hP]
        unfold Spec.Entropy.RequestValid Spec.RsaKeyGen.primeEntropy
        omega
  · have hv' : Spec.RsaKeyGen.exponentValid E = false := by simpa using hv
    rw [ite_eq_left (by rw [hv']; rfl)]
    have h0 : initStatus bits E = 0 := by
      unfold initStatus; rw [ite_eq_left (by rw [hv']; rfl)]
    refine ⟨by rw [hax, h0]; rfl, ?_⟩
    rw [hm, h0, ite_eq_right (by decide), stored_words7]
    rfl

/-! ## The whole initialization -/

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem init_ok {s : State} (scr : Scr s (s.gpr .rdi) 56)
    (hrd : ∀ i < (s.gpr .rcx).toNat, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) 1) :
    WP isa init s fun t => initPost s t ∧ Keep [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] s t := by
  let E := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  unfold init
  refine WP.seq (WP.mono (scan_ok rfl (ofNat_toNat64 _).symm (BitVec.isLt _) hrd)
    fun u ⟨_, _, h9, h10, hmu, ku⟩ => ?_)
  rw [WP.block_append_iff]
  have hsu : u.gpr .rsi = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [ku.gpr (by decide)]; exact (ofNat_toNat64 _).symm
  refine WP.mono (status_ok (E := E) hsu h9 h10 (BitVec.isLt _)) fun v ⟨⟨hav, hsv, h9v, hmv⟩, kv⟩ => ?_
  have hdv : v.gpr .rdi = s.gpr .rdi := by rw [kv.gpr (by decide), ku.gpr (by decide)]
  have scv : Scr v (s.gpr .rdi) 56 := (scr.congr ku.2.2).congr kv.2.2
  have hst : initStatus (s.gpr .rsi).toNat E < 2 ^ 64 := by
    rw [initStatus_val]; split <;> (try split) <;> omega
  refine WP.mono (words_ok scv hdv (hsv.trans hsu) (h9v.trans h9) hav
    (by have := Nat.mod_lt E (show 0 < 2 ^ 32 by decide); omega) hst) fun t ⟨⟨hat, hmt⟩, kt⟩ => ?_
  exact ⟨result_post rfl (hat.trans hav) (by rw [hmt, hmv, hmu]), ((ku.trans kv).trans kt).mono (by decide)⟩

/-! ## The contract -/

def initPub (s t : State) : Prop :=
  s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨hrd, hwr, hroom, hroome, hret⟩ := h
  have scr : Scr s (s.gpr .rdi) 56 := Scr.of_mem (by rw [hwr]; simp) hroom
  have hreads : ∀ i < (s.gpr .rcx).toNat, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  obtain ⟨tr, t, he, hp, k⟩ := init_ok scr hreads
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
  refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ⟨?_, hr⟩, hp⟩
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
    | .rdi => 0x1000 | .rsi => 1024 | .rdx => 0x2000 | .rcx => 3 | .rsp => 0x3000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 56⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.RsaKeyGen.X86_64.KeyInit
