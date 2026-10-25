module

import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBlocks
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
public import VerifiedGarbage.Proof.RsaPss.X86_64.Basic

/-!
# RSASSA-PSS verification on x86-64: the padding of a salt of known length

With the salt's length `sl < db` given, `DB`'s padding must end at
`p = db - sl - 1`: `prefixCheck` ORs into `acc` the first `p` bytes of `DB`,
a word at a time (`prefixWords`) and then a byte at a time (`prefixBytes`),
and `DB[p] ⊕ 0x01`, so that `acc` stays zero exactly when they are zero and
`DB[p]` is `0x01` (`prefixCheck_ok`); it leaves `pos` and `ℓ` in their slots
as `posCheck` would.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (ofNat_sub_beq wp_upto)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- The `n` bytes of `V` from `e` are zero. -/
def ZeroUpTo (V : Nat → Byte) (e n : Nat) : Prop := ∀ i < n, V (e + i) = 0

theorem zeroUpTo_succ (V : Nat → Byte) (e n : Nat) :
    ZeroUpTo V e (n + 1) ↔ ZeroUpTo V e n ∧ V (e + n) = 0 := by
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega_arith), h n (by omega_arith)⟩
  · intro ⟨h, h'⟩ i hi
    by_cases hl : i < n
    · exact h i hl
    · rwa [show i = n by omega_arith]

theorem zeroUpTo_add8 (V : Nat → Byte) (e n : Nat) :
    ZeroUpTo V e (n + 8) ↔ ZeroUpTo V e n ∧ ∀ i < 8, V (e + n + i) = 0 := by
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega_arith), fun i hi => by rw [Nat.add_assoc]; exact h _ (by omega_arith)⟩
  · intro ⟨h, h'⟩ i hi
    by_cases hl : i < n
    · exact h i hl
    · have := h' (i - n) (by omega_arith); rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega_arith)] at this

theorem readW64_eq_zero (m : Mem) (a : Addr) :
    m.readW a 64 = 0 ↔ ∀ i < 8, m (a + BitVec.ofNat 64 i) = 0 := by
  have e : (m.readW a 64).toNat = (m.read a 8).toNat := by
    simp only [Mem.readW, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (m.read a 8).isLt
  constructor
  · intro h i hi
    have h' : m.read a 8 = 0#64 := BitVec.eq_of_toNat_eq (by rw [← e, h]; rfl)
    rw [← Mem.extractLsb'_read m a hi, h']
    exact BitVec.eq_of_toNat_eq (by simp)
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, Mem.read_eq_of_bytes (v := 0#64) fun i hi => by
      rw [h i hi]; exact BitVec.eq_of_toNat_eq (by simp)]
    rfl

theorem shl_ofNat {x : Nat} (k : Nat) (hx : x * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hx' : x < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) hx
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx', Nat.shiftLeft_eq]

/-- `prefixCheck`'s first block. -/
def pfxHead : List Instr :=
  [.mov .rdi (.mem (sp sEb)), .mov .rsi (.mem (sp sDb)), .mov .rdx (.mem (sp sSlen)), .alu .sub .rsi (.reg .rdx),
    .alu .sub .rsi (.imm 1), .mov .rcx (.reg .rsi), .shift .shr .rcx 3, .shift .shl .rcx 3, .mov .rax (.mem (sp sAcc)),
    .mov32 .r8 (.imm 0), .alu .test .rcx (.reg .rcx)]

theorem pfxHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db sl : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hs : sl < db) (hdb2 : db ≤ 1024) :
    WP isa (.block pfxHead) u fun u' => Keep [.rdi, .rsi, .rdx, .rcx, .rax, .r8] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .rdi = off S e ∧ u'.gpr .rsi = BitVec.ofNat 64 (db - sl - 1) ∧
      u'.gpr .rcx = BitVec.ofNat 64 (8 * ((db - sl - 1) / 8)) ∧ u'.gpr .rax = W 33 ∧
      u'.gpr .r8 = BitVec.ofNat 64 0 ∧ u'.zf = some (decide (8 * ((db - sl - 1) / 8) = 0)) := by
  have hsub : BitVec.ofNat 64 db - BitVec.ofNat 64 sl - 1 = BitVec.ofNat 64 (db - sl - 1) := by
    rw [VG.Offset.ofNat_sub_ofNat (show sl ≤ db by omega_arith), show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (show 1 ≤ db - sl by omega_arith)]
  have hsh : BitVec.ofNat 64 (db - sl - 1) >>> 3 <<< 3 = BitVec.ofNat 64 (8 * ((db - sl - 1) / 8)) := by
    rw [shr_ofNat 3 (by omega_arith), shl_ofNat 3 (by omega_arith), Nat.mul_comm]
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .rax, .r8] (Q := fun u' => u'.mem = u.mem ∧
      u'.gpr .rdi = off S e ∧ u'.gpr .rsi = BitVec.ofNat 64 (db - sl - 1) ∧
      u'.gpr .rcx = BitVec.ofNat 64 (8 * ((db - sl - 1) / 8)) ∧ u'.gpr .rax = W 33 ∧
      u'.gpr .r8 = BitVec.ofNat 64 0 ∧ u'.zf = some (decide (8 * ((db - sl - 1) / 8) = 0))) ?_ rfl)
    fun u' ⟨h, k⟩ => ⟨k, h⟩
  xrun [pfxHead, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide), L.ld (d := sSlen) (by decide),
    L.ld (d := sAcc) (by decide), R.rd (d := sEb) 23 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
    R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sAcc) 33 rfl (by decide), he, hdb, hsl, hsub, hsh]
  rw [BitVec.and_self]
  have hlt : 8 * ((db - sl - 1) / 8) < 2 ^ 64 := by omega_arith
  by_cases h0 : 8 * ((db - sl - 1) / 8) = 0
  · rw [h0]; rfl
  · rw [decide_eq_false h0, beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
    exact h0 this

theorem pfxWords_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e n : Nat} {a : BitVec 64} (hn : 0 < n) (hfit : e + 8 * n ≤ oRsa)
    (hdi : u.gpr .rdi = off S e) (hcx : u.gpr .rcx = BitVec.ofNat 64 (8 * n))
    (h8 : u.gpr .r8 = BitVec.ofNat 64 0) (hax : u.gpr .rax = a) :
    WP isa prefixWords u fun u' => Keep [.rax, .r8] u u' ∧ u'.mem = u.mem ∧
      u'.gpr .r8 = BitVec.ofNat 64 (8 * n) ∧ (u'.gpr .rax = 0 ↔ a = 0 ∧ ZeroUpTo V e (8 * n)) := by
  have c5 : oRsa = 8192 := rfl
  refine wp_upto (a := 0) (N := n) hn (fun j v => Keep [.rax, .r8] u v ∧ v.mem = u.mem ∧
      v.gpr .r8 = BitVec.ofNat 64 (8 * j) ∧ (v.gpr .rax = 0 ↔ a = 0 ∧ ZeroUpTo V e (8 * j)))
    (fun j _ hj v ⟨k, hm, hv8, hva⟩ => ?_) (fun v h => h)
    ⟨Keep.refl _ _, rfl, h8, by rw [hax]; exact ⟨fun h => ⟨h, fun i hi => absurd hi (by omega_arith)⟩, fun h => h.1⟩⟩
  have Lv := L.congr (k.gpr (by decide)) k.2.2 (by rw [hm])
  have hdv : v.gpr .rdi = off S e := (k.gpr (by decide)).trans hdi
  have hcv : v.gpr .rcx = BitVec.ofNat 64 (8 * n) := (k.gpr (by decide)).trans hcx
  have hea : v.gpr .rdi + v.gpr .r8 = off S (e + 8 * j) := by rw [hdv, hv8, off_plus]
  have hld := Lv.sld (d := e + 8 * j) (by omega_arith)
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun v' => v'.zf = some (decide (j + 1 = n)) ∧ v'.mem = v.mem ∧
      v'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧
      v'.gpr .rax = v.gpr .rax ||| v.mem.readW (off S (e + 8 * j)) 64) ?_ rfl)
    fun v' ⟨⟨hz, hm', h8', hax'⟩, k'⟩ => ⟨hz, (k.trans k').mono (by decide), hm'.trans hm, h8', ?_⟩
  · xrun [prefixWords, ea_ix0, hdv, hv8, off_plus, hld, hcv, VG.Proof.MlKem.X86_64.sx_ofNat (show 8 < 2 ^ 31 by decide),
      ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega_arith) (show 8 * n < 2 ^ 64 by omega_arith)]
    have hadd : BitVec.ofNat 64 (8 * j) + 8 = BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [Nat.mul_succ, BitVec.ofNat_add]; rfl
    rw [hadd, ofNat_sub_beq (show 8 * (j + 1) < 2 ^ 64 by omega_arith) (show 8 * n < 2 ^ 64 by omega_arith)]
    exact ⟨by simp only [decide_eq_decide]; omega_arith, rfl⟩
  · rw [hax', or_eq_zero64, hva, readW64_eq_zero, show 8 * (j + 1) = 8 * j + 8 by omega_arith, zeroUpTo_add8, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [hm, off_plus, R.scr _ (by omega_arith)]

theorem pfxBytes_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e m n : Nat} {a : BitVec 64} (hmn : m < n) (hfit : e + n ≤ oRsa)
    (hdi : u.gpr .rdi = off S e) (hsi : u.gpr .rsi = BitVec.ofNat 64 n)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 m) (hax : u.gpr .rax = 0 ↔ a = 0 ∧ ZeroUpTo V e m) :
    WP isa prefixBytes u fun u' => Keep [.rax, .r8, .rdx] u u' ∧ u'.mem = u.mem ∧
      (u'.gpr .rax = 0 ↔ a = 0 ∧ ZeroUpTo V e n) := by
  have c5 : oRsa = 8192 := rfl
  refine wp_upto (a := m) (N := n) hmn (fun j v => Keep [.rax, .r8, .rdx] u v ∧ v.mem = u.mem ∧
      v.gpr .r8 = BitVec.ofNat 64 j ∧ (v.gpr .rax = 0 ↔ a = 0 ∧ ZeroUpTo V e j))
    (fun j _ hj v ⟨k, hm, hv8, hva⟩ => ?_) (fun v ⟨k, hm, _, h⟩ => ⟨k, hm, h⟩) ⟨Keep.refl _ _, rfl, h8, hax⟩
  have Lv := L.congr (k.gpr (by decide)) k.2.2 (by rw [hm])
  have hdv : v.gpr .rdi = off S e := (k.gpr (by decide)).trans hdi
  have hsv : v.gpr .rsi = BitVec.ofNat 64 n := (k.gpr (by decide)).trans hsi
  have hea : v.gpr .rdi + v.gpr .r8 = off S (e + j) := by rw [hdv, hv8, off_plus]
  have hld := Lv.sld8 (d := e + j) (by omega_arith)
  have hval : v.mem (off S (e + j)) = V (e + j) := by rw [hm]; exact R.scr _ (by omega_arith)
  refine WP.mono (WP.keep [.rax, .r8, .rdx] (Q := fun v' => v'.zf = some (decide (j + 1 = n)) ∧ v'.mem = v.mem ∧
      v'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧
      v'.gpr .rax = v.gpr .rax ||| BitVec.setWidth 64 (V (e + j))) ?_ rfl)
    fun v' ⟨⟨hz, hm', h8', hax'⟩, k'⟩ => ⟨hz, (k.trans k').mono (by decide), hm'.trans hm, h8', ?_⟩
  · xrun [prefixBytes, ea_ix0, hdv, hv8, off_plus, hld, hval, hsv, ofNat_add_lit,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show n < 2 ^ 64 by omega_arith)]
  · rw [hax', or_eq_zero64, hva, zext_eq_zero, zeroUpTo_succ, and_assoc]

/-- `lz` from its characterization below the length. -/
theorem lz_eq_of {l : List Byte} {n : Nat} (hz : ∀ j < n, l.getD j 0 = 0) (hn : n < l.length)
    (hne : l.getD n 0 ≠ 0) : lz l = n := by
  rcases Nat.lt_trichotomy (lz l) n with h | h | h
  · exact absurd (hz _ h) (getD_lz_ne (by omega_arith))
  · exact h
  · exact absurd (getD_lt_lz h) hne

/-- With the salt's length `sl < L` given: the padding of `DB` ends at
`L - sl - 1` exactly when its first nonzero byte is a `0x01` there. -/
theorem fixed_cond (dbL : List Byte) {L sl : Nat} (hlen : dbL.length = L) (hs : sl < L) :
    ((∀ i < L - sl - 1, dbL.getD i 0 = 0) ∧ dbL.getD (L - sl - 1) 0 = 1) ↔
      (lz dbL < L ∧ dbL.getD (lz dbL) 0 = 1 ∧ L - lz dbL - 1 = sl) := by
  constructor
  · intro ⟨hz, h1⟩
    have hl := lz_eq_of hz (by omega_arith) (by rw [h1]; decide)
    rw [hl]
    exact ⟨by omega_arith, h1, by omega_arith⟩
  · intro ⟨hl, h1, hsl⟩
    have hp : L - sl - 1 = lz dbL := by omega_arith
    rw [hp]
    exact ⟨fun i hi => getD_lt_lz hi, h1⟩

variable {H : Hash} (hH : Proof.Pbkdf2.Md.X86_64.HashOK H)

variable (H) in
/-- `prefixCheck`'s last block. -/
def pfxTail : List Instr :=
  [.movzx8 .rdx (ix .rdi .rsi), .alu .xor .rdx (.imm 1), .alu .or .rax (.reg .rdx),
    .store (sp sPos) .rsi, .store (sp sAcc) .rax, .mov .rax (.mem (sp sSlen)),
    .alu .add .rax (.imm (BitVec.ofNat 32 (8 + H.D))), .store (sp sL) .rax]

include hH in
theorem pfxTail_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e p sl : Nat} {r : BitVec 64} (hfit : e + p + 1 ≤ oRsa)
    (hsl : W 36 = BitVec.ofNat 64 sl)
    (hdi : u.gpr .rdi = off S e) (hsi : u.gpr .rsi = BitVec.ofNat 64 p) (hax : u.gpr .rax = r) :
    WP isa (.block (pfxTail H)) u fun u' => Lay u' F S ∧ Keep [.rdx, .rax] u u' ∧
      Rep u'.mem F S V (upd (upd (upd W 34 (BitVec.ofNat 64 p)) 33
        (r ||| (BitVec.setWidth 64 (V (e + p)) ^^^ 1))) 27 (BitVec.ofNat 64 (sl + (8 + H.D)))) := by
  have hDN := hH.hDN
  have hN := hH.N_le
  have G' := L.geo
  set a := r ||| (BitVec.setWidth 64 (V (e + p)) ^^^ 1) with ha
  have R1 := R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 p)
  have R2 := R1.wf G' (k := 33) (by decide) a
  have R3 := R2.wf G' (k := 27) (by decide) (BitVec.ofNat 64 (sl + (8 + H.D)))
  rw [show off F (8 * 34) = off F sPos from rfl] at R1 R2 R3
  rw [show off F (8 * 33) = off F sAcc from rfl] at R2 R3
  rw [show off F (8 * 27) = off F sL from rfl] at R3
  have e36 : ((u.mem.writeW (off F sPos) (BitVec.ofNat 64 p)).writeW (off F sAcc) a).readW (off F sSlen) 64 =
      BitVec.ofNat 64 sl := by
    rw [R2.rd (d := sSlen) 36 rfl (by decide)]; simp [upd, hsl]
  have hea : u.gpr .rdi + u.gpr .rsi = off S (e + p) := by rw [hdi, hsi, off_plus]
  have hld := L.sld8 (d := e + p) (by omega_arith)
  have hval : u.mem (off S (e + p)) = V (e + p) := R.scr _ (by omega_arith)
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u' => u'.mem =
      ((u.mem.writeW (off F sPos) (BitVec.ofNat 64 p)).writeW (off F sAcc) a).writeW (off F sL)
        (BitVec.ofNat 64 (sl + (8 + H.D)))) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨L.of_rep' R (hm ▸ R3) (by simp [upd]) (k.gpr (by decide)) k.2.2, k, hm ▸ R3⟩
  xrun [pfxTail, ea_ix0, ea_sp, L.rsp, hdi, hsi, off_plus, hld, hval, hax, L.st (d := sAcc) (by decide),
    L.st (d := sPos) (by decide), L.ld (d := sSlen) (by decide), L.st (d := sL) (by decide), e36,
    VG.Proof.MlKem.X86_64.sx_ofNat (show 8 + H.D < 2 ^ 31 by omega_arith)]
  rw [← ha, e36, BitVec.ofNat_add_ofNat]

include hH in
/-- `prefixCheck`: `acc` becomes some `a` that is zero exactly when `acc` was,
`DB`'s first `p = db - sl - 1` bytes are zero and `DB[p]` is `0x01`; `pos`
and `ℓ` are `p` and `sl + 8 + hLen`. -/
theorem prefixCheck_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db sl : Nat} (he : W 23 = off S e) (hdb : W 24 = BitVec.ofNat 64 db)
    (hsl : W 36 = BitVec.ofNat 64 sl) (hs : sl < db) (hfit : e + db ≤ oRsa) (hdb2 : db ≤ 1024) :
    WP isa (prefixCheck H) u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .rcx, .rax, .r8, .rdx] u u' ∧
      ∃ a, (a = 0 ↔ W 33 = 0 ∧ ZeroUpTo V e (db - sl - 1) ∧ V (e + (db - sl - 1)) = 1) ∧
      Rep u'.mem F S V (upd (upd (upd W 34 (BitVec.ofNat 64 (db - sl - 1))) 33 a) 27
        (BitVec.ofNat 64 (sl + (8 + H.D)))) := by
  have c5 : oRsa = 8192 := rfl
  unfold prefixCheck seqs seqs seqs seqs
  refine WP.seq (WP.mono (pfxHead_ok L R he hdb hsl hs hdb2)
    fun u1 ⟨k1, hm1, hdi1, hsi1, hcx1, hax1, h81, hz1⟩ => ?_)
  have L1 := L.congr (k1.gpr (by decide)) k1.2.2 (by rw [hm1])
  have R1 : Rep u1.mem F S V W := hm1 ▸ R
  -- The words.
  have hw : WP isa (.ite .e (.block []) prefixWords) u1 fun (u2 : State) => Keep [.rax, .r8] u1 u2 ∧
      u2.mem = u1.mem ∧ u2.gpr .r8 = BitVec.ofNat 64 (8 * ((db - sl - 1) / 8)) ∧
      (u2.gpr .rax = 0 ↔ W 33 = 0 ∧ ZeroUpTo V e (8 * ((db - sl - 1) / 8))) := by
    refine WP.ite (M := isa) (decide (8 * ((db - sl - 1) / 8) = 0)) (show isa.eval .e u1 = _ from hz1)
      (fun h => ?_) (fun h => ?_)
    · rw [decide_eq_true_eq] at h
      refine WP.block_nil ⟨Keep.refl _ _, rfl, by rw [h81, h], by
        rw [hax1, h]; exact ⟨fun h' => ⟨h', fun i hi => absurd hi (by omega_arith)⟩, fun h' => h'.1⟩⟩
    · rw [decide_eq_false_iff_not] at h
      exact pfxWords_ok L1 R1 (n := (db - sl - 1) / 8) (by omega_arith) (by omega_arith) hdi1 hcx1 h81 hax1
  refine WP.seq (WP.mono hw fun u2 ⟨k2, hm2, h82, hax2⟩ => ?_)
  have L2 := L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2])
  have R2 : Rep u2.mem F S V W := hm2.trans hm1 ▸ R
  have hdi2 : u2.gpr .rdi = off S e := (k2.gpr (by decide)).trans hdi1
  have hsi2 : u2.gpr .rsi = BitVec.ofNat 64 (db - sl - 1) := (k2.gpr (by decide)).trans hsi1
  -- The comparison.
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun v => v.mem = u2.mem ∧ v.gpr .r8 = u2.gpr .r8 ∧
      v.zf = some (decide (8 * ((db - sl - 1) / 8) = db - sl - 1))) ?_ rfl) fun u3 ⟨⟨hm3, h83, hz3⟩, k3⟩ => ?_)
  · xrun [h82, hsi2, ofNat_sub_beq (show 8 * ((db - sl - 1) / 8) < 2 ^ 64 by omega_arith)
      (show db - sl - 1 < 2 ^ 64 by omega_arith)]
  have L3 := L2.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep u3.mem F S V W := hm3 ▸ R2
  -- The bytes.
  have hb : WP isa (.ite .e (.block []) prefixBytes) u3 fun (u4 : State) => Keep [.rax, .r8, .rdx] u3 u4 ∧
      u4.mem = u3.mem ∧ (u4.gpr .rax = 0 ↔ W 33 = 0 ∧ ZeroUpTo V e (db - sl - 1)) := by
    refine WP.ite (M := isa) (decide (8 * ((db - sl - 1) / 8) = db - sl - 1)) (show isa.eval .e u3 = _ from hz3)
      (fun h => ?_) (fun h => ?_)
    · rw [decide_eq_true_eq] at h
      refine WP.block_nil ⟨Keep.refl _ _, rfl, ?_⟩
      rw [k3.gpr (by decide), hax2, h]
    · rw [decide_eq_false_iff_not] at h
      exact pfxBytes_ok L3 R3 (m := 8 * ((db - sl - 1) / 8)) (by omega_arith) (by omega_arith)
        ((k3.gpr (by decide)).trans hdi2) ((k3.gpr (by decide)).trans hsi2) (h83.trans h82)
        (by rw [k3.gpr (by decide)]; exact hax2)
  refine WP.seq (WP.mono hb fun u4 ⟨k4, hm4, hax4⟩ => ?_)
  have L4 := L3.congr (k4.gpr (by decide)) k4.2.2 (by rw [hm4])
  have R4 : Rep u4.mem F S V W := hm4 ▸ R3
  refine WP.mono (pfxTail_ok hH L4 R4 (e := e) (p := db - sl - 1) (sl := sl) (r := u4.gpr .rax) (by omega_arith) hsl
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans hdi2))
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans hsi2)) rfl) fun u5 ⟨L5, k5, R5⟩ => ?_
  refine ⟨L5, ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by decide), _, ?_, R5⟩
  rw [or_eq_zero64, hax4, xor_eq_zero, show (1 : BitVec 64) = BitVec.setWidth 64 (1 : Byte) from rfl, zext_inj,
    and_assoc]

end VG.Proof.RsaPss.X86_64
