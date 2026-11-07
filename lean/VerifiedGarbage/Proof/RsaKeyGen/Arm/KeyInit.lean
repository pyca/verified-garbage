module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.KeyInit
meta import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.CountedLoop
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_generate_init` on ARMv7

As on AArch64 (`Proof/RsaKeyGen/AArch64/KeyInit.lean`): `e`'s value modulo
`2^32` and whether it is below `2^32`, read octet by octet; the status and
its mask, from carries; the state's halves, each masked; and the caller's
`r4` and `r5`, which wait in two of them. Its timing depends only on the
public arguments, which its loop's count is: a taint check.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.KeyInit

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Bignum.Arm (Workspace)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.SearchInit (bytesAt_succ)
open VG.Impl.RsaKeyGen.Arm.KeyInit

theorem rev_exec (s : State) (d m : Reg) : exec (.rev d m) s = some (s.setReg d (rev (s.gpr m))) := rfl

theorem carry_ofNat (c : Bool) : (0#32 + 0#32 + (if c = true then 1#32 else 0#32)) = BitVec.ofNat 32 c.toNat := by
  cases c <;> rfl

theorem carry_dec (P : Prop) [Decidable P] :
    (0 + 0 + if decide P = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 (decide P).toNat := by
  by_cases h : P
  · rw [decide_eq_true h]; rfl
  · rw [decide_eq_false h]; rfl

theorem or_zero32 (x y : BitVec 32) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 32).toNat = 0 from rfl] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by rw [this.1]; rfl), BitVec.eq_of_toNat_eq (by rw [this.2]; rfl)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem ofNat32_eq_zero {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  · intro h; rw [h]; rfl

theorem os2ip_snoc (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem sub_one32 {k : Nat} (h1 : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change (2 ^ 32 - 1 + k % 2 ^ 32) % 2 ^ 32 = (k - 1) % 2 ^ 32
  omega

theorem ofNat_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 0 == 0) = decide (k = 0) := by
  have e : BitVec.ofNat 32 k - 0 = BitVec.ofNat 32 k := BitVec.sub_zero _
  rw [e]
  by_cases h : k = 0
  · subst h; rfl
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr fun e => h ((ofNat32_eq_zero hk).mp e)

theorem ofNat_beq0 {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  have e := ofNat_beq hk
  rwa [show BitVec.ofNat 32 k - 0 = BitVec.ofNat 32 k from BitVec.sub_zero _] at e

theorem add_one32 (E : BitVec 32) (j : Nat) : E + BitVec.ofNat 32 j + 1 = E + BitVec.ofNat 32 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `v` shifted by an octet, plus the octet `b`, modulo `2^32`. -/
theorem shl8_add (v : Nat) (hv : v < 2 ^ 32) (b : Byte) :
    BitVec.ofNat 32 v <<< 8 + b.setWidth 32 = BitVec.ofNat 32 ((256 * v + b.toNat) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (show b.toNat < 2 ^ 32 by omega), Nat.shiftLeft_eq, Nat.mod_mod]
  omega

theorem shr24 (v : Nat) (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 24 = BitVec.ofNat 32 (v / 2 ^ 24) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-! ## `e`'s octets -/

/-- After `j` of `e`'s `n` octets at `E`: its value so far modulo `2^32` in
`r4`, and in `r5` whether it is below `2^32`. -/
structure ScanInv (s : State) (E : BitVec 32) (n j : Nat) (u : State) : Prop where
  ptr : u.gpr .r2 = E + BitVec.ofNat 32 j
  value : u.gpr .r4 = BitVec.ofNat 32 (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr E) j) % 2 ^ 32)
  high : u.gpr .r5 = 0 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr E) j) < 2 ^ 32
  count : u.gpr .r3 = BitVec.ofNat 32 (n - j)
  z : u.z = decide (n - j = 0)
  mem : u.mem = s.mem
  rest : Rest [.r2, .r3, .r4, .r5, .r12] s u

theorem octet_step {s u : State} {E : BitVec 32} {n j : Nat} (hj : j < n) (hn : n < 2 ^ 32)
    (fits : E.toNat + n ≤ 2 ^ 32)
    (hrd : InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 j) 1) (h : ScanInv s E n j u) :
    WP isa (.block octet) u (ScanInv s E n (j + 1)) := by
  have addr : State.addr (E + BitVec.ofNat 32 j) = State.addr E + BitVec.ofNat 64 j :=
    VG.Arm.addr_add (by omega)
  have hr : InRegions (u.rd ++ u.wr) (State.addr E + BitVec.ofNat 64 j) 1 := by
    rw [h.rest.rd, h.rest.wr]; exact hrd
  obtain ⟨V, hVd⟩ : ∃ V, Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr E) j) = V := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, u.mem (State.addr E + BitVec.ofNat 64 j) = b := ⟨_, rfl⟩
  have hV : V % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hval : u.gpr .r4 = BitVec.ofNat 32 (V % 2 ^ 32) := by rw [h.value, hVd]
  refine WP.mono (withRest_all [.r2, .r3, .r4, .r5, .r12] (Q := fun t =>
      t.gpr .r2 = E + BitVec.ofNat 32 (j + 1) ∧
      t.gpr .r4 = BitVec.ofNat 32 ((256 * (V % 2 ^ 32) + b.toNat) % 2 ^ 32) ∧
      t.gpr .r5 = u.gpr .r5 ||| BitVec.ofNat 32 (V % 2 ^ 32 / 2 ^ 24) ∧
      t.gpr .r3 = BitVec.ofNat 32 (n - (j + 1)) ∧ t.z = decide (n - (j + 1) = 0) ∧ t.mem = u.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h2, h4, h5, h3, hz, hm⟩, k⟩ => ⟨h2, ?_, ?_, h3, hz, hm.trans h.mem, h.rest.trans k⟩
  · unfold octet
    ffrun [h.ptr, hval, h.count, BitVec.add_zero, addr, hr, hbd, add_one32, shr24 _ hV, shl8_add _ hV,
      sub_one32 (k := n - j) (by omega) (by omega), show n - j - 1 = n - (j + 1) by omega,
      ofNat_beq (k := n - (j + 1)) (by omega), ofNat_beq0 (k := n - (j + 1)) (by omega)]
  · have hb' : s.mem (State.addr E + BitVec.ofNat 64 j) = b := by rw [← h.mem]; exact hbd
    rw [h4, bytesAt_succ, os2ip_snoc, hVd, hb']
    congr 1
    omega
  · have hb' : s.mem (State.addr E + BitVec.ofNat 64 j) = b := by rw [← h.mem]; exact hbd
    have hb := b.isLt
    rw [h5, or_zero32, h.high, bytesAt_succ, os2ip_snoc, hVd, hb', ofNat32_eq_zero (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Nat.mod_eq_of_lt h1] at h2
      have := (Nat.div_eq_zero_iff_lt (by decide)).mp h2
      omega
    · intro h'
      refine ⟨by omega, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega)]
      exact Nat.div_eq_of_lt (by omega)

theorem scan_ok {s u : State} {E : BitVec 32} {n : Nat} (hp : u.gpr .r2 = E)
    (hl : u.gpr .r3 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) (fits : E.toNat + n ≤ 2 ^ 32)
    (hm : u.mem = s.mem) (hk : Rest [.r2, .r3, .r4, .r5, .r12] s u)
    (hrd : ∀ j < n, InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 j) 1) :
    WP isa scan u (ScanInv s E n n) := by
  unfold scan
  refine WP.seq (WP.mono (withRest_all [.r4, .r5] (Q := fun t =>
      t.gpr .r4 = 0 ∧ t.gpr .r5 = 0 ∧ t.z = decide (n = 0) ∧ t.mem = u.mem)
    (by ffrun [hl, ofNat_beq hn]) (by rfl) (by rfl)) fun t ⟨⟨h4, h5, hz, hmt⟩, k⟩ => ?_)
  have h0 : ScanInv s E n 0 t := ⟨by rw [k.gpr .r2 (by decide), hp, BitVec.add_zero], by rw [h4]; rfl,
    by rw [h5]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], by rw [k.gpr .r3 (by decide), hl, Nat.sub_zero],
    by rw [hz, Nat.sub_zero], hmt.trans hm, hk.trans (k.mono (by decide))⟩
  refine WP.ite _ (show some t.z = _ from rfl) (fun hz' => ?_) (fun hz' => ?_)
  · rw [hz] at hz'
    have hz' : n = 0 := of_decide_eq_true hz'
    subst hz'
    exact WP.block_nil h0
  · rw [hz] at hz'
    have hz' : n ≠ 0 := of_decide_eq_false hz'
    refine WP.mono (WP.chunk_loop (I := ScanInv s E n) (n := n) (N := 1) (k := 0) (by decide) (by omega) h0
      (fun j t hj ht => octet_step (by omega) hn fits (hrd j (by omega)) ht)
      (fun j t _ ht => ?_)) fun t ⟨j, hj, hl, ht⟩ => by
        obtain rfl : j = n := by omega
        exact ht
    have e : isa.eval .ne t = some (!decide (n - j = 0)) := by
      change some (!t.z) = _; rw [ht.z]
    rw [e]
    constructor
    · intro hl; rw [decide_eq_true (by omega)]; rfl
    · intro hl; rw [decide_eq_false (by omega)]; rfl

/-! ## The status -/

/-- The status `vg_rsa_generate_init` returns, of the size and `e`'s value. -/
def initStatus (bits e : Nat) : Nat :=
  if !Spec.RsaKeyGen.exponentValid e then 0
  else if Spec.RsaKeyGen.modulusBits bits = none then 2 else 1

theorem initStatus_val (bits E : Nat) :
    initStatus bits E = if E % 2 = 1 ∧ 3 ≤ E ∧ E < 2 ^ 32 then
      (if bits ≤ 8192 ∧ 512 ≤ bits then 1 else 2) else 0 := by
  unfold initStatus Spec.RsaKeyGen.exponentValid Spec.RsaKeyGen.modulusBits Spec.RsaKeyGen.maxBits
    Spec.RsaKeyGen.minBits
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | simp_all

/-- The mask of status 1: all ones or zero. -/
def maskOf (st : Nat) : BitVec 32 := 0 - BitVec.ofNat 32 (if st = 1 then 1 else 0)

/-- The status and its mask, from the tests' bits. -/
theorem status_bits (a b c d : Bool) (o : Nat) (ho : o < 2) (hab : b = true → a = true) :
    (2#32 - (BitVec.ofNat 32 a.toNat - BitVec.ofNat 32 b.toNat)) *
        ((BitVec.ofNat 32 o &&& BitVec.ofNat 32 c.toNat) &&& ~~~BitVec.ofNat 32 d.toNat) =
      BitVec.ofNat 32 (if o = 1 ∧ c = true ∧ d = false then (if a = true ∧ b = false then 1 else 2) else 0) ∧
    0#32 - ((BitVec.ofNat 32 o &&& BitVec.ofNat 32 c.toNat) &&& ~~~BitVec.ofNat 32 d.toNat &&&
        (BitVec.ofNat 32 a.toNat - BitVec.ofNat 32 b.toNat)) =
      maskOf (if o = 1 ∧ c = true ∧ d = false then (if a = true ∧ b = false then 1 else 2) else 0) := by
  unfold maskOf
  rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp at hab <;> decide

theorem and1_32 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 1#32 = BitVec.ofNat 32 (n % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, show (1#32).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem enc512 : encodable 512 = true := by decide

theorem sizeTest_ok {u : State} {bits : Nat} (hb : bits < 2 ^ 32) (h1 : u.gpr .r1 = BitVec.ofNat 32 bits) :
    WP isa (.block sizeTest) u fun t => (t.gpr .r3 = BitVec.ofNat 32 (decide (512 ≤ bits)).toNat -
      BitVec.ofNat 32 (decide (8193 ≤ bits)).toNat ∧ t.mem = u.mem) ∧ Rest [.r3, .r12] u t := by
  refine withRest_all [.r3, .r12] ?_ (by rfl) (by rfl)
  unfold sizeTest
  have e1 : (BitVec.ofNat 32 bits).toNat = bits := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  ffrun [h1, enc512]
  simp only [carry_dec, e1, show (512 : BitVec 32).toNat = 512 from rfl,
    show (BitVec.setWidth 32 (8193 : BitVec 16)).toNat = 8193 from rfl]

theorem expTest_ok {u : State} {V : Nat} (hV : V < 2 ^ 32) (h4 : u.gpr .r4 = BitVec.ofNat 32 V) :
    WP isa (.block expTest) u fun t => (t.gpr .r12 = (BitVec.ofNat 32 (V % 2) &&&
      BitVec.ofNat 32 (decide (3 ≤ V)).toNat) &&& ~~~BitVec.ofNat 32 (decide (1 ≤ (u.gpr .r5).toNat)).toNat ∧
      t.mem = u.mem) ∧ Rest [.r2, .r12] u t := by
  refine withRest_all [.r2, .r12] ?_ (by rfl) (by rfl)
  unfold expTest
  have e1 : (BitVec.ofNat 32 V).toNat = V := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV]
  ffrun [h4]
  simp only [carry_dec, e1, show (3 : BitVec 32).toNat = 3 from rfl, show (1 : BitVec 32).toNat = 1 from rfl]
  rw [show (1 : BitVec 32) = 1#32 from rfl, and1_32 hV]

theorem statusMask_ok {u : State} {a b c d : Bool} {o : Nat} (ho : o < 2) (hab : b = true → a = true)
    (h3 : u.gpr .r3 = BitVec.ofNat 32 a.toNat - BitVec.ofNat 32 b.toNat)
    (h12 : u.gpr .r12 = (BitVec.ofNat 32 o &&& BitVec.ofNat 32 c.toNat) &&& ~~~BitVec.ofNat 32 d.toNat) :
    WP isa (.block statusMask) u fun t =>
      (t.gpr .r5 = BitVec.ofNat 32 (if o = 1 ∧ c = true ∧ d = false then (if a = true ∧ b = false then 1 else 2) else 0) ∧
        t.gpr .r12 = maskOf (if o = 1 ∧ c = true ∧ d = false then (if a = true ∧ b = false then 1 else 2) else 0) ∧
        t.gpr .r3 = 0 ∧ t.mem = u.mem) ∧ Rest [.r3, .r5, .r12] u t := by
  refine withRest_all [.r3, .r5, .r12] ?_ (by rfl) (by rfl)
  unfold statusMask
  obtain ⟨e1, e2⟩ := status_bits a b c d o ho hab
  ffrun [h3, h12]
  exact ⟨e1, e2⟩

/-! ## The words -/

/-- The primes' octets, from the size. -/
def plenBV (bits : Nat) : BitVec 32 := (BitVec.ofNat 32 bits >>> 7) <<< 3

/-- The counted candidates, from the primes' octets and `e`'s low word. -/
def limitBV (P : BitVec 32) (V : Nat) : BitVec 32 :=
  P <<< 6 - BitVec.ofNat 32 (decide (1 ≤ (BitVec.ofNat 32 V ^^^ 3).toNat)).toNat * (P <<< 3 + P <<< 4)

/-- The halves `words` stores, in order, masked by `M`. -/
def wordsList (bits V : Nat) (M : BitVec 32) : List (Nat × BitVec 32) :=
  [(1, 0), (7, 0), (8, 0), (9, 0), (11, 0), (12, 0), (10, 4 &&& M), (2, plenBV bits &&& M),
    (4, (plenBV bits <<< 15 + plenBV bits) &&& M), (6, plenBV bits <<< 5 &&& M),
    (13, rev (BitVec.ofNat 32 V) &&& M), (0, limitBV (plenBV bits) V &&& M)]

structure Space (B : BitVec 32) (s : State) : Prop where
  space : Workspace s B 56
  ptr : s.gpr .r0 = B

theorem Space.addr {B : BitVec 32} {s : State} (h : Space B s) {d : Nat} (hd : d < 56) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr B) d := by
  rw [h.ptr]; exact VG.Arm.addr_add (by have := h.space.nowrap; omega)

theorem Space.congr {B : BitVec 32} {s t : State} (h : Space B s) (hw : t.wr = s.wr)
    (h0 : t.gpr .r0 = s.gpr .r0) : Space B t :=
  ⟨h.space.congr hw, h0.trans h.ptr⟩

def zeroList : List (Nat × BitVec 32) := [(1, 0), (7, 0), (8, 0), (9, 0), (11, 0), (12, 0)]
def smallList (bits : Nat) (M : BitVec 32) : List (Nat × BitVec 32) := [(10, 4 &&& M), (2, plenBV bits &&& M)]
def bigList (bits V : Nat) (M : BitVec 32) : List (Nat × BitVec 32) :=
  [(4, (plenBV bits <<< 15 + plenBV bits) &&& M), (6, plenBV bits <<< 5 &&& M), (13, rev (BitVec.ofNat 32 V) &&& M)]
def limitList (bits V : Nat) (M : BitVec 32) : List (Nat × BitVec 32) := [(0, limitBV (plenBV bits) V &&& M)]

theorem wordsList_eq (bits V : Nat) (M : BitVec 32) :
    wordsList bits V M = zeroList ++ smallList bits M ++ bigList bits V M ++ limitList bits V M := rfl

theorem wordsZero_ok {B : BitVec 32} {s : State} (h : Space B s) {bits : Nat}
    (h1 : s.gpr .r1 = BitVec.ofNat 32 bits) (h3 : s.gpr .r3 = 0) :
    WP isa (.block wordsZero) s fun t => (t.gpr .r2 = plenBV bits ∧
      t.mem = writeSlots s.mem (State.addr B) zeroList) ∧ Rest [.r2] s t := by
  refine withRest_all [.r2] ?_ (by rfl) (by rfl)
  unfold wordsZero zeroList writeSlots
  ffrun [h1, h3, h.addr (d := 4) (by decide), h.addr (d := 28) (by decide), h.addr (d := 32) (by decide),
    h.addr (d := 36) (by decide), h.addr (d := 44) (by decide), h.addr (d := 48) (by decide),
    h.space.write (off := 4) (by decide), h.space.write (off := 28) (by decide),
    h.space.write (off := 32) (by decide), h.space.write (off := 36) (by decide),
    h.space.write (off := 44) (by decide), h.space.write (off := 48) (by decide)]
  exact ⟨rfl, rfl⟩

theorem wordsSmall_ok {B : BitVec 32} {s : State} (h : Space B s) {bits : Nat} {M : BitVec 32}
    (h2 : s.gpr .r2 = plenBV bits) (h12 : s.gpr .r12 = M) :
    WP isa (.block wordsSmall) s fun t => t.mem = writeSlots s.mem (State.addr B) (smallList bits M) ∧
      Rest [.r1] s t := by
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  unfold wordsSmall smallList writeSlots
  ffrun [h2, h12, h.addr (d := 8) (by decide), h.addr (d := 40) (by decide),
    h.space.write (off := 8) (by decide), h.space.write (off := 40) (by decide)]
  rfl

theorem wordsBig_ok {B : BitVec 32} {s : State} (h : Space B s) {bits V : Nat} {M : BitVec 32}
    (h2 : s.gpr .r2 = plenBV bits) (h4 : s.gpr .r4 = BitVec.ofNat 32 V) (h12 : s.gpr .r12 = M) :
    WP isa (.block wordsBig) s fun t => t.mem = writeSlots s.mem (State.addr B) (bigList bits V M) ∧
      Rest [.r1] s t := by
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  unfold wordsBig bigList writeSlots
  ffrun [rev_exec, h2, h4, h12, h.addr (d := 16) (by decide), h.addr (d := 24) (by decide),
    h.addr (d := 52) (by decide), h.space.write (off := 16) (by decide), h.space.write (off := 24) (by decide),
    h.space.write (off := 52) (by decide)]
  rfl

theorem limitFlag_ok {s : State} {V : Nat} (h4 : s.gpr .r4 = BitVec.ofNat 32 V) :
    WP isa (.block limitFlag) s fun t => (t.gpr .r1 = BitVec.ofNat 32 (decide (1 ≤ (BitVec.ofNat 32 V ^^^ 3).toNat)).toNat ∧
      t.mem = s.mem) ∧ Rest [.r1] s t := by
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  unfold limitFlag
  ffrun [h4]
  simp only [carry_dec, show (1 : BitVec 32).toNat = 1 from rfl]

theorem limitStore_ok {B : BitVec 32} {s : State} (h : Space B s) {bits V : Nat} {M : BitVec 32}
    (h1 : s.gpr .r1 = BitVec.ofNat 32 (decide (1 ≤ (BitVec.ofNat 32 V ^^^ 3).toNat)).toNat)
    (h2 : s.gpr .r2 = plenBV bits) (h12 : s.gpr .r12 = M) :
    WP isa (.block limitStore) s fun t => t.mem = writeSlots s.mem (State.addr B) (limitList bits V M) ∧
      Rest [.r1, .r3] s t := by
  refine withRest_all [.r1, .r3] ?_ (by rfl) (by rfl)
  unfold limitStore limitList writeSlots limitBV
  ffrun [h1, h2, h12, h.addr (d := 0) (by decide), h.space.write (off := 0) (by decide)]
  rfl

theorem wordsLimit_ok {B : BitVec 32} {s : State} (h : Space B s) {bits V : Nat} {M : BitVec 32}
    (h2 : s.gpr .r2 = plenBV bits) (h4 : s.gpr .r4 = BitVec.ofNat 32 V) (h12 : s.gpr .r12 = M) :
    WP isa (.block wordsLimit) s fun t => t.mem = writeSlots s.mem (State.addr B) (limitList bits V M) ∧
      Rest [.r1, .r3] s t := by
  unfold wordsLimit
  refine WP.block_append (WP.mono (limitFlag_ok h4) fun u ⟨⟨hu1, hum⟩, ku⟩ => ?_)
  refine WP.mono (limitStore_ok (h.congr ku.wr (ku.gpr .r0 (by decide))) hu1 ((ku.gpr .r2 (by decide)).trans h2)
    ((ku.gpr .r12 (by decide)).trans h12)) fun t ⟨htm, kt⟩ => ⟨by rw [htm, hum], (ku.mono (by decide)).trans kt⟩

theorem words_ok {B : BitVec 32} {s : State} (h : Space B s) {bits V : Nat} {M : BitVec 32}
    (h1 : s.gpr .r1 = BitVec.ofNat 32 bits) (h4 : s.gpr .r4 = BitVec.ofNat 32 V) (h12 : s.gpr .r12 = M)
    (h3 : s.gpr .r3 = 0) :
    WP isa (.block Impl.RsaKeyGen.Arm.KeyInit.words) s fun t =>
      t.mem = writeSlots s.mem (State.addr B) (wordsList bits V M) ∧ Rest [.r1, .r2, .r3] s t := by
  unfold Impl.RsaKeyGen.Arm.KeyInit.words
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono (wordsZero_ok h h1 h3)
    fun u ⟨⟨hu2, hum⟩, ku⟩ => ?_)))
  have hu := h.congr ku.wr (ku.gpr .r0 (by decide))
  refine WP.mono (wordsSmall_ok hu hu2 ((ku.gpr .r12 (by decide)).trans h12)) fun v ⟨hvm, kv⟩ => ?_
  have hv := hu.congr kv.wr (kv.gpr .r0 (by decide))
  have hv2 : v.gpr .r2 = plenBV bits := (kv.gpr .r2 (by decide)).trans hu2
  have hv4 : v.gpr .r4 = BitVec.ofNat 32 V := (kv.gpr .r4 (by decide)).trans ((ku.gpr .r4 (by decide)).trans h4)
  have hv12 : v.gpr .r12 = M := (kv.gpr .r12 (by decide)).trans ((ku.gpr .r12 (by decide)).trans h12)
  refine WP.mono (wordsBig_ok hv hv2 hv4 hv12) fun w ⟨hwm, kw⟩ => ?_
  have hw := hv.congr kw.wr (kw.gpr .r0 (by decide))
  refine WP.mono (wordsLimit_ok hw ((kw.gpr .r2 (by decide)).trans hv2) ((kw.gpr .r4 (by decide)).trans hv4)
    ((kw.gpr .r12 (by decide)).trans hv12)) fun t ⟨htm, kt⟩ => ⟨?_, ?_⟩
  · rw [htm, hwm, hvm, hum, wordsList_eq, writeSlots_append, writeSlots_append, writeSlots_append]
  · exact ((ku.mono (by decide)).trans (kv.mono (by decide))).trans ((kw.mono (by decide)).trans (kt.mono (by decide)))

/-! ## Saving and restoring `r4` and `r5` -/

theorem save_ok {B : BitVec 32} {s : State} (h : Space B s) :
    WP isa (.block save) s fun t => t.mem = writeSlots s.mem (State.addr B) [(3, s.gpr .r4), (5, s.gpr .r5)] ∧
      Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  unfold save writeSlots
  ffrun [h.addr (d := 12) (by decide), h.addr (d := 20) (by decide), h.space.write (off := 12) (by decide),
    h.space.write (off := 20) (by decide)]
  rfl

theorem restore_ok {B : BitVec 32} {s : State} (h : Space B s) {a b : BitVec 32}
    (h3 : slot s.mem (State.addr B) 3 = a) (h5 : slot s.mem (State.addr B) 5 = b) :
    WP isa (.block restore) s fun t => (t.gpr .r0 = s.gpr .r5 ∧ t.gpr .r4 = a ∧ t.gpr .r5 = b ∧
      t.mem = writeSlots s.mem (State.addr B) [(3, 0), (5, 0)]) ∧ Rest [.r0, .r1, .r2, .r4, .r5] s t := by
  refine withRest_all [.r0, .r1, .r2, .r4, .r5] ?_ (by rfl) (by rfl)
  unfold restore writeSlots
  unfold slot at h3 h5
  ffrun [h.addr (d := 12) (by decide), h.addr (d := 20) (by decide), h.space.write (off := 12) (by decide),
    h.space.write (off := 20) (by decide), h.space.read (off := 12) (by decide), h.space.read (off := 20) (by decide),
    h3, h5]
  rfl

/-! ## The state's halves at the end -/

def saveList (a b : BitVec 32) : List (Nat × BitVec 32) := [(3, a), (5, b)]
def restoreList : List (Nat × BitVec 32) := [(3, 0), (5, 0)]

theorem bound_of (l : List (Nat × BitVec 32)) (h : l.all (fun e => decide (e.1 < 14)) = true) :
    ∀ e ∈ l, e.1 < 14 := fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

/-- A half of the final state, from the three lists of stores. -/
theorem final_slot (m : Mem) (B : Addr) (a b : BitVec 32) (bits V : Nat) (M : BitVec 32) {j : Nat} (hj : j < 14) :
    slot (writeSlots (writeSlots (writeSlots m B (saveList a b)) B (wordsList bits V M)) B restoreList) B j =
      slotValue restoreList j (slotValue (wordsList bits V M) j (slotValue (saveList a b) j (slot m B j))) := by
  rw [slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) j hj,
    slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) j hj,
    slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) j hj]

/-- `u64` words from their halves. -/
theorem wordsAt_halves (m : Mem) (B : Addr) (n : Nat) (f : Nat → Nat) (hf : ∀ j < n, f j < 2 ^ 32)
    (h0 : ∀ j < n, slot m B (2 * j) = BitVec.ofNat 32 (f j)) (h1 : ∀ j < n, slot m B (2 * j + 1) = 0) :
    Spec.Rsa.wordsAt m B n = (List.range n).map fun j => BitVec.ofNat 64 (f j) := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  rw [← off, pair_word, h1 j hj, h0 j hj]
  exact pair_ofNat (hf j hj)

theorem mask_one (x : BitVec 32) : x &&& maskOf 1 = x := by
  rw [show maskOf 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem mask_ne (x : BitVec 32) {st : Nat} (h : st ≠ 1) : x &&& maskOf st = 0 := by
  have e : maskOf st = 0 := by unfold maskOf; rw [ite_eq_right_iff.mpr (fun e => absurd e h)]; decide
  rw [e]
  exact BitVec.and_zero

theorem shl32 (L k : Nat) (h : L * 2 ^ k < 2 ^ 32) :
    BitVec.ofNat 32 L <<< k = BitVec.ofNat 32 (L * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hL : L < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem plen_eq {bits : Nat} (hb : bits < 2 ^ 32) : plenBV bits = BitVec.ofNat 32 (bits / 128 * 8) := by
  apply BitVec.eq_of_toNat_eq
  unfold plenBV
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem xor3_toNat {V : Nat} (hV : V < 2 ^ 32) : (1 ≤ (BitVec.ofNat 32 V ^^^ 3).toNat) ↔ V ≠ 3 := by
  constructor
  · intro h e; subst e; exact absurd h (by decide)
  · intro h
    refine Nat.pos_of_ne_zero fun e => h ?_
    have e' : BitVec.ofNat 32 V ^^^ 3 = 0 := BitVec.eq_of_toNat_eq (by rw [e]; rfl)
    have := congrArg (· ^^^ (3 : BitVec 32)) e'
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
    have := congrArg BitVec.toNat this
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV] at this

theorem limit_eq {L V : Nat} (hL : L ≤ 512) (hV : V < 2 ^ 32) :
    limitBV (BitVec.ofNat 32 L) V = BitVec.ofNat 32 (if V = 3 then 64 * L else 40 * L) := by
  unfold limitBV
  rw [shl32 L 6 (by omega), shl32 L 3 (by omega), shl32 L 4 (by omega), ← BitVec.ofNat_add,
    ← BitVec.ofNat_mul]
  by_cases h3 : V = 3
  · rw [decide_eq_false (by rw [xor3_toNat hV]; exact fun e => e h3), ite_eq_left h3, Bool.toNat_false,
      Nat.zero_mul, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1; omega
  · rw [decide_eq_true ((xor3_toNat hV).mpr h3), ite_eq_right h3, Bool.toNat_true, Nat.one_mul,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    congr 1; omega

/-! ## The exponent's octets -/

theorem rev_byte32 (v : BitVec 32) {k : Nat} (hk : k < 4) :
    (rev v).extractLsb' (8 * k) 8 = v.extractLsb' (8 * (3 - k)) 8 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> ext i hi <;>
    simp (disch := omega) only [rev, BitVec.getElem_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      Nat.reduceMul, Nat.reduceSub, Nat.zero_add]
  · simp only [hi, ↓reduceIte, decide_true, Bool.true_and]
  · simp only [show ¬ (8 + i < 8) by omega, show 8 + i - 8 = i by omega, hi, ↓reduceIte, decide_true,
      Bool.true_and]
  · simp only [show ¬ (16 + i < 8) by omega, show ¬ (16 + i - 8 < 8) by omega, show 16 + i - 8 - 8 = i by omega,
      hi, ↓reduceIte, decide_true, Bool.true_and]
  · simp only [show ¬ (24 + i < 8) by omega, show ¬ (24 + i - 8 < 8) by omega, show ¬ (24 + i - 8 - 8 < 8) by omega,
      show 24 + i - 8 - 8 - 8 = i by omega, hi, decide_true, Bool.true_and, ↓reduceIte]

theorem extract_nat32 (x : Nat) {j : Nat} (hj : j < 4) :
    (BitVec.ofNat 32 x).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (x / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 32 = 2 ^ (8 * j) * 2 ^ (32 - 8 * j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [show (256 : Nat) ^ j = 2 ^ (8 * j) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]

theorem e_bytes (m : Mem) (B : Addr) {E : Nat} (hE : E < 2 ^ 32) (h12 : slot m B 12 = 0)
    (h13 : slot m B 13 = rev (BitVec.ofNat 32 E)) :
    Spec.Rsa.bytesAt m (B + 48) 8 = Spec.Rsa.i2osp E 8 := by
  unfold Spec.Rsa.bytesAt Spec.Rsa.i2osp
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  unfold slot at h12 h13
  by_cases hlo : i < 4
  · have e : B + 48 + BitVec.ofNat 64 i = off B (4 * 12) + BitVec.ofNat 64 i := rfl
    rw [e, Mem.readW_byte m (off B (4 * 12)) hlo, h12]
    have : E / 256 ^ (8 - 1 - i) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hE
      (by rw [show (2 : Nat) ^ 32 = 256 ^ 4 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · have e : B + 48 + BitVec.ofNat 64 i = off B (4 * 13) + BitVec.ofNat 64 (i - 4) := by
      have h1 : B + 48 + BitVec.ofNat 64 i = B + BitVec.ofNat 64 (48 + i) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl
      have h2 : off B (4 * 13) + BitVec.ofNat 64 (i - 4) = B + BitVec.ofNat 64 (52 + (i - 4)) := by
        rw [off, BitVec.add_assoc, BitVec.ofNat_add]
      rw [h1, h2, show 48 + i = 52 + (i - 4) by omega]
    rw [e, Mem.readW_byte m (off B (4 * 13)) (show i - 4 < 4 by omega), h13, rev_byte32 _ (by omega),
      extract_nat32 _ (by omega), show 3 - (i - 4) = 8 - 1 - i by omega]

/-! ## The final halves -/

/-- The state's halves at the end, in order. -/
def finalVals (bits V : Nat) (M : BitVec 32) : List (BitVec 32) :=
  [limitBV (plenBV bits) V &&& M, 0, plenBV bits &&& M, 0, (plenBV bits <<< 15 + plenBV bits) &&& M, 0,
    plenBV bits <<< 5 &&& M, 0, 0, 0, 4 &&& M, 0, 0, rev (BitVec.ofNat 32 V) &&& M]

/-- The final memory. -/
abbrev finalMem (m : Mem) (B : Addr) (a b : BitVec 32) (bits V : Nat) (M : BitVec 32) : Mem :=
  writeSlots (writeSlots (writeSlots m B (saveList a b)) B (wordsList bits V M)) B restoreList

theorem final_vals (m : Mem) (B : Addr) (a b : BitVec 32) (bits V : Nat) (M : BitVec 32) {j : Nat} (hj : j < 14) :
    slot (finalMem m B a b bits V M) B j = (finalVals bits V M).getD j 0 := by
  rw [final_slot m B a b bits V M hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨
    j = 11 ∨ j = 12 ∨ j = 13) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem final_zero (m : Mem) (B : Addr) (a b : BitVec 32) (bits V : Nat) {st : Nat} (hst : st ≠ 1) {j : Nat}
    (hj : j < 14) : slot (finalMem m B a b bits V (maskOf st)) B j = 0 := by
  rw [final_vals m B a b bits V _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨
    j = 11 ∨ j = 12 ∨ j = 13) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [finalVals, List.getD_cons_zero, List.getD_cons_succ, mask_ne _ hst]

/-- The values of the valid words. -/
def validVals (L E : Nat) : List Nat := [if E = 3 then 64 * L else 40 * L, L, 32769 * L, 32 * L, 0, 4]

theorem final_valid (m : Mem) (B : Addr) (a b : BitVec 32) {bits E : Nat} (hb : bits < 2 ^ 32)
    (hL : bits / 128 * 8 ≤ 512) (hE : E < 2 ^ 32) {j : Nat} (hj : j < 6) :
    slot (finalMem m B a b bits E (maskOf 1)) B (2 * j) =
        BitVec.ofNat 32 ((validVals (bits / 128 * 8) E).getD j 0) ∧
      slot (finalMem m B a b bits E (maskOf 1)) B (2 * j + 1) = 0 := by
  rw [final_vals m B a b bits E _ (by omega), final_vals m B a b bits E _ (by omega)]
  have p := plen_eq hb
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [finalVals, validVals, List.getD_cons_zero, List.getD_cons_succ, mask_one, p, Nat.reduceMul,
      Nat.reduceAdd, and_true]
  · rw [limit_eq hL hE]
  · rw [shl32 _ 15 (by omega), ← BitVec.ofNat_add]; congr 1; omega
  · rw [shl32 _ 5 (by omega)]; congr 1; omega
  · rfl
  · rfl

/-! ## The status, from its tests -/

theorem status_eq (bits E H : Nat) (hH : H = 0 ↔ E < 2 ^ 32) :
    (if E % 2 ^ 32 % 2 = 1 ∧ decide (3 ≤ E % 2 ^ 32) = true ∧ decide (1 ≤ H) = false then
      (if decide (512 ≤ bits) = true ∧ decide (8193 ≤ bits) = false then 1 else 2) else 0) =
      initStatus bits E := by
  rw [initStatus_val]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases hE : E < 2 ^ 32
  · have h0 : H = 0 := hH.mpr hE
    rw [Nat.mod_eq_of_lt hE, h0]
    repeat' split
    all_goals first | rfl | omega
  · have h0 : H ≠ 0 := fun e => hE (hH.mp e)
    repeat' split
    all_goals first | rfl | omega

/-! ## The whole initialization -/

def initPre (s : State) : Prop :=
  s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧ s.wr = [⟨State.addr (s.gpr .r0), 56⟩] ∧
    (s.gpr .r0).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (⟨State.addr (s.gpr .r0), 56⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩

def initPost (s t : State) : Prop :=
  let eB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  match Spec.RsaKeyGen.keySearchInit (s.gpr .r1).toNat eB with
  | .error c => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = c ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 7 = List.replicate 7 0
  | .ok values => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 6 =
        (values ++ [first, 0, Spec.RsaKeyGen.keyGenerations]).map (BitVec.ofNat 64) ∧
      Spec.Rsa.bytesAt t.mem (State.addr (s.gpr .r0) + 48) 8 = Spec.Rsa.i2osp (Spec.Rsa.os2ip eB) 8 ∧
      Spec.Entropy.RequestValid (Spec.RsaKeyGen.primeEntropy (values.getD 1 0)) 0 first

theorem initStatus_lt (bits E : Nat) : initStatus bits E < 2 ^ 32 := by
  rw [initStatus_val]; split <;> (try split) <;> omega

theorem result_post {s t : State} {E : Nat} {a b : BitVec 32}
    (hE : E = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat))
    (hr : t.gpr .r0 = BitVec.ofNat 32 (initStatus (s.gpr .r1).toNat E))
    (hm : t.mem = finalMem s.mem (State.addr (s.gpr .r0)) a b (s.gpr .r1).toNat (E % 2 ^ 32)
      (maskOf (initStatus (s.gpr .r1).toNat E))) :
    initPost s t := by
  unfold initPost Spec.RsaKeyGen.keySearchInit
  dsimp only
  rw [← hE]
  generalize hbits : (s.gpr .r1).toNat = bits at hr hm ⊢
  have hb : bits < 2 ^ 32 := by rw [← hbits]; exact BitVec.isLt _
  have hst := initStatus_val bits E
  have ret (n : Nat) (hn : n < 2 ^ 32) (h : t.gpr .r0 = BitVec.ofNat 32 n) :
      ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = n := by
    rw [BitVec.setWidth_append_eq_right, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have zeros (st : Nat) (h : st ≠ 1) (hm' : t.mem = finalMem s.mem (State.addr (s.gpr .r0)) a b bits (E % 2 ^ 32)
      (maskOf st)) : Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 7 = List.replicate 7 0 := by
    rw [hm', wordsAt_halves _ _ 7 (fun _ => 0) (fun _ _ => by decide)
      (fun j hj => final_zero _ _ _ _ _ _ h (by omega)) (fun j hj => final_zero _ _ _ _ _ _ h (by omega))]
    rfl
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
      rw [h2] at hr hm
      exact ⟨ret 2 (by decide) hr, zeros 2 (by decide) hm⟩
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
      rw [h1] at hr hm
      have hP : nlen / 16 = bits / 128 * 8 := by omega
      have hL : bits / 128 * 8 ≤ 512 := by omega
      have hV : E % 2 ^ 32 = E := Nat.mod_eq_of_lt hvE.2.2
      rw [hV] at hm
      refine ⟨ret 1 (by decide) hr, 32 * (bits / 128 * 8), ?_, ?_, ?_⟩
      · rw [hm, wordsAt_halves _ _ 6 (fun j => (validVals (bits / 128 * 8) E).getD j 0)
          (fun j hj => by
            rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [validVals, List.getD_cons_zero, List.getD_cons_succ] <;> (try split) <;> omega)
          (fun j hj => (final_valid _ _ _ _ hb hL hvE.2.2 hj).1) (fun j hj => (final_valid _ _ _ _ hb hL hvE.2.2 hj).2)]
        rw [show ∀ f : Nat → BitVec 64, (List.range 6).map f = [f 0, f 1, f 2, f 3, f 4, f 5] from fun f => rfl]
        simp only [hP, validVals, Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeEntropy,
          Spec.RsaKeyGen.keyGenerations, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
        by_cases h3 : E = 3 <;> simp only [h3, ↓reduceIte] <;> congr 1 <;> omega
      · rw [hm]
        refine e_bytes _ _ hvE.2.2 ?_ ?_
        · rw [final_vals _ _ _ _ _ _ _ (by decide)]; rfl
        · rw [final_vals _ _ _ _ _ _ _ (by decide)]
          simp only [finalVals, List.getD_cons_zero, List.getD_cons_succ, mask_one]
      · simp only [List.getD_cons_zero, List.getD_cons_succ, hP]
        unfold Spec.Entropy.RequestValid Spec.RsaKeyGen.primeEntropy
        omega
  · have hv' : Spec.RsaKeyGen.exponentValid E = false := by simpa using hv
    rw [ite_eq_left (by rw [hv']; rfl)]
    have h0 : initStatus bits E = 0 := by
      unfold initStatus; rw [ite_eq_left (by rw [hv']; rfl)]
    rw [h0] at hr hm
    exact ⟨ret 0 (by decide) hr, zeros 0 (by decide) hm⟩

theorem slot_saved (m : Mem) (B : Addr) (a b : BitVec 32) (bits V : Nat) (M : BitVec 32) :
    slot (writeSlots (writeSlots m B (saveList a b)) B (wordsList bits V M)) B 3 = a ∧
      slot (writeSlots (writeSlots m B (saveList a b)) B (wordsList bits V M)) B 5 = b := by
  rw [slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) 3 (by decide),
    slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) 3 (by decide),
    slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) 5 (by decide),
    slot_writeSlots _ _ (N := 14) (by decide) _ (bound_of _ rfl) 5 (by decide)]
  exact ⟨rfl, rfl⟩

theorem init_ok {s : State} (h : initPre s) :
    WP isa init s fun t => initPost s t ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r12] s t ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 := by
  obtain ⟨hrd, hwr, hroom, hroome, disj⟩ := h
  have sp : Space (s.gpr .r0) s := ⟨⟨hroom, by rw [hwr]; exact List.mem_singleton_self _⟩, rfl⟩
  unfold init
  refine WP.seq (WP.mono (save_ok sp) fun u0 ⟨hm0, k0⟩ => ?_)
  have hbytes : Spec.Rsa.bytesAt u0.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat := by
    have hf := writeSlots_frame s.mem (State.addr (s.gpr .r0)) (N := 14) (by decide) (saveList (s.gpr .r4) (s.gpr .r5))
      (bound_of _ rfl)
    rw [hm0]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩)
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact disj.symm) (by simp only; omega)
      (List.mem_range.mp hi)
  have hrd0 : ∀ j < (s.gpr .r3).toNat, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 j) 1 :=
    fun i hi => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩
  have hrd1 : ∀ j < (s.gpr .r3).toNat, InRegions (u0.rd ++ u0.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 j) 1 := by
    rw [k0.rd, k0.wr]; exact hrd0
  refine WP.seq (WP.mono (scan_ok (s := u0) (u := u0) (E := s.gpr .r2) (n := (s.gpr .r3).toNat)
    (k0.gpr .r2 (by decide)) (by rw [k0.gpr .r3 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (BitVec.isLt _) hroome rfl (Rest.refl _ _) hrd1) fun u1 hs => ?_)
  generalize hEdef : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = E
  have hEu : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u0.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = E := by
    rw [hbytes, hEdef]
  have h4 := hs.value
  have h5 := hs.high
  rw [hEu] at h4 h5
  have hk1 : Rest [.r2, .r3, .r4, .r5, .r12] s u1 := (k0.mono (by decide)).trans hs.rest
  have hb : (s.gpr .r1).toNat < 2 ^ 32 := BitVec.isLt _
  have h1 : u1.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [hk1.gpr .r1 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show Impl.RsaKeyGen.Arm.KeyInit.status ++ Impl.RsaKeyGen.Arm.KeyInit.words ++ restore =
    (sizeTest ++ expTest ++ statusMask ++ Impl.RsaKeyGen.Arm.KeyInit.words) ++ restore from rfl]
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (sizeTest_ok hb h1) fun u2 ⟨⟨h23, hm2⟩, k2⟩ => ?_))))
  refine WP.mono (expTest_ok (u := u2) (V := E % 2 ^ 32) (Nat.mod_lt _ (by decide))
    ((k2.gpr .r4 (by decide)).trans h4)) fun u3 ⟨⟨h312, hm3⟩, k3⟩ => ?_
  have h5' : u2.gpr .r5 = u1.gpr .r5 := k2.gpr .r5 (by decide)
  refine WP.mono (statusMask_ok (u := u3) (o := E % 2 ^ 32 % 2) (by omega)
    (fun hb' => by simp only [decide_eq_true_eq] at hb' ⊢; omega)
    ((k3.gpr .r3 (by decide)).trans h23) h312) fun u4 ⟨⟨h45, h412, h43, hm4⟩, k4⟩ => ?_
  rw [h5', status_eq _ _ _ (show (u1.gpr .r5).toNat = 0 ↔ E < 2 ^ 32 by
    rw [← h5]; exact ⟨fun e => BitVec.eq_of_toNat_eq (by rw [e]; rfl), fun e => by rw [e]; rfl⟩)] at h45 h412
  have sp4 : Space (s.gpr .r0) u4 := sp.congr (by rw [k4.wr, k3.wr, k2.wr, hk1.wr]) (by
    rw [k4.gpr .r0 (by decide), k3.gpr .r0 (by decide), k2.gpr .r0 (by decide), hk1.gpr .r0 (by decide)])
  have h41 : u4.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [k4.gpr .r1 (by decide), k3.gpr .r1 (by decide), k2.gpr .r1 (by decide), h1]
  have h44 : u4.gpr .r4 = BitVec.ofNat 32 (E % 2 ^ 32) := by
    rw [k4.gpr .r4 (by decide), k3.gpr .r4 (by decide), k2.gpr .r4 (by decide), h4]
  refine WP.mono (words_ok sp4 h41 h44 h412 h43) fun u5 ⟨hm5, k5⟩ => ?_
  have sp5 : Space (s.gpr .r0) u5 := sp4.congr k5.wr (k5.gpr .r0 (by decide))
  have hmem5 : u5.mem = writeSlots (writeSlots s.mem (State.addr (s.gpr .r0)) (saveList (s.gpr .r4) (s.gpr .r5)))
      (State.addr (s.gpr .r0)) (wordsList (s.gpr .r1).toNat (E % 2 ^ 32) (maskOf (initStatus (s.gpr .r1).toNat E))) := by
    rw [hm5, hm4, hm3, hm2, hs.mem, hm0]; rfl
  obtain ⟨sl3, sl5⟩ := slot_saved s.mem (State.addr (s.gpr .r0)) (s.gpr .r4) (s.gpr .r5) (s.gpr .r1).toNat
    (E % 2 ^ 32) (maskOf (initStatus (s.gpr .r1).toNat E))
  rw [← hmem5] at sl3 sl5
  refine WP.mono (restore_ok sp5 sl3 sl5) fun t ⟨⟨ht0, ht4, ht5, htm⟩, kt⟩ => ⟨?_, ?_, ht4, ht5⟩
  · refine result_post (a := s.gpr .r4) (b := s.gpr .r5) hEdef.symm ?_ ?_
    · rw [ht0, k5.gpr .r5 (by decide), h45]
    · rw [htm, hmem5]; rfl
  · exact ((((hk1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans ((k5.mono (by decide)).trans (kt.mono (by decide)))

/-! ## The contract -/

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k, h4, h5⟩ := init_ok h
  refine ⟨tr, t, he, ⟨fun r hr => ?_, k.sp⟩, hp⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h4
  · exact h5
  all_goals exact k.gpr _ (by decide)

/-- The initial taint: the arguments are public. -/
def initTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false }

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) initTaint (fun s₁ s₂ _ _ hp => ?_) (by taint_decide)
  obtain ⟨_, p0, p1, p2, p3⟩ := hp
  have wf : ∀ s, VG.Arm.Taint.Wf initTaint s := fun s =>
    ⟨(fun h => absurd rfl h), (fun _ h => by simp [initTaint] at h), (fun h => absurd h (by decide)),
      (fun _ h => by simp [initTaint] at h)⟩
  refine ⟨⟨fun r hr => ?_, fun h => by simp [initTaint] at h⟩, (fun h => absurd rfl h), wf s₁, wf s₂,
    (fun _ h => by simp [initTaint] at h), (fun _ h => by simp [initTaint] at h),
    (fun h => absurd h (by decide)), (fun k hk => absurd hk (Nat.not_lt_zero k))⟩
  simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

private def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1024 | .r2 => 0x2000 | .r3 => 3 | _ => 0
  sp := 0x3000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 3⟩]
  wr := [⟨0x1000, 56⟩]

theorem init_verified : Verified target init (Spec.RsaKeyGen.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.RsaKeyGen.keyInitContract, Spec.RsaKeyGen.keyInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs, reduceClassify, Loc.val, State.addr]
      [initSat] using initSat

end VG.Proof.RsaKeyGen.Arm.KeyInit
