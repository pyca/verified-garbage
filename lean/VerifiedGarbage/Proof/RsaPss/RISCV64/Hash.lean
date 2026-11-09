module

-- separate module: it builds in parallel with `Select`, `Shift` and `Cmp`, which `Finish` also needs.

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
public import VerifiedGarbage.Proof.RsaPss.RISCV64.TabCall
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
public import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.MdHashTable.RISCV64
import VerifiedGarbage.Proof.MdStream.RISCV64.Words
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Words64

/-!
# RSASSA-PSS verification on RISC-V: the hash calls, and `H'` for a given salt length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Hash.lean`): `hInit_ok`, `hUpd_ok` and `hFin_ok`,
the calls of the streaming functions through the table of `MdHash` that is
our stack argument `j` (`TabM`) on the state at `S + oSt` (by `initM_ok`,
`updM_ok` and `finM_ok`), `update`'s data in our part of the working space
after the ranges the calls write (`oY` on). `hashFixedG_ok`: `hashFixed`
writes the digest of the `ℓ = 8 + hLen + salt_len` bytes of `M'` at `oY` to
`oDig`. It pads `M'` in place: zeros to the end of its last block `⌊(ℓ + L) /
B⌋`, `0x80` after it and the 64-bit bit count in its last 8 bytes, which is
then the padded message of `M'` (`padded`, `Proof/RsaPss/CtPad.lean`, whose
length field, for the hash functions we support and `M'` this short, is the
64-bit bit count after zeros, `MdL.len`); the table's compression function
compresses its blocks into the initial hash value `init` set, and the
table's digest writes the digest of the hash value after them, which begins
with the hash of `M'` (`MdL.hash`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64 VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa tcall)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_wb view_w8 sc_in sc_inR sc_inW sc_cov sc_w sdis
  cR_dis fx Same hfits offs)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_srl wp_sll wp_sb wp_nil
  fill_ok)
open VG.Proof.MdStream (Md bytes64 bytes64_length)
open VG.Proof.Mgf1 (ifp ifn)

theorem pres_of {rs : List Reg} {t t' : State} (o : Only rs t t') (hrs : ∀ r ∈ rs, r ∉ preserved := by decide) :
    ∀ r ∈ preserved, t'.gpr r = t.gpr r := fun r hr => o.gpr r fun h => hrs r h hr

/-- Bytes of our part of the working space outside the ranges a `Same` covers. -/
theorem bytes_same {S : Addr} {t t' : State} {rgs : List (Nat × Nat)} (h : Same S t t' rgs) {d n : Nat}
    (hd : d + n ≤ oRsa) (hr : ∀ p ∈ rgs, d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    Spec.Sha256.bytesAt t'.mem (off S d) n = Spec.Sha256.bytesAt t.mem (off S d) n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have := h (d + i) (by omega) fun p hp => by have := hr p hp; omega
  simp only [view] at this
  rw [← off_off] at this
  exact this

/-- `Same` for wider ranges. -/
theorem Same.sub {S : Addr} {t t' : State} {rgs rgs' : List (Nat × Nat)} (h : Same S t t' rgs)
    (hs : ∀ p ∈ rgs, ∃ q ∈ rgs', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) : Same S t t' rgs' :=
  fun o ho hr => h o ho fun p hp => by
    obtain ⟨q, hq, h1, h2⟩ := hs p hp
    rcases hr q hq with h' | h' <;> omega

/-- A write of bytes in our part of the working space, of the range `(d, n)`. -/
theorem same_wb {S : Addr} {t t' : State} {d : Nat} {xs : List Byte} (hd : d + xs.length ≤ oRsa)
    (hm : t'.mem = writeBytes t.mem (off S d) xs) {rgs : List (Nat × Nat)}
    (hr : ∃ q ∈ rgs, q.1 ≤ d ∧ d + xs.length ≤ q.1 + q.2) : Same S t t' rgs := fun o ho hs => by
  obtain ⟨q, hq, h1, h2⟩ := hr
  rw [hm, view_wb _ _ hd ho, ifn (by rcases hs q hq with h' | h' <;> omega)]

/-- A write of a byte in our part of the working space, in the range `q`. -/
theorem same_w8 {S : Addr} {t t' : State} {d : Nat} {b : Byte} (hd : d < oRsa)
    (hm : t'.mem = t.mem.writeW (off S d) b) {rgs : List (Nat × Nat)}
    (hr : ∃ q ∈ rgs, q.1 ≤ d ∧ d + 1 ≤ q.1 + q.2) : Same S t t' rgs := fun o ho hs => by
  obtain ⟨q, hq, h1, h2⟩ := hr
  rw [hm, view_w8 _ _ hd ho, ifn (by rcases hs q hq with h' | h' <;> omega)]

theorem off_subN (p : Addr) {a b : Nat} (h : b ≤ a) : off p a - BitVec.ofNat 64 b = off p (a - b) := by
  rw [off, off, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat h]

/-- The first `n` bytes written. -/
theorem bytesAt_wb_take (m : Mem) (q : Addr) (xs : List Byte) {n : Nat} (hn : n ≤ xs.length)
    (hl : xs.length < 2 ^ 64) : Spec.Sha256.bytesAt (writeBytes m q xs) q n = xs.take n := by
  have e : Spec.Sha256.bytesAt (writeBytes m q xs) q n =
      (Spec.Sha256.bytesAt (writeBytes m q xs) q xs.length).take n := by
    simp only [Spec.Sha256.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]
  rw [e]
  exact congrArg (List.take n) (Proof.RsaPkcs1Sig.bytesAt_writeBytes m q xs hl)

/-- The 64-bit word written, as its little-endian bytes. -/
theorem writeW64_eq (m : Mem) (a : Addr) (x : BitVec 64) : m.writeW a x = writeBytes m a (bytes64 false x) := by
  rw [Mem.writeW, write_eq_writeBytes]
  rfl

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (F : Fits S s) {H : Hash}
  {hH : HashOK H} (hF : H.F ≤ 208) {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat} {p : Addr}
  (T : TabM M dN f j S s p)
include F hF T

theorem hInit_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) :
    WP isa (hInit f j) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) []) ∧ t'.syms = s.syms := by
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ => wp_nil fun sy₁ => ?_))
  refine WP.mono (initM_ok T F hF (h.only F o₁) (sy₁.trans sy) (by rw [e₁, h.s0])) fun t' ⟨⟨b, g, sm, r⟩, y⟩ =>
    ⟨⟨b, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr], (Same.of_mem o₁.mem _).trans sm, r⟩, y⟩

theorem hUpd_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {m : List Byte}
    (hr : hH.SH.Repr t.mem (off (S s) oSt) m)
    (h1 : t.gpr .a1 = BitVec.ofNat 64 m.length) {d len : Nat} (h2 : t.gpr .a2 = off (S s) d)
    (h3 : t.gpr .a3 = BitVec.ofNat 64 len) (hd : oY ≤ d) (hl : d + len ≤ oRsa) :
    WP isa (hUpd f j) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧
      hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem (off (S s) d) len)) ∧
      t'.syms = s.syms := by
  have Fh := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hY : oY = 2048 := rfl
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ => wp_nil fun sy₁ => ?_))
  have b₁ := h.only F o₁
  refine WP.mono (updM_ok T F hF b₁ (sy₁.trans sy) (dat := off (S s) d) (len := len) (by rw [e₁, h.s0])
    (by rw [o₁.get .a2, h2]) (by rw [o₁.get .a3, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (Covers.right (by rw [b₁.wr]; exact sc_cov F hl))
    (sdis (.inr (by omega)) hl (by omega)) (cR_dis F hl))
    fun t' ⟨⟨b, g, sm, r⟩, y⟩ => ⟨⟨b, fun r hr => by rw [g r hr, pres_of o₁ (by decide) r hr],
      (Same.of_mem o₁.mem _).trans sm, ?_⟩, y⟩
  have := r m (by rw [o₁.mem]; exact hr) (by rw [o₁.get .a1, h1])
  rwa [o₁.mem] at this

theorem hFin_ok {t : State} (h : Base S vf s t) (sy : t.syms = s.syms) {m : List Byte}
    (hr : hH.SH.Repr t.mem (off (S s) oSt) m)
    (h1 : t.gpr .a1 = BitVec.ofNat 64 m.length) (hm : m.length < 2 ^ 64) :
    WP isa (hFin f j) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D = hH.SH.H.hash m) ∧ t'.syms = s.syms := by
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) (h := by decide) fun t₁ o₁ e₁ =>
    wp_addi (imm := oDig) (h := by decide) fun t₂ o₂ e₂ => wp_nil fun sy₂ => ?_))
  have k₂ : Only [.a0, .a2] t t₂ := (o₁.trans o₂).mono
  have b₂ := h.only F k₂
  refine WP.mono (finM_ok T F hF b₂ (sy₂.trans sy) (by rw [o₂.get .a0, e₁, h.s0]) (by rw [e₂, o₁.get .s0, h.s0]))
    fun t' ⟨⟨b, g, sm, r⟩, y⟩ =>
    ⟨⟨b, fun r hr => by rw [g r hr, pres_of k₂ (by decide) r hr], (Same.of_mem k₂.mem _).trans sm,
      r m (by rw [k₂.mem]; exact hr) hm (by rw [k₂.get .a1, h1])⟩, y⟩

end

/-! ## The padding of a message of a public length -/

/-- The bytes of the blocks of the padding of a message of `ℓ` bytes, with a
length field of `L` bytes. -/
abbrev padB (B L ℓ : Nat) : Nat := B * ((ℓ + L) / B + 1)

theorem padB_bounds {B L ℓ : Nat} (hB : 0 < B) :
    ℓ + L + 1 ≤ padB B L ℓ ∧ padB B L ℓ ≤ ℓ + L + B := by
  have e := Nat.div_add_mod (ℓ + L) B
  have hr := Nat.mod_lt (ℓ + L) hB
  unfold padB
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- `padLen`: `t2 := ℓ`, `t3 := padB B L ℓ`. -/
theorem padLen_ok {H : Hash} (hb : H.b = 6 ∨ H.b = 7) (hD : H.D ≤ 64) {sl : Nat} (hsl : 8 + H.D + sl ≤ 2048)
    {t : State} (h6 : t.gpr .s6 = BitVec.ofNat 64 sl) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Only [.t2, .t3] t t' → t'.gpr .t2 = BitVec.ofNat 64 (8 + H.D + sl) →
      t'.gpr .t3 = BitVec.ofNat 64 (padB H.B (H.B / 8) (8 + H.D + sl)) → WP isa (.block is) t' Q) :
    WP isa (.block (padLen H ++ is)) t Q := by
  have hB : H.B = 2 ^ H.b := rfl
  have hB' : H.B = 64 ∨ H.B = 128 := by rcases hb with e | e <;> simp [hB, e]
  have hL : H.B / 8 < 2048 := by rcases hB' with e | e <;> rw [e] <;> decide
  have hb64 : H.b < 64 := by omega
  simp only [padLen, List.cons_append, List.nil_append]
  refine wp_addi (imm := 8 + H.D) (h := by omega) fun t₁ o₁ e₁ => wp_addi (imm := H.B / 8) (h := hL)
    fun t₂ o₂ e₂ => wp_srl (sh := H.b) (h := hb64) fun t₃ o₃ e₃ => wp_addi (imm := 1) fun t₄ o₄ e₄ =>
    wp_sll (sh := H.b) (h := hb64) fun t₅ o₅ e₅ => k t₅ (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono ?_ ?_
  · rw [o₅.get .t2, o₄.get .t2, o₃.get .t2, o₂.get .t2, e₁, h6, BitVec.ofNat_add_ofNat]; congr 1; omega
  · have hl : 8 + H.D + sl + H.B / 8 < 2 ^ 64 := by rcases hB' with e | e <;> rw [e] <;> omega
    have q : (t₃.gpr .t3).toNat = (8 + H.D + sl + H.B / 8) / H.B := by
      rw [e₃, e₂, e₁, h6, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ushiftRight,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, ← hB]
      congr 1; omega
    apply BitVec.eq_of_toNat_eq
    rw [e₅, e₄, BitVec.toNat_shiftLeft, BitVec.toNat_add, q, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, ← hB]
    have hq : (8 + H.D + sl + H.B / 8) / H.B + 1 < 2 ^ 64 := by
      have := Nat.div_le_self (8 + H.D + sl + H.B / 8) H.B; omega
    have hp : padB H.B (H.B / 8) (8 + H.D + sl) < 2 ^ 64 := by
      have := padB_bounds (ℓ := 8 + H.D + sl) (B := H.B) (L := H.B / 8) (by omega)
      omega
    rw [Nat.mod_eq_of_lt (a := 1) (by decide), Nat.mod_eq_of_lt hq, Nat.mul_comm, Nat.mod_eq_of_lt hp]

/-- The length field's 8 bytes, big-endian if `be`, little-endian if not. -/
theorem storeLen_ok (be : Bool) {t : State} (hw : InRegions t.wr (t.gpr .a1) 8)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Kept [.t4, .t5] t t' → t'.mem = writeBytes t.mem (t.gpr .a1) (bytes64 be (t.gpr .t1)) →
      WP isa (.block is) t' Q) :
    WP isa (.block ((if be then Impl.Words.RISCV64.storeBE 8 .t1 .t4 .a1 0 else
      Impl.Words64.RISCV64.storeLE64 .t1 .t4 .t5 .a1 0) ++ is)) t Q := by
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    rw [WP.block_append_iff]
    have hw8 : InRegions t.wr (t.gpr .a1 + BitVec.ofNat 64 0) 8 := by rw [BitVec.add_zero]; exact hw
    refine WP.mono (Words64.storeLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide) hw8)
      fun t' ⟨g, m, rd, wr, sp⟩ => k t' ⟨fun r hr => g r (fun e => hr (by rw [e]; decide))
        (fun e => hr (by rw [e]; decide)), rd, wr, sp⟩ (by rw [m, BitVec.add_zero, writeW64_eq])
  · simp only [ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (ByteLoad.storeBE_ok (by decide) (by decide) (by decide) (by decide) (by decide)
      fun j hj => by
        obtain ⟨R, hR, hc⟩ := hw
        exact ⟨R, hR, by rw [Nat.zero_add]; exact MdStream.RISCV64.contains_add hc (by omega)⟩) fun t' e => ?_
    subst e
    refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => hr (by rw [e]; decide))]
    · rw [RegUpd.mem_write]
      show writeBytes t.mem (t.gpr .a1 + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 (t.gpr .t1)) = _
      rw [BitVec.add_zero, MdHashTable.RISCV64.beBytes_dword]

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (F : Fits S s) {H : Hash}
  {hH : HashOK H} (M : MdL H hH)
include F

/-- `padAll`, for `M'`'s `ℓ = 8 + hLen + sl` bytes at `oY` (`sl` in `s6`): its
blocks' padding after it, and the compression function's arguments; it
writes only `oY` on. -/
theorem padAll_ok {sl : Nat} {t : State} (h6 : t.gpr .s6 = BitVec.ofNat 64 sl) (h : Base S vf s t)
    (hsl : 8 + H.D + sl ≤ 1880) :
    WP isa (padAll H M.be) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oY, 2048)] ∧ t'.gpr .a0 = off (S s) oSt ∧ t'.gpr .a1 = off (S s) oY ∧
      t'.gpr .a2 = BitVec.ofNat 64 ((8 + H.D + sl + M.L) / H.B + 1) ∧ t'.gpr .a3 = off (S s) oCs ∧
      (∀ i < padB H.B M.L (8 + H.D + sl), view t'.mem (S s) (oY + i) =
        Proof.RsaPss.padded H.B M.L (Spec.Sha256.bytesAt t.mem (off (S s) oY) (8 + H.D + sl))
          (M.md.lenBytes (8 + H.D + sl)) i) ∧
      ∀ i < H.N, view t'.mem (S s) (oSt + i) = view t.mem (S s) (oSt + i) := by
  have Fh := hfits hH
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  have hCs : oCs = 1664 := rfl
  obtain ⟨_, hSt, hDg, _, _⟩ := offs
  have hD64 := hH.hD64
  have hN := hH.hN
  obtain ⟨hL, hL8⟩ := M.hL
  have hb := hH.hb
  have hB : H.B = 2 ^ H.b := rfl
  have hB' : H.B = 64 ∨ H.B = 128 := by rcases hb with e | e <;> simp [hB, e]
  have hLB : M.L < H.B := by rcases hB' with e | e <;> rw [hL, e] <;> decide
  have hB0 : 0 < H.B := by omega
  generalize hl : 8 + H.D + sl = ℓ at hsl ⊢
  have hpb := padB_bounds (ℓ := ℓ) (L := M.L) hB0
  generalize hP : padB H.B M.L ℓ = P at hpb ⊢
  have hP' : padB H.B (H.B / 8) (8 + H.D + sl) = P := by rw [← hL, hl, hP]
  let msg := Spec.Sha256.bytesAt t.mem (off (S s) oY) ℓ
  -- The sizes.
  refine WP.seq (WP.of_syms (padLen_ok hb hD64 (sl := sl) (by omega) h6 fun t₂ o₂ e₂ e₃ => wp_nil fun _ => ?_))
  rw [hl] at e₂
  rw [hP'] at e₃
  have b₂ := h.only F o₂
  -- Zeros after `M'`.
  refine WP.seq (WP.seq (Proof.RsaPss.RISCV64.wp_yBase (by rw [o₂.get .s0, h.s0]) fun t₃ o₃ e₃' =>
    wp_add fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_li (imm := 0) (by decide) fun t₆ o₆ e₆ => wp_nil ?_))
  have k₆ : Only [.a1, .t5, .t0] t₂ t₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have g6a1 : t₆.gpr .a1 = off (S s) (oY + ℓ) := by
    rw [o₆.get .a1, o₅.get .a1, e₄, e₃', o₃.get .t2, e₂]; exact off_off _ _ _
  have g6t5 : t₆.gpr .t5 = BitVec.ofNat 64 (P - ℓ) := by
    rw [o₆.get .t5, e₅, o₄.get .t3, o₃.get .t3, e₃, o₄.get .t2, o₃.get .t2, e₂, Offset.ofNat_sub_ofNat (by omega)]
  refine WP.mono (fill_ok (p := off (S s) (oY + ℓ)) (n := P - ℓ) (b := 0) (by omega) (by omega) g6a1 g6t5
    (by rw [e₆]; rfl) (sc_w F (by rw [k₆.wr, b₂.wr]) (d := oY + ℓ) (by omega))) fun t₇ ⟨k₇, m₇⟩ => ?_
  have K₇ : Kept [.a1, .t5, .t0] t₂ t₇ := (k₆.keep.trans k₇).mono
  have m₇' : t₇.mem = writeBytes t₂.mem (off (S s) (oY + ℓ)) (List.replicate (P - ℓ) 0) := by rw [m₇, k₆.mem]
  have b₇ := b₂.wb F K₇ (by rw [List.length_replicate]; omega) m₇'
  -- `0x80`, the length field and the compression function's arguments.
  have t2₇ : t₇.gpr .t2 = BitVec.ofNat 64 ℓ := by rw [K₇.get .t2, e₂]
  have t3₇ : t₇.gpr .t3 = BitVec.ofNat 64 P := by rw [K₇.get .t3, e₃]
  have s0₇ : t₇.gpr .s0 = S s := b₇.s0
  simp only [padEnd, compArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine Proof.RsaPss.RISCV64.wp_yBase s0₇ fun t₈ o₈ e₈ => wp_add fun t₉ o₉ e₉ =>
    wp_li (imm := 0x80) (by decide) fun t₁₀ o₁₀ e₁₀ => ?_
  have k₁₀ : Only [.a1, .t1] t₇ t₁₀ := (o₈.trans (o₉.trans o₁₀)).mono
  have a1₁₀ : t₁₀.gpr .a1 = off (S s) (oY + ℓ) := by
    rw [o₁₀.get .a1, e₉, e₈, o₈.get .t2, t2₇]; exact off_off _ _ _
  refine wp_sb (a := off (S s) (oY + ℓ)) (by rw [a1₁₀, BitVec.add_zero])
    (by rw [k₁₀.wr, b₇.wr]; exact sc_inW F (by omega)) fun t₁₁ m₁₁ => ?_
  have hm₁₁ : t₁₁.mem = t₇.mem.writeW (off (S s) (oY + ℓ)) (0x80 : Byte) := by
    rw [m₁₁.mem, e₁₀, k₁₀.mem]; rfl
  have K₁₁ : Kept [.a1, .t1] t₇ t₁₁ := (k₁₀.keep.trans m₁₁.keep).mono
  have b₁₁ : Base S vf s t₁₁ := b₇.keep F K₁₁ (R := [⟨off (S s) (oY + ℓ), 1⟩]) (by
      rw [hm₁₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega)))
  refine Proof.RsaPss.RISCV64.wp_yBase (by rw [b₁₁.s0]) fun t₁₂ o₁₂ e₁₂ => wp_add fun t₁₃ o₁₃ e₁₃ =>
    wp_subi (imm := 8) fun t₁₄ o₁₄ e₁₄ => wp_sll (sh := 3) fun t₁₅ o₁₅ e₁₅ => ?_
  have k₁₅ : Only [.a1, .t1] t₁₁ t₁₅ := (o₁₂.trans (o₁₃.trans (o₁₄.trans o₁₅))).mono
  have a1₁₅ : t₁₅.gpr .a1 = off (S s) (oY + P - 8) := by
    rw [o₁₅.get .a1, e₁₄, e₁₃, e₁₂, o₁₂.get .t3, K₁₁.get .t3, t3₇, ← off, off_off, off_subN _ (by omega)]
  have t1₁₅ : t₁₅.gpr .t1 = BitVec.ofNat 64 (8 * ℓ) := by
    rw [e₁₅, o₁₄.get .t2, o₁₃.get .t2, o₁₂.get .t2, K₁₁.get .t2, t2₇]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show ℓ < 2 ^ 64 by omega)]
    congr 1; omega
  refine storeLen_ok M.be (by rw [a1₁₅, k₁₅.wr, K₁₁.wr, b₇.wr]; exact sc_inW F (by omega)) fun t₁₆ k₁₆ m₁₆ => ?_
  rw [a1₁₅, t1₁₅] at m₁₆
  have K₁₆ : Kept [.a1, .t1, .t4, .t5] t₁₁ t₁₆ := (k₁₅.keep.trans k₁₆).mono
  have hm₁₆ : t₁₆.mem = writeBytes t₁₁.mem (off (S s) (oY + P - 8)) (bytes64 M.be (BitVec.ofNat 64 (8 * ℓ))) := by
    rw [m₁₆, k₁₅.mem]
  have b₁₆ : Base S vf s t₁₆ := b₁₁.wb F K₁₆ (by rw [bytes64_length]; omega) hm₁₆
  refine wp_addi (imm := oSt) (h := by decide) fun t₁₇ o₁₇ e₁₇ => Proof.RsaPss.RISCV64.wp_yBase
    (by rw [o₁₇.get .s0, b₁₆.s0]) fun t₁₈ o₁₈ e₁₈ => wp_srl (sh := H.b) (h := by omega) fun t₁₉ o₁₉ e₁₉ =>
    wp_addi (imm := oCs) (h := by decide) fun t₂₀ o₂₀ e₂₀ => wp_nil ?_
  have k₂₀ : Only [.a0, .a1, .a2, .a3] t₁₆ t₂₀ := (o₁₇.trans (o₁₈.trans (o₁₉.trans o₂₀))).mono
  have hnb : P / H.B = (ℓ + M.L) / H.B + 1 := by rw [← hP]; exact Nat.mul_div_cancel_left _ hB0
  refine ⟨b₁₆.only F k₂₀, fun r hr => ?_, ?_, by rw [o₂₀.get .a0, o₁₉.get .a0, o₁₈.get .a0, e₁₇, b₁₆.s0],
    by rw [o₂₀.get .a1, o₁₉.get .a1, e₁₈], ?_, by rw [e₂₀, o₁₉.get .s0, o₁₈.get .s0, o₁₇.get .s0, b₁₆.s0],
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [k₂₀.gpr r (by revert r; decide), K₁₆.gpr r (by revert r; decide), K₁₁.gpr r (by revert r; decide),
      K₇.gpr r (by revert r; decide), o₂.gpr r (by revert r; decide)]
  · have hR' : ∃ q ∈ [(oY, 2048)], q.1 ≤ oY + ℓ ∧ oY + ℓ + 1 ≤ q.1 + q.2 :=
      ⟨(oY, 2048), by simp, by simp only; omega, by simp only; omega⟩
    exact ((((Same.of_mem o₂.mem _).trans
      (same_wb (by rw [List.length_replicate]; omega) m₇' ⟨(oY, 2048), by simp, by simp only; omega,
        by simp only [List.length_replicate]; omega⟩)).trans (same_w8 (by omega) hm₁₁ hR')).trans
      (same_wb (by rw [bytes64_length]; omega) hm₁₆ ⟨(oY, 2048), by simp, by simp only; omega,
        by simp only [bytes64_length]; omega⟩)).trans (Same.of_mem k₂₀.mem _)
  · rw [o₂₀.get .a2, e₁₉, o₁₈.get .t3, o₁₇.get .t3, K₁₆.get .t3, K₁₁.get .t3, t3₇]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, ← hB, hnb, Nat.mod_eq_of_lt (by have := Nat.div_le_self (ℓ + M.L) H.B; omega)]
  · -- The padded message in memory.
    have hml : msg.length = ℓ := by simp [msg, Spec.Sha256.bytesAt]
    have hmg : ∀ i < ℓ, msg.getD i 0 = view t.mem (S s) (oY + i) := fun i hi => by
      simp only [msg, Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some, view]
      rw [← off_off]
    have hPB : H.B * Proof.RsaPss.lastBlk H.B M.L ℓ + H.B = P := by
      rw [← hP]; unfold padB Proof.RsaPss.lastBlk; rw [Nat.mul_add, Nat.mul_one]
    have hlen := M.len ℓ (by omega)
    show view t₂₀.mem (S s) (oY + i) = Proof.RsaPss.padded H.B M.L msg (M.md.lenBytes ℓ) i
    rw [k₂₀.mem, hm₁₆, view_wb _ _ (by rw [bytes64_length]; omega) (by omega), bytes64_length, hm₁₁,
      view_w8 _ _ (by omega) (by omega), m₇', view_wb _ _ (by rw [List.length_replicate]; omega) (by omega),
      List.length_replicate, Proof.RsaPss.padded, hml, hlen, Proof.RsaPss.getD_app, List.length_replicate]
    simp only [o₂.mem]
    generalize H.B * Proof.RsaPss.lastBlk H.B M.L ℓ = Q at hPB ⊢
    have z : ∀ n k, k < n → (List.replicate n (0 : Byte)).getD k 0 = 0 := fun n k hk => by
      simp [List.getD_eq_getElem?_getD, hk]
    by_cases h₁ : i < ℓ
    · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifp h₁, hmg i h₁]
    · by_cases h₂ : i = ℓ
      · subst h₂; rw [ifn (by omega), ifp rfl, ifn (Nat.lt_irrefl _), ifp rfl]
      · by_cases h₃ : P - 8 ≤ i
        · rw [ifp ⟨by omega, by omega⟩, ifn h₁, ifn h₂, ifp ⟨by omega, by omega⟩, ifn (by omega)]
          congr 1; omega
        · rw [ifn (by omega), ifn (by omega), ifp ⟨by omega, by omega⟩, ifn h₁, ifn h₂, z _ _ (by omega)]
          by_cases h₄ : Q + H.B - M.L ≤ i ∧ i < Q + H.B
          · rw [ifp h₄, ifp (by omega), z _ _ (by omega)]
          · rw [ifn h₄]
  · -- The hash value.
    rw [k₂₀.mem, hm₁₆, view_wb _ _ (by rw [bytes64_length]; omega) (by omega), ifn (by omega), hm₁₁,
      view_w8 _ _ (by omega) (by omega), ifn (by omega), m₇', view_wb _ _ (by rw [List.length_replicate]; omega)
      (by omega), ifn (by omega), o₂.mem]

end

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (F : Fits S s) {H : Hash}
  {hH : HashOK H} (hF : H.F ≤ 208) {M : MdL H hH} {dN : String} {f : MdFns} {j : Nat} {p : Addr}
  (T : TabM M dN f j S s p)
include F hF T

/-- `hashFixed`, for a salt length `sl` in `s6`. -/
theorem hashFixedG_ok (hal : (S s).toNat % 8 = 0) {D : Nat} (hD : H.D = D) {sl : Nat} {t : State}
    (h6 : t.gpr .s6 = BitVec.ofNat 64 sl) (h : Base S vf s t) (sy : t.syms = s.syms)
    (hsl : 8 + D + sl ≤ 1880) :
    WP isa (hashFixed H M.be f j) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, 64), (oCs, 144), (oY, 2048)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D =
        hH.SH.H.hash (Spec.Sha256.bytesAt t.mem (off (S s) oY) (8 + D + sl))) ∧ t'.syms = s.syms := by
  have Fh := hfits hH
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  have hCs : oCs = 1664 := rfl
  obtain ⟨_, hSt, hDg, _, _⟩ := offs
  have hD64 := hH.hD64
  have hN := hH.hN
  have hDN := M.hDN
  obtain ⟨hL, hL8⟩ := M.hL
  have hb := hH.hb
  have hB : H.B = 2 ^ H.b := rfl
  have hB' : H.B = 64 ∨ H.B = 128 := by rcases hb with e | e <;> simp [hB, e]
  have hLB : M.L < H.B := by rcases hB' with e | e <;> rw [hL, e] <;> decide
  have hB0 : 0 < H.B := by omega
  subst hD
  generalize hl : 8 + H.D + sl = ℓ at hsl
  have hpb := padB_bounds (ℓ := ℓ) (L := M.L) hB0
  generalize hP : padB H.B M.L ℓ = P at hpb
  -- `init`.
  refine WP.seq (WP.mono (hInit_ok F hF T h sy) fun t₁ ⟨⟨b₁, g₁, s₁, r₁⟩, y₁⟩ => ?_)
  have iv₁ : M.md.stateAt t₁.mem (off (S s) oSt) = M.iv := M.init _ _ r₁
  have em : Spec.Sha256.bytesAt t₁.mem (off (S s) oY) ℓ = Spec.Sha256.bytesAt t.mem (off (S s) oY) ℓ :=
    bytes_same s₁ (by omega) fun q hq => by simp at hq; subst hq; simp only; omega
  -- The padding.
  refine WP.seq (WP.mono_syms (padAll_ok F M (sl := sl) (by rw [g₁ _ (by decide), h6]) b₁ (by omega))
    fun t₂₀ ⟨b₂₀, g₂₀, s₂₀, x0, x1, x2, x3, vY, vS⟩ sy₂₀ => ?_)
  rw [hl] at x2 vY
  rw [hP, em] at vY
  -- The compression function.
  refine WP.seq (WP.mono (compM_ok T F hal b₂₀ (sy₂₀.trans y₁) (o := oY) (n := (ℓ + M.L) / H.B + 1) x0 x1 x2 x3
    (by omega) (by have := hP; unfold padB at this; omega))
    fun t₂₁ ⟨⟨b₂₁, g₂₁, s₂₁, c₂₁⟩, y₂₁⟩ => ?_)
  -- The digest.
  refine WP.seq (WP.of_syms (wp_addi (imm := oSt) (h := by decide) fun t₂₂ o₂₂ e₂₂ =>
    wp_addi (imm := oDig) (h := by decide) fun t₂₃ o₂₃ e₂₃ => wp_nil fun sy₂₃ => ?_))
  have k₂₃ : Only [.a0, .a1] t₂₁ t₂₃ := (o₂₂.trans o₂₃).mono
  refine WP.mono (digM_ok T F (b₂₁.only F k₂₃) (sy₂₃.trans y₂₁) (by rw [o₂₃.get .a0, e₂₂, b₂₁.s0])
    (by rw [e₂₃, o₂₂.get .s0, b₂₁.s0])) fun t' ⟨⟨b', g', s', m'⟩, y'⟩ => ⟨⟨b', ?_, ?_, ?_⟩, y'⟩
  · intro r hr
    rw [g' r hr, k₂₃.gpr r (by revert r; decide), g₂₁ r hr, g₂₀ r hr, g₁ r hr]
  · refine ((((Same.sub s₁ fun q hq => ?_).trans (Same.sub s₂₀ fun q hq => ?_)).trans
      (Same.sub s₂₁ fun q hq => ?_)).trans (Same.of_mem k₂₃.mem _)).trans (Same.sub s' fun q hq => ?_)
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨(oSt, H.S), by simp, by simp, by simp⟩
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨(oY, 2048), by simp, by simp, by simp⟩
    · have := M.hcs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨(oSt, H.S), by simp, by simp, by simp only [Hash.S]; omega⟩
      · exact ⟨(oCs, 144), by simp, by simp, by simp only; omega⟩
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨(oDig, 64), by simp, by simp, by simp only; omega⟩
  · -- The message.
    let msg := Spec.Sha256.bytesAt t.mem (off (S s) oY) ℓ
    have hml : msg.length = ℓ := by simp [msg, Spec.Sha256.bytesAt]
    -- The hash value after the blocks.
    have sY : ∀ i < H.N, t₂₀.mem (off (S s) oSt + BitVec.ofNat 64 i) =
        t₁.mem (off (S s) oSt + BitVec.ofNat 64 i) := by
      intro i hi
      rw [show off (S s) oSt + BitVec.ofNat 64 i = off (S s) (oSt + i) from off_off _ _ _]
      exact vS i hi
    have iv₂₀ : M.md.stateAt t₂₀.mem (off (S s) oSt) = M.iv := (M.md.stateAt_congr sY).trans iv₁
    have hc : M.md.compressBlocks M.iv t₂₀.mem (off (S s) oY) ((ℓ + M.L) / H.B + 1) =
        M.md.compressList M.iv (M.md.pad msg) ((M.md.pad msg).length / H.B) := by
      rw [Proof.RsaPss.pad_length M.md msg hB0 hLB, hml, Nat.mul_div_cancel_left _ hB0]
      refine M.md.compressBlocks_eq fun i hi => ?_
      rw [Proof.RsaPss.pad_getD M.md msg hB0 hLB (by rw [hml]; unfold Proof.RsaPss.lastBlk; exact hi), hml,
        ← vY i (by rw [← hP]; exact hi)]
      show t₂₀.mem (off (off (S s) oY) i) = view t₂₀.mem (S s) (oY + i)
      rw [off_off]; rfl
    have hdl := M.md.digest_length (M.md.stateAt t₂₃.mem (off (S s) oSt))
    rw [m', bytesAt_wb_take _ _ _ (by omega) (by omega), k₂₃.mem, c₂₁, iv₂₀, hc, M.hash]
    subst hl; rfl

end

end VG.Proof.RsaPss.RISCV64
