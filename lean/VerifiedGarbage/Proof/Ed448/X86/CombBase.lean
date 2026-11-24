module

public import VerifiedGarbage.Proof.Ed448.SignedComb
public import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86.BaseMain
public import VerifiedGarbage.Proof.Ed448.X86.CombTbl
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.X448.X86.Ops
import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
import VerifiedGarbage.Proof.Ed448.X86.VerifyField
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Iter

/-!
# edwards448's comb on x86 (32-bit)

`digitLoad_ok` and `selectT_ok`: from the scalar's bits (a byte each at `BITS`), the entry of
table `esi = j` of the magnitude of the digit whose nibble's bits are at
`BITS + o` into slots 8 and 9, scanning all eight (and the neutral point, entry
0): the nibble by Horner's rule (`nibble_ok`), its digit's magnitude
(`magnitude_ok`), the table's address (`tblPtr_ok`), and each entry's words,
halves of the static's 64-bit words (`tbl_word`), ORed in under the mask of its
index being the magnitude.

One digit (`digitAdd_ok`): that entry, its `x` negated for a negative digit (`negSel_ok`), and added to an accumulator by the field program
`addAff`, which evaluates to `affAdd`. A step (`combStep_ok`) adds both digits of
table `esi`; the loop (`combLoop_ok`) leaves the accumulators as `signedSum k 1
57` and `signedSum k 0 57` (`Proof/Ed448/SignedComb.lean`), and `combFinish_ok`
their combination, `signedComb k`, in slots 0–2.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double pt affAdd signedEntry signedSum signedComb addWith)
open VG.Proof.X448 (nib nib_lt nib_bits mag mag_lt negAff)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.Ed448.X86 (toOp field combSym TPTR digitPtr digitLoad negSel addAff digitAdd combStep combLoop
  double4 copyC combFinish tblSetup combBase takeOps combWord combWords nibble magnitude tblPtr selWordT
  selCoordT selEntryT selectT selMask zeroSlot)
open VG.Impl.X448.X86 (BITS slot ACC ld st sc at_ cswap)
open VG.Proof.X25519.X86 (num num_congr)

/-! ## The tables -/

/-- Coordinate `c` of an entry: `x` or `y`. -/
def coord (c : Nat) (e : Spec.X448.Fe × Spec.X448.Fe) : Nat := if c = 0 then e.1.val else e.2.val

theorem setWidth_ofNat64 (n : Nat) : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem extract_ofNat64 (n : Nat) :
    (BitVec.ofNat 64 n).extractLsb' 32 32 = BitVec.ofNat 32 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem combWord_eq {j c m k : Nat} (hc : c < 2) (hm : m < 8) (hk : k < 7) :
    combWord (112 * j + 56 * c + 7 * m + k) =
      BitVec.ofNat 64 (coord c (Impl.X448.baseTable j (m + 1)) / 2 ^ (64 * k)) := by
  have e1 : (112 * j + 56 * c + 7 * m + k) / 112 = j := by omega_using [hc, hm, hk]
  have e2 : (112 * j + 56 * c + 7 * m + k) % 56 / 7 = m := by omega_using [hc, hm, hk]
  have e3 : (112 * j + 56 * c + 7 * m + k) % 112 = 56 * c + 7 * m + k := by omega_using [hc, hm, hk]
  have e4 : (112 * j + 56 * c + 7 * m + k) % 7 = k := by omega_using [hc, hm, hk]
  simp only [combWord, e1, e2, e3, e4]
  rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
  · simp only [coord, show 56 * 0 + 7 * m + k < 56 by omega_using [hm, hk], ↓reduceIte]
  · simp only [coord, show ¬ 56 * 1 + 7 * m + k < 56 by omega_using [hm, hk], ↓reduceIte, Nat.one_ne_zero]

/-- Word `w` (of 32 bits) of coordinate `c` of entry `m + 1` of table `j`, in the static's words at
`T`. -/
theorem tbl_word {mem : Mem} {T : Addr} (h : TblWords T mem) {j c m w : Nat} (hj : j < 57)
    (hc : c < 2) (hm : m < 8) (hw : w < 14) :
    mem.readW (T + BitVec.ofNat 64 (896 * j + 448 * c + 56 * m + 4 * w)) 32 =
      BitVec.ofNat 32 (coord c (Impl.X448.baseTable j (m + 1)) / 2 ^ (32 * w)) := by
  obtain ⟨k, hk⟩ : ∃ k, w = 2 * k ∨ w = 2 * k + 1 := ⟨w / 2, by omega_using []⟩
  have hi : 112 * j + 56 * c + 7 * m + k < combWords.length := by
    rw [combWords_length]; omega_using [hj, hc, hm, hw, hk]
  have h64 := h _ hi
  rw [combWords_getD (by omega_using [hj, hc, hm, hw, hk]), combWord_eq hc hm (by omega_using [hw, hk])] at h64
  rcases hk with rfl | rfl
  · rw [show 896 * j + 448 * c + 56 * m + 4 * (2 * k) = 8 * (112 * j + 56 * c + 7 * m + k) by omega_using [],
      Mem.readW_lo32 h64, setWidth_ofNat64, show 32 * (2 * k) = 64 * k by omega_using []]
  · rw [show 896 * j + 448 * c + 56 * m + 4 * (2 * k + 1) = 8 * (112 * j + 56 * c + 7 * m + k) + 4 by omega_using [],
      ← Offset.add_add, Mem.readW_hi32 h64, extract_ofNat64, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 32 * (2 * k + 1) = 64 * k + 32 by omega_using []]

/-- The comb's tables at `P`: in 32-bit memory, readable, their words, apart from what the code
writes. -/
structure TblMem (P : BitVec 32) (s : State) : Prop where
  fit : P.toNat + 8 * combWords.length ≤ 2 ^ 32
  rd : TblR (P.setWidth 64) ∈ s.rd
  words : TblWords (P.setWidth 64) s.mem
  far : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20], (TblR (P.setWidth 64)).Disjoint r

/-- The comb's tables at `P`, whose address is at `TPTR`. -/
structure TblAt (base : Addr) (P : BitVec 32) (s : State) : Prop extends TblMem P s where
  ptr : word s.mem base TPTR = P

/-- The tables survive code that uses at most 20 bytes of stack. -/
theorem TblMem.frame {P : BitVec 32} {s t : State} (h : TblMem P s)
    (hsp : t.gpr .esp = s.gpr .esp) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hf : Frame (s.wr ++ [below (s.gpr .esp) 20]) s.mem t.mem) : TblMem P t :=
  ⟨h.fit, hr ▸ h.rd, h.words.frame hf h.far, by rw [hsp, hw]; exact h.far⟩

theorem TblAt.frame {base : Addr} {P : BitVec 32} {s t : State} (h : TblAt base P s)
    (hsp : t.gpr .esp = s.gpr .esp) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hf : Frame (s.wr ++ [below (s.gpr .esp) 20]) s.mem t.mem)
    (hp : word t.mem base TPTR = word s.mem base TPTR) : TblAt base P t :=
  ⟨h.toTblMem.frame hsp hr hw hf, hp.trans h.ptr⟩

/-- The words `V` at `a + c`, readable and beyond the working space. -/
def Cands (base : Addr) (a : BitVec 32) (c : Nat) (V : Nat → Nat) (s : State) : Prop :=
  ∀ j < 14, InRegions (s.rd ++ s.wr) (addr a (c + 4 * j)) 4 ∧
    (∀ i < 4, 8192 ≤ ofs base (addr a (c + 4 * j) + BitVec.ofNat 64 i)) ∧
    s.mem.readW (addr a (c + 4 * j)) 32 = BitVec.ofNat 32 (V j)

theorem Cands.keep {base : Addr} {a : BitVec 32} {c : Nat} {V : Nat → Nat} {s t : State}
    (h : Cands base a c V s) {o n : Nat} (hn : o + n ≤ 8192) (ho : Outside base o n s.mem t.mem)
    {rs : List Reg} (hk : Keeps rs s t) : Cands base a c V t := fun j hj => by
  obtain ⟨h1, h2, h3⟩ := h j hj
  refine ⟨by rw [hk.2.1, hk.2.2]; exact h1, h2, ?_⟩
  rw [← h3]
  exact Mem.readW_congr fun i hi => ho _ (Or.inr (Nat.le_trans hn (h2 i hi)))

/-- The words of coordinate `c` of entry `m + 1` of table `j`, whose address is `P + 896 j`. -/
theorem TblAt.cands {base : Addr} {P : BitVec 32} {s : State} (h : TblAt base P s) (hs : Scr s base) {j c m : Nat}
    (hj : j < 57) (hc : c < 2) (hm : m < 8) :
    Cands base (P + BitVec.ofNat 32 (896 * j)) (448 * c + 56 * m)
      (fun w => coord c (Impl.X448.baseTable j (m + 1)) / 2 ^ (32 * w)) s := fun w hw => by
  have hf := h.fit
  have hl := combWords_length
  have hd : (TblR (P.setWidth 64)).Disjoint ⟨base, 8192⟩ := h.far _ (List.mem_append_left _ hs.wr)
  have e : addr (P + BitVec.ofNat 32 (896 * j)) (448 * c + 56 * m + 4 * w) =
      P.setWidth 64 + BitVec.ofNat 64 (896 * j + 448 * c + 56 * m + 4 * w) := by
    have e : 896 * j + (448 * c + 56 * m + 4 * w) = 896 * j + 448 * c + 56 * m + 4 * w := by omega_using []
    rw [addr, Offset.add_add, e]
    exact addr_eq (by omega_using [hf, hl, hj, hc, hm, hw])
  rw [e]
  refine ⟨⟨_, List.mem_append_left _ h.rd, Offset.contains_base _ (by omega_using [hl, hj, hc, hm, hw])
    (by omega_using [hj, hc, hm, hw])⟩, fun i hi => ?_, tbl_word h.words hj hc hm hw⟩
  rw [Offset.add_add]
  exact VG.Proof.Ed448.X86.far hd (by omega_using [hl, hj, hc, hm, hw, hi]) (by omega_using [hl])

/-! ## The digit -/

theorem add_ofNat (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add _ _).symm

/-- `ebp = edi + 8 j`. -/
theorem digitPtr_ok (s : State) {j : Nat} (hj : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block digitPtr) s fun t =>
      t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (8 * j) ∧ Keeps [.ebp] s t ∧ t.mem = s.mem := by
  unfold digitPtr
  refine wp_mov rfl fun u1 v1 => ?_
  have e1 : u1.gpr .ebp = BitVec.ofNat 32 j := by rw [v1.gpr, hj]
  refine wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  have e2 : u2.gpr .ebp = BitVec.ofNat 32 (2 * j) := by
    rw [v2.gpr]; change u1.gpr .ebp + u1.gpr .ebp = _
    rw [e1, add_ofNat]; exact congrArg _ (by omega_using [])
  refine wp_alu (Or.inl rfl) rfl fun u3 v3 _ => ?_
  have e3 : u3.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
    rw [v3.gpr]; change u2.gpr .ebp + u2.gpr .ebp = _
    rw [e2, add_ofNat]; exact congrArg _ (by omega_using [])
  refine wp_alu (Or.inl rfl) rfl fun u4 v4 _ => ?_
  have e4 : u4.gpr .ebp = BitVec.ofNat 32 (8 * j) := by
    rw [v4.gpr]; change u3.gpr .ebp + u3.gpr .ebp = _
    rw [e3, add_ofNat]; exact congrArg _ (by omega_using [])
  refine wp_alu (Or.inl rfl) rfl fun t ht _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ht.gpr]; change u4.gpr .ebp + u4.gpr .edi = _
    rw [e4, v4.other .edi (by decide), v3.other .edi (by decide), v2.other .edi (by decide),
      v1.other .edi (by decide), BitVec.add_comm]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (ht.rest (by decide)))))
  · rw [ht.mem, v4.mem, v3.mem, v2.mem, v1.mem]

/-- Bit `t` of `k`, a byte. -/
abbrev BitsAtB (base : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 456, m (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1)

theorem bit_mod (k t : Nat) : (k >>> t) &&& 1 = k / 2 ^ t % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem nib_val : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2,
    (let c3 := (BitVec.ofNat 8 b3).setWidth 32
     let c2 := c3 + c3 + (BitVec.ofNat 8 b2).setWidth 32
     let c1 := c2 + c2 + (BitVec.ofNat 8 b1).setWidth 32
     c1 + c1 + (BitVec.ofNat 8 b0).setWidth 32) =
      BitVec.ofNat 32 (((b3 * 2 + b2) * 2 + b1) * 2 + b0) := by
  decide

/-- The nibble `i` of `k`, whose bits are at `ebp + o`. -/
theorem nibble_ok {s : State} {base : Addr} (hs : Scr s base) {k j i o : Nat}
    (ho : 8 * j + o = BITS + 4 * i) (hi : i < 114)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (8 * j)) (hb : BitsAtB base k s.mem) :
    WP isa (.block (nibble o)) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (nib k i) ∧ Keeps [.eax, .ecx] s t ∧ t.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  obtain ea : ∀ (u : State) (c : Nat), u.gpr .ebp = s.gpr .ebp → c < 4 →
      u.ea (at_ .ebp (o + c)) = off base (BITS + (4 * i + c)) := fun u c hu hc => by
    change (u.gpr .ebp + BitVec.ofNat 32 (o + c)).setWidth 64 = _
    rw [hu, hp, Offset.add_add, show 8 * j + (o + c) = BITS + (4 * i + c) by omega_using [ho]]
    exact hs.ea (by omega_using [hB, hi, hc])
  obtain rd : ∀ c < 4, InRegions (s.rd ++ s.wr) (off base (BITS + (4 * i + c))) 1 := fun c hc =>
    hs.read (by omega_using [hB, hi, hc])
  obtain bit : ∀ c < 4, s.mem (off base (BITS + (4 * i + c))) = BitVec.ofNat 8 (k / 2 ^ (4 * i + c) % 2) :=
    fun c hc => by rw [hb _ (by omega_using [hi, hc]), bit_mod]
  have lt2 : ∀ c, k / 2 ^ (4 * i + c) % 2 < 2 := fun c => Nat.mod_lt _ (by decide)
  unfold nibble
  refine wp_load8 (ea s 3 rfl (by decide)) (rd 3 (by decide)) fun u3 v3 => ?_
  have c3 : u3.gpr .ecx = (BitVec.ofNat 8 (k / 2 ^ (4 * i + 3) % 2)).setWidth 32 := by rw [v3.gpr, bit 3 (by decide)]
  refine wp_load8 (ea u3 2 (v3.other .ebp (by decide)) (by decide))
    (by rw [v3.rd, v3.wr]; exact rd 2 (by decide)) fun u4 v4 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u5 v5 _ => wp_alu (Or.inl rfl) rfl fun u6 v6 _ => ?_
  have c6 : u6.gpr .ecx = u3.gpr .ecx + u3.gpr .ecx + (BitVec.ofNat 8 (k / 2 ^ (4 * i + 2) % 2)).setWidth 32 := by
    rw [v6.gpr]; change u5.gpr .ecx + u5.gpr .eax = _
    rw [v5.gpr, v5.other .eax (by decide)]; change u4.gpr .ecx + u4.gpr .ecx + u4.gpr .eax = _
    rw [v4.gpr, v4.other .ecx (by decide), v3.mem, bit 2 (by decide)]
  obtain k6 : Keeps [.eax, .ecx] s u6 :=
    (v3.rest (by decide)).trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
  obtain m6 : u6.mem = s.mem := by rw [v6.mem, v5.mem, v4.mem, v3.mem]
  refine wp_load8 (ea u6 1 (k6.1 _ (by decide)) (by decide))
    (by rw [k6.2.1, k6.2.2]; exact rd 1 (by decide)) fun u7 v7 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u8 v8 _ => wp_alu (Or.inl rfl) rfl fun u9 v9 _ => ?_
  have c9 : u9.gpr .ecx = u6.gpr .ecx + u6.gpr .ecx + (BitVec.ofNat 8 (k / 2 ^ (4 * i + 1) % 2)).setWidth 32 := by
    rw [v9.gpr]; change u8.gpr .ecx + u8.gpr .eax = _
    rw [v8.gpr, v8.other .eax (by decide)]; change u7.gpr .ecx + u7.gpr .ecx + u7.gpr .eax = _
    rw [v7.gpr, v7.other .ecx (by decide), m6, bit 1 (by decide)]
  obtain k9 : Keeps [.eax, .ecx] s u9 :=
    k6.trans ((v7.rest (by decide)).trans ((v8.rest (by decide)).trans (v9.rest (by decide))))
  obtain m9 : u9.mem = s.mem := by rw [v9.mem, v8.mem, v7.mem, m6]
  refine wp_load8 (ea u9 0 (k9.1 _ (by decide)) (by decide))
    (by rw [k9.2.1, k9.2.2]; exact rd 0 (by decide)) fun u10 v10 => ?_
  refine wp_alu (Or.inl rfl) rfl fun u11 v11 _ => wp_alu (Or.inl rfl) rfl fun u12 v12 _ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v12.gpr]; change u11.gpr .ecx + u11.gpr .eax = _
    rw [v11.gpr, v11.other .eax (by decide)]; change u10.gpr .ecx + u10.gpr .ecx + u10.gpr .eax = _
    rw [v10.gpr, v10.other .ecx (by decide), m9, bit 0 (by decide), c9, c6, c3, nib_bits k i]
    exact nib_val _ (lt2 0) _ (lt2 1) _ (lt2 2) _ (lt2 3)
  · exact k9.trans ((v10.rest (by decide)).trans ((v11.rest (by decide)).trans (v12.rest (by decide))))
  · rw [v12.mem, v11.mem, v10.mem, m9]

theorem mag_val : ∀ n < 16,
    let m := (0 : BitVec 32) - (BitVec.ofNat 32 n - 8) >>> 31
    ((BitVec.ofNat 32 n - 8) ^^^ m) - m = BitVec.ofNat 32 (mag n) := by decide

theorem magnitude_ok (s : State) {n : Nat} (hn : n < 16) (h : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.block magnitude) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (mag n) ∧ Keeps [.eax, .ebx, .ecx] s t ∧ t.mem = s.mem := by
  unfold magnitude
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun u1 v1 _ => wp_mov rfl fun u2 v2 => wp_shift (by decide) fun u3 v3 =>
    wp_mov rfl fun u4 v4 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u5 v5 _ =>
    wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl fun u6 v6 _ => wp_alu (Or.inr (Or.inl rfl)) rfl fun t ht _ =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · have e1 : u1.gpr .ecx = BitVec.ofNat 32 n - 8 := by
      rw [v1.gpr]; change s.gpr .ecx - 8 = _; rw [h]
    have e3 : u3.gpr .eax = (BitVec.ofNat 32 n - 8) >>> 31 := by
      rw [v3.gpr]; change u2.gpr .eax >>> 31 = _; rw [v2.gpr, e1]
    have e5 : u5.gpr .ebx = (0 : BitVec 32) - (BitVec.ofNat 32 n - 8) >>> 31 := by
      rw [v5.gpr]; change u4.gpr .ebx - u4.gpr .eax = _
      rw [v4.gpr, v4.other .eax (by decide), e3]
    have c5 : u5.gpr .ecx = BitVec.ofNat 32 n - 8 := by
      rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), e1]
    rw [ht.gpr]; change u6.gpr .ecx - u6.gpr .ebx = _
    rw [v6.gpr, v6.other .ebx (by decide)]
    change (u5.gpr .ecx ^^^ u5.gpr .ebx) - u5.gpr .ebx = _
    rw [e5, c5]
    exact mag_val n hn
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans
      ((v5.rest (by decide)).trans ((v6.rest (by decide)).trans (ht.rest (by decide)))))))
  · rw [ht.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

/-- `n` doublings of `eax`. -/
theorem dbls_ok (s : State) {x : Nat} (hx : s.gpr .eax = BitVec.ofNat 32 x) : ∀ n,
    WP isa (.block (List.replicate n (.alu .add .eax (.reg .eax)))) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (2 ^ n * x) ∧ Keeps [.eax] s t ∧ t.mem = s.mem
  | 0 => WP.block_nil ⟨by rw [hx, Nat.pow_zero, Nat.one_mul], Keeps.refl _ _, rfl⟩
  | n + 1 => by
    rw [List.replicate_succ']
    refine WP.block_append_iff.mpr (WP.mono (dbls_ok s hx n) fun u ⟨e, k, m⟩ => ?_)
    refine wp_alu (Or.inl rfl) rfl fun t ht _ => WP.block_nil ⟨?_, k.trans (ht.rest (by decide)), ht.mem.trans m⟩
    rw [ht.gpr]; change u.gpr .eax + u.gpr .eax = _
    rw [e, add_ofNat, Nat.pow_succ]; exact congrArg _ (by rw [Nat.mul_right_comm, Nat.mul_two])

/-- `ebp` plus `n` times `eax`. -/
theorem adds_ok (s : State) {P : BitVec 32} {x : Nat} (hx : s.gpr .eax = BitVec.ofNat 32 x) (hp : s.gpr .ebp = P) : ∀ n,
    WP isa (.block (List.replicate n (.alu .add .ebp (.reg .eax)))) s fun t =>
      t.gpr .ebp = P + BitVec.ofNat 32 (n * x) ∧ Keeps [.ebp] s t ∧ t.mem = s.mem
  | 0 => WP.block_nil ⟨by rw [hp, Nat.zero_mul]; exact (BitVec.add_zero _).symm, Keeps.refl _ _, rfl⟩
  | n + 1 => by
    rw [List.replicate_succ']
    refine WP.block_append_iff.mpr (WP.mono (adds_ok s hx hp n) fun u ⟨e, k, m⟩ => ?_)
    refine wp_alu (Or.inl rfl) rfl fun t ht _ => WP.block_nil ⟨?_, k.trans (ht.rest (by decide)), ht.mem.trans m⟩
    rw [ht.gpr]; change u.gpr .ebp + u.gpr .eax = _
    rw [e, k.1 _ (by decide), hx, BitVec.add_assoc, add_ofNat, Nat.succ_mul]

theorem tblPtr_ok {s : State} {base : Addr} (hs : Scr s base) {P : BitVec 32} (hp : word s.mem base TPTR = P) {j : Nat}
    (hj : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block tblPtr) s fun t =>
      t.gpr .ebp = P + BitVec.ofNat 32 (896 * j) ∧ Keeps [.eax, .ebp] s t ∧ t.mem = s.mem := by
  unfold tblPtr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov rfl fun u1 v1 => ?_
  have e1 : u1.gpr .eax = BitVec.ofNat 32 j := by rw [v1.gpr, hj]
  refine WP.block_append_iff.mpr (WP.mono (dbls_ok u1 e1 7) fun u2 ⟨e2, k2, m2⟩ => ?_)
  refine load_ok ((hs.of_upd v1 (by decide)).of_keeps k2 (by decide)) (by decide) fun u3 v3 => ?_
  refine WP.mono (adds_ok u3 (x := 2 ^ 7 * j) (by rw [v3.other _ (by decide), e2]) v3.gpr 7) fun t ⟨e, k, m⟩ => ⟨?_, ?_, ?_⟩
  · rw [e, m2, v1.mem, hp, ← Nat.mul_assoc]
  · exact (v1.rest (by decide)).trans ((k2.mono (by simp)).trans ((v3.rest (by decide)).trans (k.mono (by simp))))
  · rw [m, v3.mem, m2, v1.mem]

/-! ## The selection -/

/-- Word `j` of coordinate `c` of entry `i` of table `jt`. -/
def tblLimb (jt i c j : Nat) : Nat := coord c (Impl.X448.baseTable jt i) / 2 ^ (32 * j) % 2 ^ 32

/-- The selection so far: slots 8 and 9 hold the entry of index `d` if it is below `n`, and zero
otherwise. -/
def SelT (base : Addr) (jt d n : Nat) (m : Mem) : Prop :=
  ∀ c < 2, ∀ j < 14, word m base (slot (8 + c) + 4 * j) =
    if d < n then BitVec.ofNat 32 (tblLimb jt d c j) else 0

theorem selWordT_ok {s : State} {base : Addr} (hs : Scr s base) {o j c : Nat} (ho : o + 56 ≤ 4096)
    (hj : j < 14) {V : Nat → Nat} (hv : Cands base (s.gpr .ebp) c V s) {b : Bool} (h4 : s.gpr .ebx = mask b) :
    WP isa (.block (selWordT o c j)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 4 * j))
        ((BitVec.ofNat 32 (V j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
      Keeps [.eax] s t := by
  obtain ⟨hr, _, hval⟩ := hv j hj
  unfold selWordT
  refine wp_load (a := addr (s.gpr .ebp) (c + 4 * j)) rfl hr fun u1 v1 =>
    wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u2 v2 _ => ?_
  obtain hs2 : Scr u2 base := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (readSc hs2 (by omega_using [ho, hj])) fun u3 v3 _ => ?_
  refine store_ok (hs2.of_upd v3 (by decide)) (by omega_using [ho, hj]) fun u4 v4 => WP.block_nil ⟨?_, ?_⟩
  · rw [v4.mem, v3.mem, v3.gpr]
    change u2.mem.writeW _ (u2.gpr .eax ||| word u2.mem base _) = _
    rw [v2.gpr, v2.mem, v1.mem]
    change s.mem.writeW _ ((u1.gpr .eax &&& u1.gpr .ebx) ||| _) = _
    rw [v1.gpr, v1.other _ (by decide), h4, hval]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans (v4.rest _)))

theorem selCoordT_ok {s : State} {base : Addr} (hs : Scr s base) {o c : Nat} (ho : o + 56 ≤ 4096)
    {a : BitVec 32} (ha : s.gpr .ebp = a) {V : Nat → Nat} (hv : Cands base a c V s) {b : Bool}
    (h4 : s.gpr .ebx = mask b) :
    WP isa (.block (selCoordT o c)) s fun t =>
      (∀ j < 14, word t.mem base (o + 4 * j) =
        (BitVec.ofNat 32 (V j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
      Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, word t.mem base (o + 4 * j) =
      (BitVec.ofNat 32 (V j) &&& mask b) ||| word s.mem base (o + 4 * j)) ∧
    (∀ j, n ≤ j → j < 14 → word t.mem base (o + 4 * j) = word s.mem base (o + 4 * j)) ∧
    Outside base o 56 s.mem t.mem ∧ Keeps [.eax] s t
  obtain step : ∀ n t, n < 14 → inv n t → WP isa (.block (selWordT o c n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (selWordT_ok (V := V) (hs.of_keeps tk (by decide)) ho hn
      (by rw [tk.1 _ (by decide), ha]; exact hv.keep (by omega_using [ho]) tm tk) ((tk.1 _ (by decide)).trans h4))
      fun u ⟨um, uk⟩ => ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun j hj => ?_, fun j hj hj' => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans uk⟩
    · rw [um, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hj])]
      by_cases h : j = n
      · rw [ite_eq_left h, h, ta n (Nat.le_refl _) hn]
      · rw [ite_eq_right h]; exact tf j (by omega_using [hj, h])
    · rw [out.word (by omega_using [hj]) (by omega_using [ho, hj'])]
      exact ta j (by omega_using [hj]) hj'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 14) inv step 14 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The address of table `jt` in `ebp`, its entries' words (`TblAt.cands`). -/
def RowAt (base : Addr) (jt : Nat) (s : State) : Prop :=
  ∀ m < 8, ∀ c < 2, Cands base (s.gpr .ebp) (448 * c + 56 * m)
    (fun w => coord c (Impl.X448.baseTable jt (m + 1)) / 2 ^ (32 * w)) s

theorem RowAt.keep {base : Addr} {jt : Nat} {s t : State} (h : RowAt base jt s) {o n : Nat} (hn : o + n ≤ 8192)
    (ho : Outside base o n s.mem t.mem) {rs : List Reg} (hk : Keeps rs s t) (hp : .ebp ∉ rs) :
    RowAt base jt t := fun m hm c hc => by rw [hk.1 _ hp]; exact (h m hm c hc).keep hn ho hk

/-- A word of the selection after entry `n`, whose words are not reduced. -/
theorem selT_word {jt d n c j : Nat} {w : BitVec 32}
    (hw : w = if d < n then BitVec.ofNat 32 (tblLimb jt d c j) else 0) :
    (BitVec.ofNat 32 (coord c (Impl.X448.baseTable jt n) / 2 ^ (32 * j)) &&& mask (decide (d = n))) ||| w =
      if d < n + 1 then BitVec.ofNat 32 (tblLimb jt d c j) else 0 := by
  have e : BitVec.ofNat 32 (coord c (Impl.X448.baseTable jt n) / 2 ^ (32 * j)) =
      BitVec.ofNat 32 (tblLimb jt n c j) := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat, tblLimb, Nat.mod_mod])
  rw [e]
  exact sel_word hw (fun h => by rw [h])

theorem selEntryT_ok {s : State} {base : Addr} (hs : Scr s base) {jt d m : Nat} (hd : d < 16) (hm : m < 8)
    (h5 : s.gpr .ecx = BitVec.ofNat 32 d) (hrow : RowAt base jt s) (hsel : SelT base jt d (m + 1) s.mem) :
    WP isa (.block (selEntryT m)) s fun t =>
      SelT base jt d (m + 2) t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.eax, .ebx] s t := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  unfold selEntryT
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (selMask_ok s hd (i := m + 1) (by omega_using [hm]) h5) fun u ⟨u4, uk, um⟩ => ?_
  obtain hsu := hs.of_keeps uk (by decide)
  obtain ru : RowAt base jt u := hrow.keep (o := 0) (n := 0) (by decide) (by rw [um]; exact Outside.refl _ _ _ _) uk (by decide)
  rw [WP.block_append_iff]
  have r0 := ru m hm 0 (by decide)
  rw [Nat.mul_zero, Nat.zero_add] at r0
  refine WP.mono (selCoordT_ok hsu (o := slot 8) (by omega_using [h8]) rfl r0 u4)
    fun v ⟨vf, vm, vk⟩ => ?_
  obtain hsv := hsu.of_keeps vk (by decide)
  obtain rv : RowAt base jt v := ru.keep (by omega_using [h8]) vm vk (by decide)
  have r1 := rv m hm 1 (by decide)
  rw [Nat.mul_one] at r1
  refine WP.mono (selCoordT_ok hsv (o := slot 9) (by omega_using [h9]) rfl r1
    ((vk.1 _ (by decide)).trans u4)) fun w ⟨wf, wm, wk⟩ => ⟨?_, ?_, ?_⟩
  · intro c hc j hj
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj]), vf j hj, um]
      exact selT_word (hsel 0 (by decide) j hj)
    · rw [show slot (8 + 1) = slot 9 from rfl, wf j hj, vm.word (by omega_using [h8, h9, hj]) (by omega_using [h9, hj]), um]
      exact selT_word (hsel 1 (by decide) j hj)
  · rw [← um]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))

/-- Entry 0, the neutral point `(0, 1)`. -/
theorem tblLimb_zero (jt c : Nat) (hc : c < 2) (j : Nat) :
    tblLimb jt 0 c j = if c = 1 ∧ j = 0 then 1 else 0 := by
  have e : Impl.X448.baseTable jt 0 = (0, 1) := rfl
  rw [tblLimb, e]
  rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
  · rw [ite_eq_right (fun h => absurd h.1 (by decide)), show coord 0 (0, 1) = 0 by decide +kernel, Nat.zero_div, Nat.zero_mod]
  · rw [show coord 1 (0, 1) = 1 by decide +kernel]
    by_cases h : j = 0
    · rw [ite_eq_left ⟨rfl, h⟩, h]
    · rw [ite_eq_right (fun h' => h h'.2), Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega_using [h])), Nat.zero_mod]

theorem and_one_mask (b : Bool) : mask b &&& 1 = if b then (1 : BitVec 32) else 0 := by cases b <;> decide

/-- The slots after a selection of entry `(x, y)`. -/
def selEnvT (q : Spec.X448.Fe × Spec.X448.Fe) (e : Env) : Env :=
  Function.update (Function.update e 8 q.1) 9 q.2

theorem selectT_ok {s : State} {base : Addr} (hs : Scr s base) {jt d : Nat} (hd : d < 9)
    (h5 : s.gpr .ecx = BitVec.ofNat 32 d) (hrow : RowAt base jt s) :
    WP isa (.block selectT) s fun t => Keep base s t ∧
      E t.mem base = selEnvT (Impl.X448.baseTable jt d) (E s.mem base) := by
  have h8 : slot 8 = 1088 := rfl
  have h9 : slot 9 = 1216 := rfl
  have hA : ACC = 3584 := rfl
  have hd16 : d < 16 := by omega_using [hd]
  unfold selectT
  simp only [List.append_assoc, List.cons_append]
  refine wp_mov rfl fun u hu => ?_
  obtain ku : Keeps [.eax, .ebx] s u := hu.rest (by decide)
  obtain hsu := hs.of_keeps ku (by decide)
  refine WP.block_append_iff.mpr (WP.mono (zeroSlot_ok hsu (o := slot 8) (by omega_using [h8]) hu.gpr)
    fun v ⟨vf, vm, vk⟩ => ?_)
  obtain hsv := hsu.of_keeps vk (by decide)
  refine WP.block_append_iff.mpr (WP.mono (zeroSlot_ok hsv (o := slot 9) (by omega_using [h9])
    ((vk.1 _ (by decide)).trans hu.gpr)) fun w ⟨wf, wm, wk⟩ => ?_)
  obtain kw : Keeps [.eax, .ebx] s w := ku.trans ((vk.mono (by simp)).trans (wk.mono (by simp)))
  obtain hsw := hs.of_keeps kw (by decide)
  obtain ow : Outside base (slot 8) 240 s.mem w.mem := by
    rw [← hu.mem]
    exact (vm.mono (by omega_using [h8]) (by omega_using [h8])).trans
      (wm.mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  -- Entry 0.
  refine WP.block_append_iff.mpr (WP.mono (selMask_ok w hd16 (i := 0) (by decide) ((kw.1 _ (by decide)).trans h5))
    fun w1 ⟨x1, kx, mx⟩ => ?_)
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun w2 hw2 _ => ?_
  obtain k2 : Keeps [.eax, .ebx] s w2 := kw.trans (kx.trans (hw2.rest (by decide)))
  obtain hs2 := hs.of_keeps k2 (by decide)
  refine store_ok hs2 (by omega_using [h9]) fun w3 hw3 => ?_
  obtain m3 : w3.mem = w.mem.writeW (off base (slot 9)) (if d = 0 then (1 : BitVec 32) else 0) := by
    rw [hw3.mem, hw2.mem, hw2.gpr, mx]
    change w.mem.writeW _ (w1.gpr .ebx &&& 1) = _
    rw [x1, and_one_mask]
    by_cases h : d = 0 <;> simp [h]
  obtain k3 : Keeps [.eax, .ebx] s w3 := k2.trans (hw3.rest _)
  obtain o3 : Outside base (slot 8) 240 s.mem w3.mem := ow.trans (by
    rw [m3]; exact (writeW_outside _ _ _ (by omega_using [h9])).mono (by omega_using [h8, h9]) (by omega_using [h8, h9]))
  obtain sel0 : SelT base jt d 1 w3.mem := by
    intro c hc j hj
    have hz := tblLimb_zero jt c hc j
    have hlt : d < 1 ↔ d = 0 := by omega_using []
    rcases (by omega_using [hc] : c = 0 ∨ c = 1) with rfl | rfl
    · rw [m3, (writeW_outside _ _ _ (by omega_using [h9])).word (by simp only [slot] at h8 h9 ⊢; omega_using [hj])
        (by simp only [slot]; omega_using [hj]), show slot (8 + 0) = slot 8 from rfl, wm.word (by omega_using [h8, h9, hj]) (by omega_using [h8, hj]), vf j hj]
      by_cases h : d < 1
      · rw [ite_eq_left h, hlt.mp h, hz]; rfl
      · rw [ite_eq_right h]
    · rw [m3]
      change word (w.mem.writeW (off base (slot 9 + 4 * 0)) _) base (slot 9 + 4 * j) = _
      rw [word_write w.mem base (by omega_using [h9]) (by omega_using [h9, hj])]
      by_cases hj0 : j = 0
      · rw [ite_eq_left hj0, hj0]
        by_cases h : d = 0
        · rw [ite_eq_left h, ite_eq_left (hlt.mpr h), h, tblLimb_zero jt 1 (by decide) 0]; rfl
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (hlt.mp h'))]
      · rw [ite_eq_right hj0, wf j hj]
        by_cases h : d < 1
        · rw [ite_eq_left h, hlt.mp h, hz, ite_eq_right (fun h' => hj0 h'.2)]; rfl
        · rw [ite_eq_right h]
  let inv := fun n (t : State) =>
    SelT base jt d (n + 1) t.mem ∧ Outside base (slot 8) 240 s.mem t.mem ∧ Keeps [.eax, .ebx] s t
  obtain step : ∀ n t, n < 8 → inv n t → WP isa (.block (selEntryT n)) t (inv (n + 1)) := by
    intro n t hn ⟨ts, tm, tk⟩
    exact WP.mono (selEntryT_ok (hs.of_keeps tk (by decide)) hd16 hn ((tk.1 _ (by decide)).trans h5)
      (hrow.keep (by omega_using [h8]) tm tk (by decide)) ts)
      fun x ⟨xs, xm, xk⟩ => ⟨xs, tm.trans xm, tk.trans xk⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) w3 ⟨sel0, o3, k3⟩)
    fun t ⟨ts, tm, tk⟩ => ?_
  have hsel : d < 9 := hd
  obtain lx : ∀ j < 14, limbs t.mem base (slot 8) j = (Impl.X448.baseTable jt d).1.val / 2 ^ (32 * j) % 2 ^ 32 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 0) + 4 * j)).toNat = _
      rw [ts 0 (by decide) j hj, ite_eq_left hsel, BitVec.toNat_ofNat, tblLimb, Nat.mod_mod]
      rfl
  obtain ly : ∀ j < 14, limbs t.mem base (slot 9) j = (Impl.X448.baseTable jt d).2.val / 2 ^ (32 * j) % 2 ^ 32 :=
    fun j hj => by
      change (word t.mem base (slot (8 + 1) + 4 * j)).toNat = _
      rw [ts 1 (by decide) j hj, ite_eq_left hsel, BitVec.toNat_ofNat, tblLimb, Nat.mod_mod]
      rfl
  obtain other : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 14,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i h8' h9' j hj => by
    have e8 := slot_sep h8'
    have e9 := slot_sep h9'
    have hi := slot_bound i
    change slot i.val + 56 ≤ 3584 at hi
    exact tm.limbs (by change slot i.val + 56 ≤ slot 8 ∨ slot 8 + 56 ≤ slot i.val at e8
                       change slot i.val + 56 ≤ slot 9 ∨ slot 9 + 56 ≤ slot i.val at e9
                       simp only [slot] at e8 e9 ⊢
                       omega_using [e8, e9]) (by omega_using [hi]) hj
  refine ⟨⟨tk.mono (by decide), fun p _ hp _ => tm p (by omega_using [hp, h8])⟩, ?_⟩
  funext i
  by_cases i9 : i = 9
  · subst i9; rw [selEnvT, Function.update_self]; exact F_digits _ ly
  · rw [selEnvT, Function.update_of_ne i9]
    by_cases i8 : i = 8
    · subst i8; rw [Function.update_self]; exact F_digits _ lx
    · rw [Function.update_of_ne i8]
      exact congrArg Proof.X448.toFe (num_congr (other i i8 i9))

/-- The digit's magnitude and its table's address. -/
theorem digitLoad_ok {s : State} {base : Addr} {P : BitVec 32} (hs : Scr s base) (ht : TblAt base P s)
    {k j i o : Nat} (hj : j < 57) (ho : 8 * j + o = 4 * i) (hi : i < 114)
    (he : s.gpr .esi = BitVec.ofNat 32 j) (hb : BitsAtB base k s.mem) :
    WP isa (.block (digitLoad o)) s fun t => Keeps workRegs s t ∧ t.mem = s.mem ∧
      t.gpr .ecx = BitVec.ofNat 32 (mag (nib k i)) ∧ t.gpr .ebp = P + BitVec.ofNat 32 (896 * j) ∧ RowAt base j t := by
  unfold digitLoad
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (digitPtr_ok s he) fun s1 ⟨p1, k1, m1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.block_append_iff.mpr (WP.mono (nibble_ok hs1 (k := k) (j := j) (i := i) (o := BITS + o) (by omega_using [ho]) hi
    (p1.trans (by rw [k1.1 _ (by decide)])) (by rw [m1]; exact hb)) fun s2 ⟨n2, k2, m2⟩ => ?_)
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.block_append_iff.mpr (WP.mono (magnitude_ok s2 (nib_lt _ _) n2) fun s3 ⟨n3, k3, m3⟩ => ?_)
  have hs3 := hs2.of_keeps k3 (by decide)
  have m03 : s3.mem = s.mem := by rw [m3, m2, m1]
  have e3 : s3.gpr .esi = BitVec.ofNat 32 j := by rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide), he]
  refine WP.mono (tblPtr_ok hs3 (P := P) (by rw [m03]; exact ht.ptr) e3) fun t ⟨p4, k4, m4⟩ => ?_
  have K4 : Keeps workRegs s t := (k1.mono (by decide)).trans ((k2.mono (by decide)).trans
    ((k3.mono (by decide)).trans (k4.mono (by decide))))
  have m04 : t.mem = s.mem := m4.trans m03
  refine ⟨K4, m04, by rw [k4.1 _ (by decide), n3], p4, fun m hm c hc => ?_⟩
  rw [p4]
  exact (ht.cands hs hj hc hm).keep (o := 0) (n := 0) (by decide) (by rw [m04]; exact Outside.refl _ _ _ _) K4

/-! ## A digit -/

theorem nib_neg (k i : Nat) : decide (nib k i < 8) = decide (k / 2 ^ (4 * i + 3) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (k / 2 ^ (4 * i)) (by decide : 2 > 0)
  have h1 := Nat.mod_lt (k / 2 ^ (4 * i + 1)) (by decide : 2 > 0)
  have h2 := Nat.mod_lt (k / 2 ^ (4 * i + 2)) (by decide : 2 > 0)
  refine decide_eq_decide.mpr ?_
  omega_using [h0, h1, h2]

theorem bit_mask : ∀ b < 2, (BitVec.ofNat 8 b).setWidth 32 - (1 : BitVec 32) = mask (decide (b = 0)) := by decide

theorem negSel_ok {s : State} {base : Addr} (hs : Scr s base) {k j i o : Nat}
    (ho : 8 * j + o = 4 * i) (hi : i < 114) (he : s.gpr .esi = BitVec.ofNat 32 j) (hb : BitsAtB base k s.mem) :
    WP isa (.block (negSel o)) s fun t => Keep base s t ∧
      E t.mem base = opSwap 8 12 (decide (nib k i < 8)) (E s.mem base) := by
  have hB : BITS = 3072 := rfl
  unfold negSel
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append_iff.mpr (WP.mono (digitPtr_ok s he) fun s1 ⟨p1, k1, m1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  refine wp_load8 (a := off base (BITS + (4 * i + 3))) ?_ (hs1.read (by omega_using [hB, hi])) fun s2 h2 => ?_
  · rw [hs1.ea_ptr (p1.trans (by rw [k1.1 _ (by decide)])) (by omega_using [hB, hi, ho])]
    congr 1
    omega_using [ho]
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s3 h3 _ => ?_
  have k3 : Keeps workRegs s s3 := (k1.mono (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))
  have m3 : s3.mem = s.mem := by rw [h3.mem, h2.mem, m1]
  have x3 : s3.gpr .ebx = mask (decide (nib k i < 8)) := by
    rw [h3.gpr]; change s2.gpr .ebx - 1 = _
    rw [h2.gpr, m1, hb _ (by omega_using [hi]), bit_mod, bit_mask _ (Nat.mod_lt _ (by decide)), nib_neg]
  refine WP.mono (cswapE (hs.of_keeps k3 (by decide)) 8 12 (by decide) x3) fun t ⟨kt, _, et⟩ => ⟨?_, by rw [et, m3]⟩
  exact Keep.trans ⟨k3, by rw [m3]; exact WsOut2.refl _ _ _ _ _ _⟩ kt

/-- `addAff` as X448's field operations on slots. -/
def affFields (x y z : Index) : List FieldOp := [
  .mul 12 z z, .mul 13 x 8, .mul 14 y 9, .mul 15 13 14, .mulSmall 15 15, .add 16 x y, .add 17 8 9, .mul 16 16 17,
  .sub 16 16 13, .sub 16 16 14, .sub 17 14 13, .add 18 12 15, .sub 12 12 15, .mul 13 z 18, .mul x 13 16,
  .mul 13 z 12, .mul y 13 17, .mul z 18 12]

/-- The slots an accumulator takes. -/
def Acc (x y z : Index) : Prop := (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = 3 ∧ y = 4 ∧ z = 5)

theorem affFields_impl {x y z : Index} (h : Acc x y z) : addAff x.val y.val z.val = (affFields x y z).map FieldOp.impl := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

theorem neg_impl : ([.sub (slot 12) (slot 21) (slot 8)] : List Impl.X448.X86.Op) =
    ([.sub 12 21 8] : List FieldOp).map FieldOp.impl := rfl

/-- The slots after a digit: the entry `q` of its magnitude, negated if `b`, added. -/
def digitEnv (x y z : Index) (q : Spec.X448.Fe × Spec.X448.Fe) (b : Bool) (e : Env) : Env :=
  applyOps (affFields x y z) (opSwap 8 12 b (applyOps [.sub 12 21 8] (selEnvT q e)))

theorem digitEnv_pt {x y z : Index} (h : Acc x y z) (q : Spec.X448.Fe × Spec.X448.Fe) (b : Bool) (e : Env)
    (h0 : e 21 = 0) :
    pt (digitEnv x y z q b e) x y z = affAdd (pt e x y z) (if b then negAff q else q) := by
  have e1 : (if b then negAff q else q) = (if b then e 21 - q.1 else q.1, q.2) := by
    rw [h0]; cases b <;> rfl
  rw [e1]
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

/-- What a digit keeps: 1, `d`, zero and the other accumulator. -/
theorem digitEnv_keep {x y z : Index} (h : Acc x y z) (q : Spec.X448.Fe × Spec.X448.Fe) (b : Bool) (e : Env)
    (i : Index) (hi : i = 10 ∨ i = 11 ∨ i = 21 ∨ (i.val < 6 ∧ i ≠ x ∧ i ≠ y ∧ i ≠ z)) :
    digitEnv x y z q b e i = e i := by
  have hx : i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 12 ∧ i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 15 ∧ i ≠ 16 ∧ i ≠ 17 ∧ i ≠ 18 ∧ i ≠ x ∧ i ≠ y ∧ i ≠ z := by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> revert i <;> decide
  obtain ⟨h8, h9, h12, h13, h14, h15, h16, h17, h18, hx, hy, hz⟩ := hx
  simp only [digitEnv, affFields, applyOps, FieldOp.apply, opMul, opAdd, opSub, opA24, opSwap, selEnvT,
    Function.update_of_ne h8, Function.update_of_ne h9, Function.update_of_ne h12, Function.update_of_ne h13,
    Function.update_of_ne h14, Function.update_of_ne h15, Function.update_of_ne h16, Function.update_of_ne h17,
    Function.update_of_ne h18, Function.update_of_ne hx, Function.update_of_ne hy, Function.update_of_ne hz]

theorem BitsAtB.keep {base : Addr} {k : Nat} {m m' : Mem} (h : BitsAtB base k m)
    (hm : WsOut2 base 64 2816 ACC 512 m m') : BitsAtB base k m' := fun t ht => by
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  rw [hm _ (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB])
    (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [hB])
    (by rw [ofs_off' base (by omega_using [ht, hB])]; omega_using [ht, hB, hA])]
  exact h t ht

/-- One digit, added to its accumulator. -/
theorem digitAdd_ok {s : State} {base : Addr} {P : BitVec 32} (hs : Scr s base) (hc : CallCtx s base)
    (ht : TblAt base P s) {k j i o : Nat} (hj : j < 57) (ho : 8 * j + o = 4 * i) (hi : i < 114)
    (he : s.gpr .esi = BitVec.ofNat 32 j) (hb : BitsAtB base k s.mem) {x y z : Index} (ha : Acc x y z) :
    WP isa (digitAdd o x.val y.val z.val) s fun t => Keep base s t ∧
      E t.mem base = digitEnv x y z (Impl.X448.baseTable j (mag (nib k i))) (decide (nib k i < 8)) (E s.mem base) := by
  unfold digitAdd
  rw [neg_impl, affFields_impl ha]
  refine WP.seq (WP.mono (digitLoad_ok hs ht hj ho hi he hb) fun s0 ⟨k0, m0, n0, _, r0⟩ => ?_)
  refine WP.seq (WP.mono (selectT_ok (hs.of_keeps k0 (by decide)) (jt := j) (mag_lt (nib_lt k i)) n0 r0)
    fun s1 ⟨k1', e1⟩ => ?_)
  rw [m0] at e1
  have k1 : Keep base s s1 := Keep.trans ⟨k0, by rw [m0]; exact WsOut2.refl _ _ _ _ _ _⟩ k1'
  have hs1 := k1.scr hs
  refine WP.seq (WP.mono (ops_ok hs1 (k1.ctx hc) [.sub 12 21 8]) fun s2 ⟨k2, e2⟩ => ?_)
  have k02 := k1.trans k2
  have hs2 := k02.scr hs
  have b2 := hb.keep k02.mem
  refine WP.seq (WP.mono (negSel_ok hs2 ho hi (by rw [k02.regs.1 _ (by decide), he]) b2) fun s3 ⟨k3, e3⟩ => ?_)
  have k03 := k02.trans k3
  refine WP.mono (ops_ok (k03.scr hs) (k03.ctx hc) (affFields x y z)) fun t ⟨kt, et⟩ => ⟨k03.trans kt, ?_⟩
  rw [et, e3, e2, e1]
  rfl

/-! ## The loop -/

/-- The loop's invariant, after `n` steps for `k`. -/
structure CombInv (base : Addr) (P : BitVec 32) (k : Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  ctx : CallCtx s base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : WsOut2 base 64 2816 ACC 512 s₀.mem s.mem
  tbl : TblAt base P s
  a : pt (E s.mem base) 0 1 2 = signedSum k 1 n
  c : pt (E s.mem base) 3 4 5 = signedSum k 0 n
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d
  zero : E s.mem base 21 = 0

/-- The tables after a digit. -/
theorem TblAt.digit {base : Addr} {P : BitVec 32} {s t : State} (h : TblAt base P s) (hc : CallCtx s base)
    (k : Keep base s t) {c : Prog isa} (hu : stackUse c ≤ 20)
    (hf : Frame (s.wr ++ [below (s.gpr .esp) (stackUse c)]) s.mem t.mem) : TblAt base P t :=
  h.frame (k.regs.1 _ (by decide)) k.regs.2.1 k.regs.2.2 (Frame.below_mono hf hu hc.sp)
    (k.mem.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide))

theorem combStep_ok {s₀ s : State} {base : Addr} {P : BitVec 32} {k n : Nat} (hn : n < 57)
    (hbits : BitsAtB base k s₀.mem) (hi : CombInv base P k s₀ s n) :
    WP isa combStep s fun t => CombInv base P k s₀ t (n + 1) ∧ t.zf = some (decide (n + 1 = 57)) := by
  have hs := hi.scr
  have hc := hi.ctx
  unfold combStep
  have acc : Acc 0 1 2 := Or.inl ⟨rfl, rfl, rfl⟩
  have acc' : Acc 3 4 5 := Or.inr ⟨rfl, rfl, rfl⟩
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by lit_decide)) (Nat.le_trans (by lit_decide) hc.sp)
    (digitAdd_ok hs hc hi.tbl (o := 4) (i := 2 * n + 1) hn (by omega_using []) (by omega_using [hn]) hi.esi
      (hbits.keep hi.mem) acc)) fun s1 ⟨⟨k1, e1⟩, f1⟩ => ?_)
  have hs1 := k1.scr hs
  have hc1 := k1.ctx hc
  have t1 := hi.tbl.digit hc k1 (by lit_decide) f1
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by lit_decide)) (Nat.le_trans (by lit_decide) hc1.sp)
    (digitAdd_ok hs1 hc1 t1 (o := 0) (i := 2 * n) hn (by omega_using []) (by omega_using [hn])
      (by rw [k1.regs.1 _ (by decide), hi.esi]) ((hbits.keep hi.mem).keep k1.mem) acc')) fun s2 ⟨⟨k2, e2⟩, f2⟩ => ?_)
  have t2 := t1.digit hc1 k2 (by lit_decide) f2
  have k02 := k1.trans k2
  refine wp_alu (Or.inl rfl) rfl fun s3 h3 _ => wp_cmp rfl fun t vt hz => WP.block_nil ?_
  have b3 : s3.gpr .esi = BitVec.ofNat 32 (n + 1) := by
    rw [h3.gpr]; change s2.gpr .esi + BitVec.ofNat 32 1 = _
    rw [k02.regs.1 _ (by decide), hi.esi, add_ofNat]
  have g : ∀ r, r ≠ .esi → t.gpr r = s2.gpr r := fun r hr => by rw [congrFun vt.gpr, h3.other r hr]
  have mt : t.mem = s2.mem := by rw [vt.mem, h3.mem]
  have k3 : Keeps [.esi] s2 t := ⟨fun r hr => g r (by simpa using hr), vt.rd.trans h3.rd, vt.wr.trans h3.wr⟩
  have ee : ∀ i : Index, E t.mem base i = E s2.mem base i := fun i => by rw [mt]
  have keep : ∀ i : Index, i = 10 ∨ i = 11 ∨ i = 21 → E t.mem base i = E s.mem base i := fun i h => by
    rw [ee, e2, digitEnv_keep acc' _ _ _ i (by rcases h with h | h | h <;> simp [h]),
      e1, digitEnv_keep acc _ _ _ i (by rcases h with h | h | h <;> simp [h])]
  refine ⟨⟨(k02.scr hs).of_keeps k3 (by decide), (k02.ctx hc).keep (g _ (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hi.regs.trans ((k02.regs.mono (fun _ h => List.mem_cons_of_mem _ h)).trans (k3.mono (by simp)))
  · rw [congrFun vt.gpr, b3]
  · rw [mt]; exact hi.mem.trans k02.mem
  · exact t2.frame (g _ (by decide)) k3.2.1 k3.2.2 (by rw [mt]; exact Frame.refl _ _) (by rw [mt])
  · rw [mt, signedSum, ← hi.a, signedEntry]
    have p : pt (E s2.mem base) 0 1 2 = pt (E s1.mem base) 0 1 2 := by
      rw [e2]
      exact pt_congr' (digitEnv_keep acc' _ _ _ 0 (by decide)) (digitEnv_keep acc' _ _ _ 1 (by decide))
        (digitEnv_keep acc' _ _ _ 2 (by decide))
    rw [p, e1, digitEnv_pt acc _ _ _ hi.zero]
    simp only [decide_eq_true_eq]
  · have p : pt (E s1.mem base) 3 4 5 = pt (E s.mem base) 3 4 5 := by
      rw [e1]
      exact pt_congr' (digitEnv_keep acc _ _ _ 3 (by decide)) (digitEnv_keep acc _ _ _ 4 (by decide))
        (digitEnv_keep acc _ _ _ 5 (by decide))
    have z1 : E s1.mem base 21 = 0 := by rw [e1, digitEnv_keep acc _ _ _ 21 (by decide), hi.zero]
    rw [mt, e2, digitEnv_pt acc' _ _ _ z1, p, hi.c, signedSum, signedEntry]
    simp only [decide_eq_true_eq, Nat.add_zero]
  · rw [keep 10 (Or.inl rfl)]; exact hi.one
  · rw [keep 11 (Or.inr (Or.inl rfl))]; exact hi.d
  · rw [keep 21 (Or.inr (Or.inr rfl))]; exact hi.zero
  · have e57 : ∀ n < 57, (BitVec.ofNat 32 (n + 1) - (57 : BitVec 32) == 0) = decide (n + 1 = 57) := by decide
    rw [hz, b3]
    exact congrArg some (e57 n hn)

theorem combLoop_ok {s₀ s : State} {base : Addr} {P : BitVec 32} {k : Nat} (hbits : BitsAtB base k s₀.mem)
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 0 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → CombInv base P k s₀ s' 0) :
    WP isa combLoop s fun s' => CombInv base P k s₀ s' 57 := by
  unfold combLoop
  refine WP.seq (WP.mono (setCounter_ok s 0 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := combStep) (c := .ne) (Q := fun s' => CombInv base P k s₀ s' 57)
    (fun m (s : State) => m ≤ 57 ∧ 1 ≤ m ∧ CombInv base P k s₀ s (57 - m)) ?_ 57 s'
    ⟨by decide, by decide, (Nat.sub_self 57).symm ▸ hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (combStep_ok (by omega_using [h1, h2]) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by rw [decide_eq_false (by omega_using [h1, h2, hm])]; rfl, m - 1, by omega_using [h2],
      by omega_using [h1], by omega_using [h2, hm], ?_⟩
    rw [show 57 - (m - 1) = 57 - m + 1 by omega_using [h1, h2]]
    exact hi'

/-! ## The combination -/

/-- `C` into slots 8–10. -/
def copyFields : List FieldOp := [.copy 8 3, .copy 9 4, .copy 10 5]

theorem copyC_impl : copyC = copyFields.map FieldOp.impl := by decide +kernel

theorem double4Step_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) {k : Nat} (hk : k < 2 ^ 16)
    (he : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa (.seq (field doubleOps) (.block [.alu .sub .esi (.imm 1)])) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ t.zf = some (decide (k = 0)) ∧ Keeps (.esi :: workRegs) s t ∧
      WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧ E t.mem base = applyOps doubleFields (E s.mem base) := by
  rw [field, doubleFields_impl]
  refine WP.seq (WP.mono (ops_ok hs hc doubleFields) fun u ⟨ku, eu⟩ => ?_)
  refine WP.mono (decCounter_ok hk (by rw [ku.regs.1 _ (by decide), he])) fun t ⟨et, gt, mt, rt, wt, zt⟩ => ?_
  refine ⟨et, zt, ⟨fun r hr => ?_, rt.trans ku.regs.2.1, wt.trans ku.regs.2.2⟩, by rw [mt]; exact ku.mem, by rw [mt, eu]⟩
  rw [gt r (fun h => hr (by simp [h])), ku.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h))]

/-- `n` doublings. -/
def dblEnv : Nat → Env → Env
  | 0, e => e
  | n + 1, e => applyOps doubleFields (dblEnv n e)

theorem dblEnv_keep (i : Index) (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 11) : ∀ n e, dblEnv n e i = e i
  | 0, _ => rfl
  | n + 1, e => by
    rw [dblEnv, show applyOps doubleFields (dblEnv n e) i = dblEnv n e i by
      rcases hi with rfl | rfl | rfl | rfl <;> rfl]
    exact dblEnv_keep i hi n e

theorem double4_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) :
    WP isa double4 s fun t => Keeps (.esi :: workRegs) s t ∧ WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧
      E t.mem base = dblEnv 4 (E s.mem base) := by
  unfold double4
  refine WP.seq (WP.mono (setCounter_ok s 4 (by decide)) fun s₁ ⟨e₁, g₁, m₁, r₁, w₁⟩ => ?_)
  have k₁ : Keeps (.esi :: workRegs) s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), r₁, w₁⟩
  refine WP.loop (M := isa) (fun m (t : State) => 1 ≤ m ∧ m ≤ 4 ∧ t.gpr .esi = BitVec.ofNat 32 m ∧
      Keeps (.esi :: workRegs) s t ∧ WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧
      E t.mem base = dblEnv (4 - m) (E s.mem base)) ?_ 4 s₁
    ⟨by decide, by decide, e₁, k₁, by rw [m₁]; exact WsOut2.refl _ _ _ _ _ _, by rw [m₁]; rfl⟩
  intro m t ⟨h1, h2, et, kt, ot, qt⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (double4Step_ok (hs.of_keeps kt (by decide)) (hc.keep (kt.1 _ (by decide))) (by omega_using [h2]) et)
    fun u ⟨eu, zu, ku, ou, qu⟩ => ?_
  have q : E u.mem base = dblEnv (4 - k) (E s.mem base) := by
    rw [qu, qt, show 4 - k = 4 - (k + 1) + 1 by omega_using [h2]]; rfl
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact .inl ⟨rfl, kt.trans ku, ot.trans ou, q⟩
  · refine .inr ⟨by rw [decide_eq_false (by omega_using [hk])]; rfl, k, by omega_using [], by omega_using [hk],
      by omega_using [h2], eu, kt.trans ku, ot.trans ou, q⟩

/-- The slots after the combination. -/
theorem finish_pt (e : Env) (hd : e 11 = Spec.Ed448.d) :
    pt (applyOps (addFields ++ takeFields) (applyOps copyFields (dblEnv 4 e))) 0 1 2 =
      Spec.Ed448.pointAdd (double (double (double (double (pt e 0 1 2))))) (pt e 3 4 5) := by
  have h : ∀ e' : Env, pt (applyOps (addFields ++ takeFields) (applyOps copyFields e')) 0 1 2 =
      addWith (e' 11) (pt e' 0 1 2) (pt e' 3 4 5) := fun _ => rfl
  have h4 : pt (dblEnv 4 e) 0 1 2 = double (double (double (double (pt e 0 1 2)))) := by
    have hd : ∀ e' : Env, pt (applyOps doubleFields e') 0 1 2 = double (pt e' 0 1 2) := fun _ => rfl
    simp only [dblEnv, hd]
  rw [h, dblEnv_keep 11 (by simp), hd, h4,
    pt_congr' (dblEnv_keep 3 (by simp) 4 e) (dblEnv_keep 4 (by simp) 4 e) (dblEnv_keep 5 (by simp) 4 e)]
  rfl

theorem combFinish_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base)
    (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa combFinish s fun t => Keeps (.esi :: workRegs) s t ∧ WsOut2 base 64 2816 ACC 512 s.mem t.mem ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.pointAdd
        (double (double (double (double (pt (E s.mem base) 0 1 2))))) (pt (E s.mem base) 3 4 5) := by
  unfold combFinish
  refine WP.seq (WP.mono (double4_ok hs hc) fun s1 ⟨k1, o1, e1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  have hc1 : CallCtx s1 base := hc.keep (k1.1 _ (by decide))
  rw [copyC_impl, addTake_impl]
  refine WP.seq (WP.mono (ops_ok hs1 hc1 copyFields) fun s2 ⟨k2, e2⟩ => ?_)
  refine WP.mono (ops_ok (k2.scr hs1) (k2.ctx hc1) (addFields ++ takeFields)) fun t ⟨kt, et⟩ => ?_
  have k := k2.trans kt
  exact ⟨k1.trans (k.regs.mono (fun _ h => List.mem_cons_of_mem _ h)), o1.trans k.mem, by rw [et, e2, e1]; exact finish_pt _ hd⟩

/-! ## The whole comb -/

/-- What the comb changes: `esi` and the field operations' registers, the slots, the field
functions' working space and the word at `TPTR`. -/
structure CombKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.esi :: workRegs) s t
  mem : WsOut2 base 64 2816 ACC 516 s.mem t.mem

theorem wsWide {base : Addr} {m m' : Mem} (h : WsOut2 base 64 2816 ACC 512 m m') : WsOut2 base 64 2816 ACC 516 m m' :=
  fun p h8 h1 h2 => h p h8 h1 (by rcases h2 with h2 | h2 <;> [exact Or.inl h2; exact Or.inr (by omega_using [h2])])

theorem tblSetup_ok {s : State} {base : Addr} (hs : Scr s base) (hc : CallCtx s base) :
    WP isa tblSetup s fun t => Keeps [.eax, .ecx] s t ∧ word t.mem base TPTR = s.syms combSym ∧
      WsOut2 base 64 2816 ACC 516 s.mem t.mem ∧ (∀ d, d + 4 ≤ TPTR → word t.mem base d = word s.mem base d) ∧
      ∀ t' < 456, t.mem (off base (BITS + t')) = s.mem (off base (BITS + t')) := by
  have h4 : 4 ≤ (s.gpr .esp).toNat := Nat.le_trans (by decide) hc.sp
  unfold tblSetup
  refine WP.seq (WP.mono (symFrame_ok combSym s h4) fun u hu => ?_)
  have ku : Keeps [.eax, .ecx] s u := ⟨hu.gpr, hu.rd, hu.wr⟩
  have mu : ∀ p, ofs base p < 8192 → u.mem p = s.mem p := fun p hp => by
    refine hu.frame p fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    intro hx
    refine hc.sep p ?_ (below_sub (by decide) hc.sp p hx)
    simp only [Region.Contains]
    simp only [ofs] at hp
    omega_using [hp]
  refine store_ok (hs.of_keeps ku (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have ot : Outside base TPTR 4 u.mem t.mem := by rw [ht.mem]; exact writeW_outside _ _ _ (by decide)
  have hT : TPTR = 4096 := rfl
  have hA : ACC = 3584 := rfl
  have hB : BITS = 3072 := rfl
  refine ⟨ku.trans (ht.rest _), ?_, fun p h8 h1 h2 => ?_, fun d hd => ?_, fun i hi => ?_⟩
  · rw [ht.mem, hu.addr]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ot p (by omega_using [h2, hT, hA]), mu p h8]
  · rw [ot.word (Or.inl hd) (by omega_using [hd, hT])]
    exact (Mem.readW_congr fun i hi => (mu _ (by rw [ofs_off base (by omega_using [hd, hT, hi])]; omega_using [hd, hT, hi])).symm).symm
  · have e : ofs base (off base (BITS + i)) = BITS + i := ofs_off' base (by omega_using [hi, hB])
    rw [ot _ (by rw [e]; omega_using [hi, hB, hT]), mu _ (by rw [e]; omega_using [hi, hB])]

/-- The slots before the comb: both accumulators at `[G] B`, 1, `d` and zero. -/
structure CombInit (e : Env) : Prop where
  a : pt e 0 1 2 = signedSum 0 1 0
  c : pt e 3 4 5 = signedSum 0 0 0
  one : e 10 = 1
  d : e 11 = Spec.Ed448.d
  zero : e 21 = 0

theorem combInit (e : Env) (he : ∀ i : Index, e i = Proof.X448.toFe (Impl.Ed448.X86.combVal i.val)) : CombInit e := by
  have v : ∀ i : Index, ∀ x : Spec.X448.Fe, Impl.Ed448.X86.combVal i.val = x.val → e i = x := fun i x h => by
    rw [he, h, Proof.X448.toFe_self]
  have g1 : e 0 = Impl.X448.baseG57.1 := v 0 _ rfl
  have g2 : e 1 = Impl.X448.baseG57.2 := v 1 _ rfl
  have g3 : e 2 = 1 := v 2 1 (by decide +kernel)
  have g4 : e 3 = Impl.X448.baseG57.1 := v 3 _ rfl
  have g5 : e 4 = Impl.X448.baseG57.2 := v 4 _ rfl
  have g6 : e 5 = 1 := v 5 1 (by decide +kernel)
  refine ⟨?_, ?_, v 10 1 (by decide +kernel), v 11 _ rfl, v 21 0 (by decide +kernel)⟩
  · simp only [pt, g1, g2, g3, signedSum]
  · simp only [pt, g4, g5, g6, signedSum]

/-- `[k] B` into slots 0–2. -/
theorem combBase_ok {s : State} {base : Addr} {P : BitVec 32} (hs : Scr s base) (hc : CallCtx s base)
    (hP : s.syms combSym = P) (ht : TblMem P s) {k : Nat} (hb : BitsAtB base k s.mem) (hi : CombInit (E s.mem base)) :
    WP isa combBase s fun t => CombKeep base s t ∧ pt (E t.mem base) 0 1 2 = signedComb k := by
  unfold combBase
  refine WP.seq (WP.mono (WP.withFrame (NoSp.of_all (by lit_decide)) (Nat.le_trans (by lit_decide) hc.sp)
    (tblSetup_ok hs hc)) fun s1 ⟨⟨k1, p1, o1, w1, b1⟩, f1⟩ => ?_)
  have hs1 := hs.of_keeps k1 (by decide)
  have hc1 : CallCtx s1 base := hc.keep (k1.1 _ (by decide))
  have t1 : TblAt base P s1 := ⟨ht.frame (k1.1 _ (by decide)) k1.2.1 k1.2.2
    (Frame.below_mono f1 (by lit_decide) hc.sp), p1.trans hP⟩
  have e1 : E s1.mem base = E s.mem base := funext fun i => by
    refine congrArg Proof.X448.toFe (Proof.X25519.X86.num_congr fun j hj => congrArg BitVec.toNat (w1 _ ?_))
    have := slot_range i
    simp only [TPTR]
    omega_using [this, hj]
  have hb1 : BitsAtB base k s1.mem := fun t h => (b1 t h).trans (hb t h)
  refine WP.seq (WP.mono (combLoop_ok (P := P) (k := k) (s₀ := s1) hb1 fun s' h1 h2 h3 h4 h5 => ?_) fun s2 I => ?_)
  · have k' : Keeps [.esi] s1 s' := ⟨fun r hr => h2 r (by simpa using hr), h4, h5⟩
    exact ⟨hs1.of_keeps k' (by decide), hc1.keep (h2 _ (by decide)), k'.mono (by simp), h1,
      by rw [h3]; exact WsOut2.refl _ _ _ _ _ _,
      t1.frame (h2 _ (by decide)) h4 h5 (by rw [h3]; exact Frame.refl _ _) (by rw [h3]),
      by rw [h3, e1, hi.a]; rfl, by rw [h3, e1, hi.c]; rfl, by rw [h3, e1, hi.one], by rw [h3, e1, hi.d],
      by rw [h3, e1, hi.zero]⟩
  · refine WP.mono (combFinish_ok I.scr I.ctx I.d) fun t ⟨kt, ot, et⟩ => ⟨⟨?_, ?_⟩, ?_⟩
    · exact (k1.mono (by decide)).trans (I.regs.trans kt)
    · exact o1.trans ((wsWide I.mem).trans (wsWide ot))
    · rw [et, I.a, I.c]; rfl

end VG.Proof.Ed448.X86
