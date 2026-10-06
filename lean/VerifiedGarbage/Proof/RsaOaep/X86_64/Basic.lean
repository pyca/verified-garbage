import VerifiedGarbage.Impl.RsaOaep.X86_64
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSAES-OAEP on x86-64: addresses, the frame and the working space

The memory operands (`ea_sp`, `ea_ix`, `ea_at`), bytes at offsets of a
buffer and the effect of a store on them (`wb_off`, `ww_off`), the frame and
the working space every piece of the code works in (`Lay`), the counter of
the byte loops (`stepR_ok`, `stepI_ok`), and the masks of equality the code
computes without branches (`eqMask_val`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn load64_eq load32_eq load8_eq store64_eq store32_eq store8_eq)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)

/-! ## Memory operands -/

theorem ofInt_nat (d : Nat) : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := BitVec.ofInt_natCast 64 d

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = off (t.gpr .rsp) d := by
  simp only [State.ea, sp, ofInt_nat, off]

theorem ea_ix (t : State) (b i : Reg) (d : Nat) : t.ea (ix b i d) = t.gpr b + t.gpr i + BitVec.ofNat 64 d := by
  simp only [State.ea, ix, ofInt_nat, BitVec.mul_one]

theorem ea_ix0 (t : State) (b i : Reg) : t.ea (ix b i) = t.gpr b + t.gpr i := by
  rw [ea_ix]; exact BitVec.add_zero _

theorem ea_at (t : State) (b : Reg) (d : Nat) : t.ea (at_ b d) = off (t.gpr b) d := by
  simp only [State.ea, at_, ofInt_nat, off]

theorem ea_at0 (t : State) (b : Reg) : t.ea (at_ b) = t.gpr b := by
  simp only [State.ea, at_, Int.cast_ofNat_Int, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem ea_arg (t : State) (j : Nat) : t.ea (arg j) = off (t.gpr .rsp) (frameBytes + 8 + 8 * j) := ea_sp t _

/-- `p + i + d = p + (i + d)` for an index `i`. -/
theorem off_ix (p : Addr) (i d : Nat) : p + BitVec.ofNat 64 i + BitVec.ofNat 64 d = off p (i + d) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Bytes at offsets of a buffer -/

/-- A byte store to `p + a`, read at `p + b`. -/
theorem wb_off (m : Mem) (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (v : Byte) :
    (m.writeW (off p a) v) (off p b) = if b = a then v else m (off p b) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases h : b = a
  · subst h; simp
  · simp only [h, ite_false, ifn (Offset.add_ofNat_ne p hb ha h)]

/-- A store of `w / 8` bytes to `p + a`, read at `p + b`. -/
theorem ww_off (m : Mem) (p : Addr) {a b w : Nat} (ha : a + w / 8 ≤ 2 ^ 64) (hb : b < 2 ^ 64) (v : BitVec w) :
    (m.writeW (off p a) v) (off p b) =
      if a ≤ b ∧ b < a + w / 8 then (v.setWidth (8 * (w / 8))).extractLsb' (8 * (b - a)) 8 else m (off p b) := by
  simp only [Mem.writeW, Mem.write, off]
  have e := Offset.lt_iff (p + BitVec.ofNat 64 b) p ha
  rw [Mem.sub_ofNat_toNat p hb] at e
  by_cases h : a ≤ b ∧ b < a + w / 8
  · rw [ifp (e.mpr h), ifp h, Offset.sub_toNat p h.1 hb]
  · rw [ifn (fun h' => h (e.mp h')), ifn h]

/-- The bytes at `p + o`, from the bytes at offsets of `p`. -/
theorem bytesAt_off (m : Mem) (p : Addr) (o n : Nat) :
    Spec.Rsa.bytesAt m (off p o) n = (List.range n).map fun i => m (off p (o + i)) := by
  simp only [Spec.Rsa.bytesAt, off_off]

/-! ## The frame and the working space

`F` is `rsp` in the frame, whose `frameBytes` bytes are writable; `S` the
working space, of which the first 8192 bytes are ours, in its slot; the
16 bytes a call of a streaming hash function uses are just below it. -/

/-- The bytes below `F` that a call of a streaming hash function uses: its
return address and its own call's. -/
abbrev retR (F : Addr) : Region := below F 16

structure Lay (t : State) (F S : Addr) : Prop where
  rsp : t.gpr .rsp = F
  fr : (⟨F, frameBytes⟩ : Region) ∈ t.wr
  F8 : 8 ≤ F.toNat
  Fw : F.toNat + frameBytes + 8 ≤ 2 ^ 64
  sc : Scr t S oRsa
  slot : word t.mem F sScr = S
  dFS : Region.Disjoint ⟨F, frameBytes⟩ ⟨S, oRsa⟩
  dRS : Region.Disjoint (retR F) ⟨S, oRsa⟩

theorem Lay.frScr {t : State} {F S : Addr} (L : Lay t F S) : Scr t F frameBytes :=
  Scr.of_mem L.fr (by have := L.Fw; omega)

theorem Lay.Sw {t : State} {F S : Addr} (L : Lay t F S) : S.toNat + oRsa ≤ 2 ^ 64 := L.sc.nowrap

/-- `Lay` holds of a state with the same registers `rsp`, regions and the
slot of `scratch`. -/
theorem Lay.congr {t t' : State} {F S : Addr} (L : Lay t F S) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) (hs : word t'.mem F sScr = word t.mem F sScr) : Lay t' F S :=
  ⟨hsp.trans L.rsp, hwr ▸ L.fr, L.F8, L.Fw, L.sc.congr hwr, hs.trans L.slot, L.dFS, L.dRS⟩

/-- A slot is readable. -/
theorem Lay.ld {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (off F d) 8 := L.frScr.ld hd

theorem Lay.st {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    InRegions t.wr (off F d) 8 := L.frScr.st hd

/-- Bytes of our working space. -/
theorem Lay.sld8 {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 1 ≤ oRsa) :
    InRegions (t.rd ++ t.wr) (off S d) 1 :=
  let ⟨_, hm, hc⟩ := L.sc.region hd (by decide)
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Lay.sst8 {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 1 ≤ oRsa) :
    InRegions t.wr (off S d) 1 := L.sc.st8 hd

theorem Lay.sld {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ oRsa) :
    InRegions (t.rd ++ t.wr) (off S d) 8 := L.sc.ld hd

theorem Lay.sst {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ oRsa) :
    InRegions t.wr (off S d) 8 := L.sc.st hd

theorem Lay.sst4 {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 4 ≤ oRsa) :
    InRegions t.wr (off S d) 4 :=
  let ⟨_, hm, hc⟩ := L.sc.region hd (by decide)
  ⟨_, hm, hc⟩

/-! ## Masks -/

/-- `cmp d, 1; sbb d, d` with `d = a ⊕ b`: all ones iff `a = b`. -/
def eqM (a b : BitVec 64) : BitVec 64 := if a = b then BitVec.allOnes 64 else 0

theorem cmp_sbb (x : BitVec 64) :
    x - x - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))) =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  rw [BitVec.sub_self]
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < (1 : BitVec 64).toNat := by
      intro h'
      apply h
      apply BitVec.eq_of_toNat_eq
      have : (1 : BitVec 64).toNat = 1 := rfl
      simp only [this] at h'
      show x.toNat = 0; omega
    simp only [this, decide_false, h, ite_false]
    decide

theorem xor_eq_zero (a b : BitVec 64) : (a ^^^ b = 0) ↔ a = b := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]

theorem eqM_of (a b : BitVec 64) : (if a ^^^ b = 0 then BitVec.allOnes 64 else 0) = eqM a b := by
  unfold eqM
  by_cases h : a = b
  · rw [ifp ((xor_eq_zero a b).mpr h), ifp h]
  · rw [ifn (fun h' => h ((xor_eq_zero a b).mp h')), ifn h]

/-! ## The working space and the frame, as functions

`Rep m F S V W`: in memory `m`, byte `o` of our working space is `V o`, and
word `k` of the frame is `W k`. A store to either changes the one function
at the bytes or the word it writes (`Rep.wb`, `Rep.wq`, `Rep.wd`, `Rep.wf`). -/

/-- `f` with the value at `a` replaced by `v`. -/
def upd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α := fun x => if x = a then v else f x

/-- The frame's words. -/
def nW : Nat := frameBytes / 8

structure Rep (m : Mem) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) : Prop where
  scr : ∀ o < oRsa, m (off S o) = V o
  fr : ∀ k < nW, word m F (8 * k) = W k

theorem cF (F : Addr) {k : Nat} (hk : k < nW) : Region.Contains ⟨F, frameBytes⟩ (off F (8 * k)) 8 :=
  Offset.contains_base F (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)

theorem cS (S : Addr) {o n : Nat} (h : o + n ≤ oRsa) : Region.Contains ⟨S, oRsa⟩ (off S o) n :=
  Offset.contains_base S h (by unfold oRsa at *; omega)

/-- Where the frame and the working space are. -/
structure Geo (F S : Addr) : Prop where
  Fw : F.toNat + frameBytes + 8 ≤ 2 ^ 64
  Sw : S.toNat + oRsa ≤ 2 ^ 64
  dFS : Region.Disjoint ⟨F, frameBytes⟩ ⟨S, oRsa⟩
  dRS : Region.Disjoint (retR F) ⟨S, oRsa⟩

theorem Geo.dRS' {F S : Addr} (G : Geo F S) {o : Nat} (ho : o < oRsa) : ¬ (retR F).Contains (off S o) 1 :=
  fun hc => G.dRS _ hc ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide))

theorem Lay.geo {t : State} {F S : Addr} (L : Lay t F S) : Geo F S := ⟨L.Fw, L.Sw, L.dFS, L.dRS⟩

/-- The bytes `x` of a store `v` of `n` bytes at `o`, in order. -/
def stBytes {w : Nat} (v : BitVec w) (o : Nat) (V : Nat → Byte) : Nat → Byte :=
  fun x => if o ≤ x ∧ x < o + w / 8 then (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - o)) 8 else V x

theorem Rep.ws {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {o w : Nat} (ho : o + w / 8 ≤ oRsa) (v : BitVec w) :
    Rep (m.writeW (off S o) v) F S (stBytes v o V) W where
  scr x hx := by
    rw [ww_off m S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega), stBytes, R.scr x hx]
  fr k hk := by
    rw [Bignum.word, Mem.readW_writeW_sep (Region.Disjoint.sep G.dFS (cF F hk) (cS S ho)) (by decide)]
    exact R.fr k hk

theorem stBytes_byte (v : Byte) (o : Nat) (V : Nat → Byte) : stBytes v o V = upd V o v := by
  funext x
  simp only [stBytes, upd]
  by_cases h : x = o
  · subst h; simp
  · rw [ifn (by omega), ifn h]

/-- A byte store to the working space. -/
theorem Rep.wb {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {o : Nat} (ho : o < oRsa) (v : Byte) :
    Rep (m.writeW (off S o) v) F S (upd V o v) W := by
  have := R.ws G (o := o) (w := 8) (by omega) v
  rwa [stBytes_byte] at this

/-- A word store to the frame. -/
theorem Rep.wf {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {k : Nat} (hk : k < nW) (v : BitVec 64) :
    Rep (m.writeW (off F (8 * k)) v) F S V (upd W k v) where
  scr x hx := by
    rw [Mem.writeW, Mem.write_apply (fun h => G.dFS _ ((cF F hk).byte h) ((cS S (o := x) (n := 1) (by omega)).byte
      (by rw [BitVec.sub_self]; decide)))]
    exact R.scr x hx
  fr j hj := by
    by_cases h : j = k
    · subst h
      rw [Bignum.word, Mem.readW_writeW_self64, upd, ifp rfl]
    · rw [Bignum.word, Mem.readW_writeW_sep (Offset.sep F (by unfold nW frameBytes at *; omega)
        (by unfold nW frameBytes at *; have := G.Fw; omega) (by unfold nW frameBytes at *; have := G.Fw; omega))
        (by decide), upd, ifn h]
      exact R.fr j hj

/-- Bytes of our working space are writable. -/
theorem Lay.cov {t : State} {F S : Addr} (L : Lay t F S) {o n : Nat} (h : o + n ≤ oRsa) :
    Covers [⟨off S o, n⟩] t.wr := by
  obtain ⟨⟨B₀, o₀, L₀, hm, hb, hL, _⟩, _⟩ := L.sc
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hm, o₀ + o, by rw [hb, off_off], by simp only; omega⟩

/-- Whether `o` is in one of the ranges `rgs` of offsets. -/
def inR (rgs : List (Nat × Nat)) (o : Nat) : Prop := ∃ p ∈ rgs, p.1 ≤ o ∧ o < p.1 + p.2

instance (rgs : List (Nat × Nat)) (o : Nat) : Decidable (inR rgs o) :=
  inferInstanceAs (Decidable (∃ p ∈ rgs, p.1 ≤ o ∧ o < p.1 + p.2))

/-- The regions of the ranges `rgs` of our working space. -/
def regs (S : Addr) (rgs : List (Nat × Nat)) : List Region := rgs.map fun p => ⟨off S p.1, p.2⟩

theorem retR_disjoint_F (F : Addr) {k : Nat}
    (hk : k < nW) : Region.Disjoint (⟨off F (8 * k), 8⟩ : Region) (retR F) :=
  Offset.disjoint_below F (by unfold nW frameBytes at *; omega)

/-- What a callee or a block writing only within the ranges `rgs` of our
working space and the return address below the frame leaves. -/
theorem Rep.frame {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hF : Frame (regs S rgs ++ [retR F]) m m') :
    Rep m' F S (fun o => if inR rgs o then m' (off S o) else V o) W where
  scr o ho := by
    split
    · rfl
    · rename_i hn
      rw [hF _ fun r hr hc => ?_, R.scr o ho]
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        apply hn
        refine ⟨p, hp, ?_⟩
        have := hrg p hp
        have := (Offset.lt_iff (off S o) S (d := p.1) (n := p.2) (by have := G.Sw; unfold oRsa at *; omega)).mp hc
        rwa [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega)] at this
      · simp only [List.mem_singleton] at hr; subst hr
        exact G.dRS' ho hc
  fr k hk := by
    rw [Bignum.word, hF.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact R.fr k hk
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact Region.Disjoint.sub_left (Region.Disjoint.sub_right G.dFS (Offset.sub_base S (hrg p hp)))
        (Offset.sub_base F (by unfold nW frameBytes at *; omega))
    · simp only [List.mem_singleton] at hr; subst hr
      exact retR_disjoint_F F hk

/-! ## Counters -/

theorem ofNat_add_lit (a c : Nat) :
    BitVec.ofNat 64 a + (no_index (OfNat.ofNat c) : BitVec 64) = BitVec.ofNat 64 (a + c) := by
  rw [BitVec.ofNat_add]; rfl

theorem sx_lit (c : Nat) (h : c < 2 ^ 31) :
    BitVec.signExtend 64 (no_index (OfNat.ofNat c) : BitVec 32) = BitVec.ofNat 64 c :=
  VG.Proof.MlKem.X86_64.sx_ofNat h

/-- Bytes written to the working space at `o`. -/
theorem Rep.wbs {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {o : Nat} {xs : List Byte} (ho : o + xs.length ≤ oRsa) :
    Rep (VG.WriteBytes.writeBytes m (off S o) xs) F S
      (fun x => if o ≤ x ∧ x < o + xs.length then xs.getD (x - o) 0 else V x) W where
  scr x hx := by
    simp only [VG.WriteBytes.writeBytes]
    have e := Offset.lt_iff (off S x) S (d := o) (n := xs.length) (by have := G.Sw; unfold oRsa at *; omega)
    rw [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega)] at e
    by_cases h : o ≤ x ∧ x < o + xs.length
    · rw [ifp (e.mpr h), ifp h, Offset.sub_toNat S h.1 (by unfold oRsa at *; omega)]
    · rw [ifn (fun h' => h (e.mp h')), ifn h]; exact R.scr x hx
  fr k hk := by
    rw [Bignum.word]
    refine Eq.trans (Mem.readW_congr fun i hi => ?_) (R.fr k hk)
    simp only [VG.WriteBytes.writeBytes]
    rw [ifn]
    intro h
    exact G.dFS _ ((cF F hk).byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega))
      ((cS S (o := o) (n := xs.length) ho).byte h)

theorem shr_ofNat {x : Nat} (k : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem mask_and (x y : Byte) (c : Bool) :
    (BitVec.setWidth 64 y ||| BitVec.setWidth 64 x &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool c))).setWidth 8 =
      y ||| (if c then x else 0) := by
  cases c
  · simp
  · simp only [ite_true]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    ext i hi
    simp [BitVec.getElem_or]

theorem xor_lt_one {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide ((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b).toNat < BitVec.toNat (1 : BitVec 64)) = decide (a = b) := by
  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b ≠ 0 := fun e =>
      h (by have := congrArg BitVec.toNat ((xor_eq_zero _ _).mp e); simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this)
    simp only [h, decide_false, decide_eq_false_iff_not, Nat.lt_one_iff]
    exact fun e => this (BitVec.eq_of_toNat_eq e)

/-- Offsets in different blocks differ. -/
theorem blk_ne {B b c x y : Nat} (hx : x < B) (hy : y < B) (h : b ≠ c) : B * b + x ≠ B * c + y := by
  intro e
  apply h
  have hB : 0 < B := by omega
  have : (B * b + x) / B = (B * c + y) / B := by rw [e]
  rwa [Nat.mul_add_div hB, Nat.mul_add_div hB, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy, Nat.add_zero,
    Nat.add_zero] at this

theorem upd_self {α : Type} (f : Nat → α) (a : Nat) : upd f a (f a) = f := by
  funext x; simp only [upd]; split <;> simp_all

theorem sel_byte (a s : Byte) (c : Bool) :
    (BitVec.setWidth 64 s ^^^ ((BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 s) &&&
      (0#64 - BitVec.setWidth 64 (BitVec.ofBool c)))).setWidth 8 = if c then a else s := by
  cases c
  · simp
  · simp only [ite_true]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      BitVec.xor_comm (BitVec.setWidth 64 a), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp

theorem WP.seq_assoc {A B C : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq A B) C) s Q) :
    WP isa (.seq A (.seq B C)) s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  cases he with | seq h1 h2 => cases h1 with | seq ha hb => exact ⟨_, _, .seq ha (.seq hb h2), hq⟩

theorem inR_nil (o : Nat) : ¬ inR [] o := by simp [inR]

theorem inR_cons (a n : Nat) (rgs : List (Nat × Nat)) (o : Nat) :
    inR ((a, n) :: rgs) o ↔ (a ≤ o ∧ o < a + n) ∨ inR rgs o := by
  simp [inR]

theorem range_map_getD {xs : List Byte} {n : Nat} (h : n ≤ xs.length) :
    (List.range n).map (fun i => xs.getD i 0) = xs.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp at h₁; omega)]
  rfl

theorem slot_eq (d : Nat) (k : Nat) (h : d = 8 * k) (m : Mem) (F : Addr) : word m F d = word m F (8 * k) := by
  rw [h]

/-- `Lay` after a block that changed memory only as `Rep` says, keeping `W`. -/
theorem Lay.of_rep {u u' : State} {F S : Addr} (L : Lay u F S) {V V' : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (R' : Rep u'.mem F S V' W) (hsp : u'.gpr .rsp = u.gpr .rsp) (hwr : u'.wr = u.wr) :
    Lay u' F S :=
  L.congr hsp hwr (by rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R'.fr 14 (by decide), R.fr 14 (by decide)])


theorem trunc_zext (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := by simp

theorem off_plus (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A slot, read. -/
theorem Rep.rd {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d : Nat}
    (k : Nat) (hd : d = 8 * k) (hk : k < nW) : m.readW (off F d) 64 = W k := by
  subst hd; exact R.fr k hk

/-- `Lay` after stores that keep the slot of `scratch`. -/
theorem Lay.of_rep' {u u' : State} {F S : Addr} (L : Lay u F S) {V V' : Nat → Byte} {W W' : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (R' : Rep u'.mem F S V' W') (h14 : W' 14 = W 14) (hsp : u'.gpr .rsp = u.gpr .rsp)
    (hwr : u'.wr = u.wr) : Lay u' F S :=
  L.congr hsp hwr (by rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R'.fr 14 (by decide), R.fr 14 (by decide), h14])

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hx] using this
  · intro h; subst h; rfl

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) : off p a - BitVec.ofNat 64 b = off p (a - b) := by
  simp only [off]
  rw [BitVec.sub_eq_iff_eq_add, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.sub_add_cancel h]

theorem off_sub1 (p : Addr) {a : Nat} (h : 1 ≤ a) : off p a - 1 = off p (a - 1) := off_sub p h

end VG.Proof.RsaOaep.X86_64
