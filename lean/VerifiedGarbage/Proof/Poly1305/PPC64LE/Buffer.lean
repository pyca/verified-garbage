module

import VerifiedGarbage.Proof.Poly1305.PPC64LE.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Setup
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Poly1305 on PPC64LE: the buffer

Weakest-precondition rules for the instruction forms of the byte loops and the
counts of `update` and `finalize`, exposing only what changes; bytes stored
into the buffer (bytes 56–71 of the state), which leave the coefficients
alone, and absorbing the buffer as a block. As on AArch64.
-/

@[expose] public section


namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_stw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

end

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

/-! ## The buffer -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := rfl

theorem and15 (x : BitVec 64) :
    x &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 15).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]


/-- The buffer. -/
abbrev bfR (st : Addr) : Region := ⟨off st 56, 16⟩

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `[x + 56]` for `x = st + j`. -/
theorem bufB_of (st : Addr) (j : Nat) : st + BitVec.ofNat 64 j + BitVec.ofNat 64 56 = bufB st j := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem bfR_contains (st : Addr) {d n : Nat} (h : d + n ≤ 16) :
    (bfR st).Contains (off st 56 + BitVec.ofNat 64 d) n := by
  exact Offset.contains_base _ h (by omega_using [h])

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [bufB] using he)
  rw [toNat_ofNat_lt (by omega_using [hj]), toNat_ofNat_lt (by omega_using [hk])] at this
  omega_using [h, this]

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} {st : Addr} (hw : sR st ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB st k) 1 :=
  ⟨_, hw, contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) :=
  Offset.sub st (by decide) (by decide)

theorem bfR_disjoint_cR (st : Addr) : (bfR st).Disjoint (cR st) :=
  Offset.disjoint st (by decide) (by decide) (by decide)

/-- The first `n` bytes of the buffer are not where the coefficients are. -/
theorem buf_disjoint_cR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (cR st) :=
  (bfR_disjoint_cR st).sub_left (Region.sub_prefix hn)

theorem coef_facts : ∀ k < 5, ∀ i < 5, 72 ≤ coef k i ∧ coef k i + 4 ≤ 108 := by decide +kernel

/-- The coefficients are unchanged by writes to the buffer. -/
theorem Coefs.frame {m m' : Mem} {st : Addr} {R : Nat} (h : Coefs m st R) (hf : Frame [bfR st] m m') :
    Coefs m' st R := by
  intro k hk i hi
  obtain ⟨c₁, c₂⟩ := coef_facts k hk i hi
  rw [← h k hk i hi]
  refine congrArg BitVec.toNat (hf.readW (r := ⟨off st (coef k i), 4⟩) (Region.contains_self _ _) ?_
    (by decide))
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint st (by omega_using [c₁, c₂]) (by omega_using [c₁, c₂]) (by decide)

/-- The coefficient words may be read when the state may be. -/
theorem coefIn_of {s : State} (hw : sR (s.gpr .r3) ∈ s.wr) : CoefIn s := fun off h₁ h₂ =>
  ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])⟩

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) (pad : Bool) {R : Nat} (hR : R < 2 ^ 128) (hm : s.gpr .r20 = M26)
    (hco : Coefs s.mem (s.gpr .r3) R) (hw : sR (s.gpr .r3) ∈ s.wr) :
    WP isa (.block (([.addi .r4 .r3 56] : List Instr) ++ absorb pad)) s fun s' =>
      (Bounds s → hv s' % P = ((hv s + (leNum (bytesAt s.mem (off (s.gpr .r3) 56) 16) +
        2 ^ 128 * pad.toNat)) * R) % P ∧ Bounds s') ∧ Keeps (.r4 :: absorbRegs) s s' := by
  refine WP.block_append (wp_addi (by decide) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have r3₁ : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (by decide)
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r4 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [u₁.rd, u₁.wr, u₁.gpr, ← off, off_off]
    exact ⟨_, List.mem_append_right _ hw, contains_off (by omega_using [hd]) (by omega_using [hd])⟩
  refine WP.mono (absorb_ok s₁ pad hR (by rw [u₁.other _ (by decide)]; exact hm)
    (by rw [u₁.mem, r3₁]; exact hco) (coefIn_of (by rw [u₁.wr, r3₁]; exact hw)) (hin 0 (by decide))
    (hin (0 + 8) (by decide))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, ?_⟩
  · have hv₁ : hv s₁ = hv s := by
      simp only [hv, v, u₁.other .r7 (by decide), u₁.other .r8 (by decide), u₁.other .r9 (by decide),
        u₁.other .r10 (by decide), u₁.other .r11 (by decide)]
    have hb₁ : Bounds s₁ := by
      simpa only [Bounds, v, u₁.other .r7 (by decide), u₁.other .r8 (by decide),
        u₁.other .r9 (by decide), u₁.other .r10 (by decide), u₁.other .r11 (by decide)] using hb
    obtain ⟨hv', hb'⟩ := ha hb₁
    refine ⟨?_, hb'⟩
    rw [hv', hv₁, leNum_key, u₁.mem, u₁.gpr]
  · refine ⟨fun r hr => ?_, by rw [k.2.1, u₁.mem], by rw [k.2.2.1, u₁.rd], by rw [k.2.2.2, u₁.wr]⟩
    simp only [List.mem_cons, not_or] at hr
    rw [k.1 r (by simpa using hr.2), u₁.other r hr.1]

/-! ## Copying bytes into the buffer -/

theorem copyIn_eq : copyIn = .loop (.block copyBody) (.nonzero .d .r14) := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
from byte `j0` on, from the state `sI` (where `x11 = st + j0`): after `j` bytes. -/
structure CopyInv (sI : State) (m₀ : Mem) (src : Addr) (j0 n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  r4 : s.gpr .r4 = src + BitVec.ofNat 64 j
  r15 : s.gpr .r15 = sI.gpr .r3 + BitVec.ofNat 64 (j0 + j)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .r4 → r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = writeBytes sI.mem (bufB (sI.gpr .r3) j0) ((bytesAt m₀ src n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (m₀ : Mem) (src : Addr) (n : Nat) : Prop :=
  ∀ i < n, InRegions (sI.rd ++ sI.wr) (src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bfR (sI.gpr .r3)).Contains (src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (src + BitVec.ofNat 64 i) = m₀ (src + BitVec.ofNat 64 i)

theorem copy_step {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    (hw : sR (sI.gpr .r3) ∈ sI.wr) (hs : SrcOk sI m₀ src n) {j : Nat} (hj : j < n) {s : State}
    (h : CopyInv sI m₀ src j0 n j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI m₀ src j0 n (j + 1) s' ∧ s'.gpr .r14 = BitVec.ofNat 64 (n - (j + 1)) := by
  obtain ⟨hin, hnb, hm₀⟩ := hs j hj
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR (sI.gpr .r3)).Contains (bufB (sI.gpr .r3) j0) ((bytesAt m₀ src n).take j).length := by
    rw [bufB_eq, List.length_take]; exact bfR_contains _ (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_lbz (t := .r16) (a := src + BitVec.ofNat 64 j) (by decide) (by decide)
    (by rw [h.r4, add_ofNat_zero]) (by rw [h.rd, h.wr]; exact hin) fun s₁ u₁ => ?_
  refine wp_stb (t := .r16) (a := bufB (sI.gpr .r3) (j0 + j)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.r15, bufB_of]) (by rw [u₁.wr, h.wr]; exact bufB_in hw (by omega_using [hj0, hj, hxs]))
    fun s₂ m₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_subi (by decide) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r14 → r ≠ .r15 → r ≠ .r4 → r ≠ .r16 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, m₂.gpr, u₁.other r h4]
  have hx10 : s₅.gpr .r14 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .r14 (by decide), u₃.other .r14 (by decide), m₂.gpr, u₁.other .r14 (by decide),
      h.r14, show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega_using [hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, hx10, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, hx10⟩
  · rw [u₅.other .r4 (by decide), u₄.other .r4 (by decide), u₃.gpr, m₂.gpr, u₁.other .r4 (by decide), h.r4,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.other .r15 (by decide), u₄.gpr, u₃.other .r15 (by decide), m₂.gpr, u₁.other .r15 (by decide),
      h.r15, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g r h2 h3 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : bufB (sI.gpr .r3) (j0 + j) =
        bufB (sI.gpr .r3) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (s₁.gpr .r16).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]; simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, hv, u₁.mem, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .r3) ∈ sI.wr) (hs : SrcOk sI m₀ src n) (hx1 : sI.gpr .r4 = src)
    (hx11 : sI.gpr .r15 = sI.gpr .r3 + BitVec.ofNat 64 j0) (hx10 : sI.gpr .r14 = BitVec.ofNat 64 n) :
    WP isa copyIn sI (CopyInv sI m₀ src j0 n n) := by
  have h₀ : CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hx1, add_ofNat_zero], by rw [hx11, Nat.add_zero], by rw [hx10, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hj0 hw hs hj hc) fun s' ⟨hc', hx⟩ => ?_
  have hev : isa.eval (.nonzero .d .r14) s' = some (!(BitVec.ofNat 64 (n - (j + 1)) == 0)) := by
    rw [eval_nonzero, hx]; rfl
  rw [ofNat_beq_zero (by omega_using [hj0, hn, hj])] at hev
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by rw [hev]; simp only [hl, decide_true, Bool.not_true], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by rw [hev]; simp only [hl, decide_false, Bool.not_false], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .r3) 56) (j0 + n) =
      bytesAt sI.mem (off (sI.gpr .r3) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .r3) 56) j0 (bytesAt m₀ src n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs]), bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .r3)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine writeBytes_frame _ _ _ ?_
  rw [bufB_eq, hxs]; exact bfR_contains _ hj0

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.PPC64LE
