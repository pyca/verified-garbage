module

public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Loop
public import VerifiedGarbage.Impl.AesCfb8.PPC64LE
public import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes

/-! ### `AesCfb8.PPC64LE.Steps`, which only this module used -/

section

/-!
# AES-CFB8 on PPC64LE: the code between the calls

The straight-line pieces of a byte, each run in continuation-passing style:
the data byte XORed with the first byte of the enciphered block (`encByte`,
`decByte`), and the input block shifted (`shift`), its two words each
becoming their upper seven bytes with the next byte above them, the memory
AArch64's `extr` leaves (`shiftMemX`, `Proof/AesCfb8/Mem.lean`, by
`extr_eq`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCfb8.PPC64LE
open VG.Impl.AesCbc.PPC64LE (cOff)

theorem read1 (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [BitVec.add_zero] at this
  rw [← this]
  exact (BitVec.extractLsb'_eq_self (x := m.read a 1)).symm

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a v := by
  simp [Mem.writeW]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbz t, off(n)`. -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read1]

/-- `stb t, off(n)`. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha, write1]

/-- `or d, n, m`. -/
theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-- The byte instructions of `encPost`. -/
def encByte : List Instr :=
  [.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r9 .r9 .r10, .stb .r9 .r17 0]

/-- The byte instructions of `decPost`. -/
def decByte : List Instr :=
  [.lbz .r9 .r17 0, .lbz .r10 .r19 cOff, .logic .xor .r10 .r10 .r9, .stb .r10 .r17 0]

theorem encPost_eq : encPost = encByte ++ (shift ++ advance) := rfl

theorem decPost_eq : decPost = decByte ++ (shift ++ advance) := rfl

theorem zext_xor (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  ext i hi; simp

theorem low_zext (a : Byte) : (a.setWidth 64).setWidth 8 = a := by
  ext i hi; simp

theorem encByte_wp {s : State} {P T : Addr} {rest : List Instr} {Φ : State → Prop}
    (hp : s.gpr .r17 = P) (ht : s.gpr .r19 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .r9 = (s.mem P ^^^ s.mem T).setWidth 64 →
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem P ^^^ s.mem T) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (encByte ++ rest)) s Φ := by
  simp only [encByte, List.cons_append, List.nil_append]
  refine wp_lbz (a := P) (by decide) (by decide) (by rw [hp]; simp) rP fun s₁ u₁ => ?_
  refine wp_lbz (a := T) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact ht)
    (by rw [u₁.rd, u₁.wr]; exact rT) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r9 = (s.mem P ^^^ s.mem T).setWidth 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem, zext_xor]
  refine wp_stb (a := P) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hp]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wP) fun s₄ u₄ => ?_
  refine k s₄ (by rw [u₄.gpr, v₃]) (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₄.gpr, u₃.other _ h9, u₂.other _ h10, u₁.other _ h9]
  · rw [u₄.mem, v₃, low_zext, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem decByte_wp {s : State} {P T : Addr} {rest : List Instr} {Φ : State → Prop}
    (hp : s.gpr .r17 = P) (ht : s.gpr .r19 + BitVec.ofNat 64 2048 = T)
    (rP : InRegions (s.rd ++ s.wr) P 1) (rT : InRegions (s.rd ++ s.wr) T 1) (wP : InRegions s.wr P 1)
    (k : ∀ s', s'.gpr .r9 = (s.mem P).setWidth 64 →
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW P (s.mem T ^^^ s.mem P) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (decByte ++ rest)) s Φ := by
  simp only [decByte, List.cons_append, List.nil_append]
  refine wp_lbz (a := P) (by decide) (by decide) (by rw [hp]; simp) rP fun s₁ u₁ => ?_
  refine wp_lbz (a := T) (by decide) (by decide) (by rw [u₁.other _ (by decide)]; exact ht)
    (by rw [u₁.rd, u₁.wr]; exact rT) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  have v₃ : s₃.gpr .r10 = (s.mem T ^^^ s.mem P).setWidth 64 := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, zext_xor]
  refine wp_stb (a := P) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hp]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wP) fun s₄ u₄ => ?_
  refine k s₄ (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (fun r h9 h10 => ?_) ?_ ?_ ?_
  · rw [u₄.gpr, u₃.other _ h10, u₂.other _ h10, u₁.other _ h9]
  · rw [u₄.mem, v₃, low_zext, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- `extr`'s result: the 64 bits of `x : y` above bit 8. -/
theorem extr_eq (x y : BitVec 64) : (x ++ y).extractLsb' 8 64 = (y >>> 8) ||| (x <<< 56) := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, BitVec.getElem_or,
    BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft]
  by_cases h : 8 + i < 64
  · have h' : i < 56 := by omega_using [h]
    simp [h, h']
  · have h' : ¬ i < 56 := by omega_using [h]
    simp only [h, h', ↓reduceIte, decide_false, Bool.not_false, Bool.true_and]
    rw [BitVec.getLsbD_of_ge y (8 + i) (by omega_using [h]), Bool.false_or, BitVec.getLsbD_eq_getElem (by omega_using [hi])]
    congr 1; omega_using []

/-- The input block at `Q` shifted left by a byte, with the byte in `r9`
shifted in. -/
theorem shift_wp {s : State} {Q : Addr} {c : Byte} {rest : List Instr} {Φ : State → Prop}
    (hq : s.gpr .r16 = Q) (hc : s.gpr .r9 = c.setWidth 64)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8)
    (k : ∀ s', (∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = AesCfb8.shiftMemX s.mem Q c → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (shift ++ rest)) s Φ := by
  simp only [shift, List.cons_append, List.nil_append]
  refine wp_ld (a := Q) (by decide) (by decide) (by rw [hq]; simp) r0 fun s₁ u₁ => ?_
  refine wp_ld (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), hq])
    (by rw [u₁.rd, u₁.wr]; exact r8) fun s₂ u₂ => ?_
  refine wp_lsr (by decide) fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ => ?_
  refine wp_lsr (by decide) fun s₆ u₆ => wp_lsl (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => ?_
  have q₈ : s₈.gpr .r16 = Q := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hq]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have w₀ : s₈.gpr .r10 = (s.mem.readW (Q + BitVec.ofNat 64 8) 64 ++ s.mem.readW Q 64).extractLsb' 8 64 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other .r10 (by decide), u₃.gpr, u₃.other .r11 (by decide), u₂.gpr, u₂.other .r10 (by decide),
      u₁.gpr, u₁.mem, extr_eq]
  have w₁ : s₈.gpr .r11 = (c.setWidth 64 ++ s.mem.readW (Q + BitVec.ofNat 64 8) 64).extractLsb' 8 64 := by
    rw [u₈.gpr, u₇.gpr, u₇.other .r11 (by decide), u₆.gpr, u₆.other .r9 (by decide),
      u₅.other .r11 (by decide), u₅.other .r9 (by decide), u₄.other .r11 (by decide), u₄.other .r9 (by decide),
      u₃.other .r11 (by decide), u₃.other .r9 (by decide), u₂.gpr, u₂.other .r9 (by decide),
      u₁.other .r9 (by decide), u₁.mem, hc, extr_eq]
  refine wp_std (a := Q) (by decide) (by decide) (by rw [q₈]; simp)
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w0) fun s₉ u₉ => ?_
  refine wp_std (a := Q + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₉.gpr, q₈])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact w8) fun s₁₀ u₁₀ => ?_
  refine k s₁₀ (fun r h10 h11 h12 => ?_) ?_ ?_ ?_
  · rw [u₁₀.gpr, u₉.gpr, u₈.other _ h11, u₇.other _ h12, u₆.other _ h11, u₅.other _ h10,
      u₄.other _ h12, u₃.other _ h10, u₂.other _ h11, u₁.other _ h10]
  · rw [u₁₀.mem, u₉.gpr, u₉.mem, m₈, w₀, w₁]; rfl
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.AesCfb8.PPC64LE

end

end


/-!
# AES-CFB8 on PPC64LE: one byte

As on x86-64 (`Proof/AesCfb8/X86_64/Body.lean`): `encBody_ok` and
`decBody_ok`, one run of `body` takes the loop invariant (`Loop.lean`) from
`k` bytes to `k + 1` (`BodyOk`). The input block is copied to the scratch
buffer and enciphered there (`call_ok`), the data byte is replaced, and the
input block is shifted (`finish_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE VG.Impl.AesCfb8.PPC64LE
open VG.Proof.AesCbc (copyMem copyMem_frame copyMem_bytes aesWith_state set_prefix)
open VG.Proof.AesCbc.PPC64LE (wK W R Iv Dp N S schR ivR scrR iv0 vars in_rw Sv cIv0 cIv8 cSv0 cSv8 sv8
  copy_wp CallPre CallPost blk_call encryptBlocks_noFrames preserved_ne r4_ofNat ofNat_zero_add bytesAt_frame)
open VG.Spec.Aes (bytesAt)

theorem headD_bytesAt (m : Mem) (p : Addr) : (bytesAt m p 16).headD 0 = m p := by
  simp [bytesAt, List.range_succ_eq_map]

/-- A byte outside a frame is unchanged. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 1⟩ : Region).Disjoint r) : m' p = m p := by
  have := bytesAt_frame hf hd (by decide)
  simpa [bytesAt] using this

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [AesCfb8.writeW8_apply, BitVec.sub_self]; simp

theorem frame_write8 (m : Mem) (p : Addr) (v : Byte) : Frame [⟨p, 1⟩] m (m.writeW p v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem LInv.regs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {enc : Bool} {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

theorem UPre.cByt {k : Nat} (hk : k < N s₀) : (dataR s₀).Contains (byt s₀ k) 1 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, this])

theorem UPre.byt_iv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.byt_sv {k : Nat} (hk : k < N s₀) : (⟨byt s₀ k, 1⟩ : Region).Disjoint ⟨S s₀, 2064⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ :=
  hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨S s₀, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])

theorem UPre.sv_wrap : (Sv s₀).toNat + 16 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [Sv, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
    Nat.mod_eq_of_lt (by omega_using [this])]
  omega_using [this]

/-- The arguments of a call on the copy of the input block, with the
working space at the start of the scratch buffer. -/
theorem UPre.callPre {s : State}
    (r3 : s.gpr .r3 = W s₀) (r4 : s.gpr .r4 = s₀.gpr .r4) (r5 : s.gpr .r5 = Sv s₀)
    (r6 : s.gpr .r6 = BitVec.ofNat 64 1) (r7 : s.gpr .r7 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀) where
  r3 := r3
  r4 := by rw [r4, r4_ofNat]
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := hp.rounds
  wd := hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  ds := hp.sv_scr
  wrap := hp.sv_wrap
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Sv s₀) (S s₀) (R s₀)
  saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r
  mem : s₁.mem = copyMem s.mem (Sv s₀) (Iv s₀)
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem pre_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State} (h : LInv enc s₀ k s) :
    WP isa (.block pre) s (PreA s₀ s) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  unfold pre
  refine copy_wp (dst := .r19) (src := .r16) (d := cOff) (e := 0) (P := Sv s₀) (Q := Iv s₀)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h.r19]; rfl) (by rw [h.r19]; exact sv8 _)
    (by rw [h.r16, ofNat_zero_add]) (by rw [h.r16])
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) cSv0) (by rw [hW]; exact in_rw (by simp) cSv8)
    fun s₁ g₁ mem₁ rd₁ wr₁ => ?_
  unfold mov
  refine wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_li (by decide) fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  have keep (r : Reg) (hr : r ∈ preserved) : s₆.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, h9, -⟩ := preserved_ne hr
    rw [u₆.other _ h7, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, g₁ r h9]
  refine ⟨hp.callPre ?_ ?_ ?_ ?_ ?_ ?_ ?_, keep, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁ _ (by decide), h.r14]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁ _ (by decide), h.r15]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide), h.r19]; rfl
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide), h.r19]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]

/-- What the code before the call and the call leave, for either
direction. -/
structure AfterCall (enc : Bool) (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  frame : Frame [⟨S s₀, 2064⟩] s.mem s₂.mem
  out : s₂.mem (Sv s₀) = (ciph s₀ (inKk s₀ enc k)).headD 0

theorem call_ok {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} {s : State}
    (h : LInv enc s₀ k s) (post : List Instr) {Q : State → Prop}
    (hq : ∀ s₂, AfterCall enc s₀ k s s₂ → WP isa (.block post) s₂ Q) :
    WP isa (body post) s Q := by
  refine WP.seq (WP.mono (pre_wp hp h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct encryptBlocks_noFrames a.pre)
    fun s₃ c => hq s₃ ?_)
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copyMem_frame _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem :=
    (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine ⟨fun r hr => by rw [c.saved r hr, a.saved r hr], by rw [c.rd, a.rd], by rw [c.wr, a.wr],
    (f₁.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_), ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨S s₀, 2064⟩, by simp, svSub⟩
    · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
  · rw [← headD_bytesAt s₃.mem (Sv s₀), c.out, UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      copyMem_bytes _ hp.iv_sv.symm, h.iv]

/-- After the byte operation (`v` the new data byte, `c` the byte to shift
in, in `r9`), the shift and `advance` take the invariant to `k + 1`. -/
theorem finish_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s s₂ s₃ : State}
    (h : LInv enc s₀ k s) (a : AfterCall enc s₀ k s s₂) {v : Byte}
    (g₃ : ∀ r, r ≠ .r9 → r ≠ .r10 → s₃.gpr r = s₂.gpr r) (mem₃ : s₃.mem = s₂.mem.writeW (byt s₀ k) v)
    (rd₃ : s₃.rd = s₂.rd) (wr₃ : s₃.wr = s₂.wr)
    (hv : v = (bs s₀)[k]'(by rw [length_bs]; exact hk) ^^^ (ciph s₀ (inKk s₀ enc k)).headD 0)
    (hc : s₃.gpr .r9 = (if enc then v else (bs s₀)[k]'(by rw [length_bs]; exact hk)).setWidth 64) :
    WP isa (.block (shift ++ Impl.AesCfb8.PPC64LE.advance)) s₃ (LInv enc s₀ (k + 1)) := by
  have g₃' (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₃ r h9 h10, a.g r hr]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr₃, a.wr, h.wrs hp]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, a.rd, wr₃, a.wr, h.regs hp]
  refine shift_wp (Q := Iv s₀) (by rw [g₃' .r16 (by decide), h.r16]) hc
    (by rw [hR₃]; exact in_rw (by simp) cIv0) (by rw [hR₃]; exact in_rw (by simp) cIv8)
    (by rw [hW₃]; exact in_rw (by simp) cIv0) (by rw [hW₃]; exact in_rw (by simp) cIv8)
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
  refine advance_regs (s := s₄) hk
    (by rw [g₄ _ (by decide) (by decide) (by decide), g₃' .r17 (by decide), h.r17])
    (by rw [g₄ _ (by decide) (by decide) (by decide), g₃' .r18 (by decide), h.r18])
    fun s₅ r17₅ r18₅ keep₅ mem₅ rd₅ wr₅ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₅.gpr r = s.gpr r := by
    have h10 : r ≠ .r10 := by revert hr; cases r <;> decide
    have h11 : r ≠ .r11 := by revert hr; cases r <;> decide
    have h12 : r ≠ .r12 := by revert hr; cases r <;> decide
    rw [keep₅ r h17 h18, g₄ r h10 h11 h12, g₃' r hr]
  -- Memory.
  have fStep : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨S s₀, 2064⟩] s.mem s₅.mem := by
    rw [mem₅, mem₄, mem₃]
    refine (a.frame.sub fun r hr => ?_).trans
      (((frame_write8 _ _ _).sub fun r hr => ?_).trans ((AesCfb8.shiftMemX_frame _ _ _).sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have one (r : Region) (P : Addr) (n : Nat) (hd : (⟨P, n⟩ : Region).Disjoint r) :
      ∀ r' ∈ [r], (⟨P, n⟩ : Region).Disjoint r' := fun r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact hd
  have newByte : s₅.mem (byt s₀ k) = v := by
    rw [mem₅, mem₄, byte_frame (AesCfb8.shiftMemX_frame _ _ _) (one _ _ _ (hp.byt_iv hk)), mem₃,
      writeW8_self]
  have ivIn : bytesAt s₃.mem (Iv s₀) 16 = inKk s₀ enc k := by
    rw [mem₃, bytesAt_frame (frame_write8 _ _ _) (one _ _ _ (hp.byt_iv hk).symm) (by decide),
      bytesAt_frame a.frame (one _ _ _ (hp.iv_scr.sub_right (Region.sub_prefix (by decide)))) (by decide),
      h.iv]
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega_using [hk]
  have iv_ne : iv0 s₀ ≠ [] := by simp [iv0, bytesAt]
  refine ⟨?_, ?_, ?_, r17₅, r18₅, ?_, fun r hr hv' => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · rw [g r hr (fun e => hv' (by simp [e])) (fun e => hv' (by simp [e])), h.keep r hr hv']
  · rw [rd₅, rd₄, rd₃, a.rd, h.rd]
  · rw [wr₅, wr₄, wr₃, a.wr, h.wr]
  · exact h.frame.trans (fStep.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, fun _ h => h⟩)
  · rw [hp.bytes_step hk fStep, h.data, newByte, set_prefix _ _ _ hl (by rw [length_bs]; exact hk), hv]
    simp only [outK, take_succ_bs s₀ hk, cfb8_snoc enc _ iv_ne, inKk]
  · rw [mem₅, mem₄, AesCfb8.shiftMemX_bytes, ivIn]
    simp only [inKk, take_succ_bs s₀ hk, inK_snoc enc _ iv_ne, ← hv]

theorem encBody_ok : BodyOk true (body encPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h encPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (Sv s₀) 1 :=
    in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.byt_sv hk), h.byte hk]
  rw [encPost_eq]
  refine encByte_wp (P := byt s₀ k) (T := Sv s₀) (by rw [a.g .r17 (by decide), h.r17])
    (by rw [a.g .r19 (by decide), h.r19])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk)) fun s₃ r9₃ g₃ mem₃ rd₃ wr₃ => ?_
  exact finish_wp hp hk h a g₃ mem₃ rd₃ wr₃ (by rw [p₂, a.out]) (by rw [r9₃]; simp only [↓reduceIte, p₂, a.out])

theorem decBody_ok : BodyOk false (body decPost) := by
  intro s₀ hp k hk s h
  refine call_ok hp h decPost fun s₂ a => ?_
  have hR₂ : s₂.rd ++ s₂.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [a.rd, a.wr, h.regs hp]
  have hW₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [a.wr, h.wrs hp]
  have cSv₁ : InRegions [schR s₀, ivR s₀, dataR s₀, scrR s₀] (Sv s₀) 1 :=
    in_rw (r := scrR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide))
  have p₂ : s₂.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
    rw [byte_frame a.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.byt_sv hk), h.byte hk]
  rw [decPost_eq]
  refine decByte_wp (P := byt s₀ k) (T := Sv s₀) (by rw [a.g .r17 (by decide), h.r17])
    (by rw [a.g .r19 (by decide), h.r19])
    (by rw [hR₂]; exact in_rw (by simp) (hp.cByt hk)) (by rw [hR₂]; exact cSv₁)
    (by rw [hW₂]; exact in_rw (by simp) (hp.cByt hk)) fun s₃ r9₃ g₃ mem₃ rd₃ wr₃ => ?_
  exact finish_wp hp hk h a g₃ mem₃ rd₃ wr₃ (by rw [p₂, a.out, BitVec.xor_comm])
    (by rw [r9₃]; simp only [Bool.false_eq_true, ↓reduceIte, p₂])

end VG.Proof.AesCfb8.PPC64LE
