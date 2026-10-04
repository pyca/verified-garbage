import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# Short Weierstrass curves on x86 (32-bit): tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, from the top
one down, each giving eight bytes of the table (`bitsBody_ok`). `bitMask d`
makes the mask `ecx` of the byte `esi` of the table at `d` (`bitMask_ok`): all
ones for a 1, zero for a 0 (`bitMask_bool_ok`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-! ## Masks -/

/-- `ecx = -[edi + esi + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .esi = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ size) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .ecx = 0 - (s.mem (off base (d + t))).setWidth 32 ∧ Keeps [.eax, .ecx] s s' ∧ s'.mem = s.mem := by
  simp only [bitMask]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .ecx] s s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  have e₂ : s₂.gpr .eax = s₂.gpr .edi + BitVec.ofNat 32 t := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), ht, k₂.1 _ (by decide)]
  refine wp_load8 (hs₂.ea_reg e₂ (d := d) (by omega)) (hs₂.read (d := t + d) (n := 1) (by omega))
    fun s₃ u₃ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_subS rfl fun s₅ u₅ _ => WP.block_nil ⟨?_, ((k₂.widen u₃.keeps).widen u₄.keeps).widen u₅.keeps,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, Nat.add_comm t d]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 32 = (if c then BitVec.allOnes 32 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .esi = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ size) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .ecx = (if c then BitVec.allOnes 32 else 0) ∧ Keeps [.eax, .ecx] s s' ∧ s'.mem = s.mem :=
  WP.mono (bitMask_ok hs ht hd) fun _ ⟨e, k, m⟩ => ⟨by rw [e, hc, neg_bit], k, m⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .mov .eax (.reg .edi), .alu .add .eax (.reg .esi), .movzx8 .eax (at_ .eax src),
    .mov .ebx (.reg .esi), .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .ebx),
    .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .edi)] ++
  (List.range 8).flatMap (bitJ dst) ++ [testCounter]

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 nbytes))])
      (.loop (.block (bitsBody src dst)) .ne) :=
  rfl

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((((b.setWidth 32 >>> j) &&& 1).setWidth 8) : BitVec 8) = if b.getLsbD j then 1 else 0 := by
  decide +kernel

theorem bit_byte0 : ∀ b : BitVec 8,
    (((b.setWidth 32 &&& 1).setWidth 8) : BitVec 8) = if b.getLsbD 0 then 1 else 0 := by
  decide +kernel

/-- Byte `j` of the eight at `ebx + dst`: bit `j` of the byte in `eax`. -/
theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (hb : s.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 (8 * i)) {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32)
    {dst j : Nat} (hj : j < 8) (hd : dst + (8 * i + j) + 1 ≤ size) :
    WP isa (.block (bitJ dst j)) s fun s' => Keeps [.edx] s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have e : 8 * i + (dst + j) = dst + (8 * i + j) := by omega
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.nil_append, List.cons_append]
    refine wp_movS rfl fun s₁ u₁ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
    have k₂ : Keeps [.edx] s s₂ := u₁.keeps.widen u₂.keeps
    have hs₂ := hs.of_keeps k₂ (by decide)
    have hb₂ : s₂.gpr .ebx = s₂.gpr .edi + BitVec.ofNat 32 (8 * i) := by
      rw [k₂.1 _ (by decide), k₂.1 _ (by decide), hb]
    refine wp_store8 (r := .dl) (hs₂.ea_reg hb₂ (d := dst + 0) (by omega))
      (hs₂.write (d := 8 * i + (dst + 0)) (n := 1) (by omega)) fun s₃ m₃ => WP.block_nil
      ⟨k₂.trans (m₃.keeps _), ?_⟩
    rw [m₃.mem, e, u₂.mem, u₁.mem]
    congr 1
    show (s₂.gpr .edx).setWidth 8 = _
    rw [u₂.gpr, u₁.gpr, ha]
    exact bit_byte0 b
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.cons_append, List.nil_append]
    refine wp_movS rfl fun s₁ u₁ _ => ?_
    refine wp_shr (by omega) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    have k₃ : Keeps [.edx] s s₃ := (u₁.keeps.widen u₂.keeps).widen u₃.keeps
    have hs₃ := hs.of_keeps k₃ (by decide)
    have hb₃ : s₃.gpr .ebx = s₃.gpr .edi + BitVec.ofNat 32 (8 * i) := by
      rw [k₃.1 _ (by decide), k₃.1 _ (by decide), hb]
    refine wp_store8 (r := .dl) (hs₃.ea_reg hb₃ (d := dst + j) (by omega))
      (hs₃.write (d := 8 * i + (dst + j)) (n := 1) (by omega)) fun s₄ m₄ => WP.block_nil
      ⟨k₃.trans (m₄.keeps _), ?_⟩
    rw [m₄.mem, e, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    show (s₃.gpr .edx).setWidth 8 = _
    rw [u₃.gpr, u₂.gpr, u₁.gpr, ha]
    exact bit_byte b j hj

/-- The first `k` bits of the byte in `eax`. -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (hb : s.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 (8 * i)) {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32)
    {dst : Nat} (hd : dst + 8 * i + 8 ≤ size) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => Keeps [.edx] s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨Keeps.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitJs_ok hs hb ha hd k (by omega)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_)
    refine WP.mono (bitJ_ok (hs.of_keeps k₁ (by decide)) (i := i)
      (by rw [k₁.1 _ (by decide), k₁.1 _ (by decide), hb]) (b := b) (by rw [k₁.1 _ (by decide), ha])
      (dst := dst) (j := k) (by omega) (by omega)) fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega)]; omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, writeW8_self]

/-- `ebx = edi + 8 esi`. -/
theorem rowAddr (e x : BitVec 32) (i : Nat) (hx : x = BitVec.ofNat 32 i) :
    x + x + (x + x) + (x + x + (x + x)) + e = e + BitVec.ofNat 32 (8 * i) := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- One byte of the number at `src`, the one below `esi = i + 1`: its bits to
the table at `dst`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src dst i : Nat}
    (ht : s.gpr .esi = BitVec.ofNat 32 (i + 1)) (hi : i + 1 < 2 ^ 32)
    (hsrc : src + i + 1 ≤ size) (hd : dst + 8 * i + 8 ≤ size) :
    WP isa (.block (bitsBody src dst)) s fun s' =>
      s'.gpr .esi = BitVec.ofNat 32 i ∧ s'.zf = some (decide (i = 0)) ∧
      Keeps [.eax, .ebx, .edx, .esi] s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  simp only [bitsBody, List.cons_append, List.append_assoc]
  refine wp_decCounter (j := i + 1) (by omega) ht fun s₁ c₁ k₁ m₁ => ?_
  rw [Nat.add_sub_cancel] at c₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  have k₃ : Keeps [.eax, .ebx, .edx, .esi] s s₃ := ((k₁.mono (by decide)).widen u₂.keeps).widen u₃.keeps
  have hs₃ := hs.of_keeps k₃ (by decide)
  have e₃ : s₃.gpr .eax = s₃.gpr .edi + BitVec.ofNat 32 i := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), c₁, k₃.1 _ (by decide), k₁.1 _ (by decide)]
  refine wp_load8 (hs₃.ea_reg e₃ (d := src) (by omega)) (hs₃.read (d := i + src) (n := 1) (by omega))
    fun s₄ u₄ => ?_
  refine wp_movS rfl fun s₅ u₅ _ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  refine wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => ?_
  refine wp_addS rfl fun s₉ u₉ _ => ?_
  have k₉ : Keeps [.eax, .ebx, .edx, .esi] s s₉ :=
    ((((((k₃.widen u₄.keeps).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps)).widen u₉.keeps
  have hs₉ := hs.of_keeps k₉ (by decide)
  have esi₉ : s₉.gpr .esi = BitVec.ofNat 32 i := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), c₁]
  have ebx₉ : s₉.gpr .ebx = s₉.gpr .edi + BitVec.ofNat 32 (8 * i) := by
    have hedi : s₉.gpr .edi = s₈.gpr .edi := u₉.other _ (by decide)
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, hedi, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide)]
    exact rowAddr _ _ i (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), c₁])
  have mem₉ : s₉.mem = s.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have eax₉ : s₉.gpr .eax = (s.mem (off base (src + i))).setWidth 32 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, m₁, Nat.add_comm i src]
  rw [List.nil_append]
  refine WP.block_append (WP.mono (bitJs_ok hs₉ ebx₉ eax₉ (dst := dst) (by omega) 8 (Nat.le_refl _))
    fun s₁₀ ⟨k₁₀, e₁₀, O₁₀⟩ => ?_)
  have esi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 i := by rw [k₁₀.1 _ (by decide), esi₉]
  refine wp_testCounter (by omega) esi₁₀ fun s₁₁ f₁₁ z₁₁ => WP.block_nil
    ⟨by rw [f₁₁.gpr, esi₁₀], z₁₁, (k₉.widen k₁₀).trans (f₁₁.keeps _), ?_, ?_⟩
  · rw [f₁₁.mem]; exact e₁₀
  · rw [f₁₁.mem, ← mem₉]; exact O₁₀

/-- `bits`' loop invariant, at `esi = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base size
  esi : s.gpr .esi = BitVec.ofNat 32 i
  keep : Keeps [.eax, .ebx, .edx, .esi] s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst : Nat}
    (hn0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      Keeps [.eax, .ebx, .edx, .esi] s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [bits_eq]
  have h0 : WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 (8 * n)))]) s fun s' =>
      BInv base size src dst n s s' (8 * n) :=
    wp_movS rfl fun s₁ u₁ _ => WP.block_nil ⟨hs.of_keeps (u₁.keeps.mono (rs' := [.eax, .ebx, .edx, .esi])
      (by decide)) (by decide), u₁.gpr, u₁.keeps.mono (by decide),
      by rw [u₁.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _, fun t ht ht' => absurd ht' (by omega)⟩
  refine WP.seq (WP.mono h0 fun s₁ h₁ => ?_)
  refine countLoop_ok (Inv := fun j s' => BInv base size src dst n s s' j) (n := 8 * n)
    (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩) (by omega) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine WP.mono (bitsBody_ok hb.scr hb.esi (by omega) (by omega) (by omega))
      fun s'' ⟨b', z', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega)]; omega)
    refine ⟨⟨hb.scr.of_keeps k' (by decide), b', hb.keep.trans k',
      hb.mem.trans (O'.mono (by omega) (by omega)), fun t ht ht' => ?_⟩, by rw [z']; rfl⟩
    rcases Nat.lt_or_ge t (8 * (i + 1)) with h | h
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega)]; omega), hb.bits t h ht']
  · rw [hb.bits t (by omega) ht, show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
      VG.Proof.Weierstrass.testBit_byte s.mem base (a := src) (n := n) (by omega) (Nat.mod_lt _ (by decide))]
    simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega]

end VG.Proof.Weierstrass.X86
