module

public import VerifiedGarbage.Proof.Seed.X86.AesNiMaps
public import VerifiedGarbage.Proof.Seed.Rounds
public import VerifiedGarbage.Spec.Seed.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.ModeBytes

/-!
# SEED by the AES S-box on x86 (32-bit): the core of the modes

`coreSpec`: `Impl.Seed.X86.AesNi.core` meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through the
first stack argument, and its cipher `Spec.Seed.cipher`.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Seed.X86.AesNi
open VG.Proof.Seed (byteOf maskOf sOf getLsbD_byteOf)
open VG.Spec.Seed (Word)
open VG.Proof.Modes.X86 (ScrIn)

/-! ## The byte maps -/

theorem byte_ofNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `sbox_all`, of a byte. -/
theorem sbox_ok (b : Byte) : am oP0 (aesSbox (pre b)) = sOf 0 b ∧ am oP1 (aesSbox (pre b)) = sOf 1 b := by
  have h := List.all_eq_true.mp sbox_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.trans (Proof.Seed.sTable_getD false _).symm, h.2.trans (Proof.Seed.sTable_getD true _).symm⟩

/-- `ka_all`, of a position. -/
theorem ka_ok {p : Nat} (hp : p < 16) :
    ka oKA p = (if (p / 4 + p % 4) % 2 = 0 then maskOf ((2 * (p % 4) + p / 4) % 4) else 0#8) ∧
    ka (oKA + 16) p = (if (p / 4 + p % 4) % 2 = 1 then maskOf ((2 * (p % 4) + p / 4) % 4) else 0#8) := by
  have h := List.all_eq_true.mp ka_all p (List.mem_range.mpr hp)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h

/-! ## Words in registers -/

/-- A register's bytes give it. -/
theorem bv128_ext {a b : BitVec 128} (h : ∀ q < 16, byte a q = byte b q) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have e := congrArg (fun v : BitVec 8 => v.getLsbD (j % 8)) (h (j / 8) (by omega_using [hj]))
  simp only [byte, BitVec.getLsbD_extractLsb'] at e
  rw [decide_eq_true (Nat.mod_lt _ (by decide)), Bool.true_and, Bool.true_and,
    show 8 * (j / 8) + j % 8 = j by omega_arith] at e
  exact e

theorem byteOf_eq (X : Word) (k : Nat) : byteOf X k = X.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [getLsbD_byteOf _ ht, BitVec.getLsbD_extractLsb', decide_eq_true ht, Bool.true_and]

theorem byteOf_xor (a b : Word) (k : Nat) : byteOf (a ^^^ b) k = byteOf a k ^^^ byteOf b k := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [BitVec.getLsbD_xor, getLsbD_byteOf _ ht]

/-- A word's bytes give it. -/
theorem word_ext {a b : Word} (h : ∀ k < 4, byteOf a k = byteOf b k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have e := congrArg (fun v : Byte => v.getLsbD (j % 8)) (h (j / 8) (by omega_using [hj]))
  simp only [getLsbD_byteOf _ (Nat.mod_lt j (show 0 < 8 by decide))] at e
  rwa [show 8 * (j / 8) + j % 8 = j by omega_arith] at e

/-- The register `v` holds the word `X` in each of its four lanes. -/
def Hw (v : BitVec 128) (X : Word) : Prop := ∀ q < 16, byte v q = byteOf X (q % 4)

theorem Hw.dw {v : BitVec 128} {X : Word} (h : Hw v X) {c : Nat} (hc : c < 4) : X86.dword v c = X :=
  word_ext fun k hk => by
    have e := h (4 * c + k) (by omega_using [hc, hk])
    rw [byte_eq_dword, show (4 * c + k) / 4 = c by omega_arith, show (4 * c + k) % 4 = k by omega_arith] at e
    rw [byteOf_eq, e]

theorem Hw.of_dw {v : BitVec 128} {X : Word} (h : ∀ c < 4, X86.dword v c = X) : Hw v X := fun q hq => by
  rw [byte_eq_dword, h _ (by omega_arith), byteOf_eq]

theorem Hw.paddd {a b : BitVec 128} {X Y : Word} (ha : Hw a X) (hb : Hw b Y) :
    Hw (XBinOp.eval .paddd a b) (X + Y) :=
  Hw.of_dw fun c hc => by rw [dword_paddd _ _ hc, ha.dw hc, hb.dw hc]

theorem Hw.pxor {a b : BitVec 128} {X Y : Word} (ha : Hw a X) (hb : Hw b Y) : Hw (a ^^^ b) (X ^^^ Y) :=
  fun q hq => by rw [byte_xor, ha q hq, hb q hq, byteOf_xor]

/-! ## G -/

/-- §2.2: a byte of `G(X)`, of the S-boxes of the four bytes of `X`. -/
theorem byteOf_g (X : Word) {i : Nat} (hi : i < 4) :
    byteOf (Spec.Seed.g X) i =
      (sOf 0 (byteOf X 0) &&& maskOf ((0 + i) % 4)) ^^^ (sOf 1 (byteOf X 1) &&& maskOf ((1 + i) % 4)) ^^^
        (sOf 2 (byteOf X 2) &&& maskOf ((2 + i) % 4)) ^^^ (sOf 3 (byteOf X 3) &&& maskOf ((3 + i) % 4)) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [getLsbD_byteOf _ ht, Proof.Seed.getLsbD_g X hi ht]
  simp only [Proof.Seed.xor4, BitVec.getLsbD_xor, BitVec.getLsbD_and]

/-- Lane `c`'s byte for G's output byte `i`, of `aesenclast`'s input bytes
`w`: both maps after the S-box, each under its mask of the position. -/
def lane (w : Nat → Byte) (c i : Nat) : Byte :=
  (am oP0 (aesSbox (w (srow (4 * c + i)))) &&& ka oKA (4 * c + i)) ^^^
    (am oP1 (aesSbox (w (srow (4 * c + i)))) &&& ka (oKA + 16) (4 * c + i))

/-- G's output byte `q`: the four lanes. -/
def gsum (w : Nat → Byte) (q : Nat) : Byte :=
  lane w 0 (q % 4) ^^^ lane w 1 (q % 4) ^^^ lane w 2 (q % 4) ^^^ lane w 3 (q % 4)

theorem srow_lt (p : Nat) : srow p < 16 := by unfold srow; omega_arith

theorem srow_div {c i : Nat} (hi : i < 4) : srow (4 * c + i) / 4 = (i + c) % 4 := by
  have e₁ : (4 * c + i) % 4 = i := by omega_arith
  have e₂ : (4 * c + i) / 4 = c := by omega_arith
  have hk := Nat.mod_lt (c + i) (show 0 < 4 by decide)
  unfold srow
  rw [e₁, e₂, Nat.add_comm i c]
  generalize (c + i) % 4 = k at hk ⊢
  omega_using [hi, hk]

/-- A lane's byte, when `aesenclast`'s input is the map before the S-box of
the bytes of `X`, byte `l` in lane `l`: of the S-box of one byte of `X`,
under the mask of that byte for the output byte. -/
theorem lane_ok (X : Word) {w : Nat → Byte} (hw : ∀ p < 16, w p = pre (byteOf X (p / 4))) {c i : Nat}
    (hc : c < 4) (hi : i < 4) :
    lane w c i = sOf ((i + c) % 4) (byteOf X ((i + c) % 4)) &&& maskOf (((i + c) % 4 + i) % 4) := by
  have e₁ : (4 * c + i) % 4 = i := by omega_arith
  have e₂ : (4 * c + i) / 4 = c := by omega_arith
  have hk := ka_ok (p := 4 * c + i) (by omega_arith)
  rw [e₁, e₂] at hk
  rw [lane, hw _ (srow_lt _), srow_div hi, (sbox_ok _).1, (sbox_ok _).2, hk.1, hk.2]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega_using [hc]) with rfl | rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, BitVec.and_zero,
    BitVec.xor_zero, BitVec.zero_xor] <;> rfl

/-- The four lanes are `G`'s byte. -/
theorem gsum_ok (X : Word) {w : Nat → Byte} (hw : ∀ p < 16, w p = pre (byteOf X (p / 4))) (q : Nat) :
    gsum w q = byteOf (Spec.Seed.g X) (q % 4) := by
  have hi : q % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [gsum, lane_ok X hw (by decide) hi, lane_ok X hw (by decide) hi, lane_ok X hw (by decide) hi,
    lane_ok X hw (by decide) hi, byteOf_g X hi]
  generalize q % 4 = i at hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceAdd, Nat.reduceMod] <;> ac_rfl

/-! ## What the parts of the block's code compute -/

/-- Byte `o` of the scratch buffer at `edi`. -/
def kb (s : State) (o : Nat) : Byte := s.mem ((s.gpr Impl.Modes.X86.sb).setWidth 64 + BitVec.ofNat 64 o)

/-- What a round needs of the state: the table's address in its register,
the scratch buffer's first 96 bytes, which end with the four places of the
state's halves, readable, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 96 → InRegions (s.rd ++ s.wr) (addr (s.gpr Impl.Modes.X86.sb) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

section
variable {s s' : State} {ρ : Regs}

theorem Env.rel (h : Env s) : Rel params (envOf params s) regs₀ s :=
  (rel_init (p := params) h.tb h.fit h.acc).const m0 h.msk

theorem Env.same (h : Env s) (hs : Same s s') (hm : ∀ i < 16, byte (s'.xmm m0) i = 0x0f#8) : Env s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨h.tb, h.fit, h.acc, hm⟩

theorem env_var (p : Params) (r : XReg) {q : Nat} (hq : q < 16) :
    mask (envOf p s) (var r q) nvars = byte (s.xmm r) q := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [var, mask_bit _ (by show 16 * r.ctorIdx + q < 1024; omega_using [hr, hq]), envOf_reg p s r hq]

theorem env_key (p : Params) {o : Nat} (ho : o < 96) :
    mask (envOf p s) (kv o) nvars = s.mem ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 o) := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_using [ho]), envOf_key]

theorem keeps_ok {p : Params} (hr : Rel p (envOf p s) ρ s') {r : XReg} (h : keeps ρ r = true) :
    s'.xmm r = s.xmm r := bv128_ext fun q hq => by
  simp only [keeps, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hr.bytes h.1 q hq, BV.same_eval _ (List.all_eq_true.mp h.2 q (List.mem_range.mpr hq))]
  simp only [BV.eval, sum, BitVec.xor_zero, env_var p r hq]

theorem mask_ok {p : Params} (hr : Rel p (envOf p s) ρ s') (h : maskOk ρ = true) :
    ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := fun q hq => by
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hr.bytes h.1 q hq, BV.same_eval _ (List.all_eq_true.mp h.2 q (List.mem_range.mpr hq)), BV.cst_eval]

/-- The two look-ups of the map before the S-box are the map. -/
theorem cterms_sum (env : Nat → BitVec 8) (v : Nat) : sum env (cterms v) = pre (mask env v nvars) := by
  simp only [cterms, sum, BitVec.xor_zero]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (c : Byte) (p : Nat) :
    sum env (aT t c p) = am t (aesSbox (mask env (var .xmm2 (srow p)) nvars)) &&& c := by
  simp only [aT, sum, BitVec.xor_zero]
  exact (Fn.lin_xor (g := .and c) rfl _ _).symm

theorem gT_sum (q : Nat) :
    sum (envOf params s) (gT q) = gsum (fun p => byte (s.xmm .xmm2) p) q := by
  simp only [gT, laneT, sum_append, aT_sum, gsum, lane, env_var params .xmm2 (srow_lt _)]

/-- `G`: the word in `xmm0` (its first lane) to `G` of it, in every lane;
`xmm5` and `xmm6` are kept. -/
theorem g_wp (he : Env s) {X : Word} (hx : ∀ k < 4, byte (s.xmm .xmm0) k = byteOf X k) :
    WP isa (.block g) s fun s' =>
      Same s s' ∧ Hw (s'.xmm .xmm0) (Spec.Seed.g X) ∧ s'.xmm .xmm5 = s.xmm .xmm5 ∧ s'.xmm .xmm6 = s.xmm .xmm6 ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hpre := g_all.1
  unfold gPreOk at hpre
  split at hpre <;> [cases hpre; rename_i ρ₁ hrun₁]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpre
  obtain ⟨⟨⟨⟨p2, c2⟩, k5⟩, k6⟩, km⟩ := hpre
  have hpost := g_all.2
  unfold gPostOk at hpost
  split at hpost <;> [cases hpost; rename_i ρ₂ hrun₂]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpost
  obtain ⟨⟨⟨⟨p0, c0⟩, l5⟩, l6⟩, lm⟩ := hpost
  refine WP.block_append_iff.mpr (run_wp he.rel hrun₁ fun s₁ hr₁ same₁ => ?_)
  have m₁ := mask_ok hr₁ km
  have he₁ := he.same same₁ m₁
  have w₁ : ∀ p < 16, byte (s₁.xmm .xmm2) p = pre (byteOf X (p / 4)) := fun p hp => by
    rw [hr₁.bytes p2 p hp, BV.same_eval _ (List.all_eq_true.mp c2 p (List.mem_range.mpr hp)), BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_var params .xmm0 (by omega_arith), hx _ (by omega_arith)]
  refine run_wp he₁.rel hrun₂ fun s₂ hr₂ same₂ => ?_
  refine ⟨same₁.trans same₂, fun q hq => ?_, (keeps_ok hr₂ l5).trans (keeps_ok hr₁ k5),
    (keeps_ok hr₂ l6).trans (keeps_ok hr₁ k6), mask_ok hr₂ lm⟩
  rw [hr₂.bytes p0 q hq, BV.same_eval _ (List.all_eq_true.mp c0 q (List.mem_range.mpr hq)), BV.eval, mask_zero,
    gT_sum, BitVec.zero_xor, BitVec.xor_zero]
  exact gsum_ok X w₁ q

end

/-! ## Single instructions -/

section
variable {is : List Instr} {Q : State → Prop} {s s' : State}

theorem same_mem (h : Same s s') : s'.mem = s.mem := by obtain ⟨f, rfl⟩ := h; rfl
theorem same_gpr (h : Same s s') : s'.gpr = s.gpr := by obtain ⟨f, rfl⟩ := h; rfl
theorem same_zf (h : Same s s') : s'.zf = s.zf := by obtain ⟨f, rfl⟩ := h; rfl
theorem same_rd (h : Same s s') : s'.rd = s.rd := by obtain ⟨f, rfl⟩ := h; rfl
theorem same_wr (h : Same s s') : s'.wr = s.wr := by obtain ⟨f, rfl⟩ := h; rfl
theorem same_syms (h : Same s s') : s'.syms = s.syms := by obtain ⟨f, rfl⟩ := h; rfl

/-- `sub d, v`, with the flags and the XMM registers. -/
theorem wp_subi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → s'.zf = some (s.gpr d - v == 0) →
      WP isa (.block is) s' Q) : WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl rfl)

theorem wp_addi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

/-- `movdqu d, [b + o]`, of readable bytes. -/
theorem wp_ldx {d : XReg} {b : Reg} {o : Nat} (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 16)
    (k : WP isa (.block is) (s.setXmm d (s.mem.readW (addr (s.gpr b) o) 128)) Q) :
    WP isa (.block (.movdquLoad d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setXmm d (s.mem.readW (addr (s.gpr b) o) 128)) ?_ k
  show (s.load128 (addr (s.gpr b) o)).map _ = _
  rw [State.load128, ite_eq_left hin]; rfl

/-- `movdqu [b + o], r`, to writable bytes. -/
theorem wp_stx {b : Reg} {o : Nat} {r : XReg} (hin : InRegions s.wr (addr (s.gpr b) o) 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) } Q) :
    WP isa (.block (.movdquStore ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) }) ?_ k
  show State.store128 s (addr (s.gpr b) o) _ = _
  rw [State.store128, ite_eq_left hin]

/-- An instruction of two XMM registers: only its first changes. -/
theorem wp_xb {op : XBinOp} {a b : XReg}
    (k : ∀ s', Same s s' → s'.xmm a = XBinOp.eval op (s.xmm a) (s.xmm b) → (∀ r, ¬r = a → s'.xmm r = s.xmm r) →
      WP isa (.block is) s' Q) : WP isa (.block (.xop (.bin op a b) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨_, rfl⟩ (RegUpd.xmm_setXmm_self s a _) fun _ hr => RegUpd.xmm_setXmm_of_ne s _ hr)

end

/-! ## F -/

section
variable {s : State}

/-- F (§2.1) of `A` in `xmm5` and `B` in `xmm0`: `C = G(A ⊕ B)`,
`D = G(C + A)`, `E = G(D + C)`; `E + D` to `xmm5` and `E` to `xmm0`. -/
theorem fX_wp (he : Env s) {A Bw : Word} (ha : Hw (s.xmm .xmm5) A) (hb : Hw (s.xmm .xmm0) Bw) :
    WP isa (.block fX) s fun s' => Same s s' ∧
      Hw (s'.xmm .xmm5) (Spec.Seed.g (Spec.Seed.g (Spec.Seed.g (A ^^^ Bw) + A) + Spec.Seed.g (A ^^^ Bw)) +
        Spec.Seed.g (Spec.Seed.g (A ^^^ Bw) + A)) ∧
      Hw (s'.xmm .xmm0) (Spec.Seed.g (Spec.Seed.g (Spec.Seed.g (A ^^^ Bw) + A) + Spec.Seed.g (A ^^^ Bw))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  obtain ⟨c, hc⟩ : ∃ c, c = Spec.Seed.g (A ^^^ Bw) := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨d, hd⟩ : ∃ d, d = Spec.Seed.g (c + A) := ⟨_, rfl⟩
  rw [← hd]
  obtain ⟨e, he'⟩ : ∃ e, e = Spec.Seed.g (d + c) := ⟨_, rfl⟩
  rw [← he']
  show WP isa (.block (x .pxor .xmm0 .xmm5 :: (g ++ (x .movdqa .xmm6 .xmm0 :: x .paddd .xmm0 .xmm5 :: (g ++
    (x .movdqa .xmm5 .xmm0 :: x .paddd .xmm0 .xmm6 :: (g ++ [x .paddd .xmm5 .xmm0]))))))) s _
  -- `A ⊕ B`
  refine wp_xb fun s₁ sm₁ v₁ o₁ => ?_
  have h0₁ : Hw (s₁.xmm .xmm0) (A ^^^ Bw) := by rw [v₁, BitVec.xor_comm A Bw]; exact hb.pxor ha
  have h5₁ : s₁.xmm .xmm5 = s.xmm .xmm5 := o₁ _ (by decide)
  have m₁ : ∀ q < 16, byte (s₁.xmm m0) q = 0x0f#8 := by rw [o₁ m0 (by decide)]; exact he.msk
  refine WP.block_append_iff.mpr (WP.mono (g_wp (X := A ^^^ Bw) (he.same sm₁ m₁) fun k hk => by
    rw [h0₁ k (by omega_arith), Nat.mod_eq_of_lt hk]) fun s₂ ⟨sm₂, g₂, k5₂, _, m₂⟩ => ?_)
  rw [← hc] at g₂
  -- `C`, and `C + A`
  refine wp_xb fun s₃ sm₃ v₃ o₃ => wp_xb fun s₄ sm₄ v₄ o₄ => ?_
  have h6₄ : Hw (s₄.xmm .xmm6) c := by rw [o₄ _ (by decide), v₃]; exact g₂
  have h0₄ : Hw (s₄.xmm .xmm0) (c + A) := by
    rw [v₄, o₃ .xmm0 (by decide), o₃ .xmm5 (by decide), k5₂, h5₁]; exact g₂.paddd ha
  have m₄ : ∀ q < 16, byte (s₄.xmm m0) q = 0x0f#8 := by rw [o₄ m0 (by decide), o₃ m0 (by decide)]; exact m₂
  have sm : Same s s₄ := ((sm₁.trans sm₂).trans sm₃).trans sm₄
  refine WP.block_append_iff.mpr (WP.mono (g_wp (X := c + A) (he.same sm m₄) fun k hk => by
    rw [h0₄ k (by omega_arith), Nat.mod_eq_of_lt hk]) fun s₅ ⟨sm₅, g₅, _, k6₅, m₅⟩ => ?_)
  rw [← hd] at g₅
  -- `D`, and `D + C`
  refine wp_xb fun s₆ sm₆ v₆ o₆ => wp_xb fun s₇ sm₇ v₇ o₇ => ?_
  have h5₇ : Hw (s₇.xmm .xmm5) d := by rw [o₇ _ (by decide), v₆]; exact g₅
  have h0₇ : Hw (s₇.xmm .xmm0) (d + c) := by
    rw [v₇, o₆ .xmm0 (by decide), o₆ .xmm6 (by decide), k6₅]; exact g₅.paddd h6₄
  have m₇ : ∀ q < 16, byte (s₇.xmm m0) q = 0x0f#8 := by rw [o₇ m0 (by decide), o₆ m0 (by decide)]; exact m₅
  have sm' : Same s s₇ := ((sm.trans sm₅).trans sm₆).trans sm₇
  refine WP.block_append_iff.mpr (WP.mono (g_wp (X := d + c) (he.same sm' m₇) fun k hk => by
    rw [h0₇ k (by omega_arith), Nat.mod_eq_of_lt hk]) fun s₈ ⟨sm₈, g₈, k5₈, _, m₈⟩ => ?_)
  rw [← he'] at g₈
  -- `E`, and `E + D`
  refine wp_xb fun s₉ sm₉ v₉ o₉ => WP.block_nil ?_
  refine ⟨(sm'.trans sm₈).trans sm₉, ?_, by rw [o₉ _ (by decide)]; exact g₈,
    by rw [o₉ m0 (by decide)]; exact m₈⟩
  rw [v₉, k5₈, BitVec.add_comm e d]
  exact h5₇.paddd g₈

end

/-! ## The state's halves and the round keys in the scratch buffer -/

/-- Byte `o` of the scratch buffer at `B`. -/
def sAt (m : Mem) (B : BitVec 32) (o : Nat) : Byte := m (B.setWidth 64 + BitVec.ofNat 64 o)

/-- The place of round key `i` holds `k`, and the place `j` of the state's
halves the word `X`, in every lane. -/
def KeyAt (m : Mem) (B : BitVec 32) (i : Nat) (k : Word) : Prop :=
  ∀ q < 16, sAt m B (96 + 16 * i + q) = byteOf k (q % 4)
def WordAt (m : Mem) (B : BitVec 32) (j : Nat) (X : Word) : Prop :=
  ∀ q < 16, sAt m B (32 + 16 * j + q) = byteOf X (q % 4)

/-- A byte of the scratch buffer outside the bytes `[lo, lo + n)` that were written. -/
theorem frame_sAt {m m' : Mem} {B : BitVec 32} {lo n o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 lo, n⟩] m m') (ho : o < lo ∨ lo + n ≤ o)
    (hb : o < 2 ^ 32) (hl : lo + n ≤ 2 ^ 32) : sAt m' B o = sAt m B o := by
  have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 o, 1⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [hb]) (by omega_using [hl]))
    (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
  rw [BitVec.add_zero] at this
  exact this

theorem KeyAt.frame {m m' : Mem} {B : BitVec 32} {i lo n : Nat} {k : Word} (h : KeyAt m B i k)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 lo, n⟩] m m') (hi : i < 32) (hl : lo + n ≤ 96) :
    KeyAt m' B i k := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hl]) (by omega_using [hi, hq]) (by omega_using [hl])]; exact h q hq

theorem WordAt.frame {m m' : Mem} {B : BitVec 32} {j lo n : Nat} {X : Word} (h : WordAt m B j X)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 lo, n⟩] m m') (hj : j < 4)
    (hne : 32 + 16 * j + 16 ≤ lo ∨ lo + n ≤ 32 + 16 * j) (hl : lo + n ≤ 96) : WordAt m' B j X := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hne]) (by omega_using [hj, hq]) (by omega_using [hl])]; exact h q hq

/-- A state of `crypt` after `n` turns, from the state `s₀` it starts in:
the scratch buffer's address, the round keys' pointer, and the table's
address. -/
structure At (s₀ : State) (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * n)

section
variable {s₀ s : State} {B : BitVec 32} {n : Nat}

theorem At.of_gpr {s' : State} (h : At s₀ B n s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : At s₀ B n s' :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esp, hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms,
    by rw [hg]; exact h.tb, by rw [hg]; exact h.kp⟩

theorem At.same {s' : State} (h : At s₀ B n s) (hs : Same s s') : At s₀ B n s' :=
  h.of_gpr (same_gpr hs) (same_rd hs) (same_wr hs) (same_syms hs)

theorem At.kr64 (h : At s₀ B n s) (hf : B.toNat + 648 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * n) := by
  rw [h.kp]; exact addr_eq (by omega_using [hf, hn])

theorem At.krNat (h : At s₀ B n s) (hf : B.toNat + 648 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * n) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * n) (by omega_using [hn]),
    Nat.mod_eq_of_lt (by omega_using [hf, hn])]

theorem At.scr (h : At s₀ B n s) (o : Nat) : kb s o = sAt s.mem B o := by
  rw [kb, h.base]; rfl

theorem At.env (h : At s₀ B n s) (hs : ScrIn s₀ B 162) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) : Env s := by
  have hf : B.toNat + 648 ≤ 2 ^ 32 := hs.fit
  refine ⟨by rw [h.tb, h.syms], by rw [h.base]; omega_using [hf],
    fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.base, addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- Round `h` of turn `n`, round `2 n + h` of the block: from the right
half in `xmm5` and `xmm0`, the left half in the places `2 h` and `2 h + 1`
and the round's keys, to the next round's right half in the registers and
its left half in the places `2 - 2 h` and `3 - 2 h`. -/
theorem round_ok {h : Nat} (hh : h < 2) (hs : ScrIn s₀ B 162) (hn : n < 8) (a : At s₀ B n s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {l0 l1 r0 r1 k0 k1 : Word}
    (h5 : Hw (s.xmm .xmm5) r0) (h0 : Hw (s.xmm .xmm0) r1)
    (wl0 : WordAt s.mem B (2 * h) l0) (wl1 : WordAt s.mem B (2 * h + 1) l1)
    (hk0 : KeyAt s.mem B (4 * n + 2 * h) k0) (hk1 : KeyAt s.mem B (4 * n + 2 * h + 1) k1) :
    WP isa (.block (round h)) s fun s' =>
      At s₀ B n s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr = s.gpr ∧ s'.zf = s.zf ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * (2 - 2 * h)), 32⟩] s.mem s'.mem ∧
      WordAt s'.mem B (2 - 2 * h) r0 ∧ WordAt s'.mem B (3 - 2 * h) r1 ∧
      Hw (s'.xmm .xmm5) (l0 ^^^ (Spec.Seed.f k0 k1 r0 r1).1) ∧
      Hw (s'.xmm .xmm0) (l1 ^^^ (Spec.Seed.f k0 k1 r0 r1).2) := by
  have hf : B.toNat + 648 ≤ 2 ^ 32 := hs.fit
  have hle := Nat.le_of_lt hn
  have hkn := a.krNat hf hle
  have hk64 := a.kr64 hf hle
  obtain ⟨hkey, hleft⟩ := round_all h hh
  show WP isa (.block (keyX h ++ (fX ++ leftX h))) s _
  -- the right half to its places, and the keys
  have rel : Rel kparams (envOf kparams s) regs₀ s :=
    (rel_init (p := kparams) (by show s.gpr tbr = s.syms tableName; rw [a.tb, a.syms])
      (by show (s.gpr kr).toNat + 64 ≤ _; omega_using [hkn, hf, hn])
      fun o ho => ⟨_, List.mem_append_right _ (by rw [a.wr]; exact hs.wr), by
        show Region.Contains _ (addr (s.gpr kr) o) 16
        have ho' : o + 16 ≤ 64 := ho
        rw [addr_eq (by omega_using [hkn, hf, hn, ho']), hk64, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_using [hn, ho']) (by omega_using [hn, ho'])⟩).const m0 hm
  have ok : OutOk kparams koparams s := by
    refine ⟨by show (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ _; rw [a.base]; omega_using [hf],
      fun o ho => ⟨_, by rw [a.wr]; exact hs.wr, ?_⟩, ?_, by show (s.gpr kr).toNat + 64 ≤ _; omega_using [hkn, hf, hn]⟩
    · show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
      have ho' : o + 16 ≤ 96 := ho
      rw [a.base, addr_eq (by omega_using [hf, ho'])]
      exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])
    · show Region.Disjoint ⟨(s.gpr kr).setWidth 64, 64⟩ ⟨(s.gpr Impl.Modes.X86.sb).setWidth 64, 96⟩
      rw [hk64, a.base]
      exact Offset.disjoint_base _ (by omega_arith) (by omega_using [hn])
  unfold keyOk at hkey
  split at hkey <;> [cases hkey; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hkey
  obtain ⟨⟨⟨⟨⟨⟨o5, o0⟩, ol⟩, p5⟩, p0⟩, cx⟩, cm⟩ := hkey
  refine WP.block_append_iff.mpr (runS_wp ok (RelS.init rel rfl) hrun fun s₁ hr => ?_)
  have a₁ : At s₀ B n s₁ := a.of_gpr hr.gpr hr.rd hr.wr hr.syms
  have m₁ := mask_ok hr.rel cm
  have f₁ : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * (2 - 2 * h)), 32⟩] s.mem s₁.mem := by
    refine hr.frame.sub fun r hr' => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    have he' : e.1 ∈ σ.2.map fun e => e.1 := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [ol] at he'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base]
    rcases he' with e | e <;> rw [e] <;> exact Offset.sub _ (by show _ ≤ 32 + _; omega_using [hh])
      (by show 32 + _ + 16 ≤ _; omega_using [hh])
  have wr0 : WordAt s₁.mem B (2 - 2 * h) r0 := fun q hq => by
    have := hr.out o5 hq
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base] at this
    rw [sAt, show 32 + 16 * (2 - 2 * h) + q = oR + 16 * (2 - 2 * h) + q from rfl, this]
    simp only [BV.eval, sum, BitVec.xor_zero, env_var kparams .xmm5 hq]
    exact h5 q hq
  have wr1 : WordAt s₁.mem B (3 - 2 * h) r1 := fun q hq => by
    have := hr.out o0 hq
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, a.base] at this
    rw [sAt, show 32 + 16 * (3 - 2 * h) + q = oR + 16 * (3 - 2 * h) + q from rfl, this]
    simp only [BV.eval, sum, BitVec.xor_zero, env_var kparams .xmm0 hq]
    exact h0 q hq
  have key : ∀ {i : Nat} {k : Word}, KeyAt s.mem B (4 * n + i) k → i < 4 → ∀ q < 16,
      mask (envOf kparams s) (kv (16 * i + q)) nvars = byteOf k (q % 4) := fun {i k} hk hi q hq => by
    rw [env_key kparams (by omega_using [hi, hq]), show (s.gpr kparams.kreg) = s.gpr kr from rfl, hk64,
      Offset.add_ofNat_add_ofNat, ← hk q hq, sAt]
    exact congrArg (fun o => s.mem (B.setWidth 64 + BitVec.ofNat 64 o)) (by omega_arith)
  have x5₁ : Hw (s₁.xmm .xmm5) (r0 ^^^ k0) := fun q hq => by
    have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p5 q hq, BV.same_eval _ c.1]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var kparams .xmm5 hq]
    rw [show 32 * h + q = 16 * (2 * h) + q by omega_arith, key (i := 2 * h) hk0 (by omega_using [hh]) q hq, h5 q hq,
      byteOf_xor]
  have x0₁ : Hw (s₁.xmm .xmm0) (r1 ^^^ k1) := fun q hq => by
    have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p0 q hq, BV.same_eval _ c.2]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var kparams .xmm0 hq]
    rw [show 32 * h + 16 + q = 16 * (2 * h + 1) + q by omega_arith, key (i := 2 * h + 1) hk1 (by omega_using [hh]) q hq, h0 q hq, byteOf_xor]
  have wl0₁ : WordAt s₁.mem B (2 * h) l0 := wl0.frame f₁ (by omega_using [hh]) (by omega_using [hh]) (by omega_using [hh])
  have wl1₁ : WordAt s₁.mem B (2 * h + 1) l1 :=
    wl1.frame f₁ (by omega_using [hh]) (by omega_using [hh]) (by omega_using [hh])
  -- F
  refine WP.block_append_iff.mpr (WP.mono (fX_wp (a₁.env hs m₁) x5₁ x0₁) fun s₂ ⟨sm₂, f5, f0, m₂⟩ => ?_)
  have a₂ := a₁.same sm₂
  -- the left half
  unfold leftOk at hleft
  split at hleft <;> [cases hleft; rename_i ρ hrun']
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hleft
  obtain ⟨⟨⟨q5, q0⟩, cy⟩, cn⟩ := hleft
  refine run_wp (a₂.env hs m₂).rel hrun' fun s₃ hr₃ sm₃ => ?_
  have lft : ∀ {j : Nat} {X : Word}, WordAt s₁.mem B j X → j < 4 → ∀ q < 16,
      mask (envOf params s₂) (kv (oR + 16 * j + q)) nvars = byteOf X (q % 4) := fun {j X} hw hj q hq => by
    rw [env_key params (by show 32 + 16 * j + q < 96; omega_using [hj, hq]),
      show (s₂.gpr params.kreg) = s₂.gpr Impl.Modes.X86.sb from rfl, a₂.base, ← hw q hq, sAt, same_mem sm₂]
    rfl
  have e₃ : s₃.mem = s₁.mem := (same_mem sm₃).trans (same_mem sm₂)
  refine ⟨a₂.same sm₃, mask_ok hr₃ cn, by rw [same_gpr sm₃, same_gpr sm₂, hr.gpr],
    by rw [same_zf sm₃, same_zf sm₂, hr.zf], by rw [e₃]; exact f₁, by rw [e₃]; exact wr0, by rw [e₃]; exact wr1,
    fun q hq => ?_, fun q hq => ?_⟩
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cy q (List.mem_range.mpr hq))
    rw [hr₃.bytes q5 q hq, BV.same_eval _ c.1]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var params .xmm5 hq]
    rw [show oR + 32 * h + q = oR + 16 * (2 * h) + q by omega_arith, lft (j := 2 * h) wl0₁ (by omega_using [hh]) q hq, f5 q hq,
      byteOf_xor, BitVec.xor_comm]
    rfl
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cy q (List.mem_range.mpr hq))
    rw [hr₃.bytes q0 q hq, BV.same_eval _ c.2]
    simp only [BV.eval, sum, BitVec.xor_zero, mask_xor, env_var params .xmm0 hq]
    rw [show oR + 32 * h + 16 + q = oR + 16 * (2 * h + 1) + q by omega_arith, lft (j := 2 * h + 1) wl1₁ (by omega_using [hh]) q hq,
      f0 q hq, byteOf_xor, BitVec.xor_comm]
    rfl

end

/-! ## The block -/

/-- A byte of a word of a block: the words are big-endian. -/
theorem byteOf_wordAt (b : Spec.Seed.Block) (i : Nat) {k : Nat} (hk : k < 4) :
    byteOf (Spec.Seed.wordAt b i) k = b.getD (i + (3 - k)) 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [getLsbD_byteOf _ ht]
  have h4 := Proof.Seed.getLsbD_append4 (b.getD i 0) (b.getD (i + 1) 0) (b.getD (i + 2) 0) (b.getD (i + 3) 0) ht
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
  · exact h4.1
  · exact h4.2.1
  · exact h4.2.2.1
  · exact h4.2.2.2

/-- Word `w` of the block at byte 8 of the scratch buffer. -/
def bwd (m : Mem) (B : BitVec 32) (w : Nat) : Word :=
  Spec.Seed.wordAt (Spec.Seed.blockAt m (B.setWidth 64 + BitVec.ofNat 64 8)) (4 * w)

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Seed.blockAt, Vector.getD, hi]

theorem byteOf_bwd (m : Mem) (B : BitVec 32) {w k : Nat} (hw : w < 4) (hk : k < 4) :
    byteOf (bwd m B w) k = m (B.setWidth 64 + BitVec.ofNat 64 (8 + (4 * w + (3 - k)))) := by
  rw [bwd, byteOf_wordAt _ _ hk, blockAt_getD _ _ (by omega_using [hw, hk]), Offset.add_ofNat_add_ofNat]

section
variable {s : State} {B : BitVec 32}

/-- The mask, and the block in `xmm0` to its four words: the first two in
their places, the third in `xmm5` and the last in `xmm0`. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 162⟩ : Region) ∈ s.wr) (hf : B.toNat + 648 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' =>
      s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 32⟩] s.mem s'.mem ∧
      (∀ w < 2, ∀ q < 16, sAt s'.mem B (32 + 16 * w + q) = byte (s.xmm .xmm0) (4 * w + (3 - q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm5) q = byte (s.xmm .xmm0) (4 * 2 + (3 - q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm0) q = byte (s.xmm .xmm0) (4 * 3 + (3 - q % 4))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have kn := (s.gpr kr).isLt
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr kr).toNat + 0 ≤ _; omega_using [kn])
      (fun o ho => absurd (show o + 16 ≤ 0 from ho) (by omega_arith))
  have ok : OutOk hparams koparams s := by
    refine ⟨by show (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ _; rw [hB]; omega_using [hf],
      fun o ho => ⟨_, hwr, ?_⟩, ?_, by show (s.gpr kr).toNat + 0 ≤ _; omega_using [kn]⟩
    · show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
      have ho' : o + 16 ≤ 96 := ho
      rw [hB, addr_eq (by omega_using [hf, ho'])]
      exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])
    · intro a h₁ _
      simp only [Region.Contains] at h₁
      exact absurd h₁ (by show ¬ _ + 1 ≤ 0; omega_arith)
  have hok := ends_all.1
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨o0, o1⟩, ol⟩, p5⟩, p0⟩, cx⟩, cm⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  have ev : ∀ w < 4, ∀ q, (hw w q).eval (envOf hparams s) = byte (s.xmm .xmm0) (4 * w + (3 - q % 4)) :=
    fun w hw4 q => by
    simp only [hw, BV.eval, sum, BitVec.xor_zero, env_var hparams .xmm0 (show 4 * w + (3 - q % 4) < 16 by omega_arith)]
  have st : ∀ {o w : Nat}, outOk σ.2 o (hw w) = true → w < 4 → o = 32 + 16 * w → ∀ q < 16,
      sAt s'.mem B (32 + 16 * w + q) = byte (s.xmm .xmm0) (4 * w + (3 - q % 4)) := fun {o w} ho hw4 he q hq => by
    have := hr.out ho hq
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, hB, ev w hw4 q] at this
    rw [sAt, ← this, he]
  refine ⟨hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, ?_, fun w hw2 q hq => ?_, fun q hq => ?_, fun q hq => ?_,
    mask_ok hr.rel cm⟩
  · refine hr.frame.sub fun r hr' => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr'
    have he' : e.1 ∈ σ.2.map fun e => e.1 := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [ol] at he'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he'
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [show (s.gpr koparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, hB]
    rcases he' with e | e <;> rw [e] <;> exact Offset.sub _ (by decide) (by decide)
  · rcases (show w = 0 ∨ w = 1 by omega_using [hw2]) with rfl | rfl
    · exact st o0 (by decide) rfl q hq
    · exact st o1 (by decide) rfl q hq
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p5 q hq, BV.same_eval _ c.1, ev 2 (by decide) q]
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes p0 q hq, BV.same_eval _ c.2, ev 3 (by decide) q]

end

/-- Round `j + 1`'s key, of the round keys `rk`. -/
abbrev keyOf (rk : Nat → Word) : Nat → Word × Word := fun j => (rk (2 * j), rk (2 * j + 1))

section
variable {s₀ s : State} {B : BitVec 32} {rk : Nat → Word}

/-- The block at byte 8 of the scratch buffer to its words, and the
registers of the loop. -/
theorem cryptHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 162)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa (.block cryptHead) s fun s' =>
      At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr .eax = BitVec.ofNat 32 8 ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      WordAt s'.mem B 0 (bwd s.mem B 0) ∧ WordAt s'.mem B 1 (bwd s.mem B 1) ∧
      Hw (s'.xmm .xmm5) (bwd s.mem B 2) ∧ Hw (s'.xmm .xmm0) (bwd s.mem B 3) := by
  have hf : B.toNat + 648 ≤ 2 ^ 32 := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_using [hf])]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm 96) :: .mov .eax (.imm 8) :: .movdquLoad .xmm0 ⟨Impl.Modes.X86.sb, 8⟩ :: headX)) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_movi fun s₄ u₄ => ?_
  have e₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have y₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have b₄ : s₄.gpr Impl.Modes.X86.sb = B := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have a₄ : At s B 0 s₄ := by
    refine ⟨b₄, ?_, r₄, w₄, y₄, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        addr_eq (by omega_using [hf]), BitVec.add_zero]
      exact htab
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hB]
      rfl
  have c₄ : s₄.gpr .eax = BitVec.ofNat 32 8 := by rw [u₄.gpr]; rfl
  have ha8 : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_using [hf])
  have hl : InRegions (s₄.rd ++ s₄.wr) (addr (s₄.gpr Impl.Modes.X86.sb) 8) 16 :=
    ⟨_, List.mem_append_right _ (by rw [w₄]; exact hs.wr), by
      rw [b₄, ha8]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_ldx hl ?_
  obtain ⟨s₅, hs₅⟩ : ∃ s₅, s₅ = s₄.setXmm .xmm0 (s₄.mem.readW (addr (s₄.gpr Impl.Modes.X86.sb) 8) 128) := ⟨_, rfl⟩
  rw [← hs₅]
  have a₅ : At s B 0 s₅ := by subst hs₅; exact a₄.of_gpr rfl rfl rfl rfl
  have e₅ : s₅.mem = s.mem := by subst hs₅; exact e₄
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 8 := by subst hs₅; exact c₄
  have hbyte : ∀ k < 16, byte (s₅.xmm .xmm0) k = s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + k)) := fun k hk => by
    subst hs₅
    rw [RegUpd.xmm_setXmm_self]
    show (s₄.mem.readW (addr (s₄.gpr Impl.Modes.X86.sb) 8) 128).extractLsb' (8 * k) 8 = _
    rw [byte_readW _ _ (by omega_using [hk]), b₄, ha8, Offset.add_ofNat_add_ofNat, e₄]
  refine WP.mono (head_wp (B := B) (by rw [a₅.tb, a₅.syms]) a₅.base (by rw [a₅.wr]; exact hs.wr) hf)
    fun s₈ ⟨g₈, _, rd₈, wr₈, sy₈, f₈, wd₈, x5₈, x0₈, m₈⟩ => ?_
  have pb : ∀ w < 4, ∀ q < 16, byte (s₅.xmm .xmm0) (4 * w + (3 - q % 4)) = byteOf (bwd s.mem B w) (q % 4) :=
    fun w hw4 q hq => by
    rw [hbyte _ (by omega_using [hw4]), byteOf_bwd _ _ hw4 (Nat.mod_lt _ (by decide))]
  have f₈' : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 32⟩] s.mem s₈.mem := by
    have f' : Frame _ s₅.mem s₈.mem := f₈
    rwa [e₅] at f'
  refine ⟨a₅.of_gpr g₈ rd₈ wr₈ sy₈, m₈, by rw [g₈]; exact c₅, ?_, fun i hi => (hk i hi).frame f₈' hi (by decide),
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine f₈'.sub fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  · rw [wd₈ 0 (by decide) q hq]; exact pb 0 (by decide) q hq
  · rw [wd₈ 1 (by decide) q hq]; exact pb 1 (by decide) q hq
  · rw [x5₈ q hq]; exact pb 2 (by decide) q hq
  · rw [x0₈ q hq]; exact pb 3 (by decide) q hq

/-- The state with `n` turns left: the keys' pointer after `8 - n` turns,
the turns left in `eax`, the round keys, and the state after `2 (8 - n)`
rounds: its left half in the first two places, its right half in `xmm5`
and `xmm0`. -/
def Inv (s₀ : State) (B : BitVec 32) (rk : Nat → Word) (b : Spec.Seed.Block) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ At s₀ B (8 - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .eax = BitVec.ofNat 32 n ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem ∧ (∀ i < 32, KeyAt s.mem B i (rk i)) ∧
    ∃ l0 l1 r0 r1, Proof.Seed.roundsN (keyOf rk) (2 * (8 - n)) (Proof.Seed.decodeQ b) = (l0, l1, r0, r1) ∧
      WordAt s.mem B 0 l0 ∧ WordAt s.mem B 1 l1 ∧ Hw (s.xmm .xmm5) r0 ∧ Hw (s.xmm .xmm0) r1

/-- A turn of the loop: two rounds. -/
theorem turn_wp (hs : ScrIn s₀ B 162) {b : Spec.Seed.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ B rk b (n - 1) s' := by
  obtain ⟨hn8, a, hm, hc, hfr, hk, l0, l1, r0, r1, hst, w0, w1, h5, h0⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a hst
  have hm8 : m < 8 := by omega_using [hn, hm']
  show WP isa (.block (round 0 ++ (round 1 ++ Impl.Seed.X86.AesNi.step))) s _
  -- round `2 m`
  have ka0 : KeyAt s.mem B (4 * m + 2 * 0) (rk (2 * (2 * m))) := by
    rw [show 4 * m + 2 * 0 = 2 * (2 * m) by omega_arith]; exact hk _ (by omega_using [hm8])
  have ka1 : KeyAt s.mem B (4 * m + 2 * 0 + 1) (rk (2 * (2 * m) + 1)) := by
    rw [show 4 * m + 2 * 0 + 1 = 2 * (2 * m) + 1 by omega_arith]; exact hk _ (by omega_using [hm8])
  refine WP.block_append_iff.mpr (WP.mono (round_ok (h := 0) (by decide) hs hm8 a hm h5 h0 w0 w1 ka0 ka1)
    fun s₁ ⟨a₁, m₁, g₁, z₁, f₁, wa₁, wb₁, x5₁, x0₁⟩ => ?_)
  obtain ⟨R0, hR0⟩ : ∃ R0, R0 = l0 ^^^ (Spec.Seed.f (rk (2 * (2 * m))) (rk (2 * (2 * m) + 1)) r0 r1).1 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = l1 ^^^ (Spec.Seed.f (rk (2 * (2 * m))) (rk (2 * (2 * m) + 1)) r0 r1).2 := ⟨_, rfl⟩
  rw [← hR0] at x5₁
  rw [← hR1] at x0₁
  have k₁ : ∀ i < 32, KeyAt s₁.mem B i (rk i) := fun i hi => (hk i hi).frame f₁ hi (by decide)
  -- round `2 m + 1`
  have kb0 : KeyAt s₁.mem B (4 * m + 2 * 1) (rk (2 * (2 * m + 1))) := by
    rw [show 4 * m + 2 * 1 = 2 * (2 * m + 1) by omega_arith]; exact k₁ _ (by omega_using [hm8])
  have kb1 : KeyAt s₁.mem B (4 * m + 2 * 1 + 1) (rk (2 * (2 * m + 1) + 1)) := by
    rw [show 4 * m + 2 * 1 + 1 = 2 * (2 * m + 1) + 1 by omega_arith]; exact k₁ _ (by omega_using [hm8])
  refine WP.block_append_iff.mpr (WP.mono (round_ok (h := 1) (by decide) hs hm8 a₁ m₁ x5₁ x0₁ wa₁ wb₁ kb0 kb1)
    fun s₂ ⟨a₂, m₂, g₂, z₂, f₂, wa₂, wb₂, x5₂, x0₂⟩ => ?_)
  have k₂ : ∀ i < 32, KeyAt s₂.mem B i (rk i) := fun i hi => (k₁ i hi).frame f₂ hi (by decide)
  have c₀ : s₂.gpr .eax = BitVec.ofNat 32 n := by rw [g₂, g₁, hc]
  show WP isa (.block [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]) s₂ _
  refine wp_addi_x fun s₅ u₅ x₅ => wp_subi_x fun s₆ u₆ x₆ z₆ => WP.block_nil ?_
  have e₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem]
  have xe : s₆.xmm = s₂.xmm := by rw [x₆, x₅]
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 n := by rw [u₅.other _ (by decide), c₀]
  refine ⟨?_, by omega_using [hn8], ?_, by rw [xe]; exact m₂, ?_, ?_, by rw [e₆]; exact k₂, R0, R1,
    r0 ^^^ (Spec.Seed.f (rk (2 * (2 * m + 1))) (rk (2 * (2 * m + 1) + 1)) R0 R1).1,
    r1 ^^^ (Spec.Seed.f (rk (2 * (2 * m + 1))) (rk (2 * (2 * m + 1) + 1)) R0 R1).2, ?_,
    by rw [e₆]; exact wa₂, by rw [e₆]; exact wb₂, by rw [xe]; exact x5₂, by rw [xe]; exact x0₂⟩
  · rw [z₆, c₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₆.rd, u₅.rd]; exact a₂.rd, by rw [u₆.wr, u₅.wr]; exact a₂.wr,
      by rw [u₆.syms, u₅.syms]; exact a₂.syms, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.base
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.esp
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₂.tb
    · rw [u₆.other _ (by decide), u₅.gpr, a₂.kp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₆.gpr, c₅]; exact Wp.ofNat_pred hn
  · rw [e₆]
    exact (hfr.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · rw [show 2 * (8 - (n - 1)) = 2 * m + 1 + 1 by omega_using [hn, hm', hn8], Proof.Seed.roundsN_succ,
      Proof.Seed.roundsN_succ, hst, hR0, hR1]
    rfl

/-- The eight turns: the state after the 16 rounds. -/
theorem loop_wp (hs : ScrIn s₀ B 162) {b : Spec.Seed.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.loop (.block turn) .ne) s (Inv s₀ B rk b 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ Inv s₀ B rk b n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (turn_wp hs hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The last right half, then the last left half, to the block, at byte 8
of the scratch buffer. -/
theorem cryptTail_wp {n : Nat} (hs : ScrIn s₀ B 162) (h : At s₀ B n s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {l0 l1 r0 r1 : Word} (w0 : WordAt s.mem B 0 l0) (w1 : WordAt s.mem B 1 l1) (h5 : Hw (s.xmm .xmm5) r0)
    (h0 : Hw (s.xmm .xmm0) r1) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩] s.mem s'.mem ∧
      ∀ q < 16, s'.mem (B.setWidth 64 + BitVec.ofNat 64 8 + BitVec.ofNat 64 q) =
        byteOf ((#v[r0, r1, l0, l1] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := by
  have hf : B.toNat + 648 ≤ 2 ^ 32 := hs.fit
  have he := h.env hs hm
  have hok := ends_all.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨h2, c2⟩ := hok
  refine WP.block_append_iff.mpr (run_wp he.rel hrun fun s₁ hr hsame => ?_)
  have v : ∀ q < 16, byte (s₁.xmm .xmm5) q =
      byteOf ((#v[r0, r1, l0, l1] : Vector Word 4).getD (q / 4) 0) (3 - q % 4) := fun q hq => by
    have h3 : (3 - q % 4) % 4 = 3 - q % 4 := Nat.mod_eq_of_lt (by omega_arith)
    rw [hr.bytes h2 q hq, BV.same_eval _ (List.all_eq_true.mp c2 q (List.mem_range.mpr hq))]
    simp only [BV.eval, sum, BitVec.xor_zero]
    rcases (show q / 4 = 0 ∨ q / 4 = 1 ∨ q / 4 = 2 ∨ q / 4 = 3 by omega_using [hq]) with e | e | e | e
    · rw [tw, ite_eq_left e, e, env_var params .xmm5 (by omega_arith), h5 _ (by omega_arith), h3]; rfl
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_left e, e, env_var params .xmm0 (by omega_arith),
        h0 _ (by omega_arith), h3]; rfl
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_right (by omega_using [e]), e,
        env_key params (by show 32 + 16 * (2 - 2) + (3 - q % 4) < 96; omega_arith),
        show (s.gpr params.kreg) = s.gpr Impl.Modes.X86.sb from rfl, h.base]
      have := w0 (3 - q % 4) (by omega_arith)
      rw [h3] at this
      exact this
    · rw [tw, ite_eq_right (by omega_using [e]), ite_eq_right (by omega_using [e]), e,
        env_key params (by show 32 + 16 * (3 - 2) + (3 - q % 4) < 96; omega_arith),
        show (s.gpr params.kreg) = s.gpr Impl.Modes.X86.sb from rfl, h.base]
      have := w1 (3 - q % 4) (by omega_arith)
      rw [h3] at this
      exact this
  obtain ⟨f, rfl⟩ := hsame
  have ha : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_using [hf])
  have hwr : InRegions s.wr (addr (s.gpr Impl.Modes.X86.sb) 8) 16 := ⟨_, by rw [h.wr]; exact hs.wr, by
    rw [h.base, ha]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_stx (s := { s with xmm := f }) hwr (WP.block_nil ?_)
  refine ⟨h.base, h.esp, h.rd, h.wr, h.syms, ?_, fun q hq => ?_⟩
  · show Frame _ s.mem (s.mem.writeW (addr (s.gpr Impl.Modes.X86.sb) 8) (f .xmm5))
    rw [h.base, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s.mem.writeW (addr (s.gpr Impl.Modes.X86.sb) 8) (f .xmm5)) _ = _
    rw [h.base, ← ha,
      ← byte_readW (s.mem.writeW (addr B 8) (f .xmm5)) (addr B 8) (w := 128) (k := q) (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact v q hq

private theorem ofFn_toList (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- `crypt` enciphers the block at byte 8 of the scratch buffer, under the
round keys in their places, and changes nothing else but the four places of
the state's halves. -/
theorem crypt_wp {k : Spec.Seed.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 162)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (k.getD i 0)) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩, ⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (k.getD i 0)) ∧
      Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16 =
        Spec.Seed.cipher k (Spec.Aes.bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16) := by
  obtain ⟨rk, hrk⟩ : ∃ rk : Nat → Word, rk = fun i => k.getD i 0 := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = Spec.Seed.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) := ⟨_, rfl⟩
  have hk' : ∀ i < 32, KeyAt s.mem B i (rk i) := by rw [hrk]; exact hk
  show WP isa (.seq (.block cryptHead) (.seq (.loop (.block turn) .ne) (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs htab hk') fun s₁ ⟨a₁, m₁, c₁, f₁, k₁, w0₁, w1₁, x5₁, x0₁⟩ => ?_)
  have hI : Inv s B rk blk 8 s₁ := by
    refine ⟨Nat.le_refl _, a₁, m₁, c₁, f₁, k₁, bwd s.mem B 0, bwd s.mem B 1, bwd s.mem B 2, bwd s.mem B 3, ?_,
      w0₁, w1₁, x5₁, x0₁⟩
    rw [hblk]; rfl
  refine WP.seq (WP.mono (loop_wp hs (by decide) hI)
    fun s₂ ⟨_, a₂, m₂, _, f₂, k₂, l0, l1, r0, r1, h16, v0, v1, v5, vx⟩ => ?_)
  refine WP.mono (cryptTail_wp hs a₂ m₂ v0 v1 v5 vx) fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, ?_, ?_, ?_⟩
  · exact (f₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · intro i hi q hq
    have := f₃.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_using [hi, hq]) (by decide))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    have e := k₂ i hi q hq
    rw [hrk] at e
    rw [sAt, this]
    exact e
  · rw [Spec.Seed.cipher, Proof.Seed.bytesAt_eq s.mem, ofFn_toList, ← hblk, Spec.Seed.encryptBlock,
      Proof.Seed.crypt_eq]
    have hc : Proof.Seed.roundsN (Spec.Seed.roundKey k) 16 (Proof.Seed.decodeQ blk) = (l0, l1, r0, r1) := by
      rw [← h16, hrk]; rfl
    rw [hc, show Proof.Seed.encodeSwapped (l0, l1, r0, r1) = Vector.ofFn fun i : Fin 16 =>
      byteOf ((#v[r0, r1, l0, l1] : Vector Word 4).getD (i.val / 4) 0) (3 - i.val % 4) from rfl]
    refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
    have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
    rw [Vector.getElem_toList, Vector.getElem_ofFn]
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    exact v₃ q hq

end

/-! ## The round keys `prepare` leaves -/

section

open VG.Impl.Modes.X86 (at_ argOp)

/-- Round key `i` of the schedule at `p`. -/
def rkAt (m : Mem) (p : BitVec 32) (i : Nat) : Word := (Spec.Seed.scheduleAt m (p.setWidth 64)).getD i 0

/-- The schedule's words are little-endian. -/
theorem byteOf_rkAt (m : Mem) (p : BitVec 32) {i k : Nat} (hi : i < 32) (hk : k < 4) :
    byteOf (rkAt m p i) k = m (p.setWidth 64 + BitVec.ofNat 64 (4 * i + k)) := by
  rw [rkAt, Proof.Seed.vector_getD _ _ hi, Proof.Seed.scheduleAt_readW _ _ _ hi, byteOf_eq,
    byte_readW _ _ (by omega_using [hk]), Offset.add_ofNat_add_ofNat]

/-- The schedule's bytes in `m` are those of `M`. -/
def Sch (M m : Mem) (p : BitVec 32) : Prop :=
  ∀ o < 128, m (p.setWidth 64 + BitVec.ofNat 64 o) = M (p.setWidth 64 + BitVec.ofNat 64 o)

/-- What `prepare` needs of the state it starts in: the scratch buffer, and
the schedule, apart from it. -/
structure PEnv (s₀ : State) (B p : BitVec 32) : Prop where
  scr : ScrIn s₀ B 162
  sch : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 648⟩

/-- A state of `prepare` after `i` groups of four round keys: the
schedule's pointer, the round keys' pointer, the table's address, and the
mask. -/
structure PAt (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (16 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * i)

variable {s₀ s : State} {B p : BitVec 32} {i : Nat} {M : Mem}

theorem PAt.kr64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * i) := by
  have hf := he.scr.fit
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * i) := by
  have hf := he.scr.fit
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
  have hf := he.pfit
  rw [h.sp]; exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).toNat = p.toNat + 16 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- Four round keys of the schedule to their places (`prepGroupX`). -/
theorem prepGroupX_wp (he : PEnv s₀ B p) (hi : i < 8) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block prepGroupX) s fun s' => PAt s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * i), 64⟩] s.mem s'.mem ∧
      ∀ w < 4, KeyAt s'.mem B (4 * i + w) (rkAt M p (4 * i + w)) := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have hk := h.krNat he hi
  have ha := h.axNat he hi
  have rel : Rel pparams (envOf pparams s) Regs.init s :=
    rel_init (p := pparams) (by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms])
      (by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith)
      fun o ho => ⟨_, by rw [h.rd, h.wr]; exact he.sch, by
        show Region.Contains _ (addr (s.gpr .eax) o) 16
        have ho' : o + 16 ≤ 16 := ho
        rw [addr_eq (by omega_arith), h.ax64 he hi, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ok : OutOk pparams poparams s := by
    refine ⟨by show (s.gpr kr).toNat + 64 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
      by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 64 := ho
      rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 16⟩ ⟨(s.gpr kr).setWidth 64, 64⟩
      rw [h.ax64 he hi, h.kr64 he hi]
      exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have hok := prep_ok
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, oin⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  have st : ∀ {w : Nat}, outOk σ.2 (16 * w) (pw w) = true → w < 4 → KeyAt s'.mem B (4 * i + w) (rkAt M p (4 * i + w)) :=
    fun {w} ho hw4 q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have := hr.out ho hq
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
    rw [sAt, show 96 + 16 * (4 * i + w) + q = 96 + 64 * i + (16 * w + q) by omega_arith, this, pw, BV.eval, sum,
      BitVec.xor_zero, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (4 * w + q % 4) < 1024; omega_using [hw4]), envOf_key,
      show (s.gpr pparams.kreg) = s.gpr .eax from rfl, h.ax64 he hi, Offset.add_ofNat_add_ofNat,
      hS _ (by omega_using [hi, hw4]), byteOf_rkAt _ _ (by omega_using [hi, hw4]) h4]
    exact congrArg (fun o => M (p.setWidth 64 + BitVec.ofNat 64 o)) (by omega_arith)
  refine ⟨⟨by rw [hr.gpr]; exact h.base, by rw [hr.gpr]; exact h.esp, hr.rd.trans h.rd, hr.wr.trans h.wr,
    hr.syms.trans h.syms, by rw [hr.gpr]; exact h.tb, by rw [hr.gpr]; exact h.sp, by rw [hr.gpr]; exact h.kp⟩,
    by rw [hr.gpr], ?_, fun w hw4 => ?_⟩
  · have := hr.frameIn oin
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, BitVec.add_zero, Nat.sub_zero] at this
    exact this
  · rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact st o0 (by decide)
    · exact st o1 (by decide)
    · exact st o2 (by decide)
    · exact st o3 (by decide)

/-- The schedule is outside what `prepare` writes. -/
theorem Sch.frame {m m' : Mem} {a n : Nat} (h : Sch M m p) (he : PEnv s₀ B p)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 648) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ PAt s₀ B p (8 - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 96, 512⟩] m₁ s.mem ∧
    ∀ j < 4 * (8 - n), KeyAt s.mem B j (rkAt M p j)

theorem pturn_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv s₀ M m₁ B p n s) :
    WP isa (.block prepGroup) s fun s' => s'.zf = some (decide (n = 1)) ∧ PInv s₀ M m₁ B p (n - 1) s' := by
  obtain ⟨hn8, a, hc, hS, hF, K⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a K
  have hm8 : m < 8 := by omega_using [hn, hm']
  have hf := he.scr.fit
  refine WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hm8 a hS) fun s₁ ⟨a₁, c₁, f₁, k₁⟩ => ?_)
  show WP isa (.block [.alu .add .eax (.imm 16), .alu .add kr (.imm 64), .alu .sub .ecx (.imm 1)]) s₁ _
  refine wp_addi_x fun s₂ u₂ x₂ => wp_addi_x fun s₃ u₃ x₃ => wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have e₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁, hc]
  refine ⟨?_, by omega_using [hn8], ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [z₄, c₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd]; exact a₁.rd, by rw [u₄.wr, u₃.wr, u₂.wr]; exact a₁.wr,
      by rw [u₄.syms, u₃.syms, u₂.syms]; exact a₁.syms, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.base
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.esp
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.tb
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, a₁.sp,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), a₁.kp,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₄.gpr, c₃]; exact Wp.ofNat_pred hn
  · rw [e₄]
    exact hS.frame he f₁ (by omega_using [hm8])
  · rw [e₄]
    refine hF.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by omega_arith) (by omega_using [hm8])
  · rw [e₄]
    by_cases hj' : j < 4 * m
    · intro q hq
      have := f₁.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * j + q), 1⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj', hq])) (by omega_using [hj', hq, hm8])
          (by omega_using [hm8])) (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
      rw [BitVec.add_zero] at this
      rw [sAt, this]
      exact K j hj' q hq
    · have := k₁ (j - 4 * m) (by omega_using [hj, hj', hn, hm', hn8])
      rwa [show 4 * m + (j - 4 * m) = j by omega_using [hj']] at this

/-- The eight groups: the 32 round keys in their places. -/
theorem ploop_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv s₀ M m₁ B p n s) :
    WP isa (.loop (.block prepGroup) .ne) s (PInv s₀ M m₁ B p 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ PInv s₀ M m₁ B p n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (pturn_wp he hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The table's address to the scratch buffer's first slot, and the
registers of the loop (`prepHead`), with the table's address in `eax`. -/
theorem prepHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hax : s.gpr .eax = s.syms tableName)
    (hS : Sch M s.mem p) (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4)
    (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 648⟩) :
    WP isa (.block prepHead) s fun s' => PAt s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 8 ∧ Sch M s'.mem p ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.syms tableName := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) ::
    .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 96) ::
    [.mov .ecx (.imm 8)])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 648⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0)
    fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => WP.block_nil ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have w₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have y₇ : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have b₇ : s₇.gpr Impl.Modes.X86.sb = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hB]
  have sp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
  have t₇ : s₇.gpr tbr = s.syms tableName := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.gpr, hax]
  have a₇ : s₇.gpr .eax = p := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  have c₇ : s₇.gpr .ecx = BitVec.ofNat 32 8 := by rw [u₇.gpr]; rfl
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (96 + 64 * 0) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
    rfl
  have hS₇ : Sch M s₇.mem p := by
    rw [m₇]
    exact hS.frame (a := 0) he (by rw [BitVec.add_zero]; exact f₂) (by decide)
  refine ⟨⟨b₇, sp₇, r₇, w₇, y₇, t₇, by rw [a₇]; simp, k₇⟩, c₇, hS₇, by rw [m₇]; exact f₂, ?_⟩
  rw [m₇, u₂.mem, ha0, Mem.readW_writeW_self32, hax]

/-- `prepare` leaves the round keys of the schedule in their places, and the
table's address in the scratch buffer's first slot; it writes only the
core's slots, and the four bytes below `esp` of the frame that gets the
table's address. -/
theorem prepare_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 648⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩) :
    WP isa prepare s fun s' => (∀ i < 32, KeyAt s'.mem B i (rkAt s.mem p i)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 608⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := he.scr.fit
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead)
    (.loop (.block prepGroup) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have he₁ : PEnv s₁ B p :=
    ⟨⟨by rw [a₁.wr]; exact he.scr.wr, he.scr.fit⟩, by rw [a₁.rd, a₁.wr]; exact he.sch, he.pfit, he.sep⟩
  have hS₁ : Sch s.mem s₁.mem p := fun o ho =>
    a₁.frame.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hkS.symm) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  have p₁ : s₁.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  refine WP.seq (WP.mono (prepHead_wp (M := s.mem) (by rw [a₁.gpr _ (by decide)]; exact hB) he₁
    (by rw [a₁.addr, a₁.syms]) hS₁ (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁]; exact p₁)
    (by rw [ea₁]; exact h0B)) fun s₂ ⟨a₂, c₂, hS₂, f₂, t₂⟩ => ?_)
  have hI : PInv s₁ s.mem s₂.mem B p 8 s₂ :=
    ⟨Nat.le_refl _, a₂, c₂, hS₂, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine WP.mono (ploop_wp he₁ (by decide) hI) fun s₃ ⟨_, a₃, _, _, F₃, K₃⟩ => ?_
  refine ⟨K₃, ?_, a₃.base, a₃.esp.trans esp₁, a₃.rd.trans a₁.rd, a₃.wr.trans a₁.wr, a₃.syms.trans a₁.syms, ?_⟩
  · rw [F₃.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine ((a₁.frame.mono fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (F₃.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩

end

/-! ## The core -/

section

open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument, and the four bytes below `esp` apart
from both. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Seed.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Seed.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩

theorem ea_esp {s s' : State} (h : s'.gpr .esp = s.gpr .esp) (i : Nat) : s'.ea (argOp i) = s.ea (argOp i) := by
  show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64
  rw [h]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Seed.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := h
  have hea := ea_esp hesp
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hea]; exact hd0, by rw [hesp]; exact hkS, by rw [hesp, hea]; exact h0S⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hd0 (by decide), hp]
  · rw [hk]
    exact (Proof.Seed.scheduleAt_frame hf hdis).symm

/-- The key `k` is ready in the scratch buffer at `B`: its round keys in
their places, and the table's address in the first slot. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.Seed.Schedule) : Prop :=
  (∀ i < 32, KeyAt s.mem B i (k.getD i 0)) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    B.toNat + 648 ≤ 2 ^ 32

theorem core_slots : core.slots = 152 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its buffer. -/
theorem ready_frame {s s' : State} {B : BitVec 32} {k : Spec.Seed.Schedule} {rs : List Region}
    (h : Ready s B k) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) : Ready s' B k := by
  obtain ⟨hk, ht, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 608 → (a + n ≤ 8 ∨ 24 ≤ a) → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * core.buf) (k := 4 * core.bw * core.G)
        (by show a + n ≤ 8 ∨ 8 + 16 ≤ a; omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨fun i hi q hq => ?_, ?_, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩)
      (keep (by omega_arith) (.inr (by omega_arith))) (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0)
      (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
    exact hk i hi q hq
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide) (.inl (by decide))) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

theorem prepare_ok {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Seed.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B core.total)
    (hR : (⟨B.setWidth 64, 4 * core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : core.stack ≤ (s.gpr .esp).toNat) :
    WP isa core.prepare s fun s' => Ready s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := hk
  have he : PEnv s B p := ⟨hs, hsch, hfit, hdis _ hR⟩
  refine WP.mono (prepare_wp hB he hsp hin0 hp (hd0 _ hR) hkS h0S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨fun i hi => ?_, by rw [t, sy], hs.fit⟩, b, e, f, rd, wr⟩
  rw [hk]
  exact K i hi

theorem crypt_ok {s : State} {B : BitVec 32} {k : Spec.Seed.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : ScrIn s B core.total) (hr : Ready s B k) :
    WP isa core.crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Seed.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, ht, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs ht hk) fun s' ⟨b, e, rd, wr, sy, f, k', v⟩ => ?_
  have hblk : blkAddr core B 0 = B.setWidth 64 + BitVec.ofNat 64 8 := by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 2) + BitVec.ofNat 64 (4 * 4 * 0) = _
    rw [Offset.add_ofNat_add_ofNat]
  refine ⟨b, e, ⟨k', ?_, hfit⟩, f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [f.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), sy]
    exact ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · have h0 : j = 0 := by
      have : j < 1 := hj
      omega_arith
    subst h0
    rw [hblk]
    exact v

/-- SEED's core by the AES S-box meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Spec.Seed.Schedule
  cipher k := Spec.Seed.cipher k
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Seed.cipher, core]
  layout := ⟨by decide, .inr rfl, by decide, by decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ sy f _ hd := ready_frame h sy f hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Seed.X86.AesNi
