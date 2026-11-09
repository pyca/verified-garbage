module

-- separate module: its proofs cost more than its imports, and its importer's changes need
-- not re-check them

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Hmac
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Ecdh.RISCV64.Num4
import VerifiedGarbage.Proof.Ecdh.RISCV64.Num0
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.X25519.RISCV64.Instr

/-!
# Deterministic ECDSA on RISC-V: the prologue, `X`, `h`, and steps b–g

The prologue saves our caller's `ra` and `s0`–`s9` and moves the pointers
into `s0`–`s4` and `s6`, and `D` and `B` from the table into `s7` and `s8`
(`prologue_ok`, after which `KR` holds); `X`, `Q - min(D, Q)` zero bytes and
the digest's leftmost `min(D, Q)` (`prepX_ok`, the minimum by `minSel`);
`h = bits2octets(digest)`, `X` reduced modulo `n` unless `big`, else `X`
itself (`prepH_ok`); `K = 0x00…` and `V = 0x01…` (`initKV_ok`); then steps
d–g (`rekeyFull_ok`), and step h.3 (`rekey_ok`). Doublewords stored in the
frame (`sds_ok`) give the bytes of a word (`bytesAt_of_readW`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_add wp_sub wp_ld wp_sd wp_sb wp_srl wp_sll wp_or wp_addSp)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.RISCV64 (WsReg addCall_ok CallKeep)
open VG.Proof.Mont (wordsVal Outside Outs)
open Spec.Sha256 (bytesAt)

variable {P : Rfc}

/-! ## Arithmetic -/

/-- The sign bit of `x - y`, for `x, y < 2^63`, is `x < y`. -/
theorem ltBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = if x < y then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> simp <;> omega

/-- `b + ((a - b) ∧ -(a < b))`: `min(b, a)`. -/
theorem minSel {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 b + ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63)) = BitVec.ofNat 64 (min b a) := by
  rw [ltBit ha hb]
  by_cases h : a < b
  · rw [ite_eq_left h, show BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      Nat.min_eq_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right h, show BitVec.ofNat 64 0 - 0 = 0#64 by decide, BitVec.and_zero, BitVec.add_zero,
      Nat.min_eq_left (by omega)]

/-- The `8 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 64) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (8 * j)) 64 = w) :
    bytesAt m q (8 * k) = (List.range (8 * k)).map fun i => w.extractLsb' (8 * (i % 8)) 8 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 8 * (i / 8) + i % 8 by omega, Proof.Weierstrass.byte_word m q (i / 8) (Nat.mod_lt _ (by decide)),
    h _ (by omega)]
  congr 2; omega

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

/-- Bytes apart from what changed. -/
theorem fbytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-! ## Doublewords stored in the frame -/

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- Doublewords `v` from registers, stored to the frame at offsets `o` (each
a multiple of 8, after the save area): each written region, and what each
doubleword is after the last store to it. -/
theorem sds_ok : ∀ (l : List (Reg × Nat)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ q ∈ l, 96 ≤ q.2 ∧ q.2 + 8 ≤ frB ∧ q.2 % 8 = 0) → (l.map (·.2)).Nodup → KR P s₀ s →
    (∀ t, KR P s₀ t → t.gpr = s.gpr → Frame (l.map fun q => sR s₀ q.2 8) s.mem t.mem →
      (∀ q ∈ l, t.mem.readW (sA s₀ q.2) 64 = s.gpr q.1) → WP isa (.block rest) t Q) →
    WP isa (.block (l.map (fun q => .store .d q.1 .s1 q.2) ++ rest)) s Q
  | [], s, rest, Q, _, _, h, k => k s h rfl (Frame.refl _ _) (fun _ h => absurd h (by simp))
  | (r, o) :: l, s, rest, Q, hl, hn, h, k => by
    have hj := hl (r, o) (by simp)
    simp only at hj
    have hfr : frB = 512 := rfl
    simp only [List.map_cons, List.cons_append]
    refine wp_sd (a := sA s₀ o) (by omega) (by rw [h.s1])
      (by
        show (s₀.sp + BitVec.ofNat 64 o).toNat % 8 = 0
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := hp.al; have := hp.top
        omega)
      (in_fr hp h.wr (by omega)) fun t₁ m₁ => ?_
    have F₁ : Frame [sR s₀ o 8] s.mem t₁.mem := by
      rw [m₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have k₁ : KR P s₀ t₁ := h.keep m₁.rd m₁.wr m₁.sp (fun r _ => by rw [m₁.gpr]) F₁
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl hj.1) (by decide) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, part_sub (by omega)⟩)
    have hn' := List.nodup_cons.mp hn
    exact sds_ok l (fun q hq => hl q (by simp [hq])) hn'.2 k₁ fun t h' g f hv =>
      k t h' (g.trans m₁.gpr) ((F₁.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, List.mem_cons_self, fun x hx => hx⟩).trans (f.sub fun r hr =>
          ⟨r, List.mem_cons_of_mem _ hr, fun x hx => hx⟩))
        (fun q hq => by
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · rw [f.readW (r := sR s₀ o 8) (by exact Region.contains_self _ _) (fun r hr => by
              simp only [List.mem_map] at hr
              obtain ⟨q', hq', rfl⟩ := hr
              have hq'' := hl q' (by simp [hq'])
              have hne : o ≠ q'.2 := fun e => hn'.1 (List.mem_map.mpr ⟨q', hq', e.symm⟩)
              exact part_disj (by omega) (by omega) (by omega)) (by decide), m₁.mem,
              Mem.readW_writeW_self64]
          · rw [hv q hq, m₁.gpr])

end

/-! ## The prologue -/

theorem prologue_eq : Cfg.prologue = .addSp .t0 0 :: (Spill.saveCode .t0 saved ++
    [mov .s1 .t0, mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s0 .a4, mov .s6 .a5, .load .d .s7 .a5 32,
      .load .d .s8 .a5 40]) := rfl

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem prologue_ok : WP isa (.block Cfg.prologue) s₀ (KR P s₀) := by
  rw [prologue_eq]
  have hfr : frB = 512 := rfl
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  have t0 : s₁.gpr .t0 = s₀.sp := by rw [u₁.gpr, BitVec.add_zero]
  have e₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  refine Spill.save_ok (b := .t0) (by rw [t0]; omega_using [hp.al])
    (fun q hq => by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun q hq => by
      rw [t0, u₁.wr]
      exact in_fr hp rfl (by have := saved_in q hq; omega)) ?_
  have hsv : ∀ m, Frame [⟨s₀.sp, 96⟩] s₁.mem m → ∀ o, o + 8 ≤ 48 →
      m.readW (tab s₀ + BitVec.ofNat 64 o) 64 = s₀.mem.readW (tab s₀ + BitVec.ofNat 64 o) 64 := by
    intro m hm o ho
    rw [hm.readW (r := tabR s₀) (Offset.contains_base _ ho (by have := hp.nt; omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_wr (frR s₀) (by simp)).sub_right (Region.sub_prefix (by omega))) (by decide), u₁.mem]
  have hin : ∀ o, o + 8 ≤ 48 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (tab s₀ + BitVec.ofNat 64 o) 8 := fun o ho s hrd _ =>
    ⟨tabR s₀, List.mem_append_left _ (by rw [hrd, hp.rd]; simp),
      Offset.contains_base _ ho (by have := hp.nt; omega)⟩
  have hal : ∀ o, o % 8 = 0 → o + 8 ≤ 48 → (tab s₀ + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o ho ho' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hp.ta; have := hp.nt; omega
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ =>
    wp_mv fun s₇ u₇ => ?_
  have a5 : s₇.gpr .a5 = tab s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), e₁ _ (by decide)]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]; exact u₁.rd
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]; exact u₁.wr
  have mm : s₇.mem = Spill.saveMem s₁.mem s₀.sp s₁.gpr saved := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    show Spill.saveMem s₁.mem (s₁.gpr .t0) s₁.gpr saved = _
    rw [t0]
  have F₇ : Frame [⟨s₀.sp, 96⟩] s₁.mem s₇.mem := by
    rw [mm]
    exact Spill.saveMem_frame_base (n := 96) (fun p hp' => (saved_in p hp').2) (by omega) _ _ _
  refine wp_ld (by decide) (by rw [a5]) (hal 32 (by decide) (by decide)) (hin 32 (by decide) _ rd₇ wr₇)
    fun s₈ u₈ => wp_ld (by decide) (by rw [u₈.other _ (by decide), a5]) (hal 40 (by decide) (by decide))
      (hin 40 (by decide) s₈ (by rw [u₈.rd, rd₇]) (by rw [u₈.wr, wr₇])) fun s₉ u₉ => WP.block_nil ?_
  have gg : ∀ r, r ∉ [Reg.s1, .s2, .s3, .s4, .s0, .s6, .s7, .s8] → s₉.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d, f, g, h7, h8⟩ := hr
    rw [u₉.other r h8, u₈.other r h7, u₇.other r g, u₆.other r f, u₅.other r d, u₄.other r c, u₃.other r b,
      u₂.other r a]
  have sv : Spill.Saved s₀.sp s₀.gpr saved s₉.mem := by
    rw [u₉.mem, u₈.mem, mm]
    intro q hq
    rw [Spill.saveMem_saved saved_fits s₁.mem s₀.sp s₁.gpr q hq]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact e₁ _ (by decide)
  refine ⟨by rw [u₉.rd, u₈.rd]; exact rd₇, by rw [u₉.wr, u₈.wr]; exact wr₇,
    by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]; exact u₁.sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun q hq => ?_, sv, ?_⟩
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact t0
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · upd_simp [u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr,
      u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other]
    exact e₁ _ (by decide)
  · rw [u₉.other _ (by decide), u₈.gpr, hsv _ F₇ 32 (by decide)]; exact hp.tD
  · rw [u₉.gpr, u₈.mem, hsv _ F₇ 40 (by decide)]; exact hp.tB
  · rw [gg q (by revert q; decide), e₁ q (by revert q hq; decide)]
  · rw [u₉.mem, u₈.mem]
    have F₇' := F₇
    rw [u₁.mem] at F₇'
    refine F₇'.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, by simp, Region.sub_prefix (by omega)⟩

end

/-! ## `X`, `h` -/

/-- The values of the run: the private key and its bytes, the digest and its
integer, and `h`. -/
abbrev dB (P : Rfc) (s₀ : State) : List Byte := bytesAt s₀.mem (dk s₀) P.Q
abbrev xOf (P : Rfc) (s₀ : State) : Nat := Spec.Weierstrass.ofBytes (dB P s₀)
abbrev hBOf (P : Rfc) (s₀ : State) : List Byte := bytesAt s₀.mem (dg s₀) P.H.D
abbrev eOf (P : Rfc) (s₀ : State) : Nat := Spec.Ecdsa.hashToInt P.kit.E.curve (hBOf P s₀)
abbrev hSpec (P : Rfc) (s₀ : State) : List Byte := Spec.Ecdsa.Rfc6979.bits2octets P.kit.E.curve (hBOf P s₀)

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
abbrev xSpec (P : Rfc) (s₀ : State) : List Byte :=
  List.replicate (P.Q - min P.H.D P.Q) 0 ++ (hBOf P s₀).take (min P.H.D P.Q)

/-- `V`, `X` and `h` in the frame. -/
abbrev vOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fV) P.H.D
abbrev xOfM (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ fX) P.Q
abbrev hOf (P : Rfc) (s₀ : State) (m : Mem) : List Byte := bytesAt m (sA s₀ P.c.fHo) P.Q

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

omit hp in
theorem xArgs_eq : P.c.xArgs = .li .t0 0 :: (((List.range 9).map fun j => (Reg.t0, fX + 8 * j)).map
    (fun q => .store .d q.1 .s1 q.2) ++
    ([.li .t1 P.c.Q, .sub .t2 .s7 .t1, .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3,
      .logic .and .t2 .t2 .t3, .add .a6 .t1 .t2, mov .a4 .s4, .addi .a5 .s1 (fX + P.c.Q), .sub .a5 .a5 .a6] :
      List Instr)) := by
  rw [Cfg.xArgs, List.map_map]; rfl

/-- `X`: `Q - min(D, Q)` zero bytes, then the digest's leftmost `min(D, Q)`. -/
theorem prepX_ok {s : State} (h : KR P s₀ s) :
    WP isa P.c.prepX s fun t => KR P s₀ t ∧ xOfM P s₀ t.mem = xSpec P s₀ ∧ Frame [sR s₀ fX 72] s.mem t.mem := by
  have hz := sizes P
  have hfr : frB = 512 := rfl
  obtain ⟨hQ1, hQ2, hcQ, -⟩ := hz.Q
  obtain ⟨hD0, hD64⟩ := hz.D
  unfold Cfg.prepX
  rw [xArgs_eq, hcQ]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => ?_)
  have k₁ := h.upd (by decide) u₁
  refine sds_ok hp _ (fun q hq => by
      simp only [List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      simp only [fX]; omega) (by decide) k₁ fun t₂ k₂ g₂ f₂ v₂ => ?_
  refine wp_li (imm := P.Q) (by omega) fun s₃ u₃ => wp_sub fun s₄ u₄ => wp_srl (by decide) fun s₅ u₅ =>
    wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => VG.Proof.X25519.RISCV64.wp_and fun s₈ u₈ =>
    wp_add fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => wp_addi (by simp only [fX]; omega) fun s₁₁ u₁₁ =>
    wp_sub fun s₁₂ u₁₂ => WP.block_nil ?_
  have k₁₂ : KR P s₀ s₁₂ := (((((((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide)
    u₆).upd (by decide) u₇).upd (by decide) u₈).upd (by decide) u₉).upd (by decide) u₁₀).upd (by decide) u₁₁).upd
    (by decide) u₁₂
  have m₁₂ : s₁₂.mem = t₂.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  -- the count, `min(D, Q)`
  have hN : s₁₂.gpr .a6 = BitVec.ofNat 64 (min P.Q P.H.D) := by
    upd_simp [u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other,
      u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other]
    rw [g₂, u₁.other _ (by decide), h.s7]
    exact minSel (by omega) (by omega)
  have hmin : min P.Q P.H.D = min P.H.D P.Q := Nat.min_comm _ _
  rw [hmin] at hN
  generalize hm : min P.H.D P.Q = m at hN
  have hm1 : 0 < m := by omega
  have hm2 : m ≤ P.Q := by omega
  have hm3 : m ≤ P.H.D := by omega
  have hsrc : s₁₂.gpr .a4 = dg s₀ := by
    upd_simp [u₁₂.other, u₁₁.other, u₁₀.gpr]
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide), h.s4]
  have hdst : s₁₂.gpr .a5 = sA s₀ (fX + (P.Q - m)) := by
    have hN11 : s₁₁.gpr .a6 = BitVec.ofNat 64 m := by rw [← u₁₂.other .a6 (by decide)]; exact hN
    have hs1 : s₁₀.gpr .s1 = s₀.sp := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂,
        u₁.other _ (by decide), h.s1]
    rw [u₁₂.gpr, u₁₁.gpr, hN11, hs1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, fX]
    have := hp.top
    omega
  have rd₁₂ := k₁₂.rd
  have wr₁₂ := k₁₂.wr
  refine WP.mono (WP.rdwr (copyLoop_adv (tmp := .t1) (src := .a4) (dst := .a5) (cnt := .a6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₁₂ hm1 (by omega) hN
    (fun i hi => by
      rw [hsrc, rd₁₂]
      exact ⟨dgR P s₀, List.mem_append_left _ (by rw [hp.rd]; simp),
        Offset.contains_base _ (by omega) (by have := hp.ng; omega)⟩)
    (fun i hi => by
      rw [hdst]
      have := in_fr hp wr₁₂ (o := fX + (P.Q - m) + i) (n := 1) (by simp only [fX]; omega)
      rwa [add_ofNat_add'])
    (fun x hx hx' => by
      rw [hdst] at hx
      rw [hsrc] at hx'
      have d := (hp.f_g.sub_left (part_sub (s₀ := s₀) (o := fX + (P.Q - m)) (n := m) (by simp only [fX]; omega))).sub_right
        (Region.sub_prefix (base := dg s₀) hm3)
      exact d x hx hx'))) fun t ⟨⟨hc, hf, hk, _⟩, hrd, hwr, hsp⟩ => ?_
  rw [hdst] at hc hf
  have F₃ : Frame [sR s₀ fX 72] s.mem t.mem := by
    rw [← m₁₂] at f₂
    have f₂' : Frame [sR s₀ fX 72] s₁.mem s₁₂.mem := f₂.sub fun r hr => by
      simp only [List.map_map, List.mem_map, List.mem_range] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by simp only [fX]; omega) (by simp only [fX]; omega)⟩
    rw [u₁.mem] at f₂'
    exact f₂'.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by simp only [fX]; omega) (by simp only [fX]; omega)⟩)
  refine ⟨k₁₂.keep hrd hwr hsp (fun r hr => hk.gpr (by revert r; decide)) hf
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fX]; omega)) (by decide) (by simp only [fX]; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by simp only [fX]; omega)⟩), ?_, F₃⟩
  -- the bytes
  have z₂ : bytesAt t₂.mem (sA s₀ fX) (8 * 9) = List.replicate 72 0 := by
    rw [bytesAt_of_readW (k := 9) _ _ 0 fun j hj => by
      have := v₂ (Reg.t0, fX + 8 * j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      rw [add_ofNat_add', this]; exact u₁.gpr]
    decide
  have hsp' : P.Q = (P.Q - m) + m := by omega
  show bytesAt t.mem (sA s₀ fX) P.Q =
    List.replicate (P.Q - min P.H.D P.Q) 0 ++ (hBOf P s₀).take (min P.H.D P.Q)
  rw [hm]
  conv => lhs; rw [hsp']
  rw [VG.Proof.Hmac.Common.bytesAt_add, add_ofNat_add']
  congr 1
  · rw [fbytes hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj (.inl (by omega)) (by simp only [fX]; omega) (by simp only [fX]; omega)) (by omega), m₁₂,
      bytesAt_take _ _ (show P.Q - m ≤ 8 * 9 by omega), z₂, replicate_take _ _ _ (by omega)]
  · rw [hBOf, ← bytesAt_take _ _ hm3]
    apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at h₁ ⊢
    rw [hc i h₁, hsrc, m₁₂]
    rw [show dg s₀ + BitVec.ofNat 64 i = (dgR P s₀).base + BitVec.ofNat 64 i from rfl]
    rw [k₂.frame.bytes (R := dgR P s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.f_g.symm
      · exact hp.o_g.symm
      · exact hp.g_c
      · exact hp.b_g.symm) (by show P.H.D ≤ 2 ^ 64; omega)
        (by show i < P.H.D; have := bytesAt_length s₀.mem (dg s₀) m; omega)]

end

/-- Changes within the working space are changes within `scratch`. -/
theorem frame_of_unch {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  refine h x fun w hw => .inr ?_
  have := hW w hw
  simp only [Region.Contains] at hx'
  show w.1 + w.2 ≤ (x - base).toNat
  omega

/-- `loadQ`: the `Q` bytes at `p + off`, big-endian, to the slot at `o`, in
`nw` words. -/
theorem loadQ_ok (c : Cfg) (hQw : c.Q = 8 * c.nw ∨ (c.nw = 4 ∧ c.Q = 28) ∨ (c.nw = 4 ∧ c.Q = 24)) {s : State} {base : Addr} {o : Nat}
    {p : Reg} {off n : Nat} (hw : WsReg s base) (hp : p ∉ [Reg.t0, .t1]) (ho : o % 8 = 0)
    (ho' : o + 8 * c.nw ≤ 2048) (hoff : off + 8 * c.nw ≤ 2048)
    (hr : (⟨s.gpr p, n⟩ : Region) ∈ s.rd ++ s.wr) (hn : off + c.Q ≤ n) (hn' : n ≤ 8192)
    (hsep : ∀ i < c.Q, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr p + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (c.loadQ o p off)) s fun s' =>
      VG.Proof.X25519.RISCV64.Rest [.t0, .t1] s s' ∧ Outside base o (8 * c.nw) s.mem s'.mem ∧
      wordsVal s'.mem base o c.nw = Spec.Weierstrass.ofBytes (bytesAt s.mem (s.gpr p + BitVec.ofNat 64 off) c.Q) := by
  rcases hQw with h | ⟨h4, h28⟩ | ⟨h4, h24⟩
  · rw [Cfg.loadQ, ite_eq_left_of_eq_true _ _ (eq_true h), h]
    exact VG.Proof.Weierstrass.RISCV64.loadNum_ok c.nw hw hp ho (Nat.le_trans ho' (by decide)) hoff
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))
  · rw [Cfg.loadQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h4, h28]
    exact VG.Proof.Weierstrass.RISCV64.loadNum4_ok 3 hw hp ho (by omega) (by omega)
      (VG.Proof.Weierstrass.RISCV64.in_rd4 hr (by omega) hn')
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))
  · rw [Cfg.loadQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h4, h24]
    exact VG.Proof.Weierstrass.RISCV64.loadNum0_ok 3 hw hp ho (by omega) (by omega)
      (fun j hj => Proof.Ecdh.RISCV64.P256.in_rd8 hr (by omega) hn') (fun i hi => hsep i (by omega))

/-- `storeQ`: the `nw`-word number at `a` under the mask, to `q + off`
big-endian in `Q` bytes. -/
theorem storeQ_ok (c : Cfg) (hQw : c.Q = 8 * c.nw ∨ (c.nw = 4 ∧ c.Q = 28) ∨ (c.nw = 4 ∧ c.Q = 24)) (b : Bool) {s : State} {base : Addr}
    {a : Nat} {q : Reg} {off : Nat} (hw : WsReg s base) (hc : s.gpr .a7 = VG.Proof.Weierstrass.RISCV64.maskOf b)
    (hq : q ∉ [Reg.t0, .t1]) (ha : a % 8 = 0) (ha' : a + 8 * c.nw ≤ 2048) (hoff : off + 8 * c.nw ≤ 2048)
    (hout : ∀ i < c.Q, InRegions s.wr (s.gpr q + BitVec.ofNat 64 (off + i)) 1)
    (hsep : ∀ i < c.Q, ¬ (⟨base, 8192⟩ : Region).Contains (s.gpr q + BitVec.ofNat 64 (off + i)) 1) :
    WP isa (.block (c.storeQ a q off)) s fun s' =>
      VG.Proof.X25519.RISCV64.Rest [.t0, .t1] s s' ∧ s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr q + BitVec.ofNat 64 off)
        (Spec.Weierstrass.toBytes c.Q (if b then wordsVal s.mem base a c.nw else 0)) := by
  rcases hQw with h | ⟨h4, h28⟩ | ⟨h4, h24⟩
  · rw [Cfg.storeQ, ite_eq_left_of_eq_true _ _ (eq_true h), h]
    exact VG.Proof.Weierstrass.RISCV64.storeNum_ok b c.nw hw hc hq ha (Nat.le_trans ha' (by decide)) hoff
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))
  · rw [Cfg.storeQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true (by omega)), h4, h28]
    exact VG.Proof.Weierstrass.RISCV64.storeNum4_ok b 3 hw hc hq ha (by omega) (by omega)
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))
  · rw [Cfg.storeQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), h4, h24]
    exact VG.Proof.Weierstrass.RISCV64.storeNum_low_ok b 3 hw hc hq ha (by omega) (by omega)
      (fun i hi => hout i (by omega)) (fun i hi => hsep i (by omega))

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem ws_of {s : State} (h : KR P s₀ s) : WsReg s (scr s₀) :=
  ⟨h.s0, scr_wr hp h.wr, hp.nc, hp.ca⟩

/-- `KR` across code that writes only `scratch` and temporaries. -/
theorem KR.scr {s s' : State} (h : KR P s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hf : Frame [scrR s₀] s.mem s'.mem) :
    KR P s₀ s' :=
  h.keep hrd hwr hsp hg hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.f_c.sub_left (part_sub (by decide)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun x hx => hx⟩)


/-- `X`, apart from the working space. -/
theorem x_out {i : Nat} (hi : i < P.Q) :
    ¬ (⟨scr s₀, 8192⟩ : Region).Contains (s₀.sp + BitVec.ofNat 64 (fX + i)) 1 :=
  Proof.Ecdh.RISCV64.P256.out_of_disj (n := frB) hp.f_c (by have := hp.top; omega)
    (by have := (sizes P).Q; simp only [fX, frB]; omega)

omit hp in
/-- `X`'s number is the digest's integer, if the scalars' bytes are all
their number's. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      VG.Proof.Ecdsa.Rfc6979.hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega), List.take_of_length_le (by rw [hl]), VG.Proof.Ecdsa.Rfc6979.ofBytes_zeros,
      (VG.Proof.Ecdsa.Rfc6979.hashToInt_short (by rw [hl, hq]; omega) hn).1]

omit hp in
theorem n_ne (P : Rfc) : P.kit.E.curve.n ≠ 0 := fun h0 => by
  have := P.kit.nbits
  have := P.kit.sh8
  have := (sizes P).Q
  simp only [Spec.Ecdsa.nBits, h0, Nat.log2_zero] at *
  simp only [Rfc.Q] at *
  omega

/-- `h`, unless `big`: `X` reduced modulo `n`. -/
theorem reduce_ok (hwd : P.c.big = false) {s : State} (h : KR P s₀ s) (hx : xOfM P s₀ s.mem = xSpec P s₀) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ bytesAt t.mem (sA s₀ fH) P.Q = hSpec P s₀ ∧
      Frame [scrR s₀, sR s₀ fH P.Q] s.mem t.mem := by
  have hz := sizes P
  have hn := P.kit.nw9
  have hfr : frB = 512 := rfl
  have hQ64 : P.Q ≤ 64 := by
    have := hz.big.1; rw [hwd] at this; simp only [Bool.false_eq_true, false_iff, Nat.not_lt] at this; exact this
  have hQw : P.c.Q = 8 * P.c.nw ∨ (P.c.nw = 4 ∧ P.c.Q = 28) ∨ (P.c.nw = 4 ∧ P.c.Q = 24) := by
    rw [P.hQ, P.hnw]
    rcases P.kit.Qw with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · simp only [Rfc.Q] at hQ64; omega
  obtain ⟨hQ1, hQ2, hcQ, hQ3, hQ4, hQ5, hQ6⟩ := hz.Q
  have hw := ws_of hp h
  have hk := P.kit.FNk
  have hnb : Spec.Ecdsa.nBits P.kit.E.curve = 8 * P.Q := by
    have := P.kit.nbits; rw [P.hsh hwd] at this; simp only [Rfc.Q]; omega
  unfold Cfg.reduce
  rw [P.hFN]
  simp only [Cfg.sZ, Cfg.sY]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadQ_ok P.c hQw hw (o := sX) (p := .s1) (off := fX) (n := frB) (by decide)
    (by decide) (by simp only [sX, P.hnw]; omega) (by rw [P.hnw]; simp only [fX]; omega)
    (by rw [h.s1]; exact List.mem_append_right _ (by rw [h.wr, hp.wr]; simp))
    (by rw [hcQ]; simp only [fX]; omega) (by decide)
    (fun i hi => by rw [h.s1]; exact x_out hp (by rw [hcQ] at hi; exact hi))) fun s₁ ⟨r₁, O₁, e₁⟩ => ?_
  simp only [P.hnw, hcQ] at O₁ e₁
  rw [P.hnw]
  have hw₁ := hw.of_rest r₁
  refine WP.mono (VG.Proof.Weierstrass.RISCV64.setConst_ok P.kit.nw hw₁ (o := 8 * P.kit.nw) (x := 0) (by omega)
    (by omega)) fun s₂ ⟨r₂, O₂, e₂⟩ => ?_
  have hw₂ := hw₁.of_rest r₂
  have x₂ : wordsVal s₂.mem (scr s₀) sX P.kit.nw = eOf P s₀ := by
    rw [O₂.unch.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; simp only [sX]; omega)
      (by simp only [sX]; omega), e₁, h.s1]
    have := congrArg Spec.Weierstrass.ofBytes hx
    simp only [xOfM, sA] at this
    rw [this, x_eq hnb (n_ne P) (bytesAt_length _ _ _)]
  have hx' : eOf P s₀ < 2 ^ (8 * P.kit.Q) := by
    show Spec.Ecdsa.hashToInt _ (hBOf P s₀) < _
    rw [← x_eq hnb (n_ne P) (bytesAt_length _ _ _)]
    have := VG.Proof.Ecdsa.Rfc6979.ofBytes_lt (xSpec P s₀)
    have e : (xSpec P s₀).length = P.kit.Q := by
      simp only [xSpec, List.length_append, List.length_replicate, List.length_take, bytesAt_length, Rfc.Q]; omega
    rwa [e] at this
  have hown : 4096 - 64 * P.kit.nw ≤ VG.Proof.Weierstrass.RISCV64.own P.kit.nw ∧
      VG.Proof.Weierstrass.RISCV64.own P.kit.nw + 64 * P.kit.nw ≤ 8192 := by
    rcases VG.Proof.Weierstrass.RISCV64.rvOwn_cases P.kit.nw with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
      rw [show VG.Proof.Weierstrass.RISCV64.own P.kit.nw = VG.Proof.Weierstrass.RISCV64.rvOwn P.kit.nw from rfl, h] <;>
      omega
  have two := P.kit.two (P.hsh hwd)
  rw [← P.kit.FNm] at two
  refine WP.seq (WP.mono (addCall_ok P.kit.FNok hw₂ (o := 2 * (8 * P.kit.nw)) (a := sX) (b := 8 * P.kit.nw)
    (by rw [hk]; omega) (by rw [hk]; simp only [sX]; omega) (by rw [hk]; omega)
    (by omega) (by simp only [sX]; omega) (by omega)
    (by
      rw [hk, x₂, e₂]
      simp only [Nat.zero_mod, Nat.add_zero]; omega)) fun s₃ ⟨C₃, v₃⟩ => ?_)
  rw [hk] at C₃ v₃
  have hw₃ := hw₂.of_kp C₃.kp
  refine VG.RISCV64.BE64.wp_li_int (imm := -1) (by decide) fun s₄ u₄ => ?_
  have a7 : s₄.gpr .a7 = VG.Proof.Weierstrass.RISCV64.maskOf true := by rw [u₄.gpr]; decide
  have hw₄ : WsReg s₄ (scr s₀) := ⟨by rw [u₄.other _ (by decide)]; exact hw₃.s0, by rw [u₄.wr]; exact hw₃.wr,
    hw₃.nowrap, hw₃.al⟩
  have g₄ : ∀ r ∈ kregs, s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r (by revert r; decide), C₃.kp.gpr r (kregs_pres r hr), r₂.gpr r (by revert r; decide),
      r₁.gpr r (by revert r; decide)]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, C₃.kp.rd, r₂.rd, r₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, C₃.kp.wr, r₂.wr, r₁.wr]
  have sp₄ : s₄.sp = s.sp := by rw [u₄.sp, C₃.kp.sp, r₂.sp, r₁.sp]
  have U₄ : Unch (scr s₀) ([(sX, 8 * P.kit.nw)] ++ [(8 * P.kit.nw, 8 * P.kit.nw)] ++
      [(2 * (8 * P.kit.nw), 8 * P.kit.nw), (VG.Proof.Weierstrass.RISCV64.own P.kit.nw, 64 * P.kit.nw)]) s.mem s₄.mem := by
    rw [u₄.mem]
    exact (O₁.unch.trans O₂.unch).trans C₃.mem
  have F₄ : Frame [scrR s₀] s.mem s₄.mem := frame_of_unch U₄ (by
    intro w hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> simp only [sX] <;> omega)
  have K₄ : KR P s₀ s₄ := KR.scr hp h rd₄ wr₄ sp₄ g₄ F₄
  have q₄ : s₄.gpr .s1 = s₀.sp := K₄.s1
  refine WP.mono (storeQ_ok P.c hQw true hw₄ a7 (q := .s1) (a := 2 * (8 * P.kit.nw))
    (off := fH) (by decide) (by omega) (by rw [P.hnw]; omega) (by rw [P.hnw]; simp only [fH]; omega)
    (fun i hi => by rw [q₄]; exact in_fr hp K₄.wr (o := fH + i) (n := 1) (by rw [hcQ] at hi; simp only [fH]; omega))
    (fun i hi => by
      rw [q₄]
      refine Proof.Ecdh.RISCV64.P256.out_of_disj (n := frB) hp.f_c (by have := hp.top; omega)
        (by rw [hcQ] at hi; simp only [fH]; omega))) fun s₅ ⟨r₅, m₅⟩ => ?_
  rw [P.hnw, hcQ] at m₅
  have v₄ : wordsVal s₄.mem (scr s₀) (2 * (8 * P.kit.nw)) P.kit.nw = eOf P s₀ % P.kit.E.curve.n := by
    rw [u₄.mem, v₃, x₂, e₂, P.kit.FNm]
    simp only [Nat.zero_mod, Nat.add_zero]
  have F₅ : Frame [sR s₀ fH P.Q] s₄.mem s₅.mem := by
    rw [m₅, q₄]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Weierstrass.length_toBytes]; exact Region.contains_self _ _)
  refine ⟨K₄.keep r₅.rd r₅.wr r₅.sp (fun r hr => r₅.gpr r (by revert r; decide)) F₅
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fH]; omega)) (by decide) (by simp only [fH]; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by simp only [fH]; omega)⟩), ?_, ?_⟩
  · simp only [m₅, q₄, ↓reduceIte, v₄]
    have e := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s₄.mem (sA s₀ fH)
      (Spec.Weierstrass.toBytes P.Q (eOf P s₀ % P.kit.E.curve.n))
      (by rw [VG.Proof.Weierstrass.length_toBytes]; omega)
    rw [VG.Proof.Weierstrass.length_toBytes] at e
    show bytesAt _ (s₀.sp + BitVec.ofNat 64 fH) P.Q = _
    rw [e, hSpec, Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int,
      VG.Proof.Ecdsa.Rfc6979.rlenQ hnb]
  · refine (F₄.sub fun r hr => ?_).trans (F₅.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun x hx => hx⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s₀ fH P.Q, by simp, fun x hx => hx⟩

/-- `h`: `reduce`, or, if `big`, `X` itself, which is `bits2octets` of the
digest. -/
theorem prepH_ok {s : State} (h : KR P s₀ s) (hx : xOfM P s₀ s.mem = xSpec P s₀) :
    WP isa P.c.prepH s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ ∧ xOfM P s₀ t.mem = xSpec P s₀ ∧
      Frame [scrR s₀, sR s₀ fH 64] s.mem t.mem := by
  have hz := sizes P
  have hfr : frB = 512 := rfl
  unfold Cfg.prepH hOf Cfg.fHo
  cases hb : P.c.big
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hQ64 : P.Q ≤ 64 := by
      have := hz.big.1; rw [hb] at this; simp only [Bool.false_eq_true, false_iff, Nat.not_lt] at this; exact this
    refine WP.mono (reduce_ok hp hb h hx) fun t ⟨k, e, f⟩ => ⟨k, e, ?_, f.sub fun r hr => ?_⟩
    · rw [← hx]
      exact fbytes f (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.f_c.sub_left (part_sub (by simp only [fX]; have := hz.Q; omega))
        · exact part_disj (.inl (by simp only [fX, fH]; omega)) (by simp only [fX]; omega) (by simp only [fH]; omega))
        (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun x hx => hx⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (Nat.le_refl _) (by omega)⟩
  · simp only [↓reduceIte]
    refine WP.block_nil ⟨h, ?_, hx, Frame.refl _ _⟩
    have hQ := hz.big.1.mp hb
    obtain ⟨hD0, hD64⟩ := hz.D
    have hnb : Spec.Ecdsa.nBits P.kit.E.curve + P.kit.sh = 8 * P.Q := P.kit.nbits
    have hsh := P.kit.sh8
    show bytesAt s.mem (sA s₀ fX) P.Q = _
    rw [show bytesAt s.mem (sA s₀ fX) P.Q = xOfM P s₀ s.mem from rfl, hx, hSpec,
      VG.Proof.Ecdsa.Rfc6979.bits2octets_short (R := P.Q) (by omega) (by omega)
        (by rw [bytesAt_length]; omega) (n_ne P), bytesAt_length]
    show List.replicate (P.Q - min P.H.D P.Q) 0 ++ (hBOf P s₀).take (min P.H.D P.Q) = _
    rw [Nat.min_eq_left (by omega), List.take_of_length_le (by rw [bytesAt_length])]

end


/-! ## Steps b–g and h.3 -/

/-- `KR`, with `K`, `V`, `h` and `X`. -/
structure KVH (P : Rfc) (s₀ : State) (K V : List Byte) (t : State) : Prop where
  kr : KR P s₀ t
  k : kOf P s₀ t.mem = K
  v : vOf P s₀ t.mem = V
  h : hOf P s₀ t.mem = hSpec P s₀
  x : xOfM P s₀ t.mem = xSpec P s₀

theorem fHo_cases (P : Rfc) : P.c.fHo = fX ∨ P.c.fHo = fH := by
  unfold Cfg.fHo; split <;> simp

/-- `h` lies between `K`, `V` and `T`. -/
theorem fHo_in (P : Rfc) : fX ≤ P.c.fHo ∧ P.c.fHo + P.Q ≤ fT := by
  have hz := sizes P
  unfold Cfg.fHo
  cases hb : P.c.big
  · have := hz.big.1; rw [hb] at this; simp only [Bool.false_eq_true, false_iff, Nat.not_lt] at this
    simp only [Bool.false_eq_true, ↓reduceIte, fX, fH, fT]; omega
  · have := hz.Q; simp only [↓reduceIte, fX, fT]; omega

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- A part of the frame apart from what an HMAC writes, the MAC at `dst` but. -/
theorem hd_apart {o n dst : Nat} (h : o + n ≤ frB) (hd : o + n ≤ dst ∨ dst + P.H.D ≤ o) (hdst : dst + P.H.D ≤ frB) :
    ∀ r ∈ [stR s₀, sR s₀ dst P.H.D, stk P s₀], Region.Disjoint (sR s₀ o n) r := by
  have : frB = 512 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact fr_st hp h (fun x hx => hx)
  · exact part_disj hd (by omega) (by omega)
  · exact (f_s hp).sub_left (part_sub h)

/-- What an HMAC to `dst` in `K` or `V`'s place keeps of `KVH`: `X` and `h`,
and the other of `K` and `V`. -/
theorem hd_keep {s t : State} {msg : List Byte} {dst : Nat} (hdst : dst = fK ∨ dst = fV)
    (h : HD P s₀ s msg dst t) (hh : hOf P s₀ s.mem = hSpec P s₀) (hx : xOfM P s₀ s.mem = xSpec P s₀) :
    hOf P s₀ t.mem = hSpec P s₀ ∧ xOfM P s₀ t.mem = xSpec P s₀ ∧
      (dst = fV → kOf P s₀ t.mem = kOf P s₀ s.mem) ∧ (dst = fK → vOf P s₀ t.mem = vOf P s₀ s.mem) := by
  have hz := sizes P
  have hQ := hz.Q
  have hD := hz.D
  have hfr : frB = 512 := rfl
  have hdl : dst + P.H.D ≤ 232 := by rcases hdst with rfl | rfl <;> simp only [fK, fV] <;> omega
  have hdl' : 96 ≤ dst := by rcases hdst with rfl | rfl <;> simp only [fK, fV] <;> omega
  refine ⟨?_, ?_, fun e => ?_, fun e => ?_⟩
  · rw [← hh]
    exact fbytes h.2.2.1 (hd_apart hp (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega)
      (.inr (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega)) (by omega)) (by omega)
  · rw [← hx]
    exact fbytes h.2.2.1 (hd_apart hp (by simp only [fX]; omega) (.inr (by simp only [fX]; omega)) (by omega))
      (by omega)
  · subst e
    exact fbytes h.2.2.1 (hd_apart hp (by simp only [fK]; omega) (.inl (by simp only [fK, fV]; omega)) (by omega))
      (by omega)
  · subst e
    exact fbytes h.2.2.1 (hd_apart hp (by simp only [fV]; omega) (.inr (by simp only [fK, fV]; omega)) (by omega))
      (by omega)

omit hp in
theorem initKV_eq : Cfg.initKV = ([.li .t0 0x101, .shift .sll .d .t1 .t0 16, .logic .or .t0 .t0 .t1,
    .shift .sll .d .t1 .t0 32, .logic .or .t0 .t0 .t1, .li .t1 0] : List Instr) ++
    (((List.range 8).flatMap fun j => [(Reg.t1, fK + 8 * j), (Reg.t0, fV + 8 * j)]).map
      (fun q => .store .d q.1 .s1 q.2) ++ []) := rfl

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem initKV_ok {s : State} (h : KR P s₀ s) (hh : hOf P s₀ s.mem = hSpec P s₀)
    (hx : xOfM P s₀ s.mem = xSpec P s₀) :
    WP isa (.block Cfg.initKV) s (KVH P s₀ (List.replicate P.H.D 0) (List.replicate P.H.D 1)) := by
  have hz := sizes P
  have hQ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  rw [initKV_eq, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.nil_append]
  refine wp_li (imm := 0x101) (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_or fun s₃ u₃ =>
    wp_sll (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => ?_
  have k₆ : KR P s₀ s₆ :=
    (((((h.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd
      (by decide) u₆
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r0 : s₆.gpr .t0 = BitVec.ofNat 64 0x0101010101010101 := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      u₁.gpr]
    decide
  have r1 : s₆.gpr .t1 = 0 := by rw [u₆.gpr]; rfl
  refine sds_ok hp _ (fun q hq => by
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hq
      obtain ⟨j, hj, rfl | rfl⟩ := hq <;> simp only [fK, fV] <;> omega) (by decide) k₆
    fun t k₇ g₇ f₇ v₇ => WP.block_nil ?_
  have F : Frame [sR s₀ fK 128] s.mem t.mem := by
    rw [← m₆]
    refine f₇.sub fun r hr => ?_
    simp only [List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨q, ⟨j, hj, rfl | rfl⟩, rfl⟩ := hr
    · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by simp only [fK]; omega) (by simp only [fK]; omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by simp only [fK, fV]; omega) (by simp only [fK, fV]; omega)⟩
  have wK : ∀ j < 8, t.mem.readW (sA s₀ fK + BitVec.ofNat 64 (8 * j)) 64 = 0 := fun j hj => by
    rw [add_ofNat_add', v₇ (Reg.t1, fK + 8 * j) (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, by simp⟩), r1]
  have wV : ∀ j < 8, t.mem.readW (sA s₀ fV + BitVec.ofNat 64 (8 * j)) 64 = BitVec.ofNat 64 0x0101010101010101 :=
    fun j hj => by
      rw [add_ofNat_add', v₇ (Reg.t0, fV + 8 * j) (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, by simp⟩), r0]
  have bK := bytesAt_of_readW (k := 8) _ _ _ wK
  have bV := bytesAt_of_readW (k := 8) _ _ _ wV
  rw [show (List.range (8 * 8)).map (fun i => (0 : BitVec 64).extractLsb' (8 * (i % 8)) 8) =
    List.replicate 64 0 by decide] at bK
  rw [show (List.range (8 * 8)).map (fun i => (BitVec.ofNat 64 0x0101010101010101).extractLsb' (8 * (i % 8)) 8) =
    List.replicate 64 1 by decide] at bV
  refine ⟨k₇, ?_, ?_, ?_, ?_⟩
  · show bytesAt t.mem (sA s₀ fK) P.H.D = _
    rw [bytesAt_take _ _ (show P.H.D ≤ 8 * 8 by omega), bK, replicate_take _ _ _ (by omega)]
  · show bytesAt t.mem (sA s₀ fV) P.H.D = _
    rw [bytesAt_take _ _ (show P.H.D ≤ 8 * 8 by omega), bV, replicate_take _ _ _ (by omega)]
  · rw [← hh]
    exact fbytes F (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fK, fX, fH] <;> omega))
        (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega) (by simp only [fK]; omega))
      (by omega)
  · rw [← hx]
    exact fbytes F (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inr (by simp only [fK, fX]; omega)) (by simp only [fX]; omega) (by simp only [fK]; omega))
      (by omega)

/-- The separator `b` after `V`: the first part of the messages. -/
theorem sep_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) {b : Nat} (hb : b < 256) :
    WP isa (.block (Cfg.sep b)) s fun t => KVH P s₀ K V t ∧
      bytesAt t.mem (sA s₀ fV) (P.H.D + 1) = V ++ [BitVec.ofNat 8 b] ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r := by
  have hz := sizes P
  have hQ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.sep
  refine wp_add fun s₁ u₁ => wp_li (imm := b) (by omega) fun s₂ u₂ => ?_
  have a₂ : s₂.gpr .t0 + BitVec.ofNat 64 fV = sA s₀ (fV + P.H.D) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.kr.s1, h.kr.s7]
    show s₀.sp + _ + _ = s₀.sp + _
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
  refine wp_sb (by decide) a₂ (by
      rw [u₂.wr, u₁.wr]; exact in_fr hp h.kr.wr (by simp only [fV]; omega)) fun s₃ m₃ => WP.block_nil ?_
  have k₂ : KR P s₀ s₂ := (h.kr.upd (by decide) u₁).upd (by decide) u₂
  have F : Frame [sR s₀ (fV + P.H.D) 1] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : KR P s₀ s₃ := k₂.keep m₃.rd m₃.wr m₃.sp (fun r _ => by rw [m₃.gpr]) (by rw [u₂.mem, u₁.mem]; exact F)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by simp only [fV]; omega)) (by decide) (by simp only [fV]; omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, part_sub (by simp only [fV]; omega)⟩)
  have ap : ∀ {o n : Nat}, (o + n ≤ fV + P.H.D ∨ fV + P.H.D + 1 ≤ o) → o + n ≤ frB →
      ∀ r ∈ [sR s₀ (fV + P.H.D) 1], Region.Disjoint (sR s₀ o n) r := fun ho ho' r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact part_disj ho (by omega) (by simp only [fV]; omega)
  have hv : vOf P s₀ s₃.mem = V := by
    rw [← h.v]; exact fbytes F (ap (.inl (Nat.le_refl _)) (by simp only [fV]; omega)) (by omega)
  refine ⟨⟨k₃, ?_, hv, ?_, ?_⟩, ?_, fun r hr => ?_⟩
  · rw [← h.k]; exact fbytes F (ap (.inl (by simp only [fK, fV]; omega)) (by simp only [fK]; omega)) (by omega)
  · rw [← h.h]
    exact fbytes F (ap (.inr (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fV, fX, fH] <;> omega))
      (by rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega)) (by omega)
  · rw [← h.x]
    exact fbytes F (ap (.inr (by simp only [fV, fX]; omega)) (by simp only [fX]; omega)) (by omega)
  · rw [VG.Proof.Hmac.Common.bytesAt_add, show bytesAt s₃.mem (sA s₀ fV) P.H.D = V from hv, add_ofNat_add']
    simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
    rw [m₃.mem, u₂.mem, u₁.mem, WriteBytes.writeW8_apply,
      ite_eq_left (show s₀.sp + BitVec.ofNat 64 (fV + P.H.D) = sA s₀ (fV + P.H.D) from rfl), u₂.gpr]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · rw [m₃.gpr, u₂.other r (fun e => by subst e; exact absurd hr (by decide)),
      u₁.other r (fun e => by subst e; exact absurd hr (by decide))]

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) :
    WP isa P.c.hmacV s fun t => KVH P s₀ K (Spec.Hmac.hmac P.hH.SH.H K V) t ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ Frame [stR s₀, sR s₀ fV P.H.D, stk P s₀] s.mem t.mem := by
  have hz := sizes P
  have hQ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.hmacV
  refine WP.mono (hmac_ok hp h.kr hsy (ps := [(.s1, fV, (true, 0))]) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩)
    (by simp [OneD]) (by simp [total, tlen, lval, plen]) (by decide) (by decide)
    (by simp only [tlen, plen, lval]; simp; omega)
    (dst := fV) ⟨by decide, by simp only [fV]; omega⟩) fun t hd => ?_
  have hm : msgOf P s.mem s₀ [(.s1, fV, (true, 0))] = V := by
    simp only [msgOf, List.append_nil, plen, lval, ↓reduceIte, Nat.add_zero]; exact h.v
  obtain ⟨e₁, e₂, e₃, -⟩ := hd_keep hp (.inr rfl) hd h.h h.x
  refine ⟨⟨hd.1, ?_, ?_, e₁, e₂⟩, hd.2.2.2, hd.2.2.1⟩
  · rw [e₃ rfl, h.k]
  · show bytesAt t.mem (sA s₀ fV) P.H.D = _
    rw [hd.2.1, hm, h.k]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) {b : Nat}
    (hb : b < 256) :
    WP isa (P.c.rekeyFull b) s fun t =>
      let K' := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀))
      KVH P s₀ K' (Spec.Hmac.hmac P.hH.SH.H K' V) t := by
  have hz := sizes P
  have hQ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.rekeyFull
  rw [hz.Q.2.2.1]
  refine WP.seq (VG.RISCV64.WP.mono_syms (sep_ok hp h hb) fun s₁ ⟨h₁, m₁, _⟩ y₁ => ?_)
  have hfo : P.c.fHo + P.Q ≤ frB ∧ 96 ≤ P.c.fHo := by
    rcases fHo_cases P with e | e <;> rw [e] <;> simp only [fX, fH] <;> omega
  refine WP.seq (VG.RISCV64.WP.mono_syms (hmac_ok hp h₁.kr (y₁.trans hsy)
    (ps := [(.s1, fV, (true, 1)), (.s3, 0, (false, P.Q)), (.s1, P.c.fHo, (false, P.Q))])
    (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      · exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩
      · exact ⟨.inr ⟨rfl, rfl, by simp [plen, lval]⟩, by show P.Q < 2048; omega⟩
      · exact ⟨.inl ⟨rfl, hfo.2, by simp [plen, lval]; omega⟩, by show P.Q < 2048; omega⟩)
    (by simp [OneD]) (by simp [total, tlen, lval, plen]; omega) (by simp [total]; omega) (by simp; omega)
    (by simp only [tlen, plen, lval]; simp; omega)
    (dst := fK) ⟨by decide, by simp only [fK]; omega⟩) fun t hd y₂ => ?_)
  have hm : msgOf P s₁.mem s₀ [(.s1, fV, (true, 1)), (.s3, 0, (false, P.Q)), (.s1, P.c.fHo, (false, P.Q))] =
      V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀) := by
    simp only [msgOf, List.append_nil, pA, regV, plen, lval, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    rw [m₁, BitVec.add_zero, h₁.kr.dBytes hp]
    have hh := h₁.h
    simp only [hOf] at hh
    rw [hh]
    simp
  obtain ⟨e₁, e₂, -, e₄⟩ := hd_keep hp (.inl rfl) hd h₁.h h₁.x
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ BitVec.ofNat 8 b :: (dB P s₀ ++ hSpec P s₀)))
    (V := V) ⟨hd.1, ?_, ?_, e₁, e₂⟩ (y₂.trans (y₁.trans hsy))) fun u hu => hu.1
  · show bytesAt t.mem (sA s₀ fK) P.H.D = _
    rw [hd.2.1, hm, h₁.k]
  · rw [e₄ rfl, h₁.v]

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok {s : State} {K V : List Byte} (h : KVH P s₀ K V s) (hsy : s.syms = s₀.syms) :
    WP isa P.c.rekey s (fun t => KVH P s₀ (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).1
      (Spec.Ecdsa.Rfc6979.next P.hH.SH.H K V).2 t ∧ ∀ r ∈ preserved, t.gpr r = s.gpr r) := by
  have hz := sizes P
  have hQ := hz.Q
  obtain ⟨hD0, hD⟩ := hz.D
  have hfr : frB = 512 := rfl
  unfold Cfg.rekey
  refine WP.seq (VG.RISCV64.WP.mono_syms (sep_ok hp h (b := 0) (by decide)) fun s₁ ⟨h₁, m₁, pr₁⟩ y₁ => ?_)
  refine WP.seq (VG.RISCV64.WP.mono_syms (hmac_ok hp h₁.kr (y₁.trans hsy) (ps := [(.s1, fV, (true, 1))])
    (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact ⟨.inl ⟨rfl, by simp only [fV]; omega, by simp only [fV, plen, lval]; simp; omega⟩, by decide⟩)
    (by simp [OneD]) (by simp [total, tlen, lval, plen]) (by decide) (by decide)
    (by simp only [tlen, plen, lval]; simp; omega)
    (dst := fK) ⟨by decide, by simp only [fK]; omega⟩) fun t hd y₂ => ?_)
  obtain ⟨e₁, e₂, -, e₄⟩ := hd_keep hp (.inl rfl) hd h₁.h h₁.x
  refine WP.mono (hmacV_ok hp (K := Spec.Hmac.hmac P.hH.SH.H K (V ++ [0])) (V := V) ⟨hd.1, ?_, ?_, e₁, e₂⟩
    (y₂.trans (y₁.trans hsy)))
    fun u hu => ⟨hu.1, fun r hr => (hu.2.1 r hr).trans ((hd.2.2.2 r hr).trans (pr₁ r hr))⟩
  · show bytesAt t.mem (sA s₀ fK) P.H.D = _
    rw [hd.2.1]
    simp only [msgOf, List.append_nil, pA, regV, plen, lval, ↓reduceIte]
    rw [m₁, h₁.k]
    rfl
  · rw [e₄ rfl, h₁.v]

end

end VG.Proof.Ecdsa.Rfc6979.RISCV64
