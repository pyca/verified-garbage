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
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_add wp_sub wp_ld wp_sd wp_sb wp_srl wp_sll wp_addSp)
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
    [.li .t1 P.c.Q, .sub .t2 .s7 .t1, .shift .srl .d .t3 .t2 63, .li .t4 0, .sub .t3 .t4 .t3,
      .logic .and .t2 .t2 .t3, .add .a6 .t1 .t2, mov .a4 .s4, .addi .a5 .s1 (fX + P.c.Q), .sub .a5 .a5 .a6]) := by
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

end VG.Proof.Ecdsa.Rfc6979.RISCV64
