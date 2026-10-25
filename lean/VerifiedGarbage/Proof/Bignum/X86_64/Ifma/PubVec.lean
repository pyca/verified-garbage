module
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Spec

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Conv
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-!
# The public operation with AVX512_IFMA on x86-64: the numbers of the vector code

The one-lane layouts (`PubOk`) and their area from `rbx` (`PubIfma.oA`,
`oB`, `oMx`); `B := 2^kb` (`pow2_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma.Pub

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Impl.Rsa.X86_64.PubIfma
open VG.Proof.Bignum.X86_64.Ifma
open VG.Proof.Bignum.X86_64.AmmSym (stMem stMem_outside word_stMem limbN se_ofNat)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq hdrOff)
open VG.Impl.Bignum (sArr)
open VG.Impl.Bignum.Public (aX)
open VG.Impl.Bignum.X86_64 (hdr)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The public operation's layouts. -/
def PubOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prop := l = pay2048 ∨ l = pay3072 ∨ l = pay4096

theorem PubOk.amm (hl : PubOk l) : AmmOk l := .inr hl

theorem PubOk.nl (hl : PubOk l) : l.nl = 1 := by rcases hl with rfl | rfl | rfl <;> rfl

/-- The area: the modulus and `k₀` before `A`, then `A`, `B` and the MXCSR
slots within six arrays of `W + 2` words; `2^kb` one limb; the radix
`R' = 2^(52 S)` with `S = L`, above `4 n` for `n` below `2^(64 W)`. -/
theorem PubOk.area (hl : PubOk l) :
    l.NB + 32 ≤ oA l ∧ oB l = oA l + l.NB ∧ oMx l = oB l + l.NB ∧ oMx l + 8 ≤ 48 * (l.W + 2) ∧
      kb l / 52 < l.L ∧ kb l ≤ 256 ∧ l.S = l.L ∧ 64 * l.W + 2 ≤ 52 * l.S ∧ 64 ≤ 64 * l.W ∧
      208 * l.L = 256 * l.W + kb l ∧ l.L = 4 * l.R ∧ l.W < 2 ^ 20 := by
  rcases hl with rfl | rfl | rfl <;> decide

/-! ## `B := 2^kb` -/

theorem stR11_ok {C : Addr} {v : BitVec 64} :
    ∀ (ds : List Nat) (s : State), s.gpr .r11 = C → s.gpr .rax = v →
      (∀ d ∈ ds, InRegions s.wr (C + BitVec.ofNat 64 d) 8) →
      WP isa (.block (ds.map fun d => .store (at_ .r11 d) .rax)) s
        fun s' => s' = { s with mem := stMem s.mem C v ds }
  | [], s, _, _, _ => WP.block_nil rfl
  | d :: rest, s, hC, hv, hw => by
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off C d) v }, ?_, ?_⟩
    · simp only [exec, eaG', hC, hv, State.store64, hw d (List.mem_cons_self ..), ite_true, off]
    · exact WP.mono (stR11_ok rest _ hC hv fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => h

theorem map_store' (f : Nat → Nat) (xs : List Nat) :
    xs.map (fun x => Instr.store (at_ .r11 (f x)) .rax) = (xs.map f).map (fun d => .store (at_ .r11 d) .rax) := by
  simp only [List.map_map, Function.comp_def]

/-- The limbs of `2^kb`: `2^(kb % 52)` at limb `kb / 52`, zero elsewhere. -/
theorem limbN_pow2 (k j : Nat) : limbN (2 ^ k) j = if j = k / 52 then 2 ^ (k % 52) else 0 := by
  unfold limbN
  have hk : 2 ^ k = 2 ^ (k % 52) * 2 ^ (52 * (k / 52)) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  have hlt : 2 ^ (k % 52) < 2 ^ 52 := Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ (by decide))
  split
  · rename_i h; subst h
    rw [hk, Nat.mul_div_cancel _ (Nat.pow_pos (by decide)), Nat.mod_eq_of_lt hlt]
  · rename_i h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · -- `j < k / 52`: the limb is a whole multiple of `2^52`.
      obtain ⟨d, hd⟩ : ∃ d, k / 52 = j + 1 + d := ⟨k / 52 - j - 1, by omega_arith⟩
      rw [hk, hd, show 52 * (j + 1 + d) = 52 * j + 52 * (1 + d) by omega_arith, Nat.pow_add,
        ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ (52 * j)), Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide)), Nat.pow_mul, Nat.pow_add, Nat.pow_one,
        ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 52), Nat.mul_assoc, Nat.mul_mod_right]
    · -- `j > k / 52`: the value is below `2^(52 j)`.
      rw [Nat.div_eq_of_lt]
      calc 2 ^ k < 2 ^ (52 * j) := Nat.pow_lt_pow_right (by decide) (by omega_arith)

/-- `B := 2^kb`, through `r11 = rbx`. -/
theorem pow2_ok (hl : PubOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B)
    (hw : ∀ j < l.L, InRegions s.wr (B + BitVec.ofNat 64 (oB l + l.off j)) 8) (hn : (oB l + l.NB) < 2 ^ 31) :
    WP isa (.block (pow2 l)) s fun s' =>
      (∀ j < l.L, word s'.mem B (oB l + l.off j) = BitVec.ofNat 64 (limbN (2 ^ kb l) j)) ∧
      Outside B (oB l) l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  have hA := hl.amm
  unfold pow2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r11, .rax] (Q := fun t =>
    t.gpr .r11 = B ∧ t.gpr .rax = 0 ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      xrun [hB]
      all_goals rfl) rfl) fun t ⟨⟨h11, h0, hm, hx⟩, kt⟩ => ?_
  rw [WP.block_append_iff, map_store' (fun j => oB l + l.off j)]
  refine WP.mono (stR11_ok _ _ h11 h0 fun d hd => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    rw [kt.2.2]; exact hw j (List.mem_range.mp hj)) fun u hu => ?_
  subst hu
  have hj0 : kb l / 52 < l.L := a5
  have hlast : InRegions t.wr (B + BitVec.ofNat 64 (oB l + l.off (kb l / 52))) 8 := by
    rw [kt.2.2]; exact hw _ hj0
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun u' =>
    u'.mem = (stMem t.mem B 0 ((List.range l.L).map fun j => oB l + l.off j)).writeW
      (off B (oB l + l.off (kb l / 52))) (BitVec.ofNat 64 (2 ^ (kb l % 52))) ∧ u'.mxcsr = t.mxcsr) (by
      xrun [eaG', h11, hlast]
      all_goals rfl) rfl) fun s' ⟨⟨me, mx⟩, k⟩ => ?_
  have hF' : ∀ j < l.L, oB l + l.off j + 8 ≤ oB l + l.NB := fun j hj => by
    have := off_ltN hA hj; omega_arith
  refine ⟨fun j hj => ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, by rw [mx, hx]⟩
  · rw [me, limbN_pow2]
    by_cases e : j = kb l / 52
    · subst e; simp only [↓reduceIte]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · simp only [e, ↓reduceIte]
      have hk := hF' _ hj0
      have hjj := hF' j hj
      have hs := off_sepN hA hj0 hj e
      rw [(writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by have := hF' j hj; omega_arith),
        word_stMem _ _ _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          rw [List.mem_range] at hj'
          by_cases e' : j' = j
          · exact .inl (by rw [e'])
          · exact .inr (by have := off_sepN hA hj hj' e'; omega_arith))
        (fun d hd => by
          obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
          have := hF' j' (List.mem_range.mp hj'); omega_arith)]
      rfl
  · have hk := hF' _ hj0
    rw [me, ← hm]
    exact (stMem_outside _ B 0 (by omega_arith) _ fun d hd => by
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
      have := hF' j' (List.mem_range.mp hj'); omega_arith).trans
      ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by have := hF' _ hj0; omega_arith))
  · rw [k.gpr (fun h => hr (by simp only [List.mem_singleton] at h; simp [h]))]; exact kt.gpr hr
  · rw [k.2.1]; exact kt.2.1
  · rw [k.2.2]; exact kt.2.2

/-! ## One multiplication -/

/-- The modulus' limbs at 0 and `k₀` at `oK0`, for `M` below `R' / 4`. -/
structure Mod (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k : Nat) : Prop where
  lt : ∀ j < l.L, limb l m B 0 j < 2 ^ 52
  val : val52 l m B 0 = M
  k0 : ∀ t < 4, word m B (l.oK0 + 8 * t) = BitVec.ofNat 64 k
  klt : k < 2 ^ 52
  inv : (limb l m B 0 0 * k + 1) % 2 ^ 52 = 0
  big : 4 * M ≤ 2 ^ (52 * l.S)

/-- `Mod` through writes from `oA` on. -/
theorem Mod.of_outside (hl : PubOk l) {m m' : Mem} {B : Addr} {M k n : Nat} (h : Mod l m B M k)
    (f : Outside B (oA l) n m m') (hn : oA l + n ≤ 2 ^ 63) : Mod l m' B M k := by
  obtain ⟨a1, -⟩ := hl.area
  have hlimb : ∀ j < l.L, limb l m' B 0 j = limb l m B 0 j := fun j hj => by
    have := off_ltN hl.amm hj
    simp only [limb, Nat.zero_add]
    rw [f.word (by omega_arith) (by omega_arith)]
  refine ⟨fun j hj => (hlimb j hj) ▸ h.lt j hj, ?_, fun t ht => ?_, h.klt,
    by rw [hlimb 0 (by simp only [Lay.L]; have := hl.amm.bounds.1; omega_arith)]; exact h.inv, h.big⟩
  · rw [← h.val]; exact lval_congr hlimb
  · rw [f.word (by simp only [Lay.oK0]; omega_arith) (by simp only [Lay.oK0]; omega_arith)]; exact h.k0 t ht

theorem OutN.one (hl : PubOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : OutN l B o n m m') :
    Outside B o n m m' := fun x hx => h x fun p hp => by
  rw [hl.nl] at hp
  obtain rfl : p = 0 := by omega_arith
  simpa only [Nat.mul_zero, Nat.zero_add] using hx

/-- `ammMul` with `r8`, `r9` at offsets `a`, `b` of `B = rbx`, into `A`. -/
theorem core_ok (hl : PubOk l) {s : State} {B : Addr} {M k a b : Nat} (hB : s.gpr .rbx = B)
    (r8 : s.gpr .r8 = off B a) (r9 : s.gpr .r9 = off B b) (r11 : s.gpr .r11 = off B (oA l))
    (hs : Scr s B (48 * (l.W + 2))) (hm : Mod l s.mem B M k)
    (ha : a + l.NB ≤ 48 * (l.W + 2)) (hb : b + l.NB ≤ 48 * (l.W + 2))
    (hla : ∀ j < l.L, limb l s.mem B a j < 2 ^ 52) (hlb : ∀ j < l.L, limb l s.mem B b j < 2 ^ 52) :
    WP isa (ammMul l) s fun s' =>
      (∀ j < l.L, limb l s'.mem B (oA l) j < 2 ^ 52) ∧
      (val52 l s.mem B a < 2 * M → val52 l s.mem B b < 2 * M →
        val52 l s'.mem B (oA l) < 2 * M ∧
        val52 l s'.mem B (oA l) * 2 ^ (52 * l.S) % M = val52 l s.mem B a * val52 l s.mem B b % M) ∧
      Outside B (oA l) l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨a1, a2, a3, a4, -, -, a7, -, a9, -, -, a12⟩ := hl.area
  have hn := hl.nl
  have hp : ∀ p < l.nl, p = 0 := fun p hp => by omega_arith
  have h0 : ∀ c, l.D * 0 + c = c := fun c => by rw [Nat.mul_zero, Nat.zero_add]
  have hM : val52 l s.mem B oM = M := hm.val
  refine WP.mono (ammCoreSpecN_ok hl.amm (ammMul_core hl.amm) (Z := 48 * (l.W + 2)) (k := fun _ => k) hB r8 r9 r11 hs
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith) (by omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (fun p hp' j hj => by obtain rfl := hp p hp'; rw [h0, h0, h0]; exact ⟨hla j hj, hlb j hj, hm.lt j hj⟩)
    (fun p hp' t ht => by obtain rfl := hp p hp'; rw [h0]; exact hm.k0 t ht) (fun _ _ => hm.klt)
    (fun p hp' => by obtain rfl := hp p hp'; rw [h0]; exact hm.inv))
    fun s' ⟨hv, hf, hg, h12, hrd, hwr, hx⟩ => ?_
  have v := hv 0 (by omega_arith)
  simp only [h0, hM] at v
  exact ⟨v.1, fun hA hB' => v.2 hA hB' hm.big, OutN.one hl hf, hg, h12, hrd, hwr, hx⟩

/-- `ammMul`'s operands. -/
theorem setOps_ok {s : State} {B : Addr} {o a b : Nat} (hB : s.gpr .rbx = B) (ho : o < 2 ^ 31) (ha : a < 2 ^ 31)
    (hb : b < 2 ^ 31) :
    WP isa (.block (setOps o a b)) s fun s' =>
      s'.gpr .r8 = off B a ∧ s'.gpr .r9 = off B b ∧ s'.gpr .r11 = off B o ∧
      VG.Proof.MlKem.X86_64.Keep [.r8, .r9, .r11] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8, .r9, .r11] (Q := fun s' =>
    s'.gpr .r8 = off B a ∧ s'.gpr .r9 = off B b ∧ s'.gpr .r11 = off B o ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr) (by
    unfold setOps
    xrun [hB, se_ofNat ho, se_ofNat ha, se_ofNat hb]
    all_goals rfl) rfl) fun s' ⟨⟨h8, h9, h11, m, x⟩, k⟩ => ⟨h8, h9, h11, k, m, x⟩

/-- The counter. -/
theorem inc_ok {s : State} {c : Nat} (hc : c < 20) (h13 : s.gpr .r13 = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm 20)]) s fun s' =>
      s'.gpr .r13 = BitVec.ofNat 64 (c + 1) ∧ s'.zf = some (decide (c + 1 = 20)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun s' =>
    s'.gpr .r13 = BitVec.ofNat 64 (c + 1) ∧ s'.zf = some (decide (c + 1 = 20)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h13, (by decide : BitVec.signExtend 64 (20 : BitVec 32) = BitVec.ofNat 64 20), ofNat_add_one]
    and_intros
    · rw [ofNat_sub_beq (by omega_arith) (by decide)]
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- `ld52 j o`: array `j`'s `W` words, at `rdi + arr j`, into the limbs at `B + o`. -/
theorem ld52_ok (hl : PubOk l) {s : State} {B H : Addr} {j o : Nat} (hB : s.gpr .rbx = B) (hdi : s.gpr .rdi = H)
    (h12 : s.gpr .r12 = mask52) (hj : arr l j < 2 ^ 31)
    (hrd : ∀ i < l.W, InRegions (s.rd ++ s.wr) (off H (arr l j) + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : ∀ q < l.L, InRegions s.wr (off B (o + l.off q)) 8) (ho : o + l.NB < 2 ^ 31)
    (hsep : ∀ m m' : Mem, Outside B o l.NB m m' → ∀ i < l.W,
      word m' (off H (arr l j)) (8 * i) = word m (off H (arr l j)) (8 * i)) :
    WP isa (.block (ld52 l j o)) s fun s' =>
      (∀ q < l.L, word s'.mem B (o + l.off q) = BitVec.ofNat 64 (limbN (wv s.mem (off H (arr l j)) 0 l.W) q)) ∧
      Outside B o l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rsi, .r11, .rax, .rcx, .rbp] s s' ∧
      s'.mxcsr = s.mxcsr := by
  unfold ld52 base
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rsi, .r11] (Q := fun t =>
    t.gpr .rsi = off H (arr l j) ∧ t.gpr .r11 = off B o ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
      simp only [List.cons_append, List.nil_append]
      xrun [hdi, hB, se_ofNat hj, se_ofNat (show o < 2 ^ 31 by omega_arith)]
      all_goals rfl) rfl) fun t ⟨⟨hsi, h11, hm, hx⟩, kt⟩ => ?_
  refine WP.mono (to52_ok hl.amm hsi h11 ((kt.gpr (by decide)).trans h12)
    (fun i hi => by rw [kt.2.1, kt.2.2]; exact hrd i hi)
    (fun q hq => by rw [kt.2.2, AmmSym.off_add]; exact hwr q hq)
    (fun m m' f => hsep m m' (AmmSym.Outside.rebase f (by omega_arith) (by omega_arith))))
    fun u ⟨v, f, k, x⟩ => ⟨fun q hq => by rw [← VG.Proof.Bignum.word_off, v q hq, hm], ?_,
      (kt.trans k).mono (by decide), x.trans hx⟩
  rw [← hm]; exact AmmSym.Outside.rebase f (by omega_arith) (by omega_arith)

/-! ## The loop -/

/-- What holds through the loop, from its start `t₀`: the area at `B`, the
header at `H` and the input's words at `X`, apart from `A` and `B`. -/
structure Env (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B H X : Addr) (M k : Nat) : Prop where
  scr : Scr t₀ B (48 * (l.W + 2))
  md : Mod l t₀.mem B M k
  odd : M % 2 = 1
  big : 2 ^ kb l < 2 * M
  hX : X = off H (arr l aX)
  hx : arr l aX < 2 ^ 31
  hrd : ∀ i < l.W, InRegions (t₀.rd ++ t₀.wr) (X + BitVec.ofNat 64 (8 * i)) 8
  sepX : ∀ m m' : Mem, Outside B (oA l) (2 * l.NB + 8) m m' → ∀ i < l.W, word m' X (8 * i) = word m X (8 * i)

/-- `A`'s value after multiplication `c`, modulo `M`: `R0 = R² mod m` at the
start (`R = 2^(64 W)`), and from multiplication 3 on, when `R0` is that,
`x^(2^(c-3)) R'` and finally `x^(2^16) x`. -/
def VA (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (M R0 x : Nat) : Nat → Nat → Prop
  | 0, A => A % M = R0 % M
  | 1, A => A * 2 ^ (52 * l.S) % M = R0 * R0 % M
  | 2, A => A * 2 ^ (52 * l.S) * 2 ^ (52 * l.S) % M = R0 * R0 * 2 ^ kb l % M
  | c + 3, A => R0 % M = 2 ^ (64 * l.W) * 2 ^ (64 * l.W) % M →
      A % M = (if c + 3 = 20 then x ^ 2 ^ 16 * x else x ^ 2 ^ c * 2 ^ (52 * l.S)) % M

/-- The loop's invariant before multiplication `c`. -/
structure Inv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (t₀ : State) (B H X : Addr) (M R0 : Nat) (c : Nat) (t : State) :
    Prop where
  rbx : t.gpr .rbx = B
  rdi : t.gpr .rdi = H
  r12 : t.gpr .r12 = mask52
  r13 : t.gpr .r13 = BitVec.ofNat 64 c
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13] t₀ t
  mx : t.mxcsr = t₀.mxcsr
  frame : Outside B (oA l) (2 * l.NB) t₀.mem t.mem
  a : ∀ j < l.L, limb l t.mem B (oA l) j < 2 ^ 52
  b : 3 ≤ c → ∀ j < l.L, word t.mem B (oB l + l.off j) = BitVec.ofNat 64 (limbN (wv t₀.mem X 0 l.W) j)
  v : wv t₀.mem X 0 l.W < M → val52 l t.mem B (oA l) < 2 * M ∧
    VA l M R0 (wv t₀.mem X 0 l.W) c (val52 l t.mem B (oA l))

/-- `cmp r13, n`. -/
theorem cmp_ok {t : State} {c n : Nat} (hc : c < 2 ^ 31) (hn : n < 2 ^ 31) (h13 : t.gpr .r13 = BitVec.ofNat 64 c) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 n))]) t fun t' =>
      t'.zf = some (decide (c = n)) ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mem = t.mem ∧
        t'.mxcsr = t.mxcsr := by
  xrun [h13, se_ofNat hn]
  and_intros
  · rw [ofNat_sub_beq (by omega_arith) (by omega_arith)]
  all_goals rfl

/-- `sel`: multiplication `c`'s operands, `B := 2^kb` before multiplication 1
and `B := x` before 2. -/
theorem sel_ok (hl : PubOk l) {t₀ t : State} {B H X : Addr} {M k R0 c : Nat} (e : Env l t₀ B H X M k)
    (h : Inv l t₀ B H X M R0 c t) (hc : c < 20) :
    WP isa (sel l) t fun u =>
      u.gpr .r8 = off B (if c = 2 then oB l else oA l) ∧
      u.gpr .r9 = off B (if c = 1 ∨ c = 19 then oB l else oA l) ∧
      u.gpr .r11 = off B (oA l) ∧ u.gpr .r12 = mask52 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .rbp, .r8, .r9, .r11] t u ∧ u.mxcsr = t.mxcsr ∧
      Outside B (oB l) l.NB t.mem u.mem ∧
      (1 ≤ c → ∀ j < l.L, word u.mem B (oB l + l.off j) =
        BitVec.ofNat 64 (limbN (if c = 1 then 2 ^ kb l else wv t₀.mem X 0 l.W) j)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  have hs : Scr t B (48 * (l.W + 2)) := e.scr.congr h.keep.2.2
  have hF : ∀ j < l.L, oB l + l.off j + 8 ≤ oB l + l.NB := fun j hj => by
    have := off_ltN hl.amm hj; omega_arith
  have hNB : 0 < l.NB := by simp only [Lay.NB]; have := hl.amm.bounds.1; omega_arith
  unfold sel
  refine WP.seq (WP.mono (cmp_ok (c := c) (n := 1) (by omega_arith) (by decide) h.r13) fun t₁ ⟨z₁, g₁, rd₁, wr₁, m₁, x₁⟩ => ?_)
  refine WP.ite (decide (c = 1)) (by simp [eval, z₁]) (fun hb => ?_) (fun hb => ?_)
  · -- `B := 2^kb`, then `A := A B`.
    have hc1 : c = 1 := by simpa using hb
    subst hc1
    rw [WP.block_append_iff]
    refine WP.mono (pow2_ok hl (s := t₁) (B := B) (by rw [g₁]; exact h.rbx)
      (fun j hj => by rw [wr₁]; exact hs.st (show oB l + l.off j + 8 ≤ _ by have := hF j hj; omega_arith))
      (by omega_arith)) fun u₁ ⟨v₁, o₁, k₁, x₁'⟩ => ?_
    refine WP.mono (setOps_ok (B := B) (o := oA l) (a := oA l) (b := oB l) (by rw [k₁.gpr (by decide), g₁]; exact h.rbx)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨r8, r9, r11, k₂, m₂, x₂⟩ => ?_
    refine ⟨by simpa using r8, by simpa using r9, r11, ?_, ?_, by rw [x₂, x₁', x₁], by rw [m₂, ← m₁]; exact o₁,
      fun _ j hj => by rw [m₂]; simpa using v₁ j hj⟩
    · rw [k₂.gpr (by decide), k₁.gpr (by decide), g₁]; exact h.r12
    · refine ⟨fun r hr => ?_, by rw [k₂.2.1, k₁.2.1, rd₁], by rw [k₂.2.2, k₁.2.2, wr₁]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k₂.gpr (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
        k₁.gpr (by simp [hr.1, hr.2.2.2.2.2.2]), g₁]
  have hc1 : c ≠ 1 := by simpa using hb
  refine WP.seq (WP.mono (cmp_ok (c := c) (n := 2) (by omega_arith) (by decide) (by rw [g₁]; exact h.r13))
    fun t₂ ⟨z₂, g₂, rd₂, wr₂, m₂, x₂⟩ => ?_)
  refine WP.ite (decide (c = 2)) (by simp [eval, z₂]) (fun hb => ?_) (fun hb => ?_)
  · -- `B := x`, then `A := B A`.
    have hc2 : c = 2 := by simpa using hb
    subst hc2
    have hXv : wv t₂.mem X 0 l.W = wv t₀.mem X 0 l.W := by
      rw [m₂, m₁]
      exact VG.Proof.Bignum.wv_congr fun i hi => by
        rw [Nat.zero_add]; exact e.sepX _ _ (h.frame.mono (Nat.le_refl _) (by omega_arith)) i hi
    rw [WP.block_append_iff]
    have hXv' : wv t₂.mem (off H (arr l aX)) 0 l.W = wv t₀.mem X 0 l.W := by rw [← e.hX]; exact hXv
    refine WP.mono (ld52_ok hl (s := t₂) (B := B) (H := H) (j := aX) (o := oB l)
      (by rw [g₂, g₁]; exact h.rbx) (by rw [g₂, g₁]; exact h.rdi) (by rw [g₂, g₁]; exact h.r12) e.hx
      (fun i hi => by rw [rd₂, wr₂, rd₁, wr₁, h.keep.2.1, h.keep.2.2, ← e.hX]; exact e.hrd i hi)
      (fun q hq => by rw [wr₂, wr₁]; exact hs.st (show oB l + l.off q + 8 ≤ _ by have := hF q hq; omega_arith))
      (by omega_arith)
      (fun m m' f => by rw [← e.hX]; exact e.sepX m m' (f.mono (by omega_arith) (by omega_arith)))) fun u₁ ⟨v₁, o₁, k₁, x₁'⟩ => ?_
    refine WP.mono (setOps_ok (B := B) (o := oA l) (a := oB l) (b := oA l) (by rw [k₁.gpr (by decide), g₂, g₁]; exact h.rbx)
      (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨r8, r9, r11, k₂, m₃, x₃⟩ => ?_
    refine ⟨by simpa using r8, by simpa using r9, r11, ?_, ?_, by rw [x₃, x₁', x₂, x₁],
      by rw [m₃, ← m₁, ← m₂]; exact o₁, fun _ j hj => by rw [m₃, v₁ j hj, hXv']; simp⟩
    · rw [k₂.gpr (by decide), k₁.gpr (by decide), g₂, g₁]; exact h.r12
    · refine ⟨fun r hr => ?_, by rw [k₂.2.1, k₁.2.1, rd₂, rd₁], by rw [k₂.2.2, k₁.2.2, wr₂, wr₁]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [k₂.gpr (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]),
        k₁.gpr (by simp [hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2, hr.2.1]), g₂, g₁]
  have hc2 : c ≠ 2 := by simpa using hb
  refine WP.seq (WP.mono (cmp_ok (c := c) (n := 19) (by omega_arith) (by decide) (by rw [g₂, g₁]; exact h.r13))
    fun t₃ ⟨z₃, g₃, rd₃, wr₃, m₃, x₃⟩ => ?_)
  have hB₃ : t₃.gpr .rbx = B := by rw [g₃, g₂, g₁]; exact h.rbx
  have fin : ∀ b, b < 2 ^ 31 → (if c = 1 ∨ c = 19 then oB l else oA l) = b →
      WP isa (.block (setOps (oA l) (oA l) b)) t₃ fun u =>
        u.gpr .r8 = off B (if c = 2 then oB l else oA l) ∧
        u.gpr .r9 = off B (if c = 1 ∨ c = 19 then oB l else oA l) ∧
        u.gpr .r11 = off B (oA l) ∧ u.gpr .r12 = mask52 ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rsi, .rbp, .r8, .r9, .r11] t u ∧ u.mxcsr = t.mxcsr ∧
        Outside B (oB l) l.NB t.mem u.mem ∧
        (1 ≤ c → ∀ j < l.L, word u.mem B (oB l + l.off j) =
          BitVec.ofNat 64 (limbN (if c = 1 then 2 ^ kb l else wv t₀.mem X 0 l.W) j)) := fun b hb hbe =>
    WP.mono (setOps_ok (o := oA l) (a := oA l) (b := b) hB₃ (by omega_arith) (by omega_arith) hb)
      fun u ⟨r8, r9, r11, k, m, x⟩ => by
        have hm : u.mem = t.mem := by rw [m, m₃, m₂, m₁]
        refine ⟨by simpa [hc2] using r8, ?_, r11, ?_, ?_, by rw [x, x₃, x₂, x₁], by rw [hm]; exact Outside.refl _ _ _ _,
          fun h1 j hj => ?_⟩
        · rw [r9, hbe]
        · rw [k.gpr (by decide), g₃, g₂, g₁]; exact h.r12
        · refine ⟨fun r hr => ?_, by rw [k.2.1, rd₃, rd₂, rd₁], by rw [k.2.2, wr₃, wr₂, wr₁]⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          rw [k.gpr (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g₃, g₂, g₁]
        · rw [hm, h.b (by omega_arith) j hj]; simp [hc1]
  refine WP.ite (decide (c = 19)) (by simp [eval, z₃]) (fun hb => ?_) (fun hb => ?_)
  · exact fin (oB l) (by omega_arith) (by simp only [show c = 19 by simpa using hb, ↓reduceIte, or_true])
  · have : c ≠ 19 := by simpa using hb
    exact fin (oA l) (by omega_arith) (by simp only [hc1, this, or_self, ↓reduceIte])

theorem mul_congr {M a a' b b' : Nat} (ha : a % M = a' % M) (hb : b % M = b' % M) : a * b % M = a' * b' % M := by
  rw [Nat.mul_mod, ha, hb, ← Nat.mul_mod]

/-- The values through multiplication `c`: `A' R' ≡ a b` from `VA c A`. -/
theorem va_step (hl : PubOk l) {M R0 x A A' a b c : Nat} (hM : M % 2 = 1) (hc : c < 20)
    (hA : VA l M R0 x c A) (ha : a = if c = 2 then x else A)
    (hb : b = if c = 1 then 2 ^ kb l else if c = 19 then x else A)
    (h : A' * 2 ^ (52 * l.S) % M = a * b % M) : VA l M R0 x (c + 1) A' := by
  obtain ⟨-, -, -, -, -, -, a7, -, -, a10, -, -⟩ := hl.area
  have hR := VG.Proof.Bignum.coprime_pow2 hM (52 * l.S)
  have hR2 : Nat.Coprime (2 ^ (52 * l.S) * 2 ^ (52 * l.S)) M := by
    have := VG.Proof.Bignum.coprime_pow2 hM (52 * l.S + 52 * l.S); rwa [Nat.pow_add] at this
  subst ha hb
  obtain _ | _ | _ | i := c
  · show A' * 2 ^ (52 * l.S) % M = R0 * R0 % M
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)] at h
    rw [h]; exact mul_congr hA hA
  · show A' * 2 ^ (52 * l.S) * 2 ^ (52 * l.S) % M = R0 * R0 * 2 ^ kb l % M
    rw [ite_eq_right (by decide), ite_eq_left rfl] at h
    rw [mul_congr h (rfl : 2 ^ (52 * l.S) % M = _), Nat.mul_right_comm]
    exact mul_congr hA rfl
  · intro hq
    show A' % M = (if 0 + 3 = 20 then x ^ 2 ^ 16 * x else x ^ 2 ^ 0 * 2 ^ (52 * l.S)) % M
    rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_right (by decide)] at h
    rw [ite_eq_right (by decide), Nat.pow_zero, Nat.pow_one]
    -- `R0² 2^kb ≡ R⁴ 2^kb = R'⁴`, so `A ≡ R'²`.
    have e1 : 2 ^ (64 * l.W) * 2 ^ (64 * l.W) * (2 ^ (64 * l.W) * 2 ^ (64 * l.W)) * 2 ^ kb l =
        2 ^ (52 * l.S) * 2 ^ (52 * l.S) * (2 ^ (52 * l.S) * 2 ^ (52 * l.S)) := by
      simp only [← Nat.pow_add]; congr 1; rw [a7]; omega_arith
    have h4 : R0 * R0 * 2 ^ kb l % M =
        2 ^ (52 * l.S) * 2 ^ (52 * l.S) * (2 ^ (52 * l.S) * 2 ^ (52 * l.S)) % M := by
      rw [mul_congr (mul_congr hq hq) rfl, e1]
    have hA2 : A % M = 2 ^ (52 * l.S) * 2 ^ (52 * l.S) % M := by
      refine VG.Proof.Bignum.mont_cancel hR2 ?_
      rw [← Nat.mul_assoc, show A * 2 ^ (52 * l.S) * 2 ^ (52 * l.S) % M = R0 * R0 * 2 ^ kb l % M from hA, h4]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [h, mul_congr rfl hA2, Nat.mul_assoc]
  · intro hq
    have hA := hA hq
    rw [ite_eq_right (by omega_arith)] at hA
    rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)] at h
    by_cases h19 : i + 3 = 19
    · obtain rfl : i = 16 := by omega_arith
      show A' % M = (if 16 + 1 + 3 = 20 then x ^ 2 ^ 16 * x else _) % M
      rw [ite_eq_left h19] at h
      rw [ite_eq_left (by omega_arith)]
      generalize (2 : Nat) ^ 16 = E at hA ⊢
      refine VG.Proof.Bignum.mont_cancel hR ?_
      rw [h, mul_congr hA rfl, Nat.mul_right_comm]
    · show A' % M = (if i + 1 + 3 = 20 then x ^ 2 ^ 16 * x else x ^ 2 ^ (i + 1) * 2 ^ (52 * l.S)) % M
      rw [ite_eq_right h19] at h
      rw [ite_eq_right (by omega_arith)]
      refine VG.Proof.Bignum.mont_cancel hR ?_
      rw [h, mul_congr hA hA, Nat.pow_succ 2 i, Nat.pow_mul x (2 ^ i) 2, Nat.pow_two (x ^ 2 ^ i), Nat.mul_mul_mul_comm, ← Nat.mul_assoc]

/-- The number whose limbs are those of `v`, below `2^(52 L)`. -/
theorem val52_of {m : Mem} {B : Addr} {o v : Nat} (h : ∀ j < l.L, word m B (o + l.off j) = BitVec.ofNat 64 (limbN v j))
    (hv : v < 2 ^ (52 * l.L)) : val52 l m B o = v := by
  unfold val52
  rw [lval_congr (L' := limbN v) fun j hj => by
    simp only [limb]; rw [h j hj, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have : limbN v j < 2 ^ 52 := Nat.mod_lt _ (by decide); omega_arith),
    AmmSym.lval_limbN, Nat.mod_eq_of_lt hv]

theorem limbN_lt64 (v j : Nat) : (BitVec.ofNat 64 (limbN v j)).toNat < 2 ^ 52 := by
  rw [BitVec.toNat_ofNat]
  have : limbN v j < 2 ^ 52 := Nat.mod_lt _ (by decide)
  omega_arith

/-- One multiplication of the loop. -/
theorem iter_ok (hl : PubOk l) {t₀ t : State} {B H X : Addr} {M k R0 c : Nat} (e : Env l t₀ B H X M k)
    (h : Inv l t₀ B H X M R0 c t) (hc : c < 20) :
    WP isa (VG.Impl.Bignum.X86_64.seqs [sel l, ammMul l,
        .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm 20)]]) t fun t' =>
      Inv l t₀ B H X M R0 (c + 1) t' ∧ t'.zf = some (decide (c + 1 = 20)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  have hL := (conv_boundsN hl.amm).2.1
  have hs : Scr t B (48 * (l.W + 2)) := e.scr.congr h.keep.2.2
  have hxv : wv t₀.mem X 0 l.W < 2 ^ (52 * l.L) :=
    Nat.lt_of_lt_of_le (VG.Proof.Bignum.wv_lt _ _ _ _) (AmmSym.pow2_le hL)
  have hkb : 2 ^ kb l < 2 ^ (52 * l.L) := Nat.pow_lt_pow_right (by decide) (by omega_arith)
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (sel_ok hl e h hc) fun u ⟨r8, r9, r11, r12, ku, xu, ou, bu⟩ => ?_)
  have huB : u.gpr .rbx = B := (ku.gpr (by decide)).trans h.rbx
  have hsu : Scr u B (48 * (l.W + 2)) := hs.congr ku.2.2
  have fu : Outside B (oA l) (2 * l.NB) t₀.mem u.mem := h.frame.trans (ou.mono (by omega_arith) (by omega_arith))
  have mdu : Mod l u.mem B M k := e.md.of_outside hl fu (by omega_arith)
  have hAu : ∀ j < l.L, word u.mem B (oA l + l.off j) = word t.mem B (oA l + l.off j) := fun j hj => by
    have := off_ltN hl.amm hj; exact ou.word (by omega_arith) (by omega_arith)
  have laU : ∀ j < l.L, limb l u.mem B (oA l) j < 2 ^ 52 := fun j hj => by
    simp only [limb]; rw [hAu j hj]; exact h.a j hj
  have vAu : val52 l u.mem B (oA l) = val52 l t.mem B (oA l) := lval_congr fun j hj => by
    simp only [limb]; rw [hAu j hj]
  have lB : 1 ≤ c → ∀ j < l.L, limb l u.mem B (oB l) j < 2 ^ 52 := fun h1 j hj => by
    simp only [limb]; rw [bu h1 j hj]; exact limbN_lt64 _ _
  have vB : 1 ≤ c → val52 l u.mem B (oB l) = if c = 1 then 2 ^ kb l else wv t₀.mem X 0 l.W := fun h1 =>
    val52_of (bu h1) (by split <;> with_reducible assumption)
  have la : ∀ j < l.L, limb l u.mem B (if c = 2 then oB l else oA l) j < 2 ^ 52 := by
    split
    · exact lB (by omega_arith)
    · exact laU
  have lb : ∀ j < l.L, limb l u.mem B (if c = 1 ∨ c = 19 then oB l else oA l) j < 2 ^ 52 := by
    split
    · exact lB (by omega_arith)
    · exact laU
  have va : val52 l u.mem B (if c = 2 then oB l else oA l) =
      if c = 2 then wv t₀.mem X 0 l.W else val52 l t.mem B (oA l) := by
    by_cases h2 : c = 2
    · rw [ite_eq_left h2, ite_eq_left h2, vB (by omega_arith), ite_eq_right (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right h2, vAu]
  have vb : val52 l u.mem B (if c = 1 ∨ c = 19 then oB l else oA l) =
      if c = 1 then 2 ^ kb l else if c = 19 then wv t₀.mem X 0 l.W else val52 l t.mem B (oA l) := by
    by_cases h1 : c = 1
    · rw [ite_eq_left (.inl h1), ite_eq_left h1, vB (by omega_arith), ite_eq_left h1]
    · by_cases h19 : c = 19
      · rw [ite_eq_left (.inr h19), ite_eq_right h1, ite_eq_left h19, vB (by omega_arith), ite_eq_right h1]
      · rw [ite_eq_right (by omega_arith), ite_eq_right h1, ite_eq_right h19, vAu]
  refine WP.seq (WP.mono (core_ok hl (k := k) huB r8 r9 r11 hsu mdu (by split <;> omega_arith) (by split <;> omega_arith) la lb)
    fun u' ⟨la', vv, oo, gg, r12', rd', wr', x'⟩ => ?_)
  have g' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rbp → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 →
      r ≠ .r11 → r ≠ .r12 → u'.gpr r = t.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    rw [gg r h1 h2 h3 h4 h7 h8 h10, ku.gpr (by simp [h1, h2, h4, h5, h6, h7, h9])]
  refine WP.mono (inc_ok hc (by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]; exact h.r13)) fun t' ⟨r13'', z, k3, m3, x3⟩ => ⟨?_, z⟩
  have hBo : ∀ j < l.L, word t'.mem B (oB l + l.off j) = word u.mem B (oB l + l.off j) := fun j hj => by
    have := off_ltN hl.amm hj; rw [m3]; exact oo.word (by omega_arith) (by omega_arith)
  refine ⟨?_, ?_, ?_, r13'', ⟨fun r hr => ?_, ?_, ?_⟩, by rw [x3, x', xu, h.mx], ?_, fun j hj => by
    rw [m3]; exact la' j hj, fun h3 j hj => by rw [hBo j hj, bu (by omega_arith) j hj, ite_eq_right (by omega_arith)], ?_⟩
  · rw [k3.gpr (by decide), g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact h.rbx
  · rw [k3.gpr (by decide), g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact h.rdi
  · rw [k3.gpr (by decide)]; exact r12'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
    rw [k3.gpr (by simp [h11]), g' r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
    exact h.keep.gpr (by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11])
  · rw [k3.2.1, rd', ku.2.1, h.keep.2.1]
  · rw [k3.2.2, wr', ku.2.2, h.keep.2.2]
  · rw [m3]; exact fu.trans (oo.mono (by omega_arith) (by omega_arith))
  · intro hP
    obtain ⟨hlt, hva⟩ := h.v hP
    have hxM : wv t₀.mem X 0 l.W < 2 * M := by omega_arith
    obtain ⟨lt', cg⟩ := vv (by rw [va]; split <;> omega_arith)
      (by rw [vb]; split
          · exact e.big
          · split <;> omega_arith)
    rw [m3]
    exact ⟨lt', va_step hl e.odd hc hva va vb cg⟩

/-- The loop, from multiplication `c`. -/
theorem loop_ok (hl : PubOk l) {t₀ : State} {B H X : Addr} {M k R0 : Nat} (e : Env l t₀ B H X M k) :
    ∀ c t, c < 20 → Inv l t₀ B H X M R0 c t →
      WP isa (.loop (VG.Impl.Bignum.X86_64.seqs [sel l, ammMul l,
        .block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.imm 20)]]) .ne) t (Inv l t₀ B H X M R0 20) := by
  intro c t hc hI
  refine WP.loop (M := isa) (c := .ne) (Q := Inv l t₀ B H X M R0 20)
    (fun n t => ∃ c, c < 20 ∧ n = 20 - c ∧ Inv l t₀ B H X M R0 c t) ?_ (20 - c) t ⟨c, hc, rfl, hI⟩
  intro n t ⟨c, hc, hn, hI⟩
  refine WP.mono (iter_ok hl e hI hc) fun t' ⟨hI', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  by_cases h20 : c + 1 = 20
  · rw [h20] at hI'
    exact .inl ⟨by simp [h20], hI'⟩
  · exact .inr ⟨by simp [h20], 20 - (c + 1), by omega_arith, c + 1, by omega_arith, rfl, hI'⟩

/-- The vector code: `A := x^65537`, almost reduced, from `A ≡ R²` (`R0`),
within Intel's MXCSR prologue and epilogue (the slots at `oMx`). -/
theorem vec_ok (hl : PubOk l) {s : State} {B H X : Addr} {M k : Nat} (e : Env l s B H X M k)
    (hB : s.gpr .rbx = B) (hdi : s.gpr .rdi = H) (h12 : s.gpr .r12 = mask52)
    (hA : ∀ j < l.L, limb l s.mem B (oA l) j < 2 ^ 52) (hA2 : val52 l s.mem B (oA l) < 2 * M) :
    WP isa (VG.Impl.Rsa.X86_64.PubIfma.vec l) s fun s' =>
      (∀ j < l.L, limb l s'.mem B (oA l) j < 2 ^ 52) ∧
      (wv s.mem X 0 l.W < M → val52 l s'.mem B (oA l) < 2 * M ∧
        (val52 l s.mem B (oA l) % M = 2 ^ (64 * l.W) * 2 ^ (64 * l.W) % M →
          val52 l s'.mem B (oA l) % M = wv s.mem X 0 l.W ^ 2 ^ 16 * wv s.mem X 0 l.W % M)) ∧
      Outside B (oA l) (2 * l.NB + 8) s.mem s'.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13] s s' ∧
      s'.mxcsr = s.mxcsr &&& 0xFFFF := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hl.area
  have hs := e.scr
  have hn := hs.nowrap
  unfold VG.Impl.Rsa.X86_64.PubIfma.vec withMx
  refine WP.seq (WP.mono (mxSave_ok (d := oMx l) hB hs (by omega_arith)) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  refine WP.seq (WP.seq (WP.mono (mxSet_ok (d := oMx l) hB₁ (hs.congr k₁.2.2) (by omega_arith)) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_))
  have O₁ : Outside B (oMx l) 4 s.mem s₁.mem := by
    rw [m₁]
    exact (AmmSym.writeW32_outside _ B _ (by omega_arith)).trans (AmmSym.writeW32_outside _ B _ (by omega_arith))
  have O₂ : Outside B (oMx l + 4) 4 s₁.mem s₂.mem := by
    rw [m₂]; exact AmmSym.writeW32_outside _ B _ (by omega_arith)
  have O : Outside B (oA l) (2 * l.NB + 8) s.mem s₂.mem :=
    (O₁.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
  -- `r13 := 0`
  refine WP.seq (WP.seq ?_)
  rw [WP.block_cons_iff]
  refine ⟨s₂.setReg32 .r13 (BitVec.ofNat 32 0), rfl, WP.block_nil ?_⟩
  generalize ht : s₂.setReg32 .r13 (BitVec.ofNat 32 0) = t₀
  have g₀ : ∀ r, r ≠ .r13 → t₀.gpr r = s₂.gpr r := fun r hr => by
    rw [← ht, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]
  have r13₀ : t₀.gpr .r13 = BitVec.ofNat 64 0 := by rw [← ht, State.setReg32, RegUpd.gpr_setReg_self]; rfl
  have mt : t₀.mem = s₂.mem := by rw [← ht]; rfl
  have rdt : t₀.rd = s.rd := by rw [← ht, ← k₁.2.1, ← k₂.2.1]; rfl
  have wrt : t₀.wr = s.wr := by rw [← ht, ← k₁.2.2, ← k₂.2.2]; rfl
  have xt : t₀.mxcsr = 0x1FBF := by rw [← ht, ← x₂]; rfl
  have Ot : Outside B (oA l) (2 * l.NB + 8) s.mem t₀.mem := by rw [mt]; exact O
  have gs : ∀ r, r ≠ .rax → r ≠ .r11 → r ≠ .r13 → t₀.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₀ r h3, k₂.gpr (by simp [h1]), k₁.gpr (by simp [h2])]
  have Om : Outside B (oMx l) 8 s.mem t₀.mem := by
    rw [mt]; exact (O₁.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
  have hAw : ∀ j < l.L, word t₀.mem B (oA l + l.off j) = word s.mem B (oA l + l.off j) := fun j hj => by
    have := off_ltN hl.amm hj; exact Om.word (by omega_arith) (by omega_arith)
  have hval : val52 l t₀.mem B (oA l) = val52 l s.mem B (oA l) := lval_congr fun j hj => by
    simp only [limb]; rw [hAw j hj]
  have hxv : wv t₀.mem X 0 l.W = wv s.mem X 0 l.W :=
    VG.Proof.Bignum.wv_congr fun i hi => by rw [Nat.zero_add]; exact e.sepX _ _ Ot i hi
  have e₀ : Env l t₀ B H X M k :=
    ⟨hs.congr wrt, e.md.of_outside hl Ot (by omega_arith), e.odd, e.big, e.hX, e.hx,
      fun i hi => by rw [rdt, wrt]; exact e.hrd i hi, e.sepX⟩
  have I₀ : Inv l t₀ B H X M (val52 l s.mem B (oA l)) 0 t₀ :=
    ⟨by rw [gs _ (by decide) (by decide) (by decide)]; exact hB,
      by rw [gs _ (by decide) (by decide) (by decide)]; exact hdi,
      by rw [gs _ (by decide) (by decide) (by decide)]; exact h12, r13₀,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl, Outside.refl _ _ _ _,
      fun j hj => by simp only [limb]; rw [hAw j hj]; exact hA j hj, fun h => absurd h (by decide),
      fun _ => ⟨by rw [hval]; exact hA2, by show _ % M = _ % M; rw [hval]⟩⟩
  refine WP.mono (loop_ok hl e₀ 0 t₀ (by decide) I₀) fun s₃ I₃ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, WP.block_nil ?_⟩
  have hB₃ : s₃.gpr .rbx = B := I₃.rbx
  have O₃ : Outside B (oA l) (2 * l.NB + 8) s.mem s₃.mem := Ot.trans (I₃.frame.mono (Nat.le_refl _) (by omega_arith))
  have hv : s₃.mem.readW (off B (oMx l)) 32 = s.mxcsr &&& 0xFFFF := by
    rw [VG.Proof.Bignum.Outside.readW32 (I₃.frame.trans (Outside.refl _ _ _ _)) (.inr (by omega_arith)) (by omega_arith), mt,
      VG.Proof.Bignum.Outside.readW32 O₂ (.inl (by omega_arith)) (by omega_arith), m₁, Mem.readW_writeW_self32]
  refine WP.mono (mxRestore_ok (d := oMx l) hB₃ (hs.congr (by rw [I₃.keep.2.2, wrt])) (by omega_arith) hv)
    fun s₄ ⟨m₄, g₄, rd₄, wr₄, x₄⟩ => ⟨fun j hj => by rw [m₄]; exact I₃.a j hj, fun hP => ?_,
      by rw [m₄]; exact O₃, ⟨fun r hr => ?_, by rw [rd₄, I₃.keep.2.1, rdt], by rw [wr₄, I₃.keep.2.2, wrt]⟩, x₄⟩
  · rw [← hxv] at hP
    obtain ⟨lt, va⟩ := I₃.v hP
    rw [m₄, ← hxv]
    refine ⟨lt, fun hq => ?_⟩
    have := va hq
    rw [ite_eq_left rfl] at this
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄, I₃.keep.gpr (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2]),
      gs r hr.1 hr.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2]

end VG.Proof.Bignum.X86_64.Ifma.Pub
