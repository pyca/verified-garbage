module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Limbs

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CoreU
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Tab
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Sel
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# The IFMA Miller–Rabin round: the multiplications and the table

`amm_ok`: `ammMul` at offsets of the round's area (`PubVec.core_ok`'s
statement for any output); `Rep`: a number in Montgomery form for
`R' = 2^(52 S)`; `copyN_ok`, `select_ok` (the entry of the window's digit)
and `table_ok` (`T_j = b^j R'`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside mask Frm)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma (limb val52)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52 ammMul vreg Lay at_)
open VG.Impl.Rsa.X86_64.PubIfma (setOps)
open VG.Impl.MillerRabin.X86_64.Ifma

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The bytes of the area. -/
def size (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Nat := oF l + 8

/-- The number at `o` stands for `x mod c` in Montgomery form for
`R' = 2^(52 S)`: limbs below `2⁵²`, below `2 c`, congruent to `x R'`. -/
def Rep (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (c o x : Nat) : Prop :=
  Canon l m B o ∧ val52 l m B o < 2 * c ∧ val52 l m B o % c = x * 2 ^ (52 * l.S) % c

/-- The layouts' offsets: the area below `2^31`, its numbers apart and the
moduli's room. -/
theorem PubOk.offs (hl : PubOk l) :
    size l + 63 ≤ 16 * (8 * (l.W + 2)) ∧ size l < 2 ^ 31 ∧ l.NB + 32 = oY l ∧ oY l + l.NB = oS l ∧
    oS l + l.NB = oT l 0 ∧ (∀ j, oT l j = oT l 0 + j * l.NB) ∧ oT l 4 = oP1c l ∧ oP1c l + l.NB = oM1 l ∧
    oM1 l + l.NB = oM1c l ∧ oM1c l + l.NB = oV l ∧ oV l + 8 = oMx l ∧ l.NB % 32 = 0 ∧ 64 * l.W + 2 ≤ 52 * l.S ∧
    l.S ≤ l.L ∧ 1 ≤ l.dbls ∧ l.dbls < 2 ^ 31 ∧ 1 ≤ shifts l ∧ shifts l < 2 ^ 31 := by
  rcases hl with rfl | rfl | rfl <;> refine ⟨by decide, by decide, rfl, rfl, rfl, fun j => by
    simp only [oT]; omega, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

set_option warningAsError false

/-- `ammMul` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of the area `B`
(`o` may be `a` or `b`). -/
theorem amm_ok (hl : PubOk l) {s : State} {B : Addr} {Z c k o a b : Nat} (hB : s.gpr .rbx = B)
    (r8 : s.gpr .r8 = off B a) (r9 : s.gpr .r9 = off B b) (r11 : s.gpr .r11 = off B o)
    (hs : Scr s B Z) (hZ : Z < 2 ^ 31) (hZ32 : l.NB + 32 ≤ Z) (hm : Mod l s.mem B c k)
    (ho : o + l.NB ≤ Z) (ha : a + l.NB ≤ Z) (hb : b + l.NB ≤ Z)
    (hca : Canon l s.mem B a) (hcb : Canon l s.mem B b) :
    WP isa (ammMul l) s fun t =>
      Canon l t.mem B o ∧
      (val52 l s.mem B a < 2 * c → val52 l s.mem B b < 2 * c →
        val52 l t.mem B o < 2 * c ∧
        val52 l t.mem B o * 2 ^ (52 * l.S) % c = val52 l s.mem B a * val52 l s.mem B b % c) ∧
      Outside B o l.NB s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.gpr .r12 = mask52 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  have hn := hl.nl
  have hp : ∀ p < l.nl, p = 0 := fun p hp => by omega_arith
  have h0 : ∀ c, l.D * 0 + c = c := fun c => by rw [Nat.mul_zero, Nat.zero_add]
  have hM : val52 l s.mem B VG.Impl.Rsa.X86_64.CrtIfma.oM = c := hm.val
  refine WP.mono (VG.Proof.Bignum.X86_64.Ifma.ammCoreSpecN_ok hl.amm (VG.Proof.Bignum.X86_64.Ifma.ammMul_core hl.amm)
    (Z := Z) (k := fun _ => k) hB r8 r9 r11 hs
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith) (by omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (by rw [hn]; simp only [Nat.sub_self, Nat.mul_zero]; omega_arith)
    (fun p hp' j hj => by obtain rfl := hp p hp'; rw [h0, h0, h0]; exact ⟨hca j hj, hcb j hj, hm.lt j hj⟩)
    (fun p hp' t ht => by obtain rfl := hp p hp'; rw [h0]; exact hm.k0 t ht) (fun _ _ => hm.klt)
    (fun p hp' => by obtain rfl := hp p hp'; rw [h0]; exact hm.inv))
    fun t ⟨hv, hf, hg, h12, hrd, hwr, hx⟩ => ?_
  have v := hv 0 (by omega_arith)
  simp only [h0, hM] at v
  exact ⟨v.1, fun hA hB' => v.2 hA hB' hm.big, VG.Proof.Bignum.X86_64.Ifma.Pub.OutN.one hl hf, hg, h12, hrd, hwr, hx⟩

/-- `amm_ok` on numbers in Montgomery form, for an odd `c`. -/
theorem amm_rep (hl : PubOk l) {s : State} {B : Addr} {Z c k o a b x y : Nat} (hB : s.gpr .rbx = B)
    (r8 : s.gpr .r8 = off B a) (r9 : s.gpr .r9 = off B b) (r11 : s.gpr .r11 = off B o)
    (hs : Scr s B Z) (hZ : Z < 2 ^ 31) (hZ32 : l.NB + 32 ≤ Z) (hm : Mod l s.mem B c k) (hodd : c % 2 = 1)
    (ho : o + l.NB ≤ Z) (ha : a + l.NB ≤ Z) (hb : b + l.NB ≤ Z)
    (hxa : Rep l s.mem B c a x) (hyb : Rep l s.mem B c b y) :
    WP isa (ammMul l) s fun t =>
      Rep l t.mem B c o (x * y) ∧ Outside B o l.NB s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.gpr .r12 = mask52 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (amm_ok hl hB r8 r9 r11 hs hZ hZ32 hm ho ha hb hxa.1 hyb.1) fun t ⟨hc, hv, rest⟩ => ⟨⟨hc, ?_⟩, rest⟩
  obtain ⟨lt, e⟩ := hv hxa.2.1 hyb.2.1
  refine ⟨lt, VG.Proof.Bignum.mont_cancel (VG.Proof.Bignum.coprime_pow2 hodd (52 * l.S)) ?_⟩
  rw [e, Nat.mul_mod, hxa.2.2, hyb.2.2, ← Nat.mul_mod, Nat.mul_mul_mul_comm, ← Nat.mul_assoc]

/-- The layouts' vector registers: `R` of 32 bytes for a number. -/
theorem PubOk.regs (hl : PubOk l) : 2 ≤ l.R ∧ l.R ≤ 20 ∧ l.NB = 32 * l.R ∧ l.L = 4 * l.R := by
  rcases hl with rfl | rfl | rfl <;> decide

open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique readW256_outside off_add
  wrList_outside') in
/-- `Tab.copies_ok` in an area of `Z` bytes. -/
private theorem copies_ok {B : Addr} {Z : Nat} (hZ : Z < 2 ^ 31) :
    ∀ (xs : List (Nat × Nat)) (s : State), s.gpr .rbx = B → Scr s B Z →
      (∀ x ∈ xs, x.1 + 32 ≤ Z ∧ x.2 + 32 ≤ Z) →
      (∀ x ∈ xs, ∀ y ∈ xs, y.1 + 32 ≤ x.2 ∨ x.2 + 32 ≤ y.1) →
      WP isa (.block (VG.Proof.Bignum.X86_64.Ifma.copyCode xs)) s fun s' =>
        s'.mem = wrList s.mem B (xs.map fun x => (x.2, s.mem.readW (off B x.1) 256)) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | (a, o) :: rest, s, hB, hs, hxs, hsep => by
    have ho := hxs (a, o) (List.mem_cons_self ..)
    rw [VG.Proof.Bignum.X86_64.Ifma.copyCode, List.flatMap_cons, List.cons_append, List.cons_append,
      List.nil_append, WP.block_cons_iff]
    have hld : InRegions (s.rd ++ s.wr) (off B a) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := a) (n := 32) (by omega_using [ho]) (by decide); ⟨_, List.mem_append_right _ h, c⟩
    have hst : InRegions s.wr (off B o) 32 :=
      let ⟨_, h, c⟩ := hs.region (d := o) (n := 32) (by omega_using [ho]) (by decide); ⟨_, h, c⟩
    refine ⟨s.setVy (vreg 0) (s.mem.readW (off B a) 256),
      by simp only [exec, VG.Proof.Bignum.X86_64.Ifma.ea_rG hB, State.load256, hld, ite_true, Option.map_some], ?_⟩
    have y₁ := VG.Proof.Bignum.X86_64.Ifma.vy_setVy_self s (vreg 0) (s.mem.readW (off B a) 256)
    have e₁ : ∀ t : State, t = s.setVy (vreg 0) (s.mem.readW (off B a) 256) →
        t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
      rintro t rfl; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    generalize hs₁ : s.setVy (vreg 0) (s.mem.readW (off B a) 256) = s₁ at y₁ ⊢
    obtain ⟨g₁, m₁, rd₁, wr₁, x₁⟩ := e₁ s₁ hs₁.symm
    have hB₁ : s₁.gpr .rbx = B := by rw [g₁]; exact hB
    rw [WP.block_cons_iff]
    refine ⟨{ s₁ with mem := s₁.mem.writeW (off B o) (s₁.vy (vreg 0)) }, by
      simp only [exec, VG.Proof.Bignum.X86_64.Ifma.ea_rG hB₁, State.store256, wr₁, hst, ite_true], ?_⟩
    rw [y₁, m₁]
    refine WP.mono (copies_ok hZ rest _ (by rw [← g₁] at hB; exact hB) (hs.congr wr₁)
      (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hsep x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ⟨?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, x'.trans x₁⟩
    rw [m', List.map_cons, wrList]
    refine congrArg (wrList _ B) (List.map_congr_left fun y hy => ?_)
    have := hxs y (List.mem_cons_of_mem _ hy)
    have hs' := hsep (a, o) (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
    exact congrArg _ (readW256_outside (writeW256_outside _ B _ (by omega_arith)) (by omega_using [hs'])
      (by omega_using [hZ, this]))

/-- `[o] := [a]`. -/
theorem copyN_ok (hl : PubOk l) {s : State} {B : Addr} {Z o a : Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B Z) (hZ : Z < 2 ^ 31) (ho : o + l.NB ≤ Z) (ha : a + l.NB ≤ Z) (hoa : Sep l o a)
    (_ho32 : o % 32 = 0) (_ha32 : a % 32 = 0) :
    WP isa (.block (copyN l o a)) s fun t =>
      (∀ j < l.L, limb l t.mem B o j = limb l s.mem B a j) ∧ Outside B o l.NB s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR20, hNB, hL⟩ := PubOk.regs hl
  let xs : List (Nat × Nat) := (List.range l.R).map fun k => (a + 32 * k, o + 32 * k)
  have hxs : ∀ x ∈ xs, ∃ k < l.R, x = (a + 32 * k, o + 32 * k) := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  have hcode : copyN l o a = VG.Proof.Bignum.X86_64.Ifma.copyCode xs := by
    simp only [copyN, VG.Proof.Bignum.X86_64.Ifma.copyCode, xs, List.flatMap_map]
  rw [hcode]
  unfold Sep at hoa
  refine WP.mono (copies_ok hZ xs s hB hs (fun x hx => ?_) (fun x hx y hy => ?_))
    fun t ⟨hm, hg, hrd, hwr, hx⟩ => ⟨fun j hj => ?_, ?_, ⟨fun r _ => by rw [hg], hrd, hwr⟩, hx⟩
  · obtain ⟨k, hk, rfl⟩ := hxs x hx
    dsimp only; omega_using [ho, ha, hNB, hk]
  · obtain ⟨k, hk, rfl⟩ := hxs x hx
    obtain ⟨k', hk', rfl⟩ := hxs y hy
    dsimp only; omega_using [hoa, hNB, hk, hk', ho, ha]
  · have hk : j % l.R < l.R := Nat.mod_lt _ (by omega_using [hR])
    have ht : j / l.R < 4 := Nat.div_lt_of_lt_mul (by rw [hL] at hj; rw [Nat.mul_comm]; exact hj)
    have e := VG.Proof.Bignum.X86_64.AmmSym.word_wrList_unique B (e := o + 32 * (j % l.R)) (t := j / l.R)
      (v := s.mem.readW (off B (a + 32 * (j % l.R))) 256) ht (by omega_using [ho, hZ, hNB, hk])
      (xs.map fun x => (x.2, s.mem.readW (off B x.1) 256)) s.mem
      (List.mem_map.2 ⟨(a + 32 * (j % l.R), o + 32 * (j % l.R)), List.mem_map.2 ⟨j % l.R, List.mem_range.2 hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k', hk', rfl⟩ := hxs y hy
        dsimp only; omega_using [ho, hZ, hNB, hk', hk])
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k', hk', rfl⟩ := hxs y hy
        dsimp only at he ⊢
        rw [show k' = j % l.R by omega_using [he]])
    show (word t.mem B _).toNat = (word s.mem B _).toNat
    have ex := VG.X86_64.readW_extract s.mem (off B (a + 32 * (j % l.R))) (w := 256) (k := 8 * (j / l.R)) (n := 8)
      (by omega_using [ht])
    rw [hm, show o + l.off j = o + 32 * (j % l.R) + 8 * (j / l.R) by unfold Lay.off; omega_using [], e,
      show 64 * (j / l.R) = 8 * (8 * (j / l.R)) by omega_using []]
    refine congrArg BitVec.toNat (ex.trans ?_)
    rw [VG.Proof.Bignum.X86_64.AmmSym.off_add]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; omega_using [])
  · rw [hm]
    exact VG.Proof.Bignum.X86_64.AmmSym.wrList_outside' B (by omega_using [ho, hZ]) _ s.mem fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hxs y hy
      exact ⟨by dsimp only; omega_using [], by dsimp only; omega_using [hNB, hk]⟩

/-! ## `select`, a vector register at a time -/

/-- The table's entries, `S` and the word at `oV` lie in the area. -/
theorem PubOk.ends (hl : PubOk l) : (∀ j < 4, oT l j + l.NB ≤ size l) ∧ oS l + l.NB ≤ size l ∧
    oV l + 8 ≤ size l := by
  rcases hl with rfl | rfl | rfl <;> decide

section Sel

open VG.Proof.Bignum.X86_64.Ifma (qv vi vi_vreg vreg_vi vi_inj SRel sstep_ok ESym T T.eval)
open VG.Proof.Bignum.X86_64.AmmSym (Ctx Keeps G G.eval baseOff selMask selMask_and zero_or64 or_zero64)

private theorem vreg_inj {r k : Nat} (hr : r < 32) (hk : k < 32) : vreg r = vreg k ↔ r = k :=
  ⟨fun h => by rw [← vi_vreg r hr, h, vi_vreg k hk], fun h => h ▸ rfl⟩

private theorem keeps_trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.mxcsr.trans h₁.mxcsr, ⟨h₂.flags.1.trans h₁.flags.1, h₂.flags.2.1.trans h₁.flags.2.1,
      h₂.flags.2.2.1.trans h₁.flags.2.2.1, h₂.flags.2.2.2.trans h₁.flags.2.2.2⟩⟩

private theorem srel_keeps {σ : ESym} {s₀ s : State} (h : SRel σ s₀ s) : Keeps s₀ s :=
  ⟨fun _ hr => h.gpr hr, h.mem, h.rd, h.wr, h.mxcsr, h.flags⟩

private theorem ctx0 (s : State) : Ctx (fun _ => 0) s := fun _ _ _ hn hd => absurd (show _ ≤ 0 from hd) (by omega)

/-- `vpxorq d, d, d`. -/
private theorem vz_ok (d : VReg) (s : State) :
    ∃ s', exec (.eop (.bin .vpxorq d d d)) s = some s' ∧
      (∀ r q, q < 4 → qv s' r q = if r = d then 0 else qv s r q) ∧ Keeps s s' := by
  obtain ⟨s', hx, h⟩ := sstep_ok (ctx0 s) (SRel.init s) (i := .eop (.bin .vpxorq d d d))
    (σ' := ESym.init.set d .zero) (by simp only [ESym.step, ESym.eop, ite_true])
  refine ⟨s', hx, fun r q hq => ?_, srel_keeps h⟩
  rw [h.reg r q hq]
  simp only [ESym.set, ESym.init, Bool.cond_eq_ite, Nat.beq_eq, vi_inj]
  split
  · rfl
  · simp only [T.eval, vreg_vi]

/-- The accumulators' zeroing. -/
private theorem zeros_ok : ∀ K, K ≤ 32 → ∀ s : State,
    WP isa (.block ((List.range K).map fun k => .eop (.bin .vpxorq (vreg k) (vreg k) (vreg k)))) s fun t =>
      (∀ r < 32, ∀ q < 4, qv t (vreg r) q = if r < K then 0 else qv s (vreg r) q) ∧ Keeps s t
  | 0, _, s => WP.block_nil ⟨fun r _ q _ => by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | K + 1, hK, s => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zeros_ok K (by omega) s) fun t ⟨ht, kt⟩ => ?_
    obtain ⟨u, hx, hu, ku⟩ := vz_ok (vreg K) t
    rw [List.map_cons, List.map_nil, WP.block_cons_iff]
    refine ⟨u, hx, WP.block_nil ⟨fun r hr q hq => ?_, keeps_trans kt ku⟩⟩
    simp only [hu _ q hq, vreg_inj hr (show K < 32 by omega), ht r hr q hq]
    by_cases e : r = K
    · simp [e]
    · simp only [e, ite_false]
      by_cases h' : r < K
      · simp [h', show r < K + 1 by omega]
      · simp [h', show ¬ r < K + 1 by omega]

private theorem baseOff_at (b : Reg) (d : Nat) : baseOff (at_ b d) = some (b, d) := rfl

/-- One register's load and `vpternlogq`: `k |= [B + d] & R`. -/
private theorem pair_ok {s : State} {B : Addr} {Z R k d : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hd : d + 32 ≤ Z) (hk : k < R) (hR : R + 1 < 32) :
    WP isa (.block [.evLoad (vreg (R + 1)) (at_ .rbx d), .eop (.vpternlogq (vreg k) (vreg (R + 1)) (vreg R) 0xF8)]) s
      fun t => (∀ r < 32, r ≠ R + 1 → ∀ q < 4, qv t (vreg r) q =
        if r = k then qv s (vreg k) q ||| (s.mem.readW (off B (d + 8 * q)) 64 &&& qv s (vreg R) q)
        else qv s (vreg r) q) ∧ Keeps s t := by
  have hc : Ctx (fun b => if b = .rbx then Z else 0) s := fun b d' n hn hdn => by
    by_cases e : b = .rbx
    · subst e
      simp only [ite_true] at hdn
      rw [hB]
      exact let ⟨_, h, c⟩ := hs.region hdn hn; ⟨_, List.mem_append_right _ h, c⟩
    · simp only [e, ite_false] at hdn; omega
  obtain ⟨s₁, hx₁, h₁⟩ := sstep_ok hc (SRel.init s) (i := .evLoad (vreg (R + 1)) (at_ .rbx d))
    (σ' := ESym.init.set (vreg (R + 1)) (.ld .rbx d)) (by
      simp only [ESym.step, baseOff_at, Option.bind_some, ite_true, ne_eq, reduceCtorEq, not_false_eq_true,
        true_and, hd])
  obtain ⟨s₂, hx₂, h₂⟩ := sstep_ok hc h₁ (i := .eop (.vpternlogq (vreg k) (vreg (R + 1)) (vreg R) 0xF8)) rfl
  rw [WP.block_cons_iff]
  refine ⟨s₁, hx₁, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, hx₂, WP.block_nil ⟨fun r hr hr1 q hq => ?_, srel_keeps h₂⟩⟩
  rw [h₂.reg _ q hq, vi_vreg r hr]
  simp only [ESym.set, ESym.init, Bool.cond_eq_ite, Nat.beq_eq, vi_vreg k (by omega), vi_vreg R (by omega),
    vi_vreg (R + 1) hR, show k ≠ R + 1 by omega, show R ≠ R + 1 by omega, ite_false]
  by_cases e : r = k
  · subst e; simp only [ite_true, T.eval, hB]
  · simp only [e, hr1, ite_false, T.eval]

/-- One entry's loads, OR'ed in under the mask in register `R`. -/
private theorem pairs_ok {B : Addr} {Z R D : Nat} (hR : R + 1 < 32) (hZ : D + 32 * R ≤ Z) :
    ∀ K, K ≤ R → ∀ s : State, s.gpr .rbx = B → Scr s B Z →
      WP isa (.block ((List.range K).flatMap fun k => [.evLoad (vreg (R + 1)) (at_ .rbx (D + 32 * k)),
          .eop (.vpternlogq (vreg k) (vreg (R + 1)) (vreg R) 0xF8)])) s fun t =>
        (∀ r < R, ∀ q < 4, qv t (vreg r) q = if r < K then
          qv s (vreg r) q ||| (s.mem.readW (off B (D + 32 * r + 8 * q)) 64 &&& qv s (vreg R) q) else qv s (vreg r) q) ∧
        (∀ q < 4, qv t (vreg R) q = qv s (vreg R) q) ∧ Keeps s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun r _ q _ => by simp, fun _ _ => rfl,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | K + 1, hK, s, hB, hs => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (pairs_ok hR hZ K (by omega) s hB hs) fun t ⟨ht, htR, kt⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (pair_ok (k := K) (d := D + 32 * K) (by rw [kt.gpr _ (by decide)]; exact hB) (hs.congr kt.wr)
      (by omega) (by omega) hR) fun u ⟨hu, ku⟩ => ⟨fun r hr q hq => ?_, fun q hq => ?_, keeps_trans kt ku⟩
    · rw [hu r (by omega) (by omega) q hq, kt.mem, htR q hq]
      by_cases e : r = K
      · subst e; simp only [ite_true, ht r hr q hq, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
      · simp only [e, ite_false, ht r hr q hq]
        by_cases h' : r < K
        · simp [h', show r < K + 1 by omega]
        · simp [h', show ¬ r < K + 1 by omega]
    · rw [hu R (by omega) (by omega) q hq, ite_eq_right (by omega), htR q hq]

private theorem qv_eq {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) (hH : t.ymmH = s.ymmH)
    (r : VReg) (q : Nat) : qv t r q = qv s r q := by
  cases r <;> simp only [qv, State.vy, State.ymm, hx, hy, hH]

/-- The mask of entry `j` in register `R`, for `rdx = v`. -/
private theorem mask_ok {s : State} {R j v : Nat} (hR : R < 32) (hj : j < 4) (hv : v < 4)
    (hd : s.gpr .rdx = BitVec.ofNat 64 v) :
    WP isa (.block ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg R) .rax), .eop (.vpbroadcastq (vreg R) (vreg R))] : List Instr)) s
      fun t => (∀ q < 4, qv t (vreg R) q = selMask (decide (v = j))) ∧
        (∀ r < 32, r ≠ R → ∀ q < 4, qv t (vreg r) q = qv s (vreg r) q) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  rw [show ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg R) .rax), .eop (.vpbroadcastq (vreg R) (vreg R))] : List Instr) =
      ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax)] : List Instr) ++ [.eop (.vmovq (vreg R) .rax), .eop (.vpbroadcastq (vreg R) (vreg R))]
      from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun t => t.gpr .rax = selMask (decide (v = j)) ∧
    t.mem = s.mem ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.ymmH = s.ymmH ∧ t.mxcsr = s.mxcsr) (by
    xrun [hd, VG.Proof.Bignum.X86_64.AmmSym.se_ofNat (show j < 2 ^ 31 by omega)]
    and_intros
    any_goals rfl
    rw [VG.Proof.Bignum.X86_64.AmmSym.lt_one_iff, show decide (BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 j = 0) =
      decide (v = j) from decide_eq_decide.mpr (VG.Proof.Bignum.X86_64.AmmSym.xor_zero_iff.trans
        (VG.Proof.Bignum.X86_64.AmmSym.ofNat64_inj' (by omega) (by omega)))]
    cases decide (v = j) <;> rfl) rfl) fun t ⟨⟨ha, hm, hx, hy, hH, hmx⟩, kt⟩ => ?_
  obtain ⟨t₁, hx₁, h₁⟩ := sstep_ok (ctx0 t) (SRel.init t) (i := .eop (.vmovq (vreg R) .rax)) rfl
  obtain ⟨t₂, hx₂, h₂⟩ := sstep_ok (ctx0 t) h₁ (i := .eop (.vpbroadcastq (vreg R) (vreg R))) rfl
  rw [WP.block_cons_iff]
  refine ⟨t₁, hx₁, ?_⟩
  rw [WP.block_cons_iff]
  have k₂ := srel_keeps h₂
  refine ⟨t₂, hx₂, WP.block_nil ⟨fun q hq => ?_, fun r hr hrR q hq => ?_,
    ⟨fun r hr => (k₂.gpr r (by simpa using hr)).trans (kt.gpr hr), k₂.rd.trans kt.2.1, k₂.wr.trans kt.2.2⟩,
    k₂.mem.trans hm, k₂.mxcsr.trans hmx⟩⟩
  · rw [h₂.reg _ q hq, vi_vreg R hR]
    simp only [ESym.set, ESym.init, Bool.cond_eq_ite, Nat.beq_eq, vi_vreg R hR, ite_true, T.eval, G.eval, ha]
  · rw [h₂.reg _ q hq, vi_vreg r hr]
    simp only [ESym.set, ESym.init, Bool.cond_eq_ite, Nat.beq_eq, vi_vreg R hR, hrR, ite_false, T.eval]
    exact qv_eq hx hy hH _ q

/-- Entry `j` of the selection's loop body. -/
private def entryC (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (j : Nat) : List Instr :=
  ([.mov .rax (.reg .rdx), .alu .xor .rax (.imm (BitVec.ofNat 32 j)), .alu .cmp .rax (.imm 1),
      .alu .sbb .rax (.reg .rax), .eop (.vmovq (vreg l.R) .rax), .eop (.vpbroadcastq (vreg l.R) (vreg l.R))] :
        List Instr) ++
    (List.range l.R).flatMap fun k => [.evLoad (vreg (l.R + 1)) (at_ .rbx (oT l j + 32 * k)),
      .eop (.vpternlogq (vreg k) (vreg (l.R + 1)) (vreg l.R) 0xF8)]

/-- Entry `j`: OR'ed in if `j = v`. -/
private theorem entry_ok (hl : PubOk l) {s : State} {B : Addr} {j v : Nat} (hB : s.gpr .rbx = B)
    (hs : Scr s B (size l)) (hj : j < 4) (hv : v < 4) (hd : s.gpr .rdx = BitVec.ofNat 64 v) :
    WP isa (.block (entryC l j)) s fun t =>
      (∀ r < l.R, ∀ q < 4, qv t (vreg r) q =
        qv s (vreg r) q ||| (if v = j then s.mem.readW (off B (oT l j + 32 * r + 8 * q)) 64 else 0)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR20, hNB, hL⟩ := PubOk.regs hl
  have hT := (PubOk.ends hl).1 j hj
  unfold entryC
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok (R := l.R) (by omega) hj hv hd) fun t ⟨tm, tr, kt, mt, xt⟩ => ?_
  refine WP.mono (pairs_ok (B := B) (Z := size l) (D := oT l j) (by omega)
    (by omega) l.R (Nat.le_refl _) t (by rw [kt.gpr (by decide)]; exact hB)
    (hs.congr kt.2.2)) fun u ⟨hu, _, ku⟩ => ⟨fun r hr q hq => ?_,
      ⟨fun r hr => (ku.gpr r (by simpa using hr)).trans (kt.gpr hr), ku.rd.trans kt.2.1, ku.wr.trans kt.2.2⟩,
      ku.mem.trans mt, ku.mxcsr.trans xt⟩
  rw [hu r hr q hq, ite_eq_left hr, tm q hq, selMask_and, tr r (by omega) (by omega) q hq, mt]
  simp only [decide_eq_true_eq]

/-- The four entries, for `rdx = v`. -/
private theorem entries_ok (hl : PubOk l) {B : Addr} {v : Nat} (hv : v < 4) :
    ∀ J, J ≤ 4 → ∀ s : State, s.gpr .rbx = B → Scr s B (size l) → s.gpr .rdx = BitVec.ofNat 64 v →
      WP isa (.block ((List.range J).flatMap (entryC l))) s fun t =>
        (∀ r < l.R, ∀ q < 4, qv t (vreg r) q =
          qv s (vreg r) q ||| (if v < J then s.mem.readW (off B (oT l v + 32 * r + 8 * q)) 64 else 0)) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.mxcsr = s.mxcsr
  | 0, _, s, _, _, _ => WP.block_nil ⟨fun r _ q _ => by simp, ⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩
  | J + 1, hJ, s, hB, hs, hd => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (entries_ok hl hv J (by omega) s hB hs hd) fun t ⟨ht, kt, mt, xt⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (entry_ok hl (j := J) (by rw [kt.gpr (by decide)]; exact hB) (hs.congr kt.2.2) (by omega) hv
      (by rw [kt.gpr (by decide)]; exact hd)) fun u ⟨hu, ku, mu, xu⟩ => ⟨fun r hr q hq => ?_,
        (kt.trans ku).mono (by decide), mu.trans mt, xu.trans xt⟩
    rw [hu r hr q hq, ht r hr q hq, mt, BitVec.or_assoc]
    congr 1
    by_cases e : v = J
    · subst e; simp
    · simp only [e, ite_false, or_zero64]
      by_cases h' : v < J
      · simp [h', show v < J + 1 by omega]
      · simp [h', show ¬ v < J + 1 by omega]

end Sel

/-- `[S] := T_d`, `d` the top two bits of the word at `oV`. -/
theorem select_ok (hl : PubOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B)
    (hs : Scr s B (size l)) :
    WP isa (.block (select l)) s fun t =>
      (∀ j < l.L, limb l t.mem B (oS l) j =
        limb l s.mem B (oT l ((word s.mem B (oV l)).toNat / 2 ^ 62)) j) ∧
      Outside B (oS l) l.NB s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR20, hNB, hL⟩ := PubOk.regs hl
  obtain ⟨-, hsz, -⟩ := PubOk.offs hl
  obtain ⟨-, hSe, hVe⟩ := PubOk.ends hl
  generalize hv : (word s.mem B (oV l)).toNat / 2 ^ 62 = v
  have hv4 : v < 4 := by
    rw [← hv]
    exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq (word s.mem B (oV l)).isLt (by decide))
  unfold select
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 v ∧
      t.mem = s.mem ∧ t.mxcsr = s.mxcsr) (by
    have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (oV l)) 8 := hs.ld (by omega)
    xrun [VG.Proof.Bignum.X86_64.Ifma.ea_rG hB, hld]
    and_intros
    any_goals rfl
    apply BitVec.eq_of_toNat_eq
    rw [← hv]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      VG.Proof.Bignum.word, VG.Proof.Bignum.off]
    omega) rfl) fun t₁ ⟨⟨d₁, m₁, x₁⟩, k₁⟩ => ?_
  have hB₁ : t₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok l.R (by omega) t₁) fun t₂ ⟨z₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (entries_ok hl hv4 4 (Nat.le_refl _) t₂ (by rw [k₂.gpr _ (by decide)]; exact hB₁)
    ((hs.congr k₁.2.2).congr k₂.wr) (by rw [k₂.gpr _ (by decide)]; exact d₁)) fun t₃ ⟨a₃, k₃, m₃, x₃⟩ => ?_
  have hB₃ : t₃.gpr .rbx = B := by rw [k₃.gpr (by decide), k₂.gpr _ (by decide)]; exact hB₁
  have wr₃ : t₃.wr = s.wr := by rw [k₃.2.2, k₂.wr, k₁.2.2]
  have me₃ : t₃.mem = s.mem := by rw [m₃, k₂.mem, m₁]
  let Ls : List (Nat × VReg) := (List.range l.R).map fun k => (oS l + 32 * k, vreg k)
  rw [show ((List.range l.R).map fun k => Instr.evStore (at_ .rbx (oS l + 32 * k)) (vreg k)) =
    VG.Proof.Bignum.X86_64.Ifma.storeCode .rbx Ls by
      simp only [VG.Proof.Bignum.X86_64.Ifma.storeCode, Ls, List.map_map, Function.comp_def]]
  have hLs : ∀ x ∈ Ls, ∃ k < l.R, x = (oS l + 32 * k, vreg k) := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.Ifma.stores_gen Ls t₃ hB₃ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := hLs x hx
    rw [wr₃]; exact let ⟨_, h, c⟩ := hs.region (d := oS l + 32 * k) (n := 32) (by omega) (by decide);
      ⟨_, h, c⟩) fun t ht => ?_
  subst ht
  refine ⟨fun j hj => ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have hk : j % l.R < l.R := Nat.mod_lt _ (by omega)
    have hq : j / l.R < 4 := Nat.div_lt_of_lt_mul (by rw [hL] at hj; rw [Nat.mul_comm]; exact hj)
    have e := VG.Proof.Bignum.X86_64.AmmSym.word_wrList_unique B (e := oS l + 32 * (j % l.R)) (t := j / l.R)
      (v := t₃.vy (vreg (j % l.R))) hq (by omega)
      (Ls.map fun x => (x.1, t₃.vy x.2)) t₃.mem
      (List.mem_map.2 ⟨(oS l + 32 * (j % l.R), vreg (j % l.R)),
        List.mem_map.2 ⟨j % l.R, List.mem_range.2 hk, rfl⟩, rfl⟩)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := hLs y hy
        dsimp only; omega)
      (fun x hx he => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk', rfl⟩ := hLs y hy
        dsimp only at he ⊢
        rw [show k = j % l.R by omega])
    have qq := a₃ (j % l.R) hk (j / l.R) hq
    rw [z₂ _ (by omega) _ hq, ite_eq_left hk, ite_eq_left hv4, VG.Proof.Bignum.X86_64.AmmSym.zero_or64] at qq
    show (word (VG.Proof.Bignum.X86_64.AmmSym.wrList t₃.mem B _) B (oS l + l.off j)).toNat = _
    rw [show oS l + l.off j = oS l + 32 * (j % l.R) + 8 * (j / l.R) by unfold Lay.off; omega, e]
    refine congrArg BitVec.toNat (qq.trans ?_)
    rw [k₂.mem, m₁]
    exact congrArg (fun d => s.mem.readW (off B d) 64) (by unfold Lay.off; omega)
  · have o := VG.Proof.Bignum.X86_64.AmmSym.wrList_outside' B (o := oS l) (n := l.NB) (by omega)
      (Ls.map fun x => (x.1, t₃.vy x.2)) t₃.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨k, hk, rfl⟩ := hLs y hy
        exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    exact fun x hx => (o x hx).trans (congrFun me₃ x)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show t₃.gpr r = _
    rw [k₃.gpr (by simp [hr.1]), k₂.gpr _ hr.1, k₁.gpr (by simp [hr.2])]
  · show t₃.rd = _
    rw [k₃.2.1, k₂.rd, k₁.2.1]
  · exact wr₃
  · show t₃.mxcsr = _
    rw [x₃, k₂.mxcsr, x₁]

/-- The area before the table: the modulus, `T_0 = R' mod c`, `b R mod c` at
`T_1`, `K = 2^(104 S − 64 w) mod c` at `S`, `c − T_0`, `T_0 + c` and
`c − T_0 + c`, each with limbs below `2⁵²`. -/
structure Pre (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (c k bR : Nat) : Prop where
  mod : Mod l m B c k
  t0 : Canon l m B (oT l 0) ∧ val52 l m B (oT l 0) = 2 ^ (52 * l.S) % c
  t1 : Canon l m B (oT l 1) ∧ val52 l m B (oT l 1) = bR
  kk : Canon l m B (oS l) ∧ val52 l m B (oS l) = 2 ^ (104 * l.S - 64 * l.W) % c
  m1 : Canon l m B (oM1 l) ∧ val52 l m B (oM1 l) = c - 2 ^ (52 * l.S) % c
  p1c : Canon l m B (oP1c l) ∧ val52 l m B (oP1c l) = 2 ^ (52 * l.S) % c + c
  m1c : Canon l m B (oM1c l) ∧ val52 l m B (oM1c l) = c - 2 ^ (52 * l.S) % c + c

/-- The area through the windows: `Pre`'s constants, and the table
`T_j = b^j R'` in Montgomery form. -/
structure Tab (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (c k b : Nat) : Prop where
  mod : Mod l m B c k
  t : ∀ j < 4, Rep l m B c (oT l j) (b ^ j)
  t0 : val52 l m B (oT l 0) = 2 ^ (52 * l.S) % c
  m1 : Canon l m B (oM1 l) ∧ val52 l m B (oM1 l) = c - 2 ^ (52 * l.S) % c
  p1c : Canon l m B (oP1c l) ∧ val52 l m B (oP1c l) = 2 ^ (52 * l.S) % c + c
  m1c : Canon l m B (oM1c l) ∧ val52 l m B (oM1c l) = c - 2 ^ (52 * l.S) % c + c

/-- The table: `T_1 := T_1 K`, `T_2 := T_1²`, `T_3 := T_2 T_1`, for `T_1 = b R
mod c` on entry; `c` odd, `3 ≤ c`, `c < 2^(64 W)`. -/
theorem table_ok (hl : PubOk l) {s : State} {B : Addr} {c k b : Nat} (hB : s.gpr .rbx = B)
    (h12 : s.gpr .r12 = mask52) (hs : Scr s B (size l)) (hodd : c % 2 = 1) (h3 : 3 ≤ c)
    (hc : c < 2 ^ (64 * l.W)) (hp : Pre l s.mem B c k (b * 2 ^ (64 * l.W) % c)) :
    WP isa (table l) s fun t =>
      Tab l t.mem B c k b ∧ Frm B [(oT l 1, 3 * l.NB)] s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r13 →
        t.gpr r = s.gpr r) ∧
      t.gpr .r12 = mask52 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  sorry

end VG.Proof.MillerRabin.X86_64.Ifma
