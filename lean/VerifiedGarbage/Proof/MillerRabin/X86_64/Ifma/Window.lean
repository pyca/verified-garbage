module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Mult
public import VerifiedGarbage.Proof.MillerRabin.WindowK
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.Math

/-!
# The IFMA Miller–Rabin round: the windows

`y ≡ −1` and `y ≡ ±1` as limb-wise equalities with the constants
(`isM1_ok`, `isPM1_ok`); a window of 2 bits (`window_ok`, `WindowK.kWin`);
the last pass of three squarings (`last_ok`, `MrWindow.wEnd`); and the
windows of all of `E` (`windows_ok`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma (limb val52)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52 ammMul)
open VG.Impl.Rsa.X86_64.PubIfma (setOps arr)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.RsaKeyGen.X86_64.Candidate (aE)
open VG.Proof.RsaKeyGen (mrA mrE mrSig wEnd wSq)
open VG.Proof.MillerRabin.WindowK (kWin kRun)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- What holds through the windows of a run: the area at `B` (`rbx`, below
`2^63`, with `2⁵² − 1` in `r12`) and its constants and table (`Tab`), and the
words of `E` and the one after them in the workspace `H` (`rdi`), outside
the area. -/
structure WEnv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B H : Addr) (c k b : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = B
  rdi : s.gpr .rdi = H
  r12 : s.gpr .r12 = mask52
  scr : Scr s B (size l)
  tab : Tab l s.mem B c k b
  odd : c % 2 = 1
  three : 3 ≤ c
  lt : c < 2 ^ (64 * l.W)
  erd : ∀ i < l.W + 1, InRegions (s.rd ++ s.wr) (off H (arr l aE + 8 * i)) 8
  ev : wv s.mem H (arr l aE) l.W = mrE c
  el : word s.mem H (arr l aE + 8 * l.W) = BitVec.twoPow 64 (mrA c % 64)
  esep : ∀ i < l.W + 1, ∀ x < 8, size l ≤ ofs B (off H (arr l aE + 8 * i) + BitVec.ofNat 64 x)


/-! ## Masks -/

theorem mask_or' (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

theorem mask_and' (a b : Bool) : mask a &&& mask b = mask (a && b) := by cases a <;> cases b <;> decide

theorem mask_xor1 (c : Bool) : mask c ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = mask (!c) := by
  cases c <;> decide

/-! ## Numbers equal limb by limb -/

theorem lval_inj {L L' : Nat → Nat} : ∀ n, (∀ j < n, L j < 2 ^ 52) → (∀ j < n, L' j < 2 ^ 52) →
    lval L n = lval L' n → ∀ j < n, L j = L' j
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, h', he, j, hj => by
    rw [lval_succ, lval_succ] at he
    have a := lval_lt (n := n) fun j hj => h j (by omega_arith)
    have a' := lval_lt (n := n) fun j hj => h' j (by omega_arith)
    have hP : 0 < 2 ^ (52 * n) := Nat.two_pow_pos _
    have e1 : lval L n = lval L' n := by
      have := congrArg (· % 2 ^ (52 * n)) he
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt a'] at this
      exact this
    have e2 : L n = L' n := by
      have := congrArg (· / 2 ^ (52 * n)) he
      simp only [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt a, Nat.div_eq_of_lt a', Nat.zero_add] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact lval_inj n (fun j hj => h j (by omega_arith)) (fun j hj => h' j (by omega_arith)) e1 j hj
    · exact e2

theorem limbs_eq_iff {m : Mem} {B : Addr} {o o' : Nat} (h : Canon l m B o) (h' : Canon l m B o') :
    (∀ j < l.L, limb l m B o j = limb l m B o' j) ↔ val52 l m B o = val52 l m B o' :=
  ⟨fun e => lval_congr e, fun e => lval_inj l.L h h' e⟩

/-! ## `y ≡ t` from the value of `Y` -/

/-- A value below `2 c` standing for `x < c` is `t R mod c` or that plus `c`
iff `x = t`. -/
theorem rep_eq_iff {v x t c R : Nat} (hR : Nat.Coprime R c) (hv : v < 2 * c) (hvx : v % c = x * R % c)
    (hx : x < c) (ht : t < c) : (v = t * R % c ∨ v = t * R % c + c) ↔ x = t := by
  have hc : 0 < c := by omega_arith
  constructor
  · intro h
    have hm : v % c = t * R % c := by
      rcases h with h | h
      · rw [h, Nat.mod_mod]
      · rw [h, Nat.add_mod_right, Nat.mod_mod]
    have := VG.Proof.Bignum.mont_cancel hR (by rw [← hvx, hm])
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt ht] at this
  · rintro rfl
    have h1 := Nat.mod_add_div v c
    have h2 : v / c < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hv)
    rw [hvx] at h1
    generalize x * R % c = a at h1 ⊢
    generalize v / c = q at h1 h2
    rcases (by omega_arith : q = 0 ∨ q = 1) with rfl | rfl
    · left; omega_arith
    · right; omega_arith

/-- `(c − 1) R mod c = c − R mod c`, for `R` invertible modulo `c ≥ 2`. -/
theorem m1_eq {c R : Nat} (hR : Nat.Coprime R c) (hc : 2 ≤ c) : (c - 1) * R % c = c - R % c := by
  have hr : R % c ≠ 0 := fun h => by
    have := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
    rw [hR.gcd_eq_one] at this; omega_arith
  have hrl : R % c < c := Nat.mod_lt _ (by omega_arith)
  have hal : (c - 1) * R % c < c := Nat.mod_lt _ (by omega_arith)
  have e : ((c - 1) * R % c + R % c) % c = 0 := by
    rw [← Nat.add_mod, show (c - 1) * R + R = c * R by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega_arith)]]
    exact Nat.mul_mod_right c R
  generalize (c - 1) * R % c = a at e hal ⊢
  generalize R % c = r at e hr hrl ⊢
  have hge : c ≤ a + r := by
    rcases Nat.lt_or_ge (a + r) c with h | h
    · rw [Nat.mod_eq_of_lt h] at e; omega_arith
    · exact h
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega_arith)] at e
  omega_arith

/-- The constants of `Tab` as `t R' mod c` (and that plus `c`). -/
theorem tab_vals {m : Mem} {B : Addr} {c k b : Nat} (h : Tab l m B c k b) (hodd : c % 2 = 1) (h3 : 3 ≤ c) :
    val52 l m B (oM1 l) = (c - 1) * 2 ^ (52 * l.S) % c ∧
    val52 l m B (oM1c l) = (c - 1) * 2 ^ (52 * l.S) % c + c ∧
    val52 l m B (oT l 0) = 1 * 2 ^ (52 * l.S) % c ∧
    val52 l m B (oP1c l) = 1 * 2 ^ (52 * l.S) % c + c := by
  have e := m1_eq (VG.Proof.Bignum.coprime_pow2 hodd (52 * l.S)) (by omega_arith)
  rw [h.m1.2, h.m1c.2, h.t0, h.p1c.2, e, Nat.one_mul]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `Y` against the constants. -/
theorem yeq_iff {m : Mem} {B : Addr} {c k b y : Nat} (h : Tab l m B c k b) (hodd : c % 2 = 1) (h3 : 3 ≤ c)
    (hy : Rep l m B c (oY l) y) (hyc : y < c) :
    ((∀ j < l.L, limb l m B (oY l) j = limb l m B (oM1 l) j) ∨
      (∀ j < l.L, limb l m B (oY l) j = limb l m B (oM1c l) j) ↔ y = c - 1) ∧
    ((∀ j < l.L, limb l m B (oY l) j = limb l m B (oT l 0) j) ∨
      (∀ j < l.L, limb l m B (oY l) j = limb l m B (oP1c l) j) ↔ y = 1) := by
  obtain ⟨v1, v2, v3, v4⟩ := tab_vals h hodd h3
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (52 * l.S)
  rw [limbs_eq_iff hy.1 h.m1.1, limbs_eq_iff hy.1 h.m1c.1, limbs_eq_iff hy.1 (h.t 0 (by decide)).1,
    limbs_eq_iff hy.1 h.p1c.1, v1, v2, v3, v4]
  exact ⟨rep_eq_iff hR hy.2.1 hy.2.2 hyc (by omega_arith), rep_eq_iff hR hy.2.1 hy.2.2 hyc (by omega_arith)⟩

/-! ## `y ≡ −1` and `y ≡ ±1` -/

/-- `eqN k` and `op rdx, rcx` (`mov` or `or`). -/
theorem eqOp_ok (hl : PubOk l) {s : State} {B : Addr} {k : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B (size l))
    (hk : k + l.NB ≤ size l) (op : List Instr) {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hop : ∀ u : State, WP isa (.block op) u fun t => t.gpr .rdx = f (u.gpr .rdx) (u.gpr .rcx) ∧
      t.mem = u.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] u t ∧ t.mxcsr = u.mxcsr) :
    WP isa (.block (eqN l k ++ op)) s fun t =>
      t.gpr .rdx = f (s.gpr .rdx) (mask (decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B k j))) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  have o := hl.offs
  rw [WP.block_append_iff]
  refine WP.mono (eqN_ok hl hB hs (by omega_arith) hk o.2.1) fun t ⟨hc, hm, kt, hx⟩ => ?_
  refine WP.mono (hop t) fun u ⟨hd, hmu, ku, hxu⟩ => ⟨?_, hmu.trans hm, (kt.trans ku).mono (by decide),
    hxu.trans hx⟩
  rw [hd, hc, kt.gpr (by decide)]

theorem movDC_ok (u : State) : WP isa (.block [.mov .rdx (.reg .rcx)]) u fun t =>
    t.gpr .rdx = (fun _ c => c) (u.gpr .rdx) (u.gpr .rcx) ∧ t.mem = u.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rdx] u t ∧ t.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun t => t.gpr .rdx = u.gpr .rcx ∧
    t.mem = u.mem ∧ t.mxcsr = u.mxcsr) (by xrun [RegUpd.mxcsr_setReg]) rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩

theorem orDC_ok (u : State) : WP isa (.block [.alu .or .rdx (.reg .rcx)]) u fun t =>
    t.gpr .rdx = (fun a c => a ||| c) (u.gpr .rdx) (u.gpr .rcx) ∧ t.mem = u.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rdx] u t ∧ t.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rdx] (Q := fun t => t.gpr .rdx = u.gpr .rdx ||| u.gpr .rcx ∧
    t.mem = u.mem ∧ t.mxcsr = u.mxcsr) (by xrun [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩

/-- The two equalities of `isM1`, as masks. -/
theorem isM1_mask (hl : PubOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (size l)) :
    WP isa (.block (isM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B (oM1 l) j) ||
        decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B (oM1c l) j)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  have o := hl.offs
  unfold isM1
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (eqOp_ok hl hB hs (by omega_arith) _ movDC_ok) fun t ⟨hd, hm, kt, hx⟩ => ?_
  refine WP.mono (eqOp_ok hl ((kt.gpr (by decide)).trans hB) (hs.congr kt.2.2) (k := oM1c l) (by omega_arith) _ orDC_ok)
    fun u ⟨hd', hm', ku, hx'⟩ => ⟨?_, hm'.trans hm, (kt.trans ku).mono (by decide), hx'.trans hx⟩
  rw [hd', hd, hm, mask_or']

theorem decide_or_iff {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : p ∨ q ↔ r) :
    (decide p || decide q) = decide r := by
  by_cases hr : r
  · rw [decide_eq_true hr]; rcases h.mpr hr with h | h <;> simp [h]
  · rw [decide_eq_false hr]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨fun hp => hr (h.mp (.inl hp)), fun hq => hr (h.mp (.inr hq))⟩

/-! ## What the windows keep -/

/-- A number outside `Y`, `S` and the word at `oV`. -/
def Away (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o : Nat) : Prop :=
  o + l.NB ≤ oY l ∨ (oY l + 2 * l.NB ≤ o ∧ o + l.NB ≤ oV l)

/-- The ranges the windows change. -/
abbrev wrs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × Nat) := [(oY l, 2 * l.NB), (oV l, 8)]

theorem word_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {d : Nat}
    (hd : d + 8 ≤ oY l ∨ (oY l + 2 * l.NB ≤ d ∧ d + 8 ≤ oV l)) : word m' B d = word m B d := by
  have o := hl.offs
  refine f.word_eq (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only <;> omega_arith

theorem limb_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o) :
    ∀ j < l.L, limb l m' B o j = limb l m B o j := fun j hj => by
  have := off_ltN hl.amm hj
  simp only [limb]
  unfold Away at ho
  rw [word_frm hl f (by omega_arith)]

theorem canon_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o)
    (h : Canon l m B o) : Canon l m' B o := fun j hj => by rw [limb_frm hl f ho j hj]; exact h j hj

theorem val_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o) :
    val52 l m' B o = val52 l m B o := lval_congr (limb_frm hl f ho)

theorem rep_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o c x : Nat} (ho : Away l o)
    (h : Rep l m B c o x) : Rep l m' B c o x :=
  ⟨canon_frm hl f ho h.1, by rw [val_frm hl f ho]; exact h.2.1, by rw [val_frm hl f ho]; exact h.2.2⟩

theorem away (hl : PubOk l) : Away l 0 ∧ (∀ j < 4, Away l (oT l j)) ∧ Away l (oP1c l) ∧ Away l (oM1 l) ∧
    Away l (oM1c l) := by
  unfold Away
  rcases hl with rfl | rfl | rfl <;> decide

theorem tab_frm (hl : PubOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {c k b : Nat}
    (h : Tab l m B c k b) : Tab l m' B c k b := by
  obtain ⟨a0, aT, aP, aM, aMc⟩ := away hl
  have o := hl.offs
  have hm := h.mod
  refine ⟨⟨fun j hj => by rw [limb_frm hl f a0 j hj]; exact hm.lt j hj, by rw [val_frm hl f a0]; exact hm.val,
    fun t ht => by rw [word_frm hl f (by simp only [Lay.oK0]; omega_arith)]; exact hm.k0 t ht, hm.klt,
    by rw [limb_frm hl f a0 0 (by simp only [Lay.L]; have := hl.amm.bounds.1; omega_arith)]; exact hm.inv, hm.big⟩,
    fun j hj => rep_frm hl f (aT j hj) (h.t j hj), by rw [val_frm hl f (aT 0 (by decide))]; exact h.t0,
    ⟨canon_frm hl f aM h.m1.1, by rw [val_frm hl f aM]; exact h.m1.2⟩,
    ⟨canon_frm hl f aP h.p1c.1, by rw [val_frm hl f aP]; exact h.p1c.2⟩,
    ⟨canon_frm hl f aMc h.m1c.1, by rw [val_frm hl f aMc]; exact h.m1c.2⟩⟩

theorem hword_frm (hl : PubOk l) {B H : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {d : Nat}
    (hd : ∀ x < 8, size l ≤ ofs B (off H d + BitVec.ofNat 64 x)) : word m' H d = word m H d := by
  have o := hl.offs
  refine Mem.readW_congr fun i hi => f _ fun r hr => ?_
  have := hd i (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [size] at this ⊢ <;> omega_arith

/-- `WEnv` through a change of `Y`, `S` and the word at `oV`. -/
theorem WEnv.frame (hl : PubOk l) {s t : State} {B H : Addr} {c k b : Nat} (h : WEnv l B H c k b s)
    (hbx : t.gpr .rbx = B) (hdi : t.gpr .rdi = H) (h12 : t.gpr .r12 = mask52) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (f : Frm B (wrs l) s.mem t.mem) : WEnv l B H c k b t := by
  refine ⟨hbx, hdi, h12, h.scr.congr hwr, tab_frm hl f h.tab, h.odd, h.three, h.lt,
    fun i hi => by rw [hrd, hwr]; exact h.erd i hi, ?_, ?_, h.esep⟩
  · rw [← h.ev]
    exact VG.Proof.Bignum.wv_congr fun i hi => hword_frm hl f (h.esep i (by omega_arith))
  · rw [hword_frm hl f (h.esep l.W (by omega_arith))]; exact h.el

set_option warningAsError false

/-- `rdx := mask (y = c − 1)` for `Y` standing for `y < c`. -/
theorem isM1_ok (hl : PubOk l) {s : State} {B H : Addr} {c k b y : Nat} (h : WEnv l B H c k b s)
    (hy : Rep l s.mem B c (oY l) y) (hyc : y < c) :
    WP isa (.block (isM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (y = c - 1)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (isM1_mask hl h.rbx h.scr) fun t ⟨hd, hm, k', hx⟩ => ⟨?_, hm, k', hx⟩
  rw [hd, decide_or_iff (yeq_iff h.tab h.odd h.three hy hyc).1]

/-- `rdx := mask (y = 1 ∨ y = c − 1)`. -/
theorem isPM1_ok (hl : PubOk l) {s : State} {B H : Addr} {c k b y : Nat} (h : WEnv l B H c k b s)
    (hy : Rep l s.mem B c (oY l) y) (hyc : y < c) :
    WP isa (.block (isPM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (y = 1) || decide (y = c - 1)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  have o := hl.offs
  have e := yeq_iff h.tab h.odd h.three hy hyc
  unfold isPM1
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (isM1_mask hl h.rbx h.scr) fun t ⟨hd, hm, kt, hx⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  have hBt := (kt.gpr (by decide)).trans h.rbx
  refine WP.mono (eqOp_ok hl hBt (h.scr.congr kt.2.2) (k := oT l 0) (by omega_arith) _ orDC_ok)
    fun u ⟨hd', hm', ku, hx'⟩ => ?_
  refine WP.mono (eqOp_ok hl ((ku.gpr (by decide)).trans hBt) (h.scr.congr (ku.2.2.trans kt.2.2)) (k := oP1c l)
    (by omega_arith) _ orDC_ok) fun v ⟨hd'', hm'', kv, hx''⟩ =>
    ⟨?_, hm''.trans (hm'.trans hm), ((kt.trans ku).trans kv).mono (by decide), hx''.trans (hx'.trans hx)⟩
  simp only at hd hd' hd''
  rw [hd'', hd', hd, hm', hm, mask_or', mask_or', Bool.or_assoc, decide_or_iff e.2, decide_or_iff e.1,
    Bool.or_comm]

/-- A window of a word of `E` (`r15 ≠ 0`), its digit `d` the top two bits of
the word at `oV`, from `y < c` in `Y` and the flag `P` in `rbp`: `kWin`'s
result, the word shifted by two bits, and `r14` decremented (ZF if it
reaches 0). -/
theorem window_ok (hl : PubOk l) {s : State} {B H : Addr} {c k b y n : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : s.gpr .rbp = mask P) (h15 : s.gpr .r15 ≠ 0) (h14 : s.gpr .r14 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n ≤ 32) :
    WP isa (window l) s fun t =>
      WEnv l B H c k b t ∧
      Rep l t.mem B c (oY l) (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 ∧
      (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 < c ∧
      t.gpr .rbp = mask (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).2 ∧
      word t.mem B (oV l) = word s.mem B (oV l) <<< 2 ∧
      t.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ t.zf = some (decide (n - 1 = 0)) ∧
      t.gpr .r15 = s.gpr .r15 ∧ t.gpr .rsp = s.gpr .rsp ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8)] s.mem t.mem := by
  sorry

/-- The last pass (`r15 = 0`): one window of three squarings, `wEnd`. -/
theorem last_ok (hl : PubOk l) {s : State} {B H : Addr} {c k b y : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : s.gpr .rbp = mask P) (h15 : s.gpr .r15 = 0) (h14 : s.gpr .r14 = 1) :
    WP isa (window l) s fun t =>
      t.gpr .rbp = mask (wEnd c (y, P)).2 ∧ t.gpr .r15 = 0 ∧ t.zf = some true ∧
      t.gpr .rbx = B ∧ t.gpr .rdi = H ∧ t.gpr .rsp = s.gpr .rsp ∧ t.gpr .r12 = mask52 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8)] s.mem t.mem := by
  sorry

/-- The windows of `E`, from `y := T_0` and a clear flag, and the last pass:
`rbp` is the mask of `mrIteration`'s result by windows of 2 bits. -/
theorem windows_ok (hl : PubOk l) {s : State} {B H : Addr} {c k b : Nat} (h : WEnv l B H c k b s) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (windows l)) s fun t =>
      t.gpr .rbp = mask (wEnd c (kRun 2 c b (mrE c) (32 * l.W) (32 * l.W))).2 ∧
      t.gpr .rbx = B ∧ t.gpr .rdi = H ∧ t.gpr .rsp = s.gpr .rsp ∧ t.gpr .r12 = mask52 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8)] s.mem t.mem := by
  sorry

end VG.Proof.MillerRabin.X86_64.Ifma
