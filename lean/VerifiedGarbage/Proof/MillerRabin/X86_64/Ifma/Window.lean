module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Mult
public import VerifiedGarbage.Proof.MillerRabin.WindowK
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

-- separate module: the windows, built in parallel with the setup's proofs (Setup.lean), which do not depend on them

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
open VG.Proof.Bignum.X86_64.Ifma.Pub (Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52 ammMul at_)
open VG.Impl.Rsa.X86_64.PubIfma (setOps arr)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.RsaKeyGen.X86_64.Candidate (aE sigK)
open VG.Proof.MlKem.X86_64 (Keep ifp ifn)
open VG.Proof.RsaKeyGen (mrA mrE mrSig wEnd wSq sqs)
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


/-! ## The layout -/

theorem MrOk.lay (hl : MrOk l) : size l < 2 ^ 31 ∧ oY l = l.NB + 32 ∧ oS l = oY l + l.NB ∧
    oT l 0 = oS l + l.NB ∧ oP1c l = oT l 0 + 4 * l.NB ∧ oM1 l = oP1c l + l.NB ∧ oM1c l = oM1 l + l.NB ∧
    oV l = oM1c l + l.NB ∧ oF l = oV l + 16 ∧ size l = oF l + 8 ∧ 32 ≤ l.NB ∧ l.NB % 32 = 0 ∧ l.W < 2 ^ 31 ∧
    l.NB + 32 ≤ size l := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> decide

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
    have := VG.Proof.Bignum.mont_cancel (o := x) (c := t) hR (by rw [← hvx, hm])
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
theorem eqOp_ok (hl : MrOk l) {s : State} {B : Addr} {k : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B (size l))
    (hk : k + l.NB ≤ size l) (op : List Instr) {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hop : ∀ u : State, WP isa (.block op) u fun t => t.gpr .rdx = f (u.gpr .rdx) (u.gpr .rcx) ∧
      t.mem = u.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rdx] u t ∧ t.mxcsr = u.mxcsr) :
    WP isa (.block (eqN l k ++ op)) s fun t =>
      t.gpr .rdx = f (s.gpr .rdx) (mask (decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B k j))) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  rw [WP.block_append_iff]
  refine WP.mono (eqN_ok hl hB hs (by omega_arith) hk z0) fun t ⟨hc, hm, kt, hx⟩ => ?_
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
theorem isM1_mask (hl : MrOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (size l)) :
    WP isa (.block (isM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B (oM1 l) j) ||
        decide (∀ j < l.L, limb l s.mem B (oY l) j = limb l s.mem B (oM1c l) j)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  unfold isM1
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (eqOp_ok hl hB hs (by omega_arith) _ (f := fun _ c => c) movDC_ok) fun t ⟨hd, hm, kt, hx⟩ => ?_
  refine WP.mono (eqOp_ok hl ((kt.gpr (by decide)).trans hB) (hs.congr kt.2.2) (k := oM1c l) (by omega_arith) _ (f := fun a c => a ||| c) orDC_ok)
    fun u ⟨hd', hm', ku, hx'⟩ => ⟨?_, hm'.trans hm, (kt.trans ku).mono (by decide), hx'.trans hx⟩
  rw [hd', hd, hm, mask_or']

theorem decide_or_iff {p q r : Prop} [Decidable p] [Decidable q] [Decidable r] (h : p ∨ q ↔ r) :
    (decide p || decide q) = decide r := by
  by_cases hr : r
  · rw [decide_eq_true hr]; rcases h.mpr hr with h | h <;> simp [h]
  · rw [decide_eq_false hr]; simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨fun hp => hr (h.mp (.inl hp)), fun hq => hr (h.mp (.inr hq))⟩

/-! ## What the windows keep -/

/-- A number outside `Y`, `S`, the word at `oV` and the flag. -/
def Away (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (o : Nat) : Prop :=
  o + l.NB ≤ oY l ∨ (oY l + 2 * l.NB ≤ o ∧ o + l.NB ≤ oV l)

/-- The ranges the windows change. -/
abbrev wrs (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × Nat) :=
  [(oY l, 2 * l.NB), (oV l, 8), (oF l, 8)]

theorem mem_wrs1 : (oY l, 2 * l.NB) ∈ wrs l := List.mem_cons_self ..
theorem mem_wrs2 : (oV l, 8) ∈ wrs l := List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_wrs3 : (oF l, 8) ∈ wrs l := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem word_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {d : Nat}
    (hd : d + 8 ≤ oY l ∨ (oY l + 2 * l.NB ≤ d ∧ d + 8 ≤ oV l)) : word m' B d = word m B d := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  refine f.word_eq (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith

theorem wlimb_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o) :
    ∀ j < l.L, limb l m' B o j = limb l m B o j := fun j hj => by
  have := VG.Proof.Bignum.X86_64.Ifma.off_ltN hl.amm hj
  simp only [limb]
  unfold Away at ho
  rw [word_frm hl f (by omega_arith)]

theorem canon_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o)
    (h : Canon l m B o) : Canon l m' B o := fun j hj => by rw [wlimb_frm hl f ho j hj]; exact h j hj

theorem val_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o : Nat} (ho : Away l o) :
    val52 l m' B o = val52 l m B o := lval_congr (wlimb_frm hl f ho)

theorem rep_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {o c x : Nat} (ho : Away l o)
    (h : Rep l m B c o x) : Rep l m' B c o x :=
  ⟨canon_frm hl f ho h.1, by rw [val_frm hl f ho]; exact h.2.1, by rw [val_frm hl f ho]; exact h.2.2⟩

theorem away (hl : MrOk l) : Away l 0 ∧ (∀ j < 4, Away l (oT l j)) ∧ Away l (oP1c l) ∧ Away l (oM1 l) ∧
    Away l (oM1c l) := by
  unfold Away
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> decide

theorem tab_frm (hl : MrOk l) {B : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {c k b : Nat}
    (h : Tab l m B c k b) : Tab l m' B c k b := by
  obtain ⟨a0, aT, aP, aM, aMc⟩ := away hl
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hm := h.mod
  refine ⟨⟨fun j hj => by rw [wlimb_frm hl f a0 j hj]; exact hm.lt j hj, by rw [val_frm hl f a0]; exact hm.val,
    fun t ht => by rw [word_frm hl f (by simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.oK0]; omega_arith)]; exact hm.k0 t ht, hm.klt,
    by rw [wlimb_frm hl f a0 0 (by simp only [VG.Impl.Rsa.X86_64.CrtIfma.Lay.L]; have := hl.amm.bounds.1; omega_arith)]; exact hm.inv, hm.big⟩,
    fun j hj => rep_frm hl f (aT j hj) (h.t j hj), by rw [val_frm hl f (aT 0 (by decide))]; exact h.t0,
    ⟨canon_frm hl f aM h.m1.1, by rw [val_frm hl f aM]; exact h.m1.2⟩,
    ⟨canon_frm hl f aP h.p1c.1, by rw [val_frm hl f aP]; exact h.p1c.2⟩,
    ⟨canon_frm hl f aMc h.m1c.1, by rw [val_frm hl f aMc]; exact h.m1c.2⟩⟩

theorem hword_frm (hl : MrOk l) {B H : Addr} {m m' : Mem} (f : Frm B (wrs l) m m') {d : Nat}
    (hd : ∀ x < 8, size l ≤ ofs B (off H d + BitVec.ofNat 64 x)) : word m' H d = word m H d := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  refine Mem.readW_congr fun i hi => f _ fun r hr => ?_
  have := hd i (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith

/-- `WEnv` through a change of `Y`, `S`, the word at `oV` and the flag. -/
theorem WEnv.frame (hl : MrOk l) {s t : State} {B H : Addr} {c k b : Nat} (h : WEnv l B H c k b s)
    (hbx : t.gpr .rbx = B) (hdi : t.gpr .rdi = H) (h12 : t.gpr .r12 = mask52) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (f : Frm B (wrs l) s.mem t.mem) : WEnv l B H c k b t := by
  refine ⟨hbx, hdi, h12, h.scr.congr hwr, tab_frm hl f h.tab, h.odd, h.three, h.lt,
    fun i hi => by rw [hrd, hwr]; exact h.erd i hi, ?_, ?_, h.esep⟩
  · rw [← h.ev]
    exact VG.Proof.Bignum.wv_congr fun i hi => hword_frm hl f (h.esep i (by omega_arith))
  · rw [hword_frm hl f (h.esep l.W (by omega_arith))]; exact h.el

/-- `WEnv` through a change of registers outside it. -/
theorem WEnv.keep (hl : MrOk l) {s t : State} {B H : Addr} {c k b : Nat} {rs : List Reg} (h : WEnv l B H c k b s)
    (hk : Keep rs s t) (hb : .rbx ∉ rs) (hd : .rdi ∉ rs) (h12 : .r12 ∉ rs) (hm : t.mem = s.mem) :
    WEnv l B H c k b t :=
  h.frame hl ((hk.gpr hb).trans h.rbx) ((hk.gpr hd).trans h.rdi) ((hk.gpr h12).trans h.r12) hk.2.1 hk.2.2
    (by rw [hm]; exact Frm.refl _ _ _)

/-! ## Numbers through stores elsewhere -/

theorem wlimb_out (hl : MrOk l) {B : Addr} {m m' : Mem} {o' n o : Nat} (f : Outside B o' n m m')
    (ho : o + l.NB ≤ o' ∨ o' + n ≤ o) (hb : o + l.NB ≤ 2 ^ 63) :
    ∀ j < l.L, limb l m' B o j = limb l m B o j := fun j hj => by
  have := VG.Proof.Bignum.X86_64.Ifma.off_ltN hl.amm hj
  simp only [limb]
  rw [f.word (by omega_arith) (by omega_arith)]

theorem wrep_out (hl : MrOk l) {B : Addr} {m m' : Mem} {o' n o c x : Nat} (f : Outside B o' n m m')
    (ho : o + l.NB ≤ o' ∨ o' + n ≤ o) (hb : o + l.NB ≤ 2 ^ 63) (h : Rep l m B c o x) : Rep l m' B c o x := by
  have e : val52 l m' B o = val52 l m B o := lval_congr (wlimb_out hl f ho hb)
  exact ⟨fun j hj => by rw [wlimb_out hl f ho hb j hj]; exact h.1 j hj, by rw [e]; exact h.2.1, by rw [e]; exact h.2.2⟩

theorem rep_congr {m : Mem} {B : Addr} {c o x x' : Nat} (h : Rep l m B c o x) (e : x % c = x' % c) :
    Rep l m B c o x' :=
  ⟨h.1, h.2.1, by rw [h.2.2, Nat.mul_mod, e, ← Nat.mul_mod]⟩

theorem rep_limbs {m m' : Mem} {B : Addr} {c o a x : Nat} (e : ∀ j < l.L, limb l m' B o j = limb l m B a j)
    (h : Rep l m B c a x) : Rep l m' B c o x := by
  have ev : val52 l m' B o = val52 l m B a := lval_congr e
  exact ⟨fun j hj => by rw [e j hj]; exact h.1 j hj, by rw [ev]; exact h.2.1, by rw [ev]; exact h.2.2⟩

/-- `rdx := mask (y = c − 1)` for `Y` standing for `y < c`. -/
theorem isM1_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y : Nat} (h : WEnv l B H c k b s)
    (hy : Rep l s.mem B c (oY l) y) (hyc : y < c) :
    WP isa (.block (isM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (y = c - 1)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  refine WP.mono (isM1_mask hl h.rbx h.scr) fun t ⟨hd, hm, k', hx⟩ => ⟨?_, hm, k', hx⟩
  rw [hd, decide_or_iff (yeq_iff h.tab h.odd h.three hy hyc).1]

/-- `rdx := mask (y = 1 ∨ y = c − 1)`. -/
theorem isPM1_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y : Nat} (h : WEnv l B H c k b s)
    (hy : Rep l s.mem B c (oY l) y) (hyc : y < c) :
    WP isa (.block (isPM1 l)) s fun t =>
      t.gpr .rdx = mask (decide (y = 1) || decide (y = c - 1)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] s t ∧ t.mxcsr = s.mxcsr := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have e := yeq_iff h.tab h.odd h.three hy hyc
  unfold isPM1
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (isM1_mask hl h.rbx h.scr) fun t ⟨hd, hm, kt, hx⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  have hBt := (kt.gpr (by decide)).trans h.rbx
  refine WP.mono (eqOp_ok hl hBt (h.scr.congr kt.2.2) (k := oT l 0) (by omega_arith) _ (f := fun a c => a ||| c) orDC_ok)
    fun u ⟨hd', hm', ku, hx'⟩ => ?_
  refine WP.mono (eqOp_ok hl ((ku.gpr (by decide)).trans hBt) (h.scr.congr (ku.2.2.trans kt.2.2)) (k := oP1c l)
    (by omega_arith) _ (f := fun a c => a ||| c) orDC_ok) fun v ⟨hd'', hm'', kv, hx''⟩ =>
    ⟨?_, hm''.trans (hm'.trans hm), ((kt.trans ku).trans kv).mono (by decide), hx''.trans (hx'.trans hx)⟩
  rw [hd'', hd', hd, hm', hm, mask_or', mask_or', Bool.or_assoc, decide_or_iff e.2, decide_or_iff e.1,
    Bool.or_comm]


/-! ## Single blocks -/

theorem ea_at'' (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem wtail_ok {t : State} {B : Addr} {o n : Nat} (hB : t.gpr .rbx = B)
    (hld : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 o) 8) (hst : InRegions t.wr (B + BitVec.ofNat 64 o) 8)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 63) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx o)), .shift .shl .rax 2, .store (at_ .rbx o) .rax,
      .alu .sub .r14 (.imm 1)]) t fun u =>
      u.mem = t.mem.writeW (off B o) (word t.mem B o <<< 2) ∧ u.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧
      u.zf = some (decide (n - 1 = 0)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r14] t u ∧ u.mxcsr = t.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r14] (Q := fun u =>
    u.mem = t.mem.writeW (off B o) (word t.mem B o <<< 2) ∧ u.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧
      u.zf = some (decide (n - 1 = 0)) ∧ u.mxcsr = t.mxcsr) (by
    xrun [ea_at'', hB, hld, hst, h14, VG.Proof.MlKem.X86_64.ofNat64_pred hn (by omega),
      VG.Proof.MlKem.X86_64.ofNat64_beq_zero (k := n - 1) (by omega), RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
    ) rfl) fun u ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, k, d⟩

theorem am_flag (w : BitVec 64) (P q : Bool) :
    (mask P &&& 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((w >>> 62).toNat < BitVec.toNat (1 : BitVec 64))))) |||
      (mask q &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((w >>> 62).toNat < BitVec.toNat (1 : BitVec 64)))) ^^^
        BitVec.signExtend 64 (BitVec.ofInt 32 (-1)))) = mask (if w.toNat / 2 ^ 62 = 0 then P else q) := by
  have e : (w >>> 62).toNat = w.toNat / 2 ^ 62 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  rw [e, h1]
  by_cases hd : w.toNat / 2 ^ 62 = 0
  · rw [hd, VG.Proof.MlKem.X86_64.ifp rfl]; cases P <;> cases q <;> decide
  · rw [VG.Proof.MlKem.X86_64.ifn hd, decide_eq_false (by omega)]; cases P <;> cases q <;> decide

/-- After a window's multiplication's tail: the flag at `f`. -/
theorem amTail_ok {t : State} {B : Addr} {o f : Nat} {P q : Bool} (hB : t.gpr .rbx = B)
    (hld : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 o) 8) (hlf : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 f) 8)
    (hsf : InRegions t.wr (B + BitVec.ofNat 64 f) 8) (hP : word t.mem B f = mask P) (hq : t.gpr .rdx = mask q) :
    WP isa (.block [.mov .rcx (.mem (at_ .rbx f)), .mov .rax (.mem (at_ .rbx o)), .shift .shr .rax 62,
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .and .rcx (.reg .rax),
      .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rdx (.reg .rax), .alu .or .rcx (.reg .rdx),
      .store (at_ .rbx f) .rcx]) t fun u =>
      u.mem = t.mem.writeW (off B f) (mask (if (word t.mem B o).toNat / 2 ^ 62 = 0 then P else q)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] t u ∧ u.mxcsr = t.mxcsr := by
  have hP' : t.mem.readW (B + BitVec.ofNat 64 f) 64 = mask P := hP
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx] (Q := fun u =>
    u.mem = t.mem.writeW (off B f) (mask (if (word t.mem B o).toNat / 2 ^ 62 = 0 then P else q)) ∧
      u.mxcsr = t.mxcsr) (by
    xrun [ea_at'', hB, hld, hlf, hsf, hP', hq, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
    rw [am_flag _ P q]) rfl) fun u ⟨⟨a, c⟩, k⟩ => ⟨a, k, c⟩

/-- After a squaring's tail. -/
theorem asTail_ok {t : State} {B : Addr} {f : Nat} {P q : Bool} (hB : t.gpr .rbx = B)
    (hlf : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 f) 8)
    (hsf : InRegions t.wr (B + BitVec.ofNat 64 f) 8) (hP : word t.mem B f = mask P) (hq : t.gpr .rdx = mask q) :
    WP isa (.block [.mov .rcx (.mem (at_ .rbx f)), .alu .or .rcx (.reg .rdx), .store (at_ .rbx f) .rcx]) t fun u =>
      u.mem = t.mem.writeW (off B f) (mask (P || q)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] t u ∧ u.mxcsr = t.mxcsr := by
  have hP' : t.mem.readW (B + BitVec.ofNat 64 f) 64 = mask P := hP
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx] (Q := fun u =>
    u.mem = t.mem.writeW (off B f) (mask (P || q)) ∧ u.mxcsr = t.mxcsr) (by
    xrun [ea_at'', hB, hlf, hsf, hP', hq, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags, mask_or']) rfl)
    fun u ⟨⟨a, c⟩, k⟩ => ⟨a, k, c⟩

theorem ea_disp (t : State) (r : Reg) (d : Nat) : t.ea { base := r, disp := ((d : Nat) : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem al_flag (K w : BitVec 64) (P q m : Bool) (hK : K &&& w = 0 ↔ m = false) :
    mask P ||| (mask q &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((K &&& w).toNat < BitVec.toNat (1 : BitVec 64)))) ^^^
        BitVec.signExtend 64 (BitVec.ofInt 32 (-1)))) = mask (P || (m && q)) := by
  have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
  have e : decide ((K &&& w).toNat < 1) = !m := by
    cases m
    · rw [decide_eq_true ?_]; rfl
      have := hK.mpr rfl; rw [this]; decide
    · rw [decide_eq_false ?_]; rfl
      intro h; have := hK.mp (BitVec.eq_of_toNat_eq (by show _ = 0; omega)); cases this
  rw [h1, e]; cases P <;> cases q <;> cases m <;> decide

/-- After squaring `j` of the last three's tail. -/
theorem alTail_ok {t : State} {B H : Addr} {d f : Nat} {K w : BitVec 64} {P q m : Bool} (hB : t.gpr .rbx = B)
    (hdi : t.gpr .rdi = H)
    (hld : InRegions (t.rd ++ t.wr) (H + BitVec.ofNat 64 d) 8) (hw : word t.mem H d = w) (hK : K &&& w = 0 ↔ m = false)
    (hlf : InRegions (t.rd ++ t.wr) (B + BitVec.ofNat 64 f) 8)
    (hsf : InRegions t.wr (B + BitVec.ofNat 64 f) 8) (hP : word t.mem B f = mask P) (hq : t.gpr .rdx = mask q) :
    WP isa (.block [.movImm64 .rax K, .alu .and .rax (.mem { base := .rdi, disp := ((d : Nat) : Int) }),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))),
      .alu .and .rdx (.reg .rax), .mov .rcx (.mem (at_ .rbx f)), .alu .or .rcx (.reg .rdx),
      .store (at_ .rbx f) .rcx]) t fun u =>
      u.mem = t.mem.writeW (off B f) (mask (P || (m && q))) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx] t u ∧ u.mxcsr = t.mxcsr := by
  have hw' : t.mem.readW (H + BitVec.ofNat 64 d) 64 = w := hw
  have hP' : t.mem.readW (B + BitVec.ofNat 64 f) 64 = mask P := hP
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx] (Q := fun u =>
    u.mem = t.mem.writeW (off B f) (mask (P || (m && q))) ∧ u.mxcsr = t.mxcsr) (by
    xrun [ea_disp, ea_at'', hB, hdi, hld, hw', hlf, hsf, hP', hq, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
    rw [al_flag K w P q m hK]) rfl) fun u ⟨⟨a, c⟩, k⟩ => ⟨a, k, c⟩

theorem sigK_mask {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) {a : Nat} :
    (sigK j &&& BitVec.twoPow 64 (a % 64) = 0 ↔ decide (j < VG.Proof.RsaKeyGen.sigOf a) = false) := by
  rw [← VG.Proof.RsaKeyGen.sigOf_mod, decide_eq_false_iff_not]
  have ha : a % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize a % 64 = k at ha ⊢
  rcases hj with rfl | rfl | rfl
  · rw [BitVec.and_comm]; exact (VG.Proof.RsaKeyGen.sig_mask1 k ha) ▸ Iff.rfl
  · rw [BitVec.and_comm]; exact (VG.Proof.RsaKeyGen.sig_mask2 k ha) ▸ Iff.rfl
  · rw [BitVec.and_comm]; exact (VG.Proof.RsaKeyGen.sig_mask3 k ha) ▸ Iff.rfl

theorem ea_idx (t : State) (r i : Reg) (d : Nat) :
    t.ea { base := r, index := some i, scale := 8, disp := ((d : Nat) : Int) } =
      t.gpr r + (t.gpr i * BitVec.ofNat 64 8 + BitVec.ofNat 64 d) := by
  simp only [State.ea, BitVec.add_assoc]
  exact congrArg _ (congrArg _ (BitVec.ofInt_natCast ..))

theorem idx_ofNat (j d : Nat) : BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofNat 64 d = BitVec.ofNat 64 (d + 8 * j) := by
  rw [VG.Proof.Bignum.ofNat_mul8, ← BitVec.ofNat_add, Nat.add_comm]

theorem load_ok {t : State} {B H : Addr} {o d n : Nat} {V : BitVec 64} (hB : t.gpr .rbx = B) (hdi : t.gpr .rdi = H)
    (h15 : t.gpr .r15 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n < 2 ^ 63)
    (hld : InRegions (t.rd ++ t.wr) (H + BitVec.ofNat 64 (d + 8 * (n - 1))) 8)
    (hw : word t.mem H (d + 8 * (n - 1)) = V) (hst : InRegions t.wr (B + BitVec.ofNat 64 o) 8) :
    WP isa (.block [.mov .rax (.reg .r15), .alu .sub .rax (.imm 1),
        .mov .rcx (.mem { base := .rdi, index := some .rax, scale := 8, disp := ((d : Nat) : Int) }),
        .store (at_ .rbx o) .rcx, .mov32 .r14 (.imm 32)]) t fun u =>
      u.mem = t.mem.writeW (off B o) V ∧ u.gpr .r14 = BitVec.ofNat 64 32 ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .r14] t u ∧ u.mxcsr = t.mxcsr := by
  have hw' : t.mem.readW (H + BitVec.ofNat 64 (d + 8 * (n - 1))) 64 = V := hw
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .r14] (Q := fun u =>
    u.mem = t.mem.writeW (off B o) V ∧ u.gpr .r14 = BitVec.ofNat 64 32 ∧ u.mxcsr = t.mxcsr) (by
    xrun [ea_at'', ea_idx, hB, hdi, h15, VG.Proof.MlKem.X86_64.ofNat64_pred hn (by omega), idx_ofNat, hld, hw', hst,
      RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
    all_goals rfl) rfl) fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩

theorem init_ok {t : State} {B : Addr} {o W : Nat} (hB : t.gpr .rbx = B) (hW : W < 2 ^ 31)
    (hst : InRegions t.wr (B + BitVec.ofNat 64 o) 8) :
    WP isa (.block ([.mov32 .rax (.imm 0), .store (at_ .rbx o) .rax,
      .mov32 .r15 (.imm (BitVec.ofNat 32 W))] : List Instr)) t fun u =>
      u.mem = t.mem.writeW (off B o) (mask false) ∧ u.gpr .r15 = BitVec.ofNat 64 W ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .r15] t u ∧ u.mxcsr = t.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r15] (Q := fun u =>
    u.mem = t.mem.writeW (off B o) (mask false) ∧ u.gpr .r15 = BitVec.ofNat 64 W ∧ u.mxcsr = t.mxcsr) (by
    xrun [ea_at'', hB, hst, RegUpd.mxcsr_setReg]
    refine ⟨rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := W) (by omega), Nat.mod_eq_of_lt (a := W) (by omega)]) rfl)
    fun u ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, k, c⟩

theorem next_ok {t : State} {n : Nat} (h15 : t.gpr .r15 = BitVec.ofNat 64 n) (hn : n < 2 ^ 63) :
    WP isa (.block [.alu .sub .r15 (.imm 1), .alu .cmp .r15 (.imm (BitVec.ofInt 32 (-1)))]) t fun u =>
      u.gpr .r15 = BitVec.ofNat 64 n - 1 ∧ u.zf = some (decide (n = 0)) ∧ u.mem = t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r15] t u ∧ u.mxcsr = t.mxcsr := by
  have e : (BitVec.ofNat 64 n - 1 - BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) == 0) = decide (n = 0) := by
    rw [VG.Proof.Bignum.X86_64.sub_beq_zero]
    have : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide
    rw [this]
    by_cases h : n = 0
    · subst h; decide
    · rw [decide_eq_false h]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_allOnes] at this
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [h1, Nat.mod_eq_of_lt (a := n) (by omega)] at this
      omega
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r15] (Q := fun u =>
    u.gpr .r15 = BitVec.ofNat 64 n - 1 ∧ u.zf = some (decide (n = 0)) ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr) (by
    xrun [h15, e, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]) rfl) fun u ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, k, d⟩

/-- `u` is `t` but for the flags. -/
def Same (t u : State) : Prop := VG.Proof.MlKem.X86_64.Keep [] t u ∧ u.mem = t.mem ∧ u.mxcsr = t.mxcsr

theorem Same.gpr {t u : State} (e : Same t u) (r : Reg) : u.gpr r = t.gpr r := e.1.1 r List.not_mem_nil

theorem Same.trans {t u v : State} (e : Same t u) (e' : Same u v) : Same t v :=
  ⟨(e.1.trans e'.1).mono (by decide), e'.2.1.trans e.2.1, e'.2.2.trans e.2.2⟩

theorem isLast_ite {t : State} {A X : Prog isa} {Q : State → Prop}
    (hA : t.gpr .r15 = 0 → ∀ u, Same t u → WP isa A u Q) (hX : t.gpr .r15 ≠ 0 → ∀ u, Same t u → WP isa X u Q) :
    WP isa (.seq (.block isLast) (.ite .e A X)) t Q := by
  refine WP.seq ?_
  unfold isLast
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine WP.ite (t.gpr .r15 &&& t.gpr .r15 == 0) rfl (fun hb => hA ?_ _ ⟨⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩)
    (fun hb => hX ?_ _ ⟨⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩)
  · simpa [BitVec.and_self] using hb
  · simpa [BitVec.and_self] using hb

theorem cmp13_ite {t : State} {x : BitVec 32} {A X : Prog isa} {Q : State → Prop}
    (hA : (t.gpr .r13 - BitVec.signExtend 64 x == 0) = true → ∀ u, Same t u → WP isa A u Q)
    (hX : (t.gpr .r13 - BitVec.signExtend 64 x == 0) = false → ∀ u, Same t u → WP isa X u Q) :
    WP isa (.seq (.block [.alu .cmp .r13 (.imm x)]) (.ite .e A X)) t Q := by
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  exact WP.ite (t.gpr .r13 - BitVec.signExtend 64 x == 0) rfl (fun hb => hA hb _ ⟨⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩)
    (fun hb => hX hb _ ⟨⟨fun _ _ => rfl, rfl, rfl⟩, rfl, rfl⟩)

theorem cmp1 : ∀ v < 4, (BitVec.ofNat 64 v - BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (v = 1) := by decide
theorem cmp2 : ∀ v < 4, (BitVec.ofNat 64 v - BitVec.signExtend 64 (2 : BitVec 32) == 0) = decide (v = 2) := by decide
theorem cmp3 : ∀ v < 4, (BitVec.ofNat 64 v - BitVec.signExtend 64 (3 : BitVec 32) == 0) = decide (v = 3) := by decide

theorem wsub13_ok (u : State) : WP isa (.block [.alu .sub .r13 (.imm 1)]) u fun t =>
    t.gpr .r13 = u.gpr .r13 - 1 ∧ t.zf = some (u.gpr .r13 - 1 == 0) ∧ t.mem = u.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.r13] u t ∧ t.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun t => t.gpr .r13 = u.gpr .r13 - 1 ∧
    t.zf = some (u.gpr .r13 - 1 == 0) ∧ t.mem = u.mem ∧ t.mxcsr = u.mxcsr)
    (by xrun [RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]) rfl) fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, k, d⟩

theorem mov13_ok (u : State) : WP isa (.block [.mov32 .r13 (.imm 3)]) u fun t =>
    t.gpr .r13 = BitVec.ofNat 64 3 ∧ t.mem = u.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r13] u t ∧ t.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 3 ∧
    t.mem = u.mem ∧ t.mxcsr = u.mxcsr) (by xrun [RegUpd.mxcsr_setReg]) rfl) fun t ⟨⟨a, b, d⟩, k⟩ => ⟨a, b, k, d⟩

theorem shl_div62 (x : BitVec 64) {t : Nat} (ht : t < 32) :
    (x <<< (2 * t)).toNat / 2 ^ 62 = x.toNat / 2 ^ (62 - 2 * t) % 2 ^ 2 := by
  rw [← Nat.shiftRight_eq_div_pow, ← BitVec.toNat_ushiftRight]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < 2
  · simp only [show i + 62 < 64 by omega, hi, decide_true, Bool.true_and, show 2 * t ≤ i + 62 by omega]
    congr 1; omega
  · simp only [show ¬ i + 62 < 64 by omega, hi, decide_false, Bool.false_and]

/-- The digit of window `t` of word `n − 1` of `E`. -/
theorem digit {V : BitVec 64} {E n t W : Nat} (hV : V.toNat = E / 2 ^ (64 * (n - 1)) % 2 ^ 64) (hn : 1 ≤ n)
    (hnW : n ≤ W) (ht : t < 32) :
    (V <<< (2 * t)).toNat / 2 ^ 62 = E / (2 ^ 2) ^ (32 * W - 1 - (32 * (W - n) + t)) % 2 ^ 2 := by
  rw [shl_div62 V ht, hV, VG.Proof.RsaKeyGen.mod_div_mod (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add,
    ← Nat.pow_mul, show 64 * (n - 1) + (62 - 2 * t) = 2 * (32 * W - 1 - (32 * (W - n) + t)) by omega]

theorem shl2_succ (x : BitVec 64) (t : Nat) : x <<< (2 * t) <<< 2 = x <<< (2 * (t + 1)) := by
  rw [← BitVec.shiftLeft_add, show 2 * t + 2 = 2 * (t + 1) by omega]

theorem mov14_ok (u : State) : WP isa (.block [.mov32 .r14 (.imm 1)]) u fun t =>
    t.gpr .r14 = BitVec.ofNat 64 1 ∧ t.mem = u.mem ∧ Keep [.r14] u t ∧ t.mxcsr = u.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 1 ∧
    t.mem = u.mem ∧ t.mxcsr = u.mxcsr) (by xrun [RegUpd.mxcsr_setReg]) rfl) fun t ⟨⟨a, b, d⟩, k⟩ => ⟨a, b, k, d⟩

theorem WEnv.same (hl : MrOk l) {u v : State} {B H : Addr} {c k b : Nat} (h : WEnv l B H c k b u)
    (e : Same u v) : WEnv l B H c k b v := h.keep hl e.1 (by decide) (by decide) (by decide) e.2.1

theorem Rep.same {u v : State} {B : Addr} {c o x : Nat} (h : Rep l u.mem B c o x) (e : Same u v) :
    Rep l v.mem B c o x := by rw [e.2.1]; exact h

/-! ## The multiplications -/

/-- The registers a multiplication changes. -/
abbrev MR : List Reg := [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13]

theorem keep_amm {s t : State}
    (g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keep [.rax, .rcx, .rdx, .rsi, .r9, .r10, .r12] s t :=
  ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact g r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2, hrd, hwr⟩

/-- A multiplication's step `st` (`r13` counting down). -/
structure MOut (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B H : Addr) (c k b : Nat) (t u : State) (st : Nat × Bool) :
    Prop where
  env : WEnv l B H c k b u
  rep : Rep l u.mem B c (oY l) st.1
  lt : st.1 < c
  flag : word u.mem B (oF l) = mask st.2
  r13 : u.gpr .r13 = t.gpr .r13 - 1
  zf : u.zf = some (t.gpr .r13 - 1 == 0)
  keep : Keep MR t u
  mx : u.mxcsr = t.mxcsr
  frm : Frm B (wrs l) t.mem u.mem
  v : word u.mem B (oV l) = word t.mem B (oV l)

/-- The end of a multiplication: the flag stored, `r13` counted down. -/
theorem fin_ok (hl : MrOk l) {t u w : State} {B H : Addr} {c k b z : Nat} {F : Bool}
    (hE : WEnv l B H c k b u) (hz : Rep l u.mem B c (oY l) z) (hzc : z < c)
    (hK : Keep MR t u) (h13 : u.gpr .r13 = t.gpr .r13) (hx : u.mxcsr = t.mxcsr) (hf : Frm B (wrs l) t.mem u.mem)
    (hv : word u.mem B (oV l) = word t.mem B (oV l))
    (hw : w.mem = u.mem.writeW (off B (oF l)) (mask F)) (kw : Keep [.rax, .rcx, .rdx] u w) (xw : w.mxcsr = u.mxcsr) :
    WP isa (.block [.alu .sub .r13 (.imm 1)]) w fun v => MOut l B H c k b t v (z, F) := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  refine WP.mono (wsub13_ok w) fun v ⟨r13, zf, m, kv, xv⟩ => ?_
  have ow : Outside B (oF l) 8 u.mem v.mem := by
    rw [m, hw]; exact VG.Proof.Bignum.writeW_outside _ B _ (by omega_arith)
  have fw : Frm B (wrs l) u.mem v.mem := Frm.of_outside ow mem_wrs3
  have Kv := kw.trans kv
  have h13w : w.gpr .r13 = t.gpr .r13 := (kw.gpr (by decide)).trans h13
  exact ⟨hE.frame hl ((Kv.gpr (by decide)).trans hE.rbx) ((Kv.gpr (by decide)).trans hE.rdi)
      ((Kv.gpr (by decide)).trans hE.r12) Kv.2.1 Kv.2.2 fw,
    wrep_out hl ow (.inl (by omega_arith)) (by omega_arith) hz, hzc,
    by rw [m, hw]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _, by rw [r13, h13w], by rw [zf, h13w],
    (hK.trans Kv).mono (by decide), by rw [xv, xw, hx], hf.trans fw,
    by rw [ow.word (.inl (by omega_arith)) (by omega_arith), hv]⟩

theorem wp_assoc {c₁ c₂ c₃ : Prog isa} {u : State} {Q : State → Prop}
    (h : WP isa (.seq c₁ c₂) u fun w => WP isa c₃ w Q) : WP isa c₁ u fun v => WP isa (.seq c₂ c₃) v Q :=
  WP.mono (WP.seq_iff.mp h) fun _ h' => WP.seq h'

/-- The squaring of `Y` from a state with `rbx = B`: `Y := Y Y`. -/
theorem sqY_ok (hl : MrOk l) {t u : State} {B H : Addr} {c k b y : Nat} {Q : State → Prop}
    (hE : WEnv l B H c k b t) (hy : Rep l t.mem B c (oY l) y) (e : Same t u)
    (hQ : ∀ w, WEnv l B H c k b w → Rep l w.mem B c (oY l) (y * y % c) → Keep MR t w →
      w.gpr .r13 = t.gpr .r13 → w.gpr .r15 = t.gpr .r15 → w.mxcsr = t.mxcsr → Frm B (wrs l) t.mem w.mem →
      word w.mem B (oV l) = word t.mem B (oV l) → word w.mem B (oF l) = word t.mem B (oF l) → Q w) :
    WP isa (.seq (.block (setOps (oY l) (oY l) (oY l))) (ammMul l)) u Q := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hB₂ : u.gpr .rbx = B := (e.gpr _).trans hE.rbx
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.Ifma.Pub.setOps_ok (o := oY l) (a := oY l) (b := oY l) hB₂
    (by omega_arith) (by omega_arith) (by omega_arith)) fun u₃ ⟨r8, r9, r11, k₃, m₃, x₃⟩ => ?_)
  have K₃ := e.1.trans k₃
  have mm₃ : u₃.mem = t.mem := m₃.trans e.2.1
  have hB₃ : u₃.gpr .rbx = B := (K₃.gpr (by decide)).trans hE.rbx
  have hy₃ : Rep l u₃.mem B c (oY l) y := by rw [mm₃]; exact hy
  refine WP.mono (amm_rep hl hB₃ r8 r9 r11 (hE.scr.congr K₃.2.2) z0 z13 (by rw [mm₃]; exact hE.tab.mod) hE.odd
    (by omega_arith) (by omega_arith) (by omega_arith) hy₃ hy₃) fun w ⟨hr, ho, g, r12, rd, wr, x⟩ => ?_
  have K := K₃.trans (keep_amm g rd wr)
  have o : Outside B (oY l) l.NB t.mem w.mem := by rw [← mm₃]; exact ho
  have f : Frm B (wrs l) t.mem w.mem := Frm.of_outside (o.mono (Nat.le_refl _) (by omega_arith)) mem_wrs1
  exact hQ w (hE.frame hl ((K.gpr (by decide)).trans hE.rbx) ((K.gpr (by decide)).trans hE.rdi) r12 K.2.1 K.2.2 f)
    (rep_congr hr (Nat.mod_mod _ _).symm) (K.mono (by decide)) (K.gpr (by decide)) (K.gpr (by decide))
    (by rw [x, x₃, e.2.2]) f (o.word (.inr (by omega_arith)) (by omega_arith))
    (o.word (.inr (by omega_arith)) (by omega_arith))

/-- A squaring of a window (`r15 ≠ 0`, `r13 ≠ 1`). -/
theorem multSq_ok (hl : MrOk l) {t : State} {B H : Addr} {c k b y : Nat} {P : Bool}
    (hE : WEnv l B H c k b t) (hy : Rep l t.mem B c (oY l) y) (hF : word t.mem B (oF l) = mask P)
    (h15 : t.gpr .r15 ≠ 0) (hne : (t.gpr .r13 - BitVec.signExtend 64 (1 : BitVec 32) == 0) = false) :
    WP isa (mult l) t fun u => MOut l B H c k b t u (wSq c true (y, P)) := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hc0 : 0 < c := by have := hE.three; omega_arith
  unfold mult
  refine WP.seq (isLast_ite (fun h => absurd h h15) fun _ u₁ e₁ => ?_)
  refine cmp13_ite (fun h => by rw [e₁.gpr, hne] at h; cases h) fun _ u₂ e₂ => ?_
  refine wp_assoc <| sqY_ok hl hE hy (e₁.trans e₂) fun u₄ hE₄ hz K₄ h13₄ h15₄ x₄ f₄ hV₄ hF₄ => ?_
  refine WP.seq (isLast_ite (fun h => absurd (h15₄.symm.trans h) h15) fun _ u₅ e₅ => ?_)
  refine cmp13_ite (fun h => by rw [e₅.gpr, h13₄, hne] at h; cases h) fun _ u₆ e₆ => ?_
  have s₆ := e₅.trans e₆
  unfold afterSq
  rw [WP.block_append_iff]
  refine WP.mono (isM1_ok hl (hE₄.same hl s₆) (hz.same s₆) (Nat.mod_lt _ hc0)) fun u₇ ⟨hd₇, m₇, k₇, x₇⟩ => ?_
  have hs₇ : Scr u₇ B (size l) := hE₄.scr.congr (k₇.2.2.trans s₆.1.2.2)
  refine WP.mono (asTail_ok (f := oF l) (P := P) ((k₇.gpr (by decide)).trans ((s₆.gpr _).trans hE₄.rbx))
    (hs₇.ld (by omega_arith)) (hs₇.st (by omega_arith)) (by rw [m₇, s₆.2.1, hF₄]; exact hF) hd₇)
    fun u₈ ⟨m₈, k₈, x₈⟩ => ?_
  exact fin_ok hl (F := P || decide (y * y % c = c - 1)) hE₄ hz (Nat.mod_lt _ hc0) K₄ h13₄ x₄ f₄ hV₄
    (by rw [m₈, m₇, s₆.2.1])
    ((s₆.1.trans k₇).trans k₈ |>.mono (by decide)) (by rw [x₈, x₇, s₆.2.2])

/-- `F := d ≠ 0 ? y ≡ ±1 : F` after the multiplication by `T_d`. -/
def mStep (c b d : Nat) (st : Nat × Bool) : Nat × Bool :=
  (st.1 * VG.Spec.Rsa.powMod b d c % c, if d = 0 then st.2 else
    decide (st.1 * VG.Spec.Rsa.powMod b d c % c = 1) || decide (st.1 * VG.Spec.Rsa.powMod b d c % c = c - 1))

/-- The multiplication of a window (`r15 ≠ 0`, `r13 = 1`). -/
theorem multMul_ok (hl : MrOk l) {t : State} {B H : Addr} {c k b y d : Nat} {P : Bool}
    (hE : WEnv l B H c k b t) (hy : Rep l t.mem B c (oY l) y) (hF : word t.mem B (oF l) = mask P)
    (h15 : t.gpr .r15 ≠ 0) (heq : (t.gpr .r13 - BitVec.signExtend 64 (1 : BitVec 32) == 0) = true)
    (hd : (word t.mem B (oV l)).toNat / 2 ^ 62 = d) :
    WP isa (mult l) t fun u => MOut l B H c k b t u (mStep c b d (y, P)) := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hc0 : 0 < c := by have := hE.three; omega_arith
  unfold mult
  refine WP.seq (isLast_ite (fun h => absurd h h15) fun _ u₁ e₁ => ?_)
  refine cmp13_ite (fun _ u₂ e₂ => ?_) (fun h => by rw [e₁.gpr, heq] at h; cases h)
  have s₂ := e₁.trans e₂
  have hB₂ : u₂.gpr .rbx = B := (s₂.gpr _).trans hE.rbx
  rw [WP.block_append_iff]
  refine WP.mono (select_ok hl hB₂ (hE.scr.congr s₂.1.2.2)) fun u₃ ⟨hl₃, ho₃, k₃, x₃⟩ => ?_
  have hd₃ : (word u₂.mem B (oV l)).toNat / 2 ^ 62 = d := by rw [s₂.2.1]; exact hd
  rw [hd₃] at hl₃
  have hd4 : d < 4 := by
    rw [← hd]; exact Nat.div_lt_of_lt_mul (by have := (word t.mem B (oV l)).isLt; omega_arith)
  have hB₃ := (k₃.gpr (by decide)).trans hB₂
  refine WP.mono (VG.Proof.Bignum.X86_64.Ifma.Pub.setOps_ok (o := oY l) (a := oY l) (b := oS l) hB₃
    (by omega_arith) (by omega_arith) (by omega_arith)) fun u₄ ⟨r8, r9, r11, k₄, m₄, x₄⟩ => ?_
  have K₄ := (s₂.1.trans k₃).trans k₄
  have o₄ : Outside B (oS l) l.NB t.mem u₄.mem := by rw [m₄, ← s₂.2.1]; exact ho₃
  have f₄ : Frm B (wrs l) t.mem u₄.mem := Frm.of_outside (o₄.mono (by omega_arith) (by omega_arith)) mem_wrs1
  have hy₄ : Rep l u₄.mem B c (oY l) y := wrep_out hl o₄ (.inl (by omega_arith)) (by omega_arith) hy
  have hS₄ : Rep l u₄.mem B c (oS l) (b ^ d) :=
    rep_limbs (fun j hj => by rw [m₄, hl₃ j hj, s₂.2.1]) (hE.tab.t d hd4)
  have hB₄ : u₄.gpr .rbx = B := (K₄.gpr (by decide)).trans hE.rbx
  refine WP.seq (WP.mono (amm_rep hl hB₄ r8 r9 r11 (hE.scr.congr K₄.2.2) z0 z13 (tab_frm hl f₄ hE.tab).mod hE.odd
    (by omega_arith) (by omega_arith) (by omega_arith) hy₄ hS₄) fun u₅ ⟨hr₅, ho₅, g₅, r12₅, rd₅, wr₅, x₅⟩ => ?_)
  have K₅ := K₄.trans (keep_amm g₅ rd₅ wr₅)
  have f₅ : Frm B (wrs l) t.mem u₅.mem :=
    f₄.trans (Frm.of_outside (ho₅.mono (Nat.le_refl _) (by omega_arith)) mem_wrs1)
  have hE₅ : WEnv l B H c k b u₅ :=
    hE.frame hl ((K₅.gpr (by decide)).trans hE.rbx) ((K₅.gpr (by decide)).trans hE.rdi) r12₅ K₅.2.1 K₅.2.2 f₅
  have hz : Rep l u₅.mem B c (oY l) (y * VG.Spec.Rsa.powMod b d c % c) :=
    rep_congr hr₅ (by rw [VG.Proof.Bignum.powMod_eq, Nat.mod_mod, Nat.mul_mod_mod])
  have hF₅ : word u₅.mem B (oF l) = mask P := by
    rw [ho₅.word (.inr (by omega_arith)) (by omega_arith), o₄.word (.inr (by omega_arith)) (by omega_arith)]; exact hF
  have hV₅ : word u₅.mem B (oV l) = word t.mem B (oV l) := by
    rw [ho₅.word (.inr (by omega_arith)) (by omega_arith), o₄.word (.inr (by omega_arith)) (by omega_arith)]
  have h13₅ : u₅.gpr .r13 = t.gpr .r13 := K₅.gpr (by decide)
  refine WP.seq (isLast_ite (fun h => absurd ((K₅.gpr (by decide)).symm.trans h) h15) fun _ u₆ e₆ => ?_)
  refine cmp13_ite (fun _ u₇ e₇ => ?_) (fun h => by rw [e₆.gpr, h13₅, heq] at h; cases h)
  have s₇ := e₆.trans e₇
  unfold afterMul
  rw [WP.block_append_iff]
  refine WP.mono (isPM1_ok hl (hE₅.same hl s₇) (hz.same s₇) (Nat.mod_lt _ hc0)) fun u₈ ⟨hd₈, m₈, k₈, x₈⟩ => ?_
  have hs₈ : Scr u₈ B (size l) := hE₅.scr.congr (k₈.2.2.trans s₇.1.2.2)
  refine WP.mono (amTail_ok (o := oV l) (f := oF l) (P := P) ((k₈.gpr (by decide)).trans ((s₇.gpr _).trans hE₅.rbx))
    (hs₈.ld (by omega_arith)) (hs₈.ld (by omega_arith)) (hs₈.st (by omega_arith)) (by rw [m₈, s₇.2.1]; exact hF₅) hd₈)
    fun u₉ ⟨m₉, k₉, x₉⟩ => ?_
  have hd₈ : (word u₈.mem B (oV l)).toNat / 2 ^ 62 = d := by rw [m₈, s₇.2.1, hV₅]; exact hd
  rw [hd₈] at m₉
  exact fin_ok hl hE₅ hz (Nat.mod_lt _ hc0) (K₅.mono (by decide)) h13₅ (by rw [x₅, x₄, x₃, s₂.2.2]) f₅ hV₅
    (by rw [m₉, m₈, s₇.2.1]) ((s₇.1.trans k₈).trans k₉ |>.mono (by decide)) (by rw [x₉, x₈, s₇.2.2])

/-- After squaring `j` of the last three: `F |= y ≡ −1` under `σ > j`. -/
theorem afterLast_ok (hl : MrOk l) {u : State} {B H : Addr} {c k b y j : Nat} {P : Bool}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) (hE : WEnv l B H c k b u) (hy : Rep l u.mem B c (oY l) y) (hyc : y < c)
    (hF : word u.mem B (oF l) = mask P) :
    WP isa (.block (afterLast l j)) u fun w =>
      w.mem = u.mem.writeW (off B (oF l)) (mask (P || (decide (j < mrSig c) && decide (y = c - 1)))) ∧
      Keep [.rax, .rcx, .rdx] u w ∧ w.mxcsr = u.mxcsr := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  unfold afterLast
  rw [WP.block_append_iff]
  refine WP.mono (isM1_ok hl hE hy hyc) fun w ⟨hd, m, kw, x⟩ => ?_
  have hs := hE.scr.congr kw.2.2
  refine WP.mono (alTail_ok (d := arr l aE + 8 * l.W) (f := oF l) (K := sigK j)
    (w := BitVec.twoPow 64 (mrA c % 64)) (m := decide (j < mrSig c)) (P := P) ((kw.gpr (by decide)).trans hE.rbx)
    ((kw.gpr (by decide)).trans hE.rdi) (by rw [kw.2.1, kw.2.2]; exact hE.erd l.W (by omega_arith))
    (by rw [m]; exact hE.el) (sigK_mask hj) (hs.ld (by omega_arith)) (hs.st (by omega_arith))
    (by rw [m]; exact hF) hd) fun v ⟨mv, kv, xv⟩ => ⟨by rw [mv, m], (kw.trans kv).mono (by decide), xv.trans x⟩

/-- A squaring of the last pass (`r15 = 0`, `r13 = v`): squaring `j = 4 − v`. -/
theorem multLast_ok (hl : MrOk l) {t : State} {B H : Addr} {c k b y v j : Nat} {P : Bool}
    (hE : WEnv l B H c k b t) (hy : Rep l t.mem B c (oY l) y) (hF : word t.mem B (oF l) = mask P)
    (h15 : t.gpr .r15 = 0) (h13 : t.gpr .r13 = BitVec.ofNat 64 v) (hv : v + j = 4) (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    WP isa (mult l) t fun u => MOut l B H c k b t u (wSq c (decide (j < mrSig c)) (y, P)) := by
  have hc0 : 0 < c := by have := hE.three; omega_arith
  have hv4 : v < 4 := by omega_arith
  unfold mult
  refine WP.seq (isLast_ite (fun _ u₁ e₁ => ?_) (fun h => absurd h15 h))
  refine wp_assoc <| sqY_ok hl hE hy e₁ fun u₄ hE₄ hz K₄ h13₄ h15₄ x₄ f₄ hV₄ hF₄ => ?_
  have cont : ∀ j', j' = j → ∀ w, Same u₄ w → WP isa (.block (afterLast l j')) w (fun x =>
      WP isa (.block [.alu .sub .r13 (.imm 1)]) x fun v =>
        MOut l B H c k b t v (wSq c (decide (j < mrSig c)) (y, P))) := by
    intro j' hj' w e
    rw [hj']
    refine WP.mono (afterLast_ok hl (P := P) (by omega_arith) (hE₄.same hl e) (hz.same e) (Nat.mod_lt _ hc0)
      (by rw [e.2.1, hF₄]; exact hF)) fun x ⟨mx, kx, xx⟩ => ?_
    exact fin_ok hl (F := P || (decide (j < mrSig c) && decide (y * y % c = c - 1))) hE₄ hz (Nat.mod_lt _ hc0)
      K₄ h13₄ x₄ f₄ hV₄ (by rw [mx, e.2.1])
      ((e.1.trans kx).mono (by decide)) (by rw [xx, e.2.2])
  refine WP.seq (isLast_ite (fun _ u₅ e₅ => ?_) (fun h => absurd (h15₄.trans h15) h))
  have h13₅ : u₅.gpr .r13 = BitVec.ofNat 64 v := (e₅.gpr _).trans (h13₄.trans h13)
  refine cmp13_ite (fun h u₆ e₆ => cont 1 ?_ u₆ (e₅.trans e₆))
    (fun h u₆ e₆ => cmp13_ite (fun h' u₇ e₇ => cont 2 ?_ u₇ ((e₅.trans e₆).trans e₇))
      (fun h' u₇ e₇ => cont 3 ?_ u₇ ((e₅.trans e₆).trans e₇)))
  · rw [h13₅, cmp3 v hv4] at h; have := of_decide_eq_true h; omega_arith
  · rw [e₆.gpr, h13₅, cmp2 v hv4] at h'; have := of_decide_eq_true h'; omega_arith
  · rw [h13₅, cmp3 v hv4] at h; rw [e₆.gpr, h13₅, cmp2 v hv4] at h'
    have := of_decide_eq_false h; have := of_decide_eq_false h'; omega_arith

/-! ## A window -/

/-- Through a window's multiplications, from `s` (`r13` counting). -/
structure WI (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B H : Addr) (c k b : Nat) (s : State) (st : Nat × Bool)
    (u : State) : Prop where
  env : WEnv l B H c k b u
  rep : Rep l u.mem B c (oY l) st.1
  lt : st.1 < c
  flag : word u.mem B (oF l) = mask st.2
  v : word u.mem B (oV l) = word s.mem B (oV l)
  frm : Frm B (wrs l) s.mem u.mem
  keep : Keep MR s u
  mx : u.mxcsr = s.mxcsr

theorem WI.step {B H : Addr} {c k b : Nat} {s u v : State} {st st' : Nat × Bool} (h : WI l B H c k b s st u)
    (m : MOut l B H c k b u v st') : WI l B H c k b s st' v :=
  ⟨m.env, m.rep, m.lt, m.flag, m.v.trans h.v, h.frm.trans m.frm, (h.keep.trans m.keep).mono (by decide),
    m.mx.trans h.mx⟩

/-- The registers a window changes. -/
abbrev MRW : List Reg := [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- A window, its multiplications' steps `sts`. -/
theorem window_gen (hl : MrOk l) {s : State} {B H : Addr} {c k b n : Nat} (sts : Nat → Nat × Bool)
    (hE : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) (sts 0).1) (hlt : (sts 0).1 < c)
    (hF : word s.mem B (oF l) = mask (sts 0).2) (h14 : s.gpr .r14 = BitVec.ofNat 64 n) (hn : 1 ≤ n) (hn' : n ≤ 32)
    (hstep : ∀ i < 3, ∀ u, WI l B H c k b s (sts i) u → u.gpr .r13 = BitVec.ofNat 64 (3 - i) →
      WP isa (mult l) u fun v => MOut l B H c k b u v (sts (i + 1))) :
    WP isa (window l) s fun t =>
      WEnv l B H c k b t ∧ Rep l t.mem B c (oY l) (sts 3).1 ∧ (sts 3).1 < c ∧
      word t.mem B (oF l) = mask (sts 3).2 ∧ word t.mem B (oV l) = word s.mem B (oV l) <<< 2 ∧
      t.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ t.zf = some (decide (n - 1 = 0)) ∧ Keep MRW s t ∧
      t.mxcsr = s.mxcsr ∧ Frm B (wrs l) s.mem t.mem := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  unfold window
  refine WP.seq (WP.mono (mov13_ok s) fun u₀ ⟨r13₀, m₀, k₀, x₀⟩ => ?_)
  have I₀ : WI l B H c k b s (sts 0) u₀ :=
    ⟨hE.keep hl k₀ (by decide) (by decide) (by decide) m₀, by rw [m₀]; exact hy, hlt, by rw [m₀]; exact hF,
      by rw [m₀], by rw [m₀]; exact Frm.refl _ _ _, k₀.mono (by decide), x₀⟩
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.wp_countdown (cnt := .r13) (N := 3) (by decide) (by decide)
    (fun i u => WI l B H c k b s (sts i) u) (Q := fun u => WI l B H c k b s (sts 3) u)
    (fun i hi u hI h13 => WP.mono (hstep i hi u hI h13) fun v m => ⟨hI.step m, m.r13, m.zf⟩)
    (fun _ h => h) I₀ r13₀) fun u₃ I₃ => ?_)
  have hs₃ := I₃.env.scr
  refine WP.mono (wtail_ok (o := oV l) I₃.env.rbx (hs₃.ld (by omega_arith)) (hs₃.st (by omega_arith))
    ((I₃.keep.gpr (by decide)).trans h14) hn (by omega_arith)) fun t ⟨m, r14, zf, kt, xt⟩ => ?_
  have ow : Outside B (oV l) 8 u₃.mem t.mem := by
    rw [m]; exact VG.Proof.Bignum.writeW_outside _ B _ (by omega_arith)
  have fw : Frm B (wrs l) u₃.mem t.mem := Frm.of_outside ow mem_wrs2
  have Kt := I₃.keep.trans kt
  exact ⟨I₃.env.frame hl ((kt.gpr (by decide)).trans I₃.env.rbx) ((kt.gpr (by decide)).trans I₃.env.rdi)
      ((kt.gpr (by decide)).trans I₃.env.r12) kt.2.1 kt.2.2 fw,
    wrep_out hl ow (.inl (by omega_arith)) (by omega_arith) I₃.rep, I₃.lt,
    by rw [ow.word (.inr (by omega_arith)) (by omega_arith)]; exact I₃.flag,
    by rw [m, VG.Proof.Bignum.word_writeW_self, I₃.v], r14, zf, Kt.mono (by decide), by rw [xt, I₃.mx],
    I₃.frm.trans fw⟩

/-- The steps of a window's multiplications. -/
def wst (c b d : Nat) (st : Nat × Bool) (i : Nat) : Nat × Bool := if i < 3 then sqs c i st else kWin 2 c b d st

theorem wst_zero (c b d : Nat) (st : Nat × Bool) : wst c b d st 0 = st := by
  unfold wst; rw [ifp (by decide)]; rfl

theorem wst_succ (c b d : Nat) (st : Nat × Bool) {i : Nat} (h : i + 1 < 3) :
    wst c b d st (i + 1) = wSq c true (wst c b d st i) := by
  unfold wst; rw [ifp h, ifp (by omega_arith)]; rfl

theorem wst_three (c b d : Nat) (st : Nat × Bool) : wst c b d st 3 = mStep c b d (wst c b d st 2) := by
  unfold wst; rw [ifn (by decide), ifp (by decide)]; rfl

/-- A window, with the registers it changes. -/
theorem windowW_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y n : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : word s.mem B (oF l) = mask P) (h15 : s.gpr .r15 ≠ 0) (h14 : s.gpr .r14 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n ≤ 32) :
    WP isa (window l) s fun t =>
      WEnv l B H c k b t ∧
      Rep l t.mem B c (oY l) (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 ∧
      (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 < c ∧
      word t.mem B (oF l) = mask (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).2 ∧
      word t.mem B (oV l) = word s.mem B (oV l) <<< 2 ∧
      t.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ t.zf = some (decide (n - 1 = 0)) ∧ Keep MRW s t ∧
      t.mxcsr = s.mxcsr ∧ Frm B (wrs l) s.mem t.mem := by
  have e3 := wst_three c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)
  have e3' : wst c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P) 3 =
      kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P) := by unfold wst; rw [ifn (by decide)]
  rw [← e3']
  refine window_gen hl (wst c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)) h
    (by rw [wst_zero]; exact hy) (by rw [wst_zero]; exact hyc) (by rw [wst_zero]; exact hP) h14 hn hn' ?_
  intro i hi u hI h13
  have h15u : u.gpr .r15 ≠ 0 := by rw [hI.keep.gpr (by decide)]; exact h15
  by_cases hi2 : i = 2
  · subst hi2
    rw [e3]
    exact multMul_ok hl hI.env hI.rep hI.flag h15u (by rw [h13]; decide) (by rw [hI.v])
  · rw [wst_succ _ _ _ _ (by omega_arith)]
    exact multSq_ok hl hI.env hI.rep hI.flag h15u (by
      rw [h13]; rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl <;> decide)

/-- `MrWindow.wEnd`'s squarings, the first `i`. -/
def lst (c : Nat) (st : Nat × Bool) : Nat → Nat × Bool
  | 0 => st
  | i + 1 => wSq c (decide (i + 1 < mrSig c)) (lst c st i)

/-- The last pass, with the registers it changes. -/
theorem lastW_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : word s.mem B (oF l) = mask P) (h15 : s.gpr .r15 = 0) (h14 : s.gpr .r14 = 1) :
    WP isa (window l) s fun t =>
      WEnv l B H c k b t ∧ word t.mem B (oF l) = mask (wEnd c (y, P)).2 ∧ t.zf = some true ∧ Keep MRW s t ∧
      t.mxcsr = s.mxcsr ∧ Frm B (wrs l) s.mem t.mem := by
  refine WP.mono (window_gen hl (n := 1) (lst c (y, P)) h hy hyc hP h14 (by decide) (by decide) ?_)
    fun t ⟨e, _, _, f, _, _, z, k, x, fr⟩ => ⟨e, f, z, k, x, fr⟩
  intro i hi u hI h13
  exact multLast_ok hl (j := i + 1) hI.env hI.rep hI.flag (by rw [hI.keep.gpr (by decide)]; exact h15) h13
    (by omega_arith) (by omega_arith) (by omega_arith)

/-- A window of a word of `E` (`r15 ≠ 0`), its digit `d` the top two bits of
the word at `oV`, from `y < c` in `Y` and the flag `P` at `oF`: `kWin`'s
result, the word shifted by two bits, and `r14` decremented (ZF if it
reaches 0). -/
theorem window_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y n : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : word s.mem B (oF l) = mask P) (h15 : s.gpr .r15 ≠ 0) (h14 : s.gpr .r14 = BitVec.ofNat 64 n)
    (hn : 1 ≤ n) (hn' : n ≤ 32) :
    WP isa (window l) s fun t =>
      WEnv l B H c k b t ∧
      Rep l t.mem B c (oY l) (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 ∧
      (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).1 < c ∧
      word t.mem B (oF l) = mask (kWin 2 c b ((word s.mem B (oV l)).toNat / 2 ^ 62) (y, P)).2 ∧
      word t.mem B (oV l) = word s.mem B (oV l) <<< 2 ∧
      t.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ t.zf = some (decide (n - 1 = 0)) ∧
      t.gpr .r15 = s.gpr .r15 ∧ t.gpr .rsp = s.gpr .rsp ∧ t.gpr .rbp = s.gpr .rbp ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8), (oF l, 8)] s.mem t.mem :=
  WP.mono (windowW_ok hl h hy hyc hP h15 h14 hn hn') fun _ ⟨e, r, lt, f, v, r14, z, k, x, fr⟩ =>
    ⟨e, r, lt, f, v, r14, z, k.gpr (by decide), k.gpr (by decide), k.gpr (by decide), x, fr⟩

/-- The last pass (`r15 = 0`): one window of three squarings, `wEnd`. -/
theorem last_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b y : Nat} {P : Bool}
    (h : WEnv l B H c k b s) (hy : Rep l s.mem B c (oY l) y) (hyc : y < c)
    (hP : word s.mem B (oF l) = mask P) (h15 : s.gpr .r15 = 0) (h14 : s.gpr .r14 = 1) :
    WP isa (window l) s fun t =>
      word t.mem B (oF l) = mask (wEnd c (y, P)).2 ∧ t.gpr .r15 = 0 ∧ t.zf = some true ∧
      t.gpr .rbx = B ∧ t.gpr .rdi = H ∧ t.gpr .rsp = s.gpr .rsp ∧ t.gpr .rbp = s.gpr .rbp ∧
      t.gpr .r12 = mask52 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8), (oF l, 8)] s.mem t.mem :=
  WP.mono (lastW_ok hl h hy hyc hP h15 h14) fun _ ⟨e, f, z, k, x, fr⟩ =>
    ⟨f, (k.gpr (by decide)).trans h15, z, e.rbx, e.rdi, k.gpr (by decide), k.gpr (by decide), e.r12, k.2.1, k.2.2,
      x, fr⟩

/-! ## The windows of `E` -/

/-- The registers the windows change. -/
abbrev MRO : List Reg := [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- Before the pass over word `n − 1` of `E` (`n` words left), from `s`. -/
structure OI (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B H : Addr) (c k b : Nat) (s : State) (n : Nat) (u : State) :
    Prop where
  le : n ≤ l.W
  r15 : u.gpr .r15 = BitVec.ofNat 64 n
  env : WEnv l B H c k b u
  rep : Rep l u.mem B c (oY l) (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n))).1
  lt : (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n))).1 < c
  flag : word u.mem B (oF l) = mask (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n))).2
  frm : Frm B (wrs l) s.mem u.mem
  keep : Keep MRO s u
  mx : u.mxcsr = s.mxcsr

/-- Through the windows of word `n − 1`: `t` of them done, from `s`. -/
structure WN (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B H : Addr) (c k b : Nat) (s : State) (n : Nat) (V : BitVec 64)
    (t : Nat) (u : State) : Prop where
  r15 : u.gpr .r15 = BitVec.ofNat 64 n
  env : WEnv l B H c k b u
  rep : Rep l u.mem B c (oY l) (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n) + t)).1
  lt : (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n) + t)).1 < c
  flag : word u.mem B (oF l) = mask (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n) + t)).2
  v : word u.mem B (oV l) = V <<< (2 * t)
  frm : Frm B (wrs l) s.mem u.mem
  keep : Keep MRO s u
  mx : u.mxcsr = s.mxcsr

/-- A window of the pass over word `n − 1` of `E`. -/
theorem pstep_ok (hl : MrOk l) {s v : State} {B H : Addr} {c k b n t : Nat} {V : BitVec 64}
    (hV : V.toNat = mrE c / 2 ^ (64 * (n - 1)) % 2 ^ 64) (hn : 1 ≤ n) (hW : n ≤ l.W) (ht : t < 32)
    (hJ : WN l B H c k b s n V t v) (h14 : v.gpr .r14 = BitVec.ofNat 64 (32 - t)) :
    WP isa (window l) v fun w => WN l B H c k b s n V (t + 1) w ∧ w.gpr .r14 = v.gpr .r14 - 1 ∧
      w.zf = some (v.gpr .r14 - 1 == 0) := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hd := digit (W := l.W) (t := t) hV hn hW ht
  have h15 : v.gpr .r15 ≠ 0 := by
    rw [hJ.r15]; intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact absurd this (by show n ≠ 0; omega_arith)
  refine WP.mono (windowW_ok hl hJ.env hJ.rep hJ.lt hJ.flag h15 h14 (by omega_arith) (by omega_arith))
    fun w ⟨e, r, lt, f, vv, r14, z, kw, xw, fr⟩ => ?_
  rw [hJ.v, hd] at r lt f
  have ek : kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n) + (t + 1)) =
      kWin 2 c b (mrE c / (2 ^ 2) ^ (32 * l.W - 1 - (32 * (l.W - n) + t)) % 2 ^ 2)
        (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - n) + t)) := by rw [← Nat.add_assoc, kRun]
  refine ⟨⟨(kw.gpr (by decide)).trans hJ.r15, e, by rw [ek]; exact r, by rw [ek]; exact lt, by rw [ek]; exact f,
      by rw [vv, hJ.v, shl2_succ], hJ.frm.trans fr, (hJ.keep.trans kw).mono (by decide), by rw [xw, hJ.mx]⟩,
    by rw [r14, h14, VG.Proof.MlKem.X86_64.ofNat64_pred (by omega_arith) (by omega_arith)],
    by rw [z, h14, VG.Proof.MlKem.X86_64.ofNat64_pred (by omega_arith) (by omega_arith),
      VG.Proof.MlKem.X86_64.ofNat64_beq_zero (by omega_arith)]⟩

/-- The pass over word `n − 1` of `E`, `n ≥ 1`. -/
theorem pass_ok (hl : MrOk l) {s u : State} {B H : Addr} {c k b n : Nat} (hI : OI l B H c k b s n u)
    (hn : 1 ≤ n) :
    WP isa (VG.Impl.MillerRabin.X86_64.Ifma.word l) u fun t =>
      WN l B H c k b s n (word u.mem H (arr l aE + 8 * (n - 1))) 32 t := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  have hW := hI.le
  unfold VG.Impl.MillerRabin.X86_64.Ifma.word
  refine WP.seq (isLast_ite (fun h => absurd h ?_) fun _ u₁ e₁ => ?_)
  · rw [hI.r15]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact absurd this (by show n ≠ 0; omega_arith)
  have hE₁ := hI.env.same hl e₁
  have hV : (word u.mem H (arr l aE + 8 * (n - 1))).toNat = mrE c / 2 ^ (64 * (n - 1)) % 2 ^ 64 := by
    rw [← hI.env.ev]; exact VG.Proof.Bignum.word_of_wv u.mem H (arr l aE) l.W (by omega_arith)
  refine WP.mono (load_ok (o := oV l) (d := arr l aE) (n := n) (V := word u.mem H (arr l aE + 8 * (n - 1))) hE₁.rbx hE₁.rdi ((e₁.gpr _).trans hI.r15) hn
    (by omega_arith) (hE₁.erd (n - 1) (by omega_arith)) (by rw [e₁.2.1]) (hE₁.scr.st (by omega_arith)))
    fun u₂ ⟨m₂, r14₂, k₂, x₂⟩ => ?_
  have ow : Outside B (oV l) 8 u₁.mem u₂.mem := by
    rw [m₂]; exact VG.Proof.Bignum.writeW_outside _ B _ (by omega_arith)
  have fw : Frm B (wrs l) u₁.mem u₂.mem := Frm.of_outside ow mem_wrs2
  have K₂ := (hI.keep.trans e₁.1).trans k₂
  have I₀ : WN l B H c k b s n (word u.mem H (arr l aE + 8 * (n - 1))) 0 u₂ :=
    ⟨(k₂.gpr (by decide)).trans ((e₁.gpr _).trans hI.r15),
      hE₁.frame hl ((k₂.gpr (by decide)).trans hE₁.rbx) ((k₂.gpr (by decide)).trans hE₁.rdi)
        ((k₂.gpr (by decide)).trans hE₁.r12) k₂.2.1 k₂.2.2 fw,
      wrep_out hl ow (.inl (by omega_arith)) (by omega_arith) (by rw [e₁.2.1]; exact hI.rep), hI.lt,
      by rw [ow.word (.inr (by omega_arith)) (by omega_arith), e₁.2.1]; exact hI.flag,
      by rw [m₂, VG.Proof.Bignum.word_writeW_self, Nat.mul_zero, BitVec.shiftLeft_zero],
      hI.frm.trans (by rw [← e₁.2.1]; exact fw), K₂.mono (by decide), by rw [x₂, e₁.2.2, hI.mx]⟩
  exact VG.Proof.MlKem.X86_64.wp_countdown (cnt := .r14) (N := 32) (by decide) (by decide)
    (fun t' v => WN l B H c k b s n (word u.mem H (arr l aE + 8 * (n - 1))) t' v) (fun t' ht v hJ h14 =>
      pstep_ok hl hV hn hW ht hJ h14) (fun _ h => h) I₀ r14₂

/-- The windows of `E`, from `y := T_0` and a clear flag, and the last pass:
the flag at `oF` is the mask of `mrIteration`'s result by windows of 2 bits. -/
theorem windows_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b : Nat} (h : WEnv l B H c k b s) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (windows l)) s fun t =>
      word t.mem B (oF l) = mask (wEnd c (kRun 2 c b (mrE c) (32 * l.W) (32 * l.W))).2 ∧
      t.gpr .rbp = s.gpr .rbp ∧
      t.gpr .rbx = B ∧ t.gpr .rdi = H ∧ t.gpr .rsp = s.gpr .rsp ∧ t.gpr .r12 = mask52 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr ∧
      Frm B [(oY l, 2 * l.NB), (oV l, 8), (oF l, 8)] s.mem t.mem := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13⟩ := MrOk.lay hl
  unfold windows
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyN_ok hl (o := oY l) (a := oT l 0) h.rbx h.scr z0 (by omega_arith) (by omega_arith)
    (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) fun u₁ ⟨hc₁, o₁, k₁, x₁⟩ => ?_
  have hs₁ := h.scr.congr k₁.2.2
  refine WP.mono (init_ok (o := oF l) ((k₁.gpr (by decide)).trans h.rbx) z12 (hs₁.st (by omega_arith)))
    fun u₂ ⟨m₂, r15₂, k₂, x₂⟩ => ?_
  have ow : Outside B (oF l) 8 u₁.mem u₂.mem := by
    rw [m₂]; exact VG.Proof.Bignum.writeW_outside _ B _ (by omega_arith)
  have f₁ : Frm B (wrs l) s.mem u₁.mem := Frm.of_outside (o₁.mono (Nat.le_refl _) (by omega_arith)) mem_wrs1
  have f₂ : Frm B (wrs l) s.mem u₂.mem := f₁.trans (Frm.of_outside ow mem_wrs3)
  have K₂ := k₁.trans k₂
  have e0 : kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - l.W)) = (1, false) := by
    rw [Nat.sub_self, Nat.mul_zero]; rfl
  have hc1 : 1 < c := by have := h.three; omega_arith
  have I₀ : OI l B H c k b s l.W u₂ := by
    refine ⟨Nat.le_refl _, r15₂, h.frame hl ((K₂.gpr (by decide)).trans h.rbx) ((K₂.gpr (by decide)).trans h.rdi)
      ((K₂.gpr (by decide)).trans h.r12) K₂.2.1 K₂.2.2 f₂, ?_, by rw [e0]; exact hc1, ?_, f₂,
      K₂.mono (by decide), by rw [x₂, x₁]⟩
    · rw [e0]
      exact wrep_out hl ow (.inl (by omega_arith)) (by omega_arith)
        (rep_congr (rep_limbs hc₁ (h.tab.t 0 (by decide))) (by rw [Nat.pow_zero]))
    · rw [e0, m₂]; exact VG.Proof.Bignum.word_writeW_self _ _ _ _
  refine WP.loop (fun n u => OI l B H c k b s n u) (fun n u hI => ?_) l.W u₂ I₀
  refine WP.seq ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- The last pass.
    unfold VG.Impl.MillerRabin.X86_64.Ifma.word
    refine WP.seq (isLast_ite (fun _ u₁ e₁ => ?_) (fun h' => absurd hI.r15 h'))
    refine WP.mono (mov14_ok u₁) fun u₂ ⟨r14, m, k, x⟩ => ?_
    have hE₂ := (hI.env.same hl e₁).keep hl k (by decide) (by decide) (by decide) m
    refine WP.loop (fun _ v => v = u₂) (fun _ v hv => ?_) 0 u₂ rfl
    subst hv
    have r15₂ : v.gpr .r15 = BitVec.ofNat 64 0 := (k.gpr (by decide)).trans ((e₁.gpr _).trans hI.r15)
    refine WP.mono (lastW_ok hl (y := (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - 0))).1)
      (P := (kRun 2 c b (mrE c) (32 * l.W) (32 * (l.W - 0))).2) hE₂ (by rw [m, e₁.2.1]; exact hI.rep) hI.lt (by rw [m, e₁.2.1]; exact hI.flag)
      r15₂ r14) fun t ⟨e, f, z, kt, xt, fr⟩ => .inl ⟨by simp [eval, z], ?_⟩
    refine WP.mono (next_ok (n := 0) ((kt.gpr (by decide)).trans r15₂) (by decide))
      fun t' ⟨_, z', m', k', x'⟩ => .inl ⟨by simp [eval, z'], ?_⟩
    have K := (((hI.keep.trans e₁.1).trans k).trans kt).trans k'
    refine ⟨by rw [m', f, Nat.sub_zero], K.gpr (by decide), (k'.gpr (by decide)).trans e.rbx,
      (k'.gpr (by decide)).trans e.rdi, K.gpr (by decide), (k'.gpr (by decide)).trans e.r12, K.2.1, K.2.2,
      by rw [x', xt, x, e₁.2.2, hI.mx], ?_⟩
    rw [m']
    exact (hI.frm.trans (by rw [m, e₁.2.1]; exact Frm.refl _ _ _)).trans fr
  · refine WP.mono (pass_ok hl hI hn) fun t hJ => ?_
    refine WP.mono (next_ok hJ.r15 (by have := hI.le; omega_arith)) fun t' ⟨r15', z', m', k', x'⟩ =>
      .inr ⟨by simp [eval, z', show n ≠ 0 by omega_arith], n - 1, by omega_arith, ?_⟩
    have e32 : 32 * (l.W - (n - 1)) = 32 * (l.W - n) + 32 := by have := hI.le; omega_arith
    refine ⟨by have := hI.le; omega_arith,
      by rw [r15', VG.Proof.MlKem.X86_64.ofNat64_pred hn (by have := hI.le; omega_arith)],
      hJ.env.keep hl k' (by decide) (by decide) (by decide) m', by rw [e32, m']; exact hJ.rep,
      by rw [e32]; exact hJ.lt, by rw [e32, m']; exact hJ.flag, by rw [m']; exact hJ.frm,
      (hJ.keep.trans k').mono (by decide), by rw [x', hJ.mx]⟩

end VG.Proof.MillerRabin.X86_64.Ifma
