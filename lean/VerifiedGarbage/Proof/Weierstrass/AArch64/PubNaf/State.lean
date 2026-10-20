module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Proof.Weierstrass.Naf5
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# The public NAF: what its proofs share

The public NAF (`PubNaf`) keeps its numbers where the window method does
(`WinLay`, `WinA`), and its table of the odd multiples `[1]P, [3]P, …, [15]P`
in the window method's eight entries, in Jacobian coordinates (`OddTbl`).
`NSt` is what holds from the table on; `NSt.inv` and `NSt.post` go from it to
the field programs' invariant (`Inv`) and back.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.PubNaf (cacheAt)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The cache, as one range. -/
def cacheW (K : WinCfg) : List (Nat × Nat) := [(cacheAt K 1, 128 * K.M.n)]

/-- The cache lies above every slot, the modulus, its temporary area and the
digits, and within the working space. -/
structure CacheLay (K : WinCfg) (size : Nat) : Prop where
  slots : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ cacheAt K 1
  tmp : K.M.tmp + 8 * K.M.n ≤ cacheAt K 1
  mo : K.M.mo + 8 * K.M.n ≤ cacheAt K 1
  bits : K.bits + 4 * K.J ≤ cacheAt K 1
  top : cacheAt K 1 + 128 * K.M.n ≤ size
  al : cacheAt K 1 % 8 = 0

/-- The window method's layout, with points of consecutive coordinates `R`
and `E` (which the table's copies read and write), digits for `64 n + 1`
bytes, a modulus of other than four words (whose doubling is not
P-256's forwarded one), and the cache above it all (`CacheLay`). -/
structure NafLay (K : WinCfg) (size : Nat) : Prop where
  win : WinLay K size
  al : WinA K
  n4 : K.M.n ≠ 4
  n6 : K.M.n ≤ 9
  digits : 64 * K.M.n + 1 ≤ 4 * K.J
  rxy : K.R.y = K.R.x + 8 * K.M.n
  rxz : K.R.z = K.R.x + 16 * K.M.n
  exy : K.E.y = K.E.x + 8 * K.M.n
  exz : K.E.z = K.E.x + 16 * K.M.n
  cache : CacheLay K size

/-- The registers the multiplication changes. -/
def nafClob (n : Nat) : List Reg := .x20 :: combClob n

theorem x20_not_clob' {n : Nat} (h : n < 10) : Reg.x20 ∉ clob n := by
  have : ∀ n < 10, Reg.x20 ∉ clob n := by decide
  exact this n h

theorem clob_nafClob {n : Nat} : ∀ r ∈ clob n, r ∈ nafClob n := fun r hr =>
  List.mem_cons_of_mem _ (clob_combClob r hr)

theorem nafClob_mem {n : Nat} {r : Reg}
    (h : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17, .x19, .x20, .x9]) : r ∈ nafClob n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst h
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (combClob_mem (by simp))
  · exact List.mem_cons_of_mem _ (by simp [combClob])
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (by simp [combClob])

/-- Entries `1 … 8` of the table hold `[1]P, [3]P, …, [15]P`. -/
def OddTbl (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (m : Nat) (s : State) : Prop :=
  ∀ a, 1 ≤ a → a ≤ m →
    (∀ x ∈ [(K.tblPt a).x, (K.tblPt a).y, (K.tblPt a).z], wordsVal s.mem base x K.M.n < C.p) ∧
    InvJ C (tmv C K.M.n base s (K.tblPt a).x) (tmv C K.M.n base s (K.tblPt a).y)
      (tmv C K.M.n base s (K.tblPt a).z) (mul (2 * a - 1) P)

/-- The table survives what the loop writes. -/
theorem OddTbl.unch {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat} (hL : WinLay K size)
    {P : Point C} {s s' : State} (hT : OddTbl K C base P m s) (hm : m ≤ 8)
    (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : OddTbl K C base P m s' := by
  intro j h1 hjm
  have h8 : j ≤ 8 := by omega
  have T := hT j h1 hjm
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
    have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega_using [hn, this])
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
    · exact hL.lay.tmp _ hs
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- What the multiplication reads and never writes, at the start: the slots
read only below the modulus, zero, `P` (in Jacobian coordinates) and the
digits of `k`. -/
structure NafFixed (K : WinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  ro_lt : ∀ x ∈ winRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  pt : InvJ C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  digits : ∀ t < 64 * K.M.n + 1, s₀.mem (off base (K.bits + t)) = Naf5.byte k t

/-- What holds from the table on, from `s₀` (the state before the table). -/
structure NSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State) :
    Prop where
  scr : Scr s base size
  keep : KeepRegs (nafClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : OddTbl K C base P 8 s

/-- The state after a change of `loopW` only. -/
theorem NSt.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {P : Point C} {s₀ s s' : State} (h : NSt K C base size P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (nafClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    NSt K C base size P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    h.tbl.unch hL (Nat.le_refl _) hU h.scr.nowrap⟩

/-- A change of registers only. -/
theorem NSt.regs {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {P : Point C} {s₀ s s' : State} (h : NSt K C base size P s₀ s) {rs : List Reg} (hk : Keeps rs s s')
    (hr : ∀ r ∈ rs, r ∈ nafClob K.M.n) (h0 : Reg.x0 ∉ rs) : NSt K C base size P s₀ s' :=
  h.next hL (h.scr.of_keeps hk h0) ((Keeps.regs hk).mono hr) (by rw [hk.mem]; exact Unch.refl _ _ _)

/-- The read-only slots keep their numbers. -/
theorem NSt.ro {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {P : Point C} {s₀ s : State} (h : NSt K C base size P s₀ s) (hF : NafFixed K C base s₀ P k) :
    (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hL.ro_val h.unch hn hx]; exact hF.ro_lt x hx
  · rw [hL.ro_val h.unch hn (by simp [winRo])]; exact hF.zero

/-- The digits survive what the loop writes. -/
theorem NSt.digits {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    {P : Point C} {s₀ s : State} (h : NSt K C base size P s₀ s) (hF : NafFixed K C base s₀ P k) :
    ∀ t < 64 * K.M.n + 1, s.mem (off base (K.bits + t)) = Naf5.byte k t := fun t ht => by
  have hb := hL.win.bits
  have hd := hL.digits
  rw [h.unch.byte (fun w hw => by have := hL.win.bits_w w hw; omega) (by have := h.scr.nowrap; omega)]
  exact hF.digits t ht

/-- The field programs' invariant, from the state, for slots below `p`. -/
theorem NSt.inv {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {P : Point C} {s₀ s : State}
    (h : NSt K C base size P s₀ s) {V : List Nat} (hsl : ∀ x ∈ V, x ∈ winSlots K)
    (hlt : ∀ x ∈ V, wordsVal s.mem base x K.M.n < C.p) :
    Inv K.M base size C.p (· ∈ winSlots K) V (tmv C K.M.n base s) s :=
  ⟨h.scr, h.mod, hsl, hlt, fun _ _ => rfl⟩

/-- The working points are among the slots written. -/
theorem pt_other {K : WinCfg} {o : Pt} (ho : o = K.R ∨ o = K.D ∨ o = K.E) :
    ∀ x ∈ [o.x, o.y, o.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases ho with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
    simp only [winOther, rcbW, List.cons_append, List.nil_append, List.mem_cons, true_or, or_true]

theorem rcbW_other {K : WinCfg} {o : Pt} (ho : o = K.R ∨ o = K.D ∨ o = K.E) :
    ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
  intro x hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h <;> subst h
  all_goals first
    | (simp only [winOther, rcbW, List.cons_append, List.nil_append, List.mem_cons, true_or, or_true]; done)
    | exact pt_other ho _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])

/-- A point operation's result, back in the state: what it wrote is in `loopW`. -/
theorem NSt.post {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {P Q : Point C} {s₀ s t : State} (h : NSt K C base size P s₀ s) {V : List Nat} {o : Pt}
    (ho : o = K.R ∨ o = K.D ∨ o = K.E)
    (hp : JacPost K.M K.S base size C (· ∈ winSlots K) V o Q s t) :
    NSt K C base size P s₀ t ∧ (∀ x ∈ [o.x, o.y, o.z], wordsVal t.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base t o.x) (tmv C K.M.n base t o.y) (tmv C K.M.n base t o.z) Q ∧
      (∀ x ∈ V, wordsVal t.mem base x K.M.n < C.p) ∧
      (∀ x ∈ V, x ∉ rcbW K.S o → wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n) := by
  obtain ⟨E, hk, hi, hj⟩ := hp
  have hU : Unch base (loopW K) s.mem t.mem := hk.unch.mono fun w hw => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, rcbW_other ho y hy, rfl⟩
    · exact Or.inr rfl
  refine ⟨h.next hL hi.scr ((⟨hk.gpr, hk.rd, hk.wr, hk.sp⟩ : KeepRegs (clob K.M.n) s t).mono
      clob_nafClob) hU, fun x hx => hi.lt x (List.mem_append_left _ hx),
    hi.point_tmv (fun x hx => List.mem_append_left _ hx) hj,
    fun x hx => hi.lt x (List.mem_append_right _ hx), fun x hx hw => ?_⟩
  have hs : x ∈ winSlots K := hi.sl x (List.mem_append_right _ hx)
  refine hk.unch.wordsVal (fun w hw' => ?_) (by have := hL.lay.le x hs; have := h.scr.nowrap; omega)
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw'
  rcases hw' with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hs (winOther_mem (rcbW_other ho y hy)) (fun e => hw (e ▸ hy))
  · exact hL.lay.tmp x hs

/-- The point operations' slots are apart: `2P` into `E`, `D + E` into `R`,
`R + E` and `2R` into `D`, and the copies `R = P`, `R = D`, `E = R`, and
`fromJ` of `E` into `R` (`z` the slots of zero). -/
theorem rcbApart_naf {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    RcbApart K.S K.P K.P K.E ∧ RcbApart K.S K.D K.E K.R ∧ RcbApart K.S K.E K.P K.R ∧
      RcbApart K.S K.E K.D K.R ∧ RcbApart K.S K.R K.R K.D ∧ RcbApart K.S K.R K.E K.D ∧
      RcbApart K.S ⟨K.zero, K.zero, K.zero⟩ K.R K.E ∧
      RcbApart K.S K.E ⟨K.zero, K.zero, K.zero⟩ K.R :=
  ⟨hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 3, 4, 5]) (lr := [16, 17, 19, 20, 21, 19, 20, 21]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 13, 14, 15, 3, 4, 5]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 3, 4, 5, 19, 20, 21]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 3, 4, 5, 13, 14, 15]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 0, 1, 2]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 3, 4, 5]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 3, 4, 5]) (lr := [16, 17, 18, 18, 18, 0, 1, 2]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 3, 4, 5, 18, 18, 18]) rfl rfl⟩

/-- What a point operation into `R`, `D` or `E` keeps and gives. -/
theorem jacPost_frame {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Q : Point C} {s t : State} (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    {V : List Nat} {o : Pt} (ho : o = K.R ∨ o = K.D ∨ o = K.E)
    (hp : JacPost K.M K.S base size C (· ∈ winSlots K) V o Q s t) :
    Scr t base size ∧ KeepRegs (clob K.M.n) s t ∧ Unch base (loopW K) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [o.x, o.y, o.z], wordsVal t.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base t o.x) (tmv C K.M.n base t o.y) (tmv C K.M.n base t o.z) Q ∧
      (∀ x ∈ V, wordsVal t.mem base x K.M.n < C.p) ∧
      (∀ x ∈ V, x ∉ rcbW K.S o → wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n) := by
  obtain ⟨E, hk, hi, hj⟩ := hp
  have hU : Unch base (loopW K) s.mem t.mem := hk.unch.mono fun w hw => by
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, rcbW_other ho y hy, rfl⟩
    · exact Or.inr rfl
  refine ⟨hi.scr, ⟨hk.gpr, hk.rd, hk.wr, hk.sp⟩, hU,
    hM.unch hU (fun w hw => winW_mo hL hM w (loopW_sub K w hw)) hs.nowrap,
    fun x hx => hi.lt x (List.mem_append_left _ hx),
    hi.point_tmv (fun x hx => List.mem_append_left _ hx) hj,
    fun x hx => hi.lt x (List.mem_append_right _ hx), fun x hx hw => ?_⟩
  have hs' : x ∈ winSlots K := hi.sl x (List.mem_append_right _ hx)
  refine hk.unch.wordsVal (fun w hw' => ?_) (by have := hL.lay.le x hs'; have := hs.nowrap; omega)
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw'
  rcases hw' with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hs' (winOther_mem (rcbW_other ho y hy)) (fun e => hw (e ▸ hy))
  · exact hL.lay.tmp x hs'

end VG.Proof.Weierstrass.AArch64.PubNaf
