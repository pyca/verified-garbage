module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Init
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: the working space as values

`KE s0 V F s`: the body's state (`St`, with every array counted as used),
the arrays holding `V` (`num m B w j = V j`), the flag slots `X0`–`X8`
holding `F`, and the extra word of the divisor's array `aDv` zero. The key
routines, restated on `KE` (as PPC64LE's `KS`): each updates `V` or `F`
(`upd`), and `St` carries the registers the body keeps and the frame.
`KE.of_st` builds it from any `St`, with the memory's values.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs copy sub3 sel eqS bitOf andS stBorrow sOdd sB sC)
open VG.Impl.RsaKeyGen.RISCV64.Key (aZero)
open VG.Impl.Rsa.RISCV64.Div (div)
open VG.Impl.RsaKeyGen.RISCV64.Key (nArr aDv aT X0 X1 X2 X3 X4 X5 X6 X7 X8 notS andNotS selS ltS mulTo invOf)

/-- The flag slots. -/
abbrev flags : List Nat := [X0, X1, X2, X3, X4, X5, X6, X7, X8]

/-- Every array. -/
abbrev allArrs : List Nat := List.range nArr

/-- `V` with `v` at `j`. -/
def upd (V : Nat → Nat) (j v : Nat) : Nat → Nat := fun i => if i = j then v else V i

@[simp] theorem upd_self (V : Nat → Nat) (j v : Nat) : upd V j v j = v := by simp [upd]

theorem upd_ne {V : Nat → Nat} {j v i : Nat} (h : i ≠ j) : upd V j v i = V i := by simp [upd, h]

/-- `j` is not `a`, for `a` in a list without `j`. -/
theorem ne_of_nm {j a : Nat} {l : List Nat} (hn : j ∉ l) (ha : a ∈ l := by decide) : j ≠ a :=
  fun h => hn (h ▸ ha)

/-- Values through the environments of the steps: `simp only` with the
steps' equations, the side conditions (distinct arrays) by `decide`. -/
macro "vsimp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

theorem flag01 (c : Prop) [Decidable c] : (if c then 1 else 0 : Nat) ≤ 1 := by split <;> omega

/-- `a - b` modulo `2^(64 w)`. -/
def subW (w a b : Nat) : Nat := (a + 2 ^ (64 * w) - b) % 2 ^ (64 * w)

theorem subW_lt (w a b : Nat) : subW w a b < 2 ^ (64 * w) := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem sub_val {x a b c M : Nat} (e : x + b = a + M * c) (hc : c ≤ 1) (hx : x < M) (ha : a < M)
    (hb : b < M) : x = (a + M - b) % M ∧ c = (if a < b then 1 else 0) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · have : b ≤ a := by omega
    refine ⟨?_, by simp only [show ¬ a < b by omega, ↓reduceIte]⟩
    rw [show a + M - b = (a - b) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have : a < b := by
      by_contra hh
      omega
    refine ⟨?_, by simp only [this, ↓reduceIte]⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## The state -/

theorem St.all {s0 s : State} {used : List Nat} (h : St s0 used s) : St s0 allArrs s :=
  ⟨h.cb, h.ws, fun _ hj hu => absurd (List.mem_range.mpr hj) hu⟩

structure KE (s0 : State) (V F : Nat → Nat) (s : State) : Prop where
  st : St s0 allArrs s
  arrs : ∀ j < nArr, num s.mem (bOf s0) (wOf s0) j = V j
  flg : ∀ d ∈ flags, slot s.mem (bOf s0) d = F d
  dv : word s.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0

theorem KE.of_st {s0 s : State} {used : List Nat} (h : St s0 used s)
    (hdv : word s.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0) :
    KE s0 (fun j => num s.mem (bOf s0) (wOf s0) j) (fun d => slot s.mem (bOf s0) d) s :=
  ⟨h.all, fun _ _ => rfl, fun _ _ => rfl, hdv⟩

theorem KE.ws {s0 s : State} {V F : Nat → Nat} (e : KE s0 V F s) : Ws s (bOf s0) (zOf s0) (wOf s0) nArr :=
  e.st.ws

theorem KE.lt {s0 s : State} {V F : Nat → Nat} (e : KE s0 V F s) {j : Nat} (hj : j < nArr) :
    V j < 2 ^ (64 * wOf s0) := by
  rw [← e.arrs j hj]; exact wordsVal_lt _ _ _ _

/-- An update of the arrays' values, as a fresh environment. -/
theorem KE.vx {s0 s : State} {V F : Nat → Nat} {o v : Nat} (h : KE s0 (upd V o v) F s) :
    ∃ V', KE s0 V' F s ∧ V' o = v ∧ ∀ j, j ≠ o → V' j = V j :=
  ⟨_, h, upd_self _ _ _, fun _ hj => upd_ne hj⟩

/-- An update of the flags, as a fresh environment. -/
theorem KE.fx {s0 s : State} {V F : Nat → Nat} {d x : Nat} (h : KE s0 V (upd F d x) s) :
    ∃ F', KE s0 V F' s ∧ F' d = x ∧ ∀ e, e ≠ d → F' e = F e :=
  ⟨_, h, upd_self _ _ _, fun _ he => upd_ne he⟩

theorem flag_hdr : ∀ d ∈ flags, 96 ≤ d ∧ d + 8 ≤ hdr := by decide

theorem flag_al : ∀ d ∈ flags, d % 8 = 0 := by decide

theorem flag_sep : ∀ d ∈ flags, ∀ y ∈ flags, y ∉ [d] → ∀ d' ∈ [d], y + 8 ≤ d' ∨ d' + 8 ≤ y := by decide

/-- `KE` after a step writing the arrays `js` and the slots `ds`, keeping the body's registers. -/
theorem KE.next {s0 s t : State} {V F V' F' : Nat → Nat} (e : KE s0 V F s)
    (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr) {js ds : List Nat}
    (f : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ hdr) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs)
    (hV : ∀ j < nArr, j ∉ js → V' j = V j) (hV' : ∀ j ∈ js, num t.mem (bOf s0) (wOf s0) j = V' j)
    (hF : ∀ d ∈ flags, d ∉ ds → F' d = F d) (hF' : ∀ d ∈ ds, d ∈ flags → slot t.mem (bOf s0) d = F' d)
    (hdv : aDv ∈ js → word t.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0)
    (hsep : ∀ x ∈ flags, x ∉ ds → ∀ d ∈ ds, x + 8 ≤ d ∨ d + 8 ≤ x) : KE s0 V' F' t := by
  have st := (e.st.step ws f hjs hds k hr).all
  refine ⟨st, fun j hj => ?_, fun d hd => ?_, ?_⟩
  · by_cases hm : j ∈ js
    · exact hV' j hm
    · rw [hV j hj hm, ← e.arrs j hj]
      exact f.num (fun x hx e => hm (e ▸ hx)) (fun d hd => (hds d hd).2) (e.st.fit hj)
  · by_cases hm : d ∈ ds
    · exact hF' d hm hd
    · rw [hF d hd hm, ← e.flg d hd]
      exact f.slot (flag_hdr d hd).2 (hsep d hd hm)
  · by_cases hm : aDv ∈ js
    · exact hdv hm
    · rw [← e.dv]
      exact f.word (i := wOf s0) (by omega) (fun x hx e => hm (e ▸ hx)) (fun d hd => (hds d hd).2)
        (e.st.fit (by decide))

/-- A step that writes one array. -/
theorem KE.arr1 {s0 s t : State} {V F : Nat → Nat} (e : KE s0 V F s)
    (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr) {o v : Nat} (ho : o < nArr)
    (f : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) [o] [] s.mem t.mem) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs) (hv : num t.mem (bOf s0) (wOf s0) o = v)
    (hdv : o = aDv → word t.mem (bOf s0) (arr (wOf s0) aDv + 8 * wOf s0) = 0) :
    KE s0 (upd V o v) F t := by
  refine e.next ws f (by simpa using ho) (by simp) k hr (fun j _ hn => ?_) (fun j hj => ?_)
    (fun _ _ _ => rfl) (fun d hd => by simp at hd) (fun hd => hdv (List.mem_singleton.mp hd).symm) (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hj, upd_self, hv]

/-- A step that writes one flag. -/
theorem KE.flag1 {s0 s t : State} {V F : Nat → Nat} (e : KE s0 V F s)
    (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr) {d x : Nat} (hd : d ∈ flags)
    (f : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) [] [d] s.mem t.mem) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs) (hx : slot t.mem (bOf s0) d = x) :
    KE s0 V (upd F d x) t := by
  have hsep := flag_sep d hd
  refine e.next ws f (by simp) (by simpa using flag_hdr d hd) k hr (fun _ _ _ => rfl)
    (fun j hj => by simp at hj) (fun y _ hn => ?_) (fun y hy _ => ?_) (fun hj => by simp at hj) hsep
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [upd_ne hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [hy, upd_self, hx]

/-! ## The routines on values -/

section
variable {s0 s : State} {V F : Nat → Nat}

/-- The extra word of an array, kept by a copy into it. -/
theorem copy_dv {m m' : Mem} {B : Addr} {w : Nat} (o : Outside B (arr w aDv) (8 * w) m m')
    (fit : arr w aDv + S w ≤ 2 ^ 64) :
    word m' B (arr w aDv + 8 * w) = word m B (arr w aDv + 8 * w) := by
  have hS : S w = 8 * (w + 2) := rfl
  have h1 := Mont.Outside.wordsVal o (d := arr w aDv + 8 * w) (k := 1) (by omega_arith) (by omega_arith)
  simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at h1
  exact BitVec.eq_of_toNat_eq h1

/-- `copy o a`. -/
theorem copyE (e : KE s0 V F s) {o a : Nat} (ho : o < nArr := by decide) (ha : a < nArr := by decide)
    (hoa : o ≠ a := by decide) :
    WP isa (copy o a) s (KE s0 (upd V o (V a)) F) := by
  refine WP.mono (copy_ok e.ws ho ha (by decide) hoa) fun t ⟨ht, ft, v, kt, ot⟩ => ?_
  refine e.arr1 ht ho ft kt (by decide) (by rw [v, e.arrs a ha]) fun h => ?_
  subst h; rw [copy_dv ot (e.st.fit (by decide)), e.dv]

/-- `sub3 o a b`, with the borrow in `t4`. -/
theorem sub3E (e : KE s0 V F s) {o a b : Nat} (ho : o < nArr := by decide) (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (hoa : o ≠ a := by decide) (hob : o ≠ b := by decide)
    (hodv : o ≠ aDv := by decide) :
    WP isa (sub3 o a b) s fun t => KE s0 (upd V o (subW (wOf s0) (V a) (V b))) F t ∧
      (t.gpr .t4).toNat = (if V a < V b then 1 else 0) := by
  refine WP.mono (sub3_ok e.ws ho ha hb (by decide) hoa hob) fun t ⟨ht, ft, v, b4, kt⟩ => ?_
  rw [e.arrs a ha, e.arrs b hb] at v
  obtain ⟨e1, e2⟩ := sub_val v b4 (wordsVal_lt _ _ _ _) (e.lt ha) (e.lt hb)
  exact ⟨e.arr1 ht ho ft kt (by decide) e1 (fun h => absurd h hodv), e2⟩

/-- `sel o a b sl`, the slot a flag. -/
theorem selE (e : KE s0 V F s) {o a b sl : Nat} (ho : o < nArr := by decide) (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (hoa : o ≠ a := by decide) (hob : o ≠ b := by decide)
    (hodv : o ≠ aDv := by decide) (hsl : sl ∈ flags := by decide) (bit : F sl ≤ 1) :
    WP isa (sel o a b sl) s (KE s0 (upd V o (if F sl = 0 then V a else V b)) F) := by
  rw [← e.flg sl hsl] at bit ⊢
  refine WP.mono (sel_ok e.ws ho ha hb (by decide) hoa hob (flag_hdr sl hsl).2 (flag_al sl hsl) bit)
    fun t ⟨ht, ft, v, kt⟩ => ?_
  exact e.arr1 ht ho ft kt (by decide) (by rw [v, e.arrs a ha, e.arrs b hb]) (fun h => absurd h hodv)

/-- `eqS d a b`, the slot a flag. -/
theorem eqSE (e : KE s0 V F s) {d a b : Nat} (ha : a < nArr := by decide) (hb : b < nArr := by decide)
    (hd : d ∈ flags := by decide) :
    WP isa (eqS d a b) s (KE s0 V (upd F d (if V a = V b then 1 else 0))) := by
  refine WP.mono (eqS_ok e.ws ha hb (by decide) (flag_hdr d hd).2 (flag_al d hd)) fun t ⟨ht, ft, v, kt⟩ => ?_
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.arrs a ha, e.arrs b hb])

/-! The slot operations are blocks: in continuation form, for blocks that go on. -/

/-- `bitOf d j`. -/
theorem bitOfE (e : KE s0 V F s) {d j : Nat} (hj : j < nArr := by decide) (hd : d ∈ flags := by decide)
    {rest : List Instr} {Q : State → Prop} (k : ∀ t, KE s0 V (upd F d (V j % 2)) t → WP isa (.block rest) t Q) :
    WP isa (.block (bitOf d j ++ rest)) s Q := by
  refine WP.block_append (WP.mono (bitOf_ok e.ws hj (by decide) (flag_hdr d hd).2 (flag_al d hd))
    fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.arrs j hj])

/-- `stBorrow d`, `t4` the borrow. -/
theorem stBorrowE (e : KE s0 V F s) {d c : Nat} (hd : d ∈ flags := by decide) (h4 : (s.gpr .t4).toNat = c)
    {rest : List Instr} {Q : State → Prop} (k : ∀ t, KE s0 V (upd F d c) t → WP isa (.block rest) t Q) :
    WP isa (.block (stBorrow d ++ rest)) s Q := by
  refine WP.block_append (WP.mono (stBorrow_ok e.ws (flag_hdr d hd).2 (flag_al d hd))
    fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, h4])

/-- `andS d a b`. -/
theorem andSE (e : KE s0 V F s) {d a b : Nat} (hd : d ∈ flags := by decide) (ha : a ∈ flags := by decide)
    (hb : b ∈ flags := by decide) (ba : F a ≤ 1) (bb : F b ≤ 1)
    {rest : List Instr} {Q : State → Prop} (k : ∀ t, KE s0 V (upd F d (F a * F b)) t → WP isa (.block rest) t Q) :
    WP isa (.block (andS d a b ++ rest)) s Q := by
  rw [← e.flg a ha] at ba; rw [← e.flg b hb] at bb
  refine WP.block_append (WP.mono (andS_ok e.ws (flag_hdr d hd).2 (flag_al d hd) (flag_hdr a ha).2
    (flag_al a ha) (flag_hdr b hb).2 (flag_al b hb) ba bb) fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.flg a ha, e.flg b hb])

/-- `notS d a`. -/
theorem notSE (e : KE s0 V F s) {d a : Nat} (hd : d ∈ flags := by decide) (ha : a ∈ flags := by decide)
    (ba : F a ≤ 1)
    {rest : List Instr} {Q : State → Prop} (k : ∀ t, KE s0 V (upd F d (1 - F a)) t → WP isa (.block rest) t Q) :
    WP isa (.block (notS d a ++ rest)) s Q := by
  rw [← e.flg a ha] at ba
  refine WP.block_append (WP.mono (notS_ok e.ws (flag_hdr d hd).2 (flag_al d hd) (flag_hdr a ha).2
    (flag_al a ha) ba) fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.flg a ha])

/-- `andNotS d a b`. -/
theorem andNotSE (e : KE s0 V F s) {d a b : Nat} (hd : d ∈ flags := by decide) (ha : a ∈ flags := by decide)
    (hb : b ∈ flags := by decide) (ba : F a ≤ 1) (bb : F b ≤ 1)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KE s0 V (upd F d ((1 - F a) * F b)) t → WP isa (.block rest) t Q) :
    WP isa (.block (andNotS d a b ++ rest)) s Q := by
  rw [← e.flg a ha] at ba; rw [← e.flg b hb] at bb
  refine WP.block_append (WP.mono (andNotS_ok e.ws (flag_hdr d hd).2 (flag_al d hd) (flag_hdr a ha).2
    (flag_al a ha) (flag_hdr b hb).2 (flag_al b hb) ba bb) fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.flg a ha, e.flg b hb])

/-- `selS d a b c`: `d := c ? b : a`. -/
theorem selSE (e : KE s0 V F s) {d a b c : Nat} (hd : d ∈ flags := by decide) (ha : a ∈ flags := by decide)
    (hb : b ∈ flags := by decide) (hc : c ∈ flags := by decide) (ba : F a ≤ 1) (bb : F b ≤ 1) (bc : F c ≤ 1)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KE s0 V (upd F d (if F c = 0 then F a else F b)) t → WP isa (.block rest) t Q) :
    WP isa (.block (selS d a b c ++ rest)) s Q := by
  rw [← e.flg a ha] at ba; rw [← e.flg b hb] at bb; rw [← e.flg c hc] at bc
  refine WP.block_append (WP.mono (selS_ok e.ws (flag_hdr d hd).2 (flag_al d hd) (flag_hdr a ha).2
    (flag_al a ha) (flag_hdr b hb).2 (flag_al b hb) (flag_hdr c hc).2 (flag_al c hc) ba bb bc)
    fun t ⟨ht, ft, v, kt⟩ => k t ?_)
  exact e.flag1 ht hd ft kt (by decide) (by rw [v, e.flg a ha, e.flg b hb, e.flg c hc])

/-- `ltS d a b`: the flag `d` := `[a] < [b]`, through `aT`. -/
theorem ltSE (e : KE s0 V F s) {d a b : Nat} (ha : a < nArr := by decide) (hb : b < nArr := by decide)
    (haT : aT ≠ a := by decide) (hbT : aT ≠ b := by decide) (hd : d ∈ flags := by decide) :
    WP isa (seqs (ltS d a b)) s
      (KE s0 (upd V aT (subW (wOf s0) (V a) (V b))) (upd F d (if V a < V b then 1 else 0))) := by
  change WP isa (.seq (sub3 aT a b) (.block (stBorrow d))) s _
  refine WP.seq (WP.mono (sub3E e (o := aT) (a := a) (b := b) (ha := ha) (hb := hb) (hoa := haT) (hob := hbT))
    fun t ⟨et, b4⟩ => ?_)
  rw [← List.append_nil (stBorrow d)]
  exact stBorrowE et (d := d) (hd := hd) b4 fun u eu => WP.block_nil eu

/-- `div q r aDv t`: `[q] := [q] / [aDv]`, `[r] := [q] % [aDv]`, for `[aDv] > 0`. -/
theorem divE (e : KE s0 V F s) {q r t : Nat} (hq : q < nArr := by decide) (hr : r < nArr := by decide)
    (ht : t < nArr := by decide) (hqr : q ≠ r := by decide) (hqd : q ≠ aDv := by decide)
    (hqt : q ≠ t := by decide) (hrd : r ≠ aDv := by decide) (hrt : r ≠ t := by decide)
    (hdt : aDv ≠ t := by decide) :
    WP isa (div q r aDv t) s fun u => ∃ V', KE s0 V' F u ∧
      (∀ j < nArr, j ≠ q → j ≠ r → j ≠ t → V' j = V j) ∧
      (0 < V aDv → V' q = V q / V aDv ∧ V' r = V q % V aDv) := by
  refine WP.mono (div_ok e.ws hq hr (by decide) ht (by decide) hqr hqd hqt hrd hrt hdt e.dv)
    fun u ⟨hu, fu, ku, _, hv⟩ => ?_
  refine ⟨fun j => if j = q ∨ j = r ∨ j = t then num u.mem (bOf s0) (wOf s0) j else V j, ?_, ?_, ?_⟩
  · refine e.next hu fu (by simp [hq, hr, ht]) (by simp) ku (by decide) (fun j _ hn => ?_) (fun j hj => ?_)
      (fun _ _ _ => rfl) (fun d hd => by simp at hd) (fun hd => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [hn, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [hj, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with h | h | h
      · exact absurd h.symm hqd
      · exact absurd h.symm hrd
      · exact absurd h hdt
  · intro j _ a b c; simp [a, b, c]
  · intro hpos
    rw [← e.arrs aDv (by decide)] at hpos
    obtain ⟨h1, -, h3, -⟩ := hv hpos
    simp only [true_or, or_true, ↓reduceIte]
    rw [h1, h3, e.arrs q hq, e.arrs aDv (by decide)]
    exact ⟨rfl, rfl⟩

/-- `mulTo o a b`: `[o] := [a] [b] mod 2^(64 w)`. -/
theorem mulToE (e : KE s0 V F s) {o a b : Nat} (ho : o < nArr := by decide) (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (hoa : o ≠ a := by decide) (hob : o ≠ b := by decide)
    (hoz : o ≠ aZero := by decide) (hodv : o ≠ aDv := by decide) (zero : V aZero = 0) :
    WP isa (mulTo o a b) s (KE s0 (upd V o (V a * V b % 2 ^ (64 * wOf s0))) F) := by
  refine WP.mono (mulTo_ok e.ws ho ha hb (by decide) (by decide) hoa hob hoz
    (by rw [e.arrs aZero (by decide), zero])) fun t ⟨ht, ft, _, v, kt⟩ => ?_
  exact e.arr1 ht ho ft kt (by decide) (by rw [v, e.arrs a ha, e.arrs b hb]) (fun h => absurd h hodv)

/-- `add o a b aZero t` (RdOps' `add`): `[o] := [a] + [b] mod 2^(64 w)`, through `t`. -/
theorem addE (e : KE s0 V F s) {o a b t : Nat} (ho : o < nArr := by decide) (ha : a < nArr := by decide)
    (hb : b < nArr := by decide) (ht : t < nArr := by decide) (htz : t ≠ aZero := by decide)
    (htb : t ≠ b := by decide) (hta : t ≠ a := by decide) (hoa : o ≠ a := by decide)
    (hot : o ≠ t := by decide) (hodv : o ≠ aDv := by decide) (htdv : t ≠ aDv := by decide) (zero : V aZero = 0) :
    WP isa (VG.Impl.Rsa.RISCV64.RecoverDet.add o a b aZero t) s fun u => ∃ V', KE s0 V' F u ∧
      (∀ j < nArr, j ≠ o → j ≠ t → V' j = V j) ∧ V' o = (V a + V b) % 2 ^ (64 * wOf s0) := by
  refine WP.mono (add_ok e.ws ho ha hb (by decide) ht (by decide) htz htb hta hoa hot
    (by rw [e.arrs aZero (by decide), zero])) fun u ⟨hu, fu, v, ku⟩ => ?_
  refine ⟨fun j => if j = t ∨ j = o then num u.mem (bOf s0) (wOf s0) j else V j, ?_, ?_, ?_⟩
  · refine e.next hu fu (by simp [ht, ho]) (by simp) ku (by decide) (fun j _ hn => ?_) (fun j hj => ?_)
      (fun _ _ _ => rfl) (fun d hd => by simp at hd) (fun hd => ?_) (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [hn, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      simp only [hj, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with h | h
      · exact absurd h.symm htdv
      · exact absurd h.symm hodv
  · intro j _ a b; simp [a, b]
  · simp only [or_true, ↓reduceIte]
    rw [v, e.arrs a ha, e.arrs b hb]

/-- `invOf a m k`, `k` setting `s8 := n`: `gcd` in array 1, the inverse in array 3. -/
theorem invOfE [VG.Proof.Rsa.RISCV64.InvLaw] (e : KE s0 V F s) {a m n : Nat} {k : List Instr} (ha : a < nArr := by decide)
    (hm : m < nArr := by decide) (ha15 : 15 ≤ a := by decide) (hm15 : 15 ≤ m := by decide)
    (hw : 4 ≤ wOf s0) (hn1 : 1 ≤ n) (hnw : n ≤ 2 * wOf s0)
    (hk : ∀ u : State, (∀ r ∉ opRegs, u.gpr r = s.gpr r) →
      WP isa (.block k) u fun v => (v.gpr .s8 = BitVec.ofNat 64 n ∧ v.mem = u.mem) ∧ Keep [.s8] u v)
    (odd : V m % 2 = 1) (gt : 1 < V m) (xlt : V a < 2 ^ (32 * n)) (mlt : V m < 2 ^ (32 * n)) :
    WP isa (invOf a m k) s fun u => ∃ V', KE s0 V' F u ∧
      (∀ j < nArr, j ∉ invOfArrs → V' j = V j) ∧
      V' 1 = Nat.gcd (V a) (V m) ∧ ((V m : Nat) : Int) ∣ (V' 3 : Int) * V a - V' 1 ∧ V' 3 < V m := by
  refine WP.mono (invOf_ok e.ws (by decide) (by decide) hw ha hm ha15 hm15 hn1 hnw hk
    (by rw [e.arrs a ha]; exact xlt) (by rw [e.arrs m hm]; exact mlt) (by rw [e.arrs m hm]; exact odd))
    fun u ⟨hu, fu, ku, hv⟩ => ?_
  rw [e.arrs m hm, e.arrs a ha] at hv
  obtain ⟨g1, g2, g3⟩ := hv gt
  have hj : ∀ j ∈ invOfArrs, j < nArr := by decide
  refine ⟨fun j => if j ∈ invOfArrs then num u.mem (bOf s0) (wOf s0) j else V j, ?_, ?_, ?_, ?_, ?_⟩
  · refine e.next hu fu hj (by simp) ku (by decide) (fun j _ hn => ?_) (fun j hj => ?_)
      (fun _ _ _ => rfl) (fun d hd => by simp at hd) (fun hd => absurd hd (by decide)) (by simp)
    · simp only [hn, ↓reduceIte]
    · simp only [hj, ↓reduceIte]
  · intro j _ hn; simp only [hn, ↓reduceIte]
  · simp only [show (1 : Nat) ∈ invOfArrs by decide, ↓reduceIte]; exact g1
  · simp only [show (1 : Nat) ∈ invOfArrs by decide, show (3 : Nat) ∈ invOfArrs by decide, ↓reduceIte]
    exact g2
  · simp only [show (3 : Nat) ∈ invOfArrs by decide, ↓reduceIte]; exact g3

end

end VG.Proof.RsaKeyGen.RISCV64.Key
