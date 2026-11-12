module

public import VerifiedGarbage.Proof.Rsa.X86.KcBase
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Guard
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Eq
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The checks of an RSA key on i686: the word steps on `Stg`

The products (`mulWide`, `mulShort`), the product compared with `n`
(`eqWide`), the guard (`balanced`), the branch on it (`ifBalanced`), and
the remainder by word steps (`wordMod`), each from `Stg` to `Stg`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top val32_low top_iff sub0_beq)

theorem wordRegs_body : ∀ x ∈ [.eax, .ebx, .ecx, .edx, .esi, .ebp], x ∈ bodyRegs := by decide

/-- An argument from where the checks started. -/
theorem Stg.arg {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {i : Nat} {x : BitVec 32}
    (a : VG.Proof.Bignum.X86.CallArgument s0 g.B g.Z i x) : VG.Proof.Bignum.X86.CallArgument s g.B g.Z i x :=
  a.keep h.rest (by decide)
    (VG.Proof.Rsa.X86.KeyRt.keep_outside h.ws.ws h.keep (fun j hj => List.mem_range.mp hj) (by decide))

/-- `mulWide o a b`: `[a] [b]`, `2 w` words from array `o` on. -/
theorem Stg.mulWide_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulWide g.L o a b) s fun t => Stg g s0 A live c t ∧
      val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulWide_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp; omega) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · rw [e, h.arrs.get ha, h.arrs.get hb]

/-- `mulHalf o a b`: `[a] [b]` where both are below `2^(32 (w / 2))`, `2 w` words from array `o` on. -/
theorem Stg.mulHalf_if_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf g.L o a b) s fun t => Stg g s0 A live c t ∧
      (A a < 2 ^ (32 * (g.w / 2)) → A b < 2 ^ (32 * (g.w / 2)) →
        val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b) := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulHalf_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, fun hA hB => ?_⟩
  · refine h.next ht k (by simp; omega) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · have ea : val32 s.mem g.B (arr g.w a) g.w = A a := h.arrs.get ha
    have eb : val32 s.mem g.B (arr g.w b) g.w = A b := h.arrs.get hb
    rw [e, VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := g.w) (Nat.div_le_self _ _) (by rw [ea]; exact hA), ea,
      VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := g.w) (Nat.div_le_self _ _) (by rw [eb]; exact hB), eb]

/-- `mulHalf o a b`: `[a] [b]`, both below `2^(32 (w / 2))`, `2 w` words from array `o` on. -/
theorem Stg.mulHalf_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD)
    (hA : A a < 2 ^ (32 * (g.w / 2))) (hB : A b < 2 ^ (32 * (g.w / 2))) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulHalf g.L o a b) s fun t => Stg g s0 A live c t ∧
      val32 t.mem g.B (arr g.w o) (2 * g.w) = A a * A b :=
  WP.mono (h.mulHalf_if_ok ho ha hb hol hv) fun _ ⟨ht, e⟩ => ⟨ht, e hA hB⟩

/-- Two words are the number, when it is below `2^64`. -/
theorem val32_two {m : Mem} {B : Addr} {w j : Nat} (hw : 2 ≤ w) (hl : num m B w j < 2 ^ 64) :
    val32 m B (arr w j) 2 = num m B w j :=
  val32_low hw hl

/-- `mulShort o a b`: `[a] [b]`, `[b] < 2^64`, `w + 2` words from array `o` on. -/
theorem Stg.mulShort_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o a b : Nat} (ho : o + 1 < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (hol : ∀ j ∈ live, j ≠ o ∧ j ≠ o + 1) (hv : o ≠ aVD ∧ o + 1 ≠ aVD) (hw2 : 2 ≤ g.w) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.mulShort g.L o a b) s fun t => Stg g s0 A live c t ∧
      (A b < 2 ^ 64 → val32 t.mem g.B (arr g.w o) (g.w + 2) = A a * A b) := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulShort_ok h.ws hw2 ho (h.live_lt a ha) (h.live_lt b hb)
    (hol a ha).1 (hol a ha).2 (hol b hb).1 (hol b hb).2) fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp; omega) (by decide) r wordRegs_body
      (h.arrs_keep k (fun j hj => by simp [(hol j hj).1, (hol j hj).2]) (by decide)) h.live_lt
      (h.vd_keep k (by simp [hv.1, hv.2]) (by decide)) (h.mask_keep k (by decide))
  · intro hB
    have gb := h.arrs.get hb
    rw [e, h.arrs.get ha, val32_two hw2 (by rw [gb]; exact hB), gb]

/-- `eqWide sF o n`: whether the `2 w` words from array `o` on are `[n]`, into `sF`. -/
theorem Stg.eqWide_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {o n : Nat} (ho : o + 1 < nArr) (hn : n ∈ live) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.eqWide g.L sF o n) s fun t => Stg g s0 A live c t ∧
      slot t.mem g.B sF = if val32 s.mem g.B (arr g.w o) (2 * g.w) = A n then 1 else 0 := by
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.eqWide_ok h.ws ho (h.live_lt n hn) (by decide))
    fun t ⟨ht, k, e, r⟩ => ⟨?_, ?_⟩
  · refine h.next ht k (by simp) (by decide) r (by decide)
      (h.arrs_keep k (by simp) (by decide)) h.live_lt (h.vd_keep k (by simp) (by decide)) (h.mask_keep k (by decide))
  · rw [e, h.arrs.get hn]

/-- `balanced`: the guard into `sG`, of `n_len` (argument 1), `p_len`, `q_len` and `n`'s top word. -/
theorem Stg.balanced_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {ap aq : Nat}
    (cp : VG.Proof.Bignum.X86.CallArgument s g.B g.Z (pLenArg g.full) (BitVec.ofNat 32 ap))
    (cq : VG.Proof.Bignum.X86.CallArgument s g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 aq))
    (hap : ap ≤ 1024) (haq : aq ≤ 1024) (hn : aN ∈ live) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.balanced g.L 1 (pLenArg g.full) (qLenArg g.full) aN sG)) s
      fun t => Stg g s0 A live c t ∧ ∃ an, an ≤ 1024 ∧
        VG.Proof.Bignum.X86.CallArgument s g.B g.Z 1 (BitVec.ofNat 32 an) ∧
        VG.Proof.Rsa.X86.KeyRt.kw (g.L.toLen an) = g.w ∧
        (slot t.mem g.B sG = 0 ↔ Bal an ap aq (mw s.mem g.B g.w aN (g.w - 1))) := by
  obtain ⟨an, han, hkw, cn⟩ := h.ws.lenArg
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.balanced_ok h.ws cn cp cq han hap haq (h.live_lt aN hn) (by decide))
    fun t ⟨ht, k, e, r⟩ => ⟨?_, an, han, cn, hkw, e⟩
  refine h.next ht k (by simp) (by decide) r (by decide)
    (h.arrs_keep k (by simp) (by decide)) h.live_lt (h.vd_keep k (by simp) (by decide)) (h.mask_keep k (by decide))

/-- `ifBalanced sG word other`: `word` where `sG` is zero, else `other`. -/
theorem Stg.ifBalanced_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {P : Prop} (hg : slot s.mem g.B sG = 0 ↔ P) {W O : Prog isa} {Q : State → Prop}
    (hW : P → ∀ u, Stg g s0 A live c u → WP isa W u Q) (hO : ¬P → ∀ u, Stg g s0 A live c u → WP isa O u Q) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.ifBalanced sG W O) s Q := by
  unfold VG.Impl.Rsa.X86.WordModRt.ifBalanced
  refine WP.seq (wp_movS (readSrc_sc h.ws.ws.workspace (by have := h.ws.ws.hdr_le; unfold sG hdr at *; omega))
    fun u U _ => wp_cmpi fun t T _ z => WP.block_nil ?_)
  have ht : Stg g s0 A live c t :=
    (h.regs U.keeps U.mem (by decide)).regs (T.keeps []) T.mem (by decide)
  have ev : u.gpr .eax = s.mem.readW (off g.B sG) 32 := U.gpr
  have sl : slot s.mem g.B sG = (s.mem.readW (off g.B sG) 32).toNat := rfl
  refine WP.ite _ (by change t.zf = _; exact z) (fun hb => hW (hg.mp ?_) t ht) (fun hb => hO (fun p => ?_) t ht)
  · rw [ev, sub0_beq, decide_eq_true_iff] at hb
    rw [sl, hb]
  · rw [ev, sub0_beq, decide_eq_false_iff_not] at hb
    exact hb (by rw [← sl]; exact hg.mpr p)

/-- `wordMod x r m top`: `[r] = X mod [m]`, `X` the dividend's words from array `x` on (`w`, or
`W' + k` for `top = some k`), by word steps, `m` of `p`'s length `W'` words, when the top bit of its
`W'` words is set (and `m` is then left as it was). -/
theorem Stg.wordMod_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {x r m ap : Nat} {top : Option Nat}
    (hm : MLen s0 g.B g.Z (pLenArg g.full) ap) (h4 : 4 ≤ wq ap) (hw : wq ap ≤ g.w)
    (htop : ∀ k, top = some k → wq ap + k ≤ g.w)
    (hx : x < nArr) (hr : r < nArr) (hmL : m ∈ live)
    (hl : ∀ j ∈ live, j ≠ r ∧ j ≠ aT) (hrm : r ≠ m) (hrT : r ≠ aT) (hmT : m ≠ aT)
    (hxr : r ≠ x) (hxt : aT ≠ x) (hxm : m ≠ x)
    (hv : m ≠ aVD ∧ r ≠ aVD) :
    WP isa (wordMod g.full x r m top) s fun t => ∃ M R,
      (Top (wq ap) (A m) →
        M = A m ∧ R = val32 s.mem g.B (arr g.w x) (VG.Proof.Rsa.X86.WordRt.xw g.len ap top) % A m) ∧
      Stg g s0 (upd (upd A m M) r R) (r :: live) c t := by
  have hmN := h.live_lt m hmL
  have fm := h.ws.ws.fit64 hmN
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_ok h.ws ⟨h.arg hm.arg, hm.le⟩ hx hr hmN (by decide) hrT hmT hrm hxr hxt hxm
    h4 hw htop) fun t ⟨ht, k, wk, wtop, wr, K⟩ => ⟨num t.mem g.B g.w m, num t.mem g.B g.w r, ?_, ?_⟩
  · intro ⟨lo, hi⟩
    have gm := h.arrs.get hmL
    have hpos : 0 < wq ap := by omega
    -- `m`'s words from `W'` on are zero, its word `W' - 1` has its top bit set.
    have low : val32 s.mem g.B (arr g.w m) (wq ap) = A m := by
      rw [val32_low hw (by change num s.mem g.B g.w m < _; rw [gm]; exact hi)]; exact gm
    have topw : 2 ^ 31 ≤ mw s.mem g.B g.w m (wq ap - 1) := (top_iff hpos).mpr (by rw [low]; exact lo)
    have tlt : mw s.mem g.B g.w m (wq ap - 1) < 2 ^ 32 := (s.mem.readW _ 32).isLt
    have same : ∀ i, i < g.w + 2 → mw t.mem g.B g.w m i = mw s.mem g.B g.w m i := fun i hi' => by
      by_cases e : i = wq ap - 1
      · subst e
        have key : ∀ T : Nat, 2 ^ 31 ≤ T → T < 2 ^ 32 → T % 2 ^ 31 + 2 ^ 31 = T := fun T a b => by omega
        rw [wtop]; exact key _ topw tlt
      · exact wk i hi' e
    have numEq : ∀ n, n ≤ g.w → val32 t.mem g.B (arr g.w m) n = val32 s.mem g.B (arr g.w m) n :=
      fun n hn => val32_congr (k := n) fun i (hi' : i < n) => same i (by omega)
    refine ⟨(numEq g.w (Nat.le_refl _)).trans gm, ?_⟩
    rw [wr, numEq _ hw, low]
  · refine h.next ht k (by
        intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact hmN
        · exact hr
        · decide) (by decide) K wordRegs_body ?_ ?_
      (h.vd_keep k (by simp [hv.1, hv.2]; decide) (by decide)) (h.mask_keep k (by decide))
    · exact (h.arrs_write k rfl (fun j hj => by
        by_cases e : j = m
        · exact .inl e
        · exact .inr (by simp [e, (hl j hj).1, (hl j hj).2]))
        (by decide)).add rfl
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact hr
      · exact h.live_lt j hj'

end VG.Proof.Rsa.X86.KeyCheck
