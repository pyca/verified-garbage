module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvViews
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Compare
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Array arithmetic for prime recovery by Appendix C.2 (i686)

`RvOps`' operations on the two views of the recovery's working space, and
those Appendix C.2 adds: sums with their carry (`KS.add_w`, `KS.add_W`),
halving and the low word of narrow arrays, a wide array zeroed with its
extra word (`KS.zeroWide_W`), a narrow number widened into it (`KS.widen`),
a wide number's low half read narrow (`KS.view`), and the divisions
(`KS.div_w`, `KS.div_W`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.KeyRt (chain half setOne orOne addLow zeroWide div)
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A sum and its carry: `x + P c = a + b` with `x < P`. -/
theorem sum_carry {x a b P : Nat} {c : Bool} (hx : x < P) (e : x + P * c.toNat = a + b) :
    x = (a + b) % P ∧ c = decide (P ≤ a + b) := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e
  · refine ⟨by rw [← e, Nat.mod_eq_of_lt hx], by simp; omega⟩
  · refine ⟨?_, by simp; omega⟩
    rw [← e, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

theorem KS.add_w {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (chain nar .adc o a b false) s fun t =>
      KS g s0 (upd A o ((A a + A b) % 2 ^ (32 * g.w))) (o :: live) AW liveW V ls t ∧
      t.gpr .ecx = cmask (decide (2 ^ (32 * g.w) ≤ A a + A b)) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb) false)
    fun t ⟨_, k, ⟨c, ec, v⟩, r⟩ => ?_
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_false, Nat.add_zero] at v
  rw [kw_nar] at k v
  change num t.mem g.B g.w o + _ = num s.mem g.B g.w a + num s.mem g.B g.w b at v
  rw [h.arrs a ha, h.arrs b hb] at v
  obtain ⟨xv, cv⟩ := sum_carry (val32_lt _ _ _ _) v
  exact ⟨h.write_w k ho (by simp) (r.mono (by decide)) xv hlW (by simp), by rw [ec, cv]⟩

theorem KS.add_W {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ho : o < 22) (ha : a ∈ liveW) (hb : b ∈ liveW) (hl : ∀ j ∈ live, j / 2 ≠ o) :
    WP isa (chain wid .adc o a b false) s fun t =>
      KS g s0 A live (upd AW o ((AW a + AW b) % 2 ^ (32 * g.W))) (o :: liveW) V ls t ∧
      t.gpr .ecx = cmask (decide (2 ^ (32 * g.W) ≤ AW a + AW b)) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.chainAdd_ok h.rtW ho (h.liveW_lt a ha) (h.liveW_lt b hb) false)
    fun t ⟨_, k, ⟨c, ec, v⟩, r⟩ => ?_
  simp only [VG.Proof.Rsa.X86.KeyRt.kk, Bool.toNat_false, Nat.add_zero] at v
  rw [kw_wid] at k v
  change num t.mem g.B g.W o + _ = num s.mem g.B g.W a + num s.mem g.B g.W b at v
  rw [h.arrsW a ha, h.arrsW b hb] at v
  obtain ⟨xv, cv⟩ := sum_carry (val32_lt _ _ _ _) v
  exact ⟨h.write_W k ho (by simp) (r.mono (by decide)) xv hl (by simp), by rw [ec, cv]⟩

theorem KS.half_w {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (zero : (s.gpr .ebx).toNat = 0) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (half nar j) s fun t =>
      KS g s0 (upd A j (A j / 2)) (j :: live) AW liveW V ls t ∧ Keeps opRegs s t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.half_ok h.rt (h.live_lt j hj) (by omega)) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact ⟨h.write_w k (h.live_lt j hj) (by simp) (r.mono (by decide))
    (by rw [e, zero, Nat.mul_zero, Nat.add_zero, h.arrs j hj]) hlW (by simp), r.mono (by decide)⟩

theorem KS.setOne_W {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ liveW) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (.block (setOne wid j)) s fun t =>
      KS g s0 A live (upd AW j (1 + 2 ^ 32 * (AW j / 2 ^ 32))) (j :: liveW) V ls t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok h.rtW (h.liveW_lt j hj)) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  exact h.write_W k (h.liveW_lt j hj) (by simp) (r.mono (by decide)) (by rw [e, h.arrsW j hj]) hl (by simp)

theorem KS.orOne_w {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (.block (orOne nar j)) s fun t =>
      KS g s0 (upd A j (2 * (A j / 2) + 1)) (j :: live) AW liveW V ls t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.orOne_ok h.rt (h.live_lt j hj)) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact h.write_w k (h.live_lt j hj) (by simp) (r.mono (by decide)) (by rw [e, h.arrs j hj]) hlW (by simp)

theorem KS.addLow_w {j sl : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j ∈ live) (hsl : sl ∈ ls) (even : A j % 2 = 0) (bit : V sl ≤ 1)
    (hlW : ∀ i ∈ liveW, j / 2 ≠ i) :
    WP isa (.block (addLow nar j sl)) s fun t =>
      KS g s0 (upd A j (A j + V sl)) (j :: live) AW liveW V ls t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.addLow_ok h.rt (h.live_lt j hj) (h.ls_ok sl hsl).2.1)
    fun t ⟨_, k, e, r, _⟩ => ?_
  rw [kw_nar] at k e
  have ev : num s.mem g.B g.w j % 2 = 0 := by rw [h.arrs j hj]; exact even
  have bv : slot s.mem g.B sl ≤ 1 := by rw [h.sl sl hsl]; exact bit
  exact h.write_w k (h.live_lt j hj) (by simp) (r.mono (by decide))
    (by rw [e ev bv, h.arrs j hj, h.sl sl hsl]) hlW (by simp)

/-- A wide array zeroed with the word above it. -/
theorem KS.zeroWide_W {j : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hj : j < 22) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (zeroWide wid j) s fun t =>
      KS g s0 A live (upd AW j 0) (j :: liveW) V ls t ∧
      val32 t.mem g.B (arr g.W j) (g.W + 1) = 0 := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.zeroWide_ok h.rtW hj) fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_wid] at k e
  have z : num t.mem g.B g.W j = 0 := by
    have e' := e
    rw [val32_succ] at e'
    exact (Nat.eq_zero_of_add_eq_zero e').1
  exact ⟨h.write_W k hj (by simp) (r.mono (by decide)) z hl (by simp), e⟩

/-- The low half of a wide number: narrow array `2 j` holds it modulo `2^(32 w)`. -/
theorem num_low (m : Mem) (B : Addr) (w j : Nat) :
    num m B w (2 * j) = num m B (2 * w + 2) j % 2 ^ (32 * w) := by
  have e := numW m B w j
  rw [val32_append m B (arr w (2 * j)) w 2] at e
  have p : 2 ^ (32 * (w + 2)) = 2 ^ (32 * w) * 2 ^ 64 := by rw [Nat.mul_add, Nat.pow_add]
  rw [p] at e
  have lt := val32_lt m B (arr w (2 * j)) w
  rw [e, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]

/-- `copy_ok`, with exactly the bytes it writes. -/
theorem copyOut_ok {L : VG.Impl.Rsa.X86.KeyRt.Lay} {B : Addr} {Z len N : Nat} {s : State}
    (h : VG.Proof.Rsa.X86.KeyRt.RtWs L s B Z len N) {o a : Nat} (ho : o < N) (ha : a < N) (hoa : o ≠ a) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.copy L o a) s fun t => VG.Proof.Rsa.X86.KeyRt.RtWs L t B Z len N ∧
      Outside B (arr (VG.Proof.Rsa.X86.KeyRt.kw len) o) (4 * VG.Proof.Rsa.X86.KeyRt.kw len) s.mem t.mem ∧
      num t.mem B (VG.Proof.Rsa.X86.KeyRt.kw len) o = num s.mem B (VG.Proof.Rsa.X86.KeyRt.kw len) a ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.KeyRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have hu := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.selectIn_ok hu ho ha hoa false (k := true) U.gpr) fun t ⟨F, O, V, K⟩ => ?_
  rw [U.mem] at O V
  refine ⟨F, by simpa only [VG.Proof.Rsa.X86.KeyRt.kk_false] using O, ?_,
    (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩
  simp only [num, ite_true, VG.Proof.Rsa.X86.KeyRt.kk_false] at V ⊢; exact V

/-- Words inside a run of zero words are zero. -/
theorem val32_zero_mid {m : Mem} {B : Addr} {d a b c : Nat} (h : val32 m B d (a + b + c) = 0) :
    val32 m B (d + 4 * a) b = 0 := by
  rw [Nat.add_assoc, val32_append] at h
  have h2 := (Nat.eq_zero_of_add_eq_zero h).2
  rcases Nat.mul_eq_zero.mp h2 with z | z
  · exact absurd z (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · rw [val32_append] at z; exact (Nat.eq_zero_of_add_eq_zero z).1

/-- A wide array's number from its narrow halves. -/
theorem arr_W' (g : Geo) (k : Nat) : arr g.W k = arr g.w (2 * k) := arr_W g.w k

/-- A narrow number copied into the low half of a wide array zeroed with its extra word: the
wide array holds it, and the word above it is still zero. -/
theorem KS.widen {k a : Nat} (h : KS g s0 A live AW liveW V ls s) (hk : k < 22) (ha : a ∈ live)
    (hak : a ≠ 2 * k) (zero : val32 s.mem g.B (arr g.W k) (g.W + 1) = 0)
    (hl : ∀ i ∈ live, i / 2 ≠ k) (hlW : ∀ i ∈ liveW, i ≠ k) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.copy nar (2 * k) a) s fun t =>
      KS g s0 A live (upd AW k (A a)) (k :: liveW) V ls t ∧ w32 t.mem g.B (arr g.W k + 4 * g.W) = 0 := by
  have nw := h.ws.workspace.nowrap
  have fit := h.wsW.arr_fit hk
  simp only [S] at fit
  have aW : arr g.W k = arr g.w (2 * k) := arr_W' g k
  have eW : g.W = 2 * g.w + 2 := rfl
  have ew : width g.n = g.w := rfl
  have na : nArr = 44 := rfl
  have fit2 := h.ws.arr_fit (j := 2 * k) (by omega)
  simp only [S] at fit2
  refine WP.mono (copyOut_ok h.rt (o := 2 * k) (a := a) (by omega) (h.live_lt a ha) (Ne.symm hak))
    fun t ⟨_, O, e, r⟩ => ?_
  rw [kw_nar] at O e
  change Outside g.B (arr g.w (2 * k)) (4 * g.w) s.mem t.mem at O
  change num t.mem g.B g.w (2 * k) = num s.mem g.B g.w a at e
  have keep : Keep g.B g.w [2 * k] [] s.mem t.mem := Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega) (by simp)
  have zs : val32 s.mem g.B (arr g.w (2 * k) + 4 * g.w) 2 = 0 := by
    have z := zero
    rw [aW, eW, show 2 * g.w + 2 + 1 = g.w + 2 + (g.w + 1) by omega] at z
    exact val32_zero_mid z
  have zh : num s.mem g.B g.w (2 * k + 1) = 0 := by
    have z := zero
    rw [aW, eW, show 2 * g.w + 2 + 1 = g.w + 2 + g.w + 1 by omega] at z
    have := val32_zero_mid z
    unfold num
    rw [show arr g.w (2 * k + 1) = arr g.w (2 * k) + 4 * (g.w + 2) by rw [arr_succ]]
    exact this
  have zt : val32 t.mem g.B (arr g.w (2 * k) + 4 * g.w) 2 = 0 := by
    rw [O.val32 (.inr (Nat.le_refl _)) (by omega)]; exact zs
  have zh' : num t.mem g.B g.w (2 * k + 1) = 0 := by
    unfold num
    rw [O.val32 (.inr (by rw [arr_succ]; simp only [S]; omega)) (by rw [arr_succ]; simp only [S]; omega)]
    exact zh
  have value : num t.mem g.B g.W k = A a := by
    change num t.mem g.B (2 * g.w + 2) k = A a
    rw [numW, val32_append, zt, zh']
    change num t.mem g.B g.w (2 * k) + _ + _ = _
    rw [e, h.arrs a ha]
    simp
  have top : w32 t.mem g.B (arr g.W k + 4 * g.W) = 0 := by
    rw [O.w32 (.inr (by rw [aW, eW]; omega)) (by omega)]
    have z := zero
    rw [val32_succ] at z
    rcases Nat.mul_eq_zero.mp (Nat.eq_zero_of_add_eq_zero z).2 with c | c
    · exact absurd c (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · exact c
  refine ⟨h.core keep (fun j hj => by simp at hj; subst j; exact h.ws.arr_fit (by omega)) (by simp)
    (r.mono (by decide)) (h.arrs_w keep (fun j hj i hi => by simp at hi; subst i; have := hl j hj; omega) (by simp))
    h.live_lt ((h.arrsW_w keep (fun j hj i hi => by simp at hi; subst i; have := hlW j hj; omega) (by simp)).add value)
    (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hk) (h.liveW_lt j)) (h.sl_keep keep (by simp)) h.ls_ok, top⟩

/-- A wide number's low half, read narrow. -/
theorem KS.view {j : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ liveW) :
    KS g s0 (upd A (2 * j) (AW j % 2 ^ (32 * g.w))) (2 * j :: live) AW liveW V ls s :=
  { h with
    arrs := h.arrs.add (by rw [num_low, ← h.arrsW j hj]; rfl)
    live_lt := fun i hi => (List.mem_cons.mp hi).elim (fun e => by have := h.liveW_lt j hj; show i < 44; omega) (h.live_lt i) }

/-- Whether two narrow numbers are equal, into the header word `d`. -/
theorem KS.eq_w {d a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (ha : a ∈ live) (hb : b ∈ live) (hd : SlotOk d) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.eqSFast nar d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (if A a = A b then 1 else 0)) (d :: ls) t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.eqSFast_ok h.rt (h.live_lt a ha) (h.live_lt b hb) hd.2.1)
    fun t ⟨_, k, e, r⟩ => ?_
  rw [kw_nar] at k e
  exact h.slot1 k hd (r.mono (by decide)) (by rw [e, h.arrs a ha, h.arrs b hb])

theorem divSlots_ok : ∀ d ∈ [VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb], SlotOk d := by decide

/-- The division of narrow arrays: `[q] / [d]` into `[q]` and `[q] mod [d]` into `[r]`, for the
word above `[d]` zero and `[d]` positive; `[t]` is working space. -/
theorem KS.div_w {q r d t : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hq : q ∈ live) (hd : d ∈ live) (hr : r < nArr) (ht : t < nArr)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (top : w32 s.mem g.B (arr g.w d + 4 * g.w) = 0) (hl : ∀ j ∈ live, j ≠ t)
    (hlW : ∀ j ∈ liveW, q / 2 ≠ j ∧ r / 2 ≠ j ∧ t / 2 ≠ j)
    (hls : ∀ e ∈ ls, ∀ c ∈ [VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb], e + 4 ≤ c ∨ c + 4 ≤ e) :
    WP isa (div nar q r d t) s fun u => ∃ Q R,
      KS g s0 (upd (upd A q Q) r R) (r :: live) AW liveW V ls u ∧
      (0 < A d → Q = A q / A d ∧ R = A q % A d) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.div_ok h.rt (q := q) (r := r) (d := d) (t := t) (h.live_lt q hq) hr
    (h.live_lt d hd) ht hqr hqd hqt hrd hrt hdt (by rw [kw_nar]; exact top)) fun u ⟨_, k, rr, res⟩ => ?_
  rw [kw_nar] at k res
  refine ⟨num u.mem g.B g.w q, num u.mem g.B g.w r, ?_, fun pos => ?_⟩
  · refine h.core k (fun j hj => h.ws.arr_fit (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact h.live_lt _ hq
        · exact hr
        · exact ht)) divSlots_ok (rr.mono (by decide)) ?_
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hr) (h.live_lt j))
      (h.arrsW_w k (fun j hj i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        obtain ⟨a1, a2, a3⟩ := hlW j hj
        rcases hi with rfl | rfl | rfl <;> assumption) divSlots_ok) h.liveW_lt
      (h.sl_keep k hls) h.ls_ok
    intro j hj
    by_cases jr : j = r
    · subst jr; simp [upd]
    by_cases jq : j = q
    · subst jq; simp [upd, jr]
    have jl : j ∈ live := (List.mem_cons.mp hj).resolve_left jr
    simp only [upd, jr, jq, ↓reduceIte]
    rw [k.num (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact Ne.symm jq
        · exact Ne.symm jr
        · exact Ne.symm (hl j jl))
      (fun e he => (divSlots_ok e he).2.1) (h.ws.fit64 (h.live_lt j jl)), h.arrs j jl]
  · have p : 0 < num s.mem g.B g.w d := by rw [h.arrs d hd]; exact pos
    obtain ⟨e1, e2⟩ := res p
    rw [h.arrs q hq, h.arrs d hd] at e1 e2
    exact ⟨e1, e2⟩

/-- The division of wide arrays, as `KS.div_w`. -/
theorem KS.div_W {q r d t : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hq : q ∈ liveW) (hd : d ∈ liveW) (hr : r < 22) (ht : t < 22)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (top : w32 s.mem g.B (arr g.W d + 4 * g.W) = 0) (hlW : ∀ j ∈ liveW, j ≠ t)
    (hl : ∀ j ∈ live, j / 2 ≠ q ∧ j / 2 ≠ r ∧ j / 2 ≠ t)
    (hls : ∀ e ∈ ls, ∀ c ∈ [VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb], e + 4 ≤ c ∨ c + 4 ≤ e) :
    WP isa (div wid q r d t) s fun u => ∃ Q R,
      KS g s0 A live (upd (upd AW q Q) r R) (r :: liveW) V ls u ∧
      (0 < AW d → Q = AW q / AW d ∧ R = AW q % AW d) := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.div_ok h.rtW (q := q) (r := r) (d := d) (t := t) (h.liveW_lt q hq) hr
    (h.liveW_lt d hd) ht hqr hqd hqt hrd hrt hdt (by rw [kw_wid]; exact top)) fun u ⟨_, k, rr, res⟩ => ?_
  rw [kw_wid] at k res
  refine ⟨num u.mem g.B g.W q, num u.mem g.B g.W r, ?_, fun pos => ?_⟩
  · refine h.core k (fun j hj => h.wsW.arr_fit (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · exact h.liveW_lt _ hq
        · exact hr
        · exact ht)) divSlots_ok (rr.mono (by decide))
      (h.arrs_W k (fun j hj i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        obtain ⟨a1, a2, a3⟩ := hl j hj
        rcases hi with rfl | rfl | rfl <;> assumption) divSlots_ok) h.live_lt ?_
      (fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hr) (h.liveW_lt j))
      (h.sl_keep k hls) h.ls_ok
    intro j hj
    by_cases jr : j = r
    · subst jr; simp [upd]
    by_cases jq : j = q
    · subst jq; simp [upd, jr]
    have jl : j ∈ liveW := (List.mem_cons.mp hj).resolve_left jr
    simp only [upd, jr, jq, ↓reduceIte]
    rw [k.num (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · exact Ne.symm jq
        · exact Ne.symm jr
        · exact Ne.symm (hlW j jl))
      (fun e he => (divSlots_ok e he).2.1) (h.wsW.fit64 (h.liveW_lt j jl)), h.arrsW j jl]
  · have p : 0 < num s.mem g.B g.W d := by rw [h.arrsW d hd]; exact pos
    obtain ⟨e1, e2⟩ := res p
    rw [h.arrsW q hq, h.arrsW d hd] at e1 e2
    exact ⟨e1, e2⟩

end
end VG.Proof.Rsa.X86.Recover
