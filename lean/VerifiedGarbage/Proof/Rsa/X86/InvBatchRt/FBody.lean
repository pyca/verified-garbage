module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FFinish
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FInit
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatchStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Rsa.Divstep.Inv30
import VerifiedGarbage.Proof.Rsa.Divstep.Inv30Def
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Divstep.Libsecp
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: `BatchInstance` joins it with the gcd's proof (`GcdBatchRt.Body`), which builds in
-- parallel
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq

/-! # The fused batched inverse on i686

`stepF_ok`: batch `j` takes the state of the first `j` batches (`RunAt`) to that of `j + 1`;
`loopF_ok`: the loop of double batches, `(3 n + 2) / 2` of them; `body_ok`: `[1] = gcd p x` and
`[3]` the inverse of `x` modulo `p` where it exists, `w` words each, for the virtual modulus `p` of
`[8]` and `x` at `[0]`: the statement of the batches' inverse (`BatchLaw.inv_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Rsa.Divstep (oddInput)
open VG.Impl.Rsa.X86.Keys (seqs)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-! ## The batches in turn -/

theorem stepF_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) (he : nw len % 2 = 0) {i o : Nat}
    (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) {p iv x j : Nat} (odd : p % 2 = 1) (large : 1 < p)
    (hinv : (p * iv + 1) % 2 ^ 32 = 0) (pc : p < 2 ^ (32 * nw len)) (xc : x < 2 ^ (32 * nw len))
    (hj : j < 3 * (nw len + 1)) (F : RunAt len B p iv x j i s) :
    WP isa (batchCodeF L i o) s fun t =>
      Bx L t B Z len N ∧ Keeps wordClob s t ∧ Unch B (batchWrites len) s.mem t.mem ∧
      VG.Proof.Mont.w32 t.mem B 100 = VG.Proof.Mont.w32 s.mem B 100 ∧ RunAt len B p iv x (j + 1) o t := by
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega_using []
  have hinvI : ((p : Int) * iv + 1) % 2 ^ 30 = 0 := by
    have h32 : ((p : Int) * iv + 1) % 2 ^ 32 = 0 := by exact_mod_cast hinv
    omega_using [hinv]
  have b₀ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x) odd large hinv (by omega_using []) ox j
  have b₁ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x) odd large hinv (by omega_using []) ox (j + 1)
  have c₁ := (Divstep.deRunL_cong (x := oddInput p x) (np := iv) odd large hinvI (j + 1))
  obtain ⟨bd, fo, -, -, -⟩ := b₀
  obtain ⟨-, -, f1, g1, -⟩ := b₁
  obtain ⟨-, -, ⟨d1, d2⟩, ⟨e1, e2⟩⟩ := c₁
  have K : (2 : Int) ^ (32 * nw len) * 2 ^ 31 = 2 ^ (32 * nw len) * 2 ^ 31 := rfl
  have pcI : (p : Int) + x < 2 ^ (32 * nw len) * 2 := by
    rw [pow_succ] at *; push_cast; have : (2 : Int) ^ (32 * nw len) = ((2 ^ (32 * nw len) : Nat) : Int) := by push_cast; rfl
    rw [this]; omega_using [odd, large, hinv, pc, xc, ox, hinvI, f1, g1, d1, d2, e1, e2]
  have big : (2 : Int) ^ (32 * nw len) * 2 ≤ 2 ^ (32 * nw len) * 2 ^ 31 :=
    Int.mul_le_mul_of_nonneg_left (by decide) (Int.le_of_lt (two_pow_pos' _))
  have pI : (p : Int) < 2 ^ (32 * nw len) := by exact_mod_cast pc
  -- The batch's results are the next state's.
  obtain ⟨md, mf, mg⟩ := invRun_m 30 p 0 iv (oddInput p x) j
  have hn : rde p iv x (j + 1) =
      (dNext p iv (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g (rde p iv x j).1 (rde p iv x j).2,
        eNext p iv (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g (rde p iv x j).1 (rde p iv x j).2) := by
    simp only [rde, Divstep.deRunL, dNext, eNext, bT]
    push_cast at md mf mg ⊢
    rw [md, mf, mg]
  have hfn : (rs p iv x (j + 1)).f = fNext (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g := rfl
  have hgn : (rs p iv x (j + 1)).g = gNext (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g := rfl
  have hdn : (rs p iv x (j + 1)).d = (bT (rs p iv x j).d (rs p iv x j).f (rs p iv x j).g).d := by
    show (Divstep.W32.batch 30 p iv (rs p iv x j)).d = _
    rw [Divstep.W32.batch_d]; rfl
  have range : ∀ y : Int, |y| ≤ p + x → InRange (nw len) y := fun y hy => by
    rw [abs_le] at hy; push_cast at hy; exact ⟨by omega_using [pcI, hy], by omega_using [pcI, hy]⟩
  have rangeD : ∀ y : Int, -2 * (p : Int) < y → y < p → InRange (nw len) y := fun y h1 h2 => ⟨by omega_using [pcI, h1], by omega_using [pcI, h2]⟩
  have hd : |(rs p iv x j).d| + 64 < 2 ^ 30 := by
    have : (1 + 2 * (30 * j : Nat) : Int) ≤ 1 + 60 * (3 * 514) := by push_cast; omega
    show |(Divstep.W32.invRun 30 p iv (oddInput p x) j).d| + 64 < 2 ^ 30
    omega_using [bd, this]
  have hn1 := congrArg Prod.fst hn; have hn2' := congrArg Prod.snd hn
  simp only at hn1 hn2'
  refine WP.mono (batchGen_ok h hn2 he hio F hd fo (by rw [← hfn]; exact range _ f1) (by rw [← hgn]; exact range _ g1)
    (by rw [← hn1]; exact rangeD _ d1 d2) (by rw [← hn2']; exact rangeD _ e1 e2)) fun t ⟨Ht, Kt, Ut, Ct, Ft⟩ =>
    ⟨Ht, Kt, Ut, Ct, ?_⟩
  show FAt len B p iv _ _ _ _ _ o t
  rw [hdn, hfn, hgn, hn1, hn2']
  exact Ft

/-- The state survives the counter's store. -/
theorem FAt.keep100 {len : Nat} {B : Addr} {p iv : Nat} {dl f g d e : Int} {i : Nat} {s z : State}
    (F : FAt len B p iv dl f g d e i s) (hi : i ≤ 8) (O : Outside B 100 4 s.mem z.mem)
    (hfit : rv (kw len) { arr := deArr } + deSz * (nw len + 2) ≤ 2 ^ 32)
    (hfg : rv (kw len) { arr := fgArr } + fgSz * (nw len + 2) ≤ 2 ^ 32)
    (hA : 104 ≤ rv (kw len) { arr := fgArr }) (hD : 104 ≤ rv (kw len) { arr := deArr }) :
    FAt len B p iv dl f g d e i z := by
  have e16 : win = 16 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdr_out O (.inl (by omega_using [e16])) (by omega_using [e16])]; exact F.dl
  · rw [O.w32 (.inl (by omega_using [e16])) (by omega_using [e16])]; exact F.inverse
  · rw [(Same.below O (by unfold fgSz; omega_using [hi]) hA hfg).sval_eq]; exact F.f
  · rw [(Same.below O (by unfold fgSz; omega_using [hi]) hA hfg).sval_eq]; exact F.g
  · rw [(Same.below O (by unfold deSz; omega_using [hi]) hD hfit).sval_eq]; exact F.d
  · rw [(Same.below O (by unfold deSz; omega_using [hi]) hD hfit).sval_eq]; exact F.e
  · rw [(Same.below O (by unfold deSz; omega_using []) hD hfit).sv]; exact F.p

/-- The loop of double batches. -/
theorem loopF_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) (he : nw len % 2 = 0)
    {p iv x : Nat} (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * nw len)) (xc : x < 2 ^ (32 * nw len)) (F : RunAt len B p iv x 0 0 s)
    (cnt : VG.Proof.Mont.w32 s.mem B 100 = (3 * nw len + 2) / 2) :
    WP isa (.loop (seqs [batchF L true, batchF L false,
      .block [.mov .esi (.mem (sc 100)), VG.Impl.Weierstrass.X86.decCounter, .store (sc 100) .esi,
        VG.Impl.Weierstrass.X86.testCounter]]) .ne) s fun t =>
      Bx L t B Z len N ∧ Keeps wordClob s t ∧ Unch B (batchWrites len) s.mem t.mem ∧
      RunAt len B p iv x (3 * nw len + 2) 0 t := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have hAF : rv (kw len) { arr := fgArr } = 160 + 4 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, fgArr]; omega_using []
  have hAD : rv (kw len) { arr := deArr } = 160 + 11 * (4 * kw len + 8) := by
    simp only [rv, VG.Impl.Rsa.X86.InvBatchRt.offset, deArr]; omega_using []
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  generalize hK : (3 * nw len + 2) / 2 = K at cnt
  have hK2 : 2 * K = 3 * nw len + 2 := by omega_using [he, hK]
  refine WP.loop (M := isa) (fun rem u => ∃ k, k + rem = K ∧ 0 < rem ∧ Bx L u B Z len N ∧ Keeps wordClob s u ∧
    Unch B (batchWrites len) s.mem u.mem ∧ VG.Proof.Mont.w32 u.mem B 100 = K - k ∧ RunAt len B p iv x (2 * k) 0 u)
    ?_ K s ⟨0, by omega_using [], by omega_using [hK], h, Keeps.refl _ _, Unch.refl _ _ _, by rw [cnt]; omega_using [], by simpa using F⟩
  rintro rem u ⟨k, hk, hr, Hu, Ku, Uu, Cu, Fu⟩
  simp only [seqs, batchF_eq, ↓reduceIte, Bool.false_eq_true]
  refine WP.seq (WP.mono (stepF_ok Hu hn2 he (.inl ⟨rfl, rfl⟩) odd large hinv pc xc (by omega_using [hK, hk]) Fu)
    fun u₁ ⟨H₁, K₁, U₁, C₁, F₁⟩ => ?_)
  refine WP.seq (WP.mono (stepF_ok H₁ hn2 he (.inr ⟨rfl, rfl⟩) odd large hinv pc xc (by omega_using [hK, hk, hr]) F₁)
    fun u₂ ⟨H₂, K₂, U₂, C₂, F₂⟩ => ?_)
  refine WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok H₂.ws.ws.workspace (d := 100) (by omega_using [hf16])
    (j := K - k) (by omega_using [hk, hr]) (by omega_using [hn, hf16, hK]) (by rw [C₂, C₁, Cu])) fun z ⟨c, zf, K₃, O₃⟩ => ?_
  have Hz : Bx L z B Z len N := H₂.keepHigh K₃ (by decide) (by decide) O₃ (by decide) (by omega_using [hf16])
  have Fz := F₂.keep100 (by omega_using []) O₃ (by rw [hAD, eds]; omega_using [hw, ke]) (by rw [hAF, efs]; omega_using [hw, ke]) (by omega_using [hAF]) (by omega_using [hAD])
  have Kz : Keeps wordClob s z := ((Ku.trans K₁).trans K₂).trans (K₃.mono (by decide))
  have Uz : Unch B (batchWrites len) s.mem z.mem :=
    ((((Uu.trans U₁).trans U₂).trans O₃.unch).cover fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with ((h1 | h1) | h1) | h1
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · exact ⟨w, h1, le_refl _, le_refl _⟩
      · subst h1; exact ⟨(win, 88), by simp [batchWrites], by decide, by decide⟩)
  by_cases last : k + 1 = K
  · left
    refine ⟨?_, Hz, Kz, Uz, ?_⟩
    · change z.zf.map (!·) = some false
      rw [zf, show K - k - 1 = 0 by omega_using [last]]; rfl
    · rw [show 3 * nw len + 2 = 2 * k + 1 + 1 by omega_using [he, hK, last]]; exact Fz
  · right
    refine ⟨?_, rem - 1, by omega_using [hr], k + 1, by omega_using [hk, hr], by omega_using [hk, hr, last], Hz, Kz, Uz, by rw [c]; omega_using [], ?_⟩
    · change z.zf.map (!·) = some true
      rw [zf, decide_eq_false (show ¬ K - k - 1 = 0 by omega_using [hk, hr, last])]; rfl
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega_using []]; exact Fz

/-! ## The whole inverse -/

theorem body_ok {s : State} (h : RtWs L s B Z len N) (room : 16 ≤ N) (hn2 : 2 ≤ nw len)
    (he : nw len % 2 = 0) {m x : Nat}
    (hm : val32 s.mem B (rv (kw len) (a 8)) (nw len) = m) (hx : val32 s.mem B (rv (kw len) (a 0)) (nw len) = x)
    (odd : m % 2 = 1) :
    WP isa (body L) s fun z =>
      Bx L z B Z len N ∧
      val32 z.mem B (rv (kw len) (a 1)) (kw len) = Nat.gcd (virtualMod m) x ∧
      (virtualMod m : Int) ∣ (val32 z.mem B (rv (kw len) (a 3)) (kw len) : Int) * x - (Nat.gcd (virtualMod m) x : Int) ∧
      val32 z.mem B (rv (kw len) (a 3)) (kw len) < virtualMod m ∧
      Keeps wordClob s z ∧ Unch B (bodyWrites len) s.mem z.mem := by
  have hw := kw_bound h.lenLe
  have ke := kw_eq len
  set p := virtualMod m with hpdef
  have po : p % 2 = 1 := virtualMod_odd odd
  have pl : 1 < p := by simp only [p, virtualMod]; split <;> omega_arith
  have mp : m < 2 ^ (32 * nw len) := hm ▸ val32_lt _ _ _ _
  have pc : p < 2 ^ (32 * nw len) := by
    have four : 4 ≤ 2 ^ (32 * nw len) := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ 32 * nw len by omega_using [hn2])
    simp only [p, virtualMod]; split <;> omega_arith
  have xc : x < 2 ^ (32 * nw len) := hx ▸ val32_lt _ _ _ _
  unfold body
  simp only [seqs]
  refine WP.seq (WP.mono (initF_ok h room hn2 hm hx odd) fun s₁ ⟨iv, H₁, R₁, inv, C₁, P₁, K₁, U₁⟩ => ?_)
  refine WP.seq (WP.mono (loopF_ok H₁ hn2 he po pl inv pc xc R₁ C₁) fun s₂ ⟨H₂, K₂, U₂, R₂⟩ => ?_)
  rw [batchF_eq]
  simp only [↓reduceIte]
  refine WP.seq (WP.mono (stepF_ok H₂ hn2 he (.inl ⟨rfl, rfl⟩) po pl inv pc xc (j := 3 * nw len + 2) (by omega_using []) R₂)
    fun s₃ ⟨H₃, K₃, U₃, C₃, R₃⟩ => ?_)
  -- The reference run's results.
  have hf16 := H₃.fits16
  have hn := H₃.nowrap
  have r2 := rv_a len 2; have r4 := rv_a len 4; have r11 := rv_a len 11
  have apart : ∀ r ∈ batchWrites len, rv (kw len) (a 2) + 4 * (nw len + 1) ≤ r.1 ∨ r.1 + r.2 ≤ rv (kw len) (a 2) := by
    intro r hr
    simp only [batchWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [win] <;> omega_arith
  have P₃ : val32 s₃.mem B (rv (kw len) (a 2)) (nw len + 1) = p := by
    rw [unch_val32 U₃ apart (by omega_using [hf16, hn, r2]), unch_val32 U₂ apart (by omega_using [hf16, hn, r2]), P₁]
  have done := VG.Proof.Rsa.Divstep.invRun_done (inv := iv) po pc xc
  obtain ⟨-, fabs⟩ := done
  have fb : |(rs p iv x (3 * nw len + 2 + 1)).f| < 2 ^ (32 * nw len) := by
    have gl : Nat.gcd p x < 2 ^ (32 * nw len) := (Nat.gcd_le_left x (by omega_using [po])).trans_lt pc
    rw [show 3 * nw len + 2 + 1 = 3 * (nw len + 1) by omega_using [], ← Int.natCast_natAbs]
    show ((Divstep.W32.invRun 30 p iv (oddInput p x) (3 * (nw len + 1))).f.natAbs : Int) < _
    rw [fabs]; exact_mod_cast gl
  have hinvI : ((p : Int) * iv + 1) % 2 ^ 30 = 0 := by
    have h32 : ((p : Int) * iv + 1) % 2 ^ 32 = 0 := by exact_mod_cast inv
    omega_using [h32]
  have cg := Divstep.deRunL_cong (x := oddInput p x) (np := iv) po pl hinvI (3 * nw len + 2 + 1)
  obtain ⟨dc, -, ⟨d1, d2⟩, -⟩ := cg
  refine WP.mono (finishF_ok H₃ hn2 R₃.f R₃.d P₃ pc (by omega_using [po]) fb d1 d2) fun z ⟨Hz, A₁, A₃, Kz, Uz⟩ => ?_
  -- The inverse: `inv30`'s.
  have sp := VG.Proof.Rsa.Divstep.inv30_spec (n := nw len) (a := x) (m := p) po pl xc pc
  have e3 : ((if (rs p iv x (3 * nw len + 2 + 1)).f < 0 then -(rde p iv x (3 * nw len + 2 + 1)).1
      else (rde p iv x (3 * nw len + 2 + 1)).1) % (p : Int)).toNat = VG.Proof.Rsa.Divstep.inv30 (nw len) x p := by
    unfold VG.Proof.Rsa.Divstep.inv30
    rw [show 3 * nw len + 2 + 1 = 3 * (nw len + 1) by omega_using []] at dc ⊢
    have hf : (rs p iv x (3 * (nw len + 1))).f = (Divstep.W32.invRun 30 p 0 (oddInput p x) (3 * (nw len + 1))).f :=
      (invRun_m 30 p iv 0 (oddInput p x) _).2.1
    rw [hf]
    by_cases h0 : (Divstep.W32.invRun 30 p 0 (oddInput p x) (3 * (nw len + 1))).f < 0
    · simp only [h0, ↓reduceIte]
      have := dc.neg
      unfold Int.ModEq at this
      rw [this]
    · simp only [h0, ↓reduceIte]
      unfold Int.ModEq at dc
      rw [dc]
  refine ⟨Hz, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A₁, show 3 * nw len + 2 + 1 = 3 * (nw len + 1) by omega_using []]; exact fabs
  · rw [A₃, e3, Nat.gcd_comm]; exact sp.1
  · rw [A₃, e3]; exact sp.2
  · exact (((K₁.trans K₂).trans K₃).trans Kz)
  · refine (((U₁.trans U₂).trans U₃).trans Uz).cover fun w hw => ?_
    have r0 := rv_a len 0
    simp only [List.mem_append] at hw
    rcases hw with ((h1 | h1) | h1) | h1
    · exact ⟨w, h1, le_refl _, le_refl _⟩
    · simp only [batchWrites, List.mem_cons, List.not_mem_nil, or_false] at h1
      simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
      rcases h1 with rfl | rfl | rfl | rfl <;> simp only [win] <;> omega_arith
    · simp only [batchWrites, List.mem_cons, List.not_mem_nil, or_false] at h1
      simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
      rcases h1 with rfl | rfl | rfl | rfl <;> simp only [win] <;> omega_arith
    · exact ⟨w, h1, le_refl _, le_refl _⟩

end VG.Proof.Rsa.X86.InvBatchRt.F
