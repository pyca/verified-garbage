module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
public import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.Rd.TwosW
import VerifiedGarbage.Proof.Rsa.X86.Rd.DivQ
import VerifiedGarbage.Proof.Framework.Omega

/-! # `b - 1 = (n - r) / (m + 1)` on i686

`RecoverDetRt.divB`: `D = m + 1` and `N = n - r` (wide), shifted up by `D`'s leading zeros within
`W' = ⌈n_len / 4⌉` words by word and bit stages (`stageDWH`, `stageDBH`), then divided by words
(`wordDivQ`): the quotient `⌊N 2^s / D 2^s⌋ = ⌊N / D⌋` into `aD`, and whether the remainder
`(N mod D) 2^s` is zero into `sExact`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM sB
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Spec.Rsa (isqrt)
open VG.Proof.Rsa (b2n sub32)
open VG.Impl.Mont.X86 (sc at_)
open VG.Proof.Mont.X86.Rt (PtrAt readSrc_ptr ptr_add)
open VG.Proof.Rsa.X86.WordRt (MLen wq)

/-! ## The OR of `D`'s top words -/

/-- After words `0, …, j - 1` of the OR of `c` words from `a`. -/
structure Or1I (s : State) (B : Addr) (a c j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (a + 4 * j)
  dx : (u.gpr .edx).toNat = 4 * (c - j)
  keep : Keeps [.ecx, .edx, .esi] s u
  mem : u.mem = s.mem
  cx : u.gpr .ecx = 0 ↔ val32 s.mem B a j = 0

theorem or1Step_ok {B : Addr} {s u : State} {bytes a c j : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (ha : a + 4 * c ≤ bytes) (hj : j < c) (I : Or1I s B a c j u) :
    WP isa (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) u
      fun u' => u'.zf = some (decide (j + 1 = c)) ∧ Or1I s B a c (j + 1) u' := by
  have wsu := ws.of_wr I.keep.2.2
  refine wp_orS (readSrc_ptr wsu I.si (d := 0) (by omega)) fun u₁ U₁ => ?_
  refine wp_addS rfl fun u₂ U₂ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₃ U₃ z₃ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := c) (x := u.gpr .edx) I.dx hj
  have dx₂ : u₂.gpr .edx = u.gpr .edx := by rw [U₂.other _ (by decide), U₁.other _ (by decide)]
  have m₁ : u₁.mem = s.mem := by rw [U₁.mem, I.mem]
  refine ⟨by rw [z₃, dx₂, hc.2], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₃.other _ (by decide), U₂.gpr, ptr_add (s := u₁) (x := a + 4 * j)
      (by rw [PtrAt, U₁.other _ (by decide)]; exact I.si)]
    congr 2
  · rw [U₃.gpr, dx₂, hc.1]
  · exact I.keep.trans ((U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
      (U₃.keeps.mono (by decide))))
  · rw [U₃.mem, U₂.mem, m₁]
  · rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr, or_zero_iff, I.cx, val32_succ, I.mem,
      Nat.add_zero, ← toNat_eq_zero_iff (s.mem.readW (off B (a + 4 * j)) 32)]
    change (_ ∧ w32 s.mem B (a + 4 * j) = 0) ↔ _
    have p := Nat.two_pow_pos (32 * j)
    constructor
    · rintro ⟨x, z⟩; rw [x, z, Nat.mul_zero]
    · intro x
      have x₁ : 2 ^ (32 * j) * w32 s.mem B (a + 4 * j) = 0 := by omega
      exact ⟨by omega, (Nat.mul_eq_zero.mp x₁).resolve_left (by omega)⟩

/-- A number's word `W' - 1`, from its low `W'` words. -/
theorem val32_top {m : Mem} {B : Addr} {d W' K : Nat} (h : 1 ≤ W') :
    val32 m B d (W' + K) % 2 ^ (32 * W') / 2 ^ (32 * (W' - 1)) = w32 m B (d + 4 * (W' - 1)) := by
  rw [val32_mod, show W' = W' - 1 + 1 by omega, val32_succ, Nat.add_sub_cancel, Nat.add_comm,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (val32_lt _ _ _ _), Nat.add_zero]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `stageDWH`'s OR: `ecx` zero exactly where `D`'s words `W' - c, …, W' - 1` are. -/
theorem KS.orTopD {a c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z VG.Impl.Rsa.X86.RecoverDetRt.nl a) (hD : wDD ∈ liveW)
    (hC : sC4 ∈ ls) (hV : V sC4 = 4 * c) (hc0 : 0 < c) (hc : c ≤ wq a) (hw : wq a ≤ g.w) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.KeyRt.arrPtr wid .esi wDD .edx ++
        VG.Impl.Rsa.X86.WordModRt.width4 VG.Impl.Rsa.X86.RecoverDetRt.nl .edx ++
        ([.alu .add .esi (.reg .edx), .mov .edx (.mem (sc sC4)), .alu .sub .esi (.reg .edx), .mov .ecx (.imm 0)] :
          List Instr)))
      (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne))
      s fun t => KS g s0 A live AW liveW V ls t ∧
        (t.gpr .ecx = 0 ↔ AW wDD % 2 ^ (32 * wq a) / 2 ^ (32 * (wq a - c)) = 0) := by
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  have fa := h.wsW.arr_fit (j := wDD) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at fa
  refine WP.seq ?_
  rw [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hW) hW.lenLe hW.edi
    (r := .esi) (t := .edx) (j := wDD) (by decide) (by decide) (by rw [kw_wid]; change arr g.W wDD < 2 ^ 32; omega)
    fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .esi (arr g.W wDD) at p₁
  refine VG.Proof.Rsa.X86.WordRt.width4_ok (hm.keep U₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _))
    (r := .edx) fun u₂ U₂ m₂ e₂ => ?_
  have wb : g.w ≤ 258 := by
    have := h.upper; simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  have w4 : 4 * wq a < 2 ^ 32 := by omega
  refine wp_addS rfl fun u₃ U₃ _ => ?_
  have h₃ := h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    (U₃.keeps.mono (by decide)))) (fun x hx => hx) (by rw [U₃.mem, m₂, m₁])
  refine wp_movS (h₃.readSlot hC) fun u₄ U₄ _ => wp_subS rfl fun u₅ U₅ _ => wp_movS (v := 0) rfl fun u₆ U₆ _ =>
    WP.block_nil ?_
  have p₃ : PtrAt u₃ g.B .esi (arr g.W wDD + 4 * wq a) := by
    rw [PtrAt, U₃.gpr, BitVec.toNat_add, U₂.1 .esi (by decide), p₁, e₂, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt w4]
    have := g.B.isLt; omega
  have e₃ : (u₃.gpr .esi).toNat = g.B.toNat + arr g.W wDD + 4 * wq a := by
    rw [p₃, Nat.mod_eq_of_lt (by omega : g.B.toNat + (arr g.W wDD + 4 * wq a) < 2 ^ 32)]; omega
  have p₅ : PtrAt u₅ g.B .esi (arr g.W wDD + 4 * (wq a - c)) := by
    rw [PtrAt, U₅.gpr, BitVec.toNat_sub, U₄.other .esi (by decide), e₃, U₄.gpr, hV, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 4 * c < 2 ^ 32 by omega)]
    omega
  have m₆ : u₆.mem = s.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, m₂, m₁]
  have K₆ : Keeps [.ecx, .edx, .esi] s u₆ := ((U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans
      (U₆.keeps.mono (by decide)))))))
  have I₀ : Or1I s g.B (arr g.W wDD + 4 * (wq a - c)) c 0 u₆ := by
    refine ⟨?_, ?_, K₆, m₆, ?_⟩
    · rw [Nat.mul_zero, Nat.add_zero, PtrAt, U₆.other _ (by decide)]; exact p₅
    · rw [U₆.other _ (by decide), U₅.other _ (by decide), U₄.gpr, hV, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.sub_zero]
    · rw [U₆.gpr]; simp [val32]
  have ws := h.rt.rt
  refine WP.loop (M := isa) (fun n v => ∃ j, n = c - j ∧ j < c ∧ Or1I s g.B (arr g.W wDD + 4 * (wq a - c)) c j v)
    ?_ (c - 0) u₆ ⟨0, rfl, hc0, I₀⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (or1Step_ok ws (by omega) hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = c
  · refine .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true],
      h.of_rest (J'.keep.mono (by decide)) (fun x hx => hx) J'.mem, ?_⟩
    rw [J'.cx, e, ← h.arrsW wDD hD, val32_down]
    change val32 s.mem g.B (arr g.W wDD) (wq a - c + c) / _ = 0 ↔
      val32 s.mem g.B (arr g.W wDD) g.W % _ / _ = 0
    rw [show wq a - c + c = wq a by omega, show g.W = wq a + (g.W - wq a) by omega, val32_mod]
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], c - (j + 1),
      by omega, j + 1, rfl, by omega, J'⟩

end

/-! ## A stage of `D`'s leading zeros -/

/-- `divB`'s state during the stages: `[wDD] = v.1`, `[wNN] = v.2`, `n` (narrow and wide), one and
zero, the header word `d` (a loop's size) `vd`, and the flags `sLt`, `sOkDE`. -/
def DvS (g : Geo) (s0 : State) (ok lt n : Nat) (v : Nat × Nat) (d vd : Nat) (s : State) : Prop :=
  ∃ A AW V, KS g s0 A [aOne1, aZero, aN] AW [wDD, wNN, wN] V [d, sLt, sOkDE] s ∧ V d = vd ∧
    V sLt = lt ∧ V sOkDE = ok ∧ A aOne1 = 1 ∧ A aZero = 0 ∧ A aN = n ∧ AW wDD = v.1 ∧ AW wNN = v.2 ∧
    AW wN = n

/-- Whether a stage of `k` bits shifts: `D`'s low `W'` words, `x`, are below `2^(32 W' - k)`. -/
def dP (W' x k : Nat) : Prop := x % 2 ^ (32 * W') / 2 ^ (32 * W' - k) = 0

instance (W' x k : Nat) : Decidable (dP W' x k) := by unfold dP; infer_instance

/-- A stage of `k` bits: `D` and `N` shifted up, modulo `M`, where it shifts. -/
def dRes (M W' : Nat) (v : Nat × Nat) (k : Nat) : Nat × Nat :=
  if dP W' v.1 k then (v.1 * 2 ^ k % M, v.2 * 2 ^ k % M) else v

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `upBitsSelH j`: `[j] := [j] 2^b mod 2^(32 W)` (`b` in `sB`) where `sStg`. -/
theorem KS.upBitsSel_ok {j b : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ liveW) (hj22 : j < 22)
    (hjT : j ≠ wT) (hl : ∀ i ∈ live, i / 2 ≠ wT ∧ i / 2 ≠ j) (hB : sB ∈ ls) (hVB : V sB = b) (hS : sStg ∈ ls)
    (bit : V sStg ≤ 1) (hb : 0 < b) (hb32 : b < 2 ^ 32) :
    WP isa (upBitsSelH j) s fun t =>
      KS g s0 A live (upd (upd AW wT (AW j * 2 ^ b % 2 ^ (32 * g.W))) j
        (if V sStg = 0 then AW j else AW j * 2 ^ b % 2 ^ (32 * g.W))) (j :: wT :: liveW)
        (upd V sBc 0) (sBc :: ls) t := by
  have lt : AW j < 2 ^ (32 * g.W) := by rw [← h.arrsW j hj]; exact val32_lt _ _ _ _
  unfold upBitsSelH
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W (o := wT) (a := j) (by decide) hj (Ne.symm hjT) (fun i hi => (hl i hi).1))
    fun u ⟨hu, _⟩ => ?_)
  refine WP.seq (WP.mono (KS.timesH_ok (fun _ => A) (fun i => upd AW wT (AW j * 2 ^ i % 2 ^ (32 * g.W)))
    (by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt lt]; exact hu) hB hVB hb hb32
    fun i t _ P => ?_) fun u₂ h₂ => ?_)
  · refine WP.mono (P.add_W (o := wT) (a := wT) (b := wT) (by decide) (by simp) (by simp)
      (fun i hi => (hl i hi).1)) fun v ⟨hv, _⟩ => ?_
    refine hv.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    rw [upd_upd, upd_self, ← Nat.two_mul, Nat.mul_comm, Nat.mod_mul_mod, Nat.pow_succ, Nat.mul_assoc]
  · refine WP.mono (h₂.sel_W (o := j) (a := j) (b := wT) (sl := sStg) hj22 (by simp [hj]) (by simp)
      (by simp [hS]) (by rw [upd_ne _ _ (by decide)]; exact bit) (.inr hjT) (fun i hi => (hl i hi).2))
      fun t ⟨ht, _⟩ => ?_
    simp only [upd_self, upd_ne _ _ hjT, upd_ne _ _ (show sStg ≠ sBc by decide)] at ht
    exact ht.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

end

section
variable {g : Geo} {s0 s : State}

/-- A word stage of `D`'s leading zeros, of `32 c` bits, `c < W'`. -/
theorem stageDW_ok {ok lt n a c : Nat} {v : Nat × Nat} (h : DvS g s0 ok lt n v sC4 (4 * c) s)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hc0 : 0 < c) (hc : c < wq a) (hw : wq a ≤ g.w) :
    WP isa stageDWH s (DvS g s0 ok lt n (dRes (2 ^ (32 * g.W)) (wq a) v (32 * c)) sC4 (4 * c)) := by
  obtain ⟨A, AW, V, h, hd, hlt, hok, h1, hz, hn, hD, hN, hNW⟩ := h
  have cW : c < g.W := by simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide]; simp only [Geo.w] at hw; omega
  unfold stageDWH
  simp only [seqs]
  refine WP.seq (WP.mono (h.orTopD (h.mlen ha ha1) (by simp) (by simp) hd hc0 (Nat.le_of_lt hc) hw)
    fun t₁ ⟨h₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono h₁.flagZero fun t₂ ⟨h₂, _⟩ => ?_)
  have fl : (if t₁.gpr .ecx = 0 then 1 else 0) = (if dP (wq a) v.1 (32 * c) then 1 else 0) :=
    flag_eq (by rw [e₁, hD]; unfold dP; rw [show 32 * wq a - 32 * c = 32 * (wq a - c) by omega])
  rw [fl] at h₂
  have hV₂ : upd V sStg (if dP (wq a) v.1 (32 * c) then 1 else 0) sC4 = 4 * c := by
    rw [upd_ne _ _ (by decide)]; exact hd
  refine WP.seq (WP.mono (h₂.moveUp_W (o := wT) (a := wDD) (c := c) (by decide) (by simp) (by decide) cW
    (by simp) hV₂ (by decide)) fun t₃ ⟨h₃, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h₃.sel_W (o := wDD) (a := wDD) (b := wT) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_)
  refine WP.seq (WP.mono (h₄.moveUp_W (o := wT) (a := wNN) (c := c) (by decide) (by simp) (by decide) cW
    (by simp) hV₂ (by decide)) fun t₅ ⟨h₅, _, _⟩ => ?_)
  refine WP.mono (h₅.sel_W (o := wNN) (a := wNN) (b := wT) (sl := sStg) (by decide) (by simp)
    (by simp) (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun t ⟨h₆, _⟩ => ?_
  refine ⟨A, _, _, h₆.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), hV₂, by rw [upd_ne _ _ (by decide), hlt],
    by rw [upd_ne _ _ (by decide), hok], h1, hz, hn, ?_⟩
  simp only [upd_self, upd_ne _ _ (show wDD ≠ wNN by decide), upd_ne _ _ (show wDD ≠ wT by decide),
    upd_ne _ _ (show wNN ≠ wT by decide), upd_ne _ _ (show wN ≠ wNN by decide),
    upd_ne _ _ (show wN ≠ wDD by decide), upd_ne _ _ (show wN ≠ wT by decide),
    upd_ne _ _ (show wNN ≠ wDD by decide), sel_eq, hD, hN, hNW]
  unfold dRes
  split <;> simp

/-- A bit stage of `D`'s leading zeros, of `b` bits, `0 < b < 32`. -/
theorem stageDB_ok {ok lt n a b : Nat} {v : Nat × Nat} (h : DvS g s0 ok lt n v sB b s)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hb : 0 < b) (hb32 : b < 32) (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w) :
    WP isa stageDBH s (DvS g s0 ok lt n (dRes (2 ^ (32 * g.W)) (wq a) v b) sB b) := by
  obtain ⟨A, AW, V, h, hd, hlt, hok, h1, hz, hn, hD, hN, hNW⟩ := h
  have hW := h.rtW
  have nw := hW.ws.workspace.nowrap
  have fa := h.wsW.arr_fit (j := wDD) (by decide)
  have wW : g.W = 2 * g.w + 2 := rfl
  simp only [S] at fa
  unfold stageDBH
  simp only [seqs]
  refine WP.seq (VG.Proof.Rsa.X86.WordRt.topPtr_ok hW (h.mlen ha ha1) (j := wDD) (i := 1) (r := .esi) (t := .edx)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw1 (by rw [kw_wid]; change wq a ≤ g.W + 2; omega)
    fun u₁ U₁ m₁ p₁ _ => ?_)
  rw [kw_wid] at p₁
  change PtrAt u₁ g.B .esi (arr g.W wDD + 4 * wq a - 4 * 1) at p₁
  refine wp_movS (readSrc_ptr (h.rt.rt.of_wr U₁.2.2) p₁ (d := 0) (by omega)) fun u₂ U₂ _ => WP.block_nil ?_
  have h₂ := h.of_rest (rs := opRegs) ((U₁.mono (by decide)).trans (U₂.keeps.mono (by decide)))
    (fun x hx => hx) (by rw [U₂.mem, m₁])
  have eax : (u₂.gpr .eax).toNat = AW wDD % 2 ^ (32 * wq a) / 2 ^ (32 * (wq a - 1)) := by
    rw [U₂.gpr, m₁, Nat.add_zero, show arr g.W wDD + 4 * wq a - 4 * 1 = arr g.W wDD + 4 * (wq a - 1) by omega]
    change w32 s.mem g.B (arr g.W wDD + 4 * (wq a - 1)) = _
    have e := val32_top (m := s.mem) (B := g.B) (d := arr g.W wDD) (K := g.W - wq a) hw1
    rw [show wq a + (g.W - wq a) = g.W by omega] at e
    rw [← h.arrsW wDD (by simp)]
    exact e.symm
  refine WP.seq (WP.mono (topTest_ok h₂.ws (b := b) (by rw [h₂.sl _ (by simp), hd]) hb hb32)
    fun t₃ ⟨K₃, m₃, e₃⟩ => ?_)
  have h₃ := h₂.of_rest K₃ (by decide) m₃
  refine WP.seq (WP.mono h₃.flagZero fun t₄ ⟨h₄, _⟩ => ?_)
  have fl : (if t₃.gpr .ecx = 0 then 1 else 0) = (if dP (wq a) v.1 b then 1 else 0) := by
    refine flag_eq ?_
    rw [← toNat_eq_zero_iff, e₃, eax, hD, Nat.mul_eq_zero]
    unfold dP
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * (wq a - 1) + (32 - b) = 32 * wq a - b by omega]
    have := Nat.two_pow_pos (32 - b)
    omega
  rw [fl] at h₄
  have hV₄ : upd V sStg (if dP (wq a) v.1 b then 1 else 0) sB = b := by rw [upd_ne _ _ (by decide)]; exact hd
  have bit : upd V sStg (if dP (wq a) v.1 b then 1 else 0) sStg ≤ 1 := by rw [upd_self]; split <;> decide
  refine WP.seq (WP.mono (h₄.upBitsSel_ok (j := wDD) (b := b) (by simp) (by decide) (by decide) (by decide)
    (by simp) hV₄ (by simp) bit hb (by omega)) fun t₅ h₅ => ?_)
  refine WP.mono (h₅.upBitsSel_ok (j := wNN) (b := b) (by simp) (by decide) (by decide) (by decide)
    (by simp) (by rw [upd_ne _ _ (by decide)]; exact hV₄) (by simp) (by rw [upd_ne _ _ (by decide)]; exact bit)
    hb (by omega)) fun t h₆ => ?_
  refine ⟨A, _, _, h₆.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), ?_, ?_, ?_, h1, hz, hn, ?_⟩
  · simp only [upd_ne _ _ (show sB ≠ sBc by decide)]; exact hV₄
  · simp only [upd_ne _ _ (show sLt ≠ sBc by decide), upd_ne _ _ (show sLt ≠ sStg by decide)]; exact hlt
  · simp only [upd_ne _ _ (show sOkDE ≠ sBc by decide), upd_ne _ _ (show sOkDE ≠ sStg by decide)]; exact hok
  simp only [upd_self, upd_ne _ _ (show wDD ≠ wNN by decide), upd_ne _ _ (show wDD ≠ wT by decide),
    upd_ne _ _ (show wNN ≠ wT by decide), upd_ne _ _ (show wN ≠ wNN by decide),
    upd_ne _ _ (show wN ≠ wDD by decide), upd_ne _ _ (show wN ≠ wT by decide),
    upd_ne _ _ (show wNN ≠ wDD by decide), upd_ne _ _ (show sStg ≠ sBc by decide), sel_eq, hD, hN, hNW]
  unfold dRes
  split <;> simp

end

/-! ## The stages' loops -/

section
variable {g : Geo} {s0 t u : State} {ok lt n vd d : Nat} {v : Nat × Nat}

theorem DvS.ks (h : DvS g s0 ok lt n v d vd t) :
    ∃ A AW V, KS g s0 A [aOne1, aZero, aN] AW [wDD, wNN, wN] V [d, sLt, sOkDE] t := by
  obtain ⟨A, AW, V, h, _⟩ := h
  exact ⟨A, AW, V, h⟩

theorem DvS.of_rest (h : DvS g s0 ok lt n v d vd t) (r : Keeps opRegs t u) (m : u.mem = t.mem) :
    DvS g s0 ok lt n v d vd u := by
  obtain ⟨A, AW, V, h, rest⟩ := h
  exact ⟨A, AW, V, h.of_rest r (fun x hx => hx) m, rest⟩

theorem DvS.ws (h : DvS g s0 ok lt n v d vd t) : Ws t g.B g.Z g.w VG.Impl.Rsa.X86.Recover.nArr := by
  obtain ⟨A, AW, V, h, _⟩ := h
  exact h.ws

theorem DvS.slotEq (h : DvS g s0 ok lt n v d vd t) : slot t.mem g.B d = vd := by
  obtain ⟨A, AW, V, h, hd, _⟩ := h
  rw [h.sl _ (by simp), hd]

/-- A header word written: it becomes the state's loop size. -/
theorem DvS.reslot {d' x w' : Nat} (h : DvS g s0 ok lt n v d vd t) (k : Keep g.B w' [] [d'] t.mem u.mem)
    (hd' : SlotOk d') (hne : d' ≠ sOkDE) (hne' : d' ≠ sLt) (e : slot u.mem g.B d' = x) (r : Keeps opRegs t u) :
    DvS g s0 ok lt n v d' x u := by
  obtain ⟨A, AW, V, h, _, hlt, hok, rest⟩ := h
  refine ⟨A, AW, upd V d' x, (h.slot1 k hd' r e).mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun e he => ⟨?_, rfl⟩), upd_self .., by rw [upd_ne _ _ (Ne.symm hne'), hlt],
    by rw [upd_ne _ _ (Ne.symm hne), hok], rest⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
  rcases he with rfl | rfl | rfl <;> simp

/-- The loop's size forgotten. -/
theorem DvS.forget (h : DvS g s0 ok lt n v d vd t) : DvS g s0 ok lt n v sOkDE ok t := by
  obtain ⟨A, AW, V, h, _, hlt, hok, rest⟩ := h
  exact ⟨A, AW, V, h.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun e he => ⟨by simp at he ⊢; omega, rfl⟩), hok, hlt, hok, rest⟩

/-- `D`'s stages, `2^12, …, 1` bits (word stages where `c < W'`), each taken where `x + k ≤ T`;
where `good`, the values follow `vals`. -/
theorem dPhase_ok {a T : Nat} {good : Prop} (vals : Nat → Nat × Nat)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha1 : a ≤ 1024)
    (hw1 : 1 ≤ wq a) (hw : wq a ≤ g.w)
    (hval : good → ∀ x k, x ≤ T → 0 < k → k < 32 * wq a →
      dRes (2 ^ (32 * g.W)) (wq a) (vals x) k = vals (if x + k ≤ T then x + k else x))
    (hT : T < 2 ^ 13) (hTw : T < 32 * wq a)
    (h : DvS g s0 ok lt n v sOkDE ok t) (hv : good → v = vals 0) :
    WP isa (seqs [wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 VG.Impl.Rsa.X86.RecoverDetRt.nl .eax) stageDWH,
      bitStagesL 16 1 stageDBH]) t fun u => ∃ v', DvS g s0 ok lt n v' sOkDE ok u ∧ (good → v' = vals T) := by
  have w4 : 4 * wq a < 2 ^ 32 := by simp only [wq]; omega
  have e : seqs [wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 VG.Impl.Rsa.X86.RecoverDetRt.nl .eax) stageDWH,
      bitStagesL 16 1 stageDBH] =
    .seq (wordStagesL (2 ^ 7) (VG.Impl.Rsa.X86.WordModRt.width4 VG.Impl.Rsa.X86.RecoverDetRt.nl .eax) stageDWH)
      (bitStagesL (2 ^ 4) (2 ^ 0) stageDBH) := rfl
  rw [e]
  refine WP.seq (WP.mono (wordStagesL_ok (k := 7) (lim := 4 * wq a)
    (Fin := fun t => ∃ x v, x ≤ T ∧ T - x < 32 ∧ DvS g s0 ok lt n v sOkDE ok t ∧ (good → v = vals x))
    (fun j t => ∃ x v, x ≤ T ∧ T - x < 64 * 2 ^ j ∧ DvS g s0 ok lt n v sC4 (4 * 2 ^ j) t ∧ (good → v = vals x))
    (fun j t => ∃ x v, x ≤ T ∧ T - x < 32 * 2 ^ j ∧ DvS g s0 ok lt n v sC4 (4 * 2 ^ j) t ∧ (good → v = vals x))
    (by decide) h.ws ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun t₁ F => ?_)
  · intro u k e r
    exact ⟨0, v, Nat.zero_le _, by rw [show (2 : Nat) ^ 13 = 8192 from rfl] at hT; simp; omega, h.reslot k (by decide) (by decide) (by decide) e (r.mono (by decide)), hv⟩
  · rintro j u _ ⟨x, v, _, _, P, _⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u _ ⟨x, v, _, _, P, _⟩ is Q k
    obtain ⟨A, AW, V, hK⟩ := P.ks
    exact VG.Proof.Rsa.X86.WordRt.width4_ok (hK.mlen ha ha1) (r := .eax)
      fun u' K m e => k u' (K.mono (by decide)) m (by rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt w4])
  · rintro j u u' _ ⟨x, v, h1, h2, P, hg⟩ r m
    exact ⟨x, v, h1, h2, P.of_rest r m, hg⟩
  · rintro j u _ ⟨x, v, h1, h2, P, hg⟩ lt'
    refine WP.mono (stageDW_ok P ha ha1 (Nat.two_pow_pos j) (by omega) hw) fun u' P' => ?_
    refine ⟨if x + 32 * 2 ^ j ≤ T then x + 32 * 2 ^ j else x, _, by split <;> omega, by split <;> omega, P',
      fun gd => ?_⟩
    rw [hg gd, hval gd x _ h1 (by have := Nat.two_pow_pos j; omega) (by omega)]
  · rintro j u _ ⟨x, v, h1, h2, P, hg⟩ le
    exact ⟨x, v, h1, by omega, P, hg⟩
  · rintro j u _ ⟨x, v, _, _, P, _⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u u' _ ⟨x, v, h1, h2, P, hg⟩ k e r
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have p := pow_pred hj
      exact ⟨x, v, h1, by omega, P.reslot k (by decide) (by decide) (by decide) (by rw [e]; omega) r, hg⟩
    · subst hj
      exact ⟨x, v, h1, by simpa using h2, (P.reslot k (by decide) (by decide) (by decide) e r).forget, hg⟩
  obtain ⟨x₁, v₁, hx₁, hlt₁, P₁, hg₁⟩ := F
  refine bitStagesL_ok (k := 4) (m := 0)
    (Fin := fun u => ∃ v', DvS g s0 ok lt n v' sOkDE ok u ∧ (good → v' = vals T))
    (fun j t => ∃ x v, x ≤ T ∧ T - x < 2 * 2 ^ j ∧ DvS g s0 ok lt n v sB (2 ^ j) t ∧ (good → v = vals x))
    (fun j t => ∃ x v, x ≤ T ∧ T - x < 2 ^ j ∧ DvS g s0 ok lt n v sB (2 ^ j) t ∧ (good → v = vals x))
    (by decide) (by decide) P₁.ws ?_ ?_ ?_ ?_
  · intro u k e r
    exact ⟨x₁, v₁, hx₁, by simpa using hlt₁, P₁.reslot k (by decide) (by decide) (by decide) e (r.mono (by decide)),
      hg₁⟩
  · rintro j u _ hj ⟨x, v, h1, h2, P, hg⟩
    have p16 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hj
    have p16' : 2 ^ j ≤ 16 := by simpa using p16
    refine WP.mono (stageDB_ok P ha ha1 (Nat.two_pow_pos j) (by omega) hw1 hw) fun u' P' => ?_
    refine ⟨if x + 2 ^ j ≤ T then x + 2 ^ j else x, _, by split <;> omega, by split <;> omega, P',
      fun gd => ?_⟩
    rw [hg gd, hval gd x _ h1 (Nat.two_pow_pos j) (by omega)]
  · rintro j u _ _ ⟨x, v, _, _, P, _⟩
    exact ⟨P.ws, P.slotEq⟩
  · rintro j u u' _ _ ⟨x, v, h1, h2, P, hg⟩ k e r
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have p := pow_pred hj
      exact ⟨x, v, h1, by omega, P.reslot k (by decide) (by decide) (by decide) (by rw [e]; omega) r, hg⟩
    · subst hj
      have : x = T := by simp at h2; omega
      subst this
      exact ⟨v, (P.reslot k (by decide) (by decide) (by decide) e r).forget, hg⟩

end

/-! ## `divB` -/

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat}

/-- `divB`'s start: one, `n - r` (narrow, then wide in `wNN`) and `m + 1` (narrow, then wide in
`wDD`), from the low halves of `m` and `r`. -/
theorem divB_pre {n m r : Nat} (h : KS g s0 A [aZero, aN] AW [wA, wR, wN] V [sLt, sOkDE] s)
    (hz : A aZero = 0) (hn : A aN = n) (hm : AW wA = m) (hr : AW wR = r) (hnW : AW wN = n) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.copy nar aOne1 aZero, .block (VG.Impl.Rsa.X86.KeyRt.setOne nar aOne1),
      VG.Impl.Rsa.X86.KeyRt.sub3 nar aD aN aRlo, VG.Impl.Rsa.X86.KeyRt.chain nar .adc aM1 aM aOne1 false,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wDD, VG.Impl.Rsa.X86.KeyRt.copy nar (2 * wDD) aM1,
      VG.Impl.Rsa.X86.KeyRt.zeroWide wid wNN, VG.Impl.Rsa.X86.KeyRt.copy nar (2 * wNN) aD]) s
      (DvS g s0 (V sOkDE) (V sLt) n ((m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w),
        sub32 g.w n (r % 2 ^ (32 * g.w))) sOkDE (V sOkDE)) := by
  have h₀ := (h.view (j := wA) (by simp)).view (j := wR) (by simp)
  simp only [seqs]
  refine WP.seq (WP.mono (h₀.copy_w (o := aOne1) (a := aZero) (by decide) (by simp) (by decide) (by decide))
    fun u₁ ⟨h₁, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h₁.setOne_w (j := aOne1) (by simp) (by decide)) fun u₂ ⟨h₂, _⟩ => ?_)
  refine WP.seq (WP.mono (h₂.subWrap (o := aD) (a := aN) (b := aRlo) (by decide) (by simp) (by decide)
    (by decide) (by decide) (by decide)) fun u₃ ⟨h₃, _⟩ => ?_)
  refine WP.seq (WP.mono (h₃.add_w (o := aM1) (a := aM) (b := aOne1) (by decide) (by decide) (by simp)
    (by decide)) fun u₄ ⟨h₄, _⟩ => ?_)
  refine WP.seq (WP.mono (h₄.zeroWide_W (j := wDD) (by decide) (by decide)) fun u₅ ⟨h₅, z₅⟩ => ?_)
  have h₅' := h₅.mono (liveW' := [wA, wR, wN]) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.seq (WP.mono (h₅'.widen (k := wDD) (a := aM1) (by decide) (by simp) (by decide) z₅ (by decide)
    (by decide)) fun u₆ ⟨h₆, _⟩ => ?_)
  refine WP.seq (WP.mono (h₆.zeroWide_W (j := wNN) (by decide) (by decide)) fun u₇ ⟨h₇, z₇⟩ => ?_)
  have h₇' := h₇.mono (liveW' := [wDD, wA, wR, wN]) (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  refine WP.mono (h₇'.widen (k := wNN) (a := aD) (by decide) (by simp) (by decide) z₇ (by decide)
    (by decide)) fun t ⟨h₈, _⟩ => ?_
  refine ⟨_, _, _, h₈.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, rfl⟩), rfl, rfl, rfl, ?_⟩
  have hz' : A 10 = 0 := hz
  have hn' : A 32 = n := hn
  have hm' : AW 17 = m := hm
  have hr' : AW 20 = r := hr
  have hnW' : AW 19 = n := hnW
  simp [upd, aOne1, aD, aM1, aM, aRlo, aZero, aN, wDD, wNN, wN, wA, wR, hz', hn', hm', hr', hnW']

end

/-! ## The arithmetic of the normalization -/

/-- A stage of `D`'s leading zeros on `D 2^x`, `N 2^x`, for `T` the leading zeros of `D` within
`W'` words. -/
theorem dRes_vals {D N W' W x k T : Nat} (hD0 : 0 < D) (hD : D < 2 ^ (32 * W')) (hW : W' ≤ W)
    (hT : T = 32 * W' - 1 - Nat.log2 D) (hx : x ≤ T) (hk : k < 32 * W') :
    dRes (2 ^ (32 * W)) W' (D * 2 ^ x % 2 ^ (32 * W), N * 2 ^ x % 2 ^ (32 * W)) k =
      (D * 2 ^ (if x + k ≤ T then x + k else x) % 2 ^ (32 * W),
        N * 2 ^ (if x + k ≤ T then x + k else x) % 2 ^ (32 * W)) := by
  have D0 : D ≠ 0 := by omega
  have l : Nat.log2 D < 32 * W' := (Nat.log2_lt D0).mpr hD
  have hDx : D * 2 ^ x < 2 ^ (32 * W') := (VG.Proof.Bignum.ShiftStages.lt_pow_iff D0 x _).mpr (by omega)
  have pW : 2 ^ (32 * W') ≤ 2 ^ (32 * W) := Nat.pow_le_pow_right (by decide) (by omega)
  have e1 : D * 2 ^ x % 2 ^ (32 * W) = D * 2 ^ x := Nat.mod_eq_of_lt (by omega)
  have iff : dP W' (D * 2 ^ x % 2 ^ (32 * W)) k ↔ x + k ≤ T := by
    unfold dP
    rw [e1, Nat.mod_eq_of_lt hDx, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _),
      VG.Proof.Bignum.ShiftStages.lt_pow_iff D0]
    omega
  unfold dRes
  by_cases hxk : x + k ≤ T
  · simp only [iff.mpr hxk, hxk, ↓reduceIte, VG.Proof.Bignum.ShiftStages.mul_pow_add_mod]
  · simp only [iff, hxk, ↓reduceIte]

/-- `D` and `N` shifted by `D`'s leading zeros `T` within `W'` words: `D 2^T` has its top bit set,
and neither wraps. -/
theorem norm_vals {D N W' W T : Nat} (hD0 : 0 < D) (hD : D < 2 ^ (32 * W')) (hN : N < 2 ^ (32 * W'))
    (hT : T = 32 * W' - 1 - Nat.log2 D) (h2 : 2 * W' ≤ W) :
    2 ^ (32 * W' - 1) ≤ D * 2 ^ T ∧ D * 2 ^ T < 2 ^ (32 * W') ∧ N * 2 ^ T < 2 ^ (32 * W) := by
  have D0 : D ≠ 0 := by omega
  have l : Nat.log2 D < 32 * W' := (Nat.log2_lt D0).mpr hD
  refine ⟨?_, (VG.Proof.Bignum.ShiftStages.lt_pow_iff D0 T _).mpr (by omega), ?_⟩
  · calc 2 ^ (32 * W' - 1) = 2 ^ Nat.log2 D * 2 ^ T := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ D * 2 ^ T := Nat.mul_le_mul_right _ (Nat.log2_self_le D0)
  · calc N * 2 ^ T < 2 ^ (32 * W') * 2 ^ T := Nat.mul_lt_mul_of_pos_right hN (Nat.two_pow_pos _)
      _ = 2 ^ (32 * W' + T) := by rw [Nat.pow_add]
      _ ≤ 2 ^ (32 * W) := Nat.pow_le_pow_right (by decide) (by omega)


section
open VG.Proof.Rsa.X86.WordRt (mw)

/-- `divB`: `Q = (n - r) / (m + 1)` into `aD` and whether `R = (n - r) mod (m + 1)` is zero into
`sExact`, where `m < n` and `r < n`; `D = m + 1` and `N = n - r` shifted by `D`'s leading zeros in
`W'` words, then divided by words. -/
theorem divB_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {n m r a : Nat}
    (h : KS g s0 A [aZero, aN] AW [wA, wR, wN] V [sLt, sOkDE] s)
    (hz : A aZero = 0) (hn : A aN = n) (hm : AW wA = m) (hr : AW wR = r) (hnW : AW wN = n)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (ha0 : 64 ≤ a) (ha1 : a ≤ 1024)
    (haw : VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w) (hn' : n < 2 ^ (32 * VG.Proof.Rsa.X86.WordRt.wq a)) :
    WP isa divB s fun t => ∃ Q R A' AW' V',
      KS g s0 A' [aD, aOne1, aZero, aN] AW' [wN] V' [sExact, sLt, sOkDE] t ∧
      V' sExact = b2n (decide (R = 0)) ∧ V' sLt = V sLt ∧ V' sOkDE = V sOkDE ∧
      (m < n → r < n → Q = (n - r) / (m + 1) ∧ R = (n - r) % (m + 1)) ∧
      A' aD = Q ∧ A' aOne1 = 1 ∧ A' aZero = 0 ∧ A' aN = n ∧ AW' wN = n := by
  have hw1 : 16 ≤ wq a := by simp only [wq]; omega_arith
  have hwq : wq a ≤ 256 := by simp only [wq]; omega_arith
  have wW : g.W = 2 * g.w + 2 := rfl
  have pw : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have pwW : 2 ^ (32 * g.w) ≤ 2 ^ (32 * g.W) := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have kwW : VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24) = g.W := kw_wid _
  obtain ⟨D, eD⟩ : ∃ D, D = (m % 2 ^ (32 * g.w) + 1) % 2 ^ (32 * g.w) := ⟨_, rfl⟩
  obtain ⟨N, eN⟩ : ∃ N, N = sub32 g.w n (r % 2 ^ (32 * g.w)) := ⟨_, rfl⟩
  obtain ⟨T, eT⟩ : ∃ T, T = 32 * wq a - 1 - Nat.log2 D := ⟨_, rfl⟩
  have Dlt : D < 2 ^ (32 * g.w) := by rw [eD]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have Nlt : N < 2 ^ (32 * g.w) := by rw [eN]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have gD : m < n → r < n → D = m + 1 ∧ N = n - r := fun hmn hrn => by
    refine ⟨?_, ?_⟩
    · rw [eD, Nat.mod_eq_of_lt (show m < 2 ^ (32 * g.w) by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    · rw [eN, Nat.mod_eq_of_lt (show r < 2 ^ (32 * g.w) by omega_arith), sub32,
        show n + 2 ^ (32 * g.w) - r = (n - r) + 2 ^ (32 * g.w) by omega_arith, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_arith)]
  unfold divB
  rw [seqs_append_iff, seqs_append_iff]
  refine WP.mono (divB_pre h hz hn hm hr hnW) fun t₁ P₁ => ?_
  rw [← eD, ← eN] at P₁
  refine WP.mono (dPhase_ok (good := m < n ∧ r < n) (T := T)
    (fun x => (D * 2 ^ x % 2 ^ (32 * g.W), N * 2 ^ x % 2 ^ (32 * g.W))) ha ha1 (by omega_arith) haw
    (fun ⟨hmn, hrn⟩ x k hx _ hk => by
      obtain ⟨e1, _⟩ := gD hmn hrn
      exact dRes_vals (by omega_arith) (by omega_arith) (by omega_arith) eT hx hk)
    (by rw [eT, show (2 : Nat) ^ 13 = 8192 from rfl]; omega_arith) (by omega_arith) P₁
    (fun _ => by
      show (D, N) = (D * 2 ^ 0 % _, N * 2 ^ 0 % _)
      rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]))
    fun t₂ ⟨v₂, P₂, hg₂⟩ => ?_
  obtain ⟨A₃, AW₃, V₃, h₃, _, hlt₃, hok₃, h1₃, hz₃, hn₃, hD₃, hN₃, hNW₃⟩ := P₂
  have h₃m := h₃.mono (ls' := [sLt, sOkDE]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
  simp only [seqs]
  refine WP.seq (WP.mono (wordDivQ_ok h₃m.rtW (h₃m.mlen ha ha1) (x := wNN) (r := wRB) (m := wDD) (t := wDt)
    (extra := false) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega_arith) (by rw [kwW]; omega_arith))
    fun t₄ ⟨_, k₄, mw₄, mt₄, rem₄, quo₄, _, K₄⟩ => ?_)
  rw [kwW] at k₄ mw₄ mt₄ rem₄ quo₄
  simp only [xn, kwW, Bool.toNat_false, Nat.add_zero] at rem₄ quo₄
  have h₃n := h₃m.mono (liveW' := [wN]) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_arith, rfl⟩)
    (fun d hd => ⟨hd, rfl⟩)
  have h₄ : KS g s0 A₃ [aOne1, aZero, aN] (upd (upd AW₃ wNN (num t₄.mem g.B g.W wNN)) wRB
      (num t₄.mem g.B g.W wRB)) [wNN, wRB, wN] V₃ [sLt, sOkDE] t₄ :=
    h₃n.core k₄ (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> exact h₃n.wsW.arr_fit (by decide)) (by decide) (K₄.mono (by decide))
      (h₃n.arrs_W k₄ (by decide) (by decide)) (by decide)
      (fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl
        · rw [upd_ne _ _ (by decide), upd_self]
        · rw [upd_self]
        · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
          exact (h₃n.arrsW_W k₄ (by decide) (by decide)) wN (by simp))
      (by decide) (h₃n.sl_keep k₄ (by decide)) h₃n.ls_ok
  have h₅ := (h₄.view (j := wNN) (by simp)).view (j := wRB) (by simp)
  refine WP.seq (WP.mono (h₅.copy_w (o := aD) (a := 2 * wNN) (by decide) (by simp) (by decide) (by decide))
    fun t₆ ⟨h₆, _, _⟩ => ?_)
  refine WP.mono (h₆.eq_w (d := sExact) (a := 2 * wRB) (b := aZero) (by simp) (by simp) (by decide)) fun t h₇ => ?_
  -- The values.
  obtain ⟨QN, eQ⟩ : ∃ QN, QN = num t₄.mem g.B g.W wNN := ⟨_, rfl⟩
  obtain ⟨RN, eR⟩ : ∃ RN, RN = num t₄.mem g.B g.W wRB := ⟨_, rfl⟩
  rw [← eQ, ← eR] at h₇
  have h1' : A₃ 26 = 1 := h1₃
  have hz' : A₃ 10 = 0 := hz₃
  have hn' : A₃ 32 = n := hn₃
  have hNW' : AW₃ 19 = n := hNW₃
  have hlt' : V₃ 16 = V sLt := hlt₃
  have hok' : V₃ 144 = V sOkDE := hok₃
  have hRN : RN < 2 ^ (32 * g.W) := by rw [eR]; exact val32_lt _ _ _ _
  have good : m < n ∧ r < n → QN % 2 ^ (32 * g.w) = (n - r) / (m + 1) ∧
      (RN % 2 ^ (32 * g.w) = 0 ↔ (n - r) % (m + 1) = 0) := by
    rintro ⟨hmn, hrn⟩
    obtain ⟨e1, e2⟩ := gD hmn hrn
    have hv := hg₂ ⟨hmn, hrn⟩
    have D0 : 0 < D := by omega_arith
    have DW : D < 2 ^ (32 * wq a) := by omega_arith
    have NW : N < 2 ^ (32 * wq a) := by omega_arith
    obtain ⟨top, Dlt', Nlt'⟩ := norm_vals D0 DW NW eT (show 2 * wq a ≤ g.W by omega_arith)
    have eD3 : num t₂.mem g.B g.W wDD = D * 2 ^ T := by
      rw [h₃m.arrsW wDD (by simp), hD₃, hv]; exact Nat.mod_eq_of_lt (by omega_arith)
    have eN3 : val32 t₂.mem g.B (arr g.W wNN) g.W = N * 2 ^ T := by
      change num t₂.mem g.B g.W wNN = _
      rw [h₃m.arrsW wNN (by simp), hN₃, hv]; exact Nat.mod_eq_of_lt Nlt'
    have low3 : val32 t₂.mem g.B (arr g.W wDD) (wq a) = D * 2 ^ T := by
      have e := val32_mod (m := t₂.mem) (B := g.B) (arr g.W wDD) (wq a) (g.W - wq a)
      rw [show wq a + (g.W - wq a) = g.W by omega_arith] at e
      rw [← e]; change num t₂.mem g.B g.W wDD % _ = _; rw [eD3, Nat.mod_eq_of_lt Dlt']
    have topw : 2 ^ 31 ≤ w32 t₂.mem g.B (arr g.W wDD + 4 * (wq a - 1)) := by
      have e := val32_top (m := t₂.mem) (B := g.B) (d := arr g.W wDD) (W' := wq a) (K := 0) (by omega_arith)
      rw [Nat.add_zero, low3, Nat.mod_eq_of_lt Dlt'] at e
      rw [← e, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
        show 31 + 32 * (wq a - 1) = 32 * wq a - 1 by omega_arith]
      exact top
    have low4 : val32 t₄.mem g.B (arr g.W wDD) (wq a) = D * 2 ^ T := by
      rw [← low3]
      apply val32_congr
      intro j hj
      by_cases ej : j = wq a - 1
      · subst ej
        have lt32 := (t₂.mem.readW (off g.B (arr g.W wDD + 4 * (wq a - 1))) 32).isLt
        have e := mt₄
        simp only [mw] at e
        change w32 t₄.mem g.B (arr g.W wDD + 4 * (wq a - 1)) = w32 t₂.mem g.B (arr g.W wDD + 4 * (wq a - 1))
        rw [e]
        change w32 t₂.mem g.B _ % 2 ^ 31 + 2 ^ 31 = w32 t₂.mem g.B _
        change _ < 2 ^ 32 at lt32
        have : w32 t₂.mem g.B (arr g.W wDD + 4 * (wq a - 1)) < 2 ^ 32 := lt32
        omega_arith
      · exact mw₄ j (by omega_arith) ej
    rw [eN3, low4, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)] at quo₄
    rw [← eR, eN3, low4, Nat.mul_mod_mul_right] at rem₄
    have NDlt : N / D < 2 ^ (32 * g.w) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) Nlt
    have Rlt : N % D * 2 ^ T < 2 ^ (32 * g.w) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ D0) (Nat.two_pow_pos _)) (by omega_arith)
    refine ⟨?_, ?_⟩
    · have e1' := val32_mod (m := t₄.mem) (B := g.B) (arr g.W wNN) g.w (g.w + 2)
      rw [show g.w + (g.w + 2) = g.W by omega_arith] at e1'
      have e2' := val32_mod (m := t₄.mem) (B := g.B) (arr g.W wNN) g.w (g.W - wq a + 1 - g.w)
      rw [show g.w + (g.W - wq a + 1 - g.w) = g.W - wq a + 1 by omega_arith, quo₄, Nat.mod_eq_of_lt NDlt] at e2'
      rw [eQ]
      change val32 t₄.mem g.B (arr g.W wNN) g.W % _ = _
      rw [e1', ← e2', ← e1, ← e2]
    · rw [rem₄, Nat.mod_eq_of_lt Rlt, Nat.mul_eq_zero, ← e1, ← e2]
      have := Nat.two_pow_pos T
      omega_arith
  refine ⟨QN % 2 ^ (32 * g.w),
    if m < n ∧ r < n then (n - r) % (m + 1) else RN % 2 ^ (32 * g.w), _, _, _,
    h₇.mono (fun j hj => ⟨by simp at hj ⊢; omega_arith, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega_arith, rfl⟩)
      (fun d hd => ⟨by simp at hd ⊢; omega_arith, rfl⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases G : m < n ∧ r < n
    · simp [upd, aD, wNN, wRB, aZero, sExact, hz', G, b2n, (good G).2]
    · simp [upd, aD, wNN, wRB, aZero, sExact, hz', G, b2n]
  · simp [upd, sExact, sLt, hlt']
  · simp [upd, sExact, sOkDE, hok']
  · intro hmn hrn; exact ⟨(good ⟨hmn, hrn⟩).1, by simp [hmn, hrn]⟩
  · simp [upd, aD, wNN, wRB]
  · simp [upd, aD, wNN, wRB, aOne1, h1']
  · simp [upd, aD, wNN, wRB, aZero, hz']
  · simp [upd, aD, wNN, wRB, aN, hn']
  · simp [upd, wNN, wRB, wN, hNW']

end

end VG.Proof.Rsa.X86.Recover
