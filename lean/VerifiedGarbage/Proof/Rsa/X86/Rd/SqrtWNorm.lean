module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the square root's normalization, which only `Rd/SqrtW.lean` composes

/-! # The square root by words on i686: the radicand normalized

`RecoverDetRt.normX`: the radicand `X < 2^(32 H)` (`H = 2 W'`, `W' = ⌈n_len / 4⌉`) in the wide
`wR`, its words from `H` on cleared (`clearAboveH`), `X = 0` made one (`zeroX`), then shifted up
by the word stages `c = 256, …, 1` where its top `c` of `H` words are zero, and by the even bit
stages `b = 16, …, 2` where the top `b` bits of its word `H - 1` are, so that word is at least
`2^30` (`normX_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Mont.X86 (at_ sc)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Impl.Rsa.X86.KeyRt (arrPtr bytesB)
open VG.Proof.Rsa.X86.KeyRt (kw arrPtr_ok lenSrc bytesB_ok)

theorem mem_of_sub {l₁ l₂ : List Nat} (h : ∀ d ∈ l₁, d ∈ l₂) {d : Nat} (hd : d ∈ l₁) : d ∈ l₂ := h d hd

/-! ## Words cleared -/

/-- After words `0, …, j - 1` of a loop storing zeros at `esi`, `edx` counting `K` words' bytes. -/
structure ZeroI (s : State) (B : Addr) (d K j : Nat) (u : State) : Prop where
  si : PtrAt u B .esi (d + 4 * j)
  dx : u.gpr .edx = BitVec.ofNat 32 (4 * (K - j))
  keep : Keeps [.eax, .edx, .esi] s u
  out : Outside B d (4 * j) s.mem u.mem
  val : val32 u.mem B d j = 0

theorem zeroStepX_ok {s u : State} {B : Addr} {bytes d K j : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (hd : d + 4 * K ≤ bytes) (hK32 : 4 * K < 2 ^ 32) (hj : j < K) (I : ZeroI s B d K j u) :
    WP isa (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4),
      .alu .sub .edx (.imm 4)]) u fun u' => u'.zf = some (decide (j + 1 = K)) ∧ ZeroI s B d K (j + 1) u' := by
  have nw := ws.nowrap
  have wsu := ws.of_wr I.keep.2.2
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have ws₁ := wsu.of_wr U₁.wr
  have p₁ : PtrAt u₁ B .esi (d + 4 * j) := by rw [PtrAt, U₁.other _ (by decide)]; exact I.si
  have hjK : d + 4 * j + 4 ≤ bytes := by omega_arith
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr ws₁ p₁ (d := 0) (by omega_arith))
    (VG.Proof.Mont.X86.Rt.ws_write ws₁ (y := d + 4 * j + 0) (n := 4) (by omega_arith)) fun u₂ M₂ => ?_
  refine wp_addS rfl fun u₃ U₃ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₄ U₄ z₄ => WP.block_nil ?_
  have hc := VG.Proof.Mont.X86.Rt.count_zf (N := K) (x := u.gpr .edx)
    (by rw [I.dx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]) hj
  have dx₃ : u₃.gpr .edx = u.gpr .edx := by
    rw [U₃.other _ (by decide), M₂.gpr, U₁.other _ (by decide)]
  have m₄ : u₄.mem = u.mem.writeW (off B (d + 4 * j)) (0 : BitVec 32) := by
    rw [U₄.mem, U₃.mem, M₂.mem, U₁.mem, U₁.gpr, Nat.add_zero]
  have O := writeW32_outside u.mem B (d := d + 4 * j) (0 : BitVec 32) (by omega_arith)
  rw [← m₄] at O
  refine ⟨by rw [z₄, dx₃, hc.2], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [PtrAt, U₄.other _ (by decide), U₃.gpr, VG.Proof.Mont.X86.Rt.ptr_add (s := u₂) (x := d + 4 * j)
      (by rw [PtrAt, M₂.gpr]; exact p₁)]
    congr 2
  · apply BitVec.eq_of_toNat_eq
    rw [U₄.gpr, dx₃, hc.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · exact I.keep.trans (((U₁.keeps.mono (by decide)).trans (M₂.keeps _)).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))
  · exact (I.out.mono (by omega_arith) (by omega_arith)).trans (O.mono (by omega_arith) (by omega_arith))
  · rw [val32_succ, O.val32 (.inl (by omega_arith)) (by omega_arith), I.val, m₄, w32_write_self]
    rfl

theorem zeroLoopS_ok {s u : State} {B : Addr} {bytes d K : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (hd : d + 4 * K ≤ bytes) (hK32 : 4 * K < 2 ^ 32) (hK : 0 < K) (I : ZeroI s B d K 0 u) :
    WP isa (.loop (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4),
      .alu .sub .edx (.imm 4)]) .ne) u fun v => ZeroI s B d K K v := by
  refine WP.loop (M := isa) (Q := fun v => ZeroI s B d K K v)
    (fun n v => ∃ j, n = K - j ∧ j < K ∧ ZeroI s B d K j v) ?_ _ u ⟨0, rfl, hK, I⟩
  rintro n v ⟨j, rfl, hj, J⟩
  refine WP.mono (zeroStepX_ok ws hd hK32 hj J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : j + 1 = K
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], K - (j + 1),
      by omega_arith, j + 1, rfl, by omega_arith, J'⟩

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem kwW (g : Geo) : kw (16 * g.n + 24) = g.W := kw_wid g.n

/-- `clearAboveH`: the words of `wR` from `H = 2 W'` on cleared: `[wR] mod 2^(32 H)`. -/
theorem KS.clearAbove_ok {a : Nat} (h : KS g s0 A live AW liveW V ls s) (hR : wR ∈ liveW)
    (hm : MLen s g.B g.Z nl a) (haw : wq a ≤ g.w)
    (hl : ∀ j ∈ live, j / 2 ≠ wR) :
    WP isa clearAboveH s fun t => KS g s0 A live (upd AW wR (AW wR % 2 ^ (64 * wq a))) liveW V ls t := by
  have hr := h.rtW
  have fit := hr.ws.arr_fit (show wR < 22 by decide)
  have nw := hr.ws.workspace.nowrap
  have kb := VG.Proof.Rsa.X86.KeyRt.kw_bound hr.lenLe
  have eW : g.W = 2 * g.w + 2 := rfl
  have hle := hm.le
  simp only [S, kwW] at fit kb
  unfold clearAboveH topH
  simp only [VG.Impl.Rsa.X86.Keys.seqs, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine arrPtr_ok (lenSrc hr) hr.lenLe hr.edi (r := .esi) (t := .edx) (j := wR) (by decide) (by decide)
    (by rw [kwW]; omega_arith) fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kwW] at p₁
  have hm₁ : MLen u₁ g.B g.Z nl a := hm.keep U₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.WordRt.width4_ok hm₁ fun u₂ U₂ m₂ e₂ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subS rfl fun u₅ U₅ _ => ?_
  have K₅ : Keeps [.esi, .edx] s u₅ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, m₂, m₁]
  have h₅ := hr.keep K₅ (by decide) (by decide) (by rw [m₅]; exact Outside.refl _ _ _ _)
  have p₅ : PtrAt u₅ g.B .esi (arr g.W wR + 4 * (2 * wq a)) := by
    have e4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
    have pp₂ : PtrAt u₂ g.B .esi (arr g.W wR) := by rw [PtrAt, U₂.1 _ (by decide)]; exact p₁
    rw [PtrAt, U₅.gpr, U₄.gpr, U₃.gpr, U₃.other _ (by decide), e₂, BitVec.toNat_sub,
      BitVec.toNat_add, BitVec.toNat_add, pp₂, e4]
    simp only [Nat.mul_zero, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
    have := g.B.isLt
    omega_arith
  refine bytesB_ok (lenSrc h₅) h₅.lenLe fun u₆ U₆ m₆ e₆ => ?_
  rw [kwW] at e₆
  have hm₆ : MLen u₆ g.B g.Z nl a :=
    hm.keep ((K₅.mono (by decide)).trans (U₆.mono (by decide)) : Keeps [.esi, .edx] s u₆) (by decide)
      (by rw [m₆, m₅]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.WordRt.width4_ok hm₆ fun u₇ U₇ m₇ e₇ =>
    wp_subS rfl fun u₈ U₈ _ => VG.Proof.Mont.X86.Rt.wp_subZ rfl fun u₉ U₉ z₉ => WP.block_nil ?_
  have K₉ : Keeps [.eax, .esi, .edx] s u₉ := (K₅.mono (by decide)).trans ((U₆.mono (by decide)).trans
    ((U₇.mono (by decide)).trans ((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide)))))
  have m₉ : u₉.mem = s.mem := by rw [U₉.mem, U₈.mem, m₇, m₆, m₅]
  have ax₉ : u₈.gpr .eax = BitVec.ofNat 32 (4 * wq a) := by rw [U₈.other _ (by decide), e₇]
  have dx₉ : u₉.gpr .edx = BitVec.ofNat 32 (4 * (g.W - 2 * wq a)) := by
    apply BitVec.eq_of_toNat_eq
    rw [U₉.gpr, U₈.gpr, ax₉, e₇, U₇.1 _ (by decide), BitVec.toNat_sub, BitVec.toNat_sub, e₆]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 4 * wq a) (by omega_arith), Nat.mod_eq_of_lt (a := 4 * (g.W - 2 * wq a)) (by omega_arith)]
    omega_arith
  have ne : (u₈.gpr .edx - u₈.gpr .eax == 0) = false := by
    rw [← U₉.gpr, dx₉]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    simp at this; omega_arith
  rw [ne] at z₉
  have p₉ : PtrAt u₉ g.B .esi (arr g.W wR + 4 * (2 * wq a)) := by
    rw [PtrAt, U₉.other _ (by decide), U₈.other _ (by decide), U₇.1 _ (by decide), U₆.1 _ (by decide)]; exact p₅
  refine WP.ite false (by simp only [eval, z₉]) (fun e => absurd e (by decide)) fun _ => ?_
  have I₀ : ZeroI u₉ g.B (arr g.W wR + 4 * (2 * wq a)) (g.W - 2 * wq a) 0 u₉ :=
    ⟨by simpa using p₉, by simpa using dx₉, Keeps.refl _ _, Outside.refl _ _ _ _, rfl⟩
  have ws₉ := h.rt.rt.of_keeps K₉
  refine WP.mono (zeroLoopS_ok ws₉ (by omega_arith) (by omega_arith) (by omega_arith) I₀) fun t I => ?_
  -- The value: its low `H` words kept, the rest zero, as they were.
  have O : Outside g.B (arr g.W wR + 4 * (2 * wq a)) (4 * (g.W - 2 * wq a)) s.mem t.mem := by
    rw [← m₉]; exact I.out
  have Kt : Keeps opRegs s t := (K₉.mono (by decide)).trans (I.keep.mono (by decide))
  have keep : Keep g.B g.W [wR] [] s.mem t.mem :=
    Keep.of_arr (d := 4 * (2 * wq a)) O (by simp only [S]; omega_arith) (by simp)
  have split : ∀ m : Mem, num m g.B g.W wR = val32 m g.B (arr g.W wR) (2 * wq a) +
      2 ^ (32 * (2 * wq a)) * val32 m g.B (arr g.W wR + 4 * (2 * wq a)) (g.W - 2 * wq a) := fun m => by
    rw [num, ← val32_append, show 2 * wq a + (g.W - 2 * wq a) = g.W by omega_arith]
  have v0 := h.arrsW wR hR
  have value : num t.mem g.B g.W wR = AW wR % 2 ^ (64 * wq a) := by
    rw [← v0, split, split, O.val32 (.inl (by omega_arith)) (by omega_arith), I.val,
      show 64 * wq a = 32 * (2 * wq a) by omega_arith, Nat.mul_zero, Nat.add_zero, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
  have ht := h.write_W keep (by decide) (by simp) Kt value hl (by simp)
  exact ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩)

end

/-! ## `X = 0` made one -/

theorem val32_succ' (m : Mem) (B : Addr) (d n : Nat) :
    val32 m B d (n + 1) = w32 m B d + 2 ^ 32 * val32 m B (d + 4) n := rfl

/-- Word 0 or'ed with `[X = 0]`: `X + [X = 0]`. -/
theorem or_low_val {m : Mem} {B : Addr} {d n : Nat} (hn : d + 4 * (n + 1) ≤ 2 ^ 64) :
    val32 (m.writeW (off B d) (BitVec.ofNat 32 (if val32 m B d (n + 1) = 0 then 1 else 0) |||
      m.readW (off B d) 32)) B d (n + 1) = val32 m B d (n + 1) + (if val32 m B d (n + 1) = 0 then 1 else 0) := by
  obtain ⟨z, hz⟩ : ∃ z, z = (if val32 m B d (n + 1) = 0 then 1 else 0) := ⟨_, rfl⟩
  rw [← hz]
  have O := writeW32_outside m B (d := d) (BitVec.ofNat 32 z ||| m.readW (off B d) 32) (by omega_arith)
  rw [val32_succ' (m.writeW _ _), val32_succ' m, O.val32 (.inr (Nat.le_refl _)) (by omega_arith), w32_write_self]
  by_cases hX : val32 m B d (n + 1) = 0
  · simp only [hX, ↓reduceIte] at hz
    subst hz
    rw [val32_succ'] at hX
    have hw : w32 m B d = 0 := by omega_arith
    have h0 : m.readW (off B d) 32 = 0 := BitVec.eq_of_toNat_eq hw
    have : val32 m B (d + 4) n = 0 := by omega_arith
    rw [h0, hw, this]
    rfl
  · simp only [hX, ↓reduceIte] at hz
    subst hz
    rw [BitVec.toNat_or, show (BitVec.ofNat 32 0).toNat = 0 from rfl, Nat.zero_or, Nat.add_zero]
    rfl

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat}

/-- `zeroX`: `sZf = [X = 0]`, `X := X + [X = 0]`, `sKw = sZb = 0`. -/
theorem zeroX_ok {X : Nat} (h : KS g s0 A [aD, aZero] AW [wR] V sqSlotsW s) (hX : AW wR = X) :
    WP isa zeroX s fun t => ∃ AW' V', KS g s0 A [aD, aZero] AW' [wR] V' lsN t ∧
      (∀ d ∈ sqSlotsW, V' d = V d) ∧ V' sZf = (if X = 0 then 1 else 0) ∧ V' sKw = 0 ∧ V' sZb = 0 ∧
      AW' wR = X + V' sZf := by
  unfold zeroX
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.orAll (by simp [sqZ])) fun t₁ ⟨h₁, K₁, e₁⟩ => ?_)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono h₁.flagZero fun t₂ ⟨h₂, K₂⟩ => ?_)
  have z₂ : (if t₁.gpr .ecx = 0 then 1 else 0) = (if X = 0 then 1 else 0) := by
    by_cases hz : X = 0
    · have : t₁.gpr .ecx = 0 := e₁.mpr (hX.trans hz)
      simp only [this, hz, ↓reduceIte]
    · have : ¬ t₁.gpr .ecx = 0 := fun e => hz (hX ▸ e₁.mp e)
      simp only [this, hz, ↓reduceIte]
  rw [z₂] at h₂
  generalize hzf : (if X = 0 then 1 else 0) = zf at h₂
  have zf1 : zf < 2 ^ 32 := by rw [← hzf]; split <;> decide
  refine wp_movS (h₂.readSlot (by simp)) fun t₃ U₃ _ => ?_
  have h₃ := h₂.of_rest U₃.keeps (by decide) U₃.mem
  rw [upd_self] at U₃
  refine WP.block_append (M := isa) (l₁ := ([.store (sc sZf) .eax] : List Instr)) (WP.mono (h₃.storeSlot (d := sZf) (by decide) .eax)
    fun t₄ ⟨h₄, _, K₄⟩ => ?_)
  rw [U₃.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt zf1] at h₄
  have hr := h₄.rtW
  have fit := hr.ws.arr_fit (show wR < 22 by decide)
  have nw := hr.ws.workspace.nowrap
  simp only [S, kwW] at fit
  refine arrPtr_ok (lenSrc hr) hr.lenLe hr.edi (r := .esi) (t := .edx) (j := wR) (by decide) (by decide)
    (by rw [kwW]; omega_arith) fun t₅ U₅ m₅ p₅ _ => ?_
  rw [kwW] at p₅
  have ws₅ := h₄.rt.rt.of_keeps U₅
  have ax₅ : t₅.gpr .eax = BitVec.ofNat 32 zf := by
    rw [U₅.1 _ (by decide), K₄.1 _ (by decide), U₃.gpr]
  refine wp_orS (VG.Proof.Mont.X86.Rt.readSrc_ptr ws₅ p₅ (d := 0) (by omega_arith)) fun t₆ U₆ => ?_
  have p₆ : PtrAt t₆ g.B .esi (arr g.W wR) := by rw [PtrAt, U₆.other _ (by decide)]; exact p₅
  have ws₆ := ws₅.of_wr U₆.wr
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr ws₆ p₆ (d := 0) (by omega_arith))
    (VG.Proof.Mont.X86.Rt.ws_write ws₆ (y := arr g.W wR + 0) (n := 4) (by omega_arith)) fun t₇ M₇ => ?_
  have m₇ : t₇.mem = t₄.mem.writeW (off g.B (arr g.W wR)) (BitVec.ofNat 32 zf |||
      t₄.mem.readW (off g.B (arr g.W wR)) 32) := by
    rw [M₇.mem, U₆.gpr, ax₅, U₆.mem, m₅]; simp only [Nat.add_zero]
  have K₇ : Keeps opRegs t₄ t₇ := (U₅.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans (M₇.keeps _))
  have O₇ : Outside g.B (arr g.W wR + 0) 4 t₄.mem t₇.mem := by
    rw [m₇, Nat.add_zero]; exact writeW32_outside _ _ _ (by omega_arith)
  have keep : Keep g.B g.W [wR] [] t₄.mem t₇.mem := Keep.of_arr (d := 0) O₇ (by simp only [S]; omega_arith) (by simp)
  have v₄ : num t₄.mem g.B g.W wR = X := by rw [h₄.arrsW wR (by simp), hX]
  have value : num t₇.mem g.B g.W wR = X + zf := by
    obtain ⟨W1, hW1⟩ : ∃ W1, g.W = W1 + 1 := ⟨2 * (2 * g.n + 2) + 1, rfl⟩
    have := or_low_val (m := t₄.mem) (B := g.B) (d := arr g.W wR) (n := W1) (by omega_arith)
    rw [← hW1] at this
    rw [num, m₇, ← hzf, ← v₄, num]
    exact this
  have h₇ := h₄.write_W keep (by decide) (by simp) K₇ value
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl <;> decide)
    (by simp)
  refine wp_movS (v := 0) rfl fun t₈ U₈ _ => ?_
  have h₈ := h₇.of_rest U₈.keeps (by decide) U₈.mem
  refine WP.block_append (M := isa) (l₁ := ([.store (sc sKw) .eax] : List Instr)) (WP.mono (h₈.storeSlot (d := sKw) (by decide) .eax)
    fun t₉ ⟨h₉, _, K₉⟩ => ?_)
  refine WP.mono (h₉.storeSlot (d := sZb) (by decide) .eax) fun t ⟨ht, _, Kt⟩ => ?_
  have e0 : (t₈.gpr .eax).toNat = 0 := by rw [U₈.gpr]; rfl
  have e0' : (t₉.gpr .eax).toNat = 0 := by rw [K₉.1 _ (by simp)]; exact e0
  rw [e0, e0'] at ht
  refine ⟨_, _, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; exact hj, rfl⟩)
    (fun d hd => ⟨mem_of_sub (by decide) hd, rfl⟩), ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [upd, sZb, sKw, sZf, sStg, sOkDE, sLt, sExact, sOk4]
  · simp [upd, sZb, sKw, sZf]
  · simp [upd, sZb, sKw]
  · simp [upd]
  · simp [upd, sZb, sKw, sZf]

end

/-! ## A word stage -/

/-- A number's words `L, …, L + c - 1` are zero exactly where it is below `2^(32 L)`, for a number
below `2^(32 (L + c))`. -/
theorem top_zero_iff {m : Mem} {B : Addr} {d L c R : Nat} (hx : val32 m B d (L + c + R) < 2 ^ (32 * (L + c))) :
    val32 m B (d + 4 * L) c = 0 ↔ val32 m B d (L + c + R) < 2 ^ (32 * L) := by
  have e1 := val32_append m B d (L + c) R
  have e2 := val32_append m B d L c
  have lo := val32_lt m B d L
  have p1 := Nat.two_pow_pos (32 * (L + c))
  have p2 := Nat.two_pow_pos (32 * L)
  have hi : val32 m B (d + 4 * (L + c)) R = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * (L + c)) R) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * (L + c))) e; omega_arith
  rw [e1, hi, Nat.mul_zero, Nat.add_zero, e2]
  constructor
  · intro z; rw [z, Nat.mul_zero, Nat.add_zero]; exact lo
  · intro lt
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * L) c) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * L)) e; omega_arith

/-- A mask `0 - z` (`z` a bit) and'ed with `y`, plus `K`. -/
theorem mask_and_add (z y K : Nat) (hz : z ≤ 1) (hy : y < 2 ^ 32) (hK : K + y < 2 ^ 32) :
    (((0 - BitVec.ofNat 32 z) &&& BitVec.ofNat 32 y) + BitVec.ofNat 32 K).toNat = K + y * z := by
  rcases (show z = 0 ∨ z = 1 by omega_arith) with rfl | rfl
  · rw [show (0 : BitVec 32) - BitVec.ofNat 32 0 = 0 from rfl, BitVec.toNat_add, BitVec.toNat_and,
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_and, BitVec.toNat_ofNat, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 from rfl, BitVec.allOnes_and,
      BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `stageXWH`'s or of `X`'s words `H - c, …, H - 1`. -/
theorem KS.orTopW {a c : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z nl a) (haw : wq a ≤ g.w) (hC : sC4 ∈ ls) (hV : V sC4 = 4 * c) (hc0 : 0 < c)
    (hc : c ≤ 2 * wq a) :
    WP isa (.seq (.block (arrPtr wid .esi sqZ .edx ++ VG.Impl.Rsa.X86.WordModRt.width4 nl .edx ++
      ([.alu .add .esi (.reg .edx), .alu .add .esi (.reg .edx), .mov .edx (.mem (sc sC4)), .alu .sub .esi (.reg .edx),
        .mov .ecx (.imm 0)] : List Instr))) orEsiLoop) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ Keeps opRegs s t ∧
      (t.gpr .ecx = 0 ↔ val32 s.mem g.B (arr g.W wR + 4 * (2 * wq a - c)) c = 0) := by
  have hr := h.rtW
  have fit := hr.ws.arr_fit (show wR < 22 by decide)
  have nw := hr.ws.workspace.nowrap
  have eW : g.W = 2 * g.w + 2 := rfl
  have hle := hm.le
  simp only [S, kwW] at fit
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine arrPtr_ok (lenSrc hr) hr.lenLe hr.edi (r := .esi) (t := .edx) (j := wR) (by decide) (by decide)
    (by rw [kwW]; omega_arith) fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kwW] at p₁
  have hm₁ : MLen u₁ g.B g.Z nl a := hm.keep U₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.WordRt.width4_ok hm₁ fun u₂ U₂ m₂ e₂ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => ?_
  have K₄ : Keeps opRegs s u₄ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide))))
  have m₄ : u₄.mem = s.mem := by rw [U₄.mem, U₃.mem, m₂, m₁]
  have h₄ := h.of_rest K₄ (fun x hx => hx) m₄
  refine wp_movS (h₄.readSlot hC) fun u₅ U₅ _ => wp_subS rfl fun u₆ U₆ _ => wp_movS (v := 0) rfl
    fun u₇ U₇ _ => WP.block_nil ?_
  have K₇ : Keeps opRegs s u₇ := K₄.trans ((U₅.keeps.mono (by decide)).trans
    ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide))))
  have m₇ : u₇.mem = s.mem := by rw [U₇.mem, U₆.mem, U₅.mem, m₄]
  have e4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have ec : (BitVec.ofNat 32 (4 * c)).toNat = 4 * c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have p₇ : PtrAt u₇ g.B .esi (arr g.W wR + 4 * (2 * wq a - c)) := by
    have pp₂ : PtrAt u₂ g.B .esi (arr g.W wR) := by rw [PtrAt, U₂.1 _ (by decide)]; exact p₁
    rw [PtrAt, U₇.other _ (by decide), U₆.gpr, U₅.other _ (by decide), U₅.gpr, hV, U₄.gpr, U₃.gpr,
      U₃.other _ (by decide), e₂, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, pp₂, e4, ec]
    have := g.B.isLt
    omega_arith
  have n₇ : (u₇.gpr .edx).toNat = 4 * c := by rw [U₇.other _ (by decide), U₆.other _ (by decide), U₅.gpr, hV, ec]
  have c₇ : u₇.gpr .ecx = 0 := by rw [U₇.gpr]
  refine WP.mono (orEsiLoop_ok (h.rt.rt.of_keeps K₇) hc0 (by omega_arith) p₇ n₇) fun t ⟨mt, et, Kt⟩ => ?_
  have K : Keeps opRegs s t := K₇.trans (Kt.mono (by decide))
  refine ⟨h.of_rest K (fun x hx => hx) (by rw [mt, m₇]), K, ?_⟩
  rw [et, m₇]
  exact ⟨fun e => e.2, fun e => ⟨c₇, e⟩⟩

end

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat}

theorem shr2_four (c : Nat) (hc : 4 * c < 2 ^ 32) : BitVec.ofNat 32 (4 * c) >>> 2 = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- A word stage of `normX` (`4 c` in `sC4`): where `X`'s top `c` of `H` words are zero, `X` up by
`c` words and `sKw += c`. -/
theorem stageXW_ok {a c : Nat} (h : KS g s0 A [aD, aZero] AW [wR] V (sC4 :: lsN) s)
    (hm : MLen s g.B g.Z nl a) (haw : wq a ≤ g.w) (hV : V sC4 = 4 * c) (hc0 : 0 < c) (hc : c < 2 * wq a)
    (hx : AW wR < 2 ^ (64 * wq a)) (hK : V sKw ≤ 1024) :
    WP isa stageXWH s fun t => ∃ AW' V', KS g s0 A [aD, aZero] AW' [wR] V' (sC4 :: lsN) t ∧
      (∀ d ∈ sC4 :: lsN, d ≠ sKw → V' d = V d) ∧
      (if AW wR < 2 ^ (32 * (2 * wq a - c)) then AW' wR = AW wR * 2 ^ (32 * c) ∧ V' sKw = V sKw + c
       else AW' wR = AW wR ∧ V' sKw = V sKw) := by
  have hle := hm.le
  have hwq : wq a ≤ 256 := by simp only [wq]; omega_arith
  have eW : g.W = 2 * g.w + 2 := rfl
  unfold stageXWH
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.orTopW hm haw (by simp) hV hc0 (by omega_arith)) fun t₁ ⟨h₁, K₁, e₁⟩ => ?_)
  -- The top words zero: `X < 2^(32 (H - c))`.
  have top : t₁.gpr .ecx = 0 ↔ AW wR < 2 ^ (32 * (2 * wq a - c)) := by
    rw [e₁, ← h.arrsW wR (by simp), num]
    have e : g.W = (2 * wq a - c) + c + (g.W - 2 * wq a) := by omega_arith
    have hx' := hx
    rw [← h.arrsW wR (by simp), num, e, show 64 * wq a = 32 * ((2 * wq a - c) + c) by omega_arith] at hx'
    rw [e]
    exact top_zero_iff hx'
  generalize hz : (if t₁.gpr .ecx = 0 then 1 else 0) = z
  have z1 : z ≤ 1 := by rw [← hz]; split <;> decide
  refine WP.seq (WP.block_append (WP.mono h₁.flagZero fun t₂ ⟨h₂, K₂⟩ => ?_))
  rw [hz] at h₂
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have h₂₁ := h₂.of_rest U₁.keeps (by decide) U₁.mem
  have r₂ := h₂₁.readSlot (d := sStg) (by simp)
  rw [upd_self] at r₂
  refine wp_subS r₂ fun u₂ U₂ _ => ?_
  have h₂' := h₂₁.of_rest U₂.keeps (by decide) U₂.mem
  have rC := h₂'.readSlot (d := sC4) (by simp)
  rw [upd_ne _ _ (by decide), hV] at rC
  refine wp_movS rC fun u₃ U₃ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₄ U₄ =>
    wp_logicS (.inl rfl) rfl fun u₅ U₅ => ?_
  have K₅ : Keeps opRegs u₂ u₅ := (U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans
    (U₅.keeps.mono (by decide)))
  have h₅ := h₂'.of_rest K₅ (fun x hx => hx) (by rw [U₅.mem, U₄.mem, U₃.mem])
  have rK := h₅.readSlot (d := sKw) (by simp)
  rw [upd_ne _ _ (by decide)] at rK
  refine wp_addS rK fun u₆ U₆ _ => ?_
  have h₆ := h₅.of_rest U₆.keeps (by decide) U₆.mem
  refine WP.mono (h₆.storeSlot (d := sKw) (by decide) .edx) fun t₃ ⟨h₃, _, K₃⟩ => ?_
  have v₃ : (u₆.gpr .edx).toNat = V sKw + c * z := by
    rw [U₆.gpr, U₅.gpr, show ∀ x y : BitVec 32, (if AluOp.and = AluOp.and then x &&& y else x ^^^ y) = x &&& y
      from fun _ _ => rfl, U₄.other .edx (by decide), U₃.other .edx (by decide),
      U₂.gpr, U₁.gpr, U₄.gpr, U₃.gpr, shr2_four c (by omega_arith)]
    exact mask_and_add z c (V sKw) z1 (by omega_arith) (by omega_arith)
  rw [v₃] at h₃
  -- `X` up by `c` words into `wT`, and selected.
  have hV₃ : upd (upd V sStg z) sKw (V sKw + c * z) sC4 = 4 * c := by simp only [upd, show sC4 ≠ sKw by decide, show sC4 ≠ sStg by decide, ↓reduceIte]; exact hV
  refine WP.seq (WP.mono (h₃.moveUp_W (o := VG.Impl.Rsa.X86.RecoverDetRt.wT) (a := wR) (c := c) (by decide)
    (by simp) (by decide) (by omega_arith) (by simp) hV₃ (by decide)) fun t₄ ⟨h₄, K₄, _⟩ => ?_)
  refine WP.mono (h₄.sel_W (o := wR) (a := wR) (b := VG.Impl.Rsa.X86.RecoverDetRt.wT) (sl := sStg) (by decide)
    (by simp) (by simp) (by simp) (by simp [upd, z1, sStg, sKw]) (.inr (by decide)) (by decide)) fun t ⟨ht, _⟩ => ?_
  refine ⟨_, _, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; exact .inl hj, rfl⟩)
    (fun d hd => ⟨mem_of_sub (by decide) hd, rfl⟩), ?_, ?_⟩
  · intro d hd hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [upd, sStg, sC4, sKw, sZf, sZb,
      sOkDE, sLt, sExact, sOk4]
  · by_cases hlt : AW wR < 2 ^ (32 * (2 * wq a - c))
    · have z' : z = 1 := by rw [← hz]; simp only [top.mpr hlt, ↓reduceIte]
      subst z'
      have mw : AW wR * 2 ^ (32 * c) % 2 ^ (32 * g.W) = AW wR * 2 ^ (32 * c) := by
        have h1 : AW wR * 2 ^ (32 * c) < 2 ^ (32 * (2 * wq a - c)) * 2 ^ (32 * c) :=
          Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
        have h2 : 2 ^ (32 * (2 * wq a - c)) * 2 ^ (32 * c) ≤ 2 ^ (32 * g.W) := by
          rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
        exact Nat.mod_eq_of_lt (by omega_arith)
      simp only [upd, show sStg ≠ sKw by decide, ↓reduceIte, hlt, mw, Nat.one_ne_zero, Nat.mul_one, and_self]
    · have z' : z = 0 := by rw [← hz]; simp only [show ¬ t₁.gpr .ecx = 0 from fun e => hlt (top.mp e), ↓reduceIte]
      subst z'
      simp only [upd, show sStg ≠ sKw by decide, show wR ≠ VG.Impl.Rsa.X86.RecoverDetRt.wT by decide,
        ↓reduceIte, hlt, Nat.mul_zero, Nat.add_zero, and_true]

end

/-! ## A bit stage -/

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The doubling of `wT`, `b` times (`b` in `sB`). -/
theorem KS.doubles {b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (hT : VG.Impl.Rsa.X86.RecoverDetRt.wT ∈ liveW) (hB : VG.Impl.Rsa.X86.RecoverDetRt.sB ∈ ls) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sB = b) (hb : 0 < b) (hb32 : b < 2 ^ 32)
    (hl : ∀ j ∈ live, j / 2 ≠ VG.Impl.Rsa.X86.RecoverDetRt.wT) :
    WP isa (timesH (VG.Impl.Rsa.X86.KeyRt.chain wid .adc VG.Impl.Rsa.X86.RecoverDetRt.wT
        VG.Impl.Rsa.X86.RecoverDetRt.wT VG.Impl.Rsa.X86.RecoverDetRt.wT false)) s fun t =>
      ∃ V', KS g s0 A live (upd AW VG.Impl.Rsa.X86.RecoverDetRt.wT
          (AW VG.Impl.Rsa.X86.RecoverDetRt.wT * 2 ^ b % 2 ^ (32 * g.W))) liveW V' (sBc :: ls) t ∧
        ∀ d ∈ ls, d ≠ sBc → V' d = V d := by
  have lt : AW VG.Impl.Rsa.X86.RecoverDetRt.wT < 2 ^ (32 * g.W) := by
    rw [← h.arrsW _ hT]; exact val32_lt _ _ _ _
  let P : Nat → Nat → State → Prop := fun e i t => ∃ V', KS g s0 A live (upd AW VG.Impl.Rsa.X86.RecoverDetRt.wT
      (AW VG.Impl.Rsa.X86.RecoverDetRt.wT * 2 ^ e % 2 ^ (32 * g.W))) liveW V' (sBc :: ls) t ∧
    (∀ d ∈ ls, d ≠ sBc → V' d = V d) ∧ V' sBc = b - i
  refine timesH_ok (fun i => P i i) (fun i => P (i + 1) i) hb hb32 h.ws (by rw [h.sl _ hB, hV]) ?_ ?_ ?_ ?_
  · intro t k e K
    refine ⟨upd V sBc b, (h.slot1 k (by decide) (K.mono (by decide)) e).mono (fun j hj => ⟨hj, rfl⟩)
      (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), fun d _ hd => upd_ne _ _ hd, by simp [upd]⟩
    by_cases e : j = VG.Impl.Rsa.X86.RecoverDetRt.wT
    · subst e; rw [upd_self, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt lt]
    · rw [upd_ne _ _ e]
  · rintro i t - ⟨V', ht, hV', hc⟩
    refine WP.mono (ht.add_W (o := VG.Impl.Rsa.X86.RecoverDetRt.wT) (a := VG.Impl.Rsa.X86.RecoverDetRt.wT)
      (b := VG.Impl.Rsa.X86.RecoverDetRt.wT) (by decide) hT hT hl) fun u ⟨hu, _⟩ => ?_
    refine ⟨V', hu.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
      (fun d hd => ⟨hd, rfl⟩), hV', hc⟩
    by_cases e : j = VG.Impl.Rsa.X86.RecoverDetRt.wT
    · subst e
      simp only [upd_self]
      rw [Nat.pow_succ, ← Nat.add_mod, ← Nat.mul_two, Nat.mul_assoc]
    · simp only [upd_ne _ _ e]
  · rintro i t - ⟨V', ht, -, hc⟩
    exact ⟨ht.ws, by rw [ht.sl _ (by simp), hc]⟩
  · rintro i t u - ⟨V', ht, hV', -⟩ k e K
    have hu := ht.slot1 k (by decide) K e
    refine ⟨fun _ => ⟨upd V' sBc (b - (i + 1)), hu.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), fun d hd hne => by rw [upd_ne _ _ hne, hV' d hd hne],
      by simp [upd]⟩, fun hi => ⟨upd V' sBc (b - (i + 1)), ?_, fun d hd hne => by rw [upd_ne _ _ hne, hV' d hd hne]⟩⟩
    subst hi
    exact hu.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)

end

/-- Word `L` of a number below `2^(32 (L + 1))`: its value over `2^(32 L)`. -/
theorem top_word {m : Mem} {B : Addr} {d L R : Nat} (hx : val32 m B d (L + 1 + R) < 2 ^ (32 * (L + 1))) :
    w32 m B (d + 4 * L) = val32 m B d (L + 1 + R) / 2 ^ (32 * L) := by
  have e1 := val32_append m B d (L + 1) R
  have e2 := val32_append m B d L 1
  have lo := val32_lt m B d L
  have p1 := Nat.two_pow_pos (32 * (L + 1))
  have hi : val32 m B (d + 4 * (L + 1)) R = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * (L + 1)) R) with e | e
    · exact e
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * (L + 1))) e; omega_arith
  have one : val32 m B (d + 4 * L) 1 = w32 m B (d + 4 * L) := by simp [val32]
  rw [e1, hi, Nat.mul_zero, Nat.add_zero, e2, one, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt lo, Nat.zero_add]

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat}

/-- `topH .esi sqZ 1` and the read: `eax` the word `H - 1` of `X`. -/
theorem KS.readTop {a : Nat} {live : List Nat} {liveW ls : List Nat} (h : KS g s0 A live AW liveW V ls s)
    (hm : MLen s g.B g.Z nl a) (ha0 : 1 ≤ a) (haw : wq a ≤ g.w) :
    WP isa (.block (topH .esi sqZ 1 .edx ++ ([.mov .eax (.mem (at_ .esi 0))] : List Instr))) s fun t =>
      KS g s0 A live AW liveW V ls t ∧ Keeps opRegs s t ∧
      (t.gpr .eax).toNat = w32 s.mem g.B (arr g.W wR + 4 * (2 * wq a - 1)) := by
  have hr := h.rtW
  have fit := hr.ws.arr_fit (show wR < 22 by decide)
  have nw := hr.ws.workspace.nowrap
  have eW : g.W = 2 * g.w + 2 := rfl
  have hle := hm.le
  have hwq : 1 ≤ wq a := by simp only [wq]; omega_arith
  simp only [S, kwW] at fit
  unfold topH
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine arrPtr_ok (lenSrc hr) hr.lenLe hr.edi (r := .esi) (t := .edx) (j := wR) (by decide) (by decide)
    (by rw [kwW]; omega_arith) fun u₁ U₁ m₁ p₁ _ => ?_
  rw [kwW] at p₁
  have hm₁ : MLen u₁ g.B g.Z nl a := hm.keep U₁ (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.WordRt.width4_ok hm₁ fun u₂ U₂ m₂ e₂ =>
    wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u₄ U₄ _ => wp_subS rfl fun u₅ U₅ _ => ?_
  have K₅ : Keeps opRegs s u₅ := (U₁.mono (by decide)).trans ((U₂.mono (by decide)).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, m₂, m₁]
  have e4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  have p₅ : PtrAt u₅ g.B .esi (arr g.W wR + 4 * (2 * wq a - 1)) := by
    have pp₂ : PtrAt u₂ g.B .esi (arr g.W wR) := by rw [PtrAt, U₂.1 _ (by decide)]; exact p₁
    rw [PtrAt, U₅.gpr, U₄.gpr, U₃.gpr, U₃.other _ (by decide), e₂, BitVec.toNat_sub,
      BitVec.toNat_add, BitVec.toNat_add, pp₂, e4]
    simp only [Nat.mul_one, BitVec.toNat_ofNat]
    have := g.B.isLt
    omega_arith
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr (h.rt.rt.of_keeps K₅) p₅ (d := 0) (by omega_arith))
    fun t U _ => WP.block_nil ?_
  have K : Keeps opRegs s t := K₅.trans (U.keeps.mono (by decide))
  refine ⟨h.of_rest K (fun x hx => hx) (by rw [U.mem, m₅]), K, ?_⟩
  rw [U.gpr, m₅, Nat.add_zero]

/-- A bit stage's test: `sStg` one where the top `b` bits of `X`'s word `H - 1` are zero, and `sZb += b`
there. -/
theorem stageXB_head {a b : Nat} {Q : State → Prop}
    (h : KS g s0 A [aD, aZero] AW [wR] V (VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN) s)
    (hm : MLen s g.B g.Z nl a) (ha0 : 1 ≤ a) (haw : wq a ≤ g.w) (hV : V VG.Impl.Rsa.X86.RecoverDetRt.sB = b)
    (hb0 : 0 < b) (hb : b < 32) (hx : AW wR < 2 ^ (64 * wq a)) (hZ : V sZb ≤ 1024)
    (k : ∀ t z, KS g s0 A [aD, aZero] AW [wR] (upd (upd V sStg z) sZb (V sZb + b * z))
      (sZb :: sStg :: VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN) t →
      z = (if AW wR < 2 ^ (64 * wq a - b) then 1 else 0) → WP isa (upBitsSelH sqZ) t Q) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs [
      .block (topH .esi sqZ 1 .edx ++ ([.mov .eax (.mem (at_ .esi 0))] : List Instr)), topTest,
      .block (flagZero ++ ([.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)),
        .alu .and .edx (.mem (sc VG.Impl.Rsa.X86.RecoverDetRt.sB)),
        .alu .add .edx (.mem (sc sZb)), .store (sc sZb) .edx] : List Instr)),
      upBitsSelH sqZ]) s Q := by
  have hle := hm.le
  have hwq : 1 ≤ wq a ∧ wq a ≤ 256 := by simp only [wq]; omega_arith
  have eW : g.W = 2 * g.w + 2 := rfl
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.readTop hm ha0 haw) fun t₁ ⟨h₁, K₁, e₁⟩ => ?_)
  -- The top bits zero: `X < 2^(32 H - b)`.
  have tw : w32 s.mem g.B (arr g.W wR + 4 * (2 * wq a - 1)) = AW wR / 2 ^ (32 * (2 * wq a - 1)) := by
    have e : g.W = (2 * wq a - 1) + 1 + (g.W - 2 * wq a) := by omega_arith
    have hx' := hx
    rw [← h.arrsW wR (by simp), num, e, show 64 * wq a = 32 * ((2 * wq a - 1) + 1) by omega_arith] at hx'
    rw [← h.arrsW wR (by simp), num, e]
    exact top_word hx'
  refine WP.seq (WP.mono (topTest_ok h₁.ws (b := b) (by rw [h₁.sl _ (by simp), hV]) hb0 hb)
    fun t₂ ⟨K₂, m₂, e₂⟩ => ?_)
  have h₂ := h₁.of_rest K₂ (by decide) m₂
  have top : t₂.gpr .ecx = 0 ↔ AW wR < 2 ^ (64 * wq a - b) := by
    have e : 64 * wq a - b = 32 * (2 * wq a - 1) + (32 - b) := by omega_arith
    rw [← toNat_eq_zero_iff, e₂, e₁, tw, Nat.div_div_eq_div_mul, e, Nat.pow_add]
    have p := Nat.two_pow_pos (32 - b)
    have q := Nat.two_pow_pos (32 * (2 * wq a - 1))
    constructor
    · intro z
      rcases Nat.mul_eq_zero.mp z with c | c
      · omega_arith
      · exact (Nat.div_eq_zero_iff.mp c).resolve_left (Nat.ne_of_gt (Nat.mul_pos q p))
    · intro lt
      rw [Nat.div_eq_of_lt lt, Nat.mul_zero]
  generalize hz : (if t₂.gpr .ecx = 0 then 1 else 0) = z
  have z1 : z ≤ 1 := by rw [← hz]; split <;> decide
  have zv : z = (if AW wR < 2 ^ (64 * wq a - b) then 1 else 0) := by
    rw [← hz]
    by_cases hlt : AW wR < 2 ^ (64 * wq a - b)
    · simp only [top.mpr hlt, hlt, ↓reduceIte]
    · simp only [show ¬ t₂.gpr .ecx = 0 from fun e => hlt (top.mp e), hlt, ↓reduceIte]
  refine WP.seq (WP.block_append (WP.mono h₂.flagZero fun t₃ ⟨h₃, K₃⟩ => ?_))
  rw [hz] at h₃
  refine wp_movS (v := 0) rfl fun u₁ U₁ _ => ?_
  have h₃₁ := h₃.of_rest U₁.keeps (by decide) U₁.mem
  have r₂ := h₃₁.readSlot (d := sStg) (by simp)
  rw [upd_self] at r₂
  refine wp_subS r₂ fun u₂ U₂ _ => ?_
  have h₃₂ := h₃₁.of_rest U₂.keeps (by decide) U₂.mem
  have rB := h₃₂.readSlot (d := VG.Impl.Rsa.X86.RecoverDetRt.sB) (by simp)
  rw [upd_ne _ _ (by decide), hV] at rB
  refine wp_logicS (.inl rfl) rB fun u₃ U₃ => ?_
  have h₃₃ := h₃₂.of_rest U₃.keeps (by decide) U₃.mem
  have rZ := h₃₃.readSlot (d := sZb) (by simp)
  rw [upd_ne _ _ (by decide)] at rZ
  refine wp_addS rZ fun u₄ U₄ _ => ?_
  have h₃₄ := h₃₃.of_rest U₄.keeps (by decide) U₄.mem
  refine WP.block_append (M := isa) (l₁ := ([.store (sc sZb) .edx] : List Instr))
    (WP.mono (h₃₄.storeSlot (d := sZb) (by decide) .edx) fun t₄ ⟨h₄, _, _⟩ => WP.block_nil ?_)
  have v₄ : (u₄.gpr .edx).toNat = V sZb + b * z := by
    rw [U₄.gpr, U₃.gpr, show ∀ x y : BitVec 32, (if AluOp.and = AluOp.and then x &&& y else x ^^^ y) = x &&& y
      from fun _ _ => rfl, U₂.gpr, U₁.gpr]
    exact mask_and_add z b (V sZb) z1 (by omega_arith) (by omega_arith)
  rw [v₄] at h₄
  exact k t₄ z h₄ zv

/-- A bit stage's shift: `X` up by `b` bits into `wT`, and selected where `sStg`. -/
theorem stageXB_tail {a b z : Nat} {V₀ : Nat → Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] (upd (upd V₀ sStg z) sZb (V₀ sZb + b * z))
      (sZb :: sStg :: VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN) s)
    (hV : V₀ VG.Impl.Rsa.X86.RecoverDetRt.sB = b) (hb0 : 0 < b) (hb : b < 32) (haw : wq a ≤ g.w)
    (hle : a ≤ 1024) (z1 : z ≤ 1) (hzx : z = 1 → AW wR < 2 ^ (64 * wq a - b)) :
    WP isa (upBitsSelH sqZ) s fun t => ∃ AW' V',
      KS g s0 A [aD, aZero] AW' [wR] V' (VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN) t ∧
      (∀ d ∈ VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN, d ≠ sZb → V' d = V₀ d) ∧
      V' sZb = V₀ sZb + b * z ∧ AW' wR = (if z = 1 then AW wR * 2 ^ b else AW wR) := by
  have hwq : wq a ≤ 256 := by simp only [wq]; omega_arith
  have eW : g.W = 2 * g.w + 2 := rfl
  unfold upBitsSelH
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.copy_W (o := VG.Impl.Rsa.X86.RecoverDetRt.wT) (a := wR) (by decide) (by simp)
    (by decide) (by decide)) fun t₅ ⟨h₅, _⟩ => ?_)
  refine WP.seq (WP.mono (h₅.doubles (b := b) (by simp) (by simp)
    (by simp only [upd, show VG.Impl.Rsa.X86.RecoverDetRt.sB ≠ sZb by decide,
      show VG.Impl.Rsa.X86.RecoverDetRt.sB ≠ sStg by decide, ↓reduceIte]; exact hV) hb0 (by omega_arith) (by decide))
    fun t₆ ⟨V₆, h₆, hV₆⟩ => ?_)
  have s₆ : V₆ sStg = z := by rw [hV₆ _ (by simp) (by decide)]; simp [upd, sStg, sZb]
  refine WP.mono (h₆.sel_W (o := wR) (a := wR) (b := VG.Impl.Rsa.X86.RecoverDetRt.wT) (sl := sStg) (by decide)
    (by simp) (by simp) (by simp) (by rw [s₆]; exact z1) (.inr (by decide)) (by decide)) fun t ⟨ht, _⟩ => ?_
  refine ⟨_, _, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; exact .inl hj, rfl⟩)
    (fun d hd => ⟨mem_of_sub (by decide) hd, rfl⟩), ?_, ?_, ?_⟩
  · intro d hd hne
    have hd' : d ∈ sZb :: sStg :: VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN := List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hd)
    rw [hV₆ d hd' (fun e => absurd (e ▸ hd) (by decide)), upd_ne _ _ hne,
      upd_ne _ _ (fun e => absurd (e ▸ hd) (by decide))]
  · rw [hV₆ _ (by simp) (by decide), upd_self]
  · rw [s₆]
    rcases (show z = 0 ∨ z = 1 by omega_arith) with rfl | rfl
    · simp only [upd, show wR ≠ VG.Impl.Rsa.X86.RecoverDetRt.wT by decide, ↓reduceIte, Nat.zero_ne_one]
    · have hlt := hzx rfl
      have h1 : AW wR * 2 ^ b < 2 ^ (64 * wq a - b) * 2 ^ b := Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
      have h2 : 2 ^ (64 * wq a - b) * 2 ^ b ≤ 2 ^ (32 * g.W) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (show 64 * wq a - b + b ≤ 32 * g.W by rw [eW]; omega_arith)
      have h3 : AW wR * 2 ^ b < 2 ^ (32 * g.W) := Nat.lt_of_lt_of_le h1 h2
      simp only [upd, ↓reduceIte, Nat.one_ne_zero, Nat.mod_eq_of_lt h3]

end

/-! ## The stages -/

theorem pow_lt_of_mul {x e f : Nat} (hx : 1 ≤ x) (h : x * 2 ^ e < 2 ^ f) : e < f := by
  have : 2 ^ e < 2 ^ f := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hx) h
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp this

section
variable {g : Geo} {s0 : State} {A V : Nat → Nat}

/-- Before (`e = 2^(j + 1)`) or after (`e = 2^j`) word stage `2^j`: `X₁ = X + zf` up by `sKw`
words, its top `e - 1` of `H` words not all zero. -/
def WSt (g : Geo) (s0 : State) (A V : Nat → Nat) (X a zf e c4 : Nat) (t : State) : Prop :=
  ∃ AW' V', KS g s0 A [aD, aZero] AW' [wR] V' (sC4 :: lsN) t ∧ (∀ d ∈ sqSlotsW, V' d = V d) ∧
    V' sZf = zf ∧ V' sZb = 0 ∧ V' sC4 = c4 ∧ AW' wR = (X + zf) * 2 ^ (32 * V' sKw) ∧
    AW' wR < 2 ^ (64 * wq a) ∧ 2 ^ (32 * (2 * wq a - e)) ≤ AW' wR

theorem wordStage_ok {a X zf j : Nat} (ha : g.args nl = BitVec.ofNat 32 a) (hal : a ≤ 1024)
    (haw : wq a ≤ g.w) (hzf : 1 ≤ X + zf) (hj : 2 ^ j < 2 * wq a) {t : State}
    (P : WSt g s0 A V X a zf (2 ^ (j + 1)) (4 * 2 ^ j) t) :
    WP isa stageXWH t (WSt g s0 A V X a zf (2 ^ j) (4 * 2 ^ j)) := by
  obtain ⟨AW', V', ht, hsq, hz, hzb, hC, hv, hlt, hge⟩ := P
  have hwq : wq a ≤ 256 := by simp only [wq]; omega_arith
  have Kb : V' sKw ≤ 1024 := by
    have := pow_lt_of_mul hzf (hv ▸ hlt); omega_arith
  refine WP.mono (stageXW_ok ht (ht.mlen ha hal) haw hC (Nat.two_pow_pos j) hj hlt Kb)
    fun u ⟨AW'', V'', hu, hV, hif⟩ => ⟨AW'', V'', hu, fun d hd => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV d (mem_of_sub (by decide) hd) (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [hV _ (by simp) (by decide), hz]
  · rw [hV _ (by simp) (by decide), hzb]
  · rw [hV _ (by simp) (by decide), hC]
  · have p := Nat.two_pow_pos (32 * (2 * wq a - 2 ^ j))
    have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega_arith
    rw [e2] at hge
    split at hif
    · rename_i hl
      obtain ⟨e1, e2⟩ := hif
      refine ⟨by rw [e1, e2, hv, Nat.mul_assoc, ← Nat.pow_add, Nat.mul_add], ?_, ?_⟩
      · rw [e1]
        calc AW' wR * 2 ^ (32 * 2 ^ j) < 2 ^ (32 * (2 * wq a - 2 ^ j)) * 2 ^ (32 * 2 ^ j) :=
              Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos _)
          _ = 2 ^ (64 * wq a) := by rw [← Nat.pow_add]; congr 1; omega_arith
      · rw [e1]
        calc 2 ^ (32 * (2 * wq a - 2 ^ j)) ≤ 2 ^ (32 * (2 * wq a - 2 * 2 ^ j) + 32 * 2 ^ j) :=
              Nat.pow_le_pow_right (by decide) (by omega_arith)
          _ = 2 ^ (32 * (2 * wq a - 2 * 2 ^ j)) * 2 ^ (32 * 2 ^ j) := Nat.pow_add _ _ _
          _ ≤ AW' wR * 2 ^ (32 * 2 ^ j) := Nat.mul_le_mul_right _ hge
    · rename_i hl
      obtain ⟨e1, e2⟩ := hif
      exact ⟨by rw [e1, e2, hv], by rw [e1]; exact hlt, by rw [e1]; omega_arith⟩

/-- Before (`e = 2^(j + 1)`) or after (`e = 2^j`) bit stage `2^j`: `X₁` up by `sKw` words and
`sZb` bits, the top `e - 1` bits of its word `H - 1` not all zero. -/
def BSt (g : Geo) (s0 : State) (A V : Nat → Nat) (X a zf e bv : Nat) (t : State) : Prop :=
  ∃ AW' V', KS g s0 A [aD, aZero] AW' [wR] V' (VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN) t ∧
    (∀ d ∈ sqSlotsW, V' d = V d) ∧ V' sZf = zf ∧ V' VG.Impl.Rsa.X86.RecoverDetRt.sB = bv ∧
    AW' wR = (X + zf) * 2 ^ (32 * V' sKw + V' sZb) ∧ AW' wR < 2 ^ (64 * wq a) ∧
    2 ^ (64 * wq a - e) ≤ AW' wR ∧ V' sZb % 2 = 0 ∧ V' sZb + e ≤ 32

theorem bitStage_ok {a X zf j : Nat} (ha : g.args nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (ha0 : 1 ≤ a)
    (haw : wq a ≤ g.w) (hj1 : 1 ≤ j) (hj : j ≤ 4) {t : State}
    (P : BSt g s0 A V X a zf (2 ^ (j + 1)) (2 ^ j) t) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs [
      .block (topH .esi sqZ 1 .edx ++ ([.mov .eax (.mem (at_ .esi 0))] : List Instr)), topTest,
      .block (flagZero ++ ([.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)),
        .alu .and .edx (.mem (sc VG.Impl.Rsa.X86.RecoverDetRt.sB)),
        .alu .add .edx (.mem (sc sZb)), .store (sc sZb) .edx] : List Instr)),
      upBitsSelH sqZ]) t (BSt g s0 A V X a zf (2 ^ j) (2 ^ j)) := by
  obtain ⟨AW', V', ht, hsq, hz, hB, hv, hlt, hge, hev, hzb⟩ := P
  have hwq : 1 ≤ wq a ∧ wq a ≤ 256 := by simp only [wq]; omega_arith
  have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega_arith
  have b2 : 2 ≤ 2 ^ j := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hj1; simpa using this
  have b16 : 2 ^ j ≤ 16 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hj; simpa using this
  have bev : 2 ^ j % 2 = 0 := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
    rw [Nat.pow_succ]; omega_arith
  rw [e2] at hge hzb
  refine stageXB_head ht (ht.mlen ha hal) ha0 haw hB (by omega_arith) (by omega_arith) hlt (by omega_arith) fun u z hu hzv => ?_
  have z1 : z ≤ 1 := by rw [hzv]; split <;> omega_arith
  refine WP.mono (stageXB_tail (a := a) hu hB (by omega_arith) (by omega_arith) haw hal z1
    (fun e => by rw [e] at hzv; split at hzv <;> first | with_reducible assumption | omega_arith)) fun v ⟨AW'', V'', hv', hV, hZ, hW⟩ => ?_
  have k : ∀ d ∈ VG.Impl.Rsa.X86.RecoverDetRt.sB :: lsN, d ≠ sZb → V'' d = V' d := hV
  refine ⟨AW'', V'', hv', fun d hd => ?_, ?_, ?_, ?_⟩
  · rw [k d (mem_of_sub (by decide) hd) (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [k _ (by simp) (by decide), hz]
  · rw [k _ (by simp) (by decide), hB]
  · have hK : V'' sKw = V' sKw := k _ (by simp) (by decide)
    rw [hZ, hK]
    by_cases hl : AW' wR < 2 ^ (64 * wq a - 2 ^ j)
    · have zz : z = 1 := by rw [hzv]; simp only [hl, ↓reduceIte]
      subst zz
      simp only [↓reduceIte] at hW
      rw [hW]
      refine ⟨by rw [hv, Nat.mul_assoc, ← Nat.pow_add, Nat.mul_one, Nat.add_assoc], ?_, ?_, by omega_arith, by omega_arith⟩
      · calc AW' wR * 2 ^ 2 ^ j < 2 ^ (64 * wq a - 2 ^ j) * 2 ^ 2 ^ j :=
              Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos _)
          _ = 2 ^ (64 * wq a) := by rw [← Nat.pow_add]; congr 1; omega_arith
      · calc 2 ^ (64 * wq a - 2 ^ j) = 2 ^ (64 * wq a - 2 * 2 ^ j) * 2 ^ 2 ^ j := by
              rw [← Nat.pow_add]; congr 1; omega_arith
          _ ≤ AW' wR * 2 ^ 2 ^ j := Nat.mul_le_mul_right _ hge
    · have zz : z = 0 := by rw [hzv]; simp only [hl, ↓reduceIte]
      subst zz
      simp only [Nat.zero_ne_one, ↓reduceIte] at hW
      rw [hW]
      exact ⟨by rw [hv, Nat.mul_zero, Nat.add_zero], hlt, by omega_arith, by omega_arith, by omega_arith⟩

theorem WSt.reslot {X a zf e c4 c4' : Nat} {t u : State} (P : WSt g s0 A V X a zf e c4 t)
    (k : Keep g.B g.w [] [sC4] t.mem u.mem) (hs : slot u.mem g.B sC4 = c4') (K : Keeps opRegs t u) :
    WSt g s0 A V X a zf e c4' u := by
  obtain ⟨AW', V', ht, hsq, hz, hzb, _, hv, hlt, hge⟩ := P
  have hu := ht.slot1 k (by decide) K hs
  refine ⟨AW', upd V' sC4 c4', hu.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), fun d hd => ?_, ?_, ?_, upd_self _ _ _, ?_, hlt, hge⟩
  · rw [upd_ne _ _ (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [upd_ne _ _ (by decide), hz]
  · rw [upd_ne _ _ (by decide), hzb]
  · rw [upd_ne _ _ (show sKw ≠ sC4 by decide)]; exact hv

theorem BSt.reslot {X a zf e bv bv' : Nat} {t u : State} (P : BSt g s0 A V X a zf e bv t)
    (k : Keep g.B g.w [] [VG.Impl.Rsa.X86.RecoverDetRt.sB] t.mem u.mem)
    (hs : slot u.mem g.B VG.Impl.Rsa.X86.RecoverDetRt.sB = bv') (K : Keeps opRegs t u) :
    BSt g s0 A V X a zf e bv' u := by
  obtain ⟨AW', V', ht, hsq, hz, _, hv, hlt, hge, hev, hzb⟩ := P
  have hu := ht.slot1 k (by decide) K hs
  refine ⟨AW', upd V' VG.Impl.Rsa.X86.RecoverDetRt.sB bv', hu.mono (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), fun d hd => ?_, ?_, upd_self _ _ _,
    ?_, hlt, hge, ?_, ?_⟩
  · rw [upd_ne _ _ (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [upd_ne _ _ (by decide), hz]
  · rw [upd_ne _ _ (show sKw ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide),
      upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide)]; exact hv
  · rw [upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide)]; exact hev
  · rw [upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide)]; exact hzb

/-- The word stages' start, from `zeroX`. -/
theorem wst_init {X a zf e c4 : Nat} {AW₂ V₂ : Nat → Nat} {t u : State}
    (h : KS g s0 A [aD, aZero] AW₂ [wR] V₂ lsN t) (hsq : ∀ d ∈ sqSlotsW, V₂ d = V d) (hz : V₂ sZf = zf)
    (hK : V₂ sKw = 0) (hZ : V₂ sZb = 0) (hv : AW₂ wR = X + zf) (hlt : X + zf < 2 ^ (64 * wq a))
    (hge : 2 ^ (32 * (2 * wq a - e)) ≤ X + zf)
    (k : Keep g.B g.w [] [sC4] t.mem u.mem) (hs : slot u.mem g.B sC4 = c4) (K : Keeps opRegs t u) :
    WSt g s0 A V X a zf e c4 u := by
  have hu := h.slot1 k (by decide) K hs
  refine ⟨AW₂, upd V₂ sC4 c4, hu, fun d hd => ?_, ?_, ?_, upd_self _ _ _, ?_, by rw [hv]; exact hlt,
    by rw [hv]; exact hge⟩
  · rw [upd_ne _ _ (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [upd_ne _ _ (by decide), hz]
  · rw [upd_ne _ _ (by decide), hZ]
  · rw [upd_ne _ _ (show sKw ≠ sC4 by decide), hK, hv, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]

/-- The bit stages' start, from the word stages. -/
theorem bst_init {X a zf bv : Nat} {t u : State} (hwq : 1 ≤ wq a) (P : WSt g s0 A V X a zf 1 2 t)
    (k : Keep g.B g.w [] [VG.Impl.Rsa.X86.RecoverDetRt.sB] t.mem u.mem)
    (hs : slot u.mem g.B VG.Impl.Rsa.X86.RecoverDetRt.sB = bv) (K : Keeps opRegs t u) :
    BSt g s0 A V X a zf 32 bv u := by
  obtain ⟨AW', V', ht, hsq, hz, hzb, _, hv, hlt, hge⟩ := P
  have hu := ht.slot1 k (by decide) K hs
  refine ⟨AW', upd V' VG.Impl.Rsa.X86.RecoverDetRt.sB bv, hu.mono (fun j hj => ⟨hj, rfl⟩)
    (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨mem_of_sub (by decide) hd, rfl⟩), fun d hd => ?_, ?_, upd_self _ _ _,
    ?_, hlt, ?_, ?_, ?_⟩
  · rw [upd_ne _ _ (fun e => absurd (e ▸ hd) (by decide)), hsq d hd]
  · rw [upd_ne _ _ (by decide), hz]
  · rw [upd_ne _ _ (show sKw ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide),
      upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide), hzb, Nat.add_zero]; exact hv
  · rw [show 64 * wq a - 32 = 32 * (2 * wq a - 1) by omega_arith]; exact hge
  · rw [upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide), hzb]
  · rw [upd_ne _ _ (show sZb ≠ VG.Impl.Rsa.X86.RecoverDetRt.sB by decide), hzb]

/-- The word stages `c = 256, …, 1`. -/
theorem wordStages_all {X a zf : Nat} {AW₂ V₂ : Nat → Nat} {t : State}
    (ha : g.args nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (haw : wq a ≤ g.w)
    (h : KS g s0 A [aD, aZero] AW₂ [wR] V₂ lsN t) (hsq : ∀ d ∈ sqSlotsW, V₂ d = V d) (hz : V₂ sZf = zf)
    (hK : V₂ sKw = 0) (hZ : V₂ sZb = 0) (hv : AW₂ wR = X + zf) (hlt : X + zf < 2 ^ (64 * wq a))
    (h1 : 1 ≤ X + zf) :
    WP isa (wordStagesL 256 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax ++ ([.alu .add .eax (.reg .eax)] : List Instr)) stageXWH) t
      (WSt g s0 A V X a zf 1 2) := by
  have hwq : wq a ≤ 256 := by simp only [wq]; omega_arith
  refine wordStagesL_ok (k := 8) (lim := 8 * wq a) (Fin := WSt g s0 A V X a zf 1 2)
    (fun j => WSt g s0 A V X a zf (2 ^ (j + 1)) (4 * 2 ^ j)) (fun j => WSt g s0 A V X a zf (2 ^ j) (4 * 2 ^ j))
    (by decide) h.ws ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u k hs K
    refine wst_init h hsq hz hK hZ hv hlt ?_ k hs (K.mono (by decide))
    rw [show 2 * wq a - 2 ^ (8 + 1) = 0 by omega_arith, Nat.mul_zero, Nat.pow_zero]; exact h1
  · rintro j u - ⟨AW', V', hu, -, -, -, hC, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hC]⟩
  · rintro j u - ⟨AW', V', hu, -⟩ is Q k
    rw [List.append_assoc]
    refine VG.Proof.Rsa.X86.WordRt.width4_ok (hu.mlen ha hal) fun v U m e => wp_addS rfl fun w W _ => ?_
    refine k w ((U.mono (by decide)).trans (W.keeps.mono (by decide))) (by rw [W.mem, m]) ?_
    rw [W.gpr, e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rintro j u v - ⟨AW', V', hu, r⟩ K m
    exact ⟨AW', V', hu.of_rest K (fun x hx => hx) m, r⟩
  · intro j u _ P hj
    exact wordStage_ok ha hal haw h1 (by omega_arith) P
  · rintro j u _ ⟨AW', V', hu, hsq', hz', hzb', hC, hv', hlt', -⟩ hj
    refine ⟨AW', V', hu, hsq', hz', hzb', hC, hv', hlt', ?_⟩
    rw [show 2 * wq a - 2 ^ j = 0 by omega_arith, Nat.mul_zero, Nat.pow_zero]
    rw [hv']; exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  · rintro j u - ⟨AW', V', hu, -, -, -, hC, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hC]⟩
  · intro j u v _ P k hs K
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have P' := P.reslot k hs K
      have e : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega_arith
      rw [show j - 1 + 1 = j by omega_arith, show 4 * 2 ^ (j - 1) = 2 * 2 ^ j by omega_arith]
      exact P'
    · subst hj
      exact P.reslot k hs K

/-- The bit stages `b = 16, …, 2`. -/
theorem bitStages_all {X a zf : Nat} {t : State} (ha : g.args nl = BitVec.ofNat 32 a) (hal : a ≤ 1024)
    (ha0 : 1 ≤ a) (haw : wq a ≤ g.w) (P : WSt g s0 A V X a zf 1 2 t) :
    WP isa (bitStagesL 16 2 (VG.Impl.Rsa.X86.Keys.seqs [
      .block (topH .esi sqZ 1 .edx ++ ([.mov .eax (.mem (at_ .esi 0))] : List Instr)), topTest,
      .block (flagZero ++ ([.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)),
        .alu .and .edx (.mem (sc VG.Impl.Rsa.X86.RecoverDetRt.sB)),
        .alu .add .edx (.mem (sc sZb)), .store (sc sZb) .edx] : List Instr)),
      upBitsSelH sqZ])) t (BSt g s0 A V X a zf 2 1) := by
  have hwq : 1 ≤ wq a := by simp only [wq]; omega_arith
  have hs : Ws t g.B g.Z g.w VG.Impl.Rsa.X86.Recover.nArr := by obtain ⟨_, _, ht, -⟩ := P; exact ht.ws
  refine bitStagesL_ok (k := 4) (m := 1) (Fin := BSt g s0 A V X a zf 2 1)
    (fun j => BSt g s0 A V X a zf (2 ^ (j + 1)) (2 ^ j)) (fun j => BSt g s0 A V X a zf (2 ^ j) (2 ^ j))
    (by decide) (by decide) hs ?_ ?_ ?_ ?_
  · intro u k e K
    exact bst_init hwq P k e (K.mono (by decide))
  · intro j u hm hj Q
    exact bitStage_ok ha hal ha0 haw hm hj Q
  · rintro j u - - ⟨AW', V', hu, -, -, hB, -⟩
    exact ⟨hu.ws, by rw [hu.sl _ (by simp), hB]⟩
  · intro j u v _ _ Q k e K
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have Q' := Q.reslot k e K
      have e2 : 2 ^ j = 2 * 2 ^ (j - 1) := by rw [← Nat.pow_succ']; congr 1; omega_arith
      rw [show j - 1 + 1 = j by omega_arith, show 2 ^ (j - 1) = 2 ^ j / 2 by omega_arith]
      exact Q'
    · subst hj
      exact Q.reslot k e K

end

/-- `normX`: the radicand `X < 2^(32 H)` in `wR`, `X = 0` made one, normalized to
`(X + [X = 0]) 4^(16 K + z / 2)` with its word `H - 1` at least `2^30`, `K` (`sKw`) the words and `z`
(`sZb`) the bits it was shifted by. -/
theorem normX_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {X a : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] V sqSlotsW u) (hX : AW wR = X)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (ha0 : 1 ≤ a)
    (haw : wq a ≤ g.w) :
    WP isa normX u fun v => ∃ AW' V', KS g s0 A [aD, aZero] AW' [wR] V' lsN v ∧
      (∀ d ∈ sqSlotsW, V' d = V d) ∧ V' sZf = (if X % 2 ^ (64 * wq a) = 0 then 1 else 0) ∧
      AW' wR = (X % 2 ^ (64 * wq a) + V' sZf) * 4 ^ (16 * V' sKw + V' sZb / 2) ∧
      AW' wR < 2 ^ (64 * wq a) ∧ 2 ^ 30 * 2 ^ (64 * wq a - 32) ≤ AW' wR ∧
      V' sKw < 2 * wq a ∧ V' sZb % 2 = 0 ∧ V' sZb ≤ 30 := by
  have hm := h.mlen ha hal
  have hwq : 1 ≤ wq a ∧ wq a ≤ 256 := by simp only [wq]; omega_arith
  unfold normX
  refine WP.seq (WP.mono (h.clearAbove_ok (by simp) hm haw (by decide)) fun u₁ h₁ => ?_)
  have hXa : X % 2 ^ (64 * wq a) < 2 ^ (64 * wq a) := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize hX' : X % 2 ^ (64 * wq a) = X' at hXa ⊢
  refine WP.seq (WP.mono (zeroX_ok h₁ (X := X') (by rw [upd_self, hX, hX'])) fun u₂ ⟨AW₂, V₂, h₂, hsq₂, hz₂, hK₂, hZ₂, hv₂⟩ => ?_)
  have h1 : 1 ≤ X' + V₂ sZf := by rw [hz₂]; split <;> omega_arith
  have hlt : X' + V₂ sZf < 2 ^ (64 * wq a) := by
    rw [hz₂]
    split
    · rename_i e; subst e; exact Nat.one_lt_two_pow (by omega_arith)
    · omega_arith
  refine WP.seq (WP.mono (wordStages_all ha hal haw h₂ hsq₂ rfl hK₂ hZ₂ hv₂ hlt h1) fun u₃ P => ?_)
  refine WP.mono (bitStages_all ha hal ha0 haw P) fun v ⟨AW', V', hv, hsq, hz, _, hval, hlt', hge, hev, hzb⟩ => ?_
  have hK := pow_lt_of_mul h1 (hval ▸ hlt')
  refine ⟨AW', V', hv.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩), hsq, by rw [hz, hz₂], ?_, hlt', ?_, by omega_arith, hev, by omega_arith⟩
  · rw [hval, hz, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
    congr 2
    omega_arith
  · rw [← Nat.pow_add, show 30 + (64 * wq a - 32) = 64 * wq a - 2 by omega_arith]
    exact hge

end VG.Proof.Rsa.X86.Recover
