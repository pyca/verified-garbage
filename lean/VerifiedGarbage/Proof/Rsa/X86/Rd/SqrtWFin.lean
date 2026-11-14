module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.SqrtRem
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the square root's last piece, which only `SqrtW` composes with the others

/-! # The square root by words on i686: the root shifted back

`RecoverDetRt.finishX`: whether the remainder is zero (`sOk5`), the root `D / 2` shifted down
by the normalization's `16 K + z / 2` bits (words by `K / 2`'s bits, then bits), less one where
the radicand was zero, into the narrow `aY` (`finishX_ok`).
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
open VG.Spec.Rsa (isqrt)
open VG.Impl.Rsa.X86.RecoverDetRt (timesH sBc wordStagesL bitStagesL moveH downBitsSelH)

local notation "sBh" => VG.Impl.Rsa.X86.RecoverDetRt.sB

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- `sStg := [eax ≠ 0]`. -/
theorem KS.flagNZ (h : KS g s0 A live AW liveW V ls s) :
    WP isa (.block [.alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc sStg) .eax]) s fun t =>
      KS g s0 A live AW liveW (upd V sStg (if (s.gpr .eax).toNat = 0 then 0 else 1)) (sStg :: ls) t ∧
      Keeps opRegs s t := by
  refine wp_cmpi fun s₁ F₁ c₁ _ => wp_sbb_self c₁ fun s₂ U₂ => wp_addS rfl fun s₃ U₃ _ => ?_
  have K₃ : Keeps [.eax] s s₃ := (fupd_keeps F₁ _).trans (U₂.keeps.trans U₃.keeps)
  have h₃ := h.of_rest K₃ (by decide) (by rw [U₃.mem, U₂.mem, F₁.mem])
  refine WP.mono (h₃.storeSlot (by decide) .eax) fun t ⟨ht, _, kt⟩ => ⟨?_, (K₃.mono (by decide)).trans (kt.mono (by decide))⟩
  have e : (s₃.gpr .eax).toNat = if (s.gpr .eax).toNat = 0 then 0 else 1 := by
    rw [U₃.gpr, U₂.gpr]
    by_cases z : (s.gpr .eax).toNat = 0
    · simp only [z, show (1 : BitVec 32).toNat = 1 from rfl, Nat.zero_lt_one, decide_true, ite_true]; rfl
    · simp only [z, show (1 : BitVec 32).toNat = 1 from rfl, show ¬ (s.gpr .eax).toNat < 1 by omega_using [z],
        decide_false, ite_false, Bool.false_eq_true]; rfl
  rw [e] at ht
  exact ht

theorem toNat_ofNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A word stage's flag: `sStg := [⌊K / 2⌋ ∧ c ≠ 0]` (`K` in `sKw`, `4 c` in `sC4`). -/
theorem KS.wordFlag (h : KS g s0 A live AW liveW V ls s) (hK : sKw ∈ ls) (hC : sC4 ∈ ls)
    (hK32 : V sKw < 2 ^ 32) (hC32 : V sC4 < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sKw)), .shift .shr .eax 1,
      .mov .edx (.mem (VG.Impl.Mont.X86.sc sC4)), .shift .shr .edx 2, .alu .and .eax (.reg .edx),
      .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc sStg) .eax]) s fun t =>
      KS g s0 A live AW liveW (upd V sStg (if V sKw / 2 &&& V sC4 / 4 = 0 then 0 else 1)) (sStg :: ls) t ∧
      Keeps opRegs s t := by
  refine wp_movS (h.readSlot hK) fun s₁ U₁ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₂ U₂ => ?_
  have h₂ := h.of_rest (U₁.keeps.trans U₂.keeps) (by decide) (by rw [U₂.mem, U₁.mem])
  refine wp_movS (h₂.readSlot hC) fun s₃ U₃ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₄ U₄ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₅ U₅ => ?_
  have K₅ : Keeps [.eax, .edx] s s₅ := ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
    ((U₃.keeps.mono (by decide)).trans ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))
  have h₅ := h.of_rest K₅ (by decide) (by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem])
  refine WP.mono h₅.flagNZ fun t ⟨ht, kt⟩ => ⟨?_, (K₅.mono (by decide)).trans kt⟩
  have e : (s₅.gpr .eax).toNat = V sKw / 2 &&& V sC4 / 4 := by
    rw [U₅.gpr, ite_eq_left rfl, U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr, U₁.gpr, U₄.gpr, U₃.gpr,
      BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, toNat_ofNat32 hK32,
      toNat_ofNat32 hC32, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [e] at ht
  exact ht

/-- A bit stage's flag: `sStg := [z ∧ b ≠ 0]` (`z` in `sZb`, `b` in `sB`). -/
theorem KS.bitFlag (h : KS g s0 A live AW liveW V ls s) (hZ : sZb ∈ ls) (hB : sBh ∈ ls)
    (hZ32 : V sZb < 2 ^ 32) (hB32 : V sBh < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sZb)), .alu .and .eax (.mem (VG.Impl.Mont.X86.sc sBh)),
      .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
      .store (VG.Impl.Mont.X86.sc sStg) .eax]) s fun t =>
      KS g s0 A live AW liveW (upd V sStg (if V sZb &&& V sBh = 0 then 0 else 1)) (sStg :: ls) t ∧
      Keeps opRegs s t := by
  refine wp_movS (h.readSlot hZ) fun s₁ U₁ _ => ?_
  have h₁ := h.of_rest U₁.keeps (by decide) U₁.mem
  refine wp_logicS (.inl rfl) (h₁.readSlot hB) fun s₂ U₂ => ?_
  have K₂ : Keeps [.eax] s s₂ := U₁.keeps.trans U₂.keeps
  have h₂ := h.of_rest K₂ (by decide) (by rw [U₂.mem, U₁.mem])
  refine WP.mono h₂.flagNZ fun t ⟨ht, kt⟩ => ⟨?_, (K₂.mono (by decide)).trans kt⟩
  have e : (s₂.gpr .eax).toNat = V sZb &&& V sBh := by
    rw [U₂.gpr, ite_eq_left rfl, U₁.gpr, BitVec.toNat_and, toNat_ofNat32 hZ32, toNat_ofNat32 hB32]
  rw [e] at ht
  exact ht

end

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem upd_upd_ne (f : Nat → Nat) {a b : Nat} (h : a ≠ b) {x y : Nat} : upd (upd f a x) b y a = x := by
  simp only [upd, h, ↓reduceIte]

/-- `sZb := 16 (K mod 2) + ⌊z / 2⌋` (`K` in `sKw`, `z` in `sZb`). -/
theorem KS.zbBlock (h : KS g s0 A live AW liveW V ls s) (hK : sKw ∈ ls) (hZ : sZb ∈ ls)
    (hK32 : V sKw < 2 ^ 32) (hZ32 : V sZb < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sKw)), .alu .and .eax (.imm 1),
      .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
      .alu .add .eax (.reg .eax), .mov .edx (.mem (VG.Impl.Mont.X86.sc sZb)), .shift .shr .edx 1,
      .alu .add .eax (.reg .edx), .store (VG.Impl.Mont.X86.sc sZb) .eax]) s fun t =>
      KS g s0 A live AW liveW (upd V sZb (16 * (V sKw % 2) + V sZb / 2)) (sZb :: ls) t := by
  refine wp_movS (h.readSlot hK) fun s₁ U₁ _ => wp_logicS (.inl rfl) rfl fun s₂ U₂ => ?_
  refine wp_addS rfl fun s₃ U₃ _ => wp_addS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ =>
    wp_addS rfl fun s₆ U₆ _ => ?_
  have K₆ : Keeps [.eax] s s₆ := U₁.keeps.trans (U₂.keeps.trans (U₃.keeps.trans (U₄.keeps.trans
    (U₅.keeps.trans U₆.keeps))))
  have h₆ := h.of_rest K₆ (by decide) (by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem])
  refine wp_movS (h₆.readSlot hZ) fun s₇ U₇ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide)
    fun s₈ U₈ => wp_addS rfl fun s₉ U₉ _ => ?_
  have K₉ : Keeps [.eax, .edx] s s₉ := (K₆.mono (by decide)).trans ((U₇.keeps.mono (by decide)).trans
    ((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide))))
  have h₉ := h.of_rest K₉ (by decide) (by rw [U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem])
  refine WP.mono (h₉.storeSlot (by decide) .eax) fun t ⟨ht, _, _⟩ => ?_
  have e₂ : (s₂.gpr .eax).toNat = V sKw % 2 := by
    rw [U₂.gpr, ite_eq_left rfl, U₁.gpr, BitVec.toNat_and, toNat_ofNat32 hK32,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  have l2 : V sKw % 2 < 2 := Nat.mod_lt _ (by decide)
  have e₆ : (s₆.gpr .eax).toNat = 16 * (V sKw % 2) := by
    rw [U₆.gpr, U₅.gpr, U₄.gpr, U₃.gpr]
    simp only [BitVec.toNat_add, e₂]
    omega_using []
  have e₈ : (s₈.gpr .edx).toNat = V sZb / 2 := by
    rw [U₈.gpr, BitVec.toNat_ushiftRight, U₇.gpr, toNat_ofNat32 hZ32, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have e₉ : (s₉.gpr .eax).toNat = 16 * (V sKw % 2) + V sZb / 2 := by
    rw [U₉.gpr, BitVec.toNat_add, U₈.other _ (by decide), U₇.other _ (by decide), e₆, e₈]
    omega_using [hZ32]
  rw [e₉] at ht
  exact ht

/-- `body` of `timesH`'s halvings of the wide `wT`, `b` times (`b` in `sB`). -/
theorem KS.timesHalf {b : Nat} (h : KS g s0 A live AW liveW V ls s) (hw : wT ∈ liveW)
    (hl : ∀ i ∈ live, i / 2 ≠ wT) (hb : 0 < b) (hb32 : b < 2 ^ 32) (hB : sBh ∈ ls) (hV : V sBh = b)
    (hBc : sBc ∉ ls) :
    WP isa (timesH (.seq (.block [.mov .ebx (.imm 0)]) (VG.Impl.Rsa.X86.KeyRt.half wid wT))) s fun t =>
      ∃ V', KS g s0 A live (upd AW wT (AW wT / 2 ^ b)) liveW V' (sBc :: ls) t ∧ ∀ d ∈ ls, V' d = V d := by
  have agree : ∀ (V' : Nat → Nat) (x : Nat), (∀ d ∈ ls, V' d = V d) → ∀ d ∈ ls, upd V' sBc x d = V d :=
    fun V' x hV' d hd => by
      rw [upd_ne _ _ (fun e => hBc (by rw [← e]; exact hd)), hV' d hd]
  refine timesH_ok (b := b)
    (fun i t => ∃ V', KS g s0 A live (upd AW wT (AW wT / 2 ^ i)) liveW V' (sBc :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sBc = b - i)
    (fun i t => ∃ V', KS g s0 A live (upd AW wT (AW wT / 2 ^ (i + 1))) liveW V' (sBc :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sBc = b - i)
    hb hb32 h.ws (by rw [h.sl _ hB, hV]) ?_ ?_ ?_ ?_
  · intro t k e r
    refine ⟨upd V sBc b, (h.slot1 k (by decide) (r.mono (by decide)) e).mono
      (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩),
      agree V b (fun _ _ => rfl), by rw [upd_self, Nat.sub_zero]⟩
    · rfl
    · by_cases e : j = wT
      · subst e; rw [upd_self, Nat.pow_zero, Nat.div_one]
      · rw [upd_ne _ _ e]
  · intro i t _ ⟨V', ht, hag, hc⟩
    refine WP.seq (wp_movS (v := 0) rfl fun u U _ => WP.block_nil ?_)
    have hu := ht.of_rest U.keeps (by decide) U.mem
    refine WP.mono (hu.half_W hw (by rw [U.gpr]; rfl) hl) fun t' ⟨h', _⟩ => ⟨V', ?_, hag, hc⟩
    refine h'.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    rw [upd_upd, upd_self, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  · intro i t _ ⟨V', ht, _, hc⟩
    exact ⟨ht.ws, by rw [ht.sl _ (by simp), hc]⟩
  · intro i t u _ ⟨V', ht, hag, hc⟩ k e r
    have hu := (ht.slot1 k (by decide) r e).mono (A' := A) (live' := live)
      (AW' := upd AW wT (AW wT / 2 ^ (i + 1))) (liveW' := liveW) (V' := upd V' sBc (b - (i + 1)))
      (ls' := sBc :: ls) (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
    refine ⟨fun _ => ⟨_, hu, agree V' _ hag, upd_self _ _ _⟩, fun hib => ⟨upd V' sBc (b - (i + 1)), ?_, agree V' _ hag⟩⟩
    have e2 : AW wT / 2 ^ b = AW wT / 2 ^ (i + 1) := by rw [hib]
    rw [e2]; exact hu

end

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86.Rt (PtrAt ea_ptr ws_write readSrc_ptr)
open VG.Proof.Rsa.X86.KeyRt (kw)

theorem val32_pred (m : Mem) (B : Addr) {d k : Nat} (hk : 1 ≤ k) :
    val32 m B d k = w32 m B d + 2 ^ 32 * val32 m B (d + 4) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega_using [hk]⟩
  rfl

/-- The wide `[j]`'s low word less the header word `sZf`, at most that word. -/
theorem KS.subLow {j : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ liveW) (hZ : sZf ∈ ls)
    (hle : V sZf ≤ AW j % 2 ^ 32) (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.arrPtr wid .esi j .edx ++ ([.mov .eax (.mem (at_ .esi 0)),
      .alu .sub .eax (.mem (VG.Impl.Mont.X86.sc sZf)), .store (at_ .esi 0) .eax] : List Instr))) s fun t =>
      KS g s0 A live (upd AW j (AW j - V sZf)) (j :: liveW) V ls t := by
  have hr := h.rtW
  have jl := h.liveW_lt j hj
  have fit := hr.ws.arr_fit jl
  have nw := hr.ws.workspace.nowrap
  have kp : 1 ≤ kw (16 * g.n + 24) := by rw [kw_wid]; change 1 ≤ 2 * (2 * g.n + 2) + 2; omega_using []
  simp only [S] at fit
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hr) hr.lenLe hr.edi (r := .esi)
    (t := .edx) (j := j) (by decide) (by decide) (by omega_using [fit, nw]) fun u K m p _ => ?_
  have hu := hr.rt.of_keeps K
  have hk := h.of_rest K (by decide) m
  refine wp_movS (readSrc_ptr hu p (d := 0) (by omega_using [fit])) fun u₁ U₁ _ => ?_
  have hk₁ := hk.of_rest U₁.keeps (by decide) U₁.mem
  refine wp_subS (hk₁.readSlot hZ) fun u₂ U₂ _ => ?_
  have p₂ : PtrAt u₂ g.B .esi (arr (kw (16 * g.n + 24)) j) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact p
  refine wp_storeS (ea_ptr (hu.of_wr (by rw [U₂.wr, U₁.wr])) p₂ (d := 0) (by omega_using [fit]))
    (ws_write (hu.of_wr (by rw [U₂.wr, U₁.wr])) (by omega_using [fit])) fun t T => WP.block_nil ?_
  rw [Nat.add_zero] at T
  have mem : t.mem = s.mem.writeW (off g.B (arr (kw (16 * g.n + 24)) j)) (u₂.gpr .eax) := by
    rw [T.mem, U₂.mem, U₁.mem, m]
  have O := writeW32_outside s.mem g.B (d := arr (kw (16 * g.n + 24)) j) (u₂.gpr .eax) (by omega_using [fit, nw])
  rw [← mem] at O
  have Kt : Keeps opRegs s t := (K.mono (by decide)).trans (((U₁.keeps.mono (by decide)).trans
    (U₂.keeps.mono (by decide))).trans ((T.keeps []).mono (by decide)))
  have keep : Keep g.B (kw (16 * g.n + 24)) [j] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega_using []) (by simp)
  rw [kw_wid] at keep
  refine h.write_W keep jl (by simp) Kt ?_ hl (by simp)
  -- The value: the low word replaced.
  have eK : g.W = kw (16 * g.n + 24) := (kw_wid g.n).symm
  have old := h.arrsW j hj
  rw [eK] at old ⊢
  unfold num at old ⊢
  rw [val32_pred _ _ kp] at old ⊢
  have rest := O.val32 (d := arr (kw (16 * g.n + 24)) j + 4) (k := kw (16 * g.n + 24) - 1) (.inr (by omega_using []))
    (by omega_using [fit, nw])
  have e0 : w32 s.mem g.B (arr (kw (16 * g.n + 24)) j) = AW j % 2 ^ 32 := by
    rw [← old, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [w32]; exact BitVec.isLt _)]
  have w0 : w32 t.mem g.B (arr (kw (16 * g.n + 24)) j) = w32 s.mem g.B (arr (kw (16 * g.n + 24)) j) - V sZf := by
    rw [mem, w32_write_self, U₂.gpr, U₁.gpr, m, BitVec.toNat_sub, toNat_ofNat32
      (Nat.lt_of_le_of_lt hle (Nat.mod_lt _ (by decide)))]
    simp only [w32, Nat.add_zero] at e0 ⊢
    have l := (s.mem.readW (off g.B (arr (kw (16 * g.n + 24)) j)) 32).isLt
    omega_using [hle, e0]
  rw [rest, w0, e0]
  omega_using [hle, old, e0]

/-- `subLow`, its value aside: the low word written, with no bound on `sZf`. -/
theorem KS.subLow_w {j : Nat} (h : KS g s0 A live AW liveW V ls s) (hj : j ∈ liveW) (hZ : sZf ∈ ls)
    (hl : ∀ i ∈ live, i / 2 ≠ j) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.arrPtr wid .esi j .edx ++ ([.mov .eax (.mem (at_ .esi 0)),
      .alu .sub .eax (.mem (VG.Impl.Mont.X86.sc sZf)), .store (at_ .esi 0) .eax] : List Instr))) s fun t =>
      ∃ x, KS g s0 A live (upd AW j x) (j :: liveW) V ls t := by
  have hr := h.rtW
  have jl := h.liveW_lt j hj
  have fit := hr.ws.arr_fit jl
  have nw := hr.ws.workspace.nowrap
  have kp : 1 ≤ kw (16 * g.n + 24) := by rw [kw_wid]; change 1 ≤ 2 * (2 * g.n + 2) + 2; omega_using []
  simp only [S] at fit
  refine VG.Proof.Rsa.X86.KeyRt.arrPtr_ok (VG.Proof.Rsa.X86.KeyRt.lenSrc hr) hr.lenLe hr.edi (r := .esi)
    (t := .edx) (j := j) (by decide) (by decide) (by omega_using [fit, nw]) fun u K m p _ => ?_
  have hu := hr.rt.of_keeps K
  have hk := h.of_rest K (by decide) m
  refine wp_movS (readSrc_ptr hu p (d := 0) (by omega_using [fit])) fun u₁ U₁ _ => ?_
  have hk₁ := hk.of_rest U₁.keeps (by decide) U₁.mem
  refine wp_subS (hk₁.readSlot hZ) fun u₂ U₂ _ => ?_
  have p₂ : PtrAt u₂ g.B .esi (arr (kw (16 * g.n + 24)) j) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact p
  refine wp_storeS (ea_ptr (hu.of_wr (by rw [U₂.wr, U₁.wr])) p₂ (d := 0) (by omega_using [fit]))
    (ws_write (hu.of_wr (by rw [U₂.wr, U₁.wr])) (by omega_using [fit])) fun t T => WP.block_nil ?_
  rw [Nat.add_zero] at T
  have mem : t.mem = s.mem.writeW (off g.B (arr (kw (16 * g.n + 24)) j)) (u₂.gpr .eax) := by
    rw [T.mem, U₂.mem, U₁.mem, m]
  have O := writeW32_outside s.mem g.B (d := arr (kw (16 * g.n + 24)) j) (u₂.gpr .eax) (by omega_using [fit, nw])
  rw [← mem] at O
  have Kt : Keeps opRegs s t := (K.mono (by decide)).trans (((U₁.keeps.mono (by decide)).trans
    (U₂.keeps.mono (by decide))).trans ((T.keeps []).mono (by decide)))
  have keep : Keep g.B (kw (16 * g.n + 24)) [j] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using O) (by simp only [S]; omega_using []) (by simp)
  rw [kw_wid] at keep
  exact ⟨_, h.write_W keep jl (by simp) Kt rfl hl (by simp)⟩

end

theorem and_pow_eq_zero (x j : Nat) : x &&& 2 ^ j = 0 ↔ x / 2 ^ j % 2 = 0 := by
  have hb : x.testBit j = decide (x / 2 ^ j % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  constructor
  · intro h
    have := congrArg (fun y => y.testBit j) h
    simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.and_true, Nat.zero_testBit, hb] at this
    simp at this; omega_using [this]
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases e : j = i
    · subst e; simp [hb, h]
    · simp [e]

theorem div_pow_step (x j : Nat) :
    x / 2 ^ j * 2 ^ j = x / 2 ^ (j + 1) * 2 ^ (j + 1) + (if x &&& 2 ^ j = 0 then 0 else 2 ^ j) := by
  have hq : x / 2 ^ (j + 1) = x / 2 ^ j / 2 := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
  rw [hq, Nat.pow_succ]
  have h := Nat.div_add_mod (x / 2 ^ j) 2
  by_cases e : x / 2 ^ j % 2 = 0
  · rw [ite_eq_left_iff.mpr (fun h' => absurd ((and_pow_eq_zero x j).mpr e) h')]
    generalize x / 2 ^ j = y at *
    generalize 2 ^ j = P
    rw [e] at h
    grind
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' (fun h'' => e ((and_pow_eq_zero x j).mp h'')))]
    generalize x / 2 ^ j = y at *
    generalize 2 ^ j = P
    rw [show y % 2 = 1 by omega_using [e]] at h
    grind

/-- A stage's shift by `2^j` units of `2^m` where `x` has bit `j`. -/
theorem shift_step (D x j m : Nat) :
    (if (if x &&& 2 ^ j = 0 then 0 else 1) = 0 then D / 2 ^ (m * (x / 2 ^ (j + 1) * 2 ^ (j + 1)))
      else D / 2 ^ (m * (x / 2 ^ (j + 1) * 2 ^ (j + 1))) / 2 ^ (m * 2 ^ j)) =
      D / 2 ^ (m * (x / 2 ^ j * 2 ^ j)) := by
  rw [div_pow_step x j]
  by_cases e : x &&& 2 ^ j = 0
  · simp only [e, ↓reduceIte, Nat.add_zero]
  · simp only [e, ↓reduceIte, Nat.one_ne_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]

theorem stage_zero {x j : Nat} (h : x < 2 ^ j) : x / 2 ^ j * 2 ^ j = 0 := by
  rw [Nat.div_eq_of_lt h, Nat.zero_mul]

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat}
open VG.Impl.Rsa.X86.KeyRt (sel)

theorem w_lt_W (g : Geo) : g.w < g.W := by change 2 * g.n + 2 < 2 * (2 * g.n + 2) + 2; omega_using []

/-- The word stages of `finishX`: the root down by `⌊K / 2⌋` words (`K` in `sKw`). -/
theorem fin_words {a : Nat} (h : KS g s0 A [aD, aZero] AW [sqD] V ls s)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (haw : wq a ≤ g.w)
    (hK : sKw ∈ ls) (hC : sC4 ∉ ls) (hS : sStg ∉ ls) (hKw : V sKw / 2 < wq a) (hK32 : V sKw < 2 ^ 32) :
    WP isa (wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 VG.Impl.Rsa.X86.RecoverDetRt.nl .eax) (seqs [
      .block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sKw)), .shift .shr .eax 1,
        .mov .edx (.mem (VG.Impl.Mont.X86.sc sC4)), .shift .shr .edx 2, .alu .and .eax (.reg .edx),
        .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
        .store (VG.Impl.Mont.X86.sc sStg) .eax],
      moveH wid sqD wT true false, sel wid sqD sqD wT sStg])) s fun t =>
      ∃ V', KS g s0 A [aD, aZero] (upd AW sqD (AW sqD / 2 ^ (32 * (V sKw / 2)))) [sqD] V' (sC4 :: ls) t ∧
        ∀ d ∈ ls, V' d = V d := by
  have w256 : wq a ≤ 256 := by unfold wq; omega_using [hal]
  have wW := w_lt_W g
  have agreeC : ∀ (V' : Nat → Nat) (x : Nat), (∀ d ∈ ls, V' d = V d) → ∀ d ∈ ls, upd V' sC4 x d = V d :=
    fun V' x hV' d hd => by rw [upd_ne _ _ (fun e => hC (by rw [← e]; exact hd)), hV' d hd]
  refine wordStagesL_ok (k := 7) (lim := 4 * wq a)
    (fun j t => ∃ V', KS g s0 A [aD, aZero]
      (upd AW sqD (AW sqD / 2 ^ (32 * (V sKw / 2 / 2 ^ (j + 1) * 2 ^ (j + 1))))) [sqD] V' (sC4 :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sC4 = 4 * 2 ^ j)
    (fun j t => ∃ V', KS g s0 A [aD, aZero]
      (upd AW sqD (AW sqD / 2 ^ (32 * (V sKw / 2 / 2 ^ j * 2 ^ j)))) [sqD] V' (sC4 :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sC4 = 4 * 2 ^ j)
    (by decide) h.ws ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t k e r
    refine ⟨upd V sC4 (4 * 2 ^ 7), (h.slot1 k (by decide) (r.mono (by decide)) e).mono
      (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), agreeC V _ (fun _ _ => rfl),
      upd_self _ _ _⟩
    simp only [List.mem_singleton] at hj; subst hj
    rw [upd_self, stage_zero (by omega_using [hKw, w256]), Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  · intro j t _ ⟨V', ht, _, hc⟩
    exact ⟨ht.ws, by rw [ht.sl _ (by simp), hc]⟩
  · intro j t _ ⟨V', ht, _, _⟩ is Q kk
    exact VG.Proof.Rsa.X86.WordRt.width4_ok (ht.mlen ha hal) fun u K m e =>
      kk u (K.mono (by decide)) m (by rw [e]; exact toNat_ofNat32 (by omega_using [w256]))
  · intro j t u _ ⟨V', ht, hag, hc⟩ K m
    exact ⟨V', ht.of_rest K (fun x hx => hx) m, hag, hc⟩
  · intro j t hj ⟨V', ht, hag, hc⟩ hlt
    have p7 : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hj
    simp only [VG.Impl.Rsa.X86.Keys.seqs]
    refine WP.seq (WP.mono (ht.wordFlag (by simp [hK]) (by simp) (by rw [hag _ hK]; exact hK32)
      (by rw [hc]; omega_using [p7])) fun t₁ ⟨h₁, _⟩ => ?_)
    refine WP.seq (WP.mono (h₁.moveDown_W (o := wT) (a := sqD) (c := 2 ^ j) (by decide) (by simp) (by decide)
      (by omega_using [haw, wW, hlt]) (by simp) (by rw [upd_ne _ _ (by decide), hc]) (by decide)) fun t₂ ⟨h₂, _, _⟩ => ?_)
    refine WP.mono (h₂.sel_W (o := sqD) (a := sqD) (b := wT) (sl := sStg) (by decide) (by simp) (by simp)
      (by simp) (by rw [upd_self]; split <;> decide) (.inr (by decide)) (by decide)) fun t₃ ⟨h₃, _⟩ => ?_
    refine ⟨upd V' sStg (if V' sKw / 2 &&& V' sC4 / 4 = 0 then 0 else 1),
      h₃.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨by simp at hi ⊢; exact .inl hi, ?_⟩)
        (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩),
      fun d hd => by rw [upd_ne _ _ (fun e => hS (by rw [← e]; exact hd)), hag d hd],
      by rw [upd_ne _ _ (by decide), hc]⟩
    simp only [List.mem_singleton] at hi; subst hi
    show _ = AW sqD / 2 ^ (32 * (V sKw / 2 / 2 ^ j * 2 ^ j))
    rw [upd_self, upd_self, upd_ne _ _ (by decide), upd_self, upd_self, hag _ hK, hc,
      Nat.mul_div_cancel_left _ (by decide)]
    exact shift_step (AW sqD) (V sKw / 2) j 32
  · intro j t _ ⟨V', ht, hag, hc⟩ hge
    refine ⟨V', ?_, hag, hc⟩
    have e1 : V sKw / 2 / 2 ^ j * 2 ^ j = 0 := stage_zero (by omega_using [hKw, hge])
    have e2 : V sKw / 2 / 2 ^ (j + 1) * 2 ^ (j + 1) = 0 := stage_zero (by rw [Nat.pow_succ]; omega_using [hKw, hge])
    rw [e1]; rw [e2] at ht; exact ht
  · intro j t _ ⟨V', ht, _, hc⟩
    exact ⟨ht.ws, by rw [ht.sl _ (by simp), hc]⟩
  · intro j t u _ ⟨V', ht, hag, hc⟩ k e r
    have hu := (ht.slot1 k (by decide) r e).mono (A' := A) (live' := [aD, aZero])
      (AW' := upd AW sqD (AW sqD / 2 ^ (32 * (V sKw / 2 / 2 ^ j * 2 ^ j)))) (liveW' := [sqD])
      (V' := upd V' sC4 (2 * 2 ^ j)) (ls' := sC4 :: ls) (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
    refine ⟨fun hj => ⟨upd V' sC4 (2 * 2 ^ j), ?_, agreeC V' _ hag, ?_⟩, fun hj => ⟨upd V' sC4 (2 * 2 ^ j), ?_, agreeC V' _ hag⟩⟩
    · rw [show j - 1 + 1 = j by omega_using [hj]]; exact hu
    · rw [upd_self]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [hj]⟩
      rw [Nat.add_sub_cancel, Nat.pow_succ]; omega_using []
    · subst hj
      simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one] at hu
      exact hu

end

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {AW : Nat → Nat} {V : Nat → Nat} {ls : List Nat}
open VG.Impl.Rsa.X86.KeyRt (sel copy)

/-- The bit stages of `finishX`: the root down by `z` bits (`z < 32` in `sZb`). -/
theorem fin_bits (h : KS g s0 A [aD, aZero] AW [sqD] V ls s)
    (hZ : sZb ∈ ls) (hB : sBh ∉ ls) (hS : sStg ∉ ls) (hBc : sBc ∉ ls) (hz : V sZb < 32) :
    WP isa (bitStagesL 16 1 (.seq (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sZb)),
      .alu .and .eax (.mem (VG.Impl.Mont.X86.sc sBh)), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax),
      .alu .add .eax (.imm 1), .store (VG.Impl.Mont.X86.sc sStg) .eax]) (downBitsSelH sqD))) s fun t =>
      ∃ V', KS g s0 A [aD, aZero] (upd AW sqD (AW sqD / 2 ^ (V sZb))) [sqD] V' (sBh :: ls) t ∧
        ∀ d ∈ ls, V' d = V d := by
  have agreeB : ∀ (V' : Nat → Nat) (x : Nat), (∀ d ∈ ls, V' d = V d) → ∀ d ∈ ls, upd V' sBh x d = V d :=
    fun V' x hV' d hd => by rw [upd_ne _ _ (fun e => hB (by rw [← e]; exact hd)), hV' d hd]
  refine bitStagesL_ok (k := 4) (m := 0)
    (fun j t => ∃ V', KS g s0 A [aD, aZero]
      (upd AW sqD (AW sqD / 2 ^ (V sZb / 2 ^ (j + 1) * 2 ^ (j + 1)))) [sqD] V' (sBh :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sBh = 2 ^ j)
    (fun j t => ∃ V', KS g s0 A [aD, aZero]
      (upd AW sqD (AW sqD / 2 ^ (V sZb / 2 ^ j * 2 ^ j))) [sqD] V' (sBh :: ls) t ∧
      (∀ d ∈ ls, V' d = V d) ∧ V' sBh = 2 ^ j)
    (by decide) (by decide) h.ws ?_ ?_ ?_ ?_
  · intro t k e r
    refine ⟨upd V sBh (2 ^ 4), (h.slot1 k (by decide) (r.mono (by decide)) e).mono
      (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨hd, rfl⟩), agreeB V _ (fun _ _ => rfl),
      upd_self _ _ _⟩
    simp only [List.mem_singleton] at hj; subst hj
    rw [upd_self, stage_zero (by omega_using [hz]), Nat.pow_zero, Nat.div_one]
  · intro j t _ hj ⟨V', ht, hag, hc⟩
    have p4 : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hj
    refine WP.seq (WP.mono (ht.bitFlag (by simp [hZ]) (by simp) (by rw [hag _ hZ]; omega_using [hz])
      (by rw [hc]; omega_using [p4])) fun t₁ ⟨h₁, _⟩ => ?_)
    unfold downBitsSelH
    simp only [VG.Impl.Rsa.X86.Keys.seqs]
    refine WP.seq (WP.mono (h₁.copy_W (o := wT) (a := sqD) (by decide) (by simp) (by decide) (by decide))
      fun t₂ ⟨h₂, _⟩ => ?_)
    refine WP.seq (WP.mono (h₂.timesHalf (b := 2 ^ j) (by simp) (by decide) (Nat.two_pow_pos _) (by omega_using [p4])
      (by simp) (by rw [upd_ne _ _ (by decide), hc]) (by simp [hBc]; decide)) fun t₃ ⟨V₃, h₃, hag₃⟩ => ?_)
    have v3 : V₃ sStg = if V' sZb &&& V' sBh = 0 then 0 else 1 := by rw [hag₃ _ (by simp), upd_self]
    refine WP.mono (h₃.sel_W (o := sqD) (a := sqD) (b := wT) (sl := sStg) (by decide) (by simp) (by simp)
      (by simp) (by rw [v3]; split <;> decide) (.inr (by decide)) (by decide)) fun t₄ ⟨h₄, _⟩ => ?_
    refine ⟨V₃, h₄.mono (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨by simp at hi ⊢; exact .inl hi, ?_⟩)
        (fun d hd => ⟨by simp at hd ⊢; exact .inr (.inr hd), rfl⟩),
      fun d hd => by rw [hag₃ _ (by simp [hd]), upd_ne _ _ (fun e => hS (by rw [← e]; exact hd)), hag d hd],
      by rw [hag₃ _ (by simp), upd_ne _ _ (by decide), hc]⟩
    simp only [List.mem_singleton] at hi; subst hi
    show _ = AW sqD / 2 ^ (V sZb / 2 ^ j * 2 ^ j)
    rw [upd_self, v3]
    simp only [upd_self]
    rw [upd_ne _ _ (by decide : sqD ≠ wT), upd_upd_ne _ (by decide : sqD ≠ wT), hag _ hZ, hc]
    have := shift_step (AW sqD) (V sZb) j 1
    simp only [Nat.one_mul] at this
    exact this
  · intro j t _ _ ⟨V', ht, _, hc⟩
    exact ⟨ht.ws, by rw [ht.sl _ (by simp), hc]⟩
  · intro j t u _ _ ⟨V', ht, hag, hc⟩ k e r
    have hu := (ht.slot1 k (by decide) r e).mono (A' := A) (live' := [aD, aZero])
      (AW' := upd AW sqD (AW sqD / 2 ^ (V sZb / 2 ^ j * 2 ^ j))) (liveW' := [sqD])
      (V' := upd V' sBh (2 ^ j / 2)) (ls' := sBh :: ls) (fun i hi => ⟨hi, rfl⟩) (fun i hi => ⟨hi, rfl⟩)
      (fun d hd => ⟨List.mem_cons_of_mem _ hd, rfl⟩)
    refine ⟨fun hj => ⟨upd V' sBh (2 ^ j / 2), ?_, agreeB V' _ hag, ?_⟩,
      fun hj => ⟨upd V' sBh (2 ^ j / 2), ?_, agreeB V' _ hag⟩⟩
    · rw [show j - 1 + 1 = j by omega_using [hj]]; exact hu
    · rw [upd_self]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [hj]⟩
      rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    · subst hj
      simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one] at hu
      exact hu

end

/-- The root's arithmetic: its square test and the root shifted back, less one where `X₀ = 0`. -/
theorem fin_math {X₀ zf c s r X : Nat} (hz : zf = if X₀ = 0 then 1 else 0)
    (hX : X = (X₀ + zf) * 4 ^ c) (hsr : s * s + r = X) (hr : r ≤ 2 * s) :
    (r = 0 ↔ isqrt X₀ * isqrt X₀ = X₀) ∧ s / 2 ^ c = isqrt (X₀ + zf) ∧
      zf ≤ isqrt (X₀ + zf) % 2 ^ 32 ∧ isqrt (X₀ + zf) - zf = isqrt X₀ := by
  have hs : isqrt X = s := VG.Proof.Bignum.SqrtRem.sqrt_of_rem hsr hr
  have hX' : X = 4 ^ c * (X₀ + zf) := by rw [hX, Nat.mul_comm]
  have i0 : isqrt 0 = 0 := VG.Proof.Bignum.SqrtRem.sqrt_of_rem (s := 0) (r := 0) rfl (Nat.zero_le _)
  have i1 : isqrt 1 = 1 := VG.Proof.Bignum.SqrtRem.sqrt_of_rem (s := 1) (r := 0) rfl (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← VG.Proof.Bignum.SqrtRem.square_iff_rem hsr hr, hX', VG.Proof.Bignum.SqrtRem.norm_square]
    by_cases e : X₀ = 0
    · subst e; rw [hz]; simp [i0, i1]
    · rw [hz, ite_eq_right_of_eq_false _ _ (eq_false e), Nat.add_zero]
  · rw [← hs, hX', VG.Proof.Bignum.SqrtRem.norm_sqrt]
  · by_cases e : X₀ = 0
    · subst e; rw [hz]; simp [i1]
    · rw [hz, ite_eq_right_of_eq_false _ _ (eq_false e)]; exact Nat.zero_le _
  · by_cases e : X₀ = 0
    · subst e; rw [hz]; simp [i0, i1]
    · rw [hz, ite_eq_right_of_eq_false _ _ (eq_false e), Nat.add_zero, Nat.sub_zero]

section
variable {g : Geo} {s0 u : State} {A V0 : Nat → Nat}

theorem sq_sub : ∀ d ∈ sOk5 :: sqSlotsW, d ∈ sOk5 :: lsN := by decide
theorem sq_lsN : ∀ d ∈ sqSlotsW, d ∈ lsN ∧ d ≠ sZb := by decide
theorem live_sub : ∀ j ∈ [aY, aD, aZero], j ∈ aY :: 2 * sqD :: [aD, aZero] := by decide

theorem lsN_ne : ∀ d ∈ lsN, d ≠ sOk5 ∧ d ≠ sStg ∧ d ≠ sC4 ∧ d ≠ sBh ∧ d ≠ sBc := by decide

/-- `RecoverDetRt.finishX`: whether the remainder is zero, and the root shifted back. -/
theorem finishX_ok {g : Geo} {s0 u : State} {A V0 : Nat → Nat} {a X X₀ : Nat}
    (hI : SqI g s0 A V0 a X 0 u) (z : A aZero = 0)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (ha0 : 1 ≤ a)
    (haw : wq a ≤ g.w) (hz : V0 sZf = if X₀ = 0 then 1 else 0)
    (hXe : X = (X₀ + V0 sZf) * 4 ^ (16 * V0 sKw + V0 sZb / 2))
    (hK : V0 sKw < 2 * wq a) (hzb : V0 sZb % 2 = 0) (hzb' : V0 sZb ≤ 30) :
    WP isa finishX u fun v => ∃ A' AW',
      KS g s0 A' [aY, aD, aZero] AW' [] (upd V0 sOk5 (if isqrt X₀ * isqrt X₀ = X₀ then 1 else 0))
        (sOk5 :: sqSlotsW) v ∧
      A' aY = isqrt X₀ ∧ A' aD = A aD ∧ A' aZero = 0 := by
  obtain ⟨AW, V, s, r, h, hag, _, hd, hw, hsr, hr2, _, _, hslt, _⟩ := hI
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero, Nat.div_one,
    Nat.sub_zero] at hd hw hsr hslt
  obtain ⟨msq, mroot, mle, msub⟩ := fin_math hz hXe hsr hr2
  have w256 : wq a ≤ 256 := by unfold wq; omega
  have vK : V sKw = V0 sKw := hag _ (by simp)
  have vZ : V sZb = V0 sZb := hag _ (by simp)
  have vF : V sZf = V0 sZf := hag _ (by simp)
  have ne := lsN_ne
  unfold finishX
  simp only [List.cons_append, List.nil_append, VG.Impl.Rsa.X86.Keys.seqs]
  -- Whether the remainder is zero; the root `D / 2`.
  refine WP.seq (WP.mono (h.orAll (j := wR) (by simp)) fun u₁ ⟨h₁, _, e₁⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono h₁.flagZero fun u₂ ⟨h₂, _⟩ => ?_))
  refine wp_movS (h₂.readSlot (by simp)) fun u₃ U₃ _ => ?_
  have h₃ := h₂.of_rest U₃.keeps (by decide) U₃.mem
  refine WP.mono (h₃.storeSlot (by decide) .eax) fun u₄ ⟨h₄, _, _⟩ => ?_
  refine WP.seq (wp_movS (v := 0) rfl fun u₅ U₅ _ => WP.block_nil ?_)
  have h₅ := h₄.of_rest U₅.keeps (by decide) U₅.mem
  refine WP.seq (WP.mono (h₅.half_W (j := sqD) (by simp) (by rw [U₅.gpr]; rfl) (by decide))
    fun u₆ ⟨h₆, _⟩ => ?_)
  have f₃ : (u₃.gpr .eax).toNat = if r = 0 then 1 else 0 := by
    rw [U₃.gpr, upd_self, ← hw]
    by_cases e : AW wR = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (e₁.mpr e)), ite_eq_left_of_eq_true _ _ (eq_true e)]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => e (e₁.mp h'))), ite_eq_right_of_eq_false _ _ (eq_false e)]; rfl
  rw [f₃] at h₆
  have h₆' : KS g s0 A [aD, aZero] (upd AW sqD s) [sqD] (upd V sOk5 (if r = 0 then 1 else 0))
      (sOk5 :: lsN) u₆ := by
    refine h₆.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; exact .inl hj, ?_⟩) (fun d hd => ?_)
    · simp only [List.mem_singleton] at hj; subst hj
      rw [upd_self, upd_self, hd, Nat.mul_div_cancel_left _ (by decide)]
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨by simp, by rw [upd_self, upd_self]⟩
      · obtain ⟨n1, n2, -⟩ := ne d hd
        exact ⟨by simp [hd], by rw [upd_ne _ _ n1, upd_ne _ _ n2, upd_ne _ _ n1]⟩
  -- The word stages.
  have v₆K : upd V sOk5 (if r = 0 then 1 else 0) sKw = V0 sKw := by rw [upd_ne _ _ (by decide), vK]
  refine WP.seq (WP.mono (fin_words h₆' ha hal haw (by simp) (by decide) (by decide)
    (by rw [v₆K]; omega) (by rw [v₆K]; omega)) fun u₇ ⟨V₇, h₇, ag₇⟩ => ?_)
  have v₇ : ∀ d ∈ lsN, V₇ d = V0 d := fun d hd => by
    rw [ag₇ d (by simp [hd]), upd_ne _ _ (ne d hd).1, hag d hd]
  have v₇5 : V₇ sOk5 = if r = 0 then 1 else 0 := by rw [ag₇ _ (by simp), upd_self]
  rw [upd_upd, upd_self, v₆K] at h₇
  -- `sZb := 16 (K mod 2) + z / 2`.
  refine WP.seq (WP.mono (h₇.zbBlock (by simp) (by simp) (by rw [v₇ _ (by simp)]; omega)
    (by rw [v₇ _ (by simp)]; omega)) fun u₈ h₈ => ?_)
  have h₈' := h₈.mono (A' := A) (live' := [aD, aZero]) (liveW' := [sqD]) (ls' := sOk5 :: lsN)
    (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩)
    (fun d hd => ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd), rfl⟩)
  rw [v₇ _ (by simp), v₇ _ (by simp)] at h₈'
  -- The bit stages.
  refine WP.seq (WP.mono (fin_bits h₈' (by simp) (by decide) (by decide) (by decide)
    (by rw [upd_self]; omega)) fun u₉ ⟨V₉, h₉, ag₉⟩ => ?_)
  have v₉ : ∀ d ∈ sOk5 :: sqSlotsW, V₉ d = upd V0 sOk5 (if r = 0 then 1 else 0) d := fun d hd => by
    rw [ag₉ d (sq_sub d hd)]
    rcases List.mem_cons.mp hd with rfl | hd
    · rw [upd_ne _ _ (by decide), v₇5, upd_self]
    · have hd' : d ∈ lsN := (sq_lsN d hd).1
      rw [upd_ne _ _ (sq_lsN d hd).2, v₇ d hd', upd_ne _ _ (ne d hd').1]
  have v₉F : V₉ sZf = V0 sZf := by rw [ag₉ _ (by simp), upd_ne _ _ (by decide), v₇ _ (by simp)]
  rw [upd_upd, upd_self, upd_self] at h₉
  have eroot : s / 2 ^ (32 * (V0 sKw / 2)) / 2 ^ (16 * (V0 sKw % 2) + V0 sZb / 2) = isqrt (X₀ + V0 sZf) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← mroot]; congr 2; omega
  rw [eroot] at h₉
  -- The root less one where `X₀ = 0`, then into the narrow `aY`.
  refine WP.seq (WP.mono (h₉.subLow (j := sqD) (by simp) (by simp) (by rw [upd_self, v₉F]; exact mle)
    (by decide)) fun u₁₀ h₁₀ => ?_)
  rw [upd_upd, upd_self, v₉F, msub] at h₁₀
  have hv := h₁₀.view (j := sqD) (by simp)
  refine WP.mono (hv.copy_w (o := aY) (a := 2 * sqD) (by decide) (by simp) (by decide) (by decide))
    fun v ⟨hv', _, _⟩ => ?_
  have lt : isqrt X₀ < 2 ^ (32 * g.w) := by
    have h1 : isqrt X₀ ≤ s := by
      rw [← msub, ← mroot]; exact Nat.le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _)
    have h2 : 2 ^ (32 * wq a) ≤ 2 ^ (32 * g.w) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨_, upd AW sqD (isqrt X₀), hv'.mono (fun j hj => ⟨live_sub j hj, rfl⟩) (fun j hj => by simp at hj)
    (fun d hd => ⟨List.mem_cons_of_mem _ (sq_sub d hd), ?_⟩), ?_, ?_, ?_⟩
  · rw [v₉ d hd]
    congr 1
    by_cases e : r = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e), ite_eq_left_of_eq_true _ _ (eq_true (msq.mp e))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e), ite_eq_right_of_eq_false _ _ (eq_false (fun h' => e (msq.mpr h')))]
  · rw [upd_self, upd_self, upd_self, Nat.mod_eq_of_lt lt]
  · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]
  · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), z]

end

end VG.Proof.Rsa.X86.Recover
