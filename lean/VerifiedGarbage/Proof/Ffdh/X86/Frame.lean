module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH on i686: the frame of the synthetic arguments

`fill a` stores into the 76 bytes at `esp` the eighteen arguments of private
CRT's operations, `synth a g` for the function's arguments `g` (`fill_ok`):
argument `i` in the word at `esp + 4 + 4 i`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Impl.Ffdh.X86 (Args slotOp argVal zeroVal optVal compVal val piece fill)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Bignum.X86.PublicRt (frame_other)

/-- The value of an optional argument, or zero. -/
def optArg (g : Nat → BitVec 32) : Option Nat → BitVec 32
  | some j => g j
  | none => 0

/-- Synthetic argument `i`, from the function's arguments `g`. -/
def synth (a : Args) (g : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => optArg g a.out
  | 1 => g a.plen
  | 2 => g a.dom
  | 3 => g a.plen
  | 4 => g a.dom + g a.plen
  | 5 => g a.plen
  | 6 => g a.dom + g a.plen + g a.plen
  | 7 => g a.plen
  | 8 => optArg g a.y
  | 9 => optArg g (a.y.map fun _ => a.plen)
  | 10 => optArg g a.x
  | 11 => optArg g (a.x.map (· + 1))
  | 12 => g a.dlen
  | 16 => g a.ws
  | 17 => g (a.ws + 1)
  | _ => 0

/-- Every argument position of `a` is below `n`. -/
structure Below (a : Args) (n : Nat) : Prop where
  out : ∀ j, a.out = some j → j < n
  dom : a.dom < n
  dlen : a.dlen < n
  plen : a.plen < n
  y : ∀ j, a.y = some j → j < n
  x : ∀ j, a.x = some j → j + 1 < n
  ws : a.ws + 1 < n

section
variable {is : List Instr} {Q : State → Prop}

/-- An operand at `esp` reads the same after writes to registers but `esp`, memory kept. -/
theorem src_esp {s t : State} {rs : List Reg} (K : Keeps rs s t) (esp : .esp ∉ rs) (m : t.mem = s.mem)
    {d : Nat} : readSrc t (.mem (at_ .esp d)) = readSrc s (.mem (at_ .esp d)) := by
  simp only [readSrc, State.load32, State.ea, at_, K.1 _ esp, m, K.2.1, K.2.2]; rfl

theorem optVal_ok {t : State} {g : Nat → BitVec 32} {n : Nat} {o : Option Nat} (ho : ∀ j, o = some j → j < n)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j))
    (k : ∀ u, Keeps [.eax] t u → u.mem = t.mem → u.gpr .eax = optArg g o → WP isa (.block is) u Q) :
    WP isa (.block (optVal o ++ is)) t Q := by
  cases o with
  | none => exact wp_movS rfl fun u U _ => k u U.keeps U.mem U.gpr
  | some j => exact wp_movS (hr j (ho j rfl)) fun u U _ => k u U.keeps U.mem U.gpr

/-- `val a i`: `eax` synthetic argument `i`; only `eax` and `ecx` change. -/
theorem val_ok {t : State} {a : Args} {g : Nat → BitVec 32} {n : Nat} (hb : Below a n)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j)) (i : Nat)
    (k : ∀ u, Keeps [.eax, .ecx] t u → u.mem = t.mem → u.gpr .eax = synth a g i → WP isa (.block is) u Q) :
    WP isa (.block (val a i ++ is)) t Q := by
  have opt : ∀ {o : Option Nat}, (∀ j, o = some j → j < n) → synth a g i = optArg g o → val a i = optVal o →
      WP isa (.block (val a i ++ is)) t Q := fun ho e v => by
    rw [v]; exact optVal_ok ho hr fun u K m e' => k u (K.mono (by decide)) m (by rw [e', e])
  have arg : ∀ {j : Nat}, j < n → synth a g i = g j → val a i = argVal j → WP isa (.block (val a i ++ is)) t Q :=
    fun hj e v => by
      rw [v]; exact wp_movS (hr _ hj) fun u U _ => k u (U.keeps.mono (by decide)) U.mem (by rw [U.gpr, e])
  have comp : ∀ {c : Nat}, c ≤ 2 → val a i = compVal a c →
      synth a g i = (List.replicate c (g a.plen)).foldl (· + ·) (g a.dom) → WP isa (.block (val a i ++ is)) t Q :=
    fun {c} hc v e => by
      rw [v]
      simp only [compVal, List.cons_append, List.nil_append]
      refine wp_movS (hr _ hb.dom) fun u₁ U₁ _ => ?_
      have r₁ : readSrc u₁ (.mem (argAt 19 a.plen)) = some (g a.plen) := by
        unfold argAt; rw [src_esp U₁.keeps (by decide) U₁.mem]; exact hr _ hb.plen
      refine wp_movS r₁ fun u₂ U₂ _ => ?_
      have e₂ : u₂.gpr .eax = g a.dom := by rw [U₂.other _ (by decide), U₁.gpr]
      have c₂ : u₂.gpr .ecx = g a.plen := U₂.gpr
      have K₂ : Keeps [.eax, .ecx] t u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
      have M₂ : u₂.mem = t.mem := U₂.mem.trans U₁.mem
      match c, hc with
      | 0, _ => exact k u₂ K₂ M₂ (by rw [e, e₂]; rfl)
      | 1, _ =>
        refine wp_addS rfl fun u U _ => k u (K₂.trans (U.keeps.mono (by decide))) (U.mem.trans M₂) ?_
        rw [U.gpr, e₂, c₂, e]; rfl
      | 2, _ =>
        refine wp_addS rfl fun u₃ U₃ _ => wp_addS rfl fun u U _ =>
          k u ((K₂.trans (U₃.keeps.mono (by decide))).trans (U.keeps.mono (by decide))) (U.mem.trans (U₃.mem.trans M₂)) ?_
        rw [U.gpr, U₃.gpr, U₃.other _ (by decide), e₂, c₂, e]; rfl
  have zero : synth a g i = 0 → val a i = zeroVal → WP isa (.block (val a i ++ is)) t Q := fun e v => by
    rw [v]; exact wp_movS rfl fun u U _ => k u (U.keeps.mono (by decide)) U.mem (by rw [U.gpr, e])
  match i with
  | 0 => exact opt hb.out rfl rfl
  | 1 => exact arg hb.plen rfl rfl
  | 2 => exact comp (c := 0) (by decide) rfl rfl
  | 3 => exact arg hb.plen rfl rfl
  | 4 => exact comp (c := 1) (by decide) rfl rfl
  | 5 => exact arg hb.plen rfl rfl
  | 6 => exact comp (c := 2) (by decide) rfl rfl
  | 7 => exact arg hb.plen rfl rfl
  | 8 => exact opt hb.y rfl rfl
  | 9 => exact opt (o := a.y.map fun _ => a.plen) (fun j hj => by
      cases hy : a.y with
      | none => rw [hy] at hj; cases hj
      | some _ => rw [hy] at hj; cases hj; exact hb.plen) rfl rfl
  | 10 => exact opt (fun j hj => by have := hb.x j hj; omega) rfl rfl
  | 11 => exact opt (o := a.x.map (· + 1)) (fun j hj => by
      cases hx : a.x with
      | none => rw [hx] at hj; cases hj
      | some _ => rw [hx] at hj; cases hj; exact hb.x _ hx) rfl rfl
  | 12 => exact arg hb.dlen rfl rfl
  | 13 => exact zero rfl rfl
  | 14 => exact zero rfl rfl
  | 15 => exact zero rfl rfl
  | 16 => exact arg (by have := hb.ws; omega) rfl rfl
  | 17 => exact arg hb.ws rfl rfl
  | _ + 18 => exact zero rfl rfl

/-- The frame's word of synthetic argument `i`. -/
abbrev slotAddr (P : Addr) (i : Nat) : Addr := P + BitVec.ofNat 64 (4 + 4 * i)

/-- A store into the frame of 76 bytes at `esp`. -/
theorem frame76_store {t : State} {P : Addr} (hP : (t.gpr .esp).setWidth 64 = P)
    (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32) (hfr : (⟨P, 76⟩ : Region) ∈ t.wr) {i : Nat} (hi : i < 18) :
    t.ea (slotOp i) = slotAddr P i ∧ InRegions t.wr (slotAddr P i) 4 := by
  refine ⟨?_, ⟨_, hfr, Offset.contains_base _ (by omega) (by omega)⟩⟩
  rw [slotOp, at_, ea_mk, addr_eq (by omega), hP]

/-- A word of the frame, after a store to another. -/
theorem frame76_other (m : Mem) (P : Addr) (v : BitVec 32) {i j : Nat} (h : i ≠ j) (hi : i < 18) (hj : j < 18) :
    (m.writeW (slotAddr P i) v).readW (slotAddr P j) 32 = m.readW (slotAddr P j) 32 :=
  Mem.readW_writeW_sep (Offset.sep P (by omega) (by omega) (by omega)) (by decide)

/-- An argument at `esp` reads the same after changes to registers but `esp` and memory within
regions apart from it. -/
theorem src_frame {t u : State} {rs : List Reg} (K : Keeps rs t u) (esp : .esp ∉ rs) {R : List Region}
    (F : Frame R t.mem u.mem) {d : Nat} (hd : ∀ r ∈ R, Region.Disjoint ⟨t.ea (at_ .esp d), 4⟩ r) :
    readSrc u (.mem (at_ .esp d)) = readSrc t (.mem (at_ .esp d)) := by
  have e : u.ea (at_ .esp d) = t.ea (at_ .esp d) := by simp only [State.ea, at_, K.1 _ esp]
  simp only [readSrc, State.load32, e, K.2.1, K.2.2]
  rw [F.readW (r := ⟨t.ea (at_ .esp d), 4⟩) (Region.contains_self _ _) hd (by decide)]

/-- The first `c` synthetic arguments stored into the frame at `P` (`esp`), keeping everything else
but `eax` and `ecx`. -/
theorem fill_ok {t : State} {a : Args} {g : Nat → BitVec 32} {n : Nat} (hb : Below a n) {P : Addr}
    (hP : (t.gpr .esp).setWidth 64 = P) (hesp : (t.gpr .esp).toNat + 76 ≤ 2 ^ 32)
    (hfr : (⟨P, 76⟩ : Region) ∈ t.wr)
    (hr : ∀ j < n, readSrc t (.mem (argAt 19 j)) = some (g j))
    (hargs : ∀ j < n, Region.Disjoint ⟨t.ea (argAt 19 j), 4⟩ ⟨P, 76⟩) :
    ∀ c, c ≤ 18 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ u, Keeps [.eax, .ecx] t u → Frame [⟨P, 76⟩] t.mem u.mem →
        (∀ i < c, u.mem.readW (slotAddr P i) 32 = synth a g i) → WP isa (.block is) u Q) →
      WP isa (.block ((List.range c).flatMap (piece a) ++ is)) t Q
  | 0, _, _, _, k => k t (Keeps.refl _ _) (Frame.refl _ _) fun _ h => absurd h (by omega)
  | c + 1, hc, is, Q, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine fill_ok hb hP hesp hfr hr hargs c (by omega) fun u K F S => ?_
    have hr' : ∀ j < n, readSrc u (.mem (argAt 19 j)) = some (g j) := by
      intro j hj
      rw [← hr j hj]
      exact src_frame K (by decide) F fun r hr => by rw [List.mem_singleton.mp hr]; exact hargs j hj
    unfold piece
    rw [List.append_assoc]
    refine val_ok hb hr' c fun v Kv mv ev => ?_
    have Pv : (v.gpr .esp).setWidth 64 = P := by rw [Kv.1 _ (by decide), K.1 _ (by decide), hP]
    have ev' : (v.gpr .esp).toNat + 76 ≤ 2 ^ 32 := by rw [Kv.1 _ (by decide), K.1 _ (by decide)]; exact hesp
    have wv : (⟨P, 76⟩ : Region) ∈ v.wr := by rw [Kv.2.2, K.2.2]; exact hfr
    obtain ⟨ea, wr⟩ := frame76_store Pv ev' wv (i := c) (by omega)
    refine wp_storeS ea wr fun w M => ?_
    refine k w ((K.trans Kv).trans (M.keeps _)) ?_ fun i hi => ?_
    · rw [M.mem, mv]
      exact F.trans (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega)))
    · rw [M.mem, mv]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [frame76_other _ _ _ (by omega) (by omega) (by omega), S i hi]
      · rw [Mem.readW_writeW_self32, ev]

end

end VG.Proof.Ffdh.X86
