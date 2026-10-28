module
public import VerifiedGarbage.Impl.Seed.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.Straight

import VerifiedGarbage.Proof.Seed.X86.Crypt8
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Slots, copies of blocks, and saving registers, on x86 (32-bit)

As for SM4 on x86 (`Proof/Sm4/X86/Copy.lean`, `Prologue.lean`): loads and
stores of the scratch buffer's slots through a base register
(`lptrSlot_ok`, `stSlot_ok`, and lists of them); `copyBlocks_wp`, the loop
copying `c ≥ 1` blocks of 16 bytes from `edx` to `ebx`; the prologue and
epilogue's saving and restoring of the callee-saved registers (`save_ok`,
`restore_ok`) in the slots from `savedSlot`; and the data loop's invariant
(`DInv`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt movS st movR argOp at_ addI subI)

theorem savedSlot_eq : savedSlot = 200 := rfl
theorem ptrSlot_eq : ptrSlot = 204 := rfl
theorem cntSlot_eq : cntSlot = 205 := rfl
theorem tableSlot_eq : tableSlot = 168 := rfl
theorem tableEnd_eq : tableEnd = 200 := rfl
theorem tailSlot_eq : tailSlot = 136 := rfl

/-! ## Addresses and memory -/

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega_arith

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [Offset.add_sub_add_left]; exact Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega_arith)

/-- A byte of a little-endian 32-bit word stored from a load. -/
theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl

/-- The scratch buffer at `b`, of `slots` slots or more (a mode keeps its
own after them), in the regions `rs`. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : ∃ n, slots ≤ n ∧ b.toNat + 4 * n ≤ 2 ^ 32 ∧ (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

/-- Slot `k` is in the scratch buffer. -/
theorem slot_inR {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := toNat_addr b
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A scratch buffer of exactly `slots` slots. -/
theorem ScrIn.exact {rs : List Region} {b : BitVec 32} (hr : (⟨b.setWidth 64, 4 * slots⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) : ScrIn rs b := ⟨⟨slots, Nat.le_refl _, hfit, hr⟩, hfit⟩

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  slot_inR hr hf (Nat.lt_of_lt_of_le hk hn)

theorem ldArg_ok (s : State) (d : Reg) (i : Nat) (h : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov d (.mem (argOp i))] s = some s' ∧ s'.gpr d = s.mem.readW (s.ea (argOp i)) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.ea (argOp i)) 32), by
    rw [runBlock_cons, show exec (.mov d (.mem (argOp i))) s = some (s.setReg d (s.mem.readW (s.ea (argOp i)) 32)) by
      simp [exec, readSrc, State.load32, h], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-! ## Copying blocks -/

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `mov eax, [sr + so + 16 j + d]; mov [dr + dd + 16 j + d], eax`: the
copy's next word, from the `c` blocks at `A` (`sr` plus `so`) to those at `B`
(`dr` plus `dd`). -/
theorem moveWord_ok {sr dr : Reg} {X Y : BitVec 32} {so dd c : Nat} {s₀ s : State} {j d : Nat}
    (hdr : dr ≠ .eax) (hd : d < 16) (hd4 : d % 4 = 0) (hj : j < c)
    (hfX : X.toNat + so + 16 * c ≤ 2 ^ 32) (hfY : Y.toNat + dd + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨X.setWidth 64 + BitVec.ofNat 64 so, 16 * c⟩ ⟨Y.setWidth 64 + BitVec.ofNat 64 dd, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (Y.setWidth 64 + BitVec.ofNat 64 dd + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr sr = X) (h1 : s.gpr dr = Y)
    (hi : Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ sr (so + 16 * j + d))), .store (at_ dr (dd + 16 * j + d)) .eax] s =
        some s' ∧
      Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have eA : s.ea (at_ sr (so + 16 * j + d)) = X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 (16 * j + d) := by
    rw [at_, ea_mk, h0, addr_eq (by omega_arith), Offset.add_add, Nat.add_assoc]
  let s₁ := s.setReg .eax (s.mem.readW (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 (16 * j + d)) 32)
  have eB : s₁.ea (at_ dr (dd + 16 * j + d)) = Y.setWidth 64 + BitVec.ofNat 64 dd + BitVec.ofNat 64 (16 * j + d) := by
    rw [at_, ea_mk]
    rw [show s₁.gpr dr = s.gpr dr from RegUpd.gpr_setReg_of_ne _ _ hdr, h1, addr_eq (by omega_arith),
      Offset.add_add, Nat.add_assoc]
  let m' := s.mem.writeW (Y.setWidth 64 + BitVec.ofNat 64 dd + BitVec.ofNat 64 (16 * j + d)) (s.mem.readW (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 (16 * j + d)) 32)
  refine ⟨{ s₁ with mem := m' }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  · rw [runBlock_cons, show exec (.mov .eax (.mem (at_ sr (so + 16 * j + d)))) s = some s₁ by
        simp [exec, readSrc, State.load32, eA, hr, s₁], runStep_some, runBlock_cons]
    simp only [exec, State.store32, eB, show s₁.wr = s.wr from rfl, hw, ↓reduceIte, runStep_some, runBlock_nil,
      s₁, RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega_arith
    have hAs : ∀ t < 16 * c, s.mem (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 t) = s₀.mem (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨X.setWidth 64 + BitVec.ofNat 64 so, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega_arith) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_arith)]; omega_arith), off_sub_toNat _ h8 (by omega_arith),
        Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega_arith, hAs t (by omega_arith)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
      exact hi.copied t (by omega_arith)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega_arith) _
        (by simp only [Region.Contains]; omega_arith))]

/-- `blockMove sr dr so dd j`: block `j` of the copy. -/
theorem blockMove_ok {sr dr : Reg} {X Y : BitVec 32} {so dd c : Nat} {s₀ s : State} {j : Nat}
    (hsr : sr ≠ .eax) (hdr : dr ≠ .eax) (hj : j < c)
    (hfX : X.toNat + so + 16 * c ≤ 2 ^ 32) (hfY : Y.toNat + dd + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨X.setWidth 64 + BitVec.ofNat 64 so, 16 * c⟩ ⟨Y.setWidth 64 + BitVec.ofNat 64 dd, 16 * c⟩)
    (hr : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 t) 4)
    (hw : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (Y.setWidth 64 + BitVec.ofNat 64 dd + BitVec.ofNat 64 t) 4)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (h0 : s.gpr sr = X) (h1 : s.gpr dr = Y)
    (hi : Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * j) s) :
    ∃ s', runBlock isa (blockMove sr dr so dd j) s = some s' ∧
      Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * (j + 1)) s' ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have step : ∀ w < 4, ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr sr = X → s.gpr dr = Y →
      Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * j + 4 * w) s →
      ∃ s', runBlock isa [.mov .eax (.mem (at_ sr (so + 16 * j + 4 * w))), .store (at_ dr (dd + 16 * j + 4 * w)) .eax] s =
          some s' ∧
        Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * j + 4 * w + 4) s' ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    fun w hw' {s} e1 e2 e3 e4 h => moveWord_ok hdr (by omega_arith) (by omega_arith) hj hfX hfY hsep
      (by rw [e1, e2]; exact hr _ (by omega_arith) (by omega_arith)) (by rw [e2]; exact hw _ (by omega_arith) (by omega_arith))
      e3 e4 h
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁⟩ := step 0 (by decide) hrd hwr h0 h1 (by simpa using hi)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂⟩ := step 1 (by decide) (rd₁.trans hrd) (wr₁.trans hwr)
    (by rw [g₁ _ hsr, h0]) (by rw [g₁ _ hdr, h1]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃⟩ := step 2 (by decide) (rd₂.trans (rd₁.trans hrd)) (wr₂.trans (wr₁.trans hwr))
    (by rw [g₂ _ hsr, g₁ _ hsr, h0]) (by rw [g₂ _ hdr, g₁ _ hdr, h1]) (by simpa using c₂)
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄⟩ := step 3 (by decide) (rd₃.trans (rd₂.trans (rd₁.trans hrd)))
    (wr₃.trans (wr₂.trans (wr₁.trans hwr))) (by rw [g₃ _ hsr, g₂ _ hsr, g₁ _ hsr, h0])
    (by rw [g₃ _ hdr, g₂ _ hdr, g₁ _ hdr, h1]) (by simpa using c₃)
  refine ⟨s₄, ?_, by simpa [Nat.mul_add] using c₄, fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr],
    by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rw [show blockMove sr dr so dd j =
      [.mov .eax (.mem (at_ sr (so + 16 * j + 4 * 0))), .store (at_ dr (dd + 16 * j + 4 * 0)) .eax] ++
      ([.mov .eax (.mem (at_ sr (so + 16 * j + 4 * 1))), .store (at_ dr (dd + 16 * j + 4 * 1)) .eax] ++
      ([.mov .eax (.mem (at_ sr (so + 16 * j + 4 * 2))), .store (at_ dr (dd + 16 * j + 4 * 2)) .eax] ++
      [.mov .eax (.mem (at_ sr (so + 16 * j + 4 * 3))), .store (at_ dr (dd + 16 * j + 4 * 3)) .eax])) from rfl,
    runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
    Option.bind_some, e₄]

/-- The copy's guarded blocks from `j` on, of `k`, with `ecx = c`: block `j`
when `j < c`. -/
theorem guardedFrom_wp {sr dr : Reg} {X Y : BitVec 32} {so dd c : Nat} {s₀ : State}
    (hsr : sr ≠ .eax) (hdr : dr ≠ .eax) (hsc : sr ≠ .ecx) (hdc : dr ≠ .ecx) (hc : c < 2 ^ 32)
    (hfX : X.toNat + so + 16 * c ≤ 2 ^ 32) (hfY : Y.toNat + dd + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨X.setWidth 64 + BitVec.ofNat 64 so, 16 * c⟩ ⟨Y.setWidth 64 + BitVec.ofNat 64 dd, 16 * c⟩)
    (hr : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (X.setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 t) 4)
    (hw : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (Y.setWidth 64 + BitVec.ofNat 64 dd + BitVec.ofNat 64 t) 4) :
    ∀ (k j : Nat) (s : State), j + k < 2 ^ 32 → s.rd = s₀.rd → s.wr = s₀.wr → s.gpr sr = X → s.gpr dr = Y →
      s.gpr .ecx = BitVec.ofNat 32 c → (∀ r, r ≠ .eax → s.gpr r = s₀.gpr r) →
      Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * min j c) s →
      WP isa (guardedFrom (blockMove sr dr so dd) j k) s fun s' =>
        Copied (X.setWidth 64 + BitVec.ofNat 64 so) (Y.setWidth 64 + BitVec.ofNat 64 dd) c s₀ (16 * min (j + k) c) s' ∧
        (∀ r, r ≠ .eax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr
  | 0, j, s, _, hrd, hwr, _, _, _, hg, hi => WP.block_nil ⟨by simpa using hi, hg, hrd, hwr⟩
  | k + 1, j, s, hjk, hrd, hwr, h0, h1, hcx, hg, hi => by
    rw [show j + (k + 1) = j + 1 + k by omega_arith]
    let s₁ := arithFlags s (s.gpr .ecx - BitVec.ofNat 32 (j + 1)) ((s.gpr .ecx).toNat < (BitVec.ofNat 32 (j + 1)).toNat)
      (subOverflow (s.gpr .ecx) (BitVec.ofNat 32 (j + 1)) (s.gpr .ecx - BitVec.ofNat 32 (j + 1)))
    have cf₁ : s₁.cf = some (decide (c < j + 1)) := by
      rw [RegUpd.cf_arithFlags, hcx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
        Nat.mod_eq_of_lt (by omega_arith)]
    refine WP.seq (WP.of_runBlock ⟨s₁, rfl, WP.seq ?_⟩)
    have g₁ : s₁.gpr = s.gpr := rfl
    refine WP.ite (decide (c < j + 1)) ((eval_b s₁).trans cf₁) (fun h => ?_) (fun h => ?_)
    · refine WP.block_nil (guardedFrom_wp hsr hdr hsc hdc hc hfX hfY hsep hr hw k (j + 1) s₁ (by omega_arith)
        hrd hwr h0 h1 hcx hg ?_)
      have : min (j + 1) c = min j c := by simp at h; omega_arith
      rw [this]; exact ⟨hi.copied, hi.frame⟩
    · have hj : j < c := by simp at h; omega_arith
      have hmj : min j c = j := by omega_arith
      rw [hmj] at hi
      obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂⟩ := blockMove_ok (s := s₁) hsr hdr hj hfX hfY hsep hr hw hrd hwr
        h0 h1 ⟨hi.copied, hi.frame⟩
      refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
      refine guardedFrom_wp hsr hdr hsc hdc hc hfX hfY hsep hr hw k (j + 1) s₂ (by omega_arith)
        (by rw [rd₂]; exact hrd) (by rw [wr₂]; exact hwr) ((g₂ _ hsr).trans h0) ((g₂ _ hdr).trans h1)
        ((g₂ _ (by decide)).trans hcx) (fun r hr => (g₂ r hr).trans (hg r hr)) ?_
      rw [show min (j + 1) c = j + 1 by omega_arith]; exact c₂

/-! ## Slots -/

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
  rw [slot_addr (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-- `mov d, [n + 4 k]`, `n` holding `b`, a slot of the scratch buffer. -/
theorem lptrSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (hw.slot hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, `n` holding `b`, a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, hw.slot hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .store (slotAt n x.1) x.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .mov x.1 (.mem (slotAt n x.2))) s = some s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := lptrSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .ebx

theorem savedRegs_eq : savedRegs = (List.range 4).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : BitVec 32} {k : Nat} (hw : ScrIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegs k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Saved s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax k ha
  rw [hb] at v₁
  let L : List (Nat × Reg) := (List.range 4).map fun i => (savedSlot + i, sreg i)
  have hL : savedRegs.map (fun (r, j) => Instr.store (slotAt .eax j) r) =
      L.map fun x => .store (slotAt .eax x.1) x.2 := by
    rw [savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 4).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, o₂, v₂⟩ := stW_list_ok .eax L s₁ v₁ (by rw [wr₁]; exact hw)
    (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega_arith)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, -, -⟩ := movR_ok s₂ .edi .eax
  refine ⟨s₃, ?_, by rw [r₃, g₂, v₁], fun r h0 h7 => by rw [o₃ r h7, g₂, o₁ r h0], fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, ← m₁]; exact f₂, fun j hj => ?_⟩
  · rw [saveRegs, runBlock_append, runBlock_append, e₁, Option.bind_some, hL, e₂, Option.bind_some, e₃]
  · rw [m₃, v₂ (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩),
      o₁ _ (by revert i; decide)]
  · rw [m₃, o₂ j ?_ (by rw [savedSlot_eq] at hj; rw [slots_eq]; omega_arith), m₁]
    rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_arith

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .edi = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.ebx, savedSlot), (.esi, savedSlot + 1), (.ebp, savedSlot + 3)]
  obtain ⟨s₁, e₁, m₁, rd₁, wr₁, o₁, v₁⟩ := ldW_list_ok .edi L s hb hw (by decide) (by decide)
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only [savedSlot_eq, slots_eq] <;> omega_arith)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := lptrSlot_ok s₁ .edi .edi (k := savedSlot + 2)
    (by rw [o₁ _ (by decide), hb]) (by rw [savedSlot_eq, slots_eq]; omega_arith) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show restoreRegs = (L.map fun x => .mov x.1 (.mem (slotAt .edi x.2))) ++
        [.mov .edi (.mem (slotAt .edi (savedSlot + 2)))] from rfl, runBlock_append, e₁, Option.bind_some, e₂]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show s₂.gpr .ebx = _
      rw [o₂ _ (by decide), v₁ (.ebx, savedSlot) (by simp [L])]; exact hs 0 (by decide)
    · show s₂.gpr .esi = _
      rw [o₂ _ (by decide), v₁ (.esi, savedSlot + 1) (by simp [L])]; exact hs 1 (by decide)
    · rw [show sreg 2 = .edi from rfl, v₂, m₁]; exact hs 2 (by decide)
    · show s₂.gpr .ebp = _
      rw [o₂ _ (by decide), v₁ (.ebp, savedSlot + 3) (by simp [L])]; exact hs 3 (by decide)
  · rw [o₂ r (hr 2 (by decide)), o₁ r (by
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 3 (by decide)⟩)]

/-- `restoreBE`: `ebx` and `edi` from their slots. -/
theorem restoreBE_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .edi = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreBE s = some s' ∧ s'.gpr .ebx = s₀.gpr .ebx ∧ s'.gpr .edi = s₀.gpr .edi ∧
      (∀ r, r ≠ .ebx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := lptrSlot_ok s .ebx .edi (k := savedSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := lptrSlot_ok s₁ .edi .edi (k := savedSlot + 2)
    (by rw [o₁ _ (by decide), hb]) (by decide) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, ?_, ?_, fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], by rw [m₂, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  · rw [show restoreBE = [.mov .ebx (.mem (slotAt .edi savedSlot))] ++
        [.mov .edi (.mem (slotAt .edi (savedSlot + 2)))] from rfl, runBlock_append, e₁, Option.bind_some, e₂]
  · rw [o₂ _ (by decide), v₁]; exact hs 0 (by decide)
  · rw [v₂, m₁]; exact hs 2 (by decide)

/-! ## The data -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Seed.Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Seed.Block}
    (h : DInv m₀ m D n n F) : Spec.Seed.blocksAt m D n = (List.range n).map F := by
  simp only [Spec.Seed.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (by omega_arith), show (16 * j + t) / 16 = j by omega_arith,
    show (16 * j + t) % 16 = t by omega_arith]
  simp [Vector.getD, ht]

end VG.Proof.Seed.X86
