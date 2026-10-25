module

public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Pre
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.AArch64.Loop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# One-pass XTS-AES on AArch64: a group of blocks

The loops keep `XInv B enc s₀ c p`: after `c` blocks, with the data pointer
and the number of blocks left at block `p` (`p = c` but between a group and
its advance), the tweak of block `c` in `x14` and `x15` (`twW`), the round
keys as `B` needs them, and the first `c` data blocks replaced with their
XTS (`outB`), the others as they were. `group_ok`: a group of blocks
(`[v0]`, after the eight-block groups of `Group8.lean`) through `B` takes it
from `c` to `c + N`, by `pre_ok`, `B.ok` and `post_ok`; `xts_word` gives
each block.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese (BlockFn BlockRegs VFrame st)
open VG.Impl.AesXts.AArch64Aes (pre post blk1)
open VG.Proof.Aes.AArch64.Aese (ushr3 eval_zero eval_nonzero)
open VG.Impl.Aes.AArch64.Aese (regs8)

/-- The tweak at the start, as a word. -/
abbrev tw0 (s₀ : State) : BitVec 128 := s₀.mem.readW (Iv s₀) 128

/-- Block `k` after XTS. -/
abbrev outB (enc : Bool) (s₀ : State) (k : Nat) : List Byte :=
  Spec.Xts.block (ciphOf enc (R s₀) (wK s₀)) (Spec.Xts.next (iv0 s₀) k) (bytesAt s₀.mem (blk s₀ k) 16)

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure XInv (B : BlockFn) (enc : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : B.K (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ p
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - p)
  x5 : s.gpr .x5 = S s₀
  x11 : s.gpr .x11 = Iv s₀
  tw : tweakOf s = twW (tw0 s₀) c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 =
    if k < c then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16

theorem twW_add (t : BitVec 128) (c : Nat) : ∀ k, twW (twW t c) k = twW t (c + k)
  | 0 => rfl
  | k + 1 => by rw [twW_succ, twW_add t c k, ← twW_succ]; rfl

theorem iv0_b16 (s₀ : State) : iv0 s₀ = b16 (tw0 s₀) := bytesAt_b16 _ _

theorem bregs (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) :
    BlockRegs rs ∧ .v31 ∉ rs ∧ rs.length ≤ 8 ∧ BlockRegs (rs ++ ([.v31] : List VReg)) := by
  rcases h with rfl | rfl <;> exact ⟨⟨by decide, by decide⟩, by decide, by decide, ⟨by decide, by decide⟩⟩

/-- Blocks `c … c + N − 1` (`N` the number of registers) through `B`, the
pointer not yet advanced. -/
theorem group_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀)
    (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0]) (adv : List Instr) {Q : State → Prop} {c : Nat}
    (hc : c + rs.length ≤ N s₀) {s : State} (hI : XInv B enc s₀ c c s)
    (hQ : ∀ s', XInv B enc s₀ (c + rs.length) c s' → WP isa (.block adv) s' Q) :
    WP isa (.seq (.block (pre rs 0)) (.seq (B.f rs) (.block (post .x5 rs 0 ++ adv)))) s Q := by
  obtain ⟨hbr, h31, hlen, hbr31⟩ := bregs rs hrs
  have hdw := hp.data_wrap
  have hpos : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hsw := hp.scr_wrap
  have hW : s.wr = [Iv s₀ |> fun a => (⟨a, 16⟩ : Region), dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  have eb : ∀ k, blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)) = blk s₀ (c + k) := fun k =>
    Offset.add_add_eq _ (by omega_arith)
  have inD : ∀ k < rs.length, (dataR s₀).Contains (blk s₀ c + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by rw [eb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have inS : ∀ k < rs.length, (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => Offset.contains_base _ (by omega_arith) (by omega_arith)
  have dS : ∀ k < rs.length, Region.Disjoint ⟨blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)), 16⟩ ⟨S s₀, 128⟩ :=
    fun k hk => by
      rw [eb]
      exact (hp.data_scr.sub_left (UPre.data_sub (by omega_arith))).sub_right (Region.sub_prefix (by decide))
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (pre_ok (blk s₀ c) (S s₀) (by omega_arith) rs 0 s hbr.1 h31 (by omega_arith) hI.x2 hI.x5
    (fun k hk => ⟨dataR s₀, by rw [hW]; simp, inD k hk⟩)
    (fun k hk => ⟨scrR s₀, by rw [hW]; simp, inS k hk⟩) dS)
    fun s₁ ⟨v₁, m₁, f₁, t₁, o₁, g₁, sp₁, rd₁, wr₁⟩ => ?_)
  have hK₁ := B.of_v hI.keys hbr31 (fun r hr => o₁ r (fun h => hr (List.mem_append_left _ h))
    (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _))))
    (g₁ _ (by decide) (by decide) (by decide) (by decide)) (g₁ _ (by decide) (by decide) (by decide) (by decide))
  -- The rounds.
  refine WP.seq (WP.mono (B.ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The tweaks XORed in again, and the blocks stored.
  rw [WP.block_append_iff]
  have g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂.gpr, g₁ r h1 h2 h3 h4]
  have hW₂ : s₂.wr = [Iv s₀ |> fun a => (⟨a, 16⟩ : Region), dataR s₀, scrR s₀] := by rw [f₂.wr, wr₁, hW]
  refine WP.mono (post_ok .x5 (blk s₀ c) (S s₀) (by omega_arith) rs 0 s₂ hbr.1 h31 (by omega_arith)
    (by rw [hp.blk_toNat (k := c) (by omega_arith)]; omega_arith)
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hI.x2])
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), hI.x5])
    (fun k hk => ⟨scrR s₀, by rw [f₂.rd, rd₁, hI.rd, hp.rd, hW₂]; simp, inS k hk⟩)
    (fun k hk => ⟨dataR s₀, by rw [hW₂]; simp, inD k hk⟩) dS)
    fun s₃ ⟨d₃, f₃, o₃, g₃, sp₃, rd₃, wr₃⟩ => hQ s₃ ?_
  have g₃' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃, g₂ r h1 h2 h3 h4]
  have m₂ : s₂.mem = s₁.mem := f₂.mem
  have tw₃ : tweakOf s₃ = twW (tw0 s₀) (c + rs.length) := by
    rw [tweakOf, g₃, f₂.gpr, ← tweakOf, t₁, hI.tw, twW_add]
  have hsl : Region.Sub ⟨S s₀ + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩ (scrR s₀) :=
    UPre.scr_sub (by omega_arith)
  have hdl : Region.Sub ⟨blk s₀ c + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩ (dataR s₀) := by
    rw [Nat.mul_zero, BitVec.add_zero, blk]
    exact Offset.sub_base _ (by omega_arith)
  refine ⟨by omega_arith, ?_, by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x2],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x3],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x5],
    by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), hI.x11], tw₃,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr], ?_, fun k hk => ?_⟩
  · exact B.of_v (B.of_v hK₁ hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])) hbr31
      (fun r hr => o₃ r (fun h => hr (List.mem_append_left _ h))
        (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _)))) (by rw [g₃]) (by rw [g₃])
  · refine hI.frame.trans ((f₁.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsl⟩
    · rw [← m₂]
      exact f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hdl⟩
  · by_cases hin : c ≤ k ∧ k < c + rs.length
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      have hi : i < rs.length := by omega_arith
      have e := d₃ i hi
      rw [eb] at e
      rw [bytesAt_b16, e, m₂]
      have mi := m₁ i hi
      rw [hI.tw, twW_add] at mi
      rw [mi]
      have vi := v₁ i hi
      rw [eb, hI.tw, twW_add] at vi
      have hc' : st (s₂.v rs[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ twW (tw0 s₀) (c + i))) := by
        rw [e₂ _ (List.getElem_mem hi), vi, hF]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', b16_twW, ← iv0_b16, ← bytesAt_b16, hI.data _ hk]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + rs.length by omega_arith, ite_true]
    · have hk' : ¬ (c ≤ k ∧ k < c + rs.length) := hin
      rw [Proof.Cmac.bytesAt_frame16 f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Nat.mul_zero, BitVec.add_zero, blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        m₂, Proof.Cmac.bytesAt_frame16 f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right hsl), hI.data k hk]
      by_cases hkc : k < c
      · simp only [hkc, ite_true, show k < c + rs.length by omega_arith]
      · simp only [hkc, ite_false, show ¬ k < c + rs.length by omega_arith]


/-! ## The loops -/

/-- `s'` is `s` but for `x2`, `x3` and `x13`. -/
theorem XInv.adv {B : BlockFn} {enc : Bool} {s₀ : State} {c p : Nat} {s s' : State}
    (h : XInv B enc s₀ c p s) (p' : Nat) (hx2 : s'.gpr .x2 = blk s₀ p')
    (hx3 : s'.gpr .x3 = BitVec.ofNat 64 (N s₀ - p'))
    (g : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x13 → s'.gpr r = s.gpr r) (hv : s'.v = s.v) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : XInv B enc s₀ c p' s' :=
  ⟨h.le, B.of_v h.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [hv])
      (g _ (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide)),
    hx2, hx3, by rw [g _ (by decide) (by decide) (by decide), h.x5],
    by rw [g _ (by decide) (by decide) (by decide), h.x11],
    by rw [tweakOf, g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide)]; exact h.tw,
    by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hm]; exact h.frame, fun k hk => by rw [hm]; exact h.data k hk⟩

theorem blk1_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c : Nat}
    (hc : c + 1 ≤ N s₀) {s : State} (hI : XInv B enc s₀ c c s) :
    WP isa (blk1 B.f) s (XInv B enc s₀ (c + 1) (c + 1)) := by
  have hn := hp.data_wrap
  refine group_ok B enc hF hp [.v0] (.inr rfl) _ hc hI fun s₁ h₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine h₁.adv (c + 1) ?_ ?_ (fun r h2 h3 _ => by simp [State.write, h2, h3]) rfl rfl rfl rfl
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, h₁.x2]
    exact Offset.add_add_eq _ (by omega_arith)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, h₁.x3]
    rw [Offset.ofNat_sub_ofNat (by omega_arith), show N s₀ - c - 1 = N s₀ - (c + 1) by omega_arith]

/-- The one-block loop, for the fewer than eight blocks left. -/
theorem loop1_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c : Nat}
    {s₂ : State} (hc : N s₀ - c < 8) (hI₂ : XInv B enc s₀ c c s₂) :
    WP isa (.ite (.zero .x .x3) (.block []) (.loop (blk1 B.f) (.nonzero .x .x3))) s₂
      (XInv B enc s₀ (N s₀) (N s₀)) := by
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  refine WP.ite (decide (N s₀ - c = 0)) (eval_zero hI₂.x3 (by omega_arith)) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₂.le; simp at h; omega_arith
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ XInv B enc s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blk1 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x3) s' = some false ∧ XInv B enc s₀ (N s₀) (N s₀) s') ∨
        (AArch64.eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (blk1_ok B enc hF hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x3 (by omega_arith)]
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_arith
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], N s₀ - (c + 1), by omega_arith, c + 1, rfl, by omega_arith, hI'⟩
    have hlt : c < N s₀ := by have := hI₂.le; simp at h; omega_arith
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

end VG.Proof.AesXts.AArch64.Aes
