module

public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Group
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.AesCbc.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.Cmac.Mem

/-! ### `AesXts.AArch64.Aes.Setup`, which only this module used -/

section

/-!
# One-pass XTS-AES on AArch64: the setup

`enter_ok`: the arguments moved where the round code of
`vg_aes_encrypt_blocks_aes` expects them, and the tweak loaded into `x14` and
`x15`. `encSetup_ok`, `decSetup_ok`: the round keys loaded as `aes` and
`aesDec` need them (`Keys`, `DKeys`), as `Aese.encSetup_ok` and
`Aese.decSetup_ok` show for the block functions, from a state whose
schedule at `x0` is readable and `x3` the number of blocks: so `XInv … 0 0`
holds after `enter ++ setup` (`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt roundKey)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese (keysCommon encSetup decSetup kreg dreg)
open VG.Impl.AesXts.AArch64Aes (enter)

/-- What the key setups need of the state: the schedule at `x0` readable,
and `x1` a number of rounds. -/
structure KPre (s : State) : Prop where
  key_in : ∀ {o : Nat}, o + 16 ≤ 240 → InRegions (s.rd ++ s.wr) (bkp s + BitVec.ofNat 64 o) 16
  rounds : bnr s = 10 ∨ bnr s = 12 ∨ bnr s = 14

theorem common_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block keysCommon) s₀ (Common s₀) := by
  have hR := hp.rounds
  have hn : bnb s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (bnr s₀) := by simp [bnr]
  have hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (bnb s₀) := by simp [bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega_using [hj])) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) := by
    rw [g, g, Proof.Aes.AArch64.shl4]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega_using [hR])), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, f₁.rd, f₁.wr⟩
  · simp only [State.setV, State.write, (kreg_ne j).2, ite_false]
    rw [e₁ j hj]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx3]
    exact ushr3 (by omega_using [hn])
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

/-- What a key setup leaves. -/
structure KPost (K : Nat → List Byte → State → Prop) (s₀ s : State) : Prop where
  keys : K (bnr s₀) (bsch s₀) s
  x13 : s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem encSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block encSetup) s₀ (KPost Keys s₀) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  have e9' : bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) - BitVec.ofNat 64 16 =
      bkp s₀ + BitVec.ofNat 64 (16 * (bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega_using [hR]), show 16 * bnr s₀ - 16 = 16 * (bnr s₀ - 1) by omega_using []]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [hR])), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  refine ⟨⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega_using [hR, hj])]
    exact keyIs_readW _ _ (hL j (by omega_using [hj]))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega_using []))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]
  · simp only [State.setV, State.write, h1, ite_false]; exact c₁.gpr r h1 h2 h3 h4
  · simp only [State.setV, State.write, c₁.mem]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]

theorem decSetup_ok' {s₀ : State} (hp : KPre s₀) : WP isa (.block decSetup) s₀ (KPost DKeys s₀) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (common_ok' hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [])), WP.block_nil ?_⟩
  refine WP.mono (imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  have x0 : s₁.gpr .x0 = bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  have pre : ∀ j, 1 ≤ j → j ≤ 13 → j < bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (dreg j))
        (roundKey (bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (bkp s₀) (L := 16 * (bnr s₀ + 1)) (j := 13) (hL 13 (by omega_using [h3]))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega_using [h2, h13])]
      exact keyIs_readW _ _ (hL j (by omega_using [h3]))
  refine ⟨⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [o₂ _ fun j hj => (dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega_using [hR, h2]
    have := e₂ (j - 1) (by omega_using [hj13])
    rw [show j - 1 + 1 = j by omega_using [h1], ite_eq_left (by omega_using [hj13])] at this
    rw [this]
    exact keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega_using [])
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega_using []))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV, c₁.x13]
  · rw [g₂]; simp only [State.setV]; exact c₁.gpr r h1 h2 h3 h4
  · rw [m₂]; simp only [State.setV, c₁.mem]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]

end VG.Proof.AesXts.AArch64.Aes

end

end

/-! ### `AesXts.AArch64.Aes.Group8`, which only this module used -/

section

/-!
# One-pass XTS-AES on AArch64: the eight-block groups

The eight-block loop keeps `YInv B enc s₀ c`: after `c` blocks, as `XInv`
says of the data, the pointers and the round keys, but with the tweaks a
group ahead: those of blocks `c … c + 7` in the bank at `x12` (one of
`scratch` and `scratch + 128`, the other at `x8`), and that of block
`c + 8` in `x14` and `x15`. `blk8_ok`: a group takes it to `c + 8`, by
`preL_ok`, `gen_ok` (the next group's tweaks, into the bank at `x8`), `B.ok`
and `post_ok`, and swaps the banks; `start8_ok` and `end8_ok` go from and
back to `XInv`, and `loop8_ok` runs the loop.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0)
open VG.Proof.Aes.AArch64.Aese (BlockFn BlockRegs VFrame st ushr3 eval_zero eval_nonzero)
open VG.Impl.AesXts.AArch64Aes (preL gen post blk8 start8 end8)
open VG.Impl.Aes.AArch64.Aese (regs8)

/-- The bank at offset `e` of the scratch buffer. -/
abbrev bank (s₀ : State) (e : Nat) : Addr := S s₀ + BitVec.ofNat 64 e

/-- After `c` blocks, with the tweaks of blocks `c … c + 7` in the bank at
`x12`, `scratch + e`, and that of block `c + 8` in `x14` and `x15`. -/
structure YInv (B : BlockFn) (enc : Bool) (s₀ : State) (c e : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : B.K (R s₀) (wK s₀) s
  x2 : s.gpr .x2 = blk s₀ c
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - c)
  x5 : s.gpr .x5 = S s₀
  x11 : s.gpr .x11 = Iv s₀
  he : e = 0 ∨ e = 128
  x12 : s.gpr .x12 = bank s₀ e
  x8 : s.gpr .x8 = bank s₀ (128 - e)
  cur : ∀ j < 8, s.mem.readW (bank s₀ e + BitVec.ofNat 64 (16 * j)) 128 = twW (tw0 s₀) (c + j)
  tw : tweakOf s = twW (tw0 s₀) (c + 8)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀] s₀.mem s.mem
  data : ∀ k < N s₀, bytesAt s.mem (blk s₀ k) 16 =
    if k < c then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16

theorem banks_disj {s₀ : State} {e : Nat} (he : e = 0 ∨ e = 128) :
    Region.Disjoint ⟨bank s₀ e, 128⟩ ⟨bank s₀ (128 - e), 128⟩ :=
  Offset.disjoint _ (by omega_using [he]) (by omega_using [he]) (by omega_using [])

theorem bank_sub {s₀ : State} {e : Nat} (he : e = 0 ∨ e = 128) : Region.Sub ⟨bank s₀ e, 128⟩ (scrR s₀) :=
  Offset.sub_base _ (by omega_using [he])

theorem bank_slot {s₀ : State} {e j : Nat} (he : e = 0 ∨ e = 128) (hj : j < 8) :
    (scrR s₀).Contains (bank s₀ e + BitVec.ofNat 64 (16 * j)) 16 := by
  rw [bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he, hj]) (by omega_using [he, hj])

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem bank_toNat {e : Nat} (he : e = 0 ∨ e = 128) : (bank s₀ e).toNat + 128 ≤ 2 ^ 64 := by
  have := hp.scr_wrap
  rw [bank, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega_using [he]),
    Nat.mod_eq_of_lt (by omega_using [he, this])]
  omega_using [he, this]

theorem blk_bank {e k : Nat} (he : e = 0 ∨ e = 128) (hk : k < N s₀) :
    Region.Disjoint ⟨blk s₀ k, 16⟩ ⟨bank s₀ e, 128⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (bank_sub he)

end

/-- One group of eight blocks, and the banks swapped. -/
theorem blk8_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {c e : Nat}
    (hc : c + 8 ≤ N s₀) {s : State} (hI : YInv B enc s₀ c e s) :
    WP isa (blk8 B.f) s fun s' =>
      YInv B enc s₀ (c + 8) (128 - e) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((N s₀ - (c + 8)) / 8) := by
  have hbr : BlockRegs regs8 := ⟨by decide, by decide⟩
  have hbr31 : BlockRegs (regs8 ++ ([.v31] : List VReg)) := ⟨by decide, by decide⟩
  have h31 : VReg.v31 ∉ regs8 := by decide
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  have he := hI.he
  have hl : regs8.length = 8 := rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hI.rd, hW, hp.rd]; rfl
  have eb : ∀ k, blk s₀ c + BitVec.ofNat 64 (16 * (0 + k)) = blk s₀ (c + k) := fun k =>
    Offset.add_add_eq _ (by omega_arith)
  have ec : ∀ k, bank s₀ e + BitVec.ofNat 64 (16 * (0 + k)) = bank s₀ e + BitVec.ofNat 64 (16 * k) :=
    fun k => by rw [Nat.zero_add]
  have inD : ∀ k < 8, (dataR s₀).Contains (blk s₀ c + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by rw [eb]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The blocks loaded and the tweaks XORed in.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (preL_ok (blk s₀ c) (bank s₀ e) regs8 0 s hbr.1 h31 (by decide) hI.x2 hI.x12
    (fun k hk => ⟨dataR s₀, by rw [hR]; simp, inD k hk⟩)
    (fun k hk => ⟨scrR s₀, by rw [hR]; simp, by rw [ec]; exact bank_slot he hk⟩))
    fun s₁ ⟨v₁, o₁, g₁, m₁, sp₁, rd₁, wr₁⟩ => ?_
  -- The next group's tweaks, into the other bank.
  have hx8 : s₁.gpr .x8 = bank s₀ (128 - e) := by rw [g₁, hI.x8]
  have inN : ∀ d, d + 8 ≤ 128 → InRegions s₁.wr (bank s₀ (128 - e) + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨scrR s₀, by rw [wr₁, hW]; simp, by rw [bank, Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.mono (gen_ok .x8 (bank s₀ (128 - e)) (bank_toNat hp (by omega_arith)) (by decide) (by decide) (by decide)
    (by decide) s₁ hx8 inN 8 (Nat.le_refl _)) fun s₂ ⟨e₂, f₂, t₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_
  have hK₂ : B.K (R s₀) (wK s₀) s₂ := by
    have hK₁ := B.of_v hI.keys hbr31 (fun r hr => o₁ r (fun h => hr (List.mem_append_left _ h))
      (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _)))) (by rw [g₁]) (by rw [g₁])
    exact B.of_v hK₁ (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [v₂])
      (g₂ _ (by decide) (by decide) (by decide) (by decide)) (g₂ _ (by decide) (by decide) (by decide) (by decide))
  -- The rounds.
  refine WP.seq (WP.mono (B.ok hbr hK₂) fun s₃ ⟨e₃, f₃⟩ => ?_)
  have g₃ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₃.gpr, g₂ r h1 h2 h3 h4, g₁]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [f₃.wr, wr₂, wr₁, hW]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [f₃.rd, rd₂, rd₁, hW₃, hI.rd, hp.rd]; rfl
  -- The current bank, after the next one is written.
  have curB : ∀ j < 8, s₃.mem.readW (bank s₀ e + BitVec.ofNat 64 (16 * j)) 128 = twW (tw0 s₀) (c + j) :=
    fun j hj => by
      rw [f₃.mem, f₂.readW (r := ⟨bank s₀ e + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (banks_disj he).sub_left (Offset.sub_base _ (by omega_arith))) (by decide), m₁, hI.cur j hj]
  -- The tweaks XORed in again, the blocks stored, and the advance and swap.
  rw [WP.block_append_iff]
  refine WP.mono (post_ok .x12 (blk s₀ c) (bank s₀ e) (bank_toNat hp he) regs8 0 s₃ hbr.1 h31 (by decide)
    (by rw [hp.blk_toNat (k := c) (by omega_arith)]; omega_arith)
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hI.x2])
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hI.x12])
    (fun k hk => ⟨scrR s₀, by rw [hR₃]; simp, by rw [ec]; exact bank_slot he hk⟩)
    (fun k hk => ⟨dataR s₀, by rw [hW₃]; simp, inD k hk⟩)
    (fun k hk => by rw [eb]; exact blk_bank hp he (by omega_arith)))
    fun s₄ ⟨d₄, f₄, o₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  have g₄' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₄, g₃ r h1 h2 h3 h4]
  have tw₄ : tweakOf s₄ = twW (tw0 s₀) (c + 16) := by
    rw [tweakOf, g₄, f₃.gpr, ← tweakOf, t₂, tweakOf, g₁, ← tweakOf, hI.tw, twW_add]
  have hsl : Region.Sub ⟨bank s₀ (128 - e), 128⟩ (scrR s₀) := bank_sub (by omega_arith)
  have hdl : Region.Sub ⟨blk s₀ c + BitVec.ofNat 64 (16 * 0), 16 * regs8.length⟩ (dataR s₀) := by
    rw [Nat.mul_zero, BitVec.add_zero, blk]
    exact Offset.sub_base _ (show 16 * c + 16 * 8 ≤ 16 * N s₀ by omega_arith)
  -- The next bank, after the blocks are stored.
  have nxt : ∀ j < 8, s₄.mem.readW (bank s₀ (128 - e) + BitVec.ofNat 64 (16 * j)) 128 =
      twW (tw0 s₀) (c + 8 + j) := fun j hj => by
    rw [f₄.readW (r := ⟨bank s₀ (128 - e) + BitVec.ofNat 64 (16 * j), 16⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hp.data_scr.sub_left hdl).sub_right fun a h => hsl a (Offset.sub_base _ (by omega_arith) a h)).symm)
      (by decide), f₃.mem, e₂ j hj, tweakOf, g₁, ← tweakOf, hI.tw, twW_add]
  -- The data blocks.
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 =
      if k < c + 8 then outB enc s₀ k else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      have hi : i < regs8.length := by show i < 8; omega_arith
      have hd := d₄ i hi
      rw [eb] at hd
      rw [bytesAt_b16, hd, ec, curB i (by omega_arith)]
      have vi := v₁ i hi
      rw [eb, ec, hI.cur i (by omega_arith)] at vi
      have hc' : st (s₃.v regs8[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ twW (tw0 s₀) (c + i))) := by
        rw [e₃ _ (List.getElem_mem hi), v₂, vi, hF]
      rw [xts_word enc (R s₀) (wK s₀) _ _ _ hc', b16_twW, ← iv0_b16, ← bytesAt_b16, hI.data _ hk]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + 8 by omega_arith, ite_true]
    · rw [Proof.Cmac.bytesAt_frame16 f₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Nat.mul_zero, BitVec.add_zero, blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)),
        f₃.mem, Proof.Cmac.bytesAt_frame16 f₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact blk_bank hp (by omega_arith) hk), m₁, hI.data k hk]
      by_cases hkc : k < c
      · simp only [hkc, ite_true, show k < c + 8 by omega_arith]
      · simp only [hkc, ite_false, show ¬ k < c + 8 by omega_arith]
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hI.frame.trans ((?_ : Frame [dataR s₀, scrR s₀] s.mem s₂.mem).trans ?_)
    · rw [← m₁]
      exact f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsl⟩
    · rw [← f₃.mem]
      exact f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hdl⟩
  -- `add x2, 128`, `sub x3, 8`, `lsr x13`, and the banks swapped through `x10`.
  have h4 : BitVec.ofNat 64 (N s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_arith), show N s₀ - c - 8 = N s₀ - (c + 8) by omega_arith]
  have x2₄ : s₄.gpr .x2 = blk s₀ c := by rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x2]
  have x3₄ : s₄.gpr .x3 = BitVec.ofNat 64 (N s₀ - c) := by
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x3]
  have x12₄ : s₄.gpr .x12 = bank s₀ e := by rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x12]
  have x8₄ : s₄.gpr .x8 = bank s₀ (128 - e) := by
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x8]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), WP.block_nil ?_⟩
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, by omega_arith, ?_, ?_, fun j hj => ?_, ?_, rd₄.trans (f₃.rd.trans (rd₂.trans
    (rd₁.trans hI.rd))), wr₄.trans (f₃.wr.trans (wr₂.trans (wr₁.trans hI.wr))), fr, hdata⟩, ?_⟩
  · exact B.of_v (B.of_v hK₂ hbr f₃.v (by rw [f₃.gpr]) (by rw [f₃.gpr])) hbr31
      (fun r hr => o₄ r (fun h => hr (List.mem_append_left _ h))
        (fun h => hr (h ▸ List.mem_append_right _ (List.mem_singleton_self _))))
      (by simp [State.write, g₄]) (by simp [State.write, g₄])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x2₄]
    exact Offset.add_add_eq _ (by omega_arith)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x3₄]
    exact h4
  · simp only [State.write, reduceCtorEq, ite_false]
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x5]
  · simp only [State.write, reduceCtorEq, ite_false]
    rw [g₄' _ (by decide) (by decide) (by decide) (by decide), hI.x11]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x8₄,
      BitVec.add_zero]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x12₄,
      BitVec.add_zero]
    rw [show 128 - (128 - e) = e by omega_arith]
  · show s₄.mem.readW _ 128 = _
    rw [nxt j hj, Nat.add_right_comm]
  · rw [tweakOf]; simp only [State.write, reduceCtorEq, ite_false]; rw [← tweakOf, tw₄]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, x3₄]
    rw [h4, ushr3 (by omega_arith)]

/-- The banks set up, and the first group's tweaks stored. -/
theorem start8_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {s : State}
    (hI : XInv B enc s₀ 0 0 s) : WP isa (.block start8) s (YInv B enc s₀ 0 0) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hI.wr, hp.wr]
  rw [start8, List.cons_append, List.cons_append, List.nil_append]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  have x12₁ : ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).write .x .x8
      ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).read .x .x5 + BitVec.ofNat _ 128)).gpr .x12 =
      S s₀ := by simp [State.write, State.read, hI.x5]
  refine WP.mono (gen_ok .x12 (S s₀) (by omega_using [hsw]) (by decide) (by decide) (by decide) (by decide) _ x12₁
    (fun d hd => ⟨scrR s₀, by simp [State.write, hW], Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])⟩) 8
    (Nat.le_refl _)) fun s₂ ⟨e₂, f₂, t₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x14 → r ≠ .x15 → r ≠ .x12 → r ≠ .x8 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₂ r h1 h2 h3 h4]; simp [State.write, h5, h6]
  have tw₁ : tweakOf ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).write .x .x8
      ((s.write .x .x12 (s.read .x .x5 + BitVec.ofNat _ 0)).read .x .x5 + BitVec.ofNat _ 128)) =
      twW (tw0 s₀) 0 := by
    rw [← hI.tw]; simp [tweakOf, State.write]
  have hsub : Region.Sub ⟨S s₀, 128⟩ (scrR s₀) := Region.sub_prefix (by decide)
  refine ⟨Nat.zero_le _, ?_, by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x2],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x3],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.x11], .inl rfl,
    ?_, ?_, fun j hj => ?_, ?_, by rw [rd₂]; exact hI.rd, by rw [wr₂]; exact hI.wr, ?_, fun k hk => ?_⟩
  · exact B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => by rw [v₂]; rfl)
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  · rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; simp [State.write, State.read, hI.x5, bank]
  · rw [g₂ _ (by decide) (by decide) (by decide) (by decide)]; simp [State.write, State.read, hI.x5, bank]
  · rw [show bank s₀ 0 = S s₀ by simp [bank], e₂ j hj, tw₁, twW_add]
  · rw [t₂, tw₁, twW_add]
  · exact hI.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, hsub⟩)
  · rw [Proof.Cmac.bytesAt_frame16 f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right hsub)]
    exact hI.data k hk

/-- The tweak of the next block loaded back. -/
theorem end8_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {c e : Nat} {s : State}
    (hI : YInv B enc s₀ c e s) : WP isa (.block end8) s (XInv B enc s₀ c c) := by
  have hsw := hp.scr_wrap
  have he := hI.he
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hI.rd, hI.wr, hp.rd, hp.wr]; rfl
  have c0 : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 0) 8 :=
    ⟨scrR s₀, by rw [hR]; simp, by rw [hI.x12, bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he]) (by omega_using [he])⟩
  have c8 : InRegions (s.rd ++ s.wr) (s.gpr .x12 + BitVec.ofNat 64 8) 8 :=
    ⟨scrR s₀, by rw [hR]; simp, by rw [hI.x12, bank, Offset.add_add]; exact Offset.contains_base _ (by omega_using [he]) (by omega_using [he])⟩
  rw [end8, WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 0) (by decide) c0, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 8) (by decide) (by simpa [State.write] using c8), WP.block_nil ?_⟩
  have g : ∀ r, r ≠ .x14 → r ≠ .x15 → ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).write .x .x15
      ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).mem.readW
        ((s.write .x .x14 (s.mem.readW (s.gpr .x12 + BitVec.ofNat 64 0) 64)).gpr .x12 + BitVec.ofNat 64 8) 64)).gpr r =
      s.gpr r := fun r h1 h2 => by simp [State.write, h1, h2]
  refine ⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl)
      (g _ (by decide) (by decide)) (g _ (by decide) (by decide)),
    by rw [g _ (by decide) (by decide), hI.x2], by rw [g _ (by decide) (by decide), hI.x3],
    by rw [g _ (by decide) (by decide), hI.x5], by rw [g _ (by decide) (by decide), hI.x11], ?_,
    hI.rd, hI.wr, hI.frame, hI.data⟩
  have := hI.cur 0 (by decide)
  rw [Nat.mul_zero, Nat.add_zero, readW128, ← hI.x12] at this
  simp only [tweakOf, State.write, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, BitVec.add_zero]
  rw [BitVec.add_zero] at this
  exact this

/-- The eight-block loop, from the state after the setup. -/
theorem loop8_ok (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (hI₁ : XInv B enc s₀ 0 0 s₁) (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (N s₀ / 8)) :
    WP isa (.ite (.zero .x .x13) (.block [])
        (.seq (.block start8) (.seq (.loop (blk8 B.f) (.nonzero .x .x13)) (.block end8)))) s₁
      fun s => ∃ c, N s₀ - c < 8 ∧ XInv B enc s₀ c c s := by
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  refine WP.ite (decide (N s₀ / 8 = 0)) (eval_zero h13 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil ⟨0, by simp at h; omega_using [h], hI₁⟩
  · refine WP.seq (WP.mono (start8_ok B enc hp hI₁) fun s₂ h₂ => ?_)
    let I8 : Nat → State → Prop := fun m s => ∃ c e, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ YInv B enc s₀ c e s
    have hstep : ∀ m s, I8 m s → WP isa (blk8 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c e, N s₀ - c < 8 ∧ YInv B enc s₀ c e s') ∨
        (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
      rintro m s ⟨c, e, rfl, hc, hI⟩
      refine WP.mono (blk8_ok B enc hF hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
      rw [eval_nonzero h13' (by omega_using [hn])]
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp; omega_using [hlt], c + 8, 128 - e, hlt, hI'⟩
      · exact .inr ⟨by simp; omega_using [hlt], N s₀ - (c + 8), by omega_using [hc], c + 8, 128 - e, rfl, by omega_using [hlt], hI'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I8 hstep (N s₀) s₂ ⟨0, 0, rfl, by simp at h; omega_using [h], h₂⟩)
      fun s₃ ⟨c, e, hc, h₃⟩ => ?_)
    exact WP.mono (end8_ok B enc hp h₃) fun s₄ h₄ => ⟨c, hc, h₄⟩

end VG.Proof.AesXts.AArch64.Aes

end

end


/-!
# One-pass XTS-AES on AArch64: the whole function

`crypt_wp`: `crypt setup B.f` meets the contract of `vg_aes_xts_encrypt` (or
`vg_aes_xts_decrypt`) as `modeAArch64 (xtsMode enc)` states it, but for the
registers it preserves, when `setup` loads the round keys `B` needs
(`KPre`, `KPost`) and `B` computes the cipher (or its inverse) of the
direction: `enter` and `setup` reach `XInv … 0 0` (`setup_ok`), the
eight-block groups leave fewer than eight blocks (`loop8_ok`,
`Group8.lean`), the one-block loop the rest (`loop1_ok`), reaching
`XInv … N N`, and `finish` writes the tweak after the last block back
(`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (b16)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S schR ivR dataR scrR UPre blk wK iv0 modeAArch64 in_rw)
open VG.Proof.Aes.AArch64.Aese (BlockFn bkp bnr bnb bsch)
open VG.Impl.AesXts.AArch64Aes (enter finish crypt)

theorem enter_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block enter) s₀ fun s =>
      s.gpr .x11 = Iv s₀ ∧ s.gpr .x2 = Dp s₀ ∧ s.gpr .x3 = s₀.gpr .x4 ∧ tweakOf s = tw0 s₀ ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hiv := hp.iv_wrap
  have hW : s₀.rd ++ s₀.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hp.rd, hp.wr]; rfl
  rw [enter, WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 0) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (by simpa using Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_x (off := 8) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, Size.bits,
      BitVec.add_zero]
    rw [hW]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h2 h3 h11 h14 h15 => ?_, rfl, rfl, rfl⟩
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp [State.write, State.read]
  · simp only [tweakOf, State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq,
      BitVec.add_zero]
    exact (readW128 _ _).symm
  · simp [State.write, h2, h3, h11, h14, h15]

/-- `enter` and the key setup. -/
theorem setup_ok (B : BlockFn) (enc : Bool) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (enter ++ setup)) s₀ fun s =>
      XInv B enc s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (N s₀ / 8) := by
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp) fun s₁ ⟨x11, x2, x3, t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have hx0 : bkp s₁ = W s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx1 : bnr s₁ = R s₀ := by
    simp only [bnr, R]; rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have kp : KPre s₁ := ⟨fun ho => by
      rw [rd₁, wr₁, hx0, hp.rd]
      exact in_rw (by simp) (Offset.contains_base _ ho (by omega_using [ho])), by rw [hx1]; exact hp.rounds⟩
  refine WP.mono (hs s₁ kp) fun s₂ k₂ => ?_
  have g : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x11 → r ≠ .x14 → r ≠ .x15 → r ≠ .x9 → r ≠ .x6 → r ≠ .x7 →
      r ≠ .x13 → s₂.gpr r = s₀.gpr r := fun r h2 h3 h11 h14 h15 h9 h6 h7 h13 => by
    rw [k₂.gpr r h9 h6 h7 h13, g₁ r h2 h3 h11 h14 h15]
  have hsch : bsch s₁ = wK s₀ := by simp only [bsch, wK, hx0, hx1, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · rw [← hsch, ← hx1]; exact k₂.keys
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x2, blk, Nat.mul_zero, BitVec.add_zero]
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x3, Nat.sub_zero]
    exact Proof.AesCbc.AArch64.x4_ofNat s₀
  · exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · rw [k₂.gpr _ (by decide) (by decide) (by decide) (by decide), x11]
  · rw [tweakOf, k₂.gpr _ (by decide) (by decide) (by decide) (by decide),
      k₂.gpr _ (by decide) (by decide) (by decide) (by decide), ← tweakOf, t₁]; rfl
  · rw [k₂.rd, rd₁]
  · rw [k₂.wr, wr₁]
  · rw [k₂.mem, m₁]; exact Frame.refl _ _
  · rw [k₂.mem, m₁]; simp
  · rw [k₂.x13]; simp only [bnb, x3]

theorem getElem_tweaks (t : List Byte) {n k : Nat} (hk : k < n) :
    (Spec.Xts.tweaks t n)[k]'(by rw [AesXts.length_tweaks]; exact hk) = Spec.Xts.next t k := by
  induction n generalizing t k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Spec.Xts.tweaks, List.getElem_cons_succ]; rw [ih _ (by omega_using [hk]), AesXts.next_succ']

/-- The tweak after the last block written back. -/
theorem finish_ok (B : BlockFn) (enc : Bool) {s₀ : State} (hp : UPre s₀) {s : State}
    (h : XInv B enc s₀ (N s₀) (N s₀) s) :
    WP isa (.block finish) s fun s' => (modeAArch64 (AesXts.xtsMode enc)).post s₀ s' ∧
      s'.gpr = s.gpr ∧ s'.v = s.v := by
  have hiv := hp.iv_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [finish, WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 0) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide))), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_x (off := 8) (by decide) (by
    rw [hW, h.x11]; exact in_rw (r := ivR s₀) (by simp)
      (Offset.contains_base (Iv s₀) (d := 8) (n := 8) (k := 16) (by decide) (by decide))), WP.block_nil ?_⟩
  have fr : Frame [ivR s₀] s.mem ((s.mem.writeW (Iv s₀) (s.gpr .x14)).writeW (Iv s₀ + BitVec.ofNat 64 8)
      (s.gpr .x15)) := Proof.Cmac.frame_store2 _ _ _
  have hs : Mem.Sep (Iv s₀) (64 / 8) (Iv s₀ + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep (Iv s₀) (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩ <;> simp only [h.x11, BitVec.add_zero]
  · show Spec.Cbc.blocksAt _ (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    have hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      Proof.Cmac.bytesAt_frame16 fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm),
      h.data k hk]
    simp only [hk, ite_true]
  · show bytesAt _ (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
    rw [AesCbc.length_blocksAt, bytesAt_b16, readW128, Mem.readW_writeW_self64,
      Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64, ← tweakOf, h.tw, b16_twW,
      ← iv0_b16]

/-- The whole function, but for the registers it preserves. -/
theorem crypt_wp (B : BlockFn) (enc : Bool) (hF : B.F = stF enc) {setup : List Instr}
    (hs : ∀ s, KPre s → WP isa (.block setup) s (KPost B.K s)) {s₀ : State}
    (h0 : (modeAArch64 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt setup B.f) s₀ ((modeAArch64 (AesXts.xtsMode enc)).post s₀) := by
  have hp := UPre.of h0
  refine WP.seq (WP.mono (setup_ok B enc hs hp) fun s₁ ⟨hI₁, h13⟩ => ?_)
  refine WP.seq (WP.mono (loop8_ok B enc hF hp hI₁ h13) fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  refine WP.seq (WP.mono (loop1_ok B enc hF hp hc hI₂) fun s₃ hI₃ => ?_)
  exact WP.mono (finish_ok B enc hp hI₃) fun _ h => h.1

end VG.Proof.AesXts.AArch64.Aes
