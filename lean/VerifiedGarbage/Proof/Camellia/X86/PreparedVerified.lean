module

public import VerifiedGarbage.Proof.Camellia.X86.PreparedBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Camellia.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
public import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Camellia.X86.PreparedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Camellia.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Camellia.X86.Crypt8
meta import VerifiedGarbage.Proof.Camellia.Words
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia's batches under prepared subkeys on x86 (32-bit) meet their contract

`crypt_correct`: `vg_camellia_crypt_prepared` meets `cryptX86`, with
`layout`. The function saves
the callee-saved registers in its slots (`saveAt_ok`), runs the eight blocks
of the tail buffer for 18 or 24 rounds (`crypt8_ok`) under the table its
working space holds, and restores the registers (`restoreAt_ok`): it writes
the slots below the table, the group's end's and its saved registers'
(`layout.cryptScratch`), and keeps every other. A batch's blocks are ECB in
the direction and under the subkeys of any words that the table encodes:
the run from it is the run from the words the precondition gives
(`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb argOp)
open VG.Proof.Camellia.Prepared (Holds Keeps)
open VG.Proof.Camellia (blockFn ecb_eq encryptWith_eq decryptWith_eq dirPerm dirPerm_lt)

theorem size_eq : layout.size = 4 * slots := rfl

/-- `vg_camellia_crypt_prepared` on x86: `rounds`, `ws` and `ws_len` on the stack. -/
def cryptX86 : Contract X86.isa where
  pre s :=
    let ws : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [ws] ∧ args.Disjoint ws ∧ ret.Disjoint ws ∧
      (arg s 1).toNat + (arg s 2).toNat * 8 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧
      ((arg s 0).toNat = 18 ∨ (arg s 0).toNat = 24) ∧ layout.size ≤ 8 * (arg s 2).toNat ∧
      ∃ w d, Holds layout s.mem ((arg s 1).setWidth 64) (arg s 0).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem ((arg s 1).setWidth 64) (arg s 0).toNat w d →
      Spec.Camellia.blocksAt s'.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (arg s 0).toNat w) d
          (Spec.Camellia.blocksAt s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps ((arg s 1).setWidth 64) (arg s 2).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains3 (s : State) (hfit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) {i : Nat} (hi : i < 3) :
    (⟨argAddr s 0, 12⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := setWidth_toNat (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- `mov eax, [esp + 4 + 4 i]; cmp eax, 18`. -/
theorem cmpArg_ok (s : State) (i : Nat) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 18)] s = some s' ∧
      s'.zf = some (s.mem.readW (s.ea (argOp i)) 32 - 18 == 0) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  let a := s₁.gpr .eax
  refine ⟨arithFlags s₁ (a - 18) (a.toNat < (18 : BitVec 32).toNat) (subOverflow a 18 (a - 18)), ?_,
    by rw [RegUpd.zf_arithFlags, show a = _ from v₁], fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr],
    by rw [RegUpd.mem_arithFlags, m₁], by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  rw [show ([.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 18)] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.alu .cmp .eax (.imm 18)] from rfl, runBlock_app, e₁, Option.bind_some]
  rfl

/-- The block function of a direction, as the eight-block code computes it. -/
theorem blockFn_words (d : Spec.Camellia.Direction) {R : Nat} (hR : R = 18 ∨ R = 24) (w : List (BitVec 64))
    (blk : Spec.Camellia.Block) :
    blockFn (Spec.Camellia.subkeysOfWords R w) d blk = Spec.Camellia.encodeBlock
      (cryptWords (R / 6) (fun i => w.getD (dirPerm d (R / 6) i) 0) (Spec.Camellia.decodeBlock blk)) := by
  cases d
  · rw [blockFn, Spec.Camellia.encryptBlock, encryptWith_eq hR]; rfl
  · rw [blockFn, Spec.Camellia.decryptBlock, decryptWith_eq hR]; rfl

/-- The table survives what keeps the words below the saved registers. -/
theorem words_congr {R : Nat} {m m' : Mem} {B : BitVec 32} {w : List (BitVec 64)} {d : Dir}
    (hR : R = 18 ∨ R = 24) (h : TableWordsAt R m B w d)
    (hk : ∀ k, keySlot ≤ k → k < savedSlot → m'.readW (wordAddr B k) 32 = m.readW (wordAddr B k) 32) :
    TableWordsAt R m' B w d := fun k h1 h2 => by
  have hg : R / 6 ≤ 4 := by omega
  rw [hk k h1 (by rw [savedSlot_eq]; rw [keySlot_eq] at h2; omega)]; exact h k h1 h2

/-- The regions the rounds write, within the functions' slots. -/
theorem ctxSub {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions B, Region.Sub r ⟨B.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by rw [keySlot_eq, slots_eq]; decide)
  · exact slot_sub hfit (by rw [grpSlot_eq, slots_eq]; decide)

/-- A byte of the working space below the saved registers, kept with their words. -/
theorem byte_keep {m m' : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32)
    (hk : ∀ k, k < savedSlot → m'.readW (wordAddr B k) 32 = m.readW (wordAddr B k) 32) {o : Nat}
    (ho : o < 4 * savedSlot) : m' (B.setWidth 64 + BitVec.ofNat 64 o) = m (B.setWidth 64 + BitVec.ofNat 64 o) := by
  have hs : o < 4 * slots := by rw [savedSlot_eq] at ho; rw [slots_eq]; omega
  rw [byte_word (m := m') hfit hs, byte_word (m := m) hfit hs, hk _ (by omega)]

theorem cryptPrepared_wp {s : State} (hp : cryptX86.pre s) {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hH : Holds layout s.mem ((arg s 1).setWidth 64) (arg s 0).toNat w d) :
    WP isa cryptPrepared s fun s' => abiPreserved s s' ∧
      Spec.Camellia.blocksAt s'.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (arg s 0).toNat w) d
          (Spec.Camellia.blocksAt s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 layout.buf) layout.blocks) ∧
      Keeps ((arg s 1).setWidth 64) (arg s 2).toNat layout.cryptScratch s.mem s'.mem := by
  obtain ⟨hrd, hwr, dAW, dRW, fitW, fitE, hR, hsz, -⟩ := hp
  rw [size_eq, slots_eq] at hsz
  have hfit : (arg s 1).toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
  have hsub : Region.Sub ⟨(arg s 1).setWidth 64, 4 * slots⟩ ⟨(arg s 1).setWidth 64, (arg s 2).toNat * 8⟩ :=
    Region.sub_prefix (by rw [slots_eq]; omega)
  have hwS : ScrIn s.wr (arg s 1) := ⟨⟨2 * (arg s 2).toNat, by rw [slots_eq]; omega, by omega,
    by rw [hwr, show 4 * (2 * (arg s 2).toNat) = (arg s 2).toNat * 8 by omega]; exact List.mem_singleton_self _⟩,
    hfit⟩
  have hrA : (⟨argAddr s 0, 12⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_singleton_self _
  have argIn : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → t.gpr .esp = s.gpr .esp → ∀ i < 3,
      InRegions (t.rd ++ t.wr) (t.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains3 s fitE hi⟩
  have hTW := words_of_holds hfit hR hH
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, k₁⟩ := saveAt_ok (j := cryptSavedSlot) (k := 1) (by decide) hwS
    (argIn rfl rfl rfl 1 (by decide)) (by rw [ea_arg rfl]; rfl)
  have k₁' : ∀ k, k < savedSlot → s₁.mem.readW (wordAddr (arg s 1) k) 32 = s.mem.readW (wordAddr (arg s 1) k) 32 :=
    fun k hk => k₁ k (by rw [savedSlot_eq] at hk; rw [slots_eq]; omega)
      (.inl (by rw [savedSlot_eq] at hk; rw [show cryptSavedSlot = 655 from rfl]; omega))
  have esp₁ : s₁.gpr .esp = s.gpr .esp := g₁ _ (by decide) (by decide)
  have argR₁ : s₁.mem.readW (argAddr s 0) 32 = arg s 0 :=
    f₁.readW (arg_contains3 s fitE (i := 0) (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAW.sub_right hsub) (by decide)
  obtain ⟨s₂, e₂, z₂, o₂, m₂, rd₂, wr₂⟩ := cmpArg_ok s₁ 0 (argIn rd₁ wr₁ esp₁ 0 (by decide))
  unfold cryptPrepared
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  have hz₂ : s₂.zf = some (decide ((arg s 0).toNat = 18)) := by
    rw [z₂, ea_arg esp₁, argR₁, show arg s 0 = BitVec.ofNat 32 (arg s 0).toNat by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have b₂ : s₂.gpr sb = arg s 1 := by rw [o₂ _ (by decide)]; exact b₁
  obtain ⟨g, hgR⟩ : ∃ g, (arg s 0).toNat / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  have hTW₂ : TableWordsAt (arg s 0).toNat s₂.mem (arg s 1) w (ofSpecDir d) := by
    rw [m₂]; exact words_congr hR hTW fun k _ hk => k₁' k hk
  have hcore : CorePre s₂ g (keyEntry w g (ofSpecDir d)) :=
    { scr := by rw [b₂, wr₂, wr₁]; exact hwS
      nk34 := by omega
      keys := fun i hi => by
        rw [b₂]; have := entries_of_words hTW₂ (e := i) (by omega); rw [hgR] at this; exact this
      hg := hg }
  refine WP.seq (WP.mono (M := isa) (Q := fun s' => Ctx s₂ s' ∧ ∀ b < 8, blk s' b =
      Spec.Camellia.encodeBlock (cryptWords g (keyEntry w g (ofSpecDir d)) (Spec.Camellia.decodeBlock (blk s₂ b))))
    (WP.ite (decide ((arg s 0).toNat = 18)) ((eval_e s₂).trans hz₂) (fun h => ?_) (fun h => ?_))
    fun s₃ ⟨c₃, bl₃⟩ => ?_)
  · obtain rfl : g = 3 := by simp at h; omega
    exact crypt8_ok hcore
  · obtain rfl : g = 4 := by simp at h; omega
    exact crypt8_ok hcore
  have base₃ : s₃.gpr sb = arg s 1 := by rw [c₃.base, b₂]
  have f₃ : Frame (ctxRegions (arg s 1)) s₂.mem s₃.mem := by have := c₃.frame; rw [b₂] at this; exact this
  have keep₃ : ∀ k, keySlot ≤ k → k < grpSlot →
      s₃.mem.readW (wordAddr (arg s 1) k) 32 = s₂.mem.readW (wordAddr (arg s 1) k) 32 :=
    fun k h1 h2 => slot_keep hfit (by decide) f₃ (ctx_disj hfit) h1 h2
  have keepHi₃ : ∀ k, grpSlot + 1 ≤ k → k < slots →
      s₃.mem.readW (wordAddr (arg s 1) k) 32 = s₂.mem.readW (wordAddr (arg s 1) k) 32 :=
    fun k h1 h2 => slot_keep hfit (Nat.le_refl _) f₃ (ctx_disj_hi hfit) h1 h2
  have sv₃ : SavedAt cryptSavedSlot s (arg s 1) s₃.mem := fun i hi => by
    rw [keepHi₃ _ (by rw [grpSlot_eq]; exact Nat.le_add_right _ _) (by rw [slots_eq]; show 655 + i < 672; omega), m₂]
    exact sv₁ i hi
  -- The epilogue.
  obtain ⟨s₄, e₄, rg₄, o₄, m₄, -, -⟩ := restoreAt_ok (s₀ := s) (b := arg s 1) (j := cryptSavedSlot) (by decide)
    (by rw [c₃.wr, wr₂, wr₁]; exact hwS) base₃ sv₃
  have fB : Frame [⟨(arg s 1).setWidth 64, 4 * slots⟩] s.mem s₄.mem := by
    rw [m₄]
    exact f₁.trans ((show Frame (ctxRegions (arg s 1)) s₁.mem s₃.mem by rw [← m₂]; exact f₃).sub fun r hr =>
      ⟨_, List.mem_singleton_self _, ctxSub hfit r hr⟩)
  have tail₂ : ∀ o < 4 * savedSlot,
      s₂.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 o) = s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 o) :=
    fun o ho => by rw [m₂]; exact byte_keep hfit k₁' ho
  refine WP.of_runBlock ⟨s₄, e₄, ⟨fun r hr => ?_, ?_⟩, ?_, fun i hi hout => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₄ 0 (by decide)
    · exact rg₄ 1 (by decide)
    · exact rg₄ 2 (by decide)
    · exact rg₄ 3 (by decide)
    · rw [o₄ _ (fun i hi => by revert i; decide), c₃.keep _ (by decide) (by decide), o₂ _ (by decide), esp₁]
  · exact fB.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRW.sub_right hsub) (by decide)
  · rw [ecb_eq]
    simp only [Spec.Camellia.blocksAt, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj8 : j < 8 := List.mem_range.mp hj
    have e5 := bl₃ j hj8
    simp only [blk, base₃, b₂] at e5
    simp only [Function.comp_apply, VG.Offset.add_add, layout, m₄]
    rw [e5, blockFn_words d hR, hgR]
    have hE : (fun i => w.getD (dirPerm d g i) 0) = keyEntry w g (ofSpecDir d) := by
      funext i; rw [keyEntry_eq]; cases d <;> rfl
    have hb : Spec.Camellia.blockAt s₂.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Spec.Camellia.blockAt s.mem ((arg s 1).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) := by
      apply Vector.ext; intro i hi
      simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn, VG.Offset.add_add]
      exact tail₂ _ (by rw [tailSlot_eq, savedSlot_eq]; omega)
    rw [hE, hb]
  · simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [keySlot_eq, grpSlot_eq] at hout
    by_cases hlo : i < 4 * slots
    · rw [m₄, byte_word (m := s₃.mem) hfit hlo, byte_word (m := s.mem) hfit hlo]
      rw [slots_eq] at hlo
      by_cases hg : i / 4 < grpSlot
      · rw [keep₃ _ (by rw [keySlot_eq]; omega) hg, m₂,
          k₁ _ (by rw [slots_eq]; omega) (.inl (by rw [grpSlot_eq] at hg; show _ < 655; omega))]
      · rw [keepHi₃ _ (by rw [grpSlot_eq] at hg ⊢; omega) (by rw [slots_eq]; omega), m₂,
          k₁ _ (by rw [slots_eq]; omega) (.inr (by rw [grpSlot_eq] at hg; show 655 + 4 ≤ _; omega))]
    · refine fB _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base _ (n := 1) (k := 4 * slots) (by rw [slots_eq] at hlo ⊢; omega)
        (by omega) _ (Region.contains_self _ _) hc

theorem crypt_correct (s : State) (hs : cryptX86.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptX86.post s s' := by
  obtain ⟨w₀, d₀, hH₀⟩ := hs.2.2.2.2.2.2.2.2
  obtain ⟨t, s', he, ha, -, hk⟩ := cryptPrepared_wp hs hH₀
  refine ⟨t, s', he, ha, fun w d hH => ?_, hk⟩
  obtain ⟨t₂, s₂, he₂, -, hb, -⟩ := cryptPrepared_wp hs hH
  obtain ⟨-, rfl⟩ := Exec.det he he₂
  exact hb

/-! ## Constant time -/

theorem crypt_noSp : NoSp cryptPrepared := NoSp.of_all (by lit_decide)

theorem crypt_stackUse : stackUse cryptPrepared = 0 := by lit_decide

end VG.Proof.Camellia.X86
