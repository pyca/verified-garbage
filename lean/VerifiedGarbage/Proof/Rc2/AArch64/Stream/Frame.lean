module

public import VerifiedGarbage.Proof.Rc2.AArch64.Key
public import VerifiedGarbage.Impl.Rc2.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Stream
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Copy
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.ConstantTime
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Spec.Rc2.Contract

/-! ### `Rc2.AArch64.Stream.Contract`, which only this module used -/

section

/-! # Streaming RC2-CBC on AArch64: the contracts the proofs use

`Spec.Rc2.cbcInitContract` spelled out for AArch64 (the arguments in
`x0`–`x6`), with the 16-byte frame below the stack pointer that saves `x30`
around the call. -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64

/-- `init(key = x0, key_len = x1, effective_bits = x2, iv = x3, iv_len = x4,
ctx = x5, scratch = x6)`. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let iv : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let ctx : Region := ⟨s.gpr .x5, 144⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      stk.Disjoint key ∧ stk.Disjoint iv ∧ stk.Disjoint ctx ∧ stk.Disjoint scr ∧
      (s.gpr .x5).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) direction (s.gpr .x2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .x5) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .x0)).toNat = e.code
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

end VG.Proof.Rc2.AArch64.Stream

end

end

/-! ### `Rc2.AArch64.Stream.Verified`, which only this module used -/

section

/-! ### `Rc2.AArch64.Stream.Init`, which only this module used -/

section

/-!
# Streaming RC2-CBC on AArch64: `init`

The length checks, each a subtraction and a shift tested with `cbnz` (`chk`),
return 1, 2 or 3 (`init_post_error`); otherwise, inside the frame saving
`x30`, the IV is copied to `ctx + 128` and the verified key expansion writes
the schedule to `ctx` (`main_ok`, `init_post`).
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64
open VG.Impl.Rc2.AArch64.Stream (init initMain initArgs keyCall checkKey checkBits checkIv)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_movz wp_subImm wp_lsr wp_ldr wp_str toNat_ofNat_lt
  eval_nonzero sub_beq)

theorem ofNat_toNat' (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem inR {rs : List Region} {R : Region} {a : Addr} {n : Nat} (hR : R ∈ rs) (hc : R.Contains a n) :
    InRegions rs a n := ⟨R, hR, hc⟩

/-- `(x - 1) >> sh` is nonzero unless `x` is in `1..=2^sh`. -/
theorem chk (x : BitVec 64) {sh p : Nat} (hs : sh < 64) (hp : 2 ^ sh = p) :
    ((x - BitVec.ofNat 64 1) >>> sh != 0) = decide ¬(1 ≤ x.toNat ∧ x.toNat ≤ p) := by
  have hx := x.isLt
  obtain hp' : p ≤ 2 ^ 63 := hp ▸ Nat.pow_le_pow_right (by decide) (by omega_using [hs])
  obtain hp0 : 0 < p := hp ▸ Nat.two_pow_pos sh
  obtain e : ((x - BitVec.ofNat 64 1) >>> sh).toNat = (2 ^ 64 - 1 + x.toNat) % 2 ^ 64 / p := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, hp]
    rfl
  have z : (0 : BitVec 64).toNat = 0 := rfl
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, z,
    Nat.div_eq_zero_iff]
  by_cases h0 : x.toNat = 0
  · rw [h0]; omega_using [hp', hp0]
  · rw [show (2 ^ 64 - 1 + x.toNat) % 2 ^ 64 = x.toNat - 1 by omega_using [h0]]; omega_using [hp0, h0]

/-- The arguments of `init`, and their regions, for valid lengths. -/
structure ILay (σ : State) (key iv ctx scr : Addr) (kl eb : Nat) : Prop where
  x0 : σ.gpr .x0 = key
  x1 : σ.gpr .x1 = BitVec.ofNat 64 kl
  x2 : σ.gpr .x2 = BitVec.ofNat 64 eb
  x3 : σ.gpr .x3 = iv
  x5 : σ.gpr .x5 = ctx
  x6 : σ.gpr .x6 = scr
  rd : σ.rd = [⟨key, kl⟩, ⟨iv, 8⟩]
  wr : σ.wr = [⟨ctx, 144⟩, ⟨scr, 576⟩]
  kc : Region.Disjoint ⟨key, kl⟩ ⟨ctx, 144⟩
  ks : Region.Disjoint ⟨key, kl⟩ ⟨scr, 576⟩
  ic : Region.Disjoint ⟨iv, 8⟩ ⟨ctx, 144⟩
  cs : Region.Disjoint ⟨ctx, 144⟩ ⟨scr, 576⟩
  hk : 1 ≤ kl ∧ kl ≤ 128
  he : 1 ≤ eb ∧ eb ≤ 1024

theorem expandKey_noFrames : Impl.Rc2.AArch64.expandKey.noFrames = true := by lit_decide

/-- The IV, the key expansion and 0, without the frame. -/
theorem main_ok {σ : State} {key iv ctx scr : Addr} {kl eb : Nat} (h : ILay σ key iv ctx scr kl eb) :
    WP isa initMain σ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = σ.gpr r) ∧
      BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧
      Spec.Rc2.scheduleAt s'.mem ctx = Spec.Rc2.expandKey (Spec.Rc2.bytesAt σ.mem key kl) eb ∧
      Spec.Rc2.blockAt s'.mem (ctx + 128) = Spec.Rc2.blockAt σ.mem iv := by
  have hk := h.hk
  have he := h.he
  obtain ivS : Region.Sub ⟨ctx + BitVec.ofNat 64 128, 8⟩ ⟨ctx, 144⟩ := Offset.sub_base _ (by omega_using [])
  obtain schS : Region.Sub ⟨ctx, 128⟩ ⟨ctx, 144⟩ := Region.sub_prefix (by omega_using [])
  obtain bufS : Region.Sub ⟨scr, 512⟩ ⟨scr, 576⟩ := Region.sub_prefix (by omega_using [])
  unfold initMain initArgs
  refine WP.seq (wp_ldr (a := iv) ⟨by decide, by decide⟩ (by rw [h.x3]; simp)
    (by rw [h.rd]; exact inR (R := ⟨iv, 8⟩) (by simp) (Region.contains_self _ _)) fun s₁ u₁ => ?_)
  refine wp_str (a := ctx + BitVec.ofNat 64 128) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.x5])
    (by rw [u₁.wr, h.wr]; exact inR (R := ⟨ctx, 144⟩) (by simp) (Offset.contains_base _ (by omega_using []) (by omega_using [])))
    fun s₂ g₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_
  obtain g₄ : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → s₄.gpr r = σ.gpr r := fun r h3 h4 h8 => by
    rw [u₄.other r h4, u₃.other r h3, g₂.gpr, u₁.other r h8]
  obtain m₄ : s₄.mem = σ.mem.writeW (ctx + BitVec.ofNat 64 128) (σ.mem.readW iv 64) := by
    rw [u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem]
  obtain e0 : s₄.callEntry.gpr .x0 = key :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x0)
  obtain e1 : s₄.callEntry.gpr .x1 = BitVec.ofNat 64 kl :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x1)
  obtain e2 : s₄.callEntry.gpr .x2 = BitVec.ofNat 64 eb :=
    (State.callEntry_gpr _ (by decide)).trans ((g₄ _ (by decide) (by decide) (by decide)).trans h.x2)
  obtain e3 : s₄.callEntry.gpr .x3 = ctx := (State.callEntry_gpr _ (by decide)).trans (by
    rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x5])
  obtain e4 : s₄.callEntry.gpr .x4 = scr := (State.callEntry_gpr _ (by decide)).trans (by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x6])
  obtain hkl : (BitVec.ofNat 64 kl).toNat = kl := toNat_ofNat_lt (by omega_using [hk])
  obtain heb : (BitVec.ofNat 64 eb).toNat = eb := toNat_ofNat_lt (by omega_using [he])
  obtain zero : ∀ x : Addr, x = x + BitVec.ofNat 64 0 := fun x => by simp
  obtain rd₄ : s₄.rd = σ.rd := by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd]
  obtain wr₄ : s₄.wr = σ.wr := by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.seq (WP.call (k := keyContract) key_correct (rd := [⟨key, kl⟩])
    (wr := [⟨ctx, 128⟩, ⟨scr, 512⟩]) ?_ ?_ ?_ ?_ expandKey_noFrames)
  · simp only [keyContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, e0, e1, e2,
      e3, e4, hkl, heb]
    exact ⟨trivial, trivial, h.kc.sub_right schS, h.ks.sub_right bufS,
      (h.cs.sub_left schS).sub_right bufS, hk.1, hk.2, he.1, he.2⟩
  · rw [rd₄, wr₄, h.rd, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨key, kl⟩, by simp, 0, zero key, by dsimp only; omega_using []⟩
    · exact ⟨⟨ctx, 144⟩, by simp, 0, zero ctx, by dsimp only; omega_using []⟩
    · exact ⟨⟨scr, 576⟩, by simp, 0, zero scr, by dsimp only; omega_using []⟩
  · rw [wr₄, h.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨ctx, 144⟩, by simp, 0, zero ctx, by dsimp only; omega_using []⟩
    · exact ⟨⟨scr, 576⟩, by simp, 0, zero scr, by dsimp only; omega_using []⟩
  intro s' hr hw hsp hf hcs _ hpost
  simp only [keyContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, e0, e1, e2,
    e3, hkl, heb] at hpost
  refine wp_movz fun s₅ u₅ => WP.block_nil ⟨fun r hr h30 => ?_, by rw [u₅.gpr]; rfl, ?_, ?_⟩
  · have hne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x8 := by decide
    obtain ⟨h0, h3, h4, h8⟩ := hne r hr
    rw [u₅.other r h0, hcs r hr h30, g₄ r h3 h4 h8]
  · rw [u₅.mem, hpost, m₄, Proof.Rc2.bytesAt_frame (frame_store64 _ _ _) _ _ (by omega_using [hk])
      (by simpa using h.kc.sub_right ivS)]
  · rw [u₅.mem, blockAt_frame hf (ctx + 128) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact Offset.disjoint_base ctx (k := 128) (d := 128) (n := 8) (by omega_using []) (by omega_using [])
      · exact (h.cs.sub_left ivS).sub_right bufS), m₄]
    exact blockAt_copy _ _ _

theorem init_correct (s₀ : State) (hs : initContract.pre s₀) :
    WP isa init s₀ fun s' => GprAbi s₀ s' ∧ initContract.post s₀ s' := by
  obtain ⟨sp16, hrd, hwr, kc, ks, ic, is, cs, sk, si, sc, ss, -, -⟩ := hs
  obtain np : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x8 := by decide
  unfold init checkKey
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  refine WP.ite (decide ¬(1 ≤ (s₀.gpr .x1).toNat ∧ (s₀.gpr .x1).toNat ≤ 128))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₂ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₂.gpr, u₁.gpr, chk _ (p := 128) (by decide) (by decide)]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movz fun s₃ u₃ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₃.other r (np r hr).1, u₂.other r (np r hr).2, u₁.other r (np r hr).2]
    · exact Proof.Rc2.init_post_error (by rw [u₃.gpr]; simp only [hb, not_false_eq_true, ite_true]; rfl) fun h => hb h.1
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hb
  obtain g₂ : ∀ r, r ≠ .x8 → s₂.gpr r = s₀.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  unfold checkBits
  refine WP.seq (wp_subImm (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_)
  refine WP.ite (decide ¬(1 ≤ (s₀.gpr .x2).toNat ∧ (s₀.gpr .x2).toNat ≤ 1024))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₄ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₄.gpr, u₃.gpr, g₂ _ (by decide), chk _ (p := 1024) (by decide) (by decide)])
    (fun hb' => ?_) (fun hb' => ?_)
  · simp only [decide_eq_true_eq] at hb'
    refine wp_movz fun s₅ u₅ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₅.other r (np r hr).1, u₄.other r (np r hr).2, u₃.other r (np r hr).2, g₂ r (np r hr).2]
    · exact Proof.Rc2.init_post_error (by rw [u₅.gpr]; simp only [hb, hb', and_self, not_true_eq_false, not_false_eq_true, ite_true, ite_false]; rfl)
        fun h => hb' h.2.1
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hb'
  obtain g₄ : ∀ r, r ≠ .x8 → s₄.gpr r = s₀.gpr r := fun r h => by rw [u₄.other r h, u₃.other r h, g₂ r h]
  unfold checkIv
  refine WP.seq (wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_)
  obtain eiv := sub_beq (a := (s₀.gpr .x4).toNat) (b := 8) (s₀.gpr .x4).isLt (by decide)
  rw [← ofNat_toNat' (s₀.gpr .x4)] at eiv
  refine WP.ite (!decide ((s₀.gpr .x4).toNat = 8))
    (by show VG.AArch64.eval (.nonzero .x .x8) s₅ = _
        rw [VG.Proof.MdStream.AArch64.eval_nonzero, u₅.gpr, g₄ _ (by decide), bne, eiv]) (fun hb'' => ?_) (fun hb'' => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb''
    refine wp_movz fun s₆ u₆ => WP.block_nil ⟨⟨fun r hr => ?_, by
      rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩, ?_⟩
    · rw [u₆.other r (np r hr).1, u₅.other r (np r hr).2, g₄ r (np r hr).2]
    · exact Proof.Rc2.init_post_error
        (by rw [u₆.gpr]; simp only [hb, hb', and_self, not_true_eq_false, ite_false]; rfl)
        fun h => hb'' h.2.2
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hb''
  obtain g₅ : ∀ r, r ≠ .x8 → s₅.gpr r = s₀.gpr r := fun r h => by rw [u₅.other r h, g₄ r h]
  obtain hσ : ILay (inner s₅) (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x6) (s₀.gpr .x1).toNat
      (s₀.gpr .x2).toNat := by
    obtain r₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    obtain w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    refine ⟨g₅ _ (by decide), (g₅ _ (by decide)).trans (ofNat_toNat' _),
      (g₅ _ (by decide)).trans (ofNat_toNat' _), g₅ _ (by decide), g₅ _ (by decide), g₅ _ (by decide),
      ?_, w₅.trans hwr, kc, ks, ?_, cs, hb, hb'⟩
    · show s₅.rd = _; rw [r₅, hrd, hb'']
    · rw [← hb'']; exact ic
  obtain sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain mem₅ : s₅.mem = s₀.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.frameReg (by rw [sp₅]; exact sp16) (fun R hR => ?_)
    (WP.mono (main_ok hσ) fun s₂ ⟨hk, hr, hs, hiv⟩ mm u f => ?_)
    (by rw [fdepth_of_noFrames (by lit_decide : initMain.noFrames = true)]; decide)
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr] at hR
    rw [sp₅]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sc
    · exact ss
  refine ⟨⟨fun r hr => ?_, sp₅⟩, ?_⟩
  · by_cases h30 : r = .x30
    · subst h30; simp [State.write, g₅ .x30 (by decide)]
    · simp only [State.write, h30, ite_false]
      exact (hk r hr h30).trans (g₅ r (np r hr).2)
  · have hf := frame_push s₅
    rw [mem₅, sp₅, g₅ .x30 (by decide)] at hf
    obtain e₁ : Spec.Rc2.bytesAt (inner s₅).mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
        Spec.Rc2.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat := by
      rw [inner_mem, mem₅, sp₅, g₅ .x30 (by decide)]
      exact Proof.Rc2.bytesAt_frame hf _ _ (by omega_using []) (by simpa using sk.symm)
    obtain e₂ : Spec.Rc2.blockAt (inner s₅).mem (s₀.gpr .x3) = Spec.Rc2.blockAt s₀.mem (s₀.gpr .x3) := by
      rw [inner_mem, mem₅, sp₅, g₅ .x30 (by decide)]
      exact blockAt_frame hf _ (by rw [hb''] at si; simpa using si.symm)
    have hs' : Spec.Rc2.scheduleAt s₂.mem (s₀.gpr .x5) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt (inner s₅).mem (s₀.gpr .x0) (s₀.gpr .x1).toNat)
          (s₀.gpr .x2).toNat := hs
    have hiv' : Spec.Rc2.blockAt s₂.mem (s₀.gpr .x5 + 128) =
        Spec.Rc2.blockAt (inner s₅).mem (s₀.gpr .x3) := hiv
    rw [e₁] at hs'
    rw [e₂] at hiv'
    -- The context lies apart from the frame, whose bytes the pop loses.
    have hfl : Frame [⟨s₀.sp - 16, 16⟩] s₂.mem mm := by rw [← sp₅]; exact f
    have hd {R : Region} (hR : R.Sub ⟨s₀.gpr .x5, 144⟩) :
        ∀ r ∈ [(⟨s₀.sp - 16, 16⟩ : Region)], R.Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (sc.sub_right hR).symm
    rw [← scheduleAt_frame hfl (s₀.gpr .x5) (hd (Region.sub_prefix (by decide)))] at hs'
    rw [← blockAt_frame hfl (s₀.gpr .x5 + 128)
      (hd (Offset.sub_base (s₀.gpr .x5) (d := 128) (n := 8) (k := 144) (by decide)))] at hiv'
    exact Proof.Rc2.init_post hb hb' hb'' hr hs' hiv'

end VG.Proof.Rc2.AArch64.Stream

end

end


/-!
# Verified streaming RC2-CBC on AArch64

Correctness (`Init`), constant time (`ConstantTime`), and states
satisfying the preconditions, moved to the shared contracts with `stack = 16`
(the frame saving `x30`).
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x3 => 0x2000 | .x5 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 := by
  simp [PublicRegs]

theorem init_correct' (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' :=
  WP.withPreservedV (init_correct s hs) (by lit_decide)

theorem init_verified : Verified target init (Proof.Rc2.cbcInitScratchContract abi 16) := by
  refine Verified.of_correct init_correct' (init_constantTime _) ?_
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs, initContract,
    publicRegs_seven] [initSat] using initSat

end VG.Proof.Rc2.AArch64.Stream

end

end


/-!
# RC2-CBC's `init` on AArch64, with its working space on the stack

`init` runs its code, proved with the working space as an
argument (`Verified.lean`), in a frame of 576 bytes that allocates it
(`Verified.stackScratchWiped`), and zero it before returning.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64 VG.Impl.Rc2.AArch64.Stream

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x3000, 144⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract AArch64.abi 592).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, AArch64.abi,
    AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 576 .x6 72 init)
      (Spec.Rc2.cbcInitContract AArch64.abi 592) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost AArch64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 576) (words := 72) init_verified (by decide) (by decide) (by decide)
    (cbcInitPostOut_local _) initFrameSat_pre

end VG.Proof.Rc2.AArch64.Stream
