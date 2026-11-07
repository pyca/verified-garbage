module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndTail
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: no padding string

The tape read with fewer than `psLen` nonzero octets (`reject_ok`): `out`
zeroed, `PS`'s area wiped, and the status and `tape` by the budget, from
each block of `reject` from any state (`zpre_ok`, `wd_ok`, `outcome_ok`).
What each path leaves (`post`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-! ## The blocks -/
/-- The registers but `rs`, and the rest of the state but memory, are
`t`'s. -/
structure Same (rs : List Reg) (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  keep : Keeps rs t u

theorem zpre_ok (t : State) :
    WP isa (.block [.logic .orr .x .x9 .x0 .x0, .logic .orr .x .x10 .x4 .x4, .movz .x .x13 0 0]) t fun u =>
      Same [.x9, .x10, .x13] t u ∧ u.mem = t.mem ∧ u.gpr .x9 = t.gpr .x0 ∧ u.gpr .x10 = t.gpr .x4 ∧
        u.gpr .x13 = 0 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.read, Size.bits, BitVec.setWidth_eq,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, ite_true, 
    RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false,
    BitVec.or_self, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, trivial, trivial, trivial, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem wd_ok (t : State) :
    WP isa (.block [.movz .x .x10 1024 0, .addSp .x9 oBuf]) t fun u =>
      Same [.x9, .x10] t u ∧ u.mem = t.mem ∧ u.gpr .x10 = BitVec.ofNat 64 1024 ∧
        u.gpr .x9 = off t.sp oBuf := by
  apply WP.of_runBlock
  simp only [oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Size.bits,
    BitVec.setWidth_eq, Nat.reduceMul, BitVec.shiftLeft_zero, Nat.reduceLT, ite_true, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, trivial, rfl, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `subs`'s carry: no borrow, `a ≥ b`. -/
theorem carry_sub (a b : BitVec 64) :
    decide (2 ^ 64 ≤ a.toNat + (~~~b).toNat + (true).toNat) = decide (b.toNat ≤ a.toNat) := by
  rw [BitVec.toNat_not]
  have := b.isLt
  simp only [Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega)

theorem outcome_ok {t : State} {rl : BitVec 64}
    (ha : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 1120) 8)
    (hm : t.mem.read (t.sp + BitVec.ofNat 64 1120) 8 = rl)
    (t0 : InRegions t.wr (t.gpr .x2 + 0#64) 8) (t8 : InRegions t.wr (t.gpr .x2 + 8#64) 8) :
    WP isa (.block outcome) t fun u => Same [.x0, .x9, .x10, .x11, .x12, .x13, .x14, .x17] t u ∧
      u.mem = (t.mem.write (t.gpr .x2 + 0#64) 8
          (if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then rl else 0)).write (t.gpr .x2 + 8#64) 8
        (if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then 0 else
          if (t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16)).toNat ≤ (t.gpr .x15 + 128#64).toNat then
            t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16) else t.gpr .x15 + 128#64) ∧
      u.gpr .x0 = if (t.gpr .x15 + 128#64).toNat ≤ rl.toNat then 3 else 0 := by
  apply WP.of_runBlock
  simp only [outcome, arg, frameBytes, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, BitVec.shiftLeft_zero, and_self, ite_true, ha, hm,
    CondCode.holds, RegUpd.c_write, RegUpd.c_addWithCarry, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.v_write, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.rd_addWithCarry,
    RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry, RegUpd.mem_addWithCarry, reduceCtorEq, ite_false,
    carry_sub, t0, t8, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h9, h10, h11, h12, h13, h14, h17⟩ := hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, h0, h9, h10, h11, h12, h13, h14, h17, ite_false]
  · by_cases h1 : (t.gpr .x15 + 128#64).toNat ≤ rl.toNat <;>
    by_cases h2 : (t.gpr .x15 + rl - (t.gpr .x15 - t.gpr .x16)).toNat ≤ (t.gpr .x15 + 128#64).toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_true, ite_false] <;> rfl
  · by_cases h1 : (t.gpr .x15 + 128#64).toNat ≤ rl.toNat <;>
    simp only [h1, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true, 
      ] <;> rfl

/-! ## The outcome -/

/-- The contract's postcondition, by name. -/
def post (s u : State) : Prop :=
  let res := Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)
  (∃ req, u.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 res.used ∧
    u.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 req ∧
    res.Requests (Spec.RsaPkcs1Enc.padEntropy (psLen s)) req) ∧
  match res.outcome with
  | .accepted ps => Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
      Spec.RsaPkcs1Enc.writtenRandom u.mem (s.gpr .x0) (kOf s) ((u.gpr .x0).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)
  | .entropy .. => (u.gpr .x0).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0
  | .exhausted => (u.gpr .x0).setWidth 32 = 3 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0

theorem kept_all (s : State) : kept s (stackArg s 2).toNat = VG.Proof.RsaPkcs1Enc.nz (randB s) := by
  simp only [kept]; rw [← randB_length, List.take_length]

/-- A stack argument, in memory changed only in the frame and `out`. -/
theorem arg_mem {P : Nat} {s : State} (hp : RPre P s) {m : Mem} (hf : Frame [⟨Q s, 1104⟩, outR s] s.mem m)
    {j : Nat} (hj : j < 7) : m.read (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 = stackArg s j := by
  have hQ := Q_toNat hp
  have hc : (argsR s).Contains (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 := by
    rw [← off, ← stackArgAddr_Q]; exact arg_contains s hj
  have h := hf.read (r := ⟨Q s + BitVec.ofNat 64 (1104 + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base (Q s) (d := 1104 + 8 * j) (n := 8) (k := 1104) (by omega) (by omega)
      · exact fun x h₁ h₂ => hp.dOa x h₂ (hc.byte (by simp only [Region.Contains] at h₁; omega))) (by decide)
  rw [h]
  show s.mem.read _ 8 = s.mem.readW (stackArgAddr s j) 64
  rw [stackArgAddr_Q]; rfl

theorem rd_tape0 (m : Mem) (p : Addr) (a b : BitVec 64) :
    ((m.write (p + 0#64) 8 a).write (p + 8#64) 8 b).readW p 64 = a := by
  have h1 := rd_q (m.write (p + 0#64) 8 a) p (d := 0) (e := 8) b (.inl (by decide)) (by decide) (by decide)
  rw [rd_self] at h1
  rw [add_zero'] at h1 ⊢
  exact h1

theorem rd_tape1 (m : Mem) (p : Addr) (a b : BitVec 64) :
    ((m.write (p + 0#64) 8 a).write (p + 8#64) 8 b).readW (p + BitVec.ofNat 64 8) 64 = b := rd_self _ _ _

theorem frame_tape {s : State} (m : Mem) (a b : BitVec 64) :
    Frame [tapeR s] m ((m.write (s.gpr .x2 + 0#64) 8 a).write (s.gpr .x2 + 8#64) 8 b) :=
  ((Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).write
    (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem psLen_add {P : Nat} {s : State} (hp : RPre P s) :
    (BitVec.ofNat 64 (psLen s) + BitVec.ofNat 64 128).toNat = psLen s + 128 := by
  have := hp.ps
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show psLen s < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 128 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega)]

theorem request_val {n L c : Nat} (hn : n < 2 ^ 32) (hL : L < 2 ^ 32) (hc : c ≤ n) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 L - (BitVec.ofNat 64 n - BitVec.ofNat 64 (n - c)) =
      BitVec.ofNat 64 (n + L - c) := by
  rw [sub_used (by omega) hc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n + L < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n + L - c < 2 ^ 64 by omega),
    show 2 ^ 64 - c + (n + L) = (n + L - c) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem reject_ok {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀)
    (hI : At s t₀ (stackArg s 2).toNat u) (hc : (kept s (stackArg s 2).toNat).length < psLen s) :
    WP isa reject u fun x => Fin P s x ∧ post s x := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hrl := hp.randLen
  have hlen := (stackArg s 2).isLt
  have hfu := hI.fr
  have keepS : Keeps [.x9, .x11, .x12, .x14, .x15, .x16, .x17] s u :=
    (hb.keep.trans hI.keep).mono (by simp)
  have hx15 : u.gpr .x15 = BitVec.ofNat 64 (psLen s) := (hI.keep .x15 (by decide)).trans hb.x15
  -- `out` zeroed
  refine WP.seq (WP.seq (WP.mono (zpre_ok u) fun w₁ ⟨S₁, m₁, h₉, h₁₀, h₁₃⟩ => ?_))
  have hR₁ : ∃ R ∈ w₁.wr, Region.Sub ⟨s.gpr .x0, kOf s⟩ R :=
    ⟨outR s, by rw [S₁.wr, hfu.wr, entered_wr, hp.hwr]; simp, by
      rw [outR, kOf, hp.hsi]; exact fun _ h => h⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := s.gpr .x0) (n := kOf s) (by unfold kOf; omega) (by unfold kOf; omega) hR₁ h₁₃
    (by rw [h₉]; exact keepS _ (by decide))
    (by rw [h₁₀, keepS _ (by decide)]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm))
    fun u₁ Z₁ => ?_
  -- `PS`'s area wiped
  have hx16 := hI.x16
  generalize hcdef : (kept s (stackArg s 2).toNat).length = c at hc hx16
  have hu₁x : ∀ r, r ∉ [Reg.x9, .x10, .x13] → u₁.gpr r = u.gpr r := fun r hr =>
    (Z₁.keep r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h]))).trans
      (S₁.keep r hr)
  refine WP.seq (WP.seq (WP.mono (wd_ok u₁) fun w₂ ⟨S₂, m₂, h₁₀', h₉'⟩ => ?_))
  have hsp₂ : w₂.sp = Q s := S₂.sp.trans (Z₁.sp.trans (S₁.sp.trans hfu.sp))
  have hwr₂ : w₂.wr = (entered s).wr := S₂.wr.trans (Z₁.wr.trans (S₁.wr.trans hfu.wr))
  have hR₂ : ∃ R ∈ w₂.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hwr₂, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega)⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := off (Q s) oBuf) (n := 1024) (by decide) (by decide) hR₂
    (by rw [S₂.keep _ (by decide), Z₁.keep _ (by decide)]; exact h₁₃)
    (by rw [h₉', Z₁.sp, S₁.sp, hfu.sp]) h₁₀') fun u₂ Z₂ => ?_
  have S₂' : Same [.x9, .x10] w₂ u₂ := ⟨Z₂.rd, Z₂.wr, Z₂.sp, Z₂.v, Z₂.keep⟩
  have F₂ : Frame [psR s] w₂.mem u₂.mem := Z₂.fr
  have hsp₃ : u₂.sp = Q s := S₂'.sp.trans hsp₂
  have hwr₃ : u₂.wr = (entered s).wr := S₂'.wr.trans hwr₂
  have hrd₃ : u₂.rd = s.rd := S₂'.rd.trans (S₂.rd.trans (Z₁.rd.trans (S₁.rd.trans hfu.rd)))
  have hv₃ : u₂.v = s.v := S₂'.v.trans (S₂.v.trans (Z₁.v.trans (S₁.v.trans hfu.v)))
  have psS : Region.Sub (psR s) ⟨Q s, 1104⟩ := Offset.sub_base (Q s) (d := oBuf) (n := 1024) (k := 1104)
    (by unfold oBuf; omega)
  have oS : Region.Sub ⟨s.gpr .x0, kOf s⟩ (outR s) := by rw [outR, kOf, hp.hsi]; exact fun _ h => h
  -- memory: changed in the frame and `out`
  have F₀ : Frame [⟨Q s, 1104⟩, outR s] s.mem u₂.mem := by
    have A : Frame [⟨Q s, 1104⟩, outR s] s.mem u.mem := hfu.fr.mono (by simp)
    have B : Frame [⟨Q s, 1104⟩, outR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    have C : Frame [⟨Q s, 1104⟩, outR s] u₁.mem u₂.mem := by
      rw [← m₂]; exact F₂.sub fun r hr => ⟨⟨Q s, 1104⟩, by simp, by rw [List.mem_singleton.mp hr]; exact psS⟩
    exact A.trans (B.trans C)
  have F₁ : Frame [outR s, psR s] u.mem u₂.mem := by
    have B : Frame [outR s, psR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    have C : Frame [outR s, psR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    exact B.trans C
  have keep₂ : Keeps [.x9, .x10, .x13] u u₂ :=
    ((S₁.keep.trans (Z₁.keep.trans (S₂.keep.trans S₂'.keep)))).mono (by simp)
  have g₂ : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] → u₂.gpr r = s.gpr r :=
    fun r hr => ((keepS.trans keep₂).mono (by decide)) r hr
  have hx2 : u₂.gpr .x2 = s.gpr .x2 := g₂ _ (by decide)
  have ha : InRegions (u₂.rd ++ u₂.wr) (u₂.sp + BitVec.ofNat 64 1120) 8 := by
    rw [hsp₃, hrd₃, hwr₃, ← entered_rd]; exact args_in hp (j := 2) (by decide)
  have hm : u₂.mem.read (u₂.sp + BitVec.ofNat 64 1120) 8 = stackArg s 2 := by
    rw [hsp₃]; exact arg_mem hp F₀ (j := 2) (by decide)
  have htw : tapeR s ∈ u₂.wr := by rw [hwr₃, entered_wr, hp.hwr]; simp
  have t0 : InRegions u₂.wr (u₂.gpr .x2 + 0#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  have t8 : InRegions u₂.wr (u₂.gpr .x2 + 8#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  have hx15₂ : u₂.gpr .x15 = BitVec.ofNat 64 (psLen s) := by rw [keep₂ _ (by decide)]; exact hx15
  have hx16₂ : u₂.gpr .x16 = BitVec.ofNat 64 (psLen s - c) := by rw [keep₂ _ (by decide)]; exact hx16
  refine WP.mono (outcome_ok ha hm t0 t8) fun x ⟨Sx, mx, hx0⟩ => ?_
  rw [hx15₂, hx16₂, hx2, psLen_add hp] at mx
  rw [hx15₂, psLen_add hp] at hx0
  -- what is common to both outcomes
  have hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all, hcdef]; exact hc
  have hL : stackArg s 2 = BitVec.ofNat 64 (stackArg s 2).toNat :=
    ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  have Fx : Frame [tapeR s] u₂.mem x.mem := by rw [mx]; exact frame_tape _ _ _
  have outZ : Spec.Rsa.bytesAt x.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0 := by
    have C : Frame [psR s, tapeR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    have D : Frame [psR s, tapeR s] u₂.mem x.mem := Fx.mono (by simp)
    rw [bytes_frame (C.trans D) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun y h₁ h₂ => hp.dKo y (psR_sub s y h₂) (oS y h₁)
      · exact (hp.dOt.sub_left oS)) (by unfold kOf; omega), zloop_bytes Z₁]
  have fin : Fin P s x := by
    have k : Keeps [Reg.x0, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s x :=
      ((show Keeps _ s u₂ from g₂).trans Sx.keep).mono (by decide)
    have Fs : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem := by
      have Fx' : Frame [stkR P s, tapeR s, outR s, scrR s] u₂.mem x.mem := Fx.mono (by simp)
      refine (F₀.sub fun r hr => ?_).trans Fx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨stkR P s, by simp, ?_⟩
        have := frame_sub (P := P) s (d := 0) (n := 1104) (by decide)
        rwa [off, add_zero'] at this
      · exact ⟨outR s, by simp, fun _ h => h⟩
    refine ⟨Sx.sp.trans hsp₃, Sx.rd.trans hrd₃, Sx.wr.trans hwr₃, Fs, ?_,
      fun r hr h30 => k r (by revert hr h30; revert r; decide), fun r _ => by rw [Sx.v, hv₃]⟩
    have hd : ∀ r ∈ [outR s, psR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by decide))
      · exact Offset.disjoint _ (.inr (by unfold oBuf; omega)) (by omega) (by unfold oBuf; omega)
    have hdt : ∀ r ∈ [tapeR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.dKt.sub_left (frame_sub s (by decide))
    rw [Fx.readW (Region.contains_self _ _) hdt (by decide), F₁.readW (Region.contains_self _ _) hd (by decide)]
    exact hfu.lr
  refine ⟨fin, ?_⟩
  have hcap : Spec.RsaPkcs1Enc.padEntropy (psLen s) = psLen s + 128 := rfl
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  by_cases hge : psLen s + 128 ≤ (stackArg s 2).toNat
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_exhausted hnz (by rw [randB_length, hcap]; exact hge)
    rw [ho, hu, randB_length]
    simp only [hge, ite_true] at mx hx0
    refine ⟨⟨0, ?_, ?_, rfl⟩, ?_, outZ⟩
    · rw [mx, rd_tape0]; exact hL
    · rw [mx, rd_tape1]; rfl
    · rw [hx0]; rfl
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length, hcap]; omega)
    rw [ho, hu]
    simp only [hge, ite_false] at mx hx0
    have hv : BitVec.ofNat 64 (psLen s) + stackArg s 2 - (BitVec.ofNat 64 (psLen s) - BitVec.ofNat 64 (psLen s - c)) =
        BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c) := by
      have := request_val (n := psLen s) (L := (stackArg s 2).toNat) (c := c) (by omega) (by omega) (by omega)
      rw [← hL] at this
      exact this
    have h11 : BitVec.ofNat 64 (psLen s) + 128#64 = BitVec.ofNat 64 (psLen s + 128) := by
      apply BitVec.eq_of_toNat_eq; rw [psLen_add hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hv' : (BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c)).toNat = psLen s + (stackArg s 2).toNat - c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hv, hv', h11] at mx
    refine ⟨⟨min (psLen s + (stackArg s 2).toNat - c) (psLen s + 128), ?_, ?_, ?_⟩, ?_, outZ⟩
    · rw [mx, rd_tape0]; rfl
    · rw [mx, rd_tape1]
      by_cases hm : psLen s + (stackArg s 2).toNat - c ≤ psLen s + 128
      · simp only [hm, ite_true, Nat.min_eq_left hm]
      · simp only [hm, ite_false, Nat.min_eq_right (show psLen s + 128 ≤ psLen s + (stackArg s 2).toNat - c by omega)]
    · rw [randB_length, hcap]
      exact ⟨by simp only [Nat.lt_min]; omega, Nat.min_le_right _ _⟩
    · rw [hx0]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
