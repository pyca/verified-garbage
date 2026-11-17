module

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndScan
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndInvoke
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-! ### `RsaPkcs1Enc.AArch64.RndReject`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.AArch64.RndTail`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the zero loops

The three loops that store zeros, `n` bytes from a pointer register
counting down a counter register (`zloop_ok`): the wipe of `PS`, `out`
zeroed and the octets drawn wiped.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The body of a zero loop. -/
abbrev zbody (rz rp rc : Reg) : List Instr := [.strb rz rp 0, .addImm .x rp rp 1, .subImm .x rc rc 1]

/-- After one iteration, from `t`. -/
structure ZStep (rz rp rc : Reg) (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr rp) 1 ((t.gpr rz).setWidth 8)
  ptr : u.gpr rp = t.gpr rp + BitVec.ofNat 64 1
  ctr : u.gpr rc = t.gpr rc - BitVec.ofNat 64 1
  other : ∀ r, r ≠ rp → r ≠ rc → u.gpr r = t.gpr r

theorem zbody_ok {rz rp rc : Reg} (hpc : rp ≠ rc) {t : State}
    (hw : InRegions t.wr (t.gpr rp + BitVec.ofNat 64 0) 1) :
    WP isa (.block (zbody rz rp rc)) t (ZStep rz rp rc t) := by
  apply WP.of_runBlock
  simp only [zbody, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h1 h2 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, Ne.symm hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- After `k` of the `n` iterations of a zero loop from `t`. -/
structure ZInv (rp rc : Reg) (p : Addr) (n : Nat) (t : State) (k : Nat) (u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  keep : Keeps [rp, rc] t u
  ptr : u.gpr rp = p + BitVec.ofNat 64 k
  ctr : u.gpr rc = BitVec.ofNat 64 (n - k)
  fr : Frame [⟨p, n⟩] t.mem u.mem
  zero : ∀ j < k, u.mem (p + BitVec.ofNat 64 j) = 0

theorem zloop_ok {rz rp rc : Reg} (hpc : rp ≠ rc) (hzp : rz ≠ rp) (hzc : rz ≠ rc) {p : Addr} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 64) {t : State} (hR : ∃ R ∈ t.wr, Region.Sub ⟨p, n⟩ R)
    (hz : t.gpr rz = 0) (hp0 : t.gpr rp = p) (hc0 : t.gpr rc = BitVec.ofNat 64 n) :
    WP isa (.loop (.block (zbody rz rp rc)) (.nonzero .x rc)) t (ZInv rp rc p n t n) := by
  obtain ⟨R, hRm, hRs⟩ := hR
  refine Bytes.count_loop hn (ZInv rp rc p n t) (fun k hk u hu => ?_)
    ⟨rfl, rfl, rfl, rfl, Keeps.refl _ _, by rw [hp0, add_zero'], by rw [hc0, Nat.sub_zero],
      Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hc : (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hn', hk])
  have hw : InRegions u.wr (u.gpr rp + BitVec.ofNat 64 0) 1 := by
    rw [add_zero', hu.ptr, hu.wr]; exact ⟨R, hRm, hRs _ hc⟩
  refine WP.mono (zbody_ok hpc hw) fun w hw' => ?_
  have hzu : u.gpr rz = 0 := (hu.keep rz (by simp [hzp, hzc])).trans hz
  have hm : w.mem = u.mem.write (p + BitVec.ofNat 64 k) 1 0 := by rw [hw'.mem, hu.ptr, hzu]; rfl
  have hrc : w.gpr rc = BitVec.ofNat 64 (n - (k + 1)) := by rw [hw'.ctr, hu.ctr, Bytes.counter_step hk hn']
  refine ⟨⟨hw'.rd.trans hu.rd, hw'.wr.trans hu.wr, hw'.sp.trans hu.sp, hw'.v.trans hu.v, fun r hr => ?_,
    by rw [hw'.ptr, hu.ptr, add_add'], hrc, by rw [hm]; exact hu.fr.write (List.mem_singleton_self _) _ hc,
    fun j hj => ?_⟩, by rw [hrc, Bytes.counter_ne hk hn']⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hw'.other r hr.1 hr.2]; exact hu.keep r (by simp [hr.1, hr.2])
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hn', hk]) (by omega_using [hj]))]; exact hu.zero j hj
    · exact Bytes.write1_self _ _ _

/-- The zero loop's bytes. -/
theorem zloop_bytes {rp rc : Reg} {p : Addr} {n : Nat} {t u : State} (h : ZInv rp rc p n t n u) :
    Spec.Rsa.bytesAt u.mem p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro j h₁ _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h.zero j h₁

/-- What every path leaves, at the end of the frames' body. -/
structure Fin (P : Nat) (s x : State) : Prop where
  sp : x.sp = Q s
  rd : x.rd = s.rd
  wr : x.wr = (entered s).wr
  fr : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem
  lr : x.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  cs : ∀ r ∈ preserved, r ≠ .x30 → x.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (x.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- After `status`, from `u`. -/
structure StatusStep (s u w : State) : Prop where
  rd : w.rd = u.rd
  wr : w.wr = u.wr
  sp : w.sp = u.sp
  vv : w.v = u.v
  mem : w.mem = u.mem
  x0 : (w.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32
  x12 : w.gpr .x12 = BitVec.ofNat 64 1024
  x13 : w.gpr .x13 = off (Q s) oBuf
  x14 : w.gpr .x14 = 0
  keep : Keeps [.x0, .x9, .x12, .x13, .x14] u w

theorem status_ok {P : Nat} {s u : State} {i : Nat} {pad : List Byte} (h : AfterCall P s u i pad) :
    WP isa (.block status) u (StatusStep s u) := by
  have hsp := h.sp
  apply WP.of_runBlock
  simp only [status, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, 
    State.read, Size.bits, BitVec.setWidth_eq, Nat.reduceLT, Nat.reduceMul,
    BitVec.shiftLeft_zero, ite_true, hsp, RegUpd.sp_write, RegUpd.gpr_write,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h9, h12, h13, h14⟩ := hr
    simp only [RegUpd.gpr_write, h0, h9, h12, h13, h14, ite_false]

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hj)

theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) : Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩

/-- `PS`'s area in the frame. -/
abbrev psR (s : State) : Region := ⟨off (Q s) oBuf, 1024⟩

theorem psR_sub {P : Nat} (s : State) : Region.Sub (psR s) (stkR P s) :=
  frame_sub s (by unfold oBuf; omega_using [])

/-- The status and the wipe of `PS`, after the call. -/
theorem accTail_ok {P : Nat} {s u : State} (hp : RPre P s) {i : Nat} {pad : List Byte}
    (h : AfterCall P s u i pad) :
    WP isa (.seq (.block status) wipe) u fun x => Fin P s x ∧
      x.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i ∧ x.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .x0) (kOf s) ((x.gpr .x0).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  refine WP.seq (WP.mono (status_ok h) fun w hw => ?_)
  have hR : ∃ R ∈ w.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hw.wr, h.wr, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega_using [])⟩
  refine WP.mono (zloop_ok (rz := .x14) (rp := .x13) (rc := .x12) (by decide) (by decide) (by decide)
    (by decide) (by decide) hR hw.x14 hw.x13 hw.x12) fun x hx => ?_
  have hf : Frame [psR s] u.mem x.mem := by rw [← hw.mem]; exact hx.fr
  have dK : ∀ {R : Region}, (stkR P s).Disjoint R → ∀ r ∈ [psR s], R.Disjoint r := fun hd r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_left (psR_sub s)).symm
  have kx : ∀ r, r ∉ [Reg.x0, .x9, .x12, .x13, .x14] → x.gpr r = u.gpr r := fun r hr =>
    (hx.keep r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.2.2.2.1, hr.2.2.1⟩)).trans
      (hw.keep r hr)
  refine ⟨⟨hx.sp.trans (hw.sp.trans h.sp), hx.rd.trans (hw.rd.trans h.rd), hx.wr.trans (hw.wr.trans h.wr),
    h.fr.trans (hf.sub fun r hr => ⟨stkR P s, by simp, by rw [List.mem_singleton.mp hr]; exact psR_sub s⟩),
    ?_, fun r hr h30 => (kx r ?_).trans (h.cs r hr h30), fun r hr => by rw [hx.v, hw.vv]; exact h.vs r hr⟩,
    ?_, ?_, fun hq => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by unfold oBuf; omega_using [])) (by omega_using []) (by unfold oBuf; omega_using [])) (by decide)]
    exact h.lr
  · revert hr h30; revert r; decide
  · have ht0 : (tapeR s).Contains (s.gpr .x2) 8 := by
      have := Offset.contains_base (s.gpr .x2) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [add_zero'] at this
    rw [hf.readW (w := 64) ht0 (dK hp.dKt) (by decide)]
    exact h.tape0
  · rw [hf.readW (w := 64) (r := tapeR s) (Offset.contains_base _ (by decide) (by decide)) (dK hp.dKt) (by decide)]
    exact h.tape1
  · have e : (⟨s.gpr .x0, kOf s⟩ : Region) = outR s := by rw [outR, kOf, hp.hsi]
    have h0 : (x.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32 := by
      rw [hx.keep .x0 (by decide)]; exact hw.x0
    have hb := bytes_frame (p := s.gpr .x0) (n := kOf s) hf (by rw [e]; exact dK hp.dKo)
      (by have := hp.k2; unfold kOf; omega_using [])
    have hw0 := written_random (h.res hq)
    rw [h0]
    revert hw0
    cases Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad <;>
      simp only [Spec.RsaPkcs1Enc.writtenRandom, hb] <;> exact id

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

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
  exact decide_eq_decide.mpr (by omega_using [])

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
  obtain hQ := Q_toNat hp
  obtain hc : (argsR s).Contains (Q s + BitVec.ofNat 64 (1104 + 8 * j)) 8 := by
    rw [← off, ← stackArgAddr_Q]; exact arg_contains s hj
  obtain h := hf.read (r := ⟨Q s + BitVec.ofNat 64 (1104 + 8 * j), 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base (Q s) (d := 1104 + 8 * j) (n := 8) (k := 1104) (by omega_using []) (by omega_using [hj])
      · exact fun x h₁ h₂ => hp.dOa x h₂ (hc.byte (by simp only [Region.Contains] at h₁; omega_using [h₁]))) (by decide)
  rw [h]
  show s.mem.read _ 8 = s.mem.readW (stackArgAddr s j) 64
  rw [stackArgAddr_Q]; rfl

theorem rd_tape0 (m : Mem) (p : Addr) (a b : BitVec 64) :
    ((m.write (p + 0#64) 8 a).write (p + 8#64) 8 b).readW p 64 = a := by
  obtain h1 := rd_q (m.write (p + 0#64) 8 a) p (d := 0) (e := 8) b (.inl (by decide)) (by decide) (by decide)
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
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show psLen s < 2 ^ 64 by omega_using [this]),
    Nat.mod_eq_of_lt (show 128 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_using [this])]

theorem request_val {n L c : Nat} (hn : n < 2 ^ 32) (hL : L < 2 ^ 32) (hc : c ≤ n) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 L - (BitVec.ofNat 64 n - BitVec.ofNat 64 (n - c)) =
      BitVec.ofNat 64 (n + L - c) := by
  rw [sub_used (by omega_using [hn]) hc]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [hn]), Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega_using [hL]),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hn, hc]), Nat.mod_eq_of_lt (show n + L < 2 ^ 64 by omega_using [hn, hL]),
    Nat.mod_eq_of_lt (show n + L - c < 2 ^ 64 by omega_using [hn, hL]),
    show 2 ^ 64 - c + (n + L) = (n + L - c) + 2 ^ 64 by omega_using [hn, hc], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [hn, hL])]

theorem reject_ok {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀)
    (hI : At s t₀ (stackArg s 2).toNat u) (hc : (kept s (stackArg s 2).toNat).length < psLen s) :
    WP isa reject u fun x => Fin P s x ∧ post s x := by
  have hP := hp.ps
  obtain hQ := Q_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hrl := hp.randLen
  obtain hlen := (stackArg s 2).isLt
  have hfu := hI.fr
  obtain keepS : Keeps [.x9, .x11, .x12, .x14, .x15, .x16, .x17] s u :=
    (hb.keep.trans hI.keep).mono (by simp)
  obtain hx15 : u.gpr .x15 = BitVec.ofNat 64 (psLen s) := (hI.keep .x15 (by decide)).trans hb.x15
  -- `out` zeroed
  refine WP.seq (WP.seq (WP.mono (zpre_ok u) fun w₁ ⟨S₁, m₁, h₉, h₁₀, h₁₃⟩ => ?_))
  obtain hR₁ : ∃ R ∈ w₁.wr, Region.Sub ⟨s.gpr .x0, kOf s⟩ R :=
    ⟨outR s, by rw [S₁.wr, hfu.wr, entered_wr, hp.hwr]; simp, by
      rw [outR, kOf, hp.hsi]; exact fun _ h => h⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := s.gpr .x0) (n := kOf s) (by unfold kOf; omega_using [hk1]) (by unfold kOf; omega_using []) hR₁ h₁₃
    (by rw [h₉]; exact keepS _ (by decide))
    (by rw [h₁₀, keepS _ (by decide)]; exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm))
    fun u₁ Z₁ => ?_
  -- `PS`'s area wiped
  have hx16 := hI.x16
  generalize hcdef : (kept s (stackArg s 2).toNat).length = c at hc hx16
  obtain hu₁x : ∀ r, r ∉ [Reg.x9, .x10, .x13] → u₁.gpr r = u.gpr r := fun r hr =>
    (Z₁.keep r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h]))).trans
      (S₁.keep r hr)
  refine WP.seq (WP.seq (WP.mono (wd_ok u₁) fun w₂ ⟨S₂, m₂, h₁₀', h₉'⟩ => ?_))
  obtain hsp₂ : w₂.sp = Q s := S₂.sp.trans (Z₁.sp.trans (S₁.sp.trans hfu.sp))
  obtain hwr₂ : w₂.wr = (entered s).wr := S₂.wr.trans (Z₁.wr.trans (S₁.wr.trans hfu.wr))
  obtain hR₂ : ∃ R ∈ w₂.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hwr₂, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega_using [])⟩
  refine WP.mono (zloop_ok (rz := .x13) (rp := .x9) (rc := .x10) (by decide) (by decide) (by decide)
    (p := off (Q s) oBuf) (n := 1024) (by decide) (by decide) hR₂
    (by rw [S₂.keep _ (by decide), Z₁.keep _ (by decide)]; exact h₁₃)
    (by rw [h₉', Z₁.sp, S₁.sp, hfu.sp]) h₁₀') fun u₂ Z₂ => ?_
  obtain S₂' : Same [.x9, .x10] w₂ u₂ := ⟨Z₂.rd, Z₂.wr, Z₂.sp, Z₂.v, Z₂.keep⟩
  have F₂ : Frame [psR s] w₂.mem u₂.mem := Z₂.fr
  obtain hsp₃ : u₂.sp = Q s := S₂'.sp.trans hsp₂
  obtain hwr₃ : u₂.wr = (entered s).wr := S₂'.wr.trans hwr₂
  obtain hrd₃ : u₂.rd = s.rd := S₂'.rd.trans (S₂.rd.trans (Z₁.rd.trans (S₁.rd.trans hfu.rd)))
  obtain hv₃ : u₂.v = s.v := S₂'.v.trans (S₂.v.trans (Z₁.v.trans (S₁.v.trans hfu.v)))
  obtain psS : Region.Sub (psR s) ⟨Q s, 1104⟩ := Offset.sub_base (Q s) (d := oBuf) (n := 1024) (k := 1104)
    (by unfold oBuf; omega_using [])
  obtain oS : Region.Sub ⟨s.gpr .x0, kOf s⟩ (outR s) := by rw [outR, kOf, hp.hsi]; exact fun _ h => h
  -- memory: changed in the frame and `out`
  obtain F₀ : Frame [⟨Q s, 1104⟩, outR s] s.mem u₂.mem := by
    obtain A : Frame [⟨Q s, 1104⟩, outR s] s.mem u.mem := hfu.fr.mono (by simp)
    obtain B : Frame [⟨Q s, 1104⟩, outR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    obtain C : Frame [⟨Q s, 1104⟩, outR s] u₁.mem u₂.mem := by
      rw [← m₂]; exact F₂.sub fun r hr => ⟨⟨Q s, 1104⟩, by simp, by rw [List.mem_singleton.mp hr]; exact psS⟩
    exact A.trans (B.trans C)
  obtain F₁ : Frame [outR s, psR s] u.mem u₂.mem := by
    obtain B : Frame [outR s, psR s] u.mem u₁.mem := by
      rw [← m₁]; exact Z₁.fr.sub fun r hr => ⟨outR s, by simp, by rw [List.mem_singleton.mp hr]; exact oS⟩
    obtain C : Frame [outR s, psR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    exact B.trans C
  obtain keep₂ : Keeps [.x9, .x10, .x13] u u₂ :=
    ((S₁.keep.trans (Z₁.keep.trans (S₂.keep.trans S₂'.keep)))).mono (by simp)
  obtain g₂ : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] → u₂.gpr r = s.gpr r :=
    fun r hr => ((keepS.trans keep₂).mono (by decide)) r hr
  obtain hx2 : u₂.gpr .x2 = s.gpr .x2 := g₂ _ (by decide)
  obtain ha : InRegions (u₂.rd ++ u₂.wr) (u₂.sp + BitVec.ofNat 64 1120) 8 := by
    rw [hsp₃, hrd₃, hwr₃, ← entered_rd]; exact args_in hp (j := 2) (by decide)
  obtain hm : u₂.mem.read (u₂.sp + BitVec.ofNat 64 1120) 8 = stackArg s 2 := by
    rw [hsp₃]; exact arg_mem hp F₀ (j := 2) (by decide)
  obtain htw : tapeR s ∈ u₂.wr := by rw [hwr₃, entered_wr, hp.hwr]; simp
  obtain t0 : InRegions u₂.wr (u₂.gpr .x2 + 0#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain t8 : InRegions u₂.wr (u₂.gpr .x2 + 8#64) 8 :=
    ⟨tapeR s, htw, by rw [hx2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  obtain hx15₂ : u₂.gpr .x15 = BitVec.ofNat 64 (psLen s) := by rw [keep₂ _ (by decide)]; exact hx15
  obtain hx16₂ : u₂.gpr .x16 = BitVec.ofNat 64 (psLen s - c) := by rw [keep₂ _ (by decide)]; exact hx16
  refine WP.mono (outcome_ok ha hm t0 t8) fun x ⟨Sx, mx, hx0⟩ => ?_
  rw [hx15₂, hx16₂, hx2, psLen_add hp] at mx
  rw [hx15₂, psLen_add hp] at hx0
  -- what is common to both outcomes
  obtain hnz : (VG.Proof.RsaPkcs1Enc.nz (randB s)).length < psLen s := by rw [← kept_all, hcdef]; exact hc
  obtain hL : stackArg s 2 = BitVec.ofNat 64 (stackArg s 2).toNat :=
    ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  obtain Fx : Frame [tapeR s] u₂.mem x.mem := by rw [mx]; exact frame_tape _ _ _
  obtain outZ : Spec.Rsa.bytesAt x.mem (s.gpr .x0) (kOf s) = List.replicate (kOf s) 0 := by
    obtain C : Frame [psR s, tapeR s] u₁.mem u₂.mem := by rw [← m₂]; exact F₂.mono (by simp)
    obtain D : Frame [psR s, tapeR s] u₂.mem x.mem := Fx.mono (by simp)
    rw [bytes_frame (C.trans D) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fun y h₁ h₂ => hp.dKo y (psR_sub s y h₂) (oS y h₁)
      · exact (hp.dOt.sub_left oS)) (by unfold kOf; omega_using []), zloop_bytes Z₁]
  obtain fin : Fin P s x := by
    obtain k : Keeps [Reg.x0, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s x :=
      ((show Keeps _ s u₂ from g₂).trans Sx.keep).mono (by decide)
    obtain Fs : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem := by
      obtain Fx' : Frame [stkR P s, tapeR s, outR s, scrR s] u₂.mem x.mem := Fx.mono (by simp)
      refine (F₀.sub fun r hr => ?_).trans Fx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨stkR P s, by simp, ?_⟩
        have := frame_sub (P := P) s (d := 0) (n := 1104) (by decide)
        rwa [off, add_zero'] at this
      · exact ⟨outR s, by simp, fun _ h => h⟩
    refine ⟨Sx.sp.trans hsp₃, Sx.rd.trans hrd₃, Sx.wr.trans hwr₃, Fs, ?_,
      fun r hr h30 => k r (by revert hr h30; revert r; decide), fun r _ => by rw [Sx.v, hv₃]⟩
    obtain hd : ∀ r ∈ [outR s, psR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by decide))
      · exact Offset.disjoint _ (.inr (by unfold oBuf; omega_using [])) (by omega_using []) (by unfold oBuf; omega_using [])
    obtain hdt : ∀ r ∈ [tapeR s], Region.Disjoint ⟨off (Q s) 1088, 8⟩ r := fun r hr => by
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
  · obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_entropy hnz (by rw [randB_length, hcap]; omega_using [hge])
    rw [ho, hu]
    simp only [hge, ite_false] at mx hx0
    obtain hv : BitVec.ofNat 64 (psLen s) + stackArg s 2 - (BitVec.ofNat 64 (psLen s) - BitVec.ofNat 64 (psLen s - c)) =
        BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c) := by
      have := request_val (n := psLen s) (L := (stackArg s 2).toNat) (c := c) (by omega_using [hP]) (by omega_using [hP, hrl]) (by omega_using [hc])
      rw [← hL] at this
      exact this
    obtain h11 : BitVec.ofNat 64 (psLen s) + 128#64 = BitVec.ofNat 64 (psLen s + 128) := by
      apply BitVec.eq_of_toNat_eq; rw [psLen_add hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP])]
    obtain hv' : (BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c)).toNat = psLen s + (stackArg s 2).toNat - c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP, hrl])]
    rw [hv, hv', h11] at mx
    refine ⟨⟨min (psLen s + (stackArg s 2).toNat - c) (psLen s + 128), ?_, ?_, ?_⟩, ?_, outZ⟩
    · rw [mx, rd_tape0]; rfl
    · rw [mx, rd_tape1]
      by_cases hm : psLen s + (stackArg s 2).toNat - c ≤ psLen s + 128
      · simp only [hm, ite_true, Nat.min_eq_left hm]
      · simp only [hm, ite_false, Nat.min_eq_right (show psLen s + 128 ≤ psLen s + (stackArg s 2).toNat - c by omega_using [hm])]
    · rw [randB_length, hcap]
      exact ⟨by simp only [Nat.lt_min]; omega_using [hc, hge], Nat.min_le_right _ _⟩
    · rw [hx0]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd

end

end

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: correctness

With `PS` full, the call and its tail (`accept_ok`); the frames' body
(`body_ok`); and the function (`code_ok`): the registers the ABI keeps and
`post`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- `PS` full after `i` octets: the state before the call's arguments. -/
theorem ready_of {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hf : (kept s i).length = psLen s) : Ready s u i (kept s i) := by
  have hP := hp.ps
  refine ⟨hI.fr, (hb.keep.trans hI.keep).mono (by decide), hI.x12,
    (hI.keep .x15 (by decide)).trans hb.x15, hf, ?_, hI.hi⟩
  rw [← hf]
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range]
  rw [show off (Q s) oBuf + BitVec.ofNat 64 j = off (Q s) (oBuf + j) from off_off _ _ _, hI.buf j h₁]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

theorem accept_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s t₀ u : State} (hp : RPre c.stack s) (hb : Before s t₀) {i : Nat}
    (hI : At s t₀ i u) (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa (accept (encName c) (encCode c)) u fun x => Fin c.stack s x ∧ post s x := by
  have hr := ready_of hp hb hI hf
  refine WP.seq (WP.mono (args_ok hp hr) fun w ha => ?_)
  refine WP.seq (WP.mono (call_ok c hsat hp ha) fun u' hac => ?_)
  refine WP.mono (accTail_ok hp hac) fun x ⟨hfin, ht0, ht1, hres⟩ => ⟨hfin, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  rw [ho, hu]
  exact ⟨⟨0, ht0, ht1, rfl⟩, hres⟩

theorem body_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (body (encName c) (encCode c)) (entered s) fun x => Fin c.stack s x ∧ post s x := by
  have hP := hp.ps
  refine WP.seq (WP.mono (setup_ok hp) fun t₀ hb => ?_)
  refine WP.seq (WP.mono (scan_ok hp hb) fun u ⟨i, hI, hd⟩ => ?_)
  have hc := hI.hc
  rcases hd with ⟨hf, hpre⟩ | ⟨rfl, hlt⟩
  · refine WP.ite true (by rw [eval_zero, hI.x16, hf, Nat.sub_self]; rfl) (fun _ => accept_ok c hsat hp hb hI hf hpre)
      (fun h => absurd h (by decide))
  · have hne : (BitVec.ofNat 64 (psLen s - (kept s (stackArg s 2).toNat).length) == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hP])] at this
      simp at this; omega_using [hlt, this]
    refine WP.ite false (by rw [eval_zero, hI.x16, hne]) (fun h => absurd h (by decide))
      (fun _ => reject_ok hp hb hI hlt)

theorem popped_gpr (s : State) (r : Reg) :
    (popped .x30 s).gpr r = if r = .x30 then s.mem.read s.sp 8 else s.gpr r := by
  show (s.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

/-- `post` reads the memory only in the output and the tape's two words. -/
theorem post_congr {s x y : State}
    (hb : Spec.Rsa.bytesAt y.mem (s.gpr .x0) (kOf s) = Spec.Rsa.bytesAt x.mem (s.gpr .x0) (kOf s))
    (ht : y.mem.readW (s.gpr .x2) 64 = x.mem.readW (s.gpr .x2) 64)
    (ht8 : y.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = x.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64)
    (h0 : y.gpr .x0 = x.gpr .x0) (h : post s x) : post s y := by
  simp only [post] at h ⊢
  obtain ⟨⟨req, h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨req, ht.trans h1, ht8.trans h2, h3⟩, ?_⟩
  revert h4
  generalize (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).outcome = o
  cases o <;> simp only [h0, hb, imp_self]
  intro h4 hp
  have h5 := h4 hp
  revert h5
  generalize Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) _ = C
  cases C <;> simp only [Spec.RsaPkcs1Enc.writtenRandom, hb, imp_self]

theorem popped_mem' (x : State) : (popped .x30 x).mem = x.mem := rfl

theorem freed_mem' (b : Nat) (x : State) : (freed b x).mem = x.mem := rfl

theorem rd8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem code_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (code (encName c) (encCode c)) s fun s' => abiPreserved s s' ∧ post s s' := by
  have hQ := Q_toNat hp
  refine WP.frameAlloc (by omega_using [hQ]) (by decide) ?_ ?_
  · show 1088 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_using [hQ])]
    show 1088 ≤ s.sp.toNat - 16
    omega_using [hQ]
  · show WP isa (body (encName c) (encCode c)) (entered s) _
    refine WP.mono (body_ok c hsat hp) fun x ⟨hx, hpo⟩ mm uu fl => ?_
    have hsp' : (freed frameBytes x).sp = off (Q s) 1088 := by
      show x.sp + BitVec.ofNat 64 1088 = _; rw [hx.sp]
    -- The output and the tape lie apart from the stack, whose frames' bytes are lost.
    obtain hS : Region.Sub (below s.sp (1088 + 16)) (stkR c.stack s) :=
      Offset.sub_below s.sp (a := 1104) (n := 1104) (b := c.stack + 2191 + 1) (m := c.stack + 2191 + 1)
        (by omega_arith) (by omega_arith)
    obtain hT : ∀ R ∈ [below s.sp (1088 + 16)], (tapeR s).Disjoint R := fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact hp.dKt.symm.sub_right hS
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => hx.vs r hr⟩, ?_⟩
    · show (popped .x30 (freed frameBytes x)).gpr r = s.gpr r
      rw [popped_gpr]
      by_cases h30 : r = .x30
      · subst h30
        simp only [ite_true]
        rw [hsp', freed_mem', rd8]
        exact hx.lr
      · simp only [h30, ite_false]; exact hx.cs r hr h30
    · show x.sp + BitVec.ofNat 64 1088 + 16 = s.sp
      rw [hx.sp, BitVec.add_assoc]
      exact Q_sp s
    · refine post_congr (x := x) ?_ ?_ ?_ ?_ hpo
      · exact List.map_congr_left fun i hi => lost_byte (R := outR s) fl (hp.dKo.symm.sub_right hS)
          (show i < (s.gpr .x1).toNat by rw [hp.hsi]; exact List.mem_range.mp hi)
      · exact fl.readW (r := tapeR s)
          (by simp only [tapeR, Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide) hT (by decide)
      · exact fl.readW (r := tapeR s) (Offset.contains_base (s.gpr .x2) (d := 8) (n := 64 / 8) (k := 16)
          (by decide) (by decide)) hT (by decide)
      · show (popped .x30 (freed frameBytes x)).gpr .x0 = _
        rw [popped_gpr, ite_eq_right_of_eq_false _ _ (by decide)]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
