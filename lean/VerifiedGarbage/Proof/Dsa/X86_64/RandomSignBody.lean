module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignAttempt
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! ### `Dsa.X86_64.RandomSignFinishResult`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.RandomSignPublishValue`, which this module and modules that import it used -/

section

/-! Published consumption, preserved signature bytes, and erased nonce bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_publish_used (m : Mem) (B : Addr) :
    (randomPublishMem m B).readW (word m B Random.oUsedPtr) 64 = word m B Random.oUsed :=
  Mem.readW_writeW_self64 _ _ _

theorem random_writeW_bytes {m : Mem} {p dst : Addr} {n : Nat} (v : BitVec 64)
    (hsep : Mem.Sep p n dst 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW dst v) p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply Mem.write_apply
  apply hsep
  rw [Mem.sub_ofNat_toNat _ (by have := List.mem_range.mp hi; omega_using [hn, this])]
  exact List.mem_range.mp hi

theorem random_publish_output {m : Mem} {B p : Addr} {n : Nat}
    (hframe : (⟨p, n⟩ : Region).Disjoint ⟨B, Random.frameBytes⟩)
    (hused : Mem.Sep p n (word m B Random.oUsedPtr) 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (randomPublishMem m B) p n = Spec.Rsa.bytesAt m p n := by
  unfold randomPublishMem
  rw [random_writeW_bytes _ hused hn]
  exact random_private_bytes (InScr.of_outside (random_clear_outside _ _) (by decide)) hframe (Nat.le_of_lt hn)

theorem random_publish_nonce_zero {m : Mem} {B : Addr}
    (hsep : Mem.Sep (off B Random.oNonce) 32 (word m B Random.oUsedPtr) 8) (i : Nat) (hi : i < 32) :
    randomPublishMem m B (off B (200 + i)) = 0 := by
  unfold randomPublishMem
  have he : off B (200 + i) = off B Random.oNonce + BitVec.ofNat 64 i := by
    simp only [off, Random.oNonce, BitVec.ofNat_add, BitVec.add_assoc]
  have hout : ¬(off B (200 + i) - word m B Random.oUsedPtr).toNat < 8 := by
    apply hsep
    rw [he, Mem.sub_ofNat_toNat _ (by omega_using [hi])]
    exact hi
  exact (Mem.write_apply hout).trans (random_clear_byte _ _ i hi)

end VG.Proof.Dsa.X86_64

end

end

/-! Convert a completed retry loop into the public signature and consumption outputs. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/RandomSignLoop.lean`, which only this module imported.
section

/-! Functional correctness and termination of the outer signing retry loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Dsa.Random
open VG.Proof.Dsa (RandomSignResultRel randomSignRemaining randomSignDraw)

def RandomSignLoopPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop :=
  (∃ fuel, RandomSignRunning h hq (start + result.used) fuel t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status ∧
  (result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.signature.getD (List.replicate (s.gpr .rsi).toNat 0))

def RandomSignLoopInv {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult)
    (fuel : Nat) (t : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning h hq used fuel t ∧
    RandomSignResultRel (randomInput s) start result used fuel

private theorem sample_none_status {draw : VG.Spec.Dsa.Random.Sample} (h : draw.scalar = none) :
    sampleStatus draw ≠ 1 ∧ (BitVec.ofNat 64 (sampleStatus draw) : BitVec 64) ≠ 4 := by
  simp only [sampleStatus, h]
  split <;> decide

private theorem attempt_progress (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {start fuel : Nat} {result : Spec.Dsa.RandomSignResult}
    (hi : RandomSignLoopInv h hq start result fuel t) (hv : RandomValid S s) :
    WP isa (RandomSign.attempt S.name S.code) t fun u =>
      Scr u (randomBase s) Random.frameBytes ∧ u.gpr .rsp = randomBase s ∧
      ((word u.mem (randomBase s) Random.oStatus ≠ 4 ∧ RandomSignLoopPost h hq start result u) ∨
        (word u.mem (randomBase s) Random.oStatus = 4 ∧ ∃ k < fuel, RandomSignLoopInv h hq start result k u)) := by
  obtain ⟨hpos, hbound, used, hr, hrel⟩ := hi
  cases fuel with
  | zero => omega
  | succ fuel =>
    refine WP.mono (random_sign_attempt S hr hpos (by omega_using [hbound]) hv) fun u hu => ?_
    cases hc : (randomSignDraw (randomInput s) used).scalar with
    | none =>
      simp only [RandomSignAttemptPost, hc] at hu
      obtain ⟨hr', hs⟩ := hu
      obtain ⟨_, _, hready⟩ := hr'.ready
      obtain ⟨_, hstatus, hused⟩ := hrel.sample_none hc
      have hne := sample_none_status hc
      refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hs]; exact hne.2,
        ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hs, hstatus], ?_⟩⟩
      intro he
      exact False.elim (hne.1 (hstatus.symm.trans he))
    | some k =>
      simp only [RandomSignAttemptPost, hc] at hu
      cases hs : randomSingleResult s k with
      | some sig =>
        simp only [hs, Option.isSome_some, ite_true] at hu
        obtain ⟨hr', hword, hout⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        obtain ⟨hsig, hstatus, hused⟩ := hrel.success hc hs
        refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
          ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl,
          fun _ => ?_⟩⟩
        rw [hsig]
        exact hout
      | none =>
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_sub_cancel] at hu
        obtain ⟨hr', hword, _⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        have hrel' := hrel.retry hc hs
        by_cases hz : fuel = 0
        · subst fuel
          obtain ⟨_, hstatus, hused⟩ := hrel'.exhausted
          refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
            ⟨0, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl, ?_⟩⟩
          intro he
          omega
        · have hn : fuel + 1 ≠ 1 := by omega_using [hz]
          refine ⟨hready.scr, hready.sp, Or.inr ⟨by rw [hword, ite_eq_right hn], fuel,
            by omega_using [], by omega_using [hz], by omega_using [hbound], used + (randomSignDraw (randomInput s) used).used, hr', hrel'⟩⟩

theorem random_sign_loop_correct (S : Signer) {s t : State} {h : RandomSignABI S.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel ≤ 8) (hv : RandomValid S s) :
    WP isa (.loop (.seq (RandomSign.attempt S.name S.code)
      (.block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 4)])) .e) t
      (RandomSignLoopPost h hq used (randomSignRemaining (randomInput s) used fuel)) := by
  apply random_statusLoop_rule_mx _ (randomBase s) (RandomSignLoopInv h hq used (randomSignRemaining (randomInput s) used fuel))
  · intro n a b ⟨hp, hb, k, hk, hrel⟩ hm hkeep hmx
    exact ⟨hp, hb, k, hk.congr hm hkeep hmx, hrel⟩
  · intro a b ⟨⟨n, hn⟩, hs, hout⟩ hm hkeep hmx
    exact ⟨⟨n, hn.congr hm hkeep hmx⟩, by rw [hm]; exact hs, fun h => by rw [hm]; exact hout h⟩
  · intro n a ha
    exact attempt_progress S ha hv
  · exact ⟨hpos, hbound, used, hr, RandomSignResultRel.refl _ _ _⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomSignFinishPre (s : State) (used : Nat) (t : State) : Prop where
  scr : Scr t (randomBase s) Random.frameBytes
  sp : t.gpr .rsp = randomBase s
  saved : RandomSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

structure RandomSignBodyPost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  sp : t.gpr .rsp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.signature.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

private theorem bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem random_finish_ready_result {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    {result : Spec.Dsa.RandomSignResult} (hr : RandomSignFinishPre s result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
      result.signature.getD (List.replicate (s.gpr .rsi).toNat 0))
    (hbound : result.status ≤ 2) (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  have houtlen : 0 < (s.gpr .rsi).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .rdx :=
    hr.saved (56, s.gpr .rdx) (by simp [randomSavedValues])
  have hframeOut := h.stackOut.sub_left (random_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (random_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .rdi) (s.gpr .rsi).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .rdx, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono_mx (by decide) (random_finish_ok (B := randomBase s) (op := s.gpr .rdi) (k := (s.gpr .rsi).toNat) hr.scr hr.sp
    (hr.saved (40, s.gpr .rdi) (by simp [randomSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .rsi) (by simp [randomSavedValues]))
    houtlen (s.gpr .rsi).isLt
    (fun j hj => ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .rsi).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ hmx => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .rdx := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨(hk.gpr (by decide)).trans hr.sp, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc hn => (hkv.gpr (random_saved_not_volatile hc)).trans (hr.callee r hc hn),
    by rw [hmx]; exact hr.mxcsr, ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .rsi).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hsig hs]
      exact bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem random_finish_result {extra : Nat} {s t : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {result : Spec.Dsa.RandomSignResult}
    (hp : RandomSignLoopPost h hq 0 result t) (hbound : result.status ≤ 2)
    (hsig : result.status ≠ 1 → result.signature = none) :
    WP isa RandomSign.finish t (RandomSignBodyPost s result) := by
  obtain ⟨⟨fuel, hr⟩, hstatus, houtput⟩ := hp
  obtain ⟨cm, draws, hready⟩ := hr.ready
  exact random_finish_ready_result h
    ⟨hready.scr, hready.sp, hr.saved, (by simpa only [randomContextOf, Nat.zero_add] using hready.usedWord), hr.rd, hr.wr, hr.callee, hr.mxcsr⟩
    hstatus houtput hbound hsig

end VG.Proof.Dsa.X86_64

end

end

/-! Compose initialization, bounded retries, and publication for admissible q. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_test_zero {t : State} :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) t fun u =>
      (u.mem = t.mem ∧ u.zf = some (t.gpr .rax == 0)) ∧ Keep [.rax] t u := by
  refine WP.keep [.rax] ?_ rfl
  xrun []
  exact sub_beq_zero _ _

theorem random_remaining_failure (p : VG.Proof.Dsa.RandomSignInput) (used fuel : Nat)
    (hs : (randomSignRemaining p used fuel).status ≠ 1) :
    (randomSignRemaining p used fuel).signature = none := by
  have he := randomSignLoop_success p.pLen p.qLen p.key p.digest fuel (p.rand.drop used)
  cases hc : (randomSignRemaining p used fuel).signature with
  | none => rfl
  | some sig =>
    exact False.elim (hs (he.mpr (by change (randomSignRemaining p used fuel).signature.isSome = true; rw [hc]; rfl)))

theorem random_sign_body_valid (S : Signer) {s : State} (h : RandomSignABI S.stack s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (hv : RandomValid S s) :
    WP isa (RandomSign.body S.name S.code)
      (allocState Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_running h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide) (random_sign_test_zero (t := t)) fun u ⟨⟨hum, huz⟩, hku⟩ hmx => ?_)
  have hur := hr.congr hum hku hmx
  refine WP.seq (WP.ite false (by simp only [eval, huz, ha]; rfl)
    (fun he => Bool.noConfusion he) (fun _ => ?_))
  refine WP.mono (random_sign_loop_correct S hur (by decide) (by decide) hv) fun w hw => ?_
  exact random_finish_result hw (randomSignLoop_status_le _ _ _ _ _ _) (random_remaining_failure _ _ _)

end VG.Proof.Dsa.X86_64
