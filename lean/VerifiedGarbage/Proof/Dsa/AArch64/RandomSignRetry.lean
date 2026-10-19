module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Update the bounded signing-attempt counter after a supplied-nonce call. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomRetryMem (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) : Mem :=
  if success then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := (m.writeW (off B Random.oStatus) (0 : BitVec 64)).writeW
      (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1))
    if attempts = 1 then m' else m'.writeW (off B Random.oStatus) (4 : BitVec 64)

theorem random_retryHead_ok {s : State} {B : Addr} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : (s.gpr .x0).setWidth 32 = if success then 1 else 0) :
    WP isa (.block (([.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0] : List Instr) ++
      Random.store Random.oStatus .x0)) s fun t =>
      t.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
      t.gpr .x0 = (if success then (1 : BitVec 64) else 0) ∧
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧ Keep [.x0, .x15, .x30] s t := by
  refine WP.mono (WP.keep [.x0, .x15, .x30] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
    t.gpr .x0 = (if success then (1 : BitVec 64) else 0) ∧
    t.gpr .x30 = word s.mem B RandomSign.oLink) ?_ rfl rfl rfl)
    fun t ⟨⟨hm, ha, hl⟩, hk⟩ => ⟨hm, ha, hl, hk⟩
  unfold Random.store
  brun [exec_ldrSp (show RandomSign.oLink % 8 = 0 ∧ RandomSign.oLink < 32768 by decide),
    exec_addSp (show Random.oStatus < 4096 by decide), hsp,
    hs.ld (d := RandomSign.oLink) (by decide), hs.st (d := Random.oStatus) (by decide), exec_logic, State.read, State.write,
    BitVec.or_self, ha]
  cases success <;> exact ⟨rfl, rfl⟩

theorem random_attemptDecrement_ok {s : State} {B : Addr} {attempts : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa (.block (([.ldrSp .x0 Random.oAttempts, .subImm .x .x0 .x0 1] : List Instr) ++
      Random.store Random.oAttempts .x0)) s fun t =>
      t.mem = s.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
      t.gpr .x0 = BitVec.ofNat 64 (attempts - 1) ∧ Keep [.x0, .x15] s t := by
  have hp : BitVec.ofNat 64 attempts - 1#64 = BitVec.ofNat 64 (attempts - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
    t.gpr .x0 = BitVec.ofNat 64 (attempts - 1)) ?_ rfl rfl rfl)
    fun t ⟨⟨hm, ha⟩, hk⟩ => ⟨hm, ha, hk⟩
  unfold Random.store
  brun [exec_ldrSp (show Random.oAttempts % 8 = 0 ∧ Random.oAttempts < 32768 by decide),
    exec_addSp (show Random.oAttempts < 4096 by decide), hsp,
    hs.ld (d := Random.oAttempts) (by decide), hs.st (d := Random.oAttempts) (by decide), hn, hp]

theorem random_callFinish_ok {s : State} {B : Addr} {attempts : Nat} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (ha : (s.gpr .x0).setWidth 32 = if success then 1 else 0)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa RandomSign.callFinish s fun t =>
      t.mem = randomRetryMem s.mem B success attempts ∧
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧ Keep [.x0, .x15, .x30] s t := by
  unfold RandomSign.callFinish
  refine WP.seq (WP.mono (random_retryHead_ok success hs hsp ha)
    fun u ⟨hum, hua, hul, hku⟩ => ?_)
  cases success with
  | true =>
    refine WP.ite false (by simp [eval, State.read, hua]) (fun h => Bool.noConfusion h)
      (fun _ => WP.block_nil ?_)
    exact ⟨by rw [hum]; rfl, hul, hku⟩
  | false =>
    refine WP.ite true (by simp [eval, State.read, hua]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have hus := hs.congr hku.wr
    have husp := hku.sp.trans hsp
    have hun : word u.mem B Random.oAttempts = BitVec.ofNat 64 attempts := by
      rw [hum, (writeW_outside _ B _ (by decide)).word (by decide) (by decide), hn]
    refine WP.seq (WP.mono (random_attemptDecrement_ok hus husp hun hpos hbound)
      fun v ⟨hvm, hva, hkv⟩ => ?_)
    have hvl := (hkv.gpr .x30 (by decide)).trans hul
    by_cases h1 : attempts = 1
    · refine WP.ite false (by simp [eval, State.read, hva, h1])
        (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1, ite_true],
        hvl, (hku.trans hkv).mono (by decide)⟩
    · have hnz : (BitVec.ofNat 64 (attempts - 1) == 0#64) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he
        have hh := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at hh
        omega
      refine WP.ite true (by
        change some (!(v.gpr .x0 == 0#64)) = some true
        rw [hva, hnz]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
      refine WP.mono (random_status_ok 4 (hus.congr hkv.wr) (hkv.sp.trans husp))
        fun t ⟨_, htm, hkt⟩ => ?_
      exact ⟨by rw [htm, hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1]; rfl,
        (hkt.gpr .x30 (by decide)).trans hvl, ((hku.trans hkv).trans hkt).mono (by decide)⟩

theorem random_retry_outside (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    Outside B 152 48 m (randomRetryMem m B success attempts) := by
  have step (m : Mem) (d : Nat) (v : BitVec 64) (hd : 152 ≤ d ∧ d + 8 ≤ 200) :
      Outside B 152 48 m (m.writeW (off B d) v) :=
    (writeW_outside _ _ _ (by omega)).mono hd.1 hd.2
  cases success with
  | true => exact step _ _ _ (by decide)
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split
    · exact (step _ _ _ (by decide)).trans (step _ _ _ (by decide))
    · exact ((step _ _ _ (by decide)).trans (step _ _ _ (by decide))).trans (step _ _ _ (by decide))

theorem random_retry_status (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oStatus =
      if success then 1 else if attempts = 1 then 0 else 4 := by
  cases success with
  | true => exact word_writeW_self _ _ _ _
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]
    · exact word_writeW_self _ _ _ _

theorem random_retry_attempts (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) :
    word (randomRetryMem m B success attempts) B Random.oAttempts =
      if success then word m B Random.oAttempts else BitVec.ofNat 64 (attempts - 1) := by
  cases success with
  | true => exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)
  | false =>
    simp only [randomRetryMem, Bool.false_eq_true, ite_false]
    split
    · exact word_writeW_self _ _ _ _
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]

theorem random_retry_word (m : Mem) (B : Addr) (success : Bool) (attempts d : Nat)
    (hd : d + 8 ≤ 2 ^ 64) (ha : d + 8 ≤ 152 ∨ 160 ≤ d) (hs : d + 8 ≤ 192 ∨ 200 ≤ d) :
    word (randomRetryMem m B success attempts) B d = word m B d := by
  have wa (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oAttempts) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word ha hd
  have ws (m : Mem) (v : BitVec 64) : word (m.writeW (off B Random.oStatus) v) B d = word m B d :=
    (writeW_outside _ _ _ (by decide)).word hs hd
  cases success with
  | true => exact ws _ _
  | false =>
    unfold randomRetryMem
    simp only [Bool.false_eq_true, ite_false]
    split <;> simp only [wa, ws]

end VG.Proof.Dsa.AArch64
