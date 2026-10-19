module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomDrawControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame

/-! Update the bounded signing-attempt counter after a supplied-nonce call. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomRetryMem (m : Mem) (B : Addr) (success : Bool) (attempts : Nat) : Mem :=
  if success then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := (m.writeW (off B Random.oStatus) (0 : BitVec 64)).writeW
      (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1))
    if attempts = 1 then m' else m'.writeW (off B Random.oStatus) (4 : BitVec 64)

theorem random_callFinish_ok {s : State} {B : Addr} {attempts : Nat} (success : Bool)
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (ha : (s.gpr .rax).setWidth 32 = if success then 1 else 0)
    (hn : word s.mem B Random.oAttempts = BitVec.ofNat 64 attempts)
    (hpos : 0 < attempts) (hbound : attempts < 2 ^ 64) :
    WP isa RandomSign.callFinish s fun t =>
      t.mem = randomRetryMem s.mem B success attempts ∧ Keep [.rax] s t := by
  unfold RandomSign.callFinish
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem.writeW (off B Random.oStatus) (if success then (1 : BitVec 64) else 0) ∧
      u.zf = some (!success)) ?_ rfl) fun u ⟨⟨hum, huz⟩, hku⟩ => ?_)
  · cases success <;> xrun [random_ea_sp, hsp, hs.st (d := Random.oStatus) (by decide), ha] <;> rfl
  · cases success with
    | true =>
      refine WP.ite false (by simp only [eval, huz]; rfl) (fun h => Bool.noConfusion h)
        (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hum]; rfl, hku⟩
    | false =>
      refine WP.ite true (by simp only [eval, huz]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
      have hus := hs.congr hku.2.2
      have husp := (hku.gpr (by decide)).trans hsp
      have hun : word u.mem B Random.oAttempts = BitVec.ofNat 64 attempts := by
        rw [hum, (writeW_outside _ B _ (by decide)).word (by decide) (by decide), hn]
      have hz : (BitVec.ofNat 64 (attempts - 1) == 0) = decide (attempts = 1) := by
        rw [ofNat64_beq_zero (by omega)]
        exact decide_eq_decide.mpr (by omega)
      refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun v =>
          v.mem = u.mem.writeW (off B Random.oAttempts) (BitVec.ofNat 64 (attempts - 1)) ∧
          v.zf = some (decide (attempts = 1))) (by
        xrun [random_ea_sp, husp, hus.ld (d := Random.oAttempts) (by decide),
          hus.st (d := Random.oAttempts) (by decide), hun, ofNat64_pred hpos hbound, hz]) rfl)
        fun v ⟨⟨hvm, hvz⟩, hkv⟩ => ?_)
      by_cases h1 : attempts = 1
      · refine WP.ite false (by simp only [eval, hvz, h1, decide_true]; rfl)
          (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
        exact ⟨by rw [hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1, ite_true],
          (hku.trans hkv).mono (by decide)⟩
      · refine WP.ite true (by simp only [eval, hvz, h1, decide_false]; rfl)
          (fun _ => ?_) (fun h => Bool.noConfusion h)
        refine WP.mono (random_status_ok 4 (hus.congr hkv.2.2)
          ((hkv.gpr (by decide)).trans husp)) fun t ⟨_, htm, hkt⟩ => ?_
        exact ⟨by rw [htm, hvm, hum]; simp only [randomRetryMem, Bool.false_eq_true, ite_false, h1]; rfl,
          ((hku.trans hkv).trans hkt).mono (by decide)⟩

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

end VG.Proof.Dsa.X86_64
