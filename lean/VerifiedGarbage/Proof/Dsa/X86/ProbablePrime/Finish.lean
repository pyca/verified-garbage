module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The status and the octets read -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.ProbablePrime

/-- The outputs of a test with result `res`: its status in EAX and, when the
tape sufficed, the octets read in `used`. -/
def Outputs (E : Environment) (res : Option (Bool × Spec.RsaKeyGen.Rand)) (s : State) : Prop :=
  (s.gpr .eax).toNat = Proof.Dsa.ProbablePrime.status res ∧
  ∀ b rest, res = some (b, rest) →
    Spec.Rsa.wordsAt s.mem (E.used.setWidth 64) 1 = [BitVec.ofNat 64 (E.randLength - rest.length)]

/-- The blinded loop's status word for a result. -/
def tag : Option (Bool × Spec.RsaKeyGen.Rand) → Nat
  | none => 0
  | some (true, _) => 1
  | some (false, _) => 3

theorem used_frame {E : Environment} {m m' : Mem} (O : Outside (E.used.setWidth 64) 0 8 m m') :
    Frame [E.usedRegion] m m' := by
  have F := VG.Proof.Bignum.outside_frame O (by decide)
  change Frame [⟨off (E.used.setWidth 64) 0, 8⟩] m m' at F
  have base : off (E.used.setWidth 64) 0 = E.used.setWidth 64 := by rw [off, BitVec.add_zero]
  rw [base] at F
  exact F

theorem used_outputs {E : Environment} {m : Mem} {count : BitVec 32} {res : Option (Bool × Spec.RsaKeyGen.Rand)}
    (counted : ∀ b rest, res = some (b, rest) → count.toNat = E.randLength - rest.length) :
    ∀ b rest, res = some (b, rest) →
      Spec.Rsa.wordsAt (m.writeW (E.used.setWidth 64) (BitVec.ofNat 64 count.toNat)) (E.used.setWidth 64) 1 =
        [BitVec.ofNat 64 (E.randLength - rest.length)] := by
  intro b rest same
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    counted b rest same, Mem.readW_writeW_self64]

theorem finish_ok {E : Environment} {c : Nat} {entropy : List Byte} {s : State} (I : Input E c entropy s)
    (header : 172 ≤ E.size) {res : Option (Bool × Spec.RsaKeyGen.Rand)}
    (status : w32 s.mem E.base 168 = tag res)
    (counted : ∀ b rest, res = some (b, rest) → w32 s.mem E.base 152 = E.randLength - rest.length) :
    WP isa finish s fun t =>
      Outputs E res t ∧ Frame [E.usedRegion] s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  have tagBound : tag res < 2 ^ 32 := by
    rcases res with _ | ⟨_ | _, _⟩ <;> simp only [tag] <;> decide
  have statusWord : s.mem.readW (off E.base 168) 32 = BitVec.ofNat 32 (tag res) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tagBound]
    exact status
  unfold finish
  refine WP.seq (wp_movS (readSrc_sc I.scratch (d := 168) (by omega)) fun a A _ =>
    wp_cmpS rfl fun b B Z => WP.block_nil ?_)
  have M : b.mem = s.mem := B.mem.trans A.mem
  have K : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := I.scratch.of_keeps K (by decide)
  have Wb := I.memory.usedWrite.of_keeps K
  have pointer : b.mem.readW (off E.base 44) 32 = E.used := by rw [M]; exact I.usedPtr
  have countB : b.mem.readW (off E.base 152) 32 = s.mem.readW (off E.base 152) 32 := by rw [M]
  have value : b.gpr .eax = BitVec.ofNat 32 (tag res) := by rw [(B.keeps []).1 .eax (by decide), A.gpr, statusWord]
  have usedBranch (n : Nat) (h : res ≠ none) (st : n = Proof.Dsa.ProbablePrime.status res) {q : State} (Kq : Keeps [.eax] s q)
      (Mq : q.mem = s.mem) :
      WP isa (VG.Impl.RsaKeyGen.X86.CandidateFinish.used n) q fun t =>
        Outputs E res t ∧ Frame [E.usedRegion] s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
    refine WP.mono (VG.Proof.RsaKeyGen.X86.CandidateFinish.used_ok (I.scratch.of_keeps Kq (by decide))
      (by omega) (I.memory.usedWrite.of_keeps Kq) (by rw [Mq]; exact I.usedPtr) rfl)
      fun t ⟨eax, mem, O, Kt⟩ => ?_
    refine ⟨⟨?_, ?_⟩, by rw [← Mq]; exact used_frame O, (Kq.mono (by decide)).trans Kt⟩
    · have small : n < 2 ^ 32 := by
        rw [st]
        rcases res with _ | ⟨_ | _, _⟩
        · exact absurd rfl h
        all_goals simp only [Proof.Dsa.ProbablePrime.status]; decide
      rw [eax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      exact st
    · rw [mem, Mq]
      exact used_outputs (m := s.mem) (fun b rest same => counted b rest same)
  cases res with
  | none =>
    have condition : isa.eval .e b = some false := by
      change b.zf = _
      rw [Z, A.gpr, statusWord]
      simp only [tag]
      decide
    refine WP.ite false condition (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.seq (wp_cmpS rfl fun d D Z0 => WP.block_nil ?_)
    have condition0 : isa.eval .e d = some true := by
      change d.zf = _
      rw [Z0, value]
      simp only [tag]
      decide
    refine WP.ite true condition0 (fun _ => ?_) (fun bad => nomatch bad)
    have Kd : Keeps [.eax] s d := K.widen (D.keeps [])
    refine WP.mono (VG.Proof.RsaKeyGen.X86.CandidateFinish.none_ok (Sb.of_keeps (D.keeps []) (by decide))
      (by omega) (Wb.of_keeps (D.keeps [])) (by rw [D.mem]; exact pointer)) fun t ⟨eax, _, O, Kt⟩ => ?_
    refine ⟨⟨by rw [eax]; rfl, fun _ _ bad => nomatch bad⟩, by rw [← M, ← D.mem]; exact used_frame O,
      (Kd.mono (by decide)).trans Kt⟩
  | some r =>
    obtain ⟨prime, rest⟩ := r
    cases prime
    · have condition : isa.eval .e b = some false := by
        change b.zf = _
        rw [Z, A.gpr, statusWord]
        simp only [tag]
        decide
      refine WP.ite false condition (fun bad => nomatch bad) (fun _ => ?_)
      refine WP.seq (wp_cmpS rfl fun d D Z0 => WP.block_nil ?_)
      have condition0 : isa.eval .e d = some false := by
        change d.zf = _
        rw [Z0, value]
        simp only [tag]
        decide
      refine WP.ite false condition0 (fun bad => nomatch bad) (fun _ => ?_)
      exact usedBranch 2 (fun bad => nomatch bad) rfl (K.widen (D.keeps [])) (D.mem.trans M)
    · have condition : isa.eval .e b = some true := by
        change b.zf = _
        rw [Z, A.gpr, statusWord]
        simp only [tag]
        decide
      refine WP.ite true condition (fun _ => ?_) (fun bad => nomatch bad)
      exact usedBranch 1 (fun bad => nomatch bad) rfl K M

end VG.Proof.Dsa.X86.ProbablePrime
