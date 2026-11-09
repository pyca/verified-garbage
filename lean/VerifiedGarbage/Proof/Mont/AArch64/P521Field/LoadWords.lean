module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearPair
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Framework.Block

/-! Individual loaded words, as well as their packed integer value. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def readWords (m : Mem) (p : Addr) (b : Nat) : Nat → List Word
  | 0 => []
  | k+1 => word m p b::readWords m p (b+8) k

theorem readWords_length (m : Mem) (p : Addr) (b k : Nat) : (readWords m p b k).length=k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp only [readWords,List.length_cons,ih]

theorem readWords_value (m : Mem) (p : Addr) (b k : Nat) : value (readWords m p b k)=wordsVal m p b k := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp only [readWords,value,wordsVal,ih]

theorem loadsR_each {size : Nat} {rn : Reg} : ∀ (rs : List Reg) {s : State} {p : Addr} {b : Nat},
    Ptr s rn p size → b+8*rs.length≤size → b%8=0 → rs.Nodup → rn∉rs →
    WP isa (.block (loadsR rn rs b)) s fun t =>
      rs.map t.gpr=readWords s.mem p b rs.length ∧ Keeps rs s t ∧ t.c=s.c
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl,⟨fun _ _ => rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
  | r::rs, s, p, b, hp, hb, hb8, hn, hr => by
    simp only [List.mem_cons,not_or] at hr
    have hn' := List.nodup_cons.mp hn
    rw [loadsR,←List.singleton_append,WP.block_append_iff]
    refine WP.mono (ldR_ok hp (d:=b) (by simp only [List.length_cons] at hb; omega_arith) hb8 r)
      fun u ⟨au,ku,cu⟩ => ?_
    have hpu := hp.of_keeps ku (by simpa only [List.mem_singleton] using hr.1)
    refine WP.mono (loadsR_each rs hpu (by simp only [List.length_cons] at hb; omega_arith)
      (by omega_arith) hn'.2 hr.2) fun t ⟨et,kt,ct⟩ => ?_
    refine ⟨?_,(ku.mono (by simp)).trans (kt.mono (fun _ h => List.mem_cons_of_mem _ h)),ct.trans cu⟩
    simp only [List.map_cons,List.length_cons,readWords,kt.gpr r hn'.1,au,et,ku.mem]

end VG.Proof.Mont.AArch64.P521Field
